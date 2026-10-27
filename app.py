#!/usr/bin/env python3
"""
VK Community Filter — поиск участников сообществ ВКонтакте по полу и числу друзей.

GUI: customtkinter. API: vk_api. Весь сетевой код работает в отдельном потоке,
окно обновляется через очередь сообщений.

Файлы, которые создаёт программа (рядом с app.py):
  vk_config.v2.json  — сессия vk_api (только если включено «Запомнить меня»)
  app_settings.json  — настройки окна (логин, группа, фильтры; пароль НЕ хранится)
  parser_state.json  — позиция парсера для продолжения после перезапуска
"""
import csv
import io
import json
import os
import queue
import re
import tempfile
import threading
import time
import webbrowser
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime
from tkinter import filedialog, messagebox
import tkinter as tk

import customtkinter as ctk
import requests
import vk_api
from PIL import Image, ImageDraw, ImageOps
from vk_api.exceptions import ApiError, AuthError, BadPassword, VkApiError

BASE_DIR = os.path.dirname(os.path.abspath(__file__))
CONFIG_FILE = os.path.join(BASE_DIR, "vk_config.v2.json")
STATE_FILE = os.path.join(BASE_DIR, "parser_state.json")
SETTINGS_FILE = os.path.join(BASE_DIR, "app_settings.json")
API_VERSION = "5.199"
DEFAULT_APP_ID = "2685278"  # Kate Mobile
RATE_CODES = {6, 9, 29}  # 6 — слишком часто, 9 — flood control, 29 — лимит метода

# 5 запросов groups.getMembers по 1000 участников за один execute (= 5000 за вызов)
MEMBERS_CODE = """
var items=[];var count=0;var i=0;
while(i<5){
  var r=API.groups.getMembers({"group_id":Args.g,"offset":parseInt(Args.o)+i*1000,
                               "count":1000,"fields":"sex"});
  count=r.count;items.push(r.items);i=i+1;
}
return {"count":count,"items":items};
"""

# 25 одиночных users.get: счётчик друзей отдаётся только при запросе одного пользователя
COUNTERS_CODE = """
var ids=Args.ids.split(",");var res=[];var i=0;
while(i<ids.length){
  var u=API.users.get({"user_ids":ids[i],"fields":"counters,photo_200,followers_count,last_seen,online,online_info,sex,can_write_private_message"});
  res.push(u[0]);i=i+1;
}
return res;
"""


# ----------------------------------------------------------------- утилиты
def load_json(path, default=None):
    try:
        with open(path, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return default


def save_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    os.replace(tmp, path)


def parse_group(text):
    """Ссылка / короткое имя / clubNNN -> строка для groups.getById."""
    text = text.strip()
    text = re.sub(r"^https?://(m\.)?vk\.(com|ru)/", "", text)
    text = text.split("?")[0].strip("/")
    m = re.fullmatch(r"(?:club|public|event)(\d+)", text)
    return m.group(1) if m else text


def seen_fields(u):
    """Данные о последнем заходе из профиля users.get."""
    oi = u.get("online_info") or {}
    ls = (u.get("last_seen") or {}).get("time") or oi.get("last_seen") or None
    return {"seen": ls, "online": bool(u.get("online") or oi.get("is_online")),
            "seen_status": oi.get("status"), "sex": u.get("sex")}


def seen_ok(f, window, hidden_ok, now):
    """window: None — не фильтровать, 0 — только онлайн сейчас, иначе секунды."""
    if window is None:
        return True
    if f["online"]:
        return True
    if window == 0:
        return False
    if f["seen"]:
        return now - f["seen"] <= window
    if hidden_ok:  # время скрыто, но ВК может отдать грубую категорию
        st = f["seen_status"]
        if st == "recently":
            return True
        need = {"last_week": 7 * 86400, "last_month": 30 * 86400}.get(st)
        return need is not None and window >= need
    return False


def dm_text(r):
    cw = r.get("can_write")
    return "ЛС открыты" if cw == 1 else "ЛС закрыты" if cw == 0 else "ЛС: неизвестно"


def _rel(sec):
    sec = max(0, int(sec))
    if sec < 60:
        return "только что"
    if sec < 3600:
        return f"{sec // 60} мин. назад"
    if sec < 86400:
        return f"{sec // 3600} ч. назад"
    if sec < 365 * 86400:
        return f"{sec // 86400} дн. назад"
    return f"{sec // (365 * 86400)} г. назад"


def seen_text(r):
    """(текст, вид) для показа: online / time / hidden / none."""
    if r.get("online"):
        return "Сейчас онлайн", "online"
    verb = "Была" if r.get("sex") == 1 else "Был"
    if r.get("seen"):
        return f"{verb} в сети {_rel(time.time() - r['seen'])}", "time"
    names = {"recently": "недавно", "last_week": "на этой неделе",
             "last_month": "в этом месяце", "long_ago": "давно"}
    if r.get("seen_status") in names:
        return f"{verb} в сети {names[r['seen_status']]}", "hidden"
    return "Онлайн скрыт", "none"


class Stop(Exception):
    """Внутренний сигнал остановки."""


# ----------------------------------------------------------------- backend
class Engine:
    """Сбор участников и фильтрация. Работает в своём потоке, GUI не трогает:
    всё общение через emit(kind, *payload)."""

    def __init__(self, session, emit):
        self.session = session
        self.emit = emit
        self.run_event = threading.Event()
        self.run_event.set()
        self.stop_flag = threading.Event()
        self.found = []
        self.state = None

    # --- управление
    def pause(self):
        self.run_event.clear()

    def resume(self):
        self.run_event.set()

    def stop(self):
        self.stop_flag.set()
        self.run_event.set()

    @property
    def paused(self):
        return not self.run_event.is_set()

    def log(self, text):
        self.emit("log", text)

    def _check(self):
        while not self.run_event.wait(0.25):
            if self.stop_flag.is_set():
                raise Stop()
        if self.stop_flag.is_set():
            raise Stop()

    def _sleep(self, sec):
        end = time.time() + sec
        while time.time() < end:
            if self.stop_flag.is_set():
                raise Stop()
            time.sleep(0.25)

    # --- вызовы API с защитой от лимитов и обрывов связи
    def vk_call(self, fn, *args, **kwargs):
        wait = 5
        for _ in range(12):
            self._check()
            try:
                return fn(*args, **kwargs)
            except ApiError as e:
                if e.code in RATE_CODES:
                    self.log(f"Лимит ВК (код {e.code}): {e}. Жду {wait} с…")
                    self._sleep(wait)
                    wait = min(wait * 2, 120)
                    continue
                raise
            except requests.exceptions.RequestException as e:
                self.log(f"Обрыв связи: {e}. Повтор через {wait} с…")
                self._sleep(wait)
                wait = min(wait * 2, 120)
        raise RuntimeError("Слишком много неудачных попыток подряд")

    def run_script(self, code, **args):
        """execute с проверкой execute_errors (лимиты внутри скрипта)."""
        wait = 5
        for _ in range(12):
            raw = self.vk_call(self.session.method, "execute",
                               dict(code=code, **args), raw=True)
            codes = {e.get("error_code") for e in (raw.get("execute_errors") or [])}
            if codes & RATE_CODES:
                self.log(f"Лимит ВК внутри запроса (коды {sorted(codes & RATE_CODES)}). "
                         f"Жду {wait} с…")
                self._sleep(wait)
                wait = min(wait * 2, 120)
                continue
            return raw.get("response")
        raise RuntimeError("Слишком много неудачных попыток подряд")

    # --- шаги
    def resolve_group(self, text):
        name = parse_group(text)
        r = self.vk_call(self.session.method, "groups.getById", {"group_id": name})
        if isinstance(r, dict):  # новые версии API: {"groups": [...]}
            r = r.get("groups", [])
        if not r:
            raise ValueError("Сообщество не найдено")
        return r[0]["id"], r[0].get("name", name)

    def collect_members(self, group_id, sex_wanted):
        ids, offset, count = [], 0, 0
        while True:
            self._check()
            resp = self.run_script(MEMBERS_CODE, g=str(group_id), o=str(offset))
            count = resp["count"]
            for page in resp["items"]:
                for m in page:
                    if m.get("deactivated"):
                        continue
                    if sex_wanted and m.get("sex") != sex_wanted:
                        continue
                    ids.append(m["id"])
            offset += 5000
            self.emit("status", f"Сбор участников: {min(offset, count)} / {count}")
            self.log(f"Собрано участников: {min(offset, count)} / {count} "
                     f"(подходит по полу: {len(ids)})")
            if offset >= count:
                break
        return ids

    def save_state(self):
        if self.state is not None:
            self.state["found"] = self.found
            try:
                save_json(STATE_FILE, self.state)
            except OSError as e:
                self.log(f"Не удалось сохранить прогресс: {e}")

    @staticmethod
    def _in_range(val, lo, hi):
        if lo is None and hi is None:
            return True
        if val is None:
            return False
        return (lo is None or val >= lo) and (hi is None or val <= hi)

    def refresh_rows(self):
        """У ранее найденных (из сохранённого прогресса) докачиваем фото, подписчиков, заход."""
        need = [r for r in self.found if r.get("pv") != 4]
        for i in range(0, len(need), 1000):
            chunk = need[i:i + 1000]
            users = self.vk_call(
                self.session.method, "users.get",
                {"user_ids": ",".join(str(r["id"]) for r in chunk),
                 "fields": "photo_200,followers_count,last_seen,online,online_info,sex,"
                           "can_write_private_message"})
            by_id = {u["id"]: u for u in users}
            for r in chunk:
                u = by_id.get(r["id"])
                if u:
                    r["photo"] = u.get("photo_200") or r.get("photo", "")
                    r["followers"] = u.get("followers_count", r.get("followers"))
                    r.update(seen_fields(u))
                    r["can_write"] = u.get("can_write_private_message")
                r["pv"] = 4

    def run(self, p):
        completed = False
        try:
            gid, gname = self.resolve_group(p["group"])
            self.log(f"Сообщество: {gname} (id {gid})")
            sig = {"group_id": gid, "sex": p["sex"], "only_open": p["only_open"],
                   "fr_min": p["fr_min"], "fr_max": p["fr_max"],
                   "fo_min": p["fo_min"], "fo_max": p["fo_max"],
                   "show_hidden": p["show_hidden"],
                   "seen_window": p["seen_window"], "seen_hidden": p["seen_hidden"],
                   "dm": p["dm"]}
            st = load_json(STATE_FILE)
            if st and st.get("signature") == sig and st.get("ids") is not None:
                ids, pos = st["ids"], st.get("pos", 0)
                self.found = st.get("found", [])
                hidden, seen = st.get("hidden", 0), st.get("seen", False)
                self.log(f"Найден сохранённый прогресс — продолжаю: {pos} / {len(ids)}")
                try:
                    self.refresh_rows()
                except Stop:
                    raise
                except Exception as e:
                    self.log(f"Не удалось обновить фото: {e}")
            else:
                ids = self.collect_members(gid, p["sex"])
                pos, hidden, seen = 0, 0, False
                self.found = []
            self.emit("restore", list(self.found))
            self.state = {"signature": sig, "ids": ids, "pos": pos,
                          "hidden": hidden, "seen": seen, "found": self.found}
            self.save_state()

            total = len(ids)
            if pos >= total:
                self.emit("progress", total, total, len(self.found))
                self.log("Все участники уже проверены. Для нового поиска нажмите "
                         "«Сбросить прогресс».")
                completed = True
                return
            batches = 0
            stat = {"vis": 0, "cat": 0}
            warned_seen = False
            while pos < total:
                self._check()
                chunk = ids[pos:pos + 25]
                res = self.run_script(COUNTERS_CODE, ids=",".join(map(str, chunk)))
                for u in res or []:
                    if not u or u.get("deactivated"):
                        continue
                    if p["only_open"] and u.get("is_closed"):
                        continue
                    friends = (u.get("counters") or {}).get("friends")
                    followers = u.get("followers_count")
                    if followers is None:
                        followers = (u.get("counters") or {}).get("followers")
                    if not self._in_range(followers, p["fo_min"], p["fo_max"]):
                        continue
                    sf = seen_fields(u)
                    if sf["seen"] or sf["online"]:
                        stat["vis"] += 1
                    elif sf["seen_status"]:
                        stat["cat"] += 1
                    if not seen_ok(sf, p["seen_window"], p["seen_hidden"], time.time()):
                        continue
                    cw = u.get("can_write_private_message")
                    if p["dm"] is not None and cw != p["dm"]:
                        continue
                    if friends is None:
                        hidden += 1
                        if not p["show_hidden"]:
                            continue
                    else:
                        seen = True
                        if not self._in_range(friends, p["fr_min"], p["fr_max"]):
                            continue
                    row = {"id": u["id"],
                           "name": f"{u.get('first_name', '')} {u.get('last_name', '')}".strip(),
                           "friends": friends, "followers": followers,
                           "photo": u.get("photo_200") or u.get("photo_100", ""), "pv": 4, "can_write": cw, **sf,
                           "url": f"https://vk.com/id{u['id']}"}
                    self.found.append(row)
                    self.emit("found", row)
                pos += len(chunk)
                self.state.update(pos=pos, hidden=hidden, seen=seen)
                self.emit("progress", pos, total, len(self.found))
                batches += 1
                if batches % 10 == 0:
                    self.save_state()
                if (p["seen_window"] is not None and not warned_seen and pos >= 100
                        and stat["vis"] == 0 and stat["cat"] == 0):
                    warned_seen = True
                    self.log("Внимание: ВК не отдаёт данные о последнем заходе (ни у кого из "
                             "первых 100). Фильтр «Последний заход» может ничего не найти.")
                if not seen and pos >= 100:
                    raise RuntimeError(
                        "ВК не отдаёт счётчик друзей этому токену (за 100 профилей ни одного "
                        "значения). Нужен пользовательский токен — войдите по логину или "
                        "вставьте токен пользователя.")
            self.log(f"Готово. Проверено: {total}, найдено: {len(self.found)}, "
                     f"скрыто друзей: {hidden}. Время захода: открыто у {stat['vis']}, "
                     f"только категория («недавно» и т.п.) у {stat['cat']}")
            completed = True
        except Stop:
            self.log("Остановлено. Прогресс сохранён.")
        except ApiError as e:
            self.log(f"Ошибка VK API [{e.code}]: {e}"
                     + (" — токен истёк, получите новый («Получить токен»)."
                        if e.code == 5 else ""))
        except Exception as e:  # приложение не должно падать
            self.log(f"Ошибка: {e}")
        finally:
            self.save_state()
            self.emit("done", completed)


# ----------------------------------------------------------------- GUI
class App(ctk.CTk):
    SEX_MAP = {"Только девушки": 1, "Только парни": 2, "Все": 0}
    DM_MAP = {"Не важно": None, "Только открытые ЛС": 1, "Только закрытые ЛС": 0}
    SEEN_MAP = {"Любое время": None, "Онлайн сейчас": 0, "За последний час": 3600,
                "За 6 часов": 6 * 3600, "За 24 часа": 86400, "За 3 дня": 3 * 86400,
                "За 7 дней": 7 * 86400, "За 30 дней": 30 * 86400}

    def __init__(self):
        super().__init__()
        self.settings = load_json(SETTINGS_FILE, {}) or {}
        ctk.set_appearance_mode(self.settings.get("theme", "dark"))
        ctk.set_default_color_theme("blue")
        self.title("VK Community Filter")
        self.geometry("1120x840")
        self.minsize(900, 700)

        self.q = queue.Queue()
        self.session = None
        self.engine = None
        self.thread = None
        self.tmp_config = os.path.join(tempfile.gettempdir(), f"vkfilter_{os.getpid()}.json")
        self.rows = []
        self.card_frames = []
        self.ncols = 2
        self._resize_job = None
        self._photo_err = False
        self.rendered = 0        # сколько карточек уже нарисовано
        self.avatar_labels = {}  # индекс карточки -> виджет с аватаркой
        self.gen = 0             # поколение списка (чтобы старые фото не попадали в новый)
        self.empty = None
        self.pool = ThreadPoolExecutor(max_workers=6)

        self.placeholder = self._make_avatar()
        self._build()
        self.bind("<Configure>", self._on_resize)
        self.bind_all("<Control-KeyPress>", self._on_ctrl)
        self.protocol("WM_DELETE_WINDOW", self.on_close)
        self.after(100, self.poll)
        self._auto_login()

    # ---------- построение окна
    def _build(self):
        s = self.settings
        pad = dict(padx=10, pady=5)

        # авторизация
        auth = ctk.CTkFrame(self)
        auth.pack(fill="x", padx=10, pady=(10, 4))
        ctk.CTkLabel(auth, text="Авторизация VK", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, sticky="w", **pad)
        self.auth_status = ctk.CTkLabel(auth, text="Не авторизован", text_color="#e5534b")
        self.auth_status.grid(row=0, column=1, columnspan=3, sticky="w", **pad)

        self.login_e = ctk.CTkEntry(auth, width=190, placeholder_text="Логин (телефон / email)")
        self.login_e.grid(row=1, column=0, **pad)
        self.pass_e = ctk.CTkEntry(auth, width=170, show="*", placeholder_text="Пароль")
        self.pass_e.grid(row=1, column=1, **pad)
        self.token_e = ctk.CTkEntry(auth, width=230, show="*",
                                    placeholder_text="…или токен пользователя")
        self.token_e.grid(row=1, column=2, **pad)
        self.remember = ctk.CTkCheckBox(auth, text="Запомнить меня")
        self.remember.grid(row=1, column=3, **pad)
        self.login_btn = ctk.CTkButton(auth, text="Войти", width=90, command=self.on_login)
        self.login_btn.grid(row=1, column=4, **pad)
        self.token_btn = ctk.CTkButton(auth, text="Получить токен", width=130,
                                       fg_color="#3b6e3b", hover_color="#2f582f",
                                       command=self.on_get_token)
        self.token_btn.grid(row=1, column=5, **pad)
        if s.get("login"):
            self.login_e.insert(0, s["login"])
        if s.get("remember"):
            self.remember.select()

        # параметры поиска
        sf = ctk.CTkFrame(self)
        sf.pack(fill="x", padx=10, pady=4)
        ctk.CTkLabel(sf, text="Параметры поиска", font=ctk.CTkFont(weight="bold")
                     ).grid(row=0, column=0, sticky="w", **pad)
        self.group_e = ctk.CTkEntry(sf, width=330, placeholder_text="Ссылка или короткое имя группы")
        self.group_e.grid(row=1, column=0, **pad)
        if s.get("group"):
            self.group_e.insert(0, s["group"])
        self.sex_m = ctk.CTkOptionMenu(sf, values=list(self.SEX_MAP), width=150)
        self.sex_m.set(s.get("sex", "Только девушки"))
        self.sex_m.grid(row=1, column=1, **pad)
        self.open_cb = ctk.CTkCheckBox(sf, text="Только с открытым профилем")
        self.open_cb.grid(row=1, column=2, **pad)
        if s.get("only_open"):
            self.open_cb.select()
        self.hidden_cb = ctk.CTkCheckBox(sf, text="Добавлять людей со скрытыми друзьями")
        self.hidden_cb.grid(row=1, column=3, columnspan=2, **pad)
        if s.get("show_hidden"):
            self.hidden_cb.select()

        rng = ctk.CTkFrame(sf, fg_color="transparent")
        rng.grid(row=2, column=0, columnspan=6, sticky="w", padx=4, pady=(0, 6))

        def pair(label, lo_val, hi_val):
            ctk.CTkLabel(rng, text=label).pack(side="left", padx=(8, 6))
            lo = ctk.CTkEntry(rng, width=70, placeholder_text="от")
            lo.pack(side="left")
            ctk.CTkLabel(rng, text="—").pack(side="left", padx=6)
            hi = ctk.CTkEntry(rng, width=70, placeholder_text="до")
            hi.pack(side="left", padx=(0, 28))
            if lo_val not in ("", None):
                lo.insert(0, str(lo_val))
            if hi_val not in ("", None):
                hi.insert(0, str(hi_val))
            return lo, hi

        self.fr_min_e, self.fr_max_e = pair(
            "Друзей:", s.get("friends_min", ""), s.get("friends_max", s.get("max_friends", 11)))
        self.fo_min_e, self.fo_max_e = pair(
            "Подписчиков:", s.get("followers_min", ""), s.get("followers_max", ""))
        sn = ctk.CTkFrame(sf, fg_color="transparent")
        sn.grid(row=3, column=0, columnspan=6, sticky="w", padx=4, pady=(0, 8))
        ctk.CTkLabel(sn, text="Последний заход:").pack(side="left", padx=(8, 6))
        self.seen_m = ctk.CTkOptionMenu(sn, values=list(self.SEEN_MAP), width=170)
        self.seen_m.set(s.get("seen", "Любое время"))
        self.seen_m.pack(side="left")
        self.seen_hidden_cb = ctk.CTkCheckBox(
            sn, text="Включать скрытый онлайн («был(а) недавно» и т.п.)")
        self.seen_hidden_cb.pack(side="left", padx=18)
        if s.get("seen_hidden"):
            self.seen_hidden_cb.select()
        dmf = ctk.CTkFrame(sf, fg_color="transparent")
        dmf.grid(row=4, column=0, columnspan=6, sticky="w", padx=4, pady=(0, 8))
        ctk.CTkLabel(dmf, text="Личные сообщения:").pack(side="left", padx=(8, 6))
        self.dm_m = ctk.CTkOptionMenu(dmf, values=list(self.DM_MAP), width=190)
        self.dm_m.set(s.get("dm", "Не важно"))
        self.dm_m.pack(side="left")
        self.theme_sw = ctk.CTkSwitch(sf, text="Тёмная тема", command=self.on_theme)
        if ctk.get_appearance_mode() == "Dark":
            self.theme_sw.select()
        self.theme_sw.grid(row=0, column=4, columnspan=2, sticky="e", **pad)

        # управление
        cf = ctk.CTkFrame(self)
        cf.pack(fill="x", padx=10, pady=4)
        self.start_btn = ctk.CTkButton(cf, text="Старт", width=110, command=self.on_start)
        self.start_btn.grid(row=0, column=0, **pad)
        self.pause_btn = ctk.CTkButton(cf, text="Пауза", width=130, state="disabled",
                                       command=self.on_pause)
        self.pause_btn.grid(row=0, column=1, **pad)
        self.reset_btn = ctk.CTkButton(cf, text="Сбросить прогресс", width=150,
                                       fg_color="#8a3b3b", hover_color="#6e2f2f",
                                       command=self.on_reset)
        self.reset_btn.grid(row=0, column=2, **pad)
        self.status = ctk.CTkLabel(cf, text="Проверено: 0 / 0 | Найдено: 0")
        self.status.grid(row=0, column=3, sticky="w", **pad)
        self.bar = ctk.CTkProgressBar(self)
        self.bar.set(0)
        self.bar.pack(fill="x", padx=12, pady=(2, 6))

        # результаты: прокручиваемые карточки в 2 колонки
        self.cards = ctk.CTkScrollableFrame(self)
        self.cards.pack(fill="both", expand=True, padx=10, pady=4)
        self._show_empty()

        bf = ctk.CTkFrame(self, fg_color="transparent")
        bf.pack(fill="x", padx=10)
        ctk.CTkButton(bf, text="Скопировать результаты", width=190,
                      command=self.on_copy).pack(side="left", padx=4, pady=4)
        ctk.CTkButton(bf, text="Экспорт в TXT / CSV", width=170,
                      command=self.on_export).pack(side="left", padx=4, pady=4)
        ctk.CTkLabel(bf, text="Кнопка «Перейти в профиль» (или клик по фото / имени) открывает страницу в браузере",
                     text_color="gray").pack(side="left", padx=10)

        # лог
        self.logbox = ctk.CTkTextbox(self, height=130)
        self.logbox.pack(fill="x", padx=10, pady=(4, 10))
        self.logbox.configure(state="disabled")

    # ---------- буфер обмена на любой раскладке
    def _on_ctrl(self, e):
        w = self.focus_get()
        if not isinstance(w, tk.Entry):
            return
        if e.keysym.lower() in ("v", "c", "x", "a"):
            return  # латиница — стандартная обработка уже сработала
        actions = {86: "<<Paste>>", 67: "<<Copy>>", 88: "<<Cut>>"}
        if e.keycode in actions:
            w.event_generate(actions[e.keycode])
            return "break"
        if e.keycode == 65:
            w.select_range(0, "end")
            w.icursor("end")
            return "break"

    # ---------- очередь сообщений от потоков
    def post(self, *msg):
        self.q.put(msg)

    def poll(self):
        try:
            while True:
                self.handle(self.q.get_nowait())
        except queue.Empty:
            pass
        self._maybe_render()
        self.after(100, self.poll)

    def handle(self, msg):
        kind, args = msg[0], msg[1:]
        if kind == "log":
            self.log(args[0])
        elif kind == "status":
            self.status.configure(text=args[0])
        elif kind == "progress":
            done, total, found = args
            self.status.configure(text=f"Проверено: {done} / {total} | Найдено: {found}")
            self.bar.set(done / total if total else 0)
        elif kind == "found":
            self.add_row(args[0])
        elif kind == "photo":
            gen, idx, data = args
            lbl = self.avatar_labels.get(idx)
            if gen == self.gen and lbl is not None:
                try:
                    img = self._make_avatar(data)
                    lbl.configure(image=img)
                    lbl._avatar = img  # держим ссылку
                except Exception:
                    pass
        elif kind == "restore":
            self.clear_rows()
            for r in args[0]:
                self.add_row(r)
        elif kind == "auth":
            text, ok = args
            self.auth_status.configure(text=text, text_color="#3fb950" if ok else "#e5534b")
            self.login_btn.configure(state="normal")
        elif kind == "done":
            self.set_state("idle")
        elif kind == "ask":
            kind_, prompt, reply = args
            title = {"2fa": "Двухфакторная аутентификация", "captcha": "Капча"}.get(kind_, "Ввод")
            dlg = ctk.CTkInputDialog(text=prompt, title=title)
            reply.put(dlg.get_input() or "")

    def log(self, text):
        self.logbox.configure(state="normal")
        self.logbox.insert("end", f"[{datetime.now():%H:%M:%S}] {text}\n")
        self.logbox.see("end")
        self.logbox.configure(state="disabled")

    # ---------- диалоги для потоков (2FA, капча)
    def ask_main(self, kind, prompt):
        reply = queue.Queue()
        self.post("ask", kind, prompt, reply)
        return reply.get()

    def auth_handler(self):
        code = self.ask_main("2fa", "Введите 6-значный код подтверждения\n"
                                    "(SMS, приложение-аутентификатор или VK ID):")
        return code.strip(), True

    def captcha_handler(self, captcha):
        url = captcha.get_url()
        webbrowser.open(url)
        key = self.ask_main("captcha", f"Введите символы с картинки.\nСсылка (открыта в "
                                       f"браузере):\n{url}")
        return captcha.try_again(key.strip())

    # ---------- авторизация
    def _auto_login(self):
        s = self.settings
        if not s.get("remember"):
            return
        if s.get("token"):
            self._start_login("", "", s["token"], True)
        elif s.get("login") and os.path.exists(CONFIG_FILE):
            self._start_login(s["login"], "", "", True)

    def on_login(self):
        login = self.login_e.get().strip()
        password = self.pass_e.get()
        token = self.token_e.get().strip()
        m = re.search(r"access_token=([^&\s]+)", token)  # можно вставить адрес целиком
        if m:
            token = m.group(1)
        if not token and not (login and (password or os.path.exists(CONFIG_FILE))):
            messagebox.showwarning("Авторизация", "Введите логин и пароль или токен")
            return
        self._start_login(login, password, token, bool(self.remember.get()))

    def on_get_token(self):
        """Официальная страница авторизации ВК -> вставляем адрес -> токен вытаскиваем сами."""
        app_id = str(self.settings.get("app_id", "")).strip()
        if not app_id:
            dlg = ctk.CTkInputDialog(
                text="Откуда брать токен?\n\n"
                     "• Оставьте поле ПУСТЫМ и нажмите OK — используется публичное\n"
                     "  официальное приложение Kate Mobile (ID 2685278).\n"
                     "• Или введите ID своего старого Standalone-приложения\n"
                     "  (если оно у вас ещё есть на vk.com/apps?act=manage).",
                title="ID приложения")
            val = dlg.get_input()
            if val is None:  # окно закрыли
                return
            app_id = val.strip() or DEFAULT_APP_ID
            if not app_id.isdigit():
                self.log("ID приложения должен быть числом.")
                return
            self.settings["app_id"] = app_id
        # offline не просим: новые токены ВК выдаёт на ограниченный срок
        url = ("https://oauth.vk.com/authorize?client_id=" + app_id +
               "&display=page&redirect_uri=https://oauth.vk.com/blank.html"
               "&scope=friends&response_type=token&v=" + API_VERSION)
        webbrowser.open(url)
        dlg = ctk.CTkInputDialog(
            text="1) В открывшемся окне браузера нажмите «Разрешить».\n"
                 "2) Откроется пустая страница. Скопируйте ВЕСЬ адрес из адресной строки\n"
                 "    (там будет access_token=...) и вставьте сюда:",
            title="Получение токена")
        text = (dlg.get_input() or "").strip()
        m = re.search(r"access_token=([^&\s]+)", text)
        token = m.group(1) if m else (text if re.fullmatch(r"[A-Za-z0-9_.\-]{40,}", text) else "")
        if not token:
            self.log("Токен не найден в вставленном тексте. Нужен адрес со словом access_token=.")
            return
        self.token_e.delete(0, "end")
        self.token_e.insert(0, token)
        self.log("Токен получен, выполняю вход…")
        self._start_login("", "", token, bool(self.remember.get()))

    def _start_login(self, login, password, token, remember):
        self.login_btn.configure(state="disabled")
        self.auth_status.configure(text="Вход…", text_color="gray")
        threading.Thread(target=self._login_worker,
                         args=(login, password, token, remember), daemon=True).start()

    def _login_worker(self, login, password, token, remember):
        try:
            kw = dict(api_version=API_VERSION, auth_handler=self.auth_handler,
                      captcha_handler=self.captcha_handler)
            if token:
                sess = vk_api.VkApi(token=token, **kw)
            else:
                cfg = CONFIG_FILE if remember else self.tmp_config
                sess = vk_api.VkApi(login, password or None, config_filename=cfg, **kw)
                sess.auth(token_only=True)
            me = sess.get_api().users.get()[0]
            self.session = sess
            name = f"{me.get('first_name', '')} {me.get('last_name', '')}".strip()
            if not remember and os.path.exists(CONFIG_FILE) and not token:
                os.remove(CONFIG_FILE)  # «не запоминать» — стираем старую сессию
            self.settings.update(login=login, remember=remember,
                                 token=token if remember and token else "")
            self.post("auth", f"Авторизован как {name}", True)
            self.post("log", f"Вход выполнен: {name}")
        except BadPassword:
            self.post("auth", "Не авторизован", False)
            self.post("log", "Неверный логин или пароль.")
        except AuthError as e:
            self.post("auth", "Не авторизован", False)
            self.post("log", f"Вход по логину и паролю не работает: ВК изменил страницу входа, и "
                             f"библиотека vk_api её больше не понимает ({e}). "
                             f"Нажмите «Получить токен».")
        except ApiError as e:
            self.post("auth", "Не авторизован", False)
            if e.code == 5:
                self.post("log", "Токен недействителен или истёк. Нажмите «Получить токен» "
                                 "и получите новый.")
            else:
                self.post("log", f"Ошибка авторизации [{e.code}]: {e}")
        except VkApiError as e:
            self.post("auth", "Не авторизован", False)
            self.post("log", f"Ошибка авторизации: {e}")
        except Exception as e:
            self.post("auth", "Не авторизован", False)
            self.post("log", f"Ошибка: {e}")

    # ---------- управление поиском
    def set_state(self, state):
        if state == "idle":
            self.start_btn.configure(state="normal")
            self.pause_btn.configure(state="disabled", text="Пауза")
        elif state == "running":
            self.start_btn.configure(state="disabled")
            self.pause_btn.configure(state="normal", text="Пауза")
        elif state == "paused":
            self.pause_btn.configure(state="normal", text="Продолжить")

    def on_start(self):
        if self.session is None:
            messagebox.showwarning("Старт", "Сначала авторизуйтесь")
            return
        group = self.group_e.get().strip()
        if not group:
            messagebox.showwarning("Старт", "Укажите сообщество")
            return
        def num(entry):
            t = entry.get().strip()
            return int(t) if t else None
        try:
            fr_min, fr_max = num(self.fr_min_e), num(self.fr_max_e)
            fo_min, fo_max = num(self.fo_min_e), num(self.fo_max_e)
        except ValueError:
            messagebox.showwarning("Старт", "Числа в фильтрах должны быть целыми "
                                            "(или оставьте поле пустым)")
            return
        params = {"group": group, "sex": self.SEX_MAP[self.sex_m.get()],
                  "only_open": bool(self.open_cb.get()),
                  "show_hidden": bool(self.hidden_cb.get()),
                  "fr_min": fr_min, "fr_max": fr_max, "fo_min": fo_min, "fo_max": fo_max,
                  "seen_window": self.SEEN_MAP[self.seen_m.get()],
                  "seen_hidden": bool(self.seen_hidden_cb.get()),
                  "dm": self.DM_MAP[self.dm_m.get()]}
        self.save_settings()
        self.engine = Engine(self.session, self.post)
        self.thread = threading.Thread(target=self.engine.run, args=(params,), daemon=True)
        self.thread.start()
        self.set_state("running")
        self.log("Поиск запущен")

    def on_pause(self):
        if not self.engine:
            return
        if self.engine.paused:
            self.engine.resume()
            self.set_state("running")
            self.log("Продолжаю")
        else:
            self.engine.pause()
            self.set_state("paused")
            self.log("Пауза (прогресс сохраняется)")

    def on_reset(self):
        if not messagebox.askyesno("Сброс", "Удалить сохранённый прогресс и результаты?"):
            return
        if self.thread and self.thread.is_alive():
            self.engine.stop()
        self._reset_wait()

    def _reset_wait(self):
        if self.thread and self.thread.is_alive():
            self.after(200, self._reset_wait)
            return
        try:
            os.remove(STATE_FILE)
        except OSError:
            pass
        self.clear_rows()
        self.bar.set(0)
        self.status.configure(text="Проверено: 0 / 0 | Найдено: 0")
        self.set_state("idle")
        self.log("Прогресс сброшен")

    # ---------- карточки результатов
    def _show_empty(self):
        self.empty = ctk.CTkLabel(
            self.cards, text="Пока ничего не найдено.\nНажмите «Старт» — карточки появятся здесь.",
            text_color="gray", justify="center")
        self.empty.grid(row=0, column=0, columnspan=4, pady=70)

    def clear_rows(self):
        self.gen += 1
        for w in self.cards.winfo_children():
            w.destroy()
        self.rows = []
        self.card_frames = []
        self.rendered = 0
        self.avatar_labels = {}
        self._show_empty()

    def add_row(self, r):
        self.rows.append(r)  # рисуется лениво в _maybe_render

    def _make_avatar(self, data=None, size=120):
        px = size * 2
        if data:
            img = ImageOps.fit(Image.open(io.BytesIO(data)).convert("RGBA"), (px, px))
        else:
            img = Image.new("RGBA", (px, px), (120, 120, 120, 255))
        mask = Image.new("L", (px, px), 0)
        ImageDraw.Draw(mask).rounded_rectangle((0, 0, px - 1, px - 1), radius=px // 7, fill=255)
        img.putalpha(mask)
        return ctk.CTkImage(light_image=img, dark_image=img, size=(size, size))

    def _fetch_photo(self, gen, idx, url):
        try:
            self.post("photo", gen, idx, requests.get(url, timeout=15).content)
        except Exception as e:
            if not self._photo_err:
                self._photo_err = True
                self.post("log", f"Не удалось загрузить фото: {e}")

    @staticmethod
    def _hand(widget):
        try:
            widget._label.configure(cursor="hand2")
        except Exception:
            pass

    @staticmethod
    def _fr(r):
        return "скрыто" if r.get("friends") is None else r["friends"]

    # --- число колонок зависит от ширины окна
    def _calc_cols(self):
        w = self.cards.winfo_width()
        return max(1, min(4, w // 400)) if w > 100 else 2

    def _config_cols(self):
        for c in range(4):
            self.cards.grid_columnconfigure(c, weight=1 if c < self.ncols else 0,
                                            uniform="cards" if c < self.ncols else "")

    def _on_resize(self, e):
        if e.widget is not self:
            return
        if self._resize_job:
            self.after_cancel(self._resize_job)
        self._resize_job = self.after(250, self._relayout)

    def _relayout(self):
        self._resize_job = None
        n = self._calc_cols()
        if n == self.ncols:
            return
        self.ncols = n
        self._config_cols()
        for i, f in enumerate(self.card_frames):
            f.grid(row=i // n, column=i % n, padx=8, pady=8, sticky="nsew")

    def _maybe_render(self):
        """Бесконечная прокрутка: дорисовываем карточки, когда лента доходит до низа."""
        if self.rendered >= len(self.rows):
            return
        try:
            near_bottom = self.cards._parent_canvas.yview()[1] > 0.9
        except Exception:
            near_bottom = True
        if self.rendered < 20 or near_bottom:
            if self.empty is not None:
                self.empty.destroy()
                self.empty = None
                self.ncols = self._calc_cols()
                self._config_cols()
            for _ in range(10):
                if self.rendered >= len(self.rows):
                    break
                self._build_card(self.rendered)
                self.rendered += 1

    def _build_card(self, i):
        r = self.rows[i]
        url = r["url"]
        open_url = lambda e=None, u=url: webbrowser.open(u)
        n = self.ncols
        card = ctk.CTkFrame(self.cards, corner_radius=16)
        card.grid(row=i // n, column=i % n, padx=8, pady=8, sticky="nsew")
        card.grid_columnconfigure(1, weight=1)
        self.card_frames.append(card)

        av = ctk.CTkLabel(card, text="", image=self.placeholder)
        av.grid(row=0, column=0, rowspan=5, padx=(14, 12), pady=14)
        name = ctk.CTkLabel(card, text=r["name"], anchor="w", justify="left", wraplength=240,
                            font=ctk.CTkFont(size=16, weight="bold"))
        name.grid(row=0, column=1, sticky="sw", pady=(16, 0))

        badges = ctk.CTkFrame(card, fg_color="transparent")
        badges.grid(row=1, column=1, sticky="w", pady=(6, 0))
        if r.get("friends") is None:
            ctk.CTkLabel(badges, text="Друзья скрыты", height=22, corner_radius=11,
                         fg_color=("#f5e1c8", "#5c4326"), text_color=("#6b4510", "#f3d9b1")
                         ).pack(side="left", padx=(0, 6), ipadx=6)
        else:
            ctk.CTkLabel(badges, text=f"Друзей: {r['friends']}", height=22, corner_radius=11,
                         fg_color=("#d6e6f5", "#2d4a6b"), text_color=("#1a3a5c", "#cfe3f8")
                         ).pack(side="left", padx=(0, 6), ipadx=6)
        if r.get("followers") is not None:
            ctk.CTkLabel(badges, text=f"Подписчиков: {r['followers']}", height=22,
                         corner_radius=11, fg_color=("#d8efdc", "#2c4f35"),
                         text_color=("#1d4a28", "#c9ecd1")
                         ).pack(side="left", ipadx=6)

        txt, kind = seen_text(r)
        colors = {"online": (("#bfe8c8", "#1f6b34"), ("#0f3d1c", "#d7f5de")),
                  "time": (("#e4e4e4", "#3a3a3a"), ("#333333", "#dddddd")),
                  "hidden": (("#ece3f5", "#45365a"), ("#4a3366", "#e6d9f5")),
                  "none": (("#ececec", "#333333"), ("#777777", "#999999"))}
        fg, tc = colors[kind]
        ctk.CTkLabel(card, text=txt, height=22, corner_radius=11, fg_color=fg, text_color=tc
                     ).grid(row=2, column=1, sticky="w", pady=(6, 0), ipadx=6)

        cw = r.get("can_write")
        if cw is not None:
            dm_open = cw == 1
            ctk.CTkLabel(card, text=dm_text(r), height=22, corner_radius=11,
                         fg_color=("#bfe8c8", "#1f6b34") if dm_open else ("#f3caca", "#6b2a2a"),
                         text_color=("#0f3d1c", "#d7f5de") if dm_open else ("#5c1a1a", "#f5d4d4")
                         ).grid(row=3, column=1, sticky="w", pady=(6, 0), ipadx=6)

        ctk.CTkButton(card, text="Перейти в профиль", width=170, height=34, command=open_url
                      ).grid(row=4, column=1, sticky="nw", pady=(8, 16))

        for w in (av, name):
            w.bind("<Button-1>", open_url)
            self._hand(w)
        self.avatar_labels[i] = av
        if r.get("photo"):
            self.pool.submit(self._fetch_photo, self.gen, i, r["photo"])

    def on_copy(self):
        if not self.rows:
            messagebox.showinfo("Копирование", "Пока нет результатов")
            return
        text = "\n".join(f"{r['url']}\t{r['name']}\t{self._fr(r)}\t{r.get('followers', '')}\t{seen_text(r)[0]}\t{dm_text(r)}"
                         for r in self.rows)
        self.clipboard_clear()
        self.clipboard_append(text)
        self.log(f"Скопировано в буфер: {len(self.rows)} строк")

    def on_export(self):
        if not self.rows:
            messagebox.showinfo("Экспорт", "Пока нет результатов")
            return
        path = filedialog.asksaveasfilename(
            defaultextension=".txt",
            filetypes=[("Текст", "*.txt"), ("CSV (Excel)", "*.csv")])
        if not path:
            return
        if path.lower().endswith(".csv"):
            with open(path, "w", newline="", encoding="utf-8-sig") as f:
                w = csv.writer(f, delimiter=";")
                w.writerow(["Имя", "Друзей", "Подписчиков", "Был в сети", "Личные сообщения", "Ссылка"])
                w.writerows([r["name"], self._fr(r), r.get("followers", ""), seen_text(r)[0], dm_text(r), r["url"]]
                             for r in self.rows)
        else:
            with open(path, "w", encoding="utf-8") as f:
                f.write("\n".join(f"{r['url']}  {r['name']}  (друзей: {self._fr(r)}, "
                                  f"подписчиков: {r.get('followers', '—')}, {seen_text(r)[0]}, {dm_text(r)})"
                                  for r in self.rows))
        self.log(f"Экспортировано: {path}")

    # ---------- прочее
    def on_theme(self):
        ctk.set_appearance_mode("dark" if self.theme_sw.get() else "light")

    def save_settings(self):
        self.settings.update(
            group=self.group_e.get().strip(), sex=self.sex_m.get(),
            friends_min=self.fr_min_e.get().strip(), friends_max=self.fr_max_e.get().strip(),
            followers_min=self.fo_min_e.get().strip(), followers_max=self.fo_max_e.get().strip(),
            show_hidden=bool(self.hidden_cb.get()),
            dm=self.dm_m.get(),
            seen=self.seen_m.get(), seen_hidden=bool(self.seen_hidden_cb.get()),
            only_open=bool(self.open_cb.get()),
            theme=ctk.get_appearance_mode().lower(),
            remember=bool(self.remember.get()),
            login=self.login_e.get().strip())
        if not self.settings["remember"]:
            self.settings["token"] = ""
        try:
            save_json(SETTINGS_FILE, self.settings)
        except OSError:
            pass

    def on_close(self):
        self.save_settings()
        self.pool.shutdown(wait=False, cancel_futures=True)
        if self.engine and self.thread and self.thread.is_alive():
            self.engine.stop()
            self.thread.join(timeout=3)
        try:
            os.remove(self.tmp_config)
        except OSError:
            pass
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
