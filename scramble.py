"""
scramble.py — /scramble card-image puzzle.

The bot picks a random card, cuts the art into a grid, shuffles it, and the
player swaps pieces back into place. Faster solves pay Shards, and those
Shards count toward the SAME daily minigame cap that /gcard and Versus use
(get_daily_minigame_rewards / DAILY_MINIGAME_REWARD_CAP from config).

Load it once at startup, next to gcard / deck:   import scramble
"""
import io
import time
import random
import asyncio
import secrets
import traceback
import hmac
import base64
import json
import hashlib
import math
from functools import lru_cache
import statistics
from datetime import datetime, timezone
from urllib.parse import parse_qsl
from collections import deque
from html import escape as _html_esc

from PIL import Image, ImageDraw, ImageFont   # pip install pillow
from aiogram import F
from aiogram.types import (
    WebAppInfo, Message, CallbackQuery,
    InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto, BufferedInputFile
)
from aiogram.filters import Command
from aiogram.enums import ParseMode, ChatType

from config import (
    bot, main_router, format_rarity, ensure_user, save_db,
    is_ghost_banned, is_shadow_banned, ADMIN_IDS,
    get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)
from fastapi import HTTPException
from pydantic import BaseModel
from vlog import log_action   # /vlog activity log
from deck import dlog, deck_api   # same FastAPI router the deck / chicken Mini Apps use   # same error-only log file (dlog.txt) the deck uses

# /scramble            -> the bot picks a random card and scrambles it
# The card art is cut into SCRAMBLE_COLS x SCRAMBLE_ROWS pieces and shuffled.
# Each piece wears a numbered badge (its CURRENT position, matching the
# buttons). Tap two numbers to swap those pieces; rebuild the picture to win.
SCRAMBLE_COLS = 3
SCRAMBLE_ROWS = 3
SCRAMBLE_MAX_WIDTH = 780            # working resolution of the puzzle image (smaller = faster upload/download)
SCRAMBLE_TTL = 15 * 60              # idle seconds before a puzzle expires
SCRAMBLE_MAX_GAMES = 150            # hard cap on puzzles held in memory
# Card pool: prepared card images kept ready so a board can be sent without downloading.
# Each game CONSUMES one card from the pool. When the pool drops to SCRAMBLE_POOL_LOW it
# is refilled in the background up to SCRAMBLE_POOL_SIZE, using cards that are neither
# already in the pool nor among the last SCRAMBLE_RECENT_MAX cards played.
SCRAMBLE_POOL_SIZE = 60
SCRAMBLE_POOL_LOW = 30
SCRAMBLE_RECENT_MAX = 100
SCRAMBLE_REFILL_PARALLEL = 8        # simultaneous Telegram downloads while refilling

# Button flood guard: taps are applied strictly IN ORDER (never silently dropped, so a quick
# "3 then 5" still swaps). Only taps piling up faster than the board can redraw are refused
# (more than SCRAMBLE_MAX_PENDING waiting), and the board redraws once for the whole burst.
# Too many refused taps in a row locks the board briefly.
SCRAMBLE_MAX_PENDING = 3            # taps allowed to wait for the board at once
SCRAMBLE_FLOOD_STRIKES = 5          # refused taps in a row before the lock kicks in
SCRAMBLE_FLOOD_LOCK = 5.0           # seconds the board stays locked after a flood

# (solve under N seconds, shards). Anything slower than the last tier pays nothing.
SCRAMBLE_REWARD_TIERS = [(60, 70), (120, 35)]          # chat mode

# gid -> {owner, owner_name, chat_id, chat_username, message_id, base (jpeg bytes), perm, selected, moves, started, touched,
#          last_click, strikes, locked_until, lock, name, rarity, anime}
_scramble_games: dict[str, dict] = {}
_scramble_starting: set = set()      # owners whose puzzle is being built right now
_scramble_starting_chats: set = set()   # group chats whose puzzle is being built right now
_scramble_bot_username = None
_scramble_pool: dict = {}            # card_id -> prepared JPEG, ready to play
_scramble_recent: deque = deque(maxlen=SCRAMBLE_RECENT_MAX)   # card ids played lately
_scramble_refilling = False
_scramble_inflight: set = set()      # card ids being downloaded right now
_scramble_bg: set = set()            # keeps background tasks alive
_scramble_done: dict = {}            # gid -> finish time; late taps on a finished board are ignored quietly


def _scramble_mark_done(gid: str):
    now = time.time()
    _scramble_done[gid] = now
    for k, t in list(_scramble_done.items()):
        if now - t > 60:
            _scramble_done.pop(k, None)


def _scramble_purge():
    """Drop expired puzzles and enforce the memory cap."""
    now = time.time()
    for gid, g in list(_scramble_games.items()):
        if now - g["touched"] > SCRAMBLE_TTL:
            _scramble_games.pop(gid, None)
    while len(_scramble_games) >= SCRAMBLE_MAX_GAMES:
        oldest = min(_scramble_games, key=lambda k: _scramble_games[k]["touched"])
        _scramble_games.pop(oldest, None)


def _scramble_active_game(owner: int):
    """The owner's running puzzle, if any (expired ones are cleaned out first)."""
    _scramble_purge()
    for gid, g in _scramble_games.items():
        if g["owner"] == owner:
            return gid, g
    return None, None


async def _scramble_fetch(file_id: str) -> bytes:
    """Download a card and prepare it (resize + crop to the grid)."""
    buf = io.BytesIO()
    await bot.download(file_id, destination=buf)
    return await asyncio.to_thread(_scramble_prepare, buf.getvalue())


def _scramble_valid_ids(db: dict) -> list:
    """Card ids with art. Locked series are included too, same as /gcard."""
    return [c for c, g in db.get("global_cards", {}).items() if g.get("file_id")]


def _scramble_candidates(db: dict) -> list:
    """Cards eligible to enter the pool: not in it, and not played recently.
    A tiny catalogue relaxes the 'recent' rule so the pool can still fill."""
    valid = _scramble_valid_ids(db)
    taken = set(_scramble_pool) | _scramble_inflight
    fresh = [c for c in valid if c not in taken and c not in _scramble_recent]
    return fresh or [c for c in valid if c not in taken]


def _scramble_take(db: dict):
    """Consume one ready card from the pool -> (card_id, base), or (None, None)."""
    valid = set(_scramble_valid_ids(db))
    while _scramble_pool:
        cid = random.choice(list(_scramble_pool))
        base = _scramble_pool.pop(cid)
        if cid in valid:   # card may have been removed since it was pooled
            return cid, base
    return None, None


async def _scramble_refill(db: dict):
    """Top the pool back up to SCRAMBLE_POOL_SIZE in the background."""
    global _scramble_refilling
    if _scramble_refilling:
        return
    _scramble_refilling = True
    try:
        sem = asyncio.Semaphore(SCRAMBLE_REFILL_PARALLEL)

        async def load(cid):
            """Download one card and drop it into the pool the moment it is ready,
            so players benefit before the whole batch has finished."""
            async with sem:
                base = await _scramble_fetch(db["global_cards"][cid]["file_id"])
            if (cid not in _scramble_pool and cid not in _scramble_recent
                    and len(_scramble_pool) < SCRAMBLE_POOL_SIZE):
                _scramble_pool[cid] = base
                return True
            return False

        while len(_scramble_pool) < SCRAMBLE_POOL_SIZE:
            cands = _scramble_candidates(db)
            if not cands:
                break
            batch = random.sample(cands, min(SCRAMBLE_POOL_SIZE - len(_scramble_pool), len(cands)))
            _scramble_inflight.update(batch)
            try:
                results = await asyncio.gather(*(load(c) for c in batch), return_exceptions=True)
            finally:
                _scramble_inflight.difference_update(batch)
            for r in results:
                if isinstance(r, Exception):
                    dlog.error(f"[scramble_refill] {r}")
            if not any(r is True for r in results):   # nothing added - stop instead of looping forever
                break
    except Exception as e:
        dlog.error(f"[scramble_refill] {e}", exc_info=True)
    finally:
        _scramble_refilling = False


def _scramble_kick_refill(db: dict, low: int | None = None):
    """Start a background refill when the pool is at/below the low-water mark."""
    if len(_scramble_pool) <= (SCRAMBLE_POOL_LOW if low is None else low) and not _scramble_refilling:
        task = asyncio.create_task(_scramble_refill(db))
        _scramble_bg.add(task)
        task.add_done_callback(_scramble_bg.discard)


async def _scramble_take_wait(db: dict, wait: float = 2.5):
    """Like _scramble_take, but if the pool is empty while a refill is running, give it a moment
    to land a card instead of starting a second slow download."""
    cid, base = _scramble_take(db)
    t0 = time.time()
    while cid is None and _scramble_refilling and time.time() - t0 < wait:
        await asyncio.sleep(0.1)
        cid, base = _scramble_take(db)
    return cid, base


def _scr_bg(coro):
    """Run a coroutine in the background (errors swallowed) so the player never waits on it."""
    async def _run():
        try:
            await coro
        except Exception:
            pass
    t = asyncio.create_task(_run())
    _scramble_bg.add(t)
    t.add_done_callback(_scramble_bg.discard)


_scr_save_handle = None


def _scr_save_soon(delay: float = 1.5):
    """save_db() a moment AFTER the request has been answered (several calls = one save).
    Violation logging used to save synchronously inside the request, which made captcha
    answers and swaps wait on the disk."""
    global _scr_save_handle
    if _scr_save_handle is not None:
        return
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        save_db()
        return

    def _run():
        global _scr_save_handle
        _scr_save_handle = None
        try:
            save_db()
        except Exception as e:
            dlog.error(f"[scr_save_soon] {e}", exc_info=True)
    _scr_save_handle = loop.call_later(delay, _run)


@lru_cache(maxsize=16)
def _scramble_font(size: int):
    for name in ("DejaVuSans-Bold.ttf", "Arial Bold.ttf", "arialbd.ttf"):
        try:
            return ImageFont.truetype(name, size)
        except Exception:
            continue
    try:
        return ImageFont.load_default(size=size)   # Pillow >= 10.1
    except Exception:
        return ImageFont.load_default()


def _scramble_prepare(raw: bytes) -> bytes:
    """Downscale + crop so width/height divide evenly into the grid. Returns JPEG bytes."""
    img = Image.open(io.BytesIO(raw)).convert("RGB")
    if img.width > SCRAMBLE_MAX_WIDTH:
        ratio = SCRAMBLE_MAX_WIDTH / img.width
        img = img.resize((SCRAMBLE_MAX_WIDTH, max(1, int(img.height * ratio))), Image.BICUBIC)
    w = img.width - (img.width % SCRAMBLE_COLS)
    h = img.height - (img.height % SCRAMBLE_ROWS)
    img = img.crop((0, 0, w, h))
    out = io.BytesIO()
    img.save(out, "JPEG", quality=82)
    return out.getvalue()


def _scramble_shuffle(n: int) -> list:
    """Random permutation with no piece left in its home spot (never starts solved)."""
    while True:
        perm = list(range(n))
        random.shuffle(perm)
        if all(perm[i] != i for i in range(n)):
            return perm


def _scramble_render(base: bytes, perm: list, badges: bool = True) -> bytes:
    """perm[pos] = which original piece currently sits at grid position `pos`."""
    src = Image.open(io.BytesIO(base)).convert("RGB")
    w, h = src.size
    tw, th = w // SCRAMBLE_COLS, h // SCRAMBLE_ROWS
    out = Image.new("RGB", (w, h))
    for pos, piece in enumerate(perm):
        sx, sy = (piece % SCRAMBLE_COLS) * tw, (piece // SCRAMBLE_COLS) * th
        dx, dy = (pos % SCRAMBLE_COLS) * tw, (pos // SCRAMBLE_COLS) * th
        out.paste(src.crop((sx, sy, sx + tw, sy + th)), (dx, dy))

    if badges:
        draw = ImageDraw.Draw(out)
        font = _scramble_font(max(18, tw // 7))
        r = max(16, tw // 11)
        for pos in range(len(perm)):
            x0, y0 = (pos % SCRAMBLE_COLS) * tw, (pos // SCRAMBLE_COLS) * th
            draw.rectangle((x0, y0, x0 + tw - 1, y0 + th - 1), outline=(10, 10, 14), width=4)
            cx, cy = x0 + r + 10, y0 + r + 10
            draw.ellipse((cx - r, cy - r, cx + r, cy + r), fill=(15, 15, 20), outline=(255, 255, 255), width=2)
            draw.text((cx, cy), str(pos + 1), fill=(255, 255, 255), font=font, anchor="mm")

    buf = io.BytesIO()
    out.save(buf, "JPEG", quality=80)
    return buf.getvalue()


# Telegram (Bot API 9.4+) can colour inline buttons via `style`: "primary" (blue),
# "success" (green), "danger" (red). Older aiogram builds don't have the field, so we
# detect it once and fall back to a [bracketed] number for the picked piece.
_SCR_HAS_STYLE = "style" in getattr(InlineKeyboardButton, "model_fields", {})


def _scr_btn(text: str, data: str, style: str | None = None):
    if style and _SCR_HAS_STYLE:
        return InlineKeyboardButton(text=text, callback_data=data, style=style)
    return InlineKeyboardButton(text=f"[{text}]" if style == "success" else text, callback_data=data)


def _scramble_kb(gid: str, selected: int | None = None, solved: bool = False):
    if solved:
        return None
    rows = []
    for r in range(SCRAMBLE_ROWS):
        row = []
        for i in range(r * SCRAMBLE_COLS, (r + 1) * SCRAMBLE_COLS):
            if i == selected:   # picked piece turns green
                row.append(_scr_btn(str(i + 1), f"scr:{gid}:{i}", "success"))
            elif selected is not None:   # waiting for the 2nd tap: targets turn blue
                row.append(_scr_btn(str(i + 1), f"scr:{gid}:{i}", "primary"))
            else:
                row.append(_scr_btn(str(i + 1), f"scr:{gid}:{i}"))
        rows.append(row)
    rows.append([_scr_btn("Give Up", f"scr:{gid}:give", "danger")])
    return InlineKeyboardMarkup(inline_keyboard=rows)


def _scramble_time(seconds: float) -> str:
    seconds = int(seconds)
    return f"{seconds // 60}:{seconds % 60:02d}"


def _scramble_reward_for(elapsed: float, tiers=None) -> int:
    for limit, shards in (tiers or SCRAMBLE_REWARD_TIERS):
        if elapsed < limit:
            return shards
    return 0


def _scr_stat(db: dict, event: str, uid=None, name: str = "", mode: str = "chat",
              elapsed: float = 0.0, earned: int = 0, paid: int = 0):
    """Counters for /scr_stats: one bucket for all time plus one per UTC day (30 days kept)."""
    try:
        root = db.setdefault("scramble_stats", {})
        days = root.setdefault("days", {})
        today = days.setdefault(datetime.now(timezone.utc).strftime("%Y-%m-%d"), {})
        for b in (root.setdefault("all", {}), today):
            if event == "start":
                b["started"] = b.get("started", 0) + 1
            elif event == "giveup":
                b["gave_up"] = b.get("gave_up", 0) + 1
            elif event == "solve":
                k = "solved_web" if mode == "web" else "solved_chat"
                b[k] = b.get(k, 0) + 1
                b["shards_paid"] = b.get("shards_paid", 0) + paid
                b["shards_capped"] = b.get("shards_capped", 0) + max(0, earned - paid)
                b["time_sum"] = b.get("time_sum", 0.0) + elapsed
                if b.get("fastest") is None or elapsed < b["fastest"]:
                    b["fastest"], b["fastest_name"] = round(elapsed, 2), name
        if uid is not None:
            players = today.setdefault("players", [])
            if str(uid) not in players:
                players.append(str(uid))
        for k in sorted(days)[:-30]:
            days.pop(k, None)
    except Exception as e:
        dlog.error(f"[scr_stat] {e}", exc_info=True)


# ── /scrlog: one event log for everything Scramble does (db["scramble_log"]) ──
SCRAMBLE_LOG_MAX = 3000          # when this many entries pile up ...
SCRAMBLE_LOG_TRIM_TO = 2500      # ... trim down to this, dropping the oldest NORMAL events first (violations last)
SCRAMBLE_VIOLATIONS = {
    "too_fast", "robotic_timing", "hourly_limit", "bad_swap", "too_many_moves", "retired_finish",
    "start_spam", "banned_attempt", "flood_lock",
    "captcha_wrong", "captcha_ignored", "captcha_too_fast", "ban",
}
_scramble_log_seen: dict = {}    # (event, uid) -> last time it was logged, to keep spammy events to one line a minute


def _scr_log(db: dict, event: str, uid=None, name: str = "", **info):
    """Append one event to the Scramble log. Never raises - logging must not break the game."""
    try:
        uid = "" if uid is None else str(uid)
        if not name and uid:
            u = (db.get("users") or {}).get(uid)
            name = str(u.get("name") or "") if isinstance(u, dict) else ""
        viol = event in SCRAMBLE_VIOLATIONS
        lst = db.setdefault("scramble_log", [])
        lst.append({"t": int(time.time()), "e": event, "u": uid, "n": str(name)[:24], "v": viol,
                    "i": {k: (v if isinstance(v, (int, float, bool)) else str(v)[:60])
                          for k, v in info.items() if v is not None}})
        if len(lst) > SCRAMBLE_LOG_MAX:
            excess = len(lst) - SCRAMBLE_LOG_TRIM_TO
            keep = []
            for e in lst:                       # oldest first
                if excess > 0 and not e.get("v"):
                    excess -= 1
                    continue
                keep.append(e)
            if excess > 0:
                keep = keep[excess:]
            lst[:] = keep
        if viol:
            _scr_save_soon()
    except Exception as e:
        dlog.error(f"[scr_log] {e}", exc_info=True)


def _scr_log_once(db: dict, event: str, uid, every: float = 60.0, **info):
    """Like _scr_log, but at most one line per player per `every` seconds (for events that can repeat fast)."""
    now = time.time()
    key = (event, str(uid))
    if now - _scramble_log_seen.get(key, 0) < every:
        return
    if len(_scramble_log_seen) > 3000:
        _scramble_log_seen.clear()
    _scramble_log_seen[key] = now
    _scr_log(db, event, uid, **info)


def _scramble_settle(user_id: str, name: str, username, elapsed: float, earned: int,
                     mode: str = "chat", card: dict | None = None, moves: int | None = None,
                     chat_id="?", chat_title: str = "Unknown") -> int:
    """Records the win (rounds, best time, shards) and credits `earned` shards, limited
    by the daily minigame cap shared with /gcard and Versus. Returns shards actually paid."""
    db = ensure_user(user_id, name, username)
    user_data = db["users"][user_id]

    paid = 0
    if earned > 0:
        rewards = get_daily_minigame_rewards(user_data)
        used = rewards.get("shards", 0)
        if used < DAILY_MINIGAME_REWARD_CAP:
            paid = min(earned, DAILY_MINIGAME_REWARD_CAP - used)
            user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + paid
            rewards["shards"] = used + paid

    rec = user_data.setdefault("scramble", {})
    rec["rounds"] = rec.get("rounds", 0) + 1
    rec["shards"] = rec.get("shards", 0) + paid
    best = rec.get("best_time")
    if best is None or elapsed < best:
        rec["best_time"] = round(elapsed, 2)
    _scr_stat(db, "solve", uid=user_id, name=name, mode=mode, elapsed=elapsed, earned=earned, paid=paid)
    try:   # every solve goes into /vlog (a logging error must never block the reward)
        card = card or {}
        entry = {
            "type": "scramble_web_win" if mode == "web" else "scramble_win",
            "card_name": str(card.get("name", "Unknown")),
            "rarity": format_rarity(card.get("rarity", "Common")),
            "time": round(elapsed, 2), "earned": earned, "amount": paid,
            "chat_id": chat_id, "chat_title": chat_title,
        }
        if moves is not None:
            entry["moves"] = moves
        log_action(db, user_id, entry)
    except Exception as e:
        dlog.error(f"[scramble_vlog] {e}", exc_info=True)
    save_db()
    return paid


def _scramble_caption(game: dict, selected: int | None = None) -> str:
    hint = (f"Swap <b>{selected + 1}</b> with…? Tap another number."
            if selected is not None else "Tap two numbers to swap those pieces.")
    return (
        "<b>「 SCRAMBLE 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Put the card back together!\n"
        f"<b>Moves:</b> {game['moves']}\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<i>{hint}</i>"
    )


def _scramble_end_caption(game: dict, won: bool, reward_text: str = "") -> str:
    head = "「 SCRAMBLE SOLVED! 」" if won else "「 SCRAMBLE GAVE UP 」"
    lines = (
        f"<b>{head}</b>\n━━━━━━━━━━━━━━━━━\n"
        f"<b>Character :</b> {_html_esc(str(game['name']))}\n"
        f"<b>Rarity :</b> {format_rarity(game['rarity'])}\n"
        f"<b>Anime :</b> {_html_esc(str(game['anime']))}\n"
    )
    if won:
        lines += (
            f"<b>Moves :</b> {game['moves']}\n"
            f"<b>Time :</b> {_scramble_time(game['finished'] - game['started'])}\n"
            f"{reward_text}"
        )
    return lines


def _scramble_chat_game(chat_id: int):
    """The running puzzle in this chat, if any (expired ones are cleaned out first)."""
    _scramble_purge()
    for g in _scramble_games.values():
        if g["chat_id"] == chat_id:
            return g
    return None


def _scramble_game_link(game: dict):
    """Link to the puzzle message inside a group, or None (private chats have no links)."""
    mid, cid = game.get("message_id"), game.get("chat_id")
    if not mid or not cid:
        return None
    if game.get("chat_username"):
        return f"https://t.me/{game['chat_username']}/{mid}"
    c = str(cid)
    if c.startswith("-100"):
        return f"https://t.me/c/{c[4:]}/{mid}"
    return None


async def _scramble_bot_link() -> str:
    global _scramble_bot_username
    if not _scramble_bot_username:
        _scramble_bot_username = (await bot.get_me()).username
    return f"https://t.me/{_scramble_bot_username}"


def _scr_url_btn(text: str, url: str, style: str | None = None):
    if style and _SCR_HAS_STYLE:
        return InlineKeyboardButton(text=text, url=url, style=style)
    return InlineKeyboardButton(text=text, url=url)


async def _scramble_busy_kb(game: dict | None, dm_button: bool):
    row = []
    if dm_button:
        row.append(_scr_url_btn("Play in DM", await _scramble_bot_link(), "primary"))
    link = _scramble_game_link(game) if game else None
    if link:
        row.append(_scr_url_btn("View Game", link, "success"))
    return InlineKeyboardMarkup(inline_keyboard=[row]) if row else None


@main_router.message(Command("scramble"))
async def scramble_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    if _scramble_is_banned(ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username), uid_int):
        await message.reply("You are banned from Scramble.")
        return

    is_group = message.chat.type != ChatType.PRIVATE
    chat_id = message.chat.id

    # One puzzle per player at a time.
    _, mine = _scramble_active_game(uid_int)
    if mine or uid_int in _scramble_starting:
        await message.reply(
            "You already have a scramble running!\n"
            "Finish it, or tap <b>Give Up</b> on it, before starting another.",
            reply_markup=await _scramble_busy_kb(mine, dm_button=False),
            parse_mode=ParseMode.HTML)
        return

    # One puzzle per group chat at a time.
    if is_group:
        other = _scramble_chat_game(chat_id)
        if other or chat_id in _scramble_starting_chats:
            who = f"<b>{_html_esc(other['owner_name'])}</b>" if other else "Someone"
            await message.reply(
                f"{who} is already playing a scramble in this group.\n"
                "Please play in the bot's DMs for a lag free experience.",
                reply_markup=await _scramble_busy_kb(other, dm_button=True),
                parse_mode=ParseMode.HTML)
            return

    _scramble_starting.add(uid_int)   # reserve the slots while the board is being built
    if is_group:
        _scramble_starting_chats.add(chat_id)
    gid = None
    loading = None
    try:
        loading = await message.reply("Loading your scrambled card..")
        user_id = str(uid_int)
        db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
        global_cards = db.get("global_cards", {})

        # Take a ready card from the pool (instant). Cold pool: build one on demand.
        cid, base = await _scramble_take_wait(db)
        if cid is None:
            cands = _scramble_candidates(db)
            if not cands:
                await loading.edit_text("There are no cards to scramble yet.")
                loading = None
                _scramble_kick_refill(db)
                return
            cid = random.choice(cands)
            base = await _scramble_fetch(global_cards[cid]["file_id"])
        _scramble_recent.append(cid)   # never offered again until it ages out of the recent list
        g = global_cards[cid]
        perm = _scramble_shuffle(SCRAMBLE_COLS * SCRAMBLE_ROWS)
        img = await asyncio.to_thread(_scramble_render, base, perm)

        _scramble_purge()
        gid = secrets.token_hex(4)
        now = time.time()
        game = {
            "owner": uid_int, "owner_name": str(message.from_user.first_name or "A player")[:24],
            "chat_id": chat_id, "chat_username": getattr(message.chat, "username", None), "message_id": None, "base": base, "perm": perm,
            "selected": None, "moves": 0, "started": now, "touched": now,
            "last_click": 0.0, "pending": 0, "dirty": False, "strikes": 0, "locked_until": 0.0, "lock": asyncio.Lock(),
            "name": g.get("name", "Card"), "rarity": g.get("rarity", "Common"),
            "anime": g.get("anime", "Unknown"),
        }
        _scramble_games[gid] = game
        _scr_stat(ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username),
                  "start", uid=uid_int)
        _scr_log(db, "start", uid_int, mode="chat", chat=("group" if is_group else "dm"))

        sent = await message.reply_photo(
            photo=BufferedInputFile(img, filename="scramble.jpg"),
            caption=_scramble_caption(game),
            reply_markup=_scramble_kb(gid),
            parse_mode=ParseMode.HTML
        )
        game["message_id"] = sent.message_id
        _scr_bg(loading.delete())
        loading = None
        game["started"] = game["touched"] = time.time()   # clock starts once it's on screen

        _scramble_kick_refill(db)   # pool at/below the low mark -> refill in the background
    except Exception as e:
        if gid:
            _scramble_games.pop(gid, None)   # never leave a dead puzzle blocking the player
        print(f"[scramble_CRASH] {e}")
        traceback.print_exc()
        dlog.error(f"[scramble_CRASH] {e}", exc_info=True)
        err = "Couldn't build the puzzle right now. Please try again in a moment."
        try:
            if loading:
                await loading.edit_text(err)
            else:
                await message.reply(err)
        except Exception:
            pass
    finally:
        _scramble_starting.discard(uid_int)
        _scramble_starting_chats.discard(chat_id)


async def _scramble_push(cq: CallbackQuery, gid: str, game: dict):
    """Redraw the board message. Re-renders the image only if pieces moved since the last draw."""
    if game.get("dirty"):
        img = await asyncio.to_thread(_scramble_render, game["base"], game["perm"], True)
        await cq.message.edit_media(
            media=InputMediaPhoto(media=BufferedInputFile(img, filename="scramble.jpg"),
                                  caption=_scramble_caption(game, game["selected"]),
                                  parse_mode=ParseMode.HTML),
            reply_markup=_scramble_kb(gid, game["selected"]))
        game["dirty"] = False
    else:
        await cq.message.edit_caption(
            caption=_scramble_caption(game, game["selected"]),
            reply_markup=_scramble_kb(gid, game["selected"]),
            parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("scr:"))
async def scramble_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id): return
    if _scramble_is_banned(ensure_user(str(cq.from_user.id), cq.from_user.first_name, cq.from_user.username), cq.from_user.id):
        await cq.answer("You are banned from Scramble.", show_alert=True)
        return
    try:
        _, gid, action = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return

    game = _scramble_games.get(gid)
    if not game or time.time() - game["touched"] > SCRAMBLE_TTL:
        _scramble_games.pop(gid, None)
        if gid in _scramble_done:   # finished a moment ago: late taps from a fast burst, ignore quietly
            await cq.answer()
            return
        await cq.answer("This puzzle has expired. Send /scramble for a new one.", show_alert=True)
        return
    if cq.from_user.id != game["owner"]:
        await cq.answer("This puzzle belongs to someone else. Send /scramble for your own.", show_alert=True)
        return

    # ── Flood guard ──
    now = time.time()
    if now < game["locked_until"]:
        await cq.answer(f"Too fast! Wait {int(game['locked_until'] - now) + 1}s.")
        return
    if game["pending"] >= SCRAMBLE_MAX_PENDING:   # board can't keep up: refuse the extra tap
        game["strikes"] += 1
        if game["strikes"] >= SCRAMBLE_FLOOD_STRIKES:
            game["strikes"] = 0
            game["locked_until"] = now + SCRAMBLE_FLOOD_LOCK
            _scr_log_once(ensure_user(str(cq.from_user.id), cq.from_user.first_name, cq.from_user.username),
                          "flood_lock", cq.from_user.id, mode="chat")
            await cq.answer(f"Too fast! Buttons locked for {int(SCRAMBLE_FLOOD_LOCK)}s.", show_alert=True)
        else:
            await cq.answer()   # dropped silently, instant
        return
    game["strikes"] = 0
    game["pending"] += 1

    # Acknowledge right away so the button stops spinning; the redraw follows.
    try:
        await cq.answer()
    except Exception:
        pass

    try:
        async with game["lock"]:   # taps are applied one at a time, in the order they arrived
            if gid not in _scramble_games:   # finished while we waited on the lock
                return
            game["touched"] = time.time()
            n = SCRAMBLE_COLS * SCRAMBLE_ROWS
            more = game["pending"] > 1   # more taps already waiting -> skip this redraw, the last one draws

            # ── Give up: reveal the finished picture ──
            if action == "give":
                _gdb = ensure_user(str(cq.from_user.id), cq.from_user.first_name, cq.from_user.username)
                _scr_stat(_gdb, "giveup", uid=cq.from_user.id)
                _scr_log(_gdb, "giveup", cq.from_user.id, mode="chat", moves=game["moves"], card=game["name"])
                _scramble_games.pop(gid, None)
                _scramble_mark_done(gid)
                img = await asyncio.to_thread(_scramble_render, game["base"], list(range(n)), False)
                await cq.message.edit_media(
                    media=InputMediaPhoto(media=BufferedInputFile(img, filename="scramble.jpg"),
                                          caption=_scramble_end_caption(game, won=False),
                                          parse_mode=ParseMode.HTML),
                    reply_markup=None)
                return

            try:
                idx = int(action)
            except ValueError:
                return
            if not 0 <= idx < n:
                return

            sel = game["selected"]

            # First tap (or tapping the selected piece again): just update the highlight.
            if sel is None or sel == idx:
                game["selected"] = idx if sel is None else None
                if not more:
                    await _scramble_push(cq, gid, game)
                return

            # Second tap: swap the two pieces.
            perm = game["perm"]
            perm[sel], perm[idx] = perm[idx], perm[sel]
            game["selected"] = None
            game["moves"] += 1
            game["dirty"] = True
            solved = perm == list(range(n))

            if not solved:
                if not more:
                    await _scramble_push(cq, gid, game)
                return

            # Solved: always draw the win screen, even mid-burst.
            _scramble_games.pop(gid, None)
            _scramble_mark_done(gid)
            game["finished"] = time.time()   # stop the clock before rendering/uploading
            earned = _scramble_reward_for(game["finished"] - game["started"])
            paid = _scramble_settle(str(cq.from_user.id), cq.from_user.first_name,
                                    cq.from_user.username,
                                    game["finished"] - game["started"], earned,
                                    mode="chat", card={"name": game["name"], "rarity": game["rarity"]},
                                    moves=game["moves"], chat_id=game["chat_id"],
                                    chat_title=getattr(cq.message.chat, "title", None) or "Private chat")
            _scr_log(ensure_user(str(cq.from_user.id), cq.from_user.first_name, cq.from_user.username), "solve",
                     cq.from_user.id, mode="chat", time=round(game["finished"] - game["started"], 2),
                     moves=game["moves"], paid=paid, earned=earned, card=game["name"])
            if paid > 0:
                reward_text = f"<b>Reward :</b> +{paid} Shards\n"
            elif earned > 0:
                reward_text = "<i>Daily reward cap reached</i>\n"
            else:
                reward_text = "<i>No shards - solve under 2 min to earn some.</i>\n"
            img = await asyncio.to_thread(_scramble_render, game["base"], perm, False)
            await cq.message.edit_media(
                media=InputMediaPhoto(
                    media=BufferedInputFile(img, filename="scramble.jpg"),
                    caption=_scramble_end_caption(game, won=True, reward_text=reward_text),
                    parse_mode=ParseMode.HTML),
                reply_markup=None)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[scramble_cb] failed: {e}")
            traceback.print_exc()
            dlog.error(f"[scramble_cb] failed: {e}", exc_info=True)
    finally:
        game["pending"] = max(0, game["pending"] - 1)


# ==========================================
# WEB MODE — Telegram Mini App (scramble.html)
# ==========================================
# Same stack as the deck / chicken Mini Apps: the routes live on deck_api (FastAPI) at
#   /api/deck/scramble/*      and scramble.html is hosted on Netlify next to chicken.html.
# BotFather -> /newapp -> short name "scramble" -> Web App URL = where scramble.html is hosted.
# IMPORTANT: import this module BEFORE the app calls include_router(deck_api); routes added
# after that are not picked up. Check it: open <BACKEND>/api/deck/scramble/ping -> {"ok": true}
# The server times every run itself and verifies Telegram's signed initData, so players
# can't send fake times. Shards use the same daily minigame cap as chat mode.
SCRAMBLE_WEB_LINK = "https://t.me/Animenx_bot/scramble"   # Mini App direct link
SCRAMBLE_WEB_REWARD_TIERS = [(20, 50), (40, 25)]           # web mode: dragging is fast, so tighter limits
# ── Anti-cheat knobs (web mode) ──
SCRAMBLE_WEB_MIN_SECONDS = 4            # no human solves a 9-piece board faster than this
SCRAMBLE_WEB_MIN_PER_SWAP = 0.3         # total time must be >= swaps * this (macros fire swaps instantly)
SCRAMBLE_WEB_MAX_SWAPS = 150            # a run that needs more swaps than this is thrown away
SCRAMBLE_WEB_START_GAP = 1.0            # min seconds between two /start calls from one player
SCRAMBLE_WEB_MAX_SOLVES_PER_HOUR = 120  # solves beyond this still show the card but count for nothing
SCRAMBLE_WEB_FLAG_STDEV = 0.03          # swap gaps this even (seconds) = machine timing -> flagged for review
# run token -> {uid, started, card, perm0, perm, moves, stamps, last, last_resp, done}
# The SERVER owns the shuffle and replays every swap, so "solved" is decided here, never by the browser.
# ── Captcha (web mode): spawns at random when a run starts; failing it = banned from Scramble ──
SCRAMBLE_CAPTCHA_CHANCE = 0.10          # chance a /start is answered with a captcha first
SCRAMBLE_CAPTCHA_CHANCE_FLAGGED = 0.50  # same, for players who have been flagged (too fast / robotic)
SCRAMBLE_CAPTCHA_TRIES = 3              # wrong answers allowed (a NEW, different challenge follows each) before the ban
SCRAMBLE_CAPTCHA_TTL = 60               # seconds a challenge stays valid (an expired one is just replaced)
SCRAMBLE_CAPTCHA_STAGES = 2             # challenges in a row (always different types) a normal player must pass
SCRAMBLE_CAPTCHA_STAGES_FLAGGED = 3     # same, for flagged players
SCRAMBLE_CAPTCHA_MIN_SOLVE = 1.0        # answering faster than this (seconds after the image was sent) = a bot -> counts as wrong
SCRAMBLE_CAPTCHA_MAX_SKIPS = 3          # captchas ignored in a row (start again without answering) before the ban
_SCR_CAPTCHA_CHARS = "ACDEFGHJKLMNPRTUVWXY346789"   # no look-alikes (0/O, 1/I, 5/S, 2/Z, 8/B)
_scramble_captchas: dict = {}            # uid -> {id, code, expires, tries}
_scramble_web_runs: dict = {}
_scramble_web_last_start: dict = {}      # uid -> last /start time
_scramble_web_solves: dict = {}          # uid -> deque of recent counted-solve times


class ScrWebReq(BaseModel):
    init_data: str = ""
    run: str = ""
    tab: str = "time"
    a: int = -1      # /swap: board position of the first piece
    b: int = -1      # /swap: board position of the second piece
    seq: int = 0     # /swap: 1, 2, 3 ... order of this swap within the run
    cid: str = ""    # /captcha: which challenge is being answered
    answer: str = "" # /captcha: typed text / picked number
    taps: list[list[float]] = []   # /captcha: tap positions (0..1 of the image), in the order tapped


def _scramble_web_user(init_data: str):
    """Verify Telegram WebApp initData (HMAC) -> user dict, or None if invalid/stale."""
    try:
        pairs = dict(parse_qsl(init_data or "", keep_blank_values=True))
        got = pairs.pop("hash", None)
        if not got:
            return None
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", bot.token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got):
            return None
        if time.time() - int(pairs.get("auth_date", "0")) > 86400:
            return None
        return json.loads(pairs.get("user", "{}"))
    except Exception:
        return None


def _scramble_web_auth(req: ScrWebReq) -> dict:
    u = _scramble_web_user(req.init_data)
    if not u or "id" not in u:
        raise HTTPException(status_code=401, detail="Invalid Telegram session.")
    if is_ghost_banned(int(u["id"])) or is_shadow_banned(int(u["id"])):
        raise HTTPException(status_code=403, detail="Not allowed.")
    db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    if _scramble_is_banned(db, u["id"]):
        _scr_log_once(db, "banned_attempt", u["id"], mode="web")
        raise HTTPException(status_code=403, detail="You are banned from Scramble.")
    return u


def _scramble_web_run(req: ScrWebReq, u: dict, pop: bool):
    run = _scramble_web_runs.get(req.run)
    if not run or run["uid"] != str(u["id"]):
        raise HTTPException(status_code=401, detail="Unknown run.")
    if pop:
        _scramble_web_runs.pop(req.run, None)   # one-time token: no replays
    return run


@deck_api.get("/scramble/ping")
async def scramble_web_ping():
    return {"ok": True}


def _scramble_web_tiles(base: bytes, perm: list):
    """Cut the card into separate tile images, listed in BOARD ORDER (position 0 first).
    The browser never receives the full picture or the piece numbers, so there is nothing to
    read out of the page: it can only draw tiles and report which two positions were swapped."""
    src = Image.open(io.BytesIO(base)).convert("RGB")
    w, h = src.size
    tw, th = w // SCRAMBLE_COLS, h // SCRAMBLE_ROWS
    out = []
    for piece in perm:
        sx, sy = (piece % SCRAMBLE_COLS) * tw, (piece // SCRAMBLE_COLS) * th
        buf = io.BytesIO()
        src.crop((sx, sy, sx + tw, sy + th)).save(buf, "JPEG", quality=80)
        out.append("data:image/jpeg;base64," + base64.b64encode(buf.getvalue()).decode())
    return out, w / h


def _scramble_flag(db: dict, uid: str, name: str, reason: str, **info):
    """Mark a suspicious run for admin review (shows in /vlog). Never blocks the request."""
    try:
        rec = db["users"][uid].setdefault("scramble", {})
        rec["flags"] = rec.get("flags", 0) + 1
        log_action(db, uid, {"type": "scramble_flag", "reason": reason, "name": name, **info})
        _scr_log(db, reason, uid, name, mode="web", **info)
        _scr_save_soon()
    except Exception as e:
        dlog.error(f"[scramble_flag] {e}", exc_info=True)


# ==========================================
# BANS + CAPTCHA
# ==========================================
def _scramble_is_banned(db: dict, uid) -> bool:
    u = (db.get("users") or {}).get(str(uid))
    rec = u.get("scramble") if isinstance(u, dict) else None
    return bool(isinstance(rec, dict) and rec.get("banned"))


def _scramble_ban_list(db: dict) -> list:
    """[(uid, name, info)] newest ban first."""
    rows = []
    for uid, u in (db.get("users") or {}).items():
        rec = u.get("scramble") if isinstance(u, dict) else None
        if isinstance(rec, dict) and rec.get("banned"):
            rows.append((str(uid), str(u.get("name") or "User"), rec["banned"]))
    rows.sort(key=lambda r: -(r[2].get("at") or 0))
    return rows


async def _scramble_ban(db: dict, uid: str, reason: str, by="auto"):
    """Ban a player from Scramble (chat + web, hidden from the leaderboards) and end their runs."""
    rec = db["users"][uid].setdefault("scramble", {})
    rec["banned"] = {"at": int(time.time()), "reason": reason, "by": by}
    for k, v in list(_scramble_web_runs.items()):
        if v["uid"] == uid:
            _scramble_web_runs.pop(k, None)
    _scramble_captchas.pop(uid, None)
    gid, _g = _scramble_active_game(int(uid))
    if gid:
        _scramble_games.pop(gid, None)
    try:
        log_action(db, uid, {"type": "scramble_ban", "reason": reason, "by": str(by)})
    except Exception as e:
        dlog.error(f"[scramble_ban_log] {e}", exc_info=True)
    _scr_log(db, "ban", uid, reason=reason, by=by)
    _scr_save_soon()
    _scr_bg(bot.send_message(int(uid), "You have been banned from Scramble."))   # don't make the 403 wait on Telegram


async def _scramble_unban(db: dict, uid: str, by=None) -> bool:
    u = (db.get("users") or {}).get(uid)
    rec = u.get("scramble") if isinstance(u, dict) else None
    if not (isinstance(rec, dict) and rec.get("banned")):
        return False
    rec.pop("banned", None)
    rec["flags"] = 0            # clean slate: no extra captchas for them afterwards
    rec["captcha_skips"] = 0
    _scr_log(db, "unban", uid, by=by)
    _scr_save_soon()
    _scr_bg(bot.send_message(int(uid), "You have been unbanned from Scramble. Welcome back!"))
    return True


# ── Captcha challenges: five different types, picked at random, chained ──
#   text   distorted code, typed             math   distorted sum, typed
#   count  "how many red stars?" (pick)      point  "tap the blue diamond" (position)
#   order  "tap smallest to largest" digits scattered around (positions, in order)
# Instructions live INSIDE the picture, answers never leave the server, every challenge is
# one-use, and an answer sent faster than a human could read it counts as wrong.
_SCR_CAP_W, _SCR_CAP_H, _SCR_CAP_BAR = 320, 250, 38
_SCR_CAP_COLORS = {"red": (214, 48, 49), "blue": (30, 110, 230), "green": (30, 160, 80),
                   "yellow": (232, 190, 0), "purple": (140, 60, 200)}
_SCR_CAP_SHAPES = ("circle", "square", "triangle", "star", "diamond")
_SCR_CAP_KINDS = ("text", "math", "count", "point", "order")


def _scr_cap_bg(W: int, H: int):
    c1 = tuple(random.randint(205, 245) for _ in range(3))
    c2 = tuple(random.randint(185, 240) for _ in range(3))
    img = Image.new("RGB", (W, H), c1)
    d = ImageDraw.Draw(img)
    for y in range(0, H, 2):
        t = y / H
        d.line((0, y, W, y), fill=tuple(int(c1[i] * (1 - t) + c2[i] * t) for i in range(3)), width=2)
    for _ in range(W * H // 110):
        d.point((random.randint(0, W - 1), random.randint(0, H - 1)), fill=(random.randint(120, 200),) * 3)
    return img


def _scr_cap_lines(img, n: int, alpha: int = 150, top: int = 0):
    """Translucent lines and arcs across the picture (below `top` is left alone)."""
    W, H = img.size
    ov = Image.new("RGBA", img.size, (0, 0, 0, 0))
    d = ImageDraw.Draw(ov)
    for _ in range(n):
        col = (random.randint(20, 170), random.randint(20, 170), random.randint(20, 170), alpha)
        if random.random() < 0.55:
            d.line((random.randint(0, W), random.randint(top, H), random.randint(0, W), random.randint(top, H)),
                   fill=col, width=random.choice((1, 2)))
        else:
            x, y = random.randint(-20, W - 40), random.randint(top - 20, H - 40)
            d.arc((x, y, x + random.randint(60, 200), y + random.randint(40, 140)),
                  random.randint(0, 180), random.randint(181, 360), fill=col, width=2)
    return Image.alpha_composite(img.convert("RGBA"), ov).convert("RGB")


def _scr_cap_jpeg(img) -> bytes:
    out = io.BytesIO()
    img.save(out, "JPEG", quality=85)
    return out.getvalue()


def _scr_cap_wave(img, amp: float):
    W, H = img.size
    out = img.copy()
    ph, per = random.uniform(0, 6.28), random.uniform(38, 70)
    for x in range(W):
        out.paste(img.crop((x, 0, x + 1, H)), (x, int(amp * math.sin(2 * math.pi * x / per + ph))))
    return out


def _scr_cap_text_image(text: str, size=(40, 50), rot: float = 30, amp=(3, 5), strikes: int = 2):
    """Characters rotated, resized and jittered, struck through in the text's own colours, then wave-warped.
    Characters stay dark so a person can read them; it is the combination of tricks that defeats OCR."""
    W, H = 280, 96
    img = _scr_cap_bg(W, H)
    step = (W - 40) / len(text)
    x = 20 + step / 2
    for ch in text:
        layer = Image.new("RGBA", (84, 92), (0, 0, 0, 0))
        col = (random.randint(0, 80), random.randint(0, 80), random.randint(0, 80), 255)
        ImageDraw.Draw(layer).text((42, 46), ch, font=_scramble_font(random.randint(*size)), anchor="mm", fill=col)
        layer = layer.rotate(random.uniform(-rot, rot), resample=Image.BICUBIC)
        img.paste(layer, (int(x - 42) + random.randint(-3, 3), H // 2 - 46 + random.randint(-6, 6)), layer)
        x += step
    d = ImageDraw.Draw(img)
    for _ in range(strikes):   # strike-through lines in dark, text-like colours
        d.line((random.randint(0, 40), random.randint(20, H - 20), random.randint(W - 40, W), random.randint(20, H - 20)),
               fill=(random.randint(30, 110),) * 3, width=2)
    img = _scr_cap_wave(img, random.uniform(*amp))
    return _scr_cap_lines(img, 5, alpha=170)


def _scr_cap_build_text() -> dict:
    code = "".join(random.choice(_SCR_CAPTCHA_CHARS) for _ in range(5))
    return {"image": _scr_cap_jpeg(_scr_cap_text_image(code)), "mode": "type", "input": "text",
            "hint": "Type the code", "answer": code}


def _scr_cap_build_math() -> dict:
    op = random.choice(("+", "-", "x"))
    if op == "+":
        a, b = random.randint(3, 19), random.randint(2, 9); ans = a + b
    elif op == "-":
        a, b = random.randint(11, 24), random.randint(2, 9); ans = a - b
    else:
        a, b = random.randint(2, 9), random.randint(2, 9); ans = a * b
    return {"image": _scr_cap_jpeg(_scr_cap_text_image(f"{a}{op}{b}=?", size=(36, 44), rot=16, amp=(2, 3.5), strikes=1)), "mode": "type",
            "input": "numeric", "hint": "Solve it and type the answer", "answer": str(ans)}


def _scr_cap_shape(d, kind: str, cx: float, cy: float, r: float, color, angle: float):
    edge = tuple(max(0, c - 70) for c in color)
    if kind == "circle":
        d.ellipse((cx - r, cy - r, cx + r, cy + r), fill=color, outline=edge, width=2)
        return
    if kind == "square":
        spec = [(r * 0.95, 45 + 90 * i) for i in range(4)]
    elif kind == "triangle":
        spec = [(r * 1.1, -90 + 120 * i) for i in range(3)]
    elif kind == "diamond":
        spec = [(r * (1.05 if i % 2 == 0 else 0.65), 90 * i) for i in range(4)]
    else:   # star
        spec = [(r * (1.1 if i % 2 == 0 else 0.48), -90 + 36 * i) for i in range(10)]
    a0 = math.radians(angle)
    d.polygon([(cx + rad * math.cos(math.radians(deg) + a0), cy + rad * math.sin(math.radians(deg) + a0))
               for rad, deg in spec], fill=color, outline=edge)


def _scr_cap_place(n: int, r: float, min_d: float) -> list:
    """n random spots in the play area (below the instruction bar), kept apart from each other."""
    W, H, BAR = _SCR_CAP_W, _SCR_CAP_H, _SCR_CAP_BAR
    pts = []
    for dist in (min_d, min_d * .85, min_d * .7, min_d * .55):
        pts = []
        for _ in range(700):
            p = (random.uniform(r + 4, W - r - 4), random.uniform(BAR + r + 4, H - r - 4))
            if all(math.hypot(p[0] - q[0], p[1] - q[1]) >= dist for q in pts):
                pts.append(p)
                if len(pts) == n:
                    return pts
    return pts


def _scr_cap_header(img, text: str):
    """Dark bar on top carrying the instruction, drawn character by character with a little jitter."""
    W = img.width
    d = ImageDraw.Draw(img)
    d.rectangle((0, 0, W, _SCR_CAP_BAR), fill=(28, 30, 42))
    for fs in (17, 16, 15, 14, 13):
        font = _scramble_font(fs)
        widths = [d.textlength(ch, font=font) for ch in text]
        if sum(widths) <= W - 16:
            break
    x = (W - sum(widths)) / 2
    for ch, w in zip(text, widths):
        d.text((x, _SCR_CAP_BAR / 2 + random.randint(-1, 1)), ch, font=font, anchor="lm", fill=(240, 235, 220))
        x += w
    return img


def _scr_cap_scene(placed: list, prompt: str):
    W, H = _SCR_CAP_W, _SCR_CAP_H
    img = _scr_cap_lines(_scr_cap_bg(W, H), 5, alpha=120, top=_SCR_CAP_BAR)
    d = ImageDraw.Draw(img)
    for it in random.sample(placed, len(placed)):   # random drawing order
        col = tuple(max(0, min(255, c + random.randint(-14, 14))) for c in _SCR_CAP_COLORS[it["c"]])
        _scr_cap_shape(d, it["s"], it["x"], it["y"], it["r"], col, it["a"])
    img = _scr_cap_lines(img, 6, alpha=110, top=_SCR_CAP_BAR)   # thin lines over the shapes
    return _scr_cap_header(img, prompt)


def _scr_cap_items(items: list, r_range=(19, 25), min_d: float = 62) -> list:
    pos = _scr_cap_place(len(items), 26, min_d)
    return [{"c": c, "s": s, "x": x, "y": y, "r": random.randint(*r_range), "a": random.uniform(0, 360)}
            for (c, s), (x, y) in zip(items, pos)]


def _scr_cap_build_point() -> dict:
    cols = list(_SCR_CAP_COLORS)
    tc, ts = random.choice(cols), random.choice(_SCR_CAP_SHAPES)
    items = [(tc, ts),   # the target comes first; one same-colour and one same-shape decoy are always present
             (tc, random.choice([x for x in _SCR_CAP_SHAPES if x != ts])),
             (random.choice([c for c in cols if c != tc]), ts)]
    while len(items) < 9:
        c, sh = random.choice(cols), random.choice(_SCR_CAP_SHAPES)
        if (c, sh) != (tc, ts):
            items.append((c, sh))
    placed = _scr_cap_items(items)
    t = placed[0]
    img = _scr_cap_scene(placed, f"TAP THE {tc} {ts}".upper())
    return {"image": _scr_cap_jpeg(img), "mode": "tap", "need": 1, "hint": "Follow the instruction on the image",
            "answer": {"x": t["x"], "y": t["y"], "r": t["r"] + 9}}


def _scr_cap_build_count() -> dict:
    cols = list(_SCR_CAP_COLORS)
    tc, ts = random.choice(cols), random.choice(_SCR_CAP_SHAPES)
    n = random.randint(2, 5)
    items = [(tc, ts)] * n
    items += [(tc, random.choice([x for x in _SCR_CAP_SHAPES if x != ts])) for _ in range(random.randint(2, 3))]
    items += [(random.choice([c for c in cols if c != tc]), ts) for _ in range(random.randint(2, 3))]
    placed = _scr_cap_items(items, r_range=(18, 23), min_d=58)
    img = _scr_cap_scene(placed, f"HOW MANY {tc} {ts}S?".upper())
    return {"image": _scr_cap_jpeg(img), "mode": "buttons", "options": [str(i) for i in range(1, 10)],
            "hint": "Pick the right number", "answer": str(n)}


def _scr_cap_build_order() -> dict:
    W, H = _SCR_CAP_W, _SCR_CAP_H
    digits = random.sample([1, 2, 3, 4, 5, 7, 8], 5)
    asc = random.random() < 0.5
    pos = _scr_cap_place(5, 30, 70)
    img = _scr_cap_lines(_scr_cap_bg(W, H), 4, alpha=120, top=_SCR_CAP_BAR)
    d = ImageDraw.Draw(img)
    for dg, (x, y) in zip(digits, pos):
        r = 25
        d.ellipse((x - r, y - r, x + r, y + r), fill=tuple(random.randint(150, 235) for _ in range(3)),
                  outline=(random.randint(20, 90),) * 3, width=2)
        layer = Image.new("RGBA", (70, 70), (0, 0, 0, 0))
        ImageDraw.Draw(layer).text((35, 35), str(dg), font=_scramble_font(random.randint(28, 34)), anchor="mm",
                                   fill=(random.randint(0, 70), random.randint(0, 70), random.randint(0, 70), 255))
        layer = layer.rotate(random.uniform(-35, 35), resample=Image.BICUBIC)
        img.paste(layer, (int(x - 35), int(y - 35)), layer)
    img = _scr_cap_lines(img, 7, alpha=120, top=_SCR_CAP_BAR)
    img = _scr_cap_header(img, "TAP SMALLEST TO LARGEST" if asc else "TAP LARGEST TO SMALLEST")
    order = sorted(zip(digits, pos), key=lambda t: t[0], reverse=not asc)
    return {"image": _scr_cap_jpeg(img), "mode": "tap", "need": 5, "hint": "Follow the instruction on the image",
            "answer": {"pts": [p for _d, p in order], "r": 30}}


_SCR_CAP_BUILDERS = {"text": _scr_cap_build_text, "math": _scr_cap_build_math, "count": _scr_cap_build_count,
                     "point": _scr_cap_build_point, "order": _scr_cap_build_order}


def _scr_cap_check(ch: dict, answer: str, taps: list) -> bool:
    """Is the answer to this challenge right? (Never raises.)"""
    try:
        kind, ans = ch["kind"], ch["answer"]
        if kind == "text":
            return hmac.compare_digest(str(answer).strip().upper().encode(), ans.encode())
        if kind in ("math", "count"):
            return hmac.compare_digest(str(answer).strip().encode(), str(ans).encode())
        pts = [(float(t[0]) * _SCR_CAP_W, float(t[1]) * _SCR_CAP_H) for t in (taps or [])[:12] if len(t) >= 2]
        if not all(math.isfinite(x) and math.isfinite(y) for x, y in pts):
            return False
        if kind == "point":
            return len(pts) == 1 and math.hypot(pts[0][0] - ans["x"], pts[0][1] - ans["y"]) <= ans["r"]
        if kind == "order":
            return len(pts) == len(ans["pts"]) and all(
                math.hypot(px - ax, py - ay) <= ans["r"] for (px, py), (ax, ay) in zip(pts, ans["pts"]))
    except Exception:
        pass
    return False


async def _scramble_captcha_issue(uid: str, tries_used: int = 0, stage: int = 1,
                                  stages: int = SCRAMBLE_CAPTCHA_STAGES, last_kind: str | None = None) -> dict:
    """New challenge for this player (replaces any earlier one). Never the same type twice in a row.
    The answer never leaves the server."""
    kind = random.choice([k for k in _SCR_CAP_KINDS if k != last_kind])
    spec = await asyncio.to_thread(_SCR_CAP_BUILDERS[kind])   # PIL work must not block the bot
    cid, now = secrets.token_hex(6), time.time()
    _scramble_captchas[uid] = {"id": cid, "kind": kind, "answer": spec["answer"], "issued": now,
                               "expires": now + SCRAMBLE_CAPTCHA_TTL, "tries": tries_used,
                               "stage": stage, "stages": stages}
    out = {"id": cid, "mode": spec["mode"], "hint": spec["hint"], "tries_left": SCRAMBLE_CAPTCHA_TRIES - tries_used,
           "stage": stage, "stages": stages,
           "image": "data:image/jpeg;base64," + base64.b64encode(spec["image"]).decode()}
    for k in ("need", "options", "input"):
        if k in spec:
            out[k] = spec[k]
    return out


def _scramble_captcha_due(db: dict, uid: str) -> bool:
    rec = db["users"][uid].get("scramble") or {}
    chance = SCRAMBLE_CAPTCHA_CHANCE_FLAGGED if rec.get("flags", 0) > 0 else SCRAMBLE_CAPTCHA_CHANCE
    return random.random() < chance


async def _scramble_web_launch(uid: str, db: dict) -> dict:
    """Pick a real card, shuffle it HERE, cut it into tiles, and start the clock as the tiles go out."""
    now = time.time()
    for k, v in list(_scramble_web_runs.items()):   # expire old runs + one run per player
        if now - v["started"] > SCRAMBLE_TTL or v["uid"] == uid:
            _scramble_web_runs.pop(k, None)
    cid, base = await _scramble_take_wait(db)
    if cid is None:                                  # cold pool: build one on demand
        cands = _scramble_candidates(db)
        if not cands:
            _scramble_kick_refill(db)
            return {"ok": False, "error": "no_cards"}
        cid = random.choice(cands)
        base = await _scramble_fetch(db["global_cards"][cid]["file_id"])
    _scramble_recent.append(cid)
    _scramble_kick_refill(db)
    g = db["global_cards"][cid]
    _scr_stat(db, "start", uid=uid)
    _scr_log(db, "start", uid, mode="web")
    perm = _scramble_shuffle(SCRAMBLE_COLS * SCRAMBLE_ROWS)
    tiles, ar = await asyncio.to_thread(_scramble_web_tiles, base, perm)
    run = secrets.token_hex(8)
    _scramble_web_runs[run] = {
        "uid": uid, "started": time.time(),   # the clock starts here, when the tiles are sent
        "card": {"name": str(g.get("name", "Card")), "rarity": str(g.get("rarity", "Common")),
                 "anime": str(g.get("anime", "Unknown"))},
        "perm0": list(perm), "perm": list(perm), "moves": 0, "stamps": [],
        "last": None, "last_resp": None, "done": False}
    return {"ok": True, "run": run, "tiles": tiles, "ar": ar}


@deck_api.post("/scramble/warm")
async def scramble_web_warm(req: ScrWebReq):
    """Called by scramble.html while its intro plays: fills the card pool so the first board is instant."""
    u = _scramble_web_auth(req)
    db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    _scramble_kick_refill(db, low=SCRAMBLE_POOL_SIZE - 1)
    return {"ok": True, "ready": len(_scramble_pool)}


@deck_api.post("/scramble/start")
async def scramble_web_start(req: ScrWebReq):
    """Starts a run - or, now and then, a captcha first (the puzzle is only sent once it is answered)."""
    u = _scramble_web_auth(req)
    try:
        uid = str(u["id"])
        now = time.time()
        if now - _scramble_web_last_start.get(uid, 0) < SCRAMBLE_WEB_START_GAP:
            _scr_log_once(ensure_user(uid, u.get("first_name", "User"), u.get("username")), "start_spam", uid, mode="web")
            return {"ok": False, "error": "Slow down a little."}
        if len(_scramble_web_last_start) > 2000:
            _scramble_web_last_start.clear()
        _scramble_web_last_start[uid] = now
        db = ensure_user(uid, u.get("first_name", "User"), u.get("username"))
        rec = db["users"][uid].setdefault("scramble", {})
        pending = _scramble_captchas.pop(uid, None)
        if pending and now <= pending["expires"]:        # asked for a new run without answering the captcha
            rec["captcha_skips"] = rec.get("captcha_skips", 0) + 1
            _scr_log(db, "captcha_ignored", uid, skips=rec["captcha_skips"])
            if rec["captcha_skips"] >= SCRAMBLE_CAPTCHA_MAX_SKIPS:
                await _scramble_ban(db, uid, "ignored captcha")
                raise HTTPException(status_code=403, detail="You are banned from Scramble.")
        if _scramble_captcha_due(db, uid):
            _scr_log(db, "captcha_issued", uid, flagged=bool(rec.get("flags", 0) > 0))
            stages = SCRAMBLE_CAPTCHA_STAGES_FLAGGED if rec.get("flags", 0) > 0 else SCRAMBLE_CAPTCHA_STAGES
            return {"ok": True, "captcha": await _scramble_captcha_issue(uid, stages=stages)}
        return await _scramble_web_launch(uid, db)
    except HTTPException:
        raise
    except Exception as e:
        print(f"[scramble_web_start] {e}")
        dlog.error(f"[scramble_web_start] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't build the puzzle.")


@deck_api.post("/scramble/captcha")
async def scramble_web_captcha(req: ScrWebReq):
    """Answer to a captcha challenge. Right -> the next challenge, or the puzzle after the last one.
    Wrong -> a different challenge, and the ban when the tries run out. Each challenge can be answered once."""
    u = _scramble_web_auth(req)
    try:
        uid = str(u["id"])
        db = ensure_user(uid, u.get("first_name", "User"), u.get("username"))
        ch = _scramble_captchas.get(uid)
        if not ch or ch["id"] != req.cid:
            raise HTTPException(status_code=400, detail="No captcha pending.")
        now = time.time()
        if now > ch["expires"]:
            _scramble_captchas.pop(uid, None)            # expired is not a failure - they just get a new run
            _scr_log(db, "captcha_expired", uid)
            return {"ok": False, "error": "Captcha expired. Tap Try again."}
        _scramble_captchas.pop(uid, None)                # one attempt per challenge: no probing the same one
        too_fast = now - ch["issued"] < SCRAMBLE_CAPTCHA_MIN_SOLVE
        if too_fast:
            _scr_log(db, "captcha_too_fast", uid, kind=ch["kind"], secs=round(now - ch["issued"], 2))
        if not too_fast and _scr_cap_check(ch, req.answer, req.taps):
            if ch["stage"] < ch["stages"]:               # passed, but another (different) challenge follows
                _scr_log(db, "captcha_stage_ok", uid, kind=ch["kind"], stage=ch["stage"], of=ch["stages"])
                return {"ok": True, "next": True,
                        "captcha": await _scramble_captcha_issue(uid, ch["tries"], ch["stage"] + 1, ch["stages"], ch["kind"])}
            db["users"][uid].setdefault("scramble", {})["captcha_skips"] = 0
            _scr_log(db, "captcha_passed", uid, wrong=ch["tries"], stages=ch["stages"])
            return await _scramble_web_launch(uid, db)
        tries = ch["tries"] + 1
        _scr_log(db, "captcha_wrong", uid, tries=tries, of=SCRAMBLE_CAPTCHA_TRIES, kind=ch["kind"], stage=ch["stage"])
        if tries >= SCRAMBLE_CAPTCHA_TRIES:
            await _scramble_ban(db, uid, "failed captcha")
            raise HTTPException(status_code=403, detail="Captcha failed. You are banned from Scramble.")
        return {"ok": True, "wrong": True,
                "captcha": await _scramble_captcha_issue(uid, tries, ch["stage"], ch["stages"], ch["kind"])}
    except HTTPException:
        raise
    except Exception as e:
        print(f"[scramble_web_captcha] {e}")
        dlog.error(f"[scramble_web_captcha] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Captcha error.")


@deck_api.post("/scramble/begin")
async def scramble_web_begin(req: ScrWebReq):
    """Kept so older cached copies of scramble.html don't break. It no longer touches the clock
    (a cheater could otherwise fetch the card, solve it offline, then call this to 'start')."""
    u = _scramble_web_auth(req)
    _scramble_web_run(req, u, pop=False)
    return {"ok": True}


@deck_api.post("/scramble/swap")
async def scramble_web_swap(req: ScrWebReq):
    """One swap of two board positions. The server replays it on its own copy of the board and
    answers whether the picture is now complete - and, if so, settles the reward right here."""
    u = _scramble_web_auth(req)
    run = _scramble_web_run(req, u, pop=False)
    n = SCRAMBLE_COLS * SCRAMBLE_ROWS
    a, b, seq = req.a, req.b, req.seq
    # A retry of the swap we already applied (the reply got lost): answer again, don't re-apply.
    if seq == run["moves"] and run["last"] == (a, b) and run["last_resp"] is not None:
        return run["last_resp"]
    if run["done"]:
        raise HTTPException(status_code=400, detail="Run already finished.")
    _db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    if seq != run["moves"] + 1:
        _scr_log_once(_db, "out_of_sync", u["id"], every=30, seq=seq, expected=run["moves"] + 1)
        raise HTTPException(status_code=409, detail="Out of sync.")
    if not (0 <= a < n and 0 <= b < n) or a == b:
        _scr_log(_db, "bad_swap", u["id"], a=a, b=b)
        raise HTTPException(status_code=400, detail="Bad swap.")
    if run["moves"] >= SCRAMBLE_WEB_MAX_SWAPS:
        _scramble_web_runs.pop(req.run, None)
        _scr_log(_db, "too_many_moves", u["id"], moves=run["moves"])
        raise HTTPException(status_code=400, detail="Too many moves.")

    now = time.time()
    perm = run["perm"]
    perm[a], perm[b] = perm[b], perm[a]
    run["moves"] += 1
    run["stamps"].append(now)
    run["last"] = (a, b)
    if perm != list(range(n)):
        run["last_resp"] = {"ok": True, "solved": False}
        return run["last_resp"]

    # ── Solved (as decided by the server) ──
    try:
        uid, name = str(u["id"]), u.get("first_name", "User")
        db = ensure_user(uid, name, u.get("username"))
        moves, elapsed = run["moves"], now - run["started"]
        perm0 = run["perm0"]
        solution = [perm0.index(p) for p in range(n)]
        gaps = [y - x for x, y in zip(run["stamps"], run["stamps"][1:])]
        base_resp = {"ok": True, "solved": True, "time": round(elapsed, 2), "moves": moves,
                     "card": run["card"], "solution": solution}
        if elapsed < max(SCRAMBLE_WEB_MIN_SECONDS, moves * SCRAMBLE_WEB_MIN_PER_SWAP):
            _scramble_flag(db, uid, name, "too_fast", elapsed=round(elapsed, 2), moves=moves)
            resp = {"ok": False, "error": "too_fast"}          # not recorded, not paid
        else:
            if len(gaps) >= 5 and statistics.pstdev(gaps) < SCRAMBLE_WEB_FLAG_STDEV:
                _scramble_flag(db, uid, name, "robotic_timing", elapsed=round(elapsed, 2),
                               moves=moves, stdev=round(statistics.pstdev(gaps), 4))
            dq = _scramble_web_solves.setdefault(uid, deque())
            while dq and now - dq[0] > 3600:
                dq.popleft()
            if len(dq) >= SCRAMBLE_WEB_MAX_SOLVES_PER_HOUR:    # farming: shows the card, counts for nothing
                _scr_log(db, "hourly_limit", uid, name, solves=len(dq), time=round(elapsed, 2))
                resp = {**base_resp, "limited": True, "earned": 0, "paid": 0}
            else:
                dq.append(now)
                earned = _scramble_reward_for(elapsed, SCRAMBLE_WEB_REWARD_TIERS)
                paid = _scramble_settle(uid, name, u.get("username"), elapsed, earned, mode="web",
                                        card=run["card"], moves=moves, chat_id="web",
                                        chat_title="Scramble Web App")
                resp = {**base_resp, "earned": earned, "paid": paid}
                _scr_log(db, "solve", uid, name, mode="web", time=round(elapsed, 2), moves=moves,
                         paid=paid, earned=earned, card=run["card"]["name"])
        run["done"] = True
        run["last_resp"] = resp
        return resp
    except HTTPException:
        raise
    except Exception as e:
        print(f"[scramble_web_swap] {e}")
        dlog.error(f"[scramble_web_swap] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't save the result.")


@deck_api.post("/scramble/finish")
async def scramble_web_finish(req: ScrWebReq):
    """Retired: the server now decides the win inside /scramble/swap. Without a verified board a
    bare 'finish' call proves nothing, so it can no longer pay out."""
    u = _scramble_web_auth(req)
    _scr_log(ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username")), "retired_finish", u["id"], mode="web")
    raise HTTPException(status_code=410, detail="Update scramble.html - this endpoint is retired.")


@deck_api.post("/scramble/giveup")
async def scramble_web_giveup(req: ScrWebReq):
    """Reveal the card (like chat mode's Give Up). No shards."""
    u = _scramble_web_auth(req)
    run = _scramble_web_run(req, u, pop=True)
    if run["done"]:
        raise HTTPException(status_code=400, detail="Run already finished.")
    _gdb = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    _scr_stat(_gdb, "giveup", uid=u["id"])
    _scr_log(_gdb, "giveup", u["id"], mode="web", moves=run["moves"], card=run["card"]["name"])
    perm0 = run["perm0"]
    return {"ok": True, "card": run["card"],
            "solution": [perm0.index(p) for p in range(SCRAMBLE_COLS * SCRAMBLE_ROWS)]}


@deck_api.post("/scramble/lb")
async def scramble_web_lb(req: ScrWebReq):
    """Top 10 + the caller's own rank for one tab (time / rounds / shards)."""
    u = _scramble_web_auth(req)
    if req.tab not in SCRAMBLE_LB_TABS:
        raise HTTPException(status_code=400, detail="Bad tab.")
    db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
    rows = _scramble_board(db, req.tab)
    me = next((i for i, x in enumerate(rows) if x[1] == str(u["id"])), None)
    return {
        "ok": True,
        "rows": [{"name": n, "value": _scramble_fmt_value(req.tab, v)} for v, _u, n in rows[:10]],
        "me": None if me is None else {"rank": me + 1, "value": _scramble_fmt_value(req.tab, rows[me][0])}}


_scramble_avatar_cache: dict = {}   # uid -> (data_url | None, fetched_at)


@deck_api.post("/scramble/avatar")
async def scramble_web_avatar(req: ScrWebReq):
    """Profile picture fallback for players whose Telegram launch data has no photo_url."""
    u = _scramble_web_auth(req)
    uid = int(u["id"])
    hit = _scramble_avatar_cache.get(uid)
    if hit and time.time() - hit[1] < 3600:
        return {"ok": bool(hit[0]), "photo": hit[0]}
    photo = None
    try:
        res = await bot.get_user_profile_photos(uid, limit=1)
        if res.total_count and res.photos:
            buf = io.BytesIO()
            await bot.download(res.photos[0][0].file_id, destination=buf)   # smallest size is plenty
            photo = "data:image/jpeg;base64," + base64.b64encode(buf.getvalue()).decode()
    except Exception as e:
        dlog.error(f"[scramble_web_avatar] {e}", exc_info=True)
    if len(_scramble_avatar_cache) > 500:
        _scramble_avatar_cache.clear()
    _scramble_avatar_cache[uid] = (photo, time.time())
    return {"ok": bool(photo), "photo": photo}


@main_router.message(Command("webscr", "scramble_web"))
async def scramble_web_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    if _scramble_is_banned(ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username), uid_int):
        await message.reply("You are banned from Scramble.")
        return
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        _scr_url_btn("Play Web Mode", SCRAMBLE_WEB_LINK, "primary")]])
    await message.reply(
        "<b>「 SCRAMBLE WEB 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Under 20 sec : <b>50</b> Shards\nUnder 40 sec : <b>25</b> Shards\n"
        "━━━━━━━━━━━━━━━━━\n<i>Tap the button to open the Mini App.</i>",
        reply_markup=kb, parse_mode=ParseMode.HTML)


# ==========================================
# /scramble_lbd — LEADERBOARD
# ==========================================
SCRAMBLE_LB_TABS = {"time": "Time taken", "rounds": "Round", "shards": "Total shards collected"}
SCRAMBLE_LB_TITLES = {"time": "FASTEST TIME", "rounds": "ROUNDS SOLVED", "shards": "TOTAL SHARDS"}
SCRAMBLE_LBD_IMAGE = "https://i.ibb.co/TMFbh2KY/IMG-20261006-113510.jpg"   # leaderboard banner (caption limit: 1024 chars)


def _scramble_fmt_best(t: float) -> str:
    if t < 60:
        return f"{t:.2f}s"
    return f"{int(t // 60)}m {t % 60:04.1f}s"


def _scramble_board(db: dict, tab: str):
    """[(value, uid, name)] best first. Time: lowest wins; Round / Shards: highest wins."""
    rows = []
    for uid, u in (db.get("users") or {}).items():
        rec = u.get("scramble") if isinstance(u, dict) else None
        if not isinstance(rec, dict) or rec.get("banned"):
            continue
        if tab == "time":
            v = rec.get("best_time")
        elif tab == "rounds":
            v = rec.get("rounds", 0)
        else:
            v = rec.get("shards", 0)
        if v and v > 0:
            name = str(u.get("name") or "User")[:24]
            rows.append((v, str(uid), name))
    if tab == "time":
        rows.sort(key=lambda r: (r[0], r[1]))
    else:
        rows.sort(key=lambda r: (-r[0], r[1]))
    return rows


def _scramble_fmt_value(tab: str, v) -> str:
    if tab == "time":
        return _scramble_fmt_best(v)
    if tab == "rounds":
        return f"{int(v):,} round" + ("" if int(v) == 1 else "s")
    return f"{int(v):,} shards"


def _scramble_lb_text(db: dict, tab: str, uid) -> str:
    rows = _scramble_board(db, tab)
    text = f"<b>「 SCRAMBLE - {SCRAMBLE_LB_TITLES[tab]} 」</b>\n━━━━━━━━━━━━━━━━━\n"
    if rows:
        text += "\n".join(
            f"<b>{i + 1}.</b> <b>{_html_esc(name[:18])}</b> - {_scramble_fmt_value(tab, v)}"
            for i, (v, _u, name) in enumerate(rows[:10])
        )
    else:
        text += "Nobody has solved a scramble yet. Be the first with /scramble"
    text += "\n━━━━━━━━━━━━━━━━━\n"
    me = str(uid)
    idx = next((i for i, r in enumerate(rows) if r[1] == me), None)
    if idx is None:
        text += "<b>Your rank:</b> Unranked"
    else:
        text += f"<b>Your rank:</b> #{idx + 1} with {_scramble_fmt_value(tab, rows[idx][0])}"
    return text


def _scramble_lb_kb(owner, active: str) -> InlineKeyboardMarkup:
    def btn(tab):
        return _scr_btn(SCRAMBLE_LB_TABS[tab], f"slb:{tab}:{owner}",
                        "success" if tab == active else "primary")
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("time"), btn("rounds")],
        [btn("shards")],
    ])


@main_router.message(Command("scramble_lbd"))
async def scramble_lbd_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    try:
        db = ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
        text = _scramble_lb_text(db, "time", uid_int)
        kb = _scramble_lb_kb(uid_int, "time")
        try:   # banner image with the leaderboard as its caption
            await message.reply_photo(photo=SCRAMBLE_LBD_IMAGE, caption=text,
                                      reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception as e:   # image unreachable: still show the leaderboard as text
            dlog.error(f"[scramble_lbd_photo] {e}", exc_info=True)
            await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[scramble_lbd_CRASH] {e}")
        traceback.print_exc()
        dlog.error(f"[scramble_lbd_CRASH] {e}", exc_info=True)
        await message.reply("The leaderboard is unavailable right now. Please try again in a moment.")


@main_router.callback_query(F.data.startswith("slb:"))
async def scramble_lbd_cb(cq: CallbackQuery):
    if is_ghost_banned(cq.from_user.id) or is_shadow_banned(cq.from_user.id): return
    try:
        _, tab, owner = cq.data.split(":")
    except ValueError:
        await cq.answer()
        return
    if tab not in SCRAMBLE_LB_TABS:
        await cq.answer()
        return
    if str(cq.from_user.id) != owner:
        await cq.answer("This leaderboard belongs to someone else. Send /scramble_lbd for your own.", show_alert=True)
        return
    try:
        db = ensure_user(owner, cq.from_user.first_name, cq.from_user.username)
        text = _scramble_lb_text(db, tab, cq.from_user.id)
        kb = _scramble_lb_kb(owner, tab)
        if cq.message.photo:   # banner image: the leaderboard lives in the caption
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:                  # older text-only leaderboard message
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[scramble_lbd_cb] failed: {e}")
            dlog.error(f"[scramble_lbd_cb] failed: {e}", exc_info=True)
    await cq.answer()


# ==========================================
# /scr_stats — ADMIN ONLY, DM ONLY
# ==========================================
def _scr_fmt_t(t) -> str:
    if t is None:
        return "-"
    return f"{t:.2f}s" if t < 60 else f"{int(t // 60)}m {t % 60:.1f}s"


def _scr_section(title: str, b: dict) -> str:
    chat, web = b.get("solved_chat", 0), b.get("solved_web", 0)
    solved = chat + web
    started, gave = b.get("started", 0), b.get("gave_up", 0)
    avg = (b.get("time_sum", 0.0) / solved) if solved else None
    rate = f"{solved / started * 100:.0f}%" if started else "-"
    fast = _scr_fmt_t(b.get("fastest"))
    if b.get("fastest") is not None and b.get("fastest_name"):
        fast += f" ({_html_esc(str(b['fastest_name'])[:18])})"
    lines = [
        f"<b>{title}</b>",
        f"Games started   : <b>{started:,}</b>",
        f"Solved          : <b>{solved:,}</b>  (Chat {chat:,} | Web {web:,})",
        f"Given up        : <b>{gave:,}</b>",
        f"Solve rate      : <b>{rate}</b>",
        f"Average time    : <b>{_scr_fmt_t(avg)}</b>",
        f"Fastest solve   : <b>{fast}</b>",
        f"Shards paid     : <b>{b.get('shards_paid', 0):,}</b>",
        f"Shards capped   : <b>{b.get('shards_capped', 0):,}</b>  (lost to daily cap)",
    ]
    if "players" in b:
        lines.insert(1, f"Active players  : <b>{len(b['players']):,}</b>")
    return "\n".join(lines)


@main_router.message(Command("scr_stats"))
async def scramble_stats_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return   # not an admin: behave as if the command doesn't exist
    if message.chat.type != ChatType.PRIVATE:
        await message.reply("Use /scr_stats in my DMs.")
        return
    try:
        db = ensure_user(str(message.from_user.id), message.from_user.first_name, message.from_user.username)
        root = db.get("scramble_stats") or {}
        today_key = datetime.now(timezone.utc).strftime("%Y-%m-%d")
        today = (root.get("days") or {}).get(today_key, {})

        # Records are the source of truth for history; tracked counters only start once this feature is live.
        rounds_rows = _scramble_board(db, "rounds")
        shard_rows = _scramble_board(db, "shards")
        time_rows = _scramble_board(db, "time")
        allb = dict(root.get("all") or {})
        allt = (
            "<b>ALL TIME</b>\n"
            f"Players         : <b>{len(rounds_rows):,}</b>\n"
            f"Banned          : <b>{len(_scramble_ban_list(db)):,}</b>\n"
            f"Rounds solved   : <b>{sum(v for v, _, _ in rounds_rows):,}</b>\n"
            f"Shards paid     : <b>{sum(v for v, _, _ in shard_rows):,}</b>\n"
            f"Fastest solve   : <b>{_scr_fmt_t(time_rows[0][0]) if time_rows else '-'}"
            f"{' (' + _html_esc(time_rows[0][2][:18]) + ')' if time_rows else ''}</b>"
        )
        text = (
            "<b>「 SCRAMBLE STATS 」</b>\n━━━━━━━━━━━━━━━━━\n"
            + _scr_section(f"TODAY ({today_key} UTC)", today)
            + "\n━━━━━━━━━━━━━━━━━\n" + allt
            + "\n━━━━━━━━━━━━━━━━━\n"
            + _scr_section("ALL TIME - SINCE TRACKING STARTED", allb)
        )
        await message.reply(text, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[scr_stats_CRASH] {e}")
        traceback.print_exc()
        dlog.error(f"[scr_stats_CRASH] {e}", exc_info=True)
        await message.reply("Stats are unavailable right now.")


# ==========================================
# /scrlist  /scruban — ADMIN ONLY
# ==========================================
@main_router.message(Command("scrlist"))
async def scramble_banlist_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return   # not an admin: behave as if the command doesn't exist
    if message.chat.type != ChatType.PRIVATE:
        await message.reply("Use /scrlist in my DMs.")
        return
    try:
        db = ensure_user(str(message.from_user.id), message.from_user.first_name, message.from_user.username)
        rows = _scramble_ban_list(db)
        text = f"<b>「 SCRAMBLE BAN LIST 」</b>\n━━━━━━━━━━━━━━━━━\n"
        if not rows:
            text += "Nobody is banned."
        else:
            for i, (uid, name, info) in enumerate(rows[:40], 1):
                when = datetime.fromtimestamp(info.get("at") or 0, timezone.utc).strftime("%Y-%m-%d %H:%M")
                by = "auto" if info.get("by") == "auto" else f"admin {info.get('by')}"
                text += (f"<b>{i}.</b> {_html_esc(name[:20])} (<code>{uid}</code>)\n"
                         f"    {_html_esc(str(info.get('reason', '-')))} · {when} UTC · {by}\n")
            if len(rows) > 40:
                text += f"…and {len(rows) - 40} more.\n"
            text += "━━━━━━━━━━━━━━━━━\n<i>/scruban &lt;user_id&gt; · reply + /scruban · /scruban all</i>"
        await message.reply(text, parse_mode=ParseMode.HTML)
    except Exception as e:
        print(f"[scrlist_CRASH] {e}")
        dlog.error(f"[scrlist_CRASH] {e}", exc_info=True)
        await message.reply("Ban list unavailable right now.")


@main_router.message(Command("scruban"))
async def scramble_unban_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return
    try:
        db = ensure_user(str(message.from_user.id), message.from_user.first_name, message.from_user.username)
        parts = (message.text or "").split()
        arg = parts[1] if len(parts) > 1 else None
        if arg and arg.lower() == "all":
            ids = [uid for uid, _n, _i in _scramble_ban_list(db)]
            for uid in ids:
                await _scramble_unban(db, uid, by=message.from_user.id)
            await message.reply(f"Unbanned {len(ids)} player(s) from Scramble.")
            return
        if arg is None and message.reply_to_message and message.reply_to_message.from_user:
            arg = str(message.reply_to_message.from_user.id)
        if not arg or not arg.lstrip("-").isdigit():
            await message.reply("Usage: /scruban &lt;user_id&gt; - or reply to the player's message - or /scruban all",
                                parse_mode=ParseMode.HTML)
            return
        if await _scramble_unban(db, arg, by=message.from_user.id):
            await message.reply(f"Unbanned <code>{_html_esc(arg)}</code> from Scramble.", parse_mode=ParseMode.HTML)
        else:
            await message.reply("That player isn't banned from Scramble.")
    except Exception as e:
        print(f"[scruban_CRASH] {e}")
        dlog.error(f"[scruban_CRASH] {e}", exc_info=True)
        await message.reply("Couldn't unban right now.")


# ==========================================
# /scrlog — ADMIN ONLY, DM ONLY  ->  sends scrlog.txt (just the file, no message)
# ==========================================
#   /scrlog                 everything, newest first
#   /scrlog v               violations only (too fast, captcha fails, bans, spam ...)
#   /scrlog <user_id>       one player      /scrlog <user_id> v   one player's violations
def _scr_log_text(db: dict, viol_only: bool, uid: str) -> str:
    def clean(x) -> str:
        return str(x).replace("\n", " ").replace("\r", " ")

    rows = [e for e in reversed(db.get("scramble_log") or [])
            if (not viol_only or e.get("v")) and (not uid or e.get("u") == uid)]
    scope = ("violations" if viol_only else "all events") + (f" | player {uid}" if uid else "")
    now = datetime.now(timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
    lines = ["SCRAMBLE LOG", f"scope: {scope}", f"entries: {len(rows):,} (newest first)",
             f"generated: {now} UTC", "=" * 64, ""]
    if not rows:
        lines.append("Nothing logged yet.")
    for e in rows:
        when = datetime.fromtimestamp(e.get("t") or 0, timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
        flag = "VIOLATION" if e.get("v") else "event"
        who = f"{clean(e.get('n') or '-')} ({clean(e.get('u') or '-')})"
        info = ", ".join(f"{k}={clean(v)}" for k, v in (e.get("i") or {}).items())
        lines.append(f"{when} UTC | {flag:<9} | {clean(e.get('e'))} | {who}" + (f" | {info}" if info else ""))
    return "\n".join(lines) + "\n"


@main_router.message(Command("scrlog"))
async def scramble_log_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return   # not an admin: behave as if the command doesn't exist
    if message.chat.type != ChatType.PRIVATE:
        await message.reply("Use /scrlog in my DMs.")
        return
    try:
        db = ensure_user(str(message.from_user.id), message.from_user.first_name, message.from_user.username)
        viol, uid = False, ""
        for tok in (message.text or "").split()[1:]:
            if tok.lower() in ("v", "viol", "violations"):
                viol = True
            elif tok.lstrip("-").isdigit():
                uid = tok
        data = (await asyncio.to_thread(_scr_log_text, db, viol, uid)).encode("utf-8")
        await message.reply_document(BufferedInputFile(data, filename="scrlog.txt"))
    except Exception as e:
        print(f"[scrlog_CRASH] {e}")
        dlog.error(f"[scrlog_CRASH] {e}", exc_info=True)
        await message.reply("The log is unavailable right now.")


@main_router.callback_query(F.data.startswith("slog:"))
async def scramble_log_cb(cq: CallbackQuery):
    """Buttons on old paged /scrlog messages: the log is a .txt file now."""
    if cq.from_user.id in ADMIN_IDS:
        await cq.answer("Send /scrlog again - the log now comes as a .txt file.", show_alert=True)
    else:
        await cq.answer()
