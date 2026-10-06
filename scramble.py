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
SCRAMBLE_MAX_WIDTH = 900            # working resolution of the puzzle image
SCRAMBLE_TTL = 15 * 60              # idle seconds before a puzzle expires
SCRAMBLE_MAX_GAMES = 150            # hard cap on puzzles held in memory
# Card pool: prepared card images kept ready so a board can be sent without downloading.
# Each game CONSUMES one card from the pool. When the pool drops to SCRAMBLE_POOL_LOW it
# is refilled in the background up to SCRAMBLE_POOL_SIZE, using cards that are neither
# already in the pool nor among the last SCRAMBLE_RECENT_MAX cards played.
SCRAMBLE_POOL_SIZE = 60
SCRAMBLE_POOL_LOW = 30
SCRAMBLE_RECENT_MAX = 100
SCRAMBLE_REFILL_PARALLEL = 4        # simultaneous Telegram downloads while refilling

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
    """Card ids with art, skipping locked animes."""
    locked = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
    return [c for c, g in db.get("global_cards", {}).items()
            if g.get("file_id") and str(g.get("anime", "")).lower().strip() not in locked]


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
        if cid in valid:   # card may have been removed/locked since it was pooled
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


def _scramble_kick_refill(db: dict):
    """Start a background refill when the pool is at/below the low-water mark."""
    if len(_scramble_pool) <= SCRAMBLE_POOL_LOW and not _scramble_refilling:
        task = asyncio.create_task(_scramble_refill(db))
        _scramble_bg.add(task)
        task.add_done_callback(_scramble_bg.discard)


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
        img = img.resize((SCRAMBLE_MAX_WIDTH, max(1, int(img.height * ratio))), Image.LANCZOS)
    w = img.width - (img.width % SCRAMBLE_COLS)
    h = img.height - (img.height % SCRAMBLE_ROWS)
    img = img.crop((0, 0, w, h))
    out = io.BytesIO()
    img.save(out, "JPEG", quality=85)
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
    out.save(buf, "JPEG", quality=88)
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
        cid, base = _scramble_take(db)
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

        sent = await message.reply_photo(
            photo=BufferedInputFile(img, filename="scramble.jpg"),
            caption=_scramble_caption(game),
            reply_markup=_scramble_kb(gid),
            parse_mode=ParseMode.HTML
        )
        game["message_id"] = sent.message_id
        try:
            await loading.delete()
        except Exception:
            pass
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
                _scr_stat(ensure_user(str(cq.from_user.id), cq.from_user.first_name, cq.from_user.username),
                          "giveup", uid=cq.from_user.id)
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
SCRAMBLE_WEB_MIN_SECONDS = 2                               # a 9-piece board needs 5+ swaps, so faster than this is a bot
_scramble_web_runs: dict = {}                              # run token -> {uid, started, card}


class ScrWebReq(BaseModel):
    init_data: str = ""
    run: str = ""
    tab: str = "time"


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


@deck_api.post("/scramble/start")
async def scramble_web_start(req: ScrWebReq):
    """Pick a real card (same pool as /scramble); the client cuts it, clock starts at /begin."""
    u = _scramble_web_auth(req)
    try:
        uid = str(u["id"])
        db = ensure_user(uid, u.get("first_name", "User"), u.get("username"))
        now = time.time()
        for k, v in list(_scramble_web_runs.items()):   # expire old runs + one run per player
            if now - v["started"] > SCRAMBLE_TTL or v["uid"] == uid:
                _scramble_web_runs.pop(k, None)
        cid, base = _scramble_take(db)
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
        run = secrets.token_hex(8)
        _scramble_web_runs[run] = {"uid": uid, "started": now, "card": {
            "name": str(g.get("name", "Card")), "rarity": str(g.get("rarity", "Common")),
            "anime": str(g.get("anime", "Unknown"))}}
        return {"ok": True, "run": run,
                "image": "data:image/jpeg;base64," + base64.b64encode(base).decode()}
    except Exception as e:
        print(f"[scramble_web_start] {e}")
        dlog.error(f"[scramble_web_start] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't build the puzzle.")


@deck_api.post("/scramble/begin")
async def scramble_web_begin(req: ScrWebReq):
    """Client calls this once the card art is on screen: that is when the clock starts."""
    u = _scramble_web_auth(req)
    _scramble_web_run(req, u, pop=False)["started"] = time.time()
    return {"ok": True}


@deck_api.post("/scramble/finish")
async def scramble_web_finish(req: ScrWebReq):
    u = _scramble_web_auth(req)
    run = _scramble_web_run(req, u, pop=True)
    try:
        elapsed = time.time() - run["started"]
        if elapsed < SCRAMBLE_WEB_MIN_SECONDS:
            raise HTTPException(status_code=400, detail="Too fast.")
        earned = _scramble_reward_for(elapsed, SCRAMBLE_WEB_REWARD_TIERS)
        paid = _scramble_settle(str(u["id"]), u.get("first_name", "User"), u.get("username"), elapsed, earned,
                                mode="web", card=run["card"], chat_id="web", chat_title="Scramble Web App")
        return {"ok": True, "earned": earned, "paid": paid, "time": round(elapsed, 2), "card": run["card"]}
    except HTTPException:
        raise
    except Exception as e:
        print(f"[scramble_web_finish] {e}")
        dlog.error(f"[scramble_web_finish] {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Couldn't save the result.")


@deck_api.post("/scramble/giveup")
async def scramble_web_giveup(req: ScrWebReq):
    """Reveal the card (like chat mode's Give Up). No shards."""
    u = _scramble_web_auth(req)
    run = _scramble_web_run(req, u, pop=True)
    _scr_stat(ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username")), "giveup", uid=u["id"])
    return {"ok": True, "card": run["card"]}


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
        if not isinstance(rec, dict):
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
