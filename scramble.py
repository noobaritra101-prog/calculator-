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
import json
import hashlib
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
    is_ghost_banned, is_shadow_banned,
    get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)
from aiohttp import web
from deck import dlog   # same error-only log file (dlog.txt) the deck uses

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

# Button flood guard: taps closer together than the cooldown are dropped silently
# (instant, no spinner). Too many dropped taps in a row locks the board briefly.
SCRAMBLE_CLICK_COOLDOWN = 0.5       # min seconds between accepted taps
SCRAMBLE_FLOOD_STRIKES = 5          # dropped taps in a row before the lock kicks in
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


def _scramble_settle(user_id: str, name: str, username, elapsed: float, earned: int) -> int:
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
            "last_click": 0.0, "strikes": 0, "locked_until": 0.0, "lock": asyncio.Lock(),
            "name": g.get("name", "Card"), "rarity": g.get("rarity", "Common"),
            "anime": g.get("anime", "Unknown"),
        }
        _scramble_games[gid] = game

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
    if now - game["last_click"] < SCRAMBLE_CLICK_COOLDOWN:
        game["strikes"] += 1
        if game["strikes"] >= SCRAMBLE_FLOOD_STRIKES:
            game["strikes"] = 0
            game["locked_until"] = now + SCRAMBLE_FLOOD_LOCK
            await cq.answer(f"Too fast! Buttons locked for {int(SCRAMBLE_FLOOD_LOCK)}s.", show_alert=True)
        else:
            await cq.answer()   # dropped silently, instant
        return
    game["strikes"] = 0
    game["last_click"] = now

    # Acknowledge right away so the button stops spinning; the redraw follows.
    try:
        await cq.answer()
    except Exception:
        pass

    try:
        async with game["lock"]:
            if gid not in _scramble_games:   # finished while we waited on the lock
                return
            game["touched"] = time.time()
            n = SCRAMBLE_COLS * SCRAMBLE_ROWS

            # ── Give up: reveal the finished picture ──
            if action == "give":
                _scramble_games.pop(gid, None)
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
                await cq.message.edit_caption(
                    caption=_scramble_caption(game, game["selected"]),
                    reply_markup=_scramble_kb(gid, game["selected"]),
                    parse_mode=ParseMode.HTML)
                return

            # Second tap: swap the two pieces and redraw.
            perm = game["perm"]
            perm[sel], perm[idx] = perm[idx], perm[sel]
            game["selected"] = None
            game["moves"] += 1
            solved = perm == list(range(n))

            reward_text = ""
            if solved:
                _scramble_games.pop(gid, None)
                game["finished"] = time.time()   # stop the clock before rendering/uploading
                earned = _scramble_reward_for(game["finished"] - game["started"])
                paid = _scramble_settle(str(cq.from_user.id), cq.from_user.first_name,
                                        cq.from_user.username,
                                        game["finished"] - game["started"], earned)
                if paid > 0:
                    reward_text = f"<b>Reward :</b> +{paid} Shards\n"
                elif earned > 0:
                    reward_text = "<i>Daily reward cap reached</i>\n"
                else:
                    reward_text = "<i>No shards - solve under 2 min to earn some.</i>\n"
            img = await asyncio.to_thread(_scramble_render, game["base"], perm, not solved)
            await cq.message.edit_media(
                media=InputMediaPhoto(
                    media=BufferedInputFile(img, filename="scramble.jpg"),
                    caption=_scramble_end_caption(game, won=True, reward_text=reward_text) if solved else _scramble_caption(game),
                    parse_mode=ParseMode.HTML),
                reply_markup=_scramble_kb(gid, solved=solved))
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[scramble_cb] failed: {e}")
            traceback.print_exc()
            dlog.error(f"[scramble_cb] failed: {e}", exc_info=True)


# ==========================================
# WEB MODE — Telegram Mini App (scramble.html)
# ==========================================
# Host scramble.html on your own https domain, point the BotFather Mini App 'scramble' at it, and mount
# scramble_web_routes(app) on the aiohttp app that serves it (same origin = no CORS setup).
# The server times every run itself and validates Telegram's signed initData, so the
# client can't claim a fake time. Shards use the same daily minigame cap as chat mode.
SCRAMBLE_WEB_LINK = "https://t.me/Animenx_bot/scramble"   # Mini App direct link (set in BotFather -> /newapp)
SCRAMBLE_WEB_REWARD_TIERS = [(60, 50), (120, 25)]      # web mode: lower than chat mode
SCRAMBLE_WEB_MIN_SECONDS = 6                           # faster than this is not humanly possible
_scramble_web_runs: dict = {}                          # run token -> (user_id, started)


def _scramble_web_user(init_data: str):
    """Verify Telegram WebApp initData (HMAC) -> user dict, or None if invalid/stale."""
    try:
        pairs = dict(parse_qsl(init_data, strict_parsing=True))
        got = pairs.pop("hash")
        check = "\n".join(f"{k}={v}" for k, v in sorted(pairs.items()))
        secret = hmac.new(b"WebAppData", bot.token.encode(), hashlib.sha256).digest()
        calc = hmac.new(secret, check.encode(), hashlib.sha256).hexdigest()
        if not hmac.compare_digest(calc, got):
            return None
        if time.time() - int(pairs.get("auth_date", 0)) > 86400:
            return None
        return json.loads(pairs["user"])
    except Exception:
        return None


async def scramble_web_start(request):
    try:
        u = _scramble_web_user((await request.json()).get("initData", ""))
        if not u or is_ghost_banned(u["id"]) or is_shadow_banned(u["id"]):
            return web.json_response({"ok": False}, status=401)
        now = time.time()
        for k, (_, t) in list(_scramble_web_runs.items()):
            if now - t > SCRAMBLE_TTL:
                _scramble_web_runs.pop(k, None)
        run = secrets.token_hex(8)
        _scramble_web_runs[run] = (str(u["id"]), now)
        return web.json_response({"ok": True, "run": run})
    except Exception as e:
        dlog.error(f"[scramble_web_start] {e}", exc_info=True)
        return web.json_response({"ok": False}, status=400)


async def scramble_web_finish(request):
    try:
        body = await request.json()
        u = _scramble_web_user(body.get("initData", ""))
        entry = _scramble_web_runs.pop(body.get("run"), None)   # one-time token: no replays
        if not u or not entry or entry[0] != str(u["id"]):
            return web.json_response({"ok": False}, status=401)
        elapsed = time.time() - entry[1]
        if elapsed < SCRAMBLE_WEB_MIN_SECONDS:
            return web.json_response({"ok": False}, status=400)
        earned = _scramble_reward_for(elapsed, SCRAMBLE_WEB_REWARD_TIERS)
        paid = _scramble_settle(str(u["id"]), u.get("first_name", "User"), u.get("username"), elapsed, earned)
        return web.json_response({"ok": True, "earned": earned, "paid": paid, "time": round(elapsed, 2)})
    except Exception as e:
        dlog.error(f"[scramble_web_finish] {e}", exc_info=True)
        return web.json_response({"ok": False}, status=400)


async def scramble_web_lb(request):
    """Top 10 + the caller's own rank for one tab (time / rounds / shards)."""
    try:
        body = await request.json()
        u = _scramble_web_user(body.get("initData", ""))
        tab = body.get("tab", "time")
        if not u or tab not in SCRAMBLE_LB_TABS:
            return web.json_response({"ok": False}, status=401)
        db = ensure_user(str(u["id"]), u.get("first_name", "User"), u.get("username"))
        rows = _scramble_board(db, tab)
        me = next((i for i, x in enumerate(rows) if x[1] == str(u["id"])), None)
        return web.json_response({
            "ok": True,
            "rows": [{"name": n, "value": _scramble_fmt_value(tab, v)} for v, _u, n in rows[:10]],
            "me": None if me is None else {"rank": me + 1, "value": _scramble_fmt_value(tab, rows[me][0])}})
    except Exception as e:
        dlog.error(f"[scramble_web_lb] {e}", exc_info=True)
        return web.json_response({"ok": False}, status=400)


def scramble_web_routes(app: "web.Application"):
    """Call once on your aiohttp app: scramble_web_routes(app)"""
    app.router.add_post("/scramble/start", scramble_web_start)
    app.router.add_post("/scramble/finish", scramble_web_finish)
    app.router.add_post("/scramble/lb", scramble_web_lb)


@main_router.message(Command("webscr", "scramble_web"))
async def scramble_web_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        _scr_url_btn("Play Web Mode", SCRAMBLE_WEB_LINK, "primary")]])
    await message.reply(
        "<b>「 SCRAMBLE WEB 」</b>\n━━━━━━━━━━━━━━━━━\n"
        "Under 1 min : <b>50</b> Shards\nUnder 2 min : <b>25</b> Shards\n"
        "━━━━━━━━━━━━━━━━━\n<i>Tap the button to open the Mini App.</i>",
        reply_markup=kb, parse_mode=ParseMode.HTML)


# ==========================================
# /scramble_lbd — LEADERBOARD
# ==========================================
SCRAMBLE_LB_TABS = {"time": "Time taken", "rounds": "Round", "shards": "Total shards collected"}
SCRAMBLE_LB_TITLES = {"time": "FASTEST TIME", "rounds": "ROUNDS SOLVED", "shards": "TOTAL SHARDS"}


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
            f"<b>{i + 1}.</b> <b>{_html_esc(name)}</b> - {_scramble_fmt_value(tab, v)}"
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
        await message.reply(
            _scramble_lb_text(db, "time", uid_int),
            reply_markup=_scramble_lb_kb(uid_int, "time"),
            parse_mode=ParseMode.HTML)
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
        await cq.message.edit_text(
            _scramble_lb_text(db, tab, cq.from_user.id),
            reply_markup=_scramble_lb_kb(owner, tab),
            parse_mode=ParseMode.HTML)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[scramble_lbd_cb] failed: {e}")
            dlog.error(f"[scramble_lbd_cb] failed: {e}", exc_info=True)
    await cq.answer()
