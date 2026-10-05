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
from html import escape as _html_esc

from PIL import Image, ImageDraw, ImageFont   # pip install pillow
from aiogram import F
from aiogram.types import (
    Message, CallbackQuery,
    InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto, BufferedInputFile
)
from aiogram.filters import Command
from aiogram.enums import ParseMode

from config import (
    bot, main_router, format_rarity, ensure_user, save_db,
    is_ghost_banned, is_shadow_banned,
    get_daily_minigame_rewards, DAILY_MINIGAME_REWARD_CAP
)
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
SCRAMBLE_CLICK_COOLDOWN = 1.0       # seconds between button taps (flood guard)

# (solve under N seconds, shards). Anything slower than the last tier pays nothing.
SCRAMBLE_REWARD_TIERS = [(60, 100), (120, 50)]

# gid -> {owner, base (jpeg bytes), perm, selected, moves, started, touched, lock, name, rarity, anime}
_scramble_games: dict[str, dict] = {}


def _scramble_purge(owner: int | None = None):
    """Drop expired puzzles, any older puzzle of `owner`, and enforce the memory cap."""
    now = time.time()
    for gid, g in list(_scramble_games.items()):
        if now - g["touched"] > SCRAMBLE_TTL or (owner is not None and g["owner"] == owner):
            _scramble_games.pop(gid, None)
    while len(_scramble_games) >= SCRAMBLE_MAX_GAMES:
        oldest = min(_scramble_games, key=lambda k: _scramble_games[k]["touched"])
        _scramble_games.pop(oldest, None)


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
    img.save(out, "JPEG", quality=92)
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


def _scramble_reward_for(elapsed: float) -> int:
    for limit, shards in SCRAMBLE_REWARD_TIERS:
        if elapsed < limit:
            return shards
    return 0


def _scramble_pay(user_id: str, name: str, username, earned: int) -> int:
    """Credits `earned` shards, limited by the daily minigame cap shared with
    /gcard and Versus. Returns the amount actually paid."""
    if earned <= 0:
        return 0
    db = ensure_user(user_id, name, username)
    user_data = db["users"][user_id]
    rewards = get_daily_minigame_rewards(user_data)
    used = rewards.get("shards", 0)
    if used >= DAILY_MINIGAME_REWARD_CAP:
        return 0
    paid = min(earned, DAILY_MINIGAME_REWARD_CAP - used)
    user_data["nexus_shards"] = user_data.get("nexus_shards", 0) + paid
    rewards["shards"] = used + paid
    save_db()
    return paid


def _scramble_caption(game: dict, selected: int | None = None) -> str:
    hint = (f"Swap <b>{selected + 1}</b> with…? Tap another number."
            if selected is not None else "Tap two numbers to swap those pieces.")
    return (
        "<b>「 🧩 SCRAMBLE 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Put the card back together!\n"
        "<blockquote>Under 1 min: <b>100 Shards</b>\n"
        "Under 2 min: <b>50 Shards</b>\n"
        "Slower: no shards</blockquote>\n"
        f"<b>Moves:</b> {game['moves']}\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<i>{hint}</i>"
    )


def _scramble_end_caption(game: dict, won: bool, reward_text: str = "") -> str:
    head = "「 🧩 SCRAMBLE SOLVED! 」" if won else "「 🏳️ SCRAMBLE GAVE UP 」"
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


@main_router.message(Command("scramble"))
async def scramble_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return

    user_id = str(uid_int)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    global_cards = db.get("global_cards", {})

    try:
        # Bot picks any random card (skipping locked animes) — not limited to the player's deck.
        locked = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
        pool = [c for c, g in global_cards.items()
                if g.get("file_id") and str(g.get("anime", "")).lower().strip() not in locked]
        if not pool:
            await message.reply("There are no cards to scramble yet.")
            return
        cid = random.choice(pool)

        g = global_cards[cid]
        await bot.send_chat_action(message.chat.id, "upload_photo")

        buf = io.BytesIO()
        await bot.download(g["file_id"], destination=buf)
        base = await asyncio.to_thread(_scramble_prepare, buf.getvalue())
        perm = _scramble_shuffle(SCRAMBLE_COLS * SCRAMBLE_ROWS)
        img = await asyncio.to_thread(_scramble_render, base, perm)

        _scramble_purge(owner=uid_int)   # one puzzle per player at a time
        gid = secrets.token_hex(4)
        game = {
            "owner": uid_int, "base": base, "perm": perm, "selected": None, "moves": 0,
            "started": time.time(), "touched": time.time(), "last_click": 0.0, "lock": asyncio.Lock(),
            "name": g.get("name", "Card"), "rarity": g.get("rarity", "Common"),
            "anime": g.get("anime", "Unknown"),
        }
        _scramble_games[gid] = game

        await message.reply_photo(
            photo=BufferedInputFile(img, filename="scramble.jpg"),
            caption=_scramble_caption(game),
            reply_markup=_scramble_kb(gid),
            parse_mode=ParseMode.HTML
        )
        game["started"] = time.time()   # clock starts once the puzzle is actually on screen
        game["touched"] = game["started"]
    except Exception as e:
        print(f"[scramble_CRASH] {e}")
        traceback.print_exc()
        dlog.error(f"[scramble_CRASH] {e}", exc_info=True)
        await message.reply("Couldn't build the puzzle right now. Please try again in a moment.")


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

    # Flood guard: ignore taps that arrive faster than the cooldown.
    now = time.time()
    if now - game["last_click"] < SCRAMBLE_CLICK_COOLDOWN:
        await cq.answer("Slow down a little…")
        return
    game["last_click"] = now

    try:
        async with game["lock"]:
            if gid not in _scramble_games:   # finished while we waited on the lock
                await cq.answer()
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
                await cq.answer()
                return

            try:
                idx = int(action)
            except ValueError:
                await cq.answer()
                return
            if not 0 <= idx < n:
                await cq.answer()
                return

            sel = game["selected"]

            # First tap (or tapping the selected piece again): just update the highlight.
            if sel is None or sel == idx:
                game["selected"] = idx if sel is None else None
                await cq.message.edit_caption(
                    caption=_scramble_caption(game, game["selected"]),
                    reply_markup=_scramble_kb(gid, game["selected"]),
                    parse_mode=ParseMode.HTML)
                await cq.answer()
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
                paid = _scramble_pay(str(cq.from_user.id), cq.from_user.first_name,
                                     cq.from_user.username, earned)
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
            await cq.answer("Solved!" if solved else None)
    except Exception as e:
        if "not modified" not in str(e).lower():
            print(f"[scramble_cb] failed: {e}")
            traceback.print_exc()
            dlog.error(f"[scramble_cb] failed: {e}", exc_info=True)
        try:
            await cq.answer()
        except Exception:
            pass
