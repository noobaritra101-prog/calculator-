"""
PROFILE BANNER SYSTEM (shared logic + all banner commands)
============================================================
Admin-managed pool of banner template images. Exactly one banner is the
global "default" at a time, and /profile (in handlers.py) composites the
viewing user's own Telegram profile picture into the round placeholder cut
into that banner, using Pillow. Users can also own individual banners
(currently only via promo code rewards — see `banner:amount:id` in
/add_promo) and pick one of their own as their personal "current" banner
via /mybanners, which overrides the default for their own /profile only;
get_active_banner_id() resolves that precedence for any given user.

This module holds everything banner-related: the detection/compositing
helpers, get_active_banner_id() / pick_redeemable_banner_id() (also used
by handlers.py's /redeem and a_handlers.py's /check and /add_promo),
build_profile_banner() (called from handlers.py's /profile), and every
banner command itself — admin-only /ab, /rb, /lbanner, /set_default, and
the user-facing /mybanners — registered directly on main_router here so
they come alive as soon as this module is imported.

Requires Pillow, numpy, and scipy (`pip install Pillow numpy scipy`).
"""
import os
import time
import math
import random
from io import BytesIO
from datetime import datetime, timezone
from typing import Optional

from PIL import Image, ImageDraw, ImageFont
import numpy as np
from scipy import ndimage

from aiogram import F
from aiogram.types import (
    Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton,
    InputMediaPhoto, FSInputFile
)
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode

from config import (
    bot, main_router, load_db, save_db, ADMIN_IDS, DB_GROUP_ID,
    get_mention, is_ghost_banned, is_shadow_banned, ensure_user
)

# ==========================================
# STORAGE
# ==========================================
# Downloaded banner images live on disk here — the db only stores metadata
# (name, file path, detected circle geometry, who added it, when). If this
# runs somewhere without a persistent volume, a redeploy can wipe this
# folder while the db entries survive; build_profile_banner() checks the
# file still exists and quietly falls back to the plain profile photo/text
# rather than crashing /profile if it's gone — just re-run /ab to restore it.
BANNERS_DIR = "banners"
os.makedirs(BANNERS_DIR, exist_ok=True)

# How close to pure white (0-255 per channel) a pixel must be to count as
# part of the circular placeholder cutout. Tight enough that bright colors
# elsewhere in a busy banner (gold lightning, oranges, etc.) don't get
# mistaken for it.
_WHITE_THRESHOLD = 245


async def get_current_profile_photo_file_id(user_id: int, big: bool = True) -> Optional[str]:
    """Returns the file_id for a user's *actually current* profile photo,
    or None if they have none / it can't be read.

    get_user_profile_photos() reads from the user's photo gallery (every
    photo they've ever set, newest first) and Telegram doesn't always
    refresh that list promptly after someone changes their photo — bots
    were seeing everyone's OLD photo composited into their banner even
    right after they'd updated it. get_chat() instead returns the chat's
    live `.photo` pointer, which reflects the current photo directly, so
    it's used first here. The gallery lookup is kept only as a fallback
    for the case get_chat() genuinely has no photo (e.g. it was somehow
    unset) but the gallery still has one on record."""
    try:
        chat = await bot.get_chat(user_id)
        if chat.photo:
            return chat.photo.big_file_id if big else chat.photo.small_file_id
    except Exception:
        pass

    try:
        photos = await bot.get_user_profile_photos(user_id, limit=1)
        if photos.total_count > 0:
            return photos.photos[0][-1 if big else 0].file_id
    except Exception:
        pass

    return None


async def ensure_banner_file(bid: str, meta: dict) -> bool:
    """Makes sure a banner's image actually exists on disk before it's used,
    self-healing it from Telegram if not.

    The banners/ folder can get wiped by a redeploy on hosts without a
    persistent disk (see the module docstring) even though `meta` — and the
    Telegram `file_id` it carries — survives in database.json. Telegram
    keeps that file_id valid indefinitely (it points at a copy of the image
    Telegram itself is still hosting), so we just re-download it back into
    place instead of leaving /profile, /lbanner, and /mybanners stuck
    showing "Image file missing" until an admin manually re-runs /ab.

    Returns True once a usable file is on disk (was already there, or the
    re-download succeeded), False if it's unrecoverable (e.g. no stored
    file_id, from a banner added before this existed)."""
    file_path = meta.get("file_path")
    if file_path and os.path.exists(file_path):
        return True

    file_id = meta.get("file_id")
    if not file_id or not file_path:
        return False

    try:
        os.makedirs(os.path.dirname(file_path) or ".", exist_ok=True)
        await bot.download(file_id, destination=file_path)
        return os.path.exists(file_path)
    except Exception:
        return False


def next_banner_id(db: dict) -> str:
    banners = db.get("banners", {})
    existing = [int(k) for k in banners.keys() if k.isdigit()]
    return str(max(existing, default=0) + 1)


def get_active_banner_id(db: dict, user_id) -> Optional[str]:
    """Resolves which banner id should be used for this user's /profile.

    A user's own pick (set via /mybanners) wins, but only while it's still
    a real banner they actually own and its file is still on disk —
    otherwise this quietly falls back to the shared admin-set default, the
    same as a user who never picked one at all."""
    uid = str(user_id)
    all_banners = db.get("banners", {})
    user_data = db.get("users", {}).get(uid, {})

    personal_id = user_data.get("current_banner_id")
    if personal_id and personal_id in all_banners and personal_id in user_data.get("banners", {}):
        if user_data["banners"][personal_id].get("amount", 0) > 0 and os.path.exists(all_banners[personal_id].get("file_path", "")):
            return personal_id

    default_id = db.get("settings", {}).get("default_banner_id")
    if default_id and default_id in all_banners:
        return default_id

    return None


def pick_redeemable_banner_id(db: dict, requested: str) -> Optional[str]:
    """Resolves a promo's `banner:amount:target` reward to a concrete
    banner id that a player can actually be awarded through /redeem.

    The current global default is always excluded from the eligible pool —
    every user already gets it for free on /profile, so "winning" it from
    a promo would be worthless. A banner an admin has locked with
    /lock_banner is excluded the same way, whether it was requested randomly
    or by specific id — see the /lock_banner section below. `requested == "r"`
    draws randomly from whatever remains; a specific id must exist and
    must not be the current default or locked. Returns None if nothing
    eligible is available."""
    all_banners = db.get("banners", {})
    default_id = db.get("settings", {}).get("default_banner_id")
    eligible = {bid: meta for bid, meta in all_banners.items()
                if bid != default_id and not meta.get("drop_locked")}

    requested = (requested or "r").strip().lower()
    if requested == "r":
        if not eligible:
            return None
        return random.choice(list(eligible.keys()))

    return requested if requested in eligible else None


def detect_circle(img: Image.Image) -> Optional[dict]:
    """Finds the largest near-white *connected region* in a banner template
    (not just the bounding box of every whitish pixel anywhere in the image
    — busy banners have plenty of those: cloud highlights, bright text,
    lightning, sparkle effects) and returns its center + radius, but only
    if that region is actually shaped like a filled circle. Returns None if
    no such region exists."""
    rgb = img.convert("RGB")
    arr = np.asarray(rgb)
    r, g, b = arr[..., 0].astype(int), arr[..., 1].astype(int), arr[..., 2].astype(int)
    mask = (r > _WHITE_THRESHOLD) & (g > _WHITE_THRESHOLD) & (b > _WHITE_THRESHOLD)
    if not mask.any():
        return None

    labeled, num_components = ndimage.label(mask)
    if num_components == 0:
        return None

    sizes = ndimage.sum(mask, labeled, range(1, num_components + 1))
    biggest_label = int(np.argmax(sizes)) + 1
    biggest_size = float(sizes[biggest_label - 1])

    ys, xs = np.where(labeled == biggest_label)
    x0, x1 = int(xs.min()), int(xs.max())
    y0, y1 = int(ys.min()), int(ys.max())
    width, height = x1 - x0, y1 - y0

    if width < 20 or height < 20:
        return None

    radius = min(width, height) / 2

    # A real filled circle's pixel count should land close to pi*r^2. This
    # is what actually rules out ovals, thin rings/borders, or an odd-shaped
    # white splash — the earlier width/height bounding-box check alone
    # can't tell those apart from a genuine circle.
    expected_area = math.pi * (radius ** 2)
    fill_ratio = biggest_size / expected_area if expected_area else 0
    if fill_ratio < 0.85 or fill_ratio > 1.15:
        return None

    return {
        "cx": (x0 + x1) / 2,
        "cy": (y0 + y1) / 2,
        "radius": radius,
    }


def _make_circular(img: Image.Image, size: int) -> Image.Image:
    """Center-crops to a square, resizes to `size`x`size`, and masks it
    into a circle (RGBA, transparent outside the circle)."""
    img = img.convert("RGBA")
    w, h = img.size
    side = min(w, h)
    left, top = (w - side) // 2, (h - side) // 2
    img = img.crop((left, top, left + side, top + side)).resize((size, size), Image.LANCZOS)

    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size, size), fill=255)
    out = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    out.paste(img, (0, 0), mask)
    return out


def _placeholder_avatar(name: str, size: int) -> Image.Image:
    """Used when the user has no Telegram profile photo (or it couldn't be
    fetched) — a plain colored circle with their first initial, so the
    banner still shows something in the frame instead of a blank hole."""
    colors = ["#7C3AED", "#2563EB", "#DC2626", "#059669", "#D97706", "#DB2777"]
    safe_name = name or "?"
    initial = safe_name.strip()[:1].upper() or "?"
    color = colors[sum(map(ord, safe_name)) % len(colors)]

    img = Image.new("RGBA", (size, size), color)
    draw = ImageDraw.Draw(img)
    try:
        font = ImageFont.truetype("DejaVuSans-Bold.ttf", int(size * 0.5))
    except Exception:
        font = ImageFont.load_default()
    bbox = draw.textbbox((0, 0), initial, font=font)
    tw, th = bbox[2] - bbox[0], bbox[3] - bbox[1]
    draw.text(((size - tw) / 2 - bbox[0], (size - th) / 2 - bbox[1]), initial, fill="white", font=font)

    mask = Image.new("L", (size, size), 0)
    ImageDraw.Draw(mask).ellipse((0, 0, size, size), fill=255)
    out = Image.new("RGBA", (size, size), (0, 0, 0, 0))
    out.paste(img, (0, 0), mask)
    return out


async def build_profile_banner(user_id: int, first_name: str) -> Optional[BytesIO]:
    """Returns a ready-to-send JPEG (the default banner with the user's own
    Telegram profile picture composited into its circle), or None if there's
    no default banner set / its file is missing — callers should fall back
    to the plain profile photo/text in that case."""
    db = load_db()
    active_id = get_active_banner_id(db, user_id)
    if not active_id:
        return None

    banner_meta = db.get("banners", {}).get(active_id)
    if not banner_meta or not await ensure_banner_file(active_id, banner_meta):
        return None

    try:
        banner = Image.open(banner_meta["file_path"]).convert("RGBA")
    except Exception:
        return None

    circle = banner_meta["circle"]
    size = max(1, int(circle["radius"] * 2))

    try:
        file_id = await get_current_profile_photo_file_id(user_id, big=True)
        if file_id:
            buf = await bot.download(file_id)
            circular_pfp = _make_circular(Image.open(buf), size)
        else:
            circular_pfp = _placeholder_avatar(first_name, size)
    except Exception:
        circular_pfp = _placeholder_avatar(first_name, size)

    paste_x = int(circle["cx"] - circle["radius"])
    paste_y = int(circle["cy"] - circle["radius"])
    banner.paste(circular_pfp, (paste_x, paste_y), circular_pfp)

    out = BytesIO()
    banner.convert("RGB").save(out, format="JPEG", quality=92)
    out.seek(0)
    return out


# ==========================================
# /ab <name> — ADD BANNER (ADMIN ONLY, reply to a photo)
# ==========================================
@main_router.message(Command("ab"))
async def add_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not message.reply_to_message or not message.reply_to_message.photo:
        await message.reply(
            "<b>Usage:</b> reply to a photo with <code>/ab &lt;name&gt;</code>\n"
            "The photo needs one plain white circular area — that's where each "
            "user's own profile picture gets composited in.",
            parse_mode=ParseMode.HTML
        )
        return

    name = (command.args or "").strip()
    if not name:
        await message.reply("<b>Usage:</b> reply to a photo with <code>/ab &lt;name&gt;</code>", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    banner_id = next_banner_id(db)
    file_path = os.path.join(BANNERS_DIR, f"{banner_id}.png")

    file_id = message.reply_to_message.photo[-1].file_id
    await bot.download(file_id, destination=file_path)

    try:
        circle = detect_circle(Image.open(file_path))
    except Exception:
        circle = None

    if not circle:
        try:
            os.remove(file_path)
        except Exception:
            pass
        await message.reply(
            "Couldn't find a white circle placeholder in that image.\n"
            "Make sure it has one solid, roughly-circular white area for the profile picture to go into.",
            parse_mode=ParseMode.HTML
        )
        return

    banners_db = db.setdefault("banners", {})

    added_by_mention = get_mention(message.from_user.id, message.from_user.first_name)
    log_text = (
        "<b>「 📥 DATABASE LOG : NEW BANNER 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        "<blockquote><i>A new profile banner template has been registered globally.</i></blockquote>\n\n"
        f"• 🆔 <b>Banner ID:</b> <code>{banner_id}</code>\n"
        f"• 🏷️ <b>Name:</b> <b>{name}</b>\n"
        f"• ⭕ <b>Circle:</b> ~{int(circle['radius'] * 2)}px diameter\n"
        f"• — <b>Added By:</b> {added_by_mention}\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    msg_id = None
    try:
        msg = await bot.send_photo(DB_GROUP_ID, photo=file_id, caption=log_text, parse_mode=ParseMode.HTML)
        msg_id = msg.message_id
    except Exception as e:
        print(f"[LOG_GROUP] Banner send failed: {e}")

    banners_db[banner_id] = {
        "name": name,
        "file_path": file_path,
        "file_id": file_id,
        "circle": circle,
        "msg_id": msg_id,
        "added_by": str(message.from_user.id),
        "added_at": int(time.time()),
    }
    save_db()

    await message.reply(
        f"<b>Banner added</b>\n"
        f"ID: <code>{banner_id}</code>\n"
        f"Name: {name}\n"
        f"Detected circle: ~{int(circle['radius'] * 2)}px diameter\n\n"
        f"Use <code>/set_default {banner_id}</code> to make it active for everyone's /profile.",
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /rb <banner_id> — REMOVE BANNER (ADMIN ONLY)
# ==========================================
@main_router.message(Command("rb"))
async def remove_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args or not command.args.strip():
        await message.reply("<b>Usage:</b> <code>/rb &lt;banner_id&gt;</code>", parse_mode=ParseMode.HTML)
        return

    banner_id = command.args.strip()
    db = load_db()
    banners_db = db.get("banners", {})

    if banner_id not in banners_db:
        await message.reply("No banner with that ID. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
        return

    file_path = banners_db[banner_id].get("file_path")
    name = banners_db[banner_id].get("name", "Unnamed")
    msg_id = banners_db[banner_id].get("msg_id")
    del banners_db[banner_id]

    was_default = db.get("settings", {}).get("default_banner_id") == banner_id
    if was_default:
        db.setdefault("settings", {})["default_banner_id"] = None

    save_db()

    if file_path and os.path.exists(file_path):
        try:
            os.remove(file_path)
        except Exception:
            pass

    if msg_id:
        try:
            await bot.delete_message(chat_id=DB_GROUP_ID, message_id=msg_id)
        except Exception:
            pass

    note = ""
    if was_default:
        note = "\n\n<i>This was the default banner — /profile will show plain profile photos again until a new default is set.</i>"
    await message.reply(f"Removed banner <b>{name}</b> (<code>{banner_id}</code>).{note}", parse_mode=ParseMode.HTML)


# ==========================================
# /eb <banner_id> | <new name> — EDIT BANNER (ADMIN ONLY)
# ==========================================
# Mirrors a_handlers.py's /edit_card: reply to a new photo to swap the
# image (re-detecting its circle placeholder), otherwise just renames it.
# Owned-banner records only ever store {bid: {"amount": N}} — no name
# snapshot like cards have — so there's nothing to sync out to owners here.
@main_router.message(Command("eb"))
async def edit_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args or not command.args.strip():
        await message.reply(
            "<b>Usage:</b> <code>/eb &lt;banner_id&gt; | &lt;new name&gt;</code>\n\n"
            "<i>Note: To change the picture, reply to a new image with this command. "
            "If you don't reply to an image, the old picture is kept. Leave the name "
            "blank after the pipe (or omit the pipe entirely) to keep the old name.</i>",
            parse_mode=ParseMode.HTML
        )
        return

    args = command.args.split("|")
    banner_id = args[0].strip()

    db = load_db()
    banners_db = db.get("banners", {})
    if banner_id not in banners_db:
        await message.reply(f"No banner with ID <code>{banner_id}</code>. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
        return

    meta = banners_db[banner_id]
    old_name = meta.get("name", "Unnamed")
    new_name = args[1].strip() if len(args) > 1 and args[1].strip() else old_name

    file_path = meta.get("file_path") or os.path.join(BANNERS_DIR, f"{banner_id}.png")
    new_circle = meta.get("circle")
    new_file_id = meta.get("file_id")
    photo_changed = False

    if message.reply_to_message and message.reply_to_message.photo:
        candidate_file_id = message.reply_to_message.photo[-1].file_id
        tmp_path = file_path + ".new"
        await bot.download(candidate_file_id, destination=tmp_path)

        try:
            detected = detect_circle(Image.open(tmp_path))
        except Exception:
            detected = None

        if not detected:
            try:
                os.remove(tmp_path)
            except Exception:
                pass
            await message.reply(
                "Couldn't find a white circle placeholder in that new image — the old banner was left unchanged.\n"
                "Make sure it has one solid, roughly-circular white area for the profile picture to go into.",
                parse_mode=ParseMode.HTML
            )
            return

        os.replace(tmp_path, file_path)
        new_circle = detected
        new_file_id = candidate_file_id
        photo_changed = True

    meta["name"] = new_name
    meta["file_path"] = file_path
    meta["file_id"] = new_file_id
    meta["circle"] = new_circle
    save_db()

    changes = []
    if new_name != old_name:
        changes.append(f"name: '{old_name}' → '{new_name}'")
    if photo_changed:
        changes.append(f"photo updated (~{int(new_circle['radius'] * 2)}px circle)")

    log_text = (
        "<b>「 📥 DATABASE LOG : BANNER EDITED 」</b>\n"
        "━━━━━━━━━━━━━━━━━━━\n\n"
        f"• 🆔 <b>Banner ID:</b> <code>{banner_id}</code>\n"
        f"• 🏷️ <b>Name:</b> <b>{new_name}</b>\n"
        f"• ⭕ <b>Circle:</b> ~{int(new_circle['radius'] * 2)}px diameter\n"
        "━━━━━━━━━━━━━━━━━━━"
    )

    msg_id = meta.get("msg_id")
    if msg_id:
        try:
            if photo_changed:
                await bot.edit_message_media(
                    chat_id=DB_GROUP_ID,
                    message_id=msg_id,
                    media=InputMediaPhoto(media=new_file_id, caption=log_text, parse_mode=ParseMode.HTML)
                )
            else:
                await bot.edit_message_caption(
                    chat_id=DB_GROUP_ID,
                    message_id=msg_id,
                    caption=log_text,
                    parse_mode=ParseMode.HTML
                )
        except Exception as e:
            print(f"[EDIT_BANNER] Failed to update group log message: {e}")

    await message.reply(
        f"✅ Banner <code>{banner_id}</code> updated successfully!"
        + (f"\n\n<b>Changes:</b> " + "; ".join(changes) if changes else "\n\n<i>No fields changed.</i>"),
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /lbanner — LIST ALL BANNERS, ONE PER PAGE WITH PICTURE (ADMIN ONLY)
# ==========================================
async def _show_lbanner_page(event, edit=False, page=0):
    db = load_db()
    banners_db = db.get("banners", {})
    default_id = db.get("settings", {}).get("default_banner_id")

    if not banners_db:
        text = "No banners added yet. Reply to a photo with <code>/ab &lt;name&gt;</code> to add one."
        kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Close", callback_data="close_msg")]])
        if edit and isinstance(event, CallbackQuery):
            try:
                await event.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            except Exception:
                try:
                    await event.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
                except Exception:
                    pass
        else:
            target = event.message if isinstance(event, CallbackQuery) else event
            await target.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        return

    ordered_ids = sorted(banners_db.keys(), key=lambda x: int(x))
    total = len(ordered_ids)
    if page >= total: page = total - 1
    if page < 0: page = 0

    bid = ordered_ids[page]
    meta = banners_db[bid]
    is_default = (bid == default_id)
    is_locked = bool(meta.get("drop_locked"))

    added_by_mention = get_mention(int(meta.get("added_by", 0) or 0), "Unknown") if meta.get("added_by") else "Unknown"
    added_at = meta.get("added_at")
    added_line = datetime.fromtimestamp(added_at, tz=timezone.utc).strftime("%Y-%m-%d") if added_at else "Unknown"

    caption = (
        f"<b>「 🖼️ BANNER LIST 」</b>\n━━━━━━━━━━━━━━━━━\n\n"
        f"• 🆔 <b>ID:</b> <code>{bid}</code>\n"
        f"• 🏷️ <b>Name:</b> {meta.get('name', 'Unnamed')}\n"
        f"• ⭕ <b>Circle:</b> ~{int(meta.get('circle', {}).get('radius', 0) * 2)}px diameter\n"
        f"• — <b>Added By:</b> {added_by_mention}\n"
        f"• 📅 <b>Added:</b> {added_line}\n"
        f"• 🌐 <b>Status:</b> {'<b>Default</b> ✅' if is_default else 'Not default'}\n"
        f"• 🔐 <b>Drop:</b> {'🔒 Locked' if is_locked else '🔓 Unlocked'}\n\n"
        f"Page <b>{page+1}/{total}</b>"
    )

    buttons = []

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="Previous", callback_data=f"lb_page|{page-1}"))
    if page < total - 1:
        nav.append(InlineKeyboardButton(text="Next", callback_data=f"lb_page|{page+1}"))
    if nav:
        buttons.append(nav)
    buttons.append([InlineKeyboardButton(text="Close", callback_data="close_msg")])

    markup = InlineKeyboardMarkup(inline_keyboard=buttons)

    file_path = meta.get("file_path")
    photo_ok = await ensure_banner_file(bid, meta)

    if edit and isinstance(event, CallbackQuery):
        try:
            if photo_ok:
                await event.message.edit_media(
                    InputMediaPhoto(media=FSInputFile(file_path), caption=caption, parse_mode=ParseMode.HTML),
                    reply_markup=markup
                )
            else:
                await event.message.edit_caption(caption=caption + "\n\n<i>⚠️ Image file missing on disk.</i>", reply_markup=markup, parse_mode=ParseMode.HTML)
        except Exception:
            pass
    else:
        target = event.message if isinstance(event, CallbackQuery) else event
        if photo_ok:
            await target.reply_photo(photo=FSInputFile(file_path), caption=caption, reply_markup=markup, parse_mode=ParseMode.HTML)
        else:
            await target.reply(caption + "\n\n<i>⚠️ Image file missing on disk.</i>", reply_markup=markup, parse_mode=ParseMode.HTML)


@main_router.message(Command("lbanner"))
async def list_banners_cmd(message: Message):
    if message.from_user.id not in ADMIN_IDS:
        return
    await _show_lbanner_page(message)


@main_router.callback_query(F.data.startswith("lb_page|"))
async def lbanner_page_cb(cq: CallbackQuery):
    if cq.from_user.id not in ADMIN_IDS:
        await cq.answer("⚠️ Admin restricted.", show_alert=True)
        return
    page = int(cq.data.split("|")[1])
    await cq.answer()
    await _show_lbanner_page(cq, edit=True, page=page)


# ==========================================
# /set_default <banner_id> — SET GLOBAL DEFAULT BANNER (ADMIN ONLY)
# ==========================================
@main_router.message(Command("set_default"))
async def set_default_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args or not command.args.strip():
        await message.reply("<b>Usage:</b> <code>/set_default &lt;banner_id&gt;</code>", parse_mode=ParseMode.HTML)
        return

    banner_id = command.args.strip()
    db = load_db()
    banners_db = db.get("banners", {})

    if banner_id not in banners_db:
        await message.reply("No banner with that ID. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
        return

    db.setdefault("settings", {})["default_banner_id"] = banner_id
    save_db()

    await message.reply(
        f"Default banner set to <b>{banners_db[banner_id].get('name', 'Unnamed')}</b> (<code>{banner_id}</code>) for all users.",
        parse_mode=ParseMode.HTML
    )


# ==========================================
# /lock_banner <banner_id> — EXCLUDE FROM PROMO REWARD POOL (ADMIN ONLY)
# /unlock_banner <banner_id> — RE-ALLOW IN PROMO REWARD POOL (ADMIN ONLY)
# ==========================================
# Locking a banner excludes it from pick_redeemable_banner_id() — the
# resolver /redeem uses for a promo's `banner:` reward — the same way the
# current default is already excluded. A locked banner can't be handed
# out whether drawn randomly (`banner:amount:r`) or targeted by its exact
# ID (`banner:amount:<id>`); it just stays visible/browsable everywhere
# else (/lbanner, /profile if set default, /mybanners for anyone who
# already owns it). A promo already referencing a banner by ID before it
# gets locked simply stops paying out that reward on future redeems, the
# same silent-skip behavior as a removed or now-default target.
@main_router.message(Command("lock_banner"))
async def lock_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args or not command.args.strip():
        await message.reply("<b>Usage:</b> <code>/lock_banner &lt;banner_id&gt;</code>", parse_mode=ParseMode.HTML)
        return

    banner_id = command.args.strip()
    db = load_db()
    banners_db = db.get("banners", {})

    if banner_id not in banners_db:
        await message.reply("No banner with that ID. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
        return

    meta = banners_db[banner_id]
    name = meta.get("name", "Unnamed")

    if meta.get("drop_locked"):
        await message.reply(f"🔒 <b>{name}</b> (<code>{banner_id}</code>) is already locked from drops.", parse_mode=ParseMode.HTML)
        return

    meta["drop_locked"] = True
    save_db()

    await message.reply(
        f"🔒 Locked <b>{name}</b> (<code>{banner_id}</code>) — it will no longer be awarded via /redeem, "
        "random or targeted.",
        parse_mode=ParseMode.HTML
    )


@main_router.message(Command("unlock_banner"))
async def unlock_banner_cmd(message: Message, command: CommandObject):
    if message.from_user.id not in ADMIN_IDS:
        return

    if not command.args or not command.args.strip():
        await message.reply("<b>Usage:</b> <code>/unlock_banner &lt;banner_id&gt;</code>", parse_mode=ParseMode.HTML)
        return

    banner_id = command.args.strip()
    db = load_db()
    banners_db = db.get("banners", {})

    if banner_id not in banners_db:
        await message.reply("No banner with that ID. Use /lbanner to see available IDs.", parse_mode=ParseMode.HTML)
        return

    meta = banners_db[banner_id]
    name = meta.get("name", "Unnamed")

    if not meta.get("drop_locked"):
        await message.reply(f"🔓 <b>{name}</b> (<code>{banner_id}</code>) isn't locked.", parse_mode=ParseMode.HTML)
        return

    meta["drop_locked"] = False
    save_db()

    await message.reply(f"🔓 Unlocked <b>{name}</b> (<code>{banner_id}</code>) — it's eligible for /redeem again.", parse_mode=ParseMode.HTML)


# ==========================================
# PERSONAL BANNER PICKER (/mybanners)
# ==========================================
# Banners a user owns (currently only obtainable via a promo's `banner:`
# reward — see a_handlers.py's /add_promo) can be browsed here one at a
# time with a picture, and set as that user's personal "current" banner,
# which overrides the shared admin default for their own /profile only.
# See get_active_banner_id() above for the precedence this feeds into.
async def _show_my_banners(event, user_id: str, edit=False, page=0, origin="std"):
    # origin distinguishes how this view was entered: "std" for the plain
    # /mybanners command (last button is "Close" — deletes the message),
    # "profile" for the "Change Banner" button on /profile (last button is
    # "Back" — returns to the profile card via mb_back instead). Every
    # nav/action button below re-threads `origin` into its own
    # callback_data so it stays consistent across pages.
    db = load_db()
    user_data = db.get("users", {}).get(user_id, {})
    all_banners = db.get("banners", {})
    default_id = db.get("settings", {}).get("default_banner_id")

    owned = {bid: m for bid, m in user_data.get("banners", {}).items()
             if m.get("amount", 0) > 0 and bid in all_banners}

    # The server default is always included in the browse list too — even
    # for a user who's never been directly awarded it — since it's what
    # /profile actually falls back to. It just isn't counted as "owned".
    page_ids = sorted(owned.keys(), key=lambda x: int(x))
    if default_id and default_id in all_banners and default_id not in page_ids:
        page_ids = [default_id] + page_ids

    current_id = user_data.get("current_banner_id")

    def _last_button():
        if origin == "profile":
            return InlineKeyboardButton(text="Back", callback_data=f"mb_back|{user_id}")
        return InlineKeyboardButton(text="Close", callback_data=f"close_msg|{user_id}")

    if not page_ids:
        text = (
            "<b>My Banners</b>\n\n"
            "You don't own any banners yet, and no server default banner is set up. "
            "Banners can be won from promo codes."
        )
        kb = InlineKeyboardMarkup(inline_keyboard=[[_last_button()]])
        if edit and isinstance(event, CallbackQuery):
            try:
                await event.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            except Exception:
                try:
                    await event.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
                except Exception:
                    pass
        else:
            target = event.message if isinstance(event, CallbackQuery) else event
            await target.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        return

    total = len(page_ids)
    if page >= total: page = total - 1
    if page < 0: page = 0

    bid = page_ids[page]
    meta = all_banners.get(bid, {})
    is_owned = bid in owned
    amount = owned.get(bid, {}).get("amount")
    is_default = (bid == default_id)
    is_current = (bid == current_id) or (current_id is None and is_default)

    tags = []
    if is_current: tags.append("Currently Active")
    if is_default: tags.append("Server Default")
    tag_line = f"\nStatus: {' , '.join(tags)}" if tags else ""
    owned_line = f"Owned: x{amount}" if is_owned else "Owned: Free (Server Default)"

    caption = (
        f"<b>My Banners</b>\n\n"
        f"Name: {meta.get('name', 'Unnamed')}\n"
        f"ID: <code>{bid}</code>\n"
        f"{owned_line}{tag_line}\n\n"
        f"Page {page+1}/{total}"
    )

    action_row = []
    if is_owned and not is_current:
        action_row.append(InlineKeyboardButton(text="Set as Current", callback_data=f"mb_set|{user_id}|{bid}|{page}|{origin}"))
    if current_id is not None:
        action_row.append(InlineKeyboardButton(text="Use Default", callback_data=f"mb_def|{user_id}|{page}|{origin}"))

    buttons = []
    if action_row:
        buttons.append(action_row)

    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="Prev", callback_data=f"mb_page|{user_id}|{page-1}|{origin}"))
    if page < total - 1:
        nav.append(InlineKeyboardButton(text="Next", callback_data=f"mb_page|{user_id}|{page+1}|{origin}"))
    if nav:
        buttons.append(nav)
    buttons.append([_last_button()])

    markup = InlineKeyboardMarkup(inline_keyboard=buttons)

    file_path = meta.get("file_path")
    photo_ok = await ensure_banner_file(bid, meta)

    if edit and isinstance(event, CallbackQuery):
        try:
            if photo_ok:
                await event.message.edit_media(
                    InputMediaPhoto(media=FSInputFile(file_path), caption=caption, parse_mode=ParseMode.HTML),
                    reply_markup=markup
                )
            else:
                await event.message.edit_caption(caption=caption + "\n\nImage file missing.", reply_markup=markup, parse_mode=ParseMode.HTML)
        except Exception:
            pass
    else:
        target = event.message if isinstance(event, CallbackQuery) else event
        if photo_ok:
            await target.reply_photo(photo=FSInputFile(file_path), caption=caption, reply_markup=markup, parse_mode=ParseMode.HTML)
        else:
            await target.reply(caption + "\n\nImage file missing.", reply_markup=markup, parse_mode=ParseMode.HTML)


@main_router.message(Command("mybanners"))
async def mybanners_cmd(message: Message):
    uid_int = message.from_user.id
    if is_ghost_banned(uid_int) or is_shadow_banned(uid_int): return
    ensure_user(str(uid_int), message.from_user.first_name, message.from_user.username)
    await _show_my_banners(message, str(uid_int))


@main_router.callback_query(F.data.startswith("mb_open|"))
async def mybanners_open_cb(cq: CallbackQuery):
    # Entry point for the "Change Banner" button on /profile — opens the
    # same paged view as /mybanners, edited in place over the profile card.
    # Always origin="profile" since this button only ever lives on /profile.
    owner_id = cq.data.split("|")[1]
    if str(cq.from_user.id) != owner_id:
        await cq.answer("This isn't your profile!", show_alert=True)
        return
    await cq.answer()
    await _show_my_banners(cq, owner_id, edit=True, page=0, origin="profile")


@main_router.callback_query(F.data.startswith("mb_page|"))
async def mybanners_page_cb(cq: CallbackQuery):
    parts = cq.data.split("|")
    owner_id, page = parts[1], int(parts[2])
    origin = parts[3] if len(parts) > 3 else "std"
    if str(cq.from_user.id) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return
    await cq.answer()
    await _show_my_banners(cq, owner_id, edit=True, page=page, origin=origin)


@main_router.callback_query(F.data.startswith("mb_set|"))
async def mybanners_set_cb(cq: CallbackQuery):
    parts = cq.data.split("|")
    owner_id, bid, page = parts[1], parts[2], int(parts[3])
    origin = parts[4] if len(parts) > 4 else "std"
    if str(cq.from_user.id) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    db = load_db()
    user_data = db.setdefault("users", {}).setdefault(owner_id, {})
    owned = user_data.get("banners", {})
    if bid not in owned or owned[bid].get("amount", 0) <= 0:
        await cq.answer("You no longer own that banner.", show_alert=True)
        return

    user_data["current_banner_id"] = bid
    save_db()
    await cq.answer("Set as your current banner.")
    await _show_my_banners(cq, owner_id, edit=True, page=page, origin=origin)


@main_router.callback_query(F.data.startswith("mb_def|"))
async def mybanners_default_cb(cq: CallbackQuery):
    parts = cq.data.split("|")
    owner_id, page = parts[1], int(parts[2])
    origin = parts[3] if len(parts) > 3 else "std"
    if str(cq.from_user.id) != owner_id:
        await cq.answer("This menu is not for you!", show_alert=True)
        return

    db = load_db()
    user_data = db.setdefault("users", {}).setdefault(owner_id, {})
    user_data["current_banner_id"] = None
    save_db()
    await cq.answer("Reverted to the server default banner.")
    await _show_my_banners(cq, owner_id, edit=True, page=page, origin=origin)
