import time
import uuid
import random
import asyncio
import logging
from aiogram import F
from aiogram.types import Message, CallbackQuery, InlineKeyboardMarkup, InlineKeyboardButton, InputMediaPhoto, InputRichMessage, LabeledPrice, PreCheckoutQuery
from aiogram.filters import Command, CommandObject
from aiogram.enums import ParseMode, ButtonStyle
from datetime import datetime, timezone, timedelta

from fastapi import APIRouter, HTTPException
from pydantic import BaseModel

import config
from config import (
    bot, main_router, load_db, save_db, ensure_user, 
    format_rarity, SHOP_PRICES, OFFLINE_STORE_GROUP
)
from vlog import log_action

# Reuses the SAME logger instance deck.py configures (Python's logging module
# caches loggers by name globally), so store errors land in the same dlog.txt
# and are retrievable via /dlog without any extra setup here.
dlog = logging.getLogger("deck_dlog")

store_api = APIRouter(prefix="/api/store", tags=["Store"])

# ==========================================
# PRIVACY CHECK HELPER
# ==========================================
async def verify_user(cq: CallbackQuery, target_id: str) -> bool:
    """Ensures only the user who executed the command can use the buttons."""
    if str(cq.from_user.id) != str(target_id):
        await cq.answer("This menu is not for you!", show_alert=True)
        return False
    return True

def is_divine_day() -> bool:
    """The Divine slot only appears on Sundays (UTC, matching the daily shop reset)."""
    return datetime.now(timezone.utc).weekday() == 6  # Monday=0 ... Sunday=6

def time_until_shop_reset() -> str:
    """Returns a human-readable 'Xh Ym' countdown until the next midnight UTC
    shop reset, matching the existing 'Resets at midnight UTC' rotation."""
    now = datetime.now(timezone.utc)
    tomorrow = now.date() + timedelta(days=1)
    reset_at = datetime.combine(tomorrow, datetime.min.time(), tzinfo=timezone.utc)
    remaining = reset_at - now
    total_minutes = max(0, int(remaining.total_seconds() // 60))
    hours, minutes = divmod(total_minutes, 60)
    return f"{hours}h {minutes}m"

# ==========================================
# PURCHASE LOCKS
# ==========================================
# Fixes: users opening /store in two chats/sessions and tapping "Confirm
# Purchase" almost simultaneously could buy the same card 2-3 times.
# The old code did load_db() -> check "already bought"/"enough shards" ->
# mutate -> save_db() with no atomicity, so two concurrent taps could both
# pass the check before either one saved. Wrapping the whole
# check-then-act sequence in an asyncio.Lock per key makes the second tap
# wait for the first to finish (and see the now-updated state) before it
# even reads the DB, so it correctly gets rejected as "already bought" /
# "listing no longer available".
_action_locks: dict[str, asyncio.Lock] = {}

def _get_lock(key: str) -> asyncio.Lock:
    lock = _action_locks.get(key)
    if lock is None:
        lock = asyncio.Lock()
        _action_locks[key] = lock
    return lock

# ==========================================
# STALE BUTTON GUARD (Online Store)
# ==========================================
# A refresh (or a day rollover) replaces rolled_basic/rolled_elite/
# rolled_divine and clears "bought". Any /store message the user still has
# open from BEFORE that point keeps showing "Buy <old card>" buttons that
# reference a card no longer in today's actual rotation. Nothing previously
# checked that — only "does the card exist" and "is it already bought" —
# so a stale button from an old/duplicate /store view could still be used
# to buy a card that's no longer being offered. This closes that gap.
def _is_live_online_offer(dp: dict, card_id: str) -> bool:
    """True only if card_id is one of TODAY's currently active roll slots."""
    if not dp or dp.get("date") != config.get_shop_rotation_seed():
        return False
    return card_id in (dp.get("rolled_basic"), dp.get("rolled_elite"), dp.get("rolled_divine"))

async def _reject_stale_online_offer(cq: CallbackQuery, uid: str):
    """Tell the user this button is from an outdated store view instead of
    silently processing (or silently failing on) a stale card reference."""
    await cq.answer("⚠️ This offer has expired — the store has moved on. Please open a fresh /store.", show_alert=True)
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🔄 Open Fresh Store", callback_data=f"st_on_{uid}", style=ButtonStyle.PRIMARY)]])
    expired_text = (
        "<b>「 ⚠️ EXPIRED 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "This store view is outdated — it was refreshed or reset elsewhere.\n"
        "Tap below to see the current selection."
    )
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=expired_text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(expired_text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass

# ==========================================
# STAR SHOP (real Telegram Stars — XTR)
# ==========================================
# Catalog lives in the DB now, not in code, so it can be managed live:
#   db["star_shop"][card_id] = {"price": <stars>, "limit": <int, 0=unlimited>, "sold": <int>}
# Managed via the admin-only /astar, /rstar, /allstar commands below.
# Every card, regardless of limit, can still only be bought ONCE per user
# (tracked in star_purchases) — "limit" caps TOTAL copies sold across everyone.

def _star_purchases(user_data: dict) -> list:
    return user_data.setdefault("star_purchases", [])

def _star_shop_catalog(db: dict) -> dict:
    return db.setdefault("star_shop", {})

def _is_star_admin(uid: int) -> bool:
    return uid in config.ADMIN_IDS

def _build_star_shop_view(uid: str, db: dict) -> tuple[str, InlineKeyboardMarkup]:
    user_data = db["users"][uid]
    bought = _star_purchases(user_data)
    catalog = _star_shop_catalog(db)

    text = "「 ⭐ 𝗦𝗧𝗔𝗥 𝗦𝗛𝗢𝗣 」\n━━━━━━━━━━━━━━━━━\n"
    kb_list = []
    for card_id, entry in catalog.items():
        card_data = db["global_cards"].get(card_id)
        if not card_data:
            continue
        rarity = format_rarity(card_data["rarity"])
        price = entry.get("price", 0)
        limit = entry.get("limit", 0)
        sold = entry.get("sold", 0)
        label = f"<b>{card_data['name']} ({rarity}) :</b>"

        if card_id in bought:
            text += f"{label} ✅ Owned\n"
            continue

        sold_out = limit > 0 and sold >= limit
        stock_str = f" ({sold}/{limit} sold)" if limit > 0 else ""
        view_btn = InlineKeyboardButton(text=f"{card_data['name']}", callback_data=f"starview_{uid}_{card_id}")
        if sold_out:
            text += f"{label} 🚫 Sold Out{stock_str}\n"
            kb_list.append([view_btn, InlineKeyboardButton(text="Sold Out", callback_data="noop", style=ButtonStyle.DANGER)])
            continue

        text += f"{label} {price} ⭐{stock_str}\n"
        kb_list.append([view_btn, InlineKeyboardButton(text=f"Buy — {price} Stars", callback_data=f"buystar_{uid}_{card_id}", style=ButtonStyle.SUCCESS)])

    if not catalog:
        text += "<i>Nothing on sale right now — check back later!</i>\n"
    text += (
        "━━━━━━━━━━━━━━━━━\n"
        "<blockquote>Buy these cards outright with real Telegram Stars.\n"
        "Each card can only be bought once per account.</blockquote>"
    )
    kb_list.append([InlineKeyboardButton(text="Custom Cards", callback_data=f"customcard_{uid}", style=ButtonStyle.PRIMARY)])
    kb_list.append([InlineKeyboardButton(text="Privacy Policy", callback_data=f"starpolicy_{uid}", style=ButtonStyle.PRIMARY)])
    kb_list.append([InlineKeyboardButton(text="Back", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)])
    return text, InlineKeyboardMarkup(inline_keyboard=kb_list)


@main_router.callback_query(F.data.startswith("starview_"))
async def star_shop_view_card_cb(cq: CallbackQuery):
    """Lets a player see the actual card art before buying — tapping a
    card's 🖼️ button swaps the Star Shop text view for a photo preview."""
    parts = cq.data.split("_")
    uid, card_id = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    db = load_db()
    card_data = db["global_cards"].get(card_id)
    if not card_data:
        await cq.answer("This card no longer exists.", show_alert=True)
        return

    entry = db.get("star_shop", {}).get(card_id, {})
    rarity = format_rarity(card_data["rarity"])
    caption = (
        "<b>「 🃏 CARD PREVIEW 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"Name: <b>{card_data['name']}</b>\n"
        f"Rarity: {rarity}\n"
        f"Anime: {card_data.get('anime', 'Unknown')}\n"
        f"Price: {entry.get('price', 0)} ⭐"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Back to Star Shop", callback_data=f"st_star_{uid}", style=ButtonStyle.DANGER)]])

    try:
        if cq.message.photo:
            await cq.message.edit_media(InputMediaPhoto(media=card_data["file_id"], caption=caption, parse_mode=ParseMode.HTML, has_spoiler=True), reply_markup=kb)
        else:
            await cq.message.delete()
            await bot.send_photo(chat_id=cq.message.chat.id, photo=card_data["file_id"], caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML, has_spoiler=True)
    except Exception:
        pass
    await cq.answer()


# ------------------------------------------
# Custom Card commissions (DM-only request → notifies the owner)
# ------------------------------------------
CUSTOM_CARD_OWNER_ID = 5716292610

@main_router.callback_query(F.data.startswith("customcard_"))
async def custom_card_request_cb(cq: CallbackQuery):
    uid = cq.data.split("_", 1)[1]
    if not await verify_user(cq, uid): return

    if cq.message.chat.type != "private":
        await cq.answer("⚠️ Custom Card requests only work in a private DM with the bot — message me directly to use this.", show_alert=True)
        return

    user = cq.from_user
    safe_name = str(user.first_name or "User").replace("<", "&lt;").replace(">", "&gt;")
    mention = f'<a href="tg://user?id={uid}">{safe_name}</a>'
    username_str = f"@{user.username}" if user.username else "—"

    try:
        await bot.send_message(
            chat_id=CUSTOM_CARD_OWNER_ID,
            text=(
                "<b>「 🎨 CUSTOM CARD REQUEST 」</b>\n"
                "━━━━━━━━━━━━━━━━━\n"
                f"From: {mention}\n"
                f"User ID: <code>{uid}</code>\n"
                f"Username: {username_str}\n"
                "━━━━━━━━━━━━━━━━━\n"
                "They tapped 🎨 Custom Cards in the Star Shop — DM them to discuss what they want made and the price."
            ),
            parse_mode=ParseMode.HTML
        )
    except Exception as e:
        dlog.error(f"[custom_card_request_CRASH] uid={uid}: {e}", exc_info=True)
        await cq.answer("Couldn't send your request — please try again later.", show_alert=True)
        return

    await cq.answer("✅ Request sent! You'll be contacted directly to discuss your custom card.", show_alert=True)


@main_router.callback_query(F.data.startswith("starpolicy_"))
async def star_shop_policy_cb(cq: CallbackQuery):
    uid = cq.data.split("_", 1)[1]
    if not await verify_user(cq, uid): return

    text = (
        "<b>「 📜 STAR SHOP POLICY 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "<blockquote>"
        "All Star Shop purchases are final.\n\n"
        "Telegram Stars are a real payment method. Once a card has been "
        "delivered to your account, it cannot be refunded, exchanged, or "
        "reversed for any reason — including a change of mind, buying the "
        "wrong card, or already owning it through other means.\n\n"
        "Refunds are only issued automatically in rare technical cases — "
        "for example if a listing sells out or is pulled from sale in the "
        "instant between your payment and delivery.\n\n"
        "By tapping Buy, you agree to these terms."
        "</blockquote>\n"
        "━━━━━━━━━━━━━━━━━"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Back to Star Shop", callback_data=f"st_star_{uid}", style=ButtonStyle.DANGER)]])

    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()


@main_router.message(Command("star_shop"))
async def star_shop_cmd(message: Message):
    """Standalone entry point — jumps straight into the Star Shop without
    routing through /store first."""
    uid = str(message.from_user.id)
    db = ensure_user(uid, message.from_user.first_name, message.from_user.username)
    text, kb = _build_star_shop_view(uid, db)
    pic = db.get("settings", {}).get("pic_star_shop") or db.get("settings", {}).get("pic_store")
    if pic:
        await message.reply_photo(photo=pic, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
    else:
        await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)


@main_router.callback_query(F.data.startswith("st_star_"))
async def store_star_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)
    text, kb = _build_star_shop_view(uid, db)

    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("buystar_"))
async def buy_star_invoice_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, card_id = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)
    catalog = _star_shop_catalog(db)
    entry = catalog.get(card_id)
    if not entry:
        await cq.answer("This item is no longer for sale.", show_alert=True)
        return
    card_data = db["global_cards"].get(card_id)
    if not card_data:
        await cq.answer("This card no longer exists.", show_alert=True)
        return
    if card_id in _star_purchases(db["users"][uid]):
        await cq.answer("You already own this Star Shop card!", show_alert=True)
        return
    limit = entry.get("limit", 0)
    sold = entry.get("sold", 0)
    if limit > 0 and sold >= limit:
        await cq.answer("This card just sold out!", show_alert=True)
        return

    stars = entry["price"]
    rarity = format_rarity(card_data["rarity"])

    try:
        await bot.send_invoice(
            chat_id=cq.message.chat.id,
            title=f"{card_data['name']} ({rarity})"[:32],
            description=f"Unlock {card_data['name']} permanently — a one-time addition to your collection."[:255],
            payload=f"starbuy_{uid}_{card_id}",
            currency="XTR",
            prices=[LabeledPrice(label=card_data["name"][:32], amount=stars)],
            provider_token="",  # Telegram Stars payments always use an empty provider_token
        )
    except Exception as e:
        dlog.error(f"[star_shop_invoice_CRASH] uid={uid} card={card_id}: {e}", exc_info=True)
        await cq.answer("Couldn't open the payment sheet — please try again.", show_alert=True)
        return
    await cq.answer()


@main_router.pre_checkout_query()
async def star_shop_pre_checkout(pcq: PreCheckoutQuery):
    """Telegram requires an answer within 10 seconds or the payment sheet
    is cancelled client-side. Re-checks eligibility (including stock)
    right before Telegram actually charges the user's Stars balance."""
    payload = pcq.invoice_payload
    if not payload.startswith("starbuy_"):
        await pcq.answer(ok=False, error_message="Unknown order — please reopen the Star Shop.")
        return
    try:
        _, uid, card_id = payload.split("_", 2)
    except ValueError:
        await pcq.answer(ok=False, error_message="Corrupted order — please reopen the Star Shop.")
        return

    db = load_db()
    catalog = db.get("star_shop", {})
    entry = catalog.get(card_id)
    if not entry or card_id not in db.get("global_cards", {}):
        await pcq.answer(ok=False, error_message="This card is no longer for sale.")
        return
    if card_id in db.get("users", {}).get(uid, {}).get("star_purchases", []):
        await pcq.answer(ok=False, error_message="You already own this card.")
        return
    limit = entry.get("limit", 0)
    if limit > 0 and entry.get("sold", 0) >= limit:
        await pcq.answer(ok=False, error_message="This card just sold out.")
        return

    await pcq.answer(ok=True)


@main_router.message(F.successful_payment)
async def star_shop_payment_success(message: Message):
    """Fires once Telegram confirms the Stars charge actually went through.
    This is the only point where the card is granted — send_invoice and
    pre_checkout only ever reserve the right to pay, never move Stars."""
    sp = message.successful_payment
    payload = sp.invoice_payload
    if not payload.startswith("starbuy_"):
        return
    try:
        _, uid, card_id = payload.split("_", 2)
    except ValueError:
        dlog.error(f"[star_shop_payment_CRASH] malformed payload={payload} charge_id={sp.telegram_payment_charge_id}")
        return

    # Locked per-CARD (not per-user) so a global stock limit can't be
    # oversold by two different users paying for the last copy at once.
    async with _get_lock(f"star_stock_{card_id}"):
        db = ensure_user(uid, message.from_user.first_name, message.from_user.username)
        user_data = db["users"][uid]
        bought = _star_purchases(user_data)
        catalog = _star_shop_catalog(db)
        entry = catalog.get(card_id)
        card_data = db["global_cards"].get(card_id)

        async def _refund(reason: str):
            try:
                await bot.refund_star_payment(user_id=int(uid), telegram_payment_charge_id=sp.telegram_payment_charge_id)
                note = "Your Stars were refunded."
            except Exception as e:
                dlog.error(f"[star_shop_refund_CRASH] uid={uid} card={card_id} charge_id={sp.telegram_payment_charge_id}: {e}", exc_info=True)
                note = f"Refund failed automatically — contact support with order ID: {sp.telegram_payment_charge_id}"
            await message.reply(f"⚠️ {reason} {note}")

        if not card_data:
            dlog.error(f"[star_shop_payment_CRASH] uid={uid} paid for missing card={card_id} charge_id={sp.telegram_payment_charge_id}")
            await _refund("That card no longer exists.")
            return
        if not entry:
            await _refund("That card was pulled from sale before your payment completed.")
            return
        if card_id in bought:
            dlog.error(f"[star_shop_payment_DUPLICATE] uid={uid} card={card_id} charge_id={sp.telegram_payment_charge_id}")
            await _refund("You already owned this card.")
            return
        limit = entry.get("limit", 0)
        sold = entry.get("sold", 0)
        if limit > 0 and sold >= limit:
            await _refund("This card sold out right as your payment completed.")
            return

        my_cards = user_data.setdefault("cards", {})
        if card_id not in my_cards:
            my_cards[card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
        my_cards[card_id]["amount"] += 1
        user_data["total_claimed"] = user_data.get("total_claimed", 0) + 1
        bought.append(card_id)
        user_data["stars_spent"] = user_data.get("stars_spent", 0) + sp.total_amount
        entry["sold"] = sold + 1

        save_db()
        await config.flush_db_now()

        rarity = format_rarity(card_data["rarity"])
        log_action(db, uid, {
            "type": "store_buy_star",
            "card_name": card_data["name"],
            "rarity": rarity,
            "price": f"{sp.total_amount} ⭐",
            "chat_id": message.chat.id,
            "chat_title": message.chat.title or "Private Chat",
        })

    await message.reply(
        f"<b>「 ⭐ STAR PURCHASE COMPLETE 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"You now own <b>{card_data['name']}</b> ({rarity})!\n"
        f"Paid: {sp.total_amount} ⭐",
        parse_mode=ParseMode.HTML
    )


# ------------------------------------------
# Admin catalog management: /astar, /rstar, /allstar
# ------------------------------------------
@main_router.message(Command("astar"))
async def astar_cmd(message: Message, command: CommandObject):
    if not _is_star_admin(message.from_user.id):
        return
    args = (command.args or "").strip()
    parts = [p.strip() for p in args.split("|")]
    if len(parts) != 3 or not all(parts):
        await message.reply(
            "Usage: <code>/astar card_id | price | limit</code>\n"
            "<i>limit = 0 for unlimited stock.</i>",
            parse_mode=ParseMode.HTML
        )
        return
    card_id, price_str, limit_str = parts

    db = load_db()
    if card_id not in db["global_cards"]:
        await message.reply("⚠️ No card with that ID exists in global_cards.")
        return
    if not price_str.isdigit() or int(price_str) <= 0:
        await message.reply("⚠️ Price must be a positive whole number of Stars.")
        return
    if not limit_str.isdigit():
        await message.reply("⚠️ Limit must be a whole number (0 = unlimited).")
        return

    price = int(price_str)
    limit = int(limit_str)
    catalog = _star_shop_catalog(db)
    existing_sold = catalog.get(card_id, {}).get("sold", 0)
    catalog[card_id] = {"price": price, "limit": limit, "sold": existing_sold}
    save_db()
    await config.flush_db_now()

    card_name = db["global_cards"][card_id]["name"]
    limit_desc = "Unlimited" if limit == 0 else str(limit)
    await message.reply(
        f"✅ <b>{card_name}</b> is now on sale in the Star Shop.\n"
        f"Price: {price} ⭐ | Stock limit: {limit_desc}",
        parse_mode=ParseMode.HTML
    )


@main_router.message(Command("rstar"))
async def rstar_cmd(message: Message, command: CommandObject):
    if not _is_star_admin(message.from_user.id):
        return
    card_id = (command.args or "").strip()
    if not card_id:
        await message.reply("Usage: <code>/rstar card_id</code>", parse_mode=ParseMode.HTML)
        return

    db = load_db()
    catalog = _star_shop_catalog(db)
    if card_id not in catalog:
        await message.reply("⚠️ That card isn't currently listed in the Star Shop.")
        return

    card_name = db["global_cards"].get(card_id, {}).get("name", card_id)
    del catalog[card_id]
    save_db()
    await config.flush_db_now()
    await message.reply(f"🗑️ <b>{card_name}</b> has been removed from the Star Shop.", parse_mode=ParseMode.HTML)


@main_router.message(Command("allstar"))
async def allstar_cmd(message: Message):
    if not _is_star_admin(message.from_user.id):
        return
    db = load_db()
    catalog = _star_shop_catalog(db)
    if not catalog:
        await message.reply("The Star Shop is currently empty.")
        return

    lines = ["<b>「 ⭐ STAR SHOP CATALOG 」</b>", "━━━━━━━━━━━━━━━━━"]
    for card_id, entry in catalog.items():
        card_data = db["global_cards"].get(card_id)
        name = card_data["name"] if card_data else "⚠️ Missing card"
        rarity = format_rarity(card_data["rarity"]) if card_data else "?"
        price = entry.get("price", 0)
        limit = entry.get("limit", 0)
        sold = entry.get("sold", 0)
        stock = f"{sold}/{limit}" if limit > 0 else f"{sold}/∞"
        lines.append(f"🃏 <code>{card_id}</code> — <b>{name}</b> ({rarity})\n   {price} ⭐ | Sold: {stock}")
    lines.append("━━━━━━━━━━━━━━━━━")
    await message.reply("\n".join(lines), parse_mode=ParseMode.HTML)

# ==========================================
# NEXUS MARKETPLACE (/store)
# ==========================================
@main_router.message(Command("store"))
async def store_cmd(message: Message):
    uid = str(message.from_user.id)
    ensure_user(uid, message.from_user.first_name, message.from_user.username)
    
    text = (
        "<b>「 🏪 𝗡𝗘𝗫𝗨𝗦 𝗠𝗔𝗥𝗞𝗘𝗧𝗣𝗟𝗔𝗖𝗘  」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Choose a marketplace to browse:"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛒 Online Store", callback_data=f"st_on_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="🛍️ Manage Offline Store", callback_data=f"st_off_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="📋 All Active Listings", callback_data=f"st_glob_off_{uid}_0_all", style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="🛍️ Oϝϝʅιɳҽ Sƚσɾҽ (GC)", url="https://t.me/nexus_offstore")]
    ])
    
    db = load_db()
    pic = db.get("settings", {}).get("pic_store")
    if pic: 
        await message.reply_photo(photo=pic, caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
    else: 
        await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML)

@main_router.callback_query(F.data.startswith("st_main_"))
async def store_main_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    text = (
        "<b>「 🏪 𝗡𝗘𝗫𝗨𝗦 𝗠𝗔𝗥𝗞𝗘𝗧𝗣𝗟𝗔𝗖𝗘  」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        "Choose a marketplace to browse:"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🛒 Online Store", callback_data=f"st_on_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="🛍️ Manage Offline Store", callback_data=f"st_off_{uid}", style=ButtonStyle.PRIMARY)],
        [InlineKeyboardButton(text="📋 All Active Listings", callback_data=f"st_glob_off_{uid}_0_all", style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="🛍️ Oϝϝʅιɳҽ Sƚσɾҽ (GC)", url="https://t.me/nexus_offstore")]
    ])
    
    db = load_db()
    pic = db.get("settings", {}).get("pic_store")
    
    try:
        if pic:
            await cq.message.edit_media(InputMediaPhoto(media=pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("st_on_"))
async def store_online_cb(cq: CallbackQuery):
    uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)
    
    today = config.get_shop_rotation_seed()
    dp = db["users"][uid].setdefault("daily_purchases", {})
    
    if dp.get("date") != today:
        db["users"][uid]["daily_purchases"] = {
            "date": today,
            "bought": [],
            "free_refreshes_used": 0,
            "paid_refreshes_used": 0,
            "refresh_seed_offset": 0
        }
        save_db()
        dp = db["users"][uid]["daily_purchases"]
        
    bought_list = dp.setdefault("bought", [])
    offset = dp.setdefault("refresh_seed_offset", 0)

    locked_animes_lower = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
    divine_day = is_divine_day()

    # If this offset was already rolled today, reuse the SAME cards instead
    # of re-deriving from random.choice() against the live eligible pool.
    # BUG THIS FIXES: basics/elites/divines pools are filtered by whichever
    # animes are locked RIGHT NOW — so even with an unchanged seed, locking
    # or unlocking ANY anime (even one unrelated to what's showing) shifts
    # the pool's contents/order, and random.choice() over a shifted pool
    # can land on a totally different card. That looked like "the store
    # randomly refreshed itself" on every lock/unlock, with no actual
    # refresh action or date change involved.
    rolled_basic  = dp.get("rolled_basic")
    rolled_elite  = dp.get("rolled_elite")
    rolled_divine = dp.get("rolled_divine")
    already_rolled = (
        dp.get("rolled_offset") == offset
        and rolled_basic in db["global_cards"]
        and rolled_elite  in db["global_cards"]
        and (not divine_day or rolled_divine is None or rolled_divine in db["global_cards"])
    )

    if already_rolled:
        c_b = (rolled_basic, db["global_cards"][rolled_basic])
        c_e = (rolled_elite, db["global_cards"][rolled_elite])
        c_d = (rolled_divine, db["global_cards"][rolled_divine]) if (divine_day and rolled_divine) else None
    else:
        basics = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Basic 🃏" and v["anime"].lower().strip() not in locked_animes_lower}
        elites = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Elite ⚓" and v["anime"].lower().strip() not in locked_animes_lower}

        if not basics or not elites:
            await cq.answer("⚠️ Store is resting. Not enough cards in the global database.", show_alert=True)
            return

        # Divine slot only rolls in on Sundays.
        divines = {}
        if divine_day:
            divines = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Divine ❄️" and v["anime"].lower().strip() not in locked_animes_lower}

        # Basic/Elite/Divine re-roll on refresh — their seed includes the offset.
        seed = f"{today}_{uid}_{offset}"
        random.seed(seed)
        c_b = random.choice(list(basics.items()))
        c_e = random.choice(list(elites.items()))
        c_d = random.choice(list(divines.items())) if divines else None
        random.seed()

        # Lock in today's selection so it stays stable regardless of any
        # later lock/unlock actions, until the next refresh or day change.
        dp["rolled_offset"] = offset
        dp["rolled_basic"]  = c_b[0]
        dp["rolled_elite"]  = c_e[0]
        dp["rolled_divine"] = c_d[0] if c_d else None
        save_db()

    text = (
        "<b>「 🛒 𝗢𝗡𝗟𝗜𝗡𝗘 𝗦𝗧𝗢𝗥𝗘 」</b>\n"
        "━━━━━━━━━━━━━━━━━\n"
        f"<i>Your personalized daily stock. Resets in {time_until_shop_reset()}.</i>\n\n"
        f"🃏 <b>{c_b[1]['name']}</b> ➜ {SHOP_PRICES['Basic 🃏']} 💠\n"
        f"⚓ <b>{c_e[1]['name']}</b> ➜ {SHOP_PRICES['Elite ⚓']} 💠\n"
    )
    if c_d:
        divine_price = SHOP_PRICES.get('Divine ❄️', 5000)
        text += f"❄️ <b>{c_d[1]['name']}</b> ➜ {divine_price} 💠 <i>(Sunday Special!)</i>\n"
    text += "━━━━━━━━━━━━━━━━━"

    btn_b = InlineKeyboardButton(text=f"Buy {c_b[1]['name']}", callback_data=f"buyon_{uid}_{c_b[0]}", style=ButtonStyle.SUCCESS) if c_b[0] not in bought_list else InlineKeyboardButton(text="Sold Out (Basic)", callback_data="noop", style=ButtonStyle.DANGER)
    btn_e = InlineKeyboardButton(text=f"Buy {c_e[1]['name']}", callback_data=f"buyon_{uid}_{c_e[0]}", style=ButtonStyle.SUCCESS) if c_e[0] not in bought_list else InlineKeyboardButton(text="Sold Out (Elite)", callback_data="noop", style=ButtonStyle.DANGER)

    # Refresh Row Logic
    refresh_buttons = []
    free_used = dp.setdefault("free_refreshes_used", 0)
    paid_used = dp.setdefault("paid_refreshes_used", 0)

    if free_used < 1:
        refresh_buttons.append(InlineKeyboardButton(text="🔄 Free Refresh", callback_data=f"stonref_free_{uid}", style=ButtonStyle.PRIMARY))
    elif paid_used < 1:
        refresh_buttons.append(InlineKeyboardButton(text="🔄 Refresh (200 Shards 💠)", callback_data=f"stonref_paid_{uid}", style=ButtonStyle.PRIMARY))

    kb_list = [
        [btn_b], 
        [btn_e]
    ]
    if c_d:
        btn_d = InlineKeyboardButton(text=f"Buy {c_d[1]['name']} ❄️", callback_data=f"buyon_{uid}_{c_d[0]}", style=ButtonStyle.SUCCESS) if c_d[0] not in bought_list else InlineKeyboardButton(text="Sold Out (Divine)", callback_data="noop", style=ButtonStyle.DANGER)
        kb_list.append([btn_d])
    if refresh_buttons:
        kb_list.append(refresh_buttons)
    kb_list.append([InlineKeyboardButton(text="Back", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)])
    
    kb = InlineKeyboardMarkup(inline_keyboard=kb_list)
    pic = db.get("settings", {}).get("pic_online_store")
    
    try:
        if pic:
            await cq.message.edit_media(InputMediaPhoto(media=pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("stonref_"))
async def online_store_refresh_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    ref_type = parts[1]
    uid = parts[2]
    if not await verify_user(cq, uid): return

    db = load_db()
    user_data = db["users"][uid]
    dp = user_data.setdefault("daily_purchases", {})
    
    today = config.get_shop_rotation_seed()
    if dp.get("date") != today:
        dp["date"] = today
        dp["bought"] = []
        dp["free_refreshes_used"] = 0
        dp["paid_refreshes_used"] = 0
        dp["refresh_seed_offset"] = 0

    # Divine slot removed from the Online Store — Basic/Elite both re-roll
    # on refresh, so a refresh can simply clear the whole "bought" list.
    def reset_bought():
        dp["bought"] = []

    async with _get_lock(f"buy_online_{uid}"):
        if ref_type == "free":
            if dp.setdefault("free_refreshes_used", 0) >= 1:
                await cq.answer("Free refresh already claimed!", show_alert=True)
                return
            dp["free_refreshes_used"] = 1
            dp["refresh_seed_offset"] = dp.get("refresh_seed_offset", 0) + 1
            reset_bought()
            save_db()
            await cq.answer("🔄 Store refreshed successfully!", show_alert=True)

        elif ref_type == "paid":
            if dp.setdefault("free_refreshes_used", 0) < 1:
                await cq.answer("💡 Please use your Free Refresh first!", show_alert=True)
                return
            if dp.setdefault("paid_refreshes_used", 0) >= 1:
                await cq.answer("Paid refresh already claimed!", show_alert=True)
                return
            if user_data.get("nexus_shards", 0) < 200:
                await cq.answer("Insufficient Shards! You need 200 Shards 💠.", show_alert=True)
                return

            user_data["nexus_shards"] -= 200
            dp["paid_refreshes_used"] = 1
            dp["refresh_seed_offset"] = dp.get("refresh_seed_offset", 0) + 1
            reset_bought()
            save_db()
            await config.flush_db_now()
            await cq.answer("🔄 Store refreshed! -200 Shards 💠", show_alert=True)

    await store_online_cb(cq)


@main_router.callback_query(F.data.startswith("buyon_"))
async def buy_online_confirm_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, card_id = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)
    dp = db["users"][uid].get("daily_purchases", {})
    if not _is_live_online_offer(dp, card_id):
        await _reject_stale_online_offer(cq, uid)
        return

    if card_id not in db["global_cards"]:
        await cq.answer("This card no longer exists.", show_alert=True)
        return

    card_data = db["global_cards"][card_id]
    locked_animes_lower = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
    if card_data["anime"].lower().strip() in locked_animes_lower:
        await cq.answer("🔒 This card's series is currently locked and unavailable.", show_alert=True)
        return

    rarity = format_rarity(card_data["rarity"])
    if rarity == "Divine ❄️" and not is_divine_day():
        await cq.answer("❄️ The Divine slot only appears on Sundays!", show_alert=True)
        return
    price = SHOP_PRICES.get(rarity, 99999)

    caption = (
        f"<b>「 PURCHASE CONFIRMATION 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"👤 <b>Card:</b> {card_data['name']}\n"
        f"🌟 <b>Rarity:</b> {rarity}\n"
        f"💰 <b>Price:</b> {price} Shards 💠\n\n"
        f"<i>Do you wish to proceed with this purchase?</i>"
    )

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="✅ Confirm Purchase", callback_data=f"cbon_{uid}_{card_id}", style=ButtonStyle.SUCCESS)],
        [InlineKeyboardButton(text="Cancel", callback_data=f"st_on_{uid}", style=ButtonStyle.DANGER)]
    ])
    
    try:
        if cq.message.photo:
            await cq.message.edit_media(InputMediaPhoto(media=card_data["file_id"], caption=caption, parse_mode=ParseMode.HTML, has_spoiler=True), reply_markup=kb)
        else:
            await cq.message.delete()
            await bot.send_photo(chat_id=cq.message.chat.id, photo=card_data["file_id"], caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML, has_spoiler=True)
    except Exception:
        pass
    await cq.answer()

@main_router.callback_query(F.data.startswith("cbon_"))
async def buy_online_execute_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, card_id = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    async with _get_lock(f"buy_online_{uid}"):
        db = load_db()
        if card_id not in db["global_cards"]:
            await cq.answer("This card no longer exists.", show_alert=True)
            return

        today = config.get_shop_rotation_seed()
        if db["users"][uid].setdefault("daily_purchases", {}).get("date") != today:
            db["users"][uid]["daily_purchases"] = {
                "date": today,
                "bought": [],
                "free_refreshes_used": 0,
                "paid_refreshes_used": 0,
                "refresh_seed_offset": 0
            }

        dp = db["users"][uid]["daily_purchases"]
        if not _is_live_online_offer(dp, card_id):
            await _reject_stale_online_offer(cq, uid)
            return

        if card_id in dp.setdefault("bought", []):
            await cq.answer("You already bought this card today!", show_alert=True)
            return

        card_data = db["global_cards"][card_id]
        locked_animes_lower = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
        if card_data["anime"].lower().strip() in locked_animes_lower:
            await cq.answer("🔒 This card's series is currently locked and unavailable.", show_alert=True)
            return

        rarity = format_rarity(card_data["rarity"])
        if rarity == "Divine ❄️" and not is_divine_day():
            await cq.answer("❄️ The Divine slot only appears on Sundays!", show_alert=True)
            return
        price = SHOP_PRICES.get(rarity, 99999)

        user_data = db["users"][uid]
        current_shards = user_data.get("nexus_shards", 0)

        if current_shards < price:
            await cq.answer(f"Not enough Shards! You need {price} 💠.", show_alert=True)
            return

        db["users"][uid]["nexus_shards"] -= price

        if card_id not in db["users"][uid]["cards"]:
            db["users"][uid]["cards"][card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
        db["users"][uid]["cards"][card_id]["amount"] += 1
        db["users"][uid]["total_claimed"] = db["users"][uid].get("total_claimed", 0) + 1

        db["users"][uid]["daily_purchases"]["bought"].append(card_id)
        save_db()
        await config.flush_db_now()

        log_action(db, uid, {
            "type": "store_buy_online",
            "card_name": card_data["name"],
            "rarity": rarity,
            "price": price,
            "chat_id": cq.message.chat.id,
            "chat_title": cq.message.chat.title or "Private Chat",
        })

    success_text = (
        f"<b>「 PURCHASE COMPLETE ✅ 」</b>\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"You successfully bought <b>{card_data['name']}</b> for {price} Shards!"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Back to Store", callback_data=f"st_on_{uid}", style=ButtonStyle.DANGER)]])
    
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(success_text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer(f"✅ Purchased {card_data['name']}!", show_alert=True)

# ==========================================
# OFFLINE STORE CONSIGNMENT (/sell & Mgmt)
# ==========================================
@main_router.message(Command("sell"))
async def sell_cmd(message: Message, command: CommandObject):
    user_id = str(message.from_user.id)
    db = ensure_user(user_id, message.from_user.first_name, message.from_user.username)
    user_data = db["users"][user_id]
    
    # safeguard 1: Restrict accounts strictly under the 48-hour registration threshold
    account_age_hours = (time.time() - user_data.get("joined", time.time())) / 3600
    if account_age_hours < 48:
        await message.reply_rich(InputRichMessage(html=(
            "⚠️ <b>Consignment Locked!</b>\n"
            "To list items on the Offline Market, your account registration age must exceed <b>48 hours</b>."
        )))
        return

    if not command.args:
        await message.reply_rich(InputRichMessage(html="⚠️ <b>Usage:</b> <code>/sell &lt;card name&gt; &lt;price&gt;</code>\nExample: <code>/sell goku 500</code>"))
        return

    parts = command.args.rsplit(maxsplit=1)
    if len(parts) < 2 or not parts[1].isdigit():
        await message.reply_rich(InputRichMessage(html="⚠️ Invalid format. Make sure you specify the price at the end.\nExample: <code>/sell naruto 250</code>"))
        return

    query = parts[0].lower().strip()
    price = int(parts[1])

    if price < 1:
        await message.reply_rich(InputRichMessage(html="Price must be at least 1 Shard."))
        return

    my_cards = user_data.get("cards", {})
    best_match = None
    best_ratio = 0.0

    for cid, cdata in my_cards.items():
        if cdata["amount"] <= 0: continue
        name_lower = cdata["name"].lower()
        if query == name_lower:
            best_match = (cid, cdata)
            break
        if query in name_lower:
            ratio = 0.8 + (len(query) / len(name_lower)) * 0.1
            if ratio > best_ratio:
                best_ratio = ratio
                best_match = (cid, cdata)

    if not best_match:
        await message.reply_rich(InputRichMessage(html=f"You do not own a card matching <b>{parts[0]}</b>."))
        return

    matched_cid, matched_data = best_match
    global_data = db["global_cards"].get(matched_cid, {})
    
    # safeguard 2: Enforce rarity-based price floors to protect market value boundaries
    rarity_normalized = format_rarity(matched_data["rarity"])
    min_price = 150
    if rarity_normalized == "Elite ⚓":
        min_price = 600
    elif rarity_normalized == "Divine ❄️":
        min_price = 7000
        
    if price < min_price:
        await message.reply_rich(InputRichMessage(html=(
            f"<b>Underpriced Listing Blocked!</b>\n"
            f"To prevent trade manipulation, <b>{rarity_normalized}</b> cards cannot be listed below <b>{min_price} Shards 💠</b>."
        )))
        return

    caption = (
        f"<b>「 SELL CONFIRMATION ぁ 」\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"Character :</b> {matched_data['name']}<b>〔 {rarity_normalized} 〕\n"
        f"Price :</b> {price} 💠\n\n"
        f"<blockquote><b>ⓘ By confirming, this card will be removed from your deck and sent to "
        f"<a href=\"https://t.me/nexus_offstore\">the Offline Store group</a></b></blockquote>"
    )

    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="Confirm", callback_data=f"listsell_{user_id}_{matched_cid}_{price}", style=ButtonStyle.SUCCESS),
            InlineKeyboardButton(text="Cancel", callback_data="cancel_action", style=ButtonStyle.DANGER)
        ]
    ])
    await message.reply_photo(photo=global_data.get("file_id"), caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML, has_spoiler=True)

@main_router.callback_query(F.data == "cancel_action")
async def cancel_action_cb(cq: CallbackQuery):
    """Generic 'Cancel' button used in confirmation flows (e.g. /sell) —
    was missing entirely, so Cancel just spun forever and never closed."""
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption="<b>Cancelled.</b>", reply_markup=None, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text("<b>Cancelled.</b>", reply_markup=None, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()

@main_router.callback_query(F.data == "noop")
async def noop_cb(cq: CallbackQuery):
    """Sold Out buttons point here — was missing a handler, so tapping a
    sold-out slot left Telegram's loading spinner stuck on the button."""
    await cq.answer()

@main_router.callback_query(F.data.startswith("listsell_"))
async def confirm_sell_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, card_id, price = parts[1], parts[2], int(parts[3])
    if not await verify_user(cq, uid): return

    db = load_db()
    my_cards = db["users"].get(uid, {}).get("cards", {})

    if card_id not in my_cards or my_cards[card_id]["amount"] <= 0:
        await cq.answer("You don't own this card anymore!", show_alert=True)
        return

    my_cards[card_id]["amount"] -= 1
    if my_cards[card_id]["amount"] <= 0:
        del my_cards[card_id]
        if db["users"][uid].get("special_card") == card_id:
            db["users"][uid]["special_card"] = None

    listing_id = str(uuid.uuid4())[:8]
    bot_info = await bot.get_me()
    deep_link = f"https://t.me/{bot_info.username}?start=buy_{listing_id}"

    global_data = db["global_cards"][card_id]
    seller_name = db["users"][uid]["name"]

    rarity_str = format_rarity(global_data["rarity"])
    rarity_name, _, rarity_icon = rarity_str.rpartition(" ")

    post_text = (
        f"<b>「 OFFLINE STORE LISTING 🛍️」\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"Name :</b> {global_data['name']}\n"
        f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
        f"<b>Anime :</b> {global_data['anime']}\n"
        f"<b>Price :</b> {price} Shards\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"<blockquote><b>Seller:</b> {seller_name} \n[<code>{uid}</code>]</blockquote>"
    )

    group_kb = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="Buy Now", url=deep_link)]
    ])

    try:
        msg = await bot.send_photo(
            chat_id=OFFLINE_STORE_GROUP,
            photo=global_data["file_id"],
            caption=post_text,
            reply_markup=group_kb,
            parse_mode=ParseMode.HTML,
            has_spoiler=True
        )
        
        db["offline_store"][listing_id] = {
            "seller_id": uid,
            "card_id": card_id,
            "price": price,
            "msg_id": msg.message_id
        }
        save_db()

        success_text = (
            "✅ <b>Listing created successfully!</b>\n"
            "Your card has been moved to the Offline Store.\n\n"
            f"<b>⤷  Link Here :</b> https://t.me/nexus_offstore/{msg.message_id}"
        )
        try:
            if cq.message.photo:
                await cq.message.edit_caption(caption=success_text, reply_markup=None, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(success_text, reply_markup=None, parse_mode=ParseMode.HTML)
        except Exception: pass
        await cq.answer()
        
    except Exception as e:
        if card_id not in my_cards:
            my_cards[card_id] = {"name": global_data["name"], "rarity": global_data["rarity"], "amount": 0}
        my_cards[card_id]["amount"] += 1
        save_db()
        await cq.answer(f"Failed to list in group: {e}", show_alert=True)

@main_router.callback_query(F.data.startswith("st_off_"))
async def offline_listings_mgr(cq: CallbackQuery, uid: str = None):
    if uid is None:
        uid = cq.data.split("_")[2]
    if not await verify_user(cq, uid): return

    db = load_db()
    my_listings = {lid: data for lid, data in db.get("offline_store", {}).items() if data["seller_id"] == uid}
    
    if not my_listings:
        text = "<b>「 🛍️ 𝗠𝗬 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦  」</b>\n━━━━━━━━━━━━━━━━━\nYou currently have no active listings.\nUse <code>/sell &lt;card&gt; &lt;price&gt;</code> to list an item."
        kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📋 All Active Listings", callback_data=f"st_glob_off_{uid}_0_all", style=ButtonStyle.SUCCESS)],
            [InlineKeyboardButton(text="🛍️ Oϝϝʅιɳҽ Sƚσɾҽ (GC)", url="https://t.me/nexus_offstore")],
            [InlineKeyboardButton(text="Back", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)]
        ])
    else:
        text = "<b>「 🛍️ 𝗠𝗬 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦  」</b>\n━━━━━━━━━━━━━━━━━\nSelect a listing to remove it and retrieve your card:\n\n"
        buttons = []
        for lid, data in my_listings.items():
            card_name = db["global_cards"].get(data["card_id"], {}).get("name", "Unknown")
            btn_text = f"Remove {card_name} ({data['price']} 💠)"
            buttons.append([InlineKeyboardButton(text=btn_text, callback_data=f"rm_list_{uid}_{lid}", style=ButtonStyle.DANGER)])
            
        buttons.append([InlineKeyboardButton(text="📋 All Active Listings", callback_data=f"st_glob_off_{uid}_0_all", style=ButtonStyle.SUCCESS)])
        buttons.append([InlineKeyboardButton(text="🛍️ Oϝϝʅιɳҽ Sƚσɾҽ (GC)", url="https://t.me/nexus_offstore")])
        buttons.append([InlineKeyboardButton(text="Back", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)])
        kb = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    pic = db.get("settings", {}).get("pic_offline_store")
    
    try:
        if pic:
            await cq.message.edit_media(InputMediaPhoto(media=pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()

@main_router.callback_query(F.data.startswith("rm_list_"))
async def remove_listing_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, lid = parts[2], parts[3]
    if not await verify_user(cq, uid): return

    db = load_db()
    if lid not in db.get("offline_store", {}):
        await cq.answer("Listing not found or already sold.", show_alert=True)
        return
        
    listing = db["offline_store"][lid]
    
    card_id = listing["card_id"]
    global_card = db["global_cards"].get(card_id)
    
    my_cards = db["users"][uid].setdefault("cards", {})
    if card_id not in my_cards:
        my_cards[card_id] = {"name": global_card["name"], "rarity": global_card["rarity"], "amount": 0}
    my_cards[card_id]["amount"] += 1
    
    try:
        await bot.delete_message(OFFLINE_STORE_GROUP, listing["msg_id"])
    except Exception: pass
    
    del db["offline_store"][lid]
    save_db()
    
    await cq.answer("✅ Listing removed! The card was returned to your deck.", show_alert=True)
    await offline_listings_mgr(cq, uid=uid)

@main_router.callback_query(F.data.startswith("buyoff_"))
async def confirm_offline_buy_cb(cq: CallbackQuery):
    """Shows the purchase confirmation card before an offline listing is
    bought — mirrors the online store's buyon_ -> cbon_ two-step pattern so
    a tap can't execute a purchase without a confirm step in between."""
    parts = cq.data.split("_")
    uid, lid = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)
    if lid not in db.get("offline_store", {}):
        try: await cq.message.edit_caption(caption="This listing is no longer available.", reply_markup=None)
        except Exception: pass
        await cq.answer("Listing sold or removed.", show_alert=True)
        return

    listing = db["offline_store"][lid]
    card_data = db["global_cards"].get(listing["card_id"])
    if not card_data:
        await cq.answer("This card no longer exists.", show_alert=True)
        return

    rarity_str = format_rarity(card_data["rarity"])
    rarity_name, _, rarity_icon = rarity_str.rpartition(" ")

    caption = (
        f"<b>「 PURCHASE CONFIRMATION 」\n"
        f"━━━━━━━━━━━━━━━━━\n"
        f"Name :</b> {card_data['name']}\n"
        f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
        f"<b>Anime :</b> {card_data.get('anime', 'Unknown')}\n"
        f"<b>Price :</b> {listing['price']} Shards\n\n"
        f"Do you wish to proceed with this purchase?"
    )
    kb = InlineKeyboardMarkup(inline_keyboard=[
        [
            InlineKeyboardButton(text="Confirm", callback_data=f"cboff_{uid}_{lid}", style=ButtonStyle.SUCCESS),
            InlineKeyboardButton(text="Cancel", callback_data="cancel_action", style=ButtonStyle.DANGER)
        ]
    ])
    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=caption, reply_markup=kb, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(caption, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer()


@main_router.callback_query(F.data.startswith("cboff_"))
async def execute_offline_buy_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid, lid = parts[1], parts[2]
    if not await verify_user(cq, uid): return

    try:
        await _execute_offline_buy(cq, uid, lid)
    except Exception as e:
        # Whatever goes wrong here, the tap must still resolve — an
        # uncaught exception before cq.answer() leaves Telegram's client
        # spinning on the button forever, which is what "Confirm button
        # not working" actually looks like from the user's side.
        dlog.error(f"[offline_buy_CRASH] uid={uid} lid={lid}: {e}", exc_info=True)
        try:
            await cq.answer("Something went wrong completing this purchase. Please try again.", show_alert=True)
        except Exception:
            pass


async def _execute_offline_buy(cq: CallbackQuery, uid: str, lid: str):
    async with _get_lock(f"buy_offline_{lid}"):
        db = ensure_user(uid, cq.from_user.first_name, cq.from_user.username)

        if lid not in db.get("offline_store", {}):
            try: await cq.message.edit_caption(caption="This listing is no longer available.", reply_markup=None)
            except Exception: pass
            await cq.answer("Listing sold or removed.", show_alert=True)
            return

        listing = db["offline_store"][lid]
        price = listing["price"]
        seller_id = listing["seller_id"]
        card_id = listing["card_id"]

        if seller_id == uid:
            await cq.answer("You cannot buy your own listing.", show_alert=True)
            return

        buyer_data = db["users"].get(uid, {})
        if buyer_data.get("nexus_shards", 0) < price:
            await cq.answer("You don't have enough Shards to complete this transaction.", show_alert=True)
            return

        db["users"][uid]["nexus_shards"] -= price

        if seller_id in db["users"]:
            db["users"][seller_id]["nexus_shards"] = db["users"][seller_id].get("nexus_shards", 0) + price
        else:
            db["users"][seller_id] = {
                "name": "Unknown",
                "nexus_shards": price,
                "cards": {},
                "joined": int(time.time()),
                "stocks": {},
                "daily_purchases": {"date": "", "bought": []}
            }

        buyer_cards = db["users"][uid].setdefault("cards", {})
        global_card = db["global_cards"][card_id]

        if card_id not in buyer_cards:
            buyer_cards[card_id] = {"name": global_card["name"], "rarity": global_card["rarity"], "amount": 0}
        buyer_cards[card_id]["amount"] += 1

        del db["offline_store"][lid]
        save_db()
        await config.flush_db_now()

        buyer_name = db["users"][uid].get("name", "User")
        seller_name = db["users"].get(seller_id, {}).get("name", "Unknown")
        rarity_str = format_rarity(global_card["rarity"])
        rarity_name, _, rarity_icon = rarity_str.rpartition(" ")

        log_action(db, uid, {
            "type": "store_buy_offline",
            "card_name": global_card["name"],
            "rarity": rarity_str,
            "price": price,
            "cp_name": seller_name,
            "cp_id": seller_id,
            "chat_id": OFFLINE_STORE_GROUP,
            "chat_title": "Offline Marketplace",
        })
        log_action(db, seller_id, {
            "type": "store_sell_offline",
            "card_name": global_card["name"],
            "rarity": rarity_str,
            "price": price,
            "cp_name": buyer_name,
            "cp_id": uid,
            "chat_id": OFFLINE_STORE_GROUP,
            "chat_title": "Offline Marketplace",
        })

    try:
        sold_text = (
            f"<b>「 🛍️ SOLD 」\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"Name :</b> {global_card['name']}\n"
            f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
            f"<b>Anime :</b> {global_card.get('anime', 'Unknown')}\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"<blockquote>✅ Purchased by {buyer_name} for {price} 💠</blockquote>"
        )
        await bot.edit_message_caption(chat_id=OFFLINE_STORE_GROUP, message_id=listing["msg_id"], caption=sold_text, reply_markup=None, parse_mode=ParseMode.HTML)
    except Exception: pass

    try:
        seller_msg = (
            f"🎊 <b>Great News !</b> Your Card <b>{global_card['name']}〔{rarity_icon}〕</b>"
            f"has been bought by {buyer_name} [{uid}] for {price} Shards."
        )
        await bot.send_message(chat_id=int(seller_id), text=seller_msg, parse_mode=ParseMode.HTML)
    except Exception:
        pass

    try:
        if cq.message.photo:
            await cq.message.edit_caption(caption=f"✅ <b>Purchase Complete!</b>\nYou bought <b>{global_card['name']}</b> for {price} Shards.", reply_markup=None, parse_mode=ParseMode.HTML)
        else:
            await cq.message.edit_text(f"✅ <b>Purchase Complete!</b>\nYou bought <b>{global_card['name']}</b> for {price} Shards.", reply_markup=None, parse_mode=ParseMode.HTML)
    except Exception: pass
    await cq.answer("✅ Purchase successful!", show_alert=True)


# ==========================================
# /viewsells - USER LISTINGS CHECKER
# ==========================================
@main_router.message(Command("viewsells"))
async def viewsells_cmd(message: Message):
    uid_int = message.from_user.id
    if config.is_ghost_banned(uid_int) or config.is_shadow_banned(uid_int): return

    uid = str(uid_int)
    db = ensure_user(uid, message.from_user.first_name, message.from_user.username)
    my_listings = {lid: data for lid, data in db.get("offline_store", {}).items() if data["seller_id"] == uid}
    
    if not my_listings:
        await message.reply_rich(
            InputRichMessage(html=(
                "<b>「 🛍️ 𝗠𝗬 𝗢𝗙𝗙𝗟𝗜𝗡𝗘 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦 」</b>\n"
                "━━━━━━━━━━━━━━━━━\n"
                "You do not have any active listings currently.\n"
                "Use <code>/sell &lt;card name&gt; &lt;price&gt;</code> to list a card."
            )),
            reply_markup=InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🗑️ Close", callback_data="close_msg")]])
        )
        return
        
    bot_info = await bot.get_me()
    text = "<b>「 🛍️ 𝗠𝗬 𝗢𝗙𝗙𝗟𝗜𝗡𝗘 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦 」</b>\n━━━━━━━━━━━━━━━━━\n\n"
    for lid, data in my_listings.items():
        card_data = db["global_cards"].get(data["card_id"])
        if not card_data: continue
        rarity = format_rarity(card_data["rarity"])
        msg_id = data.get("msg_id")
        
        # Link directly to the Channel/GC Post
        link = f"https://t.me/nexus_offstore/{msg_id}" if msg_id else f"https://t.me/nexus_offstore"
        text += f"• <a href='{link}'>{card_data['name']}</a> [{rarity}] - <b>{data['price']} 💠</b>\n"
        
    text += "\n━━━━━━━━━━━━━━━━━"
    kb = InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="🗑️ Close", callback_data="close_msg")]])
    await message.reply(text, reply_markup=kb, parse_mode=ParseMode.HTML, disable_web_page_preview=True)


# ==========================================
# GLOBAL OFFLINE STORE CARDS LOOKUP (BROWSER)
# ==========================================
# Maps the short category code used in callback_data to the rarity string
# produced by format_rarity(), plus the label shown on the selector button.
CATEGORY_MAP = {
    "all":    (None,          "All"),
    "basic":  ("Basic 🃏",    "Basic 🃏"),
    "elite":  ("Elite ⚓",    "Elite ⚓"),
    "divine": ("Divine ❄️",   "Divine ❄️"),
}

@main_router.callback_query(F.data.startswith("st_glob_off_"))
async def st_global_listings_cb(cq: CallbackQuery):
    parts = cq.data.split("_")
    uid = parts[3]
    page = int(parts[4])
    # Older buttons (from before categories existed) won't have a 6th part —
    # fall back to "all" so they keep working instead of erroring out.
    cat = parts[5] if len(parts) > 5 else "all"
    if cat not in CATEGORY_MAP:
        cat = "all"
    if not await verify_user(cq, uid): return

    db = load_db()
    offline_store = db.get("offline_store", {})

    rarity_filter, _ = CATEGORY_MAP[cat]

    # Build the category selector row. The active category is highlighted.
    def cat_button(code: str) -> InlineKeyboardButton:
        _, label = CATEGORY_MAP[code]
        is_active = (code == cat)
        return InlineKeyboardButton(
            text=label,
            callback_data=f"st_glob_off_{uid}_0_{code}",
            style=ButtonStyle.SUCCESS if is_active else ButtonStyle.PRIMARY
        )
    selector_row = [cat_button("basic"), cat_button("elite")]
    selector_row2 = [cat_button("divine"), cat_button("all")]

    if not offline_store:
        text = "<b>「 🌐 𝗚𝗟𝗢𝗕𝗔𝗟 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦 」</b>\n━━━━━━━━━━━━━━━━━\nNo active listings found in the Offline Store."
        kb = InlineKeyboardMarkup(inline_keyboard=[
            selector_row,
            selector_row2,
            [InlineKeyboardButton(text="Back", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)]
        ])
        try:
            await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
        except Exception:
            await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
        return

    listings_list = list(offline_store.items())

    # Filter by the selected rarity category (skip cards missing from the
    # global card table rather than erroring, same as the render loop below).
    if rarity_filter is not None:
        filtered = []
        for lid, data in listings_list:
            card_data = db["global_cards"].get(data["card_id"])
            if not card_data:
                continue
            if format_rarity(card_data["rarity"]) == rarity_filter:
                filtered.append((lid, data))
        listings_list = filtered

    # Sorter: lowest price first
    listings_list.sort(key=lambda x: x[1].get("price", 0))

    per_page = 10
    total = len(listings_list)
    total_pages = max(1, (total - 1) // per_page + 1)
    
    if page >= total_pages: page = total_pages - 1
    if page < 0: page = 0
    
    start = page * per_page
    end = min(start + per_page, total)
    sliced = listings_list[start:end]

    _, cat_label = CATEGORY_MAP[cat]
    text = f"<b>「 🌐 𝗚𝗟𝗢𝗕𝗔𝗟 𝗟𝗜𝗦𝗧𝗜𝗡𝗚𝗦 」</b>\n━━━━━━━━━━━━━━━━━\n"
    text += f"<i>Category: {cat_label}</i>\n"
    text += "<i>Click on a card name to view its post in the Offline GC:</i>\n\n"

    if not sliced:
        text += "<i>No active listings in this category.</i>\n"

    for lid, data in sliced:
        card_data = db["global_cards"].get(data["card_id"])
        if not card_data: continue
        rarity = format_rarity(card_data["rarity"])
        seller_id = data["seller_id"]
        seller_name = db["users"].get(seller_id, {}).get("name", "User")
        
        # Hyperlink configured to redirect specifically to the offline GC post
        msg_id = data.get("msg_id")
        gc_post_link = f"https://t.me/nexus_offstore/{msg_id}" if msg_id else "https://t.me/nexus_offstore"
        text += f"• <a href='{gc_post_link}'>{card_data['name']}</a> [{rarity}] - <b>{data['price']} 💠</b> (by {seller_name})\n"
        
    text += f"\n━━━━━━━━━━━━━━━━━\nPage <b>{page+1}/{total_pages}</b>"
    
    nav = []
    if page > 0:
        nav.append(InlineKeyboardButton(text="❮", callback_data=f"st_glob_off_{uid}_{page-1}_{cat}"))
    if end < total:
        nav.append(InlineKeyboardButton(text="❯", callback_data=f"st_glob_off_{uid}_{page+1}_{cat}"))
        
    kb_list = [selector_row, selector_row2]
    if nav:
        kb_list.append(nav)
    kb_list.append([InlineKeyboardButton(text="Back to Store", callback_data=f"st_main_{uid}", style=ButtonStyle.DANGER)])
    kb = InlineKeyboardMarkup(inline_keyboard=kb_list)
    
    pic = db.get("settings", {}).get("pic_offline_store") or db.get("settings", {}).get("pic_store")
    
    try:
        if pic:
            await cq.message.edit_media(InputMediaPhoto(media=pic, caption=text, parse_mode=ParseMode.HTML), reply_markup=kb)
        else:
            if cq.message.photo:
                await cq.message.edit_caption(caption=text, reply_markup=kb, parse_mode=ParseMode.HTML)
            else:
                await cq.message.edit_text(text, reply_markup=kb, parse_mode=ParseMode.HTML)
    except Exception:
        pass
    await cq.answer()

# ==========================================
# REST API — used by the /webdeck Mini App's Store tab.
# Mirrors the bot command/callback logic above exactly (same locks, same
# price floors, same rotation/seed rules) so behavior stays identical
# between the Telegram chat commands and the web app.
# ==========================================

class OnlineBuyRequest(BaseModel):
    user_id: str
    card_id: str

class OnlineRefreshRequest(BaseModel):
    user_id: str
    type: str  # "free" | "paid"

class SellRequest(BaseModel):
    user_id: str
    card_id: str
    price: int

class RemoveListingRequest(BaseModel):
    user_id: str
    listing_id: str

class OfflineBuyRequest(BaseModel):
    user_id: str
    listing_id: str


def _slot_payload(cid_data, bought_list):
    if not cid_data:
        return None
    cid, cdata = cid_data
    rarity = format_rarity(cdata["rarity"])
    return {
        "card_id": cid,
        "name": cdata["name"],
        "anime": cdata.get("anime"),
        "rarity": rarity,
        "price": SHOP_PRICES.get(rarity, 99999),
        "bought": cid in bought_list
    }


@store_api.get("/online/{user_id}")
async def api_get_online_store(user_id: str):
    """Same roll/lock-in logic as store_online_cb — reused so the price and
    card shown in the web app always matches what /store shows in chat."""
    try:
        db = ensure_user(user_id, "User", None)
        today = config.get_shop_rotation_seed()
        dp = db["users"][user_id].setdefault("daily_purchases", {})

        if dp.get("date") != today:
            db["users"][user_id]["daily_purchases"] = {
                "date": today, "bought": [], "free_refreshes_used": 0,
                "paid_refreshes_used": 0, "refresh_seed_offset": 0
            }
            save_db()
            dp = db["users"][user_id]["daily_purchases"]

        bought_list = dp.setdefault("bought", [])
        offset = dp.setdefault("refresh_seed_offset", 0)
        locked_animes_lower = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
        divine_day = is_divine_day()

        rolled_basic  = dp.get("rolled_basic")
        rolled_elite  = dp.get("rolled_elite")
        rolled_divine = dp.get("rolled_divine")
        already_rolled = (
            dp.get("rolled_offset") == offset
            and rolled_basic in db["global_cards"]
            and rolled_elite  in db["global_cards"]
            and (not divine_day or rolled_divine is None or rolled_divine in db["global_cards"])
        )

        if already_rolled:
            c_b = (rolled_basic, db["global_cards"][rolled_basic])
            c_e = (rolled_elite, db["global_cards"][rolled_elite])
            c_d = (rolled_divine, db["global_cards"][rolled_divine]) if (divine_day and rolled_divine) else None
        else:
            basics = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Basic 🃏" and v["anime"].lower().strip() not in locked_animes_lower}
            elites = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Elite ⚓" and v["anime"].lower().strip() not in locked_animes_lower}

            if not basics or not elites:
                return {"error": True, "message": "Store is resting. Not enough cards in the global database."}

            divines = {}
            if divine_day:
                divines = {k: v for k, v in db["global_cards"].items() if format_rarity(v["rarity"]) == "Divine ❄️" and v["anime"].lower().strip() not in locked_animes_lower}

            seed = f"{today}_{user_id}_{offset}"
            random.seed(seed)
            c_b = random.choice(list(basics.items()))
            c_e = random.choice(list(elites.items()))
            c_d = random.choice(list(divines.items())) if divines else None
            random.seed()

            dp["rolled_offset"] = offset
            dp["rolled_basic"]  = c_b[0]
            dp["rolled_elite"]  = c_e[0]
            dp["rolled_divine"] = c_d[0] if c_d else None
            save_db()

        free_used = dp.setdefault("free_refreshes_used", 0)
        paid_used = dp.setdefault("paid_refreshes_used", 0)

        return {
            "error": False,
            "reset_in": time_until_shop_reset(),
            "basic": _slot_payload(c_b, bought_list),
            "elite": _slot_payload(c_e, bought_list),
            "divine": _slot_payload(c_d, bought_list) if c_d else None,
            "divine_day": divine_day,
            "free_refresh_available": free_used < 1,
            "paid_refresh_available": free_used >= 1 and paid_used < 1,
            "paid_refresh_cost": 200,
            "balance": db["users"][user_id].get("nexus_shards", 0)
        }
    except Exception as e:
        dlog.error(f"[store_online_state_CRASH] uid={user_id}: {e}", exc_info=True)
        return {"error": True, "message": "Failed to load store."}


@store_api.post("/online/refresh")
async def api_online_refresh(req: OnlineRefreshRequest):
    try:
        async with _get_lock(f"buy_online_{req.user_id}"):
            db = load_db()
            if req.user_id not in db.get("users", {}):
                raise HTTPException(status_code=404, detail="User not found.")

            user_data = db["users"][req.user_id]
            dp = user_data.setdefault("daily_purchases", {})
            today = config.get_shop_rotation_seed()
            if dp.get("date") != today:
                dp["date"] = today
                dp["bought"] = []
                dp["free_refreshes_used"] = 0
                dp["paid_refreshes_used"] = 0
                dp["refresh_seed_offset"] = 0

            if req.type == "free":
                if dp.setdefault("free_refreshes_used", 0) >= 1:
                    raise HTTPException(status_code=400, detail="Free refresh already claimed!")
                dp["free_refreshes_used"] = 1
                dp["refresh_seed_offset"] = dp.get("refresh_seed_offset", 0) + 1
                dp["bought"] = []
                save_db()
            elif req.type == "paid":
                if dp.setdefault("free_refreshes_used", 0) < 1:
                    raise HTTPException(status_code=400, detail="Please use your Free Refresh first!")
                if dp.setdefault("paid_refreshes_used", 0) >= 1:
                    raise HTTPException(status_code=400, detail="Paid refresh already claimed!")
                if user_data.get("nexus_shards", 0) < 200:
                    raise HTTPException(status_code=400, detail="Insufficient Shards! You need 200 Shards 💠.")
                user_data["nexus_shards"] -= 200
                dp["paid_refreshes_used"] = 1
                dp["refresh_seed_offset"] = dp.get("refresh_seed_offset", 0) + 1
                dp["bought"] = []
                save_db()
                await config.flush_db_now()
            else:
                raise HTTPException(status_code=400, detail="Invalid refresh type.")

        return {"success": True}
    except HTTPException:
        raise
    except Exception as e:
        dlog.error(f"[store_online_refresh_CRASH] uid={req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Refresh failed.")


@store_api.post("/online/buy")
async def api_online_buy(req: OnlineBuyRequest):
    try:
        async with _get_lock(f"buy_online_{req.user_id}"):
            db = load_db()
            if req.user_id not in db.get("users", {}):
                raise HTTPException(status_code=404, detail="User not found.")
            if req.card_id not in db["global_cards"]:
                raise HTTPException(status_code=404, detail="This card no longer exists.")

            today = config.get_shop_rotation_seed()
            if db["users"][req.user_id].setdefault("daily_purchases", {}).get("date") != today:
                db["users"][req.user_id]["daily_purchases"] = {
                    "date": today, "bought": [], "free_refreshes_used": 0,
                    "paid_refreshes_used": 0, "refresh_seed_offset": 0
                }

            dp = db["users"][req.user_id]["daily_purchases"]
            if not _is_live_online_offer(dp, req.card_id):
                raise HTTPException(status_code=409, detail="This offer has expired — please refresh the store.")
            if req.card_id in dp.setdefault("bought", []):
                raise HTTPException(status_code=400, detail="You already bought this card today!")

            card_data = db["global_cards"][req.card_id]
            locked_animes_lower = [a.lower().strip() for a in db.get("settings", {}).get("locked_animes", [])]
            if card_data["anime"].lower().strip() in locked_animes_lower:
                raise HTTPException(status_code=403, detail="This card's series is currently locked and unavailable.")

            rarity = format_rarity(card_data["rarity"])
            if rarity == "Divine ❄️" and not is_divine_day():
                raise HTTPException(status_code=403, detail="The Divine slot only appears on Sundays!")
            price = SHOP_PRICES.get(rarity, 99999)

            user_data = db["users"][req.user_id]
            if user_data.get("nexus_shards", 0) < price:
                raise HTTPException(status_code=400, detail=f"Not enough Shards! You need {price} 💠.")

            user_data["nexus_shards"] -= price
            if req.card_id not in user_data["cards"]:
                user_data["cards"][req.card_id] = {"name": card_data["name"], "rarity": card_data["rarity"], "amount": 0}
            user_data["cards"][req.card_id]["amount"] += 1
            user_data["total_claimed"] = user_data.get("total_claimed", 0) + 1
            dp["bought"].append(req.card_id)
            save_db()
            await config.flush_db_now()

            new_balance = user_data["nexus_shards"]
            card_name = card_data["name"]

        return {"success": True, "card_name": card_name, "price": price, "new_balance": new_balance}
    except HTTPException:
        raise
    except Exception as e:
        dlog.error(f"[store_online_buy_CRASH] uid={req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Purchase failed.")


@store_api.get("/offline/mine/{user_id}")
async def api_get_my_listings(user_id: str):
    try:
        db = load_db()
        my_listings = []
        for lid, data in db.get("offline_store", {}).items():
            if data["seller_id"] != user_id:
                continue
            card = db["global_cards"].get(data["card_id"], {})
            my_listings.append({
                "listing_id": lid,
                "card_id": data["card_id"],
                "name": card.get("name", "Unknown"),
                "rarity": format_rarity(card.get("rarity", "")),
                "anime": card.get("anime"),
                "price": data["price"]
            })
        return {"error": False, "listings": my_listings}
    except Exception as e:
        dlog.error(f"[store_offline_mine_CRASH] uid={user_id}: {e}", exc_info=True)
        return {"error": True, "listings": []}


@store_api.post("/offline/list")
async def api_create_listing(req: SellRequest):
    """Same checks as /sell (account age, rarity price floor) — the web app
    just skips the fuzzy-name search since the user picks a card_id directly
    from their own deck."""
    try:
        db = ensure_user(req.user_id, "User", None)
        user_data = db["users"][req.user_id]

        account_age_hours = (time.time() - user_data.get("joined", time.time())) / 3600
        if account_age_hours < 48:
            raise HTTPException(status_code=403, detail="To list items on the Offline Market, your account registration age must exceed 48 hours.")

        if req.price < 1:
            raise HTTPException(status_code=400, detail="Price must be at least 1 Shard.")

        my_cards = user_data.get("cards", {})
        if req.card_id not in my_cards or my_cards[req.card_id]["amount"] <= 0:
            raise HTTPException(status_code=404, detail="You do not own this card.")

        global_data = db["global_cards"].get(req.card_id)
        if not global_data:
            raise HTTPException(status_code=404, detail="This card no longer exists.")

        rarity_normalized = format_rarity(global_data["rarity"])
        min_price = 150
        if rarity_normalized == "Elite ⚓":
            min_price = 600
        elif rarity_normalized == "Divine ❄️":
            min_price = 2500
        if req.price < min_price:
            raise HTTPException(status_code=400, detail=f"To prevent trade manipulation, {rarity_normalized} cards cannot be listed below {min_price} Shards 💠.")

        my_cards[req.card_id]["amount"] -= 1
        if my_cards[req.card_id]["amount"] <= 0:
            del my_cards[req.card_id]
            if user_data.get("special_card") == req.card_id:
                user_data["special_card"] = None

        listing_id = str(uuid.uuid4())[:8]
        bot_info = await bot.get_me()
        deep_link = f"https://t.me/{bot_info.username}?start=buy_{listing_id}"
        seller_name = user_data["name"]
        rarity_name, _, rarity_icon = rarity_normalized.rpartition(" ")

        post_text = (
            f"<b>「 OFFLINE STORE LISTING 🛍️」\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"Name :</b> {global_data['name']}\n"
            f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
            f"<b>Anime :</b> {global_data['anime']}\n"
            f"<b>Price :</b> {req.price} Shards\n"
            f"━━━━━━━━━━━━━━━━━\n"
            f"<blockquote><b>Seller:</b> {seller_name} \n[<code>{req.user_id}</code>]</blockquote>"
        )
        group_kb = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="Buy Now", url=deep_link)]
        ])

        try:
            msg = await bot.send_photo(
                chat_id=OFFLINE_STORE_GROUP,
                photo=global_data["file_id"],
                caption=post_text,
                reply_markup=group_kb,
                parse_mode=ParseMode.HTML,
                has_spoiler=True
            )
            db["offline_store"][listing_id] = {
                "seller_id": req.user_id,
                "card_id": req.card_id,
                "price": req.price,
                "msg_id": msg.message_id
            }
            save_db()
            await config.flush_db_now()
        except Exception as e:
            # Roll back the card deduction if posting to the group failed.
            if req.card_id not in my_cards:
                my_cards[req.card_id] = {"name": global_data["name"], "rarity": global_data["rarity"], "amount": 0}
            my_cards[req.card_id]["amount"] += 1
            save_db()
            raise HTTPException(status_code=502, detail=f"Failed to list in group: {e}")

        return {"success": True, "listing_id": listing_id}
    except HTTPException:
        raise
    except Exception as e:
        dlog.error(f"[store_offline_list_CRASH] uid={req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Listing failed.")


@store_api.post("/offline/remove")
async def api_remove_listing(req: RemoveListingRequest):
    try:
        db = load_db()
        if req.listing_id not in db.get("offline_store", {}):
            raise HTTPException(status_code=404, detail="Listing not found or already sold.")

        listing = db["offline_store"][req.listing_id]
        if listing["seller_id"] != req.user_id:
            raise HTTPException(status_code=403, detail="This isn't your listing.")

        card_id = listing["card_id"]
        global_card = db["global_cards"].get(card_id)
        my_cards = db["users"][req.user_id].setdefault("cards", {})
        if card_id not in my_cards:
            my_cards[card_id] = {"name": global_card["name"], "rarity": global_card["rarity"], "amount": 0}
        my_cards[card_id]["amount"] += 1

        try:
            await bot.delete_message(OFFLINE_STORE_GROUP, listing["msg_id"])
        except Exception:
            pass

        del db["offline_store"][req.listing_id]
        save_db()
        await config.flush_db_now()
        return {"success": True}
    except HTTPException:
        raise
    except Exception as e:
        dlog.error(f"[store_offline_remove_CRASH] uid={req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Failed to remove listing.")


@store_api.get("/offline/all")
async def api_get_global_listings(category: str = "all", page: int = 0):
    try:
        if category not in CATEGORY_MAP:
            category = "all"
        db = load_db()
        offline_store = db.get("offline_store", {})
        rarity_filter, _ = CATEGORY_MAP[category]

        listings_list = list(offline_store.items())
        if rarity_filter is not None:
            filtered = []
            for lid, data in listings_list:
                card_data = db["global_cards"].get(data["card_id"])
                if not card_data:
                    continue
                if format_rarity(card_data["rarity"]) == rarity_filter:
                    filtered.append((lid, data))
            listings_list = filtered

        listings_list.sort(key=lambda x: x[1].get("price", 0))

        per_page = 20
        total = len(listings_list)
        total_pages = max(1, (total - 1) // per_page + 1)
        if page >= total_pages: page = total_pages - 1
        if page < 0: page = 0
        start = page * per_page
        end = min(start + per_page, total)
        sliced = listings_list[start:end]

        results = []
        for lid, data in sliced:
            card_data = db["global_cards"].get(data["card_id"])
            if not card_data:
                continue
            seller_name = db["users"].get(data["seller_id"], {}).get("name", "User")
            results.append({
                "listing_id": lid,
                "card_id": data["card_id"],
                "name": card_data["name"],
                "rarity": format_rarity(card_data["rarity"]),
                "anime": card_data.get("anime"),
                "price": data["price"],
                "seller_name": seller_name,
                "seller_id": data["seller_id"]
            })

        return {"error": False, "listings": results, "page": page, "total_pages": total_pages, "total": total}
    except Exception as e:
        dlog.error(f"[store_offline_all_CRASH]: {e}", exc_info=True)
        return {"error": True, "listings": [], "page": 0, "total_pages": 1, "total": 0}


@store_api.post("/offline/buy")
async def api_buy_offline(req: OfflineBuyRequest):
    try:
        async with _get_lock(f"buy_offline_{req.listing_id}"):
            db = ensure_user(req.user_id, "User", None)
            if req.listing_id not in db.get("offline_store", {}):
                raise HTTPException(status_code=404, detail="This listing is no longer available.")

            listing = db["offline_store"][req.listing_id]
            price = listing["price"]
            seller_id = listing["seller_id"]
            card_id = listing["card_id"]

            if seller_id == req.user_id:
                raise HTTPException(status_code=400, detail="You cannot buy your own listing.")

            buyer_data = db["users"].get(req.user_id, {})
            if buyer_data.get("nexus_shards", 0) < price:
                raise HTTPException(status_code=400, detail="You don't have enough Shards to complete this transaction.")

            db["users"][req.user_id]["nexus_shards"] -= price
            if seller_id in db["users"]:
                db["users"][seller_id]["nexus_shards"] = db["users"][seller_id].get("nexus_shards", 0) + price
            else:
                db["users"][seller_id] = {
                    "name": "Unknown", "nexus_shards": price, "cards": {},
                    "joined": int(time.time()), "stocks": {},
                    "daily_purchases": {"date": "", "bought": []}
                }

            buyer_cards = db["users"][req.user_id].setdefault("cards", {})
            global_card = db["global_cards"][card_id]
            if card_id not in buyer_cards:
                buyer_cards[card_id] = {"name": global_card["name"], "rarity": global_card["rarity"], "amount": 0}
            buyer_cards[card_id]["amount"] += 1

            del db["offline_store"][req.listing_id]
            save_db()
            await config.flush_db_now()

            buyer_name = db["users"][req.user_id].get("name", "User")
            seller_name = db["users"].get(seller_id, {}).get("name", "Unknown")
            rarity_str = format_rarity(global_card["rarity"])
            rarity_name, _, rarity_icon = rarity_str.rpartition(" ")

            log_action(db, req.user_id, {
                "type": "store_buy_offline",
                "card_name": global_card["name"],
                "rarity": rarity_str,
                "price": price,
                "cp_name": seller_name,
                "cp_id": seller_id,
                "chat_id": OFFLINE_STORE_GROUP,
                "chat_title": "Offline Marketplace",
            })
            log_action(db, seller_id, {
                "type": "store_sell_offline",
                "card_name": global_card["name"],
                "rarity": rarity_str,
                "price": price,
                "cp_name": buyer_name,
                "cp_id": req.user_id,
                "chat_id": OFFLINE_STORE_GROUP,
                "chat_title": "Offline Marketplace",
            })

        # Best-effort notifications, same as the bot flow — never block the buyer on these.
        try:
            sold_text = (
                f"<b>「 🛍️ SOLD 」\n"
                f"━━━━━━━━━━━━━━━━━\n"
                f"Name :</b> {global_card['name']}\n"
                f"<b>Rarity :</b> {rarity_name}<b>〔{rarity_icon}〕</b>\n"
                f"<b>Anime :</b> {global_card.get('anime', 'Unknown')}\n"
                f"━━━━━━━━━━━━━━━━━\n"
                f"<blockquote>✅ Purchased by {buyer_name} for {price} 💠</blockquote>"
            )
            await bot.edit_message_caption(chat_id=OFFLINE_STORE_GROUP, message_id=listing["msg_id"], caption=sold_text, reply_markup=None, parse_mode=ParseMode.HTML)
        except Exception:
            pass
        try:
            seller_msg = (
                f"🎊 <b>Great News !</b> Your Card <b>{global_card['name']}〔{rarity_icon}〕</b>"
                f"has been bought by {buyer_name} [{req.user_id}] for {price} Shards."
            )
            await bot.send_message(chat_id=int(seller_id), text=seller_msg, parse_mode=ParseMode.HTML)
        except Exception:
            pass

        return {"success": True, "card_name": global_card["name"], "price": price}
    except HTTPException:
        raise
    except Exception as e:
        dlog.error(f"[store_offline_buy_CRASH] uid={req.user_id}: {e}", exc_info=True)
        raise HTTPException(status_code=500, detail="Purchase failed.")
