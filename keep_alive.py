"""
keep_alive.py — keeps a Render free Web Service from spinning down.

Render puts a free web service to sleep after ~15 minutes without an incoming HTTP request,
which also stops the bot's polling. Two layers are used:

1. /health  (GET and HEAD)  — a tiny endpoint any uptime monitor can hit.
2. keep_alive_loop()        — the bot pings its own PUBLIC url every 9 minutes. Going through the
                              public url counts as inbound traffic, so Render treats the service as active.

A self-ping cannot wake a service that is already asleep, so ALSO add a free external monitor
(UptimeRobot / cron-job.org) that hits  https://<your-app>.onrender.com/health  every 5 minutes.
"""
import asyncio
import logging
import os

import aiohttp
from fastapi import APIRouter

logger = logging.getLogger("AnimeNexus")

keep_alive_router = APIRouter()

PING_INTERVAL_SECONDS = 9 * 60          # Render sleeps after 15 min idle
PING_TIMEOUT_SECONDS = 20


@keep_alive_router.api_route("/health", methods=["GET", "HEAD"], include_in_schema=False)
async def health():
    return {"status": "ok"}


def _public_url() -> str:
    # Render sets RENDER_EXTERNAL_URL automatically; KEEP_ALIVE_URL lets you override it.
    return (os.environ.get("KEEP_ALIVE_URL") or os.environ.get("RENDER_EXTERNAL_URL") or "").rstrip("/")


async def keep_alive_loop():
    base = _public_url()
    if not base:
        logger.info("[keep_alive] RENDER_EXTERNAL_URL / KEEP_ALIVE_URL not set - self-ping disabled.")
        return
    url = f"{base}/health"
    logger.info(f"[keep_alive] Pinging {url} every {PING_INTERVAL_SECONDS // 60} minutes.")
    await asyncio.sleep(60)             # let the server finish starting first
    timeout = aiohttp.ClientTimeout(total=PING_TIMEOUT_SECONDS)
    while True:
        try:
            async with aiohttp.ClientSession(timeout=timeout) as session:
                async with session.get(url) as resp:
                    logger.debug(f"[keep_alive] ping -> {resp.status}")
        except asyncio.CancelledError:
            raise
        except Exception as e:
            logger.warning(f"[keep_alive] ping failed: {e}")
        await asyncio.sleep(PING_INTERVAL_SECONDS)
