import time
import asyncio
from collections import deque
from typing import Optional, Callable, Any, Coroutine
import logging

logger = logging.getLogger(__name__)

class SlidingWindowRateLimiter:
    """
    Ensures that at most `max_calls` operations happen within a sliding window of `period` seconds.
    Uses asyncio lock and sleeps if necessary before proceeding.
    """
    def __init__(self, max_calls: int, period: float = 1.0):
        self.max_calls = max_calls
        self.period = period
        self.timestamps = deque()
        self.lock = asyncio.Lock()

    async def acquire(self):
        async with self.lock:
            now = time.monotonic()
            # Remove timestamps outside the window
            while self.timestamps and now - self.timestamps[0] >= self.period:
                self.timestamps.popleft()
            if len(self.timestamps) >= self.max_calls:
                # Wait until the oldest timestamp leaves the window
                wait_time = self.period - (now - self.timestamps[0]) + 0.001
                await asyncio.sleep(wait_time)
                now = time.monotonic()
                while self.timestamps and now - self.timestamps[0] >= self.period:
                    self.timestamps.popleft()
            self.timestamps.append(now)


class RateLimitedRetrySender:
    """
    Wraps an async sender function (like bot.send_message or message.copy) with
    a sliding window rate limiter and retry logic for transient failures.
    """
    def __init__(self, limiter: SlidingWindowRateLimiter, max_retries: int = 3):
        self.limiter = limiter
        self.max_retries = max_retries

    async def send(self, sender: Callable[..., Coroutine[Any, Any, Any]], *args, **kwargs) -> Any:
        """
        Call `sender(*args, **kwargs)` with rate limiting and retry on Telegram retry-after errors.
        `sender` is an async function like bot.send_message or update.message.copy.
        """
        last_exception = None
        for attempt in range(self.max_retries):
            try:
                await self.limiter.acquire()
                result = await sender(*args, **kwargs)
                return result
            except Exception as e:
                last_exception = e
                # Detect if it's a flood wait error from Telegram
                retry_after = self._extract_retry_after(e)
                if retry_after is not None:
                    wait = retry_after
                else:
                    # For other network errors, wait a short while
                    wait = 1.0
                logger.warning(
                    f"Sender failed (attempt {attempt+1}/{self.max_retries}): {e}. "
                    f"Retrying after {wait:.1f}s."
                )
                await asyncio.sleep(wait)
        # All retries exhausted
        raise last_exception if last_exception else RuntimeError("Max retries exceeded")

    @staticmethod
    def _extract_retry_after(exception: Exception) -> Optional[float]:
        """Extract retry_after from Telegram's RetryAfter exception, if present."""
        # PTB's RetryAfter exception has a `retry_after` attribute
        if hasattr(exception, 'retry_after'):
            return float(exception.retry_after)
        return None
