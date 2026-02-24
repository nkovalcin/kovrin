"""
Kovrin Circuit Breaker

Wraps LLM provider calls with circuit breaker pattern to prevent
cascading failures when a provider is down or degraded.

States:
- CLOSED: Normal operation, requests pass through
- OPEN: Provider is failing, requests are rejected immediately
- HALF_OPEN: Testing if provider has recovered

Transitions:
- CLOSED → OPEN: After N consecutive failures
- OPEN → HALF_OPEN: After M seconds cooldown
- HALF_OPEN → CLOSED: Successful test request
- HALF_OPEN → OPEN: Failed test request
"""

from __future__ import annotations

import asyncio
import time
from enum import Enum
from typing import Any

from kovrin.providers.base import LLMProvider, LLMResponse, ProviderCapability, ProviderConfig


class CircuitState(str, Enum):
    """Circuit breaker states."""

    CLOSED = "CLOSED"
    OPEN = "OPEN"
    HALF_OPEN = "HALF_OPEN"


class CircuitBreakerProvider(LLMProvider):
    """Wraps an LLM provider with circuit breaker protection.

    When the underlying provider fails repeatedly, the circuit opens
    and requests fail fast without hitting the provider. After a cooldown
    period, a single test request is allowed through (half-open). If it
    succeeds, the circuit closes again.
    """

    def __init__(
        self,
        provider: LLMProvider,
        failure_threshold: int = 5,
        recovery_timeout: float = 60.0,
        config: ProviderConfig | None = None,
    ):
        """Initialize circuit breaker.

        Args:
            provider: The underlying LLM provider to protect.
            failure_threshold: Number of consecutive failures before opening.
            recovery_timeout: Seconds to wait before testing recovery.
        """
        super().__init__(config or provider._config)
        self._provider = provider
        self._failure_threshold = failure_threshold
        self._recovery_timeout = recovery_timeout
        self._state = CircuitState.CLOSED
        self._failure_count = 0
        self._last_failure_time = 0.0
        self._lock = asyncio.Lock()

    @property
    def state(self) -> CircuitState:
        """Current circuit state."""
        if self._state == CircuitState.OPEN:
            # Check if cooldown has elapsed
            if time.monotonic() - self._last_failure_time >= self._recovery_timeout:
                return CircuitState.HALF_OPEN
        return self._state

    @property
    def wrapped_provider(self) -> LLMProvider:
        """Access the underlying provider."""
        return self._provider

    def supports(self, capability: ProviderCapability) -> bool:
        """Delegate capability check to wrapped provider."""
        return self._provider.supports(capability)

    async def _create_message_impl(
        self,
        messages: list[dict[str, Any]],
        *,
        max_tokens: int = 4096,
        system: str | None = None,
        tools: list[dict] | None = None,
        temperature: float | None = None,
    ) -> LLMResponse:
        """Execute with circuit breaker protection."""
        async with self._lock:
            current_state = self.state

            if current_state == CircuitState.OPEN:
                raise RuntimeError(
                    f"Circuit breaker OPEN for {self._provider.name} — "
                    f"provider unavailable (failed {self._failure_count} times, "
                    f"cooldown {self._recovery_timeout}s)"
                )

        try:
            response = await self._provider._create_message_impl(
                messages,
                max_tokens=max_tokens,
                system=system,
                tools=tools,
                temperature=temperature,
            )
            async with self._lock:
                self._failure_count = 0
                self._state = CircuitState.CLOSED
            return response

        except Exception:
            async with self._lock:
                self._failure_count += 1
                self._last_failure_time = time.monotonic()
                if self._failure_count >= self._failure_threshold:
                    self._state = CircuitState.OPEN
            raise

    def reset(self) -> None:
        """Manually reset the circuit breaker to CLOSED state."""
        self._state = CircuitState.CLOSED
        self._failure_count = 0
        self._last_failure_time = 0.0
