"""
Kovrin LLM Provider Base

Abstract interface for LLM providers. All providers implement this
interface, allowing the framework to swap models without changing
business logic.

Key design decisions:
- Async-first (all providers are async)
- Retry with exponential backoff built into base class
- Tool use abstracted into a common format
- Provider-agnostic response model (LLMResponse)
"""

from __future__ import annotations

import asyncio
import time
from abc import ABC, abstractmethod
from enum import Enum
from typing import Any

from pydantic import BaseModel, Field


class ContentBlock(BaseModel):
    """A single content block in an LLM response.

    Abstracts over provider-specific formats (Anthropic's content blocks,
    OpenAI's choices, etc.) into a unified structure.
    """
    type: str = "text"  # "text" or "tool_use"
    text: str = ""
    tool_name: str = ""
    tool_input: dict[str, Any] = Field(default_factory=dict)
    tool_use_id: str = ""


class LLMResponse(BaseModel):
    """Unified response from any LLM provider.

    Normalizes different API response formats into a single structure
    that the Kovrin engine can process uniformly.
    """
    content: list[ContentBlock] = Field(default_factory=list)
    stop_reason: str = "end_turn"
    model: str = ""
    input_tokens: int = 0
    output_tokens: int = 0

    @property
    def text(self) -> str:
        """Extract concatenated text from all text blocks."""
        return "".join(b.text for b in self.content if b.type == "text")

    @property
    def tool_calls(self) -> list[ContentBlock]:
        """Extract all tool_use blocks."""
        return [b for b in self.content if b.type == "tool_use"]

    @property
    def has_tool_use(self) -> bool:
        """Check if response contains any tool_use blocks."""
        return self.stop_reason == "tool_use" or any(b.type == "tool_use" for b in self.content)


class ProviderConfig(BaseModel):
    """Configuration for an LLM provider."""
    api_key: str | None = None
    model: str = ""
    base_url: str | None = None
    max_retries: int = 3
    timeout_seconds: float = 30.0
    retry_base_delay: float = 1.0  # exponential backoff base (1s, 2s, 4s)


class ProviderCapability(str, Enum):
    """Capabilities that providers may support."""
    TOOL_USE = "TOOL_USE"
    STREAMING = "STREAMING"
    VISION = "VISION"
    SYSTEM_PROMPT = "SYSTEM_PROMPT"
    JSON_MODE = "JSON_MODE"


class LLMProvider(ABC):
    """Abstract base class for LLM providers.

    All providers must implement create_message(). The base class
    provides retry logic with exponential backoff.
    """

    def __init__(self, config: ProviderConfig | None = None):
        self._config = config or ProviderConfig()

    @property
    def name(self) -> str:
        """Human-readable provider name."""
        return self.__class__.__name__

    @property
    def model(self) -> str:
        """Current model name."""
        return self._config.model

    @abstractmethod
    def supports(self, capability: ProviderCapability) -> bool:
        """Check if this provider supports a given capability."""
        ...

    @abstractmethod
    async def _create_message_impl(
        self,
        messages: list[dict[str, Any]],
        *,
        max_tokens: int = 4096,
        system: str | None = None,
        tools: list[dict] | None = None,
        temperature: float | None = None,
    ) -> LLMResponse:
        """Provider-specific implementation of message creation.

        Subclasses implement this. The base class wraps it with retry logic.
        """
        ...

    async def create_message(
        self,
        messages: list[dict[str, Any]],
        *,
        max_tokens: int = 4096,
        system: str | None = None,
        tools: list[dict] | None = None,
        temperature: float | None = None,
        model: str | None = None,
    ) -> LLMResponse:
        """Create a message with automatic retry and exponential backoff.

        Args:
            messages: List of message dicts (role + content).
            max_tokens: Maximum tokens in response.
            system: Optional system prompt.
            tools: Optional tool definitions for tool use.
            temperature: Optional temperature override.
            model: Optional model override for this call only.

        Returns:
            Unified LLMResponse.
        """
        original_model = self._config.model
        if model:
            self._config.model = model

        last_error: Exception | None = None
        for attempt in range(self._config.max_retries):
            try:
                response = await self._create_message_impl(
                    messages,
                    max_tokens=max_tokens,
                    system=system,
                    tools=tools,
                    temperature=temperature,
                )
                if model:
                    self._config.model = original_model
                return response
            except Exception as e:
                last_error = e
                if attempt < self._config.max_retries - 1:
                    delay = self._config.retry_base_delay * (2 ** attempt)
                    await asyncio.sleep(delay)

        if model:
            self._config.model = original_model

        raise RuntimeError(
            f"Provider {self.name} failed after {self._config.max_retries} retries: {last_error}"
        ) from last_error
