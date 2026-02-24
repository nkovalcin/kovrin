"""
Kovrin Claude Provider

Wraps the Anthropic SDK (anthropic.AsyncAnthropic) behind the
unified LLMProvider interface. This is the primary provider for
Kovrin — all safety-critical operations use Claude.

Supports:
- Tool use (native)
- System prompts
- Streaming (future)
- Vision (future)
"""

from __future__ import annotations

from typing import Any

import anthropic

from kovrin.providers.base import (
    ContentBlock,
    LLMProvider,
    LLMResponse,
    ProviderCapability,
    ProviderConfig,
)


class ClaudeProvider(LLMProvider):
    """Anthropic Claude provider via the official SDK.

    Uses anthropic.AsyncAnthropic for async API calls.
    Falls back to ANTHROPIC_API_KEY env var if no key provided.
    """

    DEFAULT_MODEL = "claude-sonnet-4-20250514"

    def __init__(
        self,
        config: ProviderConfig | None = None,
        client: anthropic.AsyncAnthropic | None = None,
    ):
        super().__init__(config or ProviderConfig(model=self.DEFAULT_MODEL))
        self._client = client or anthropic.AsyncAnthropic(
            api_key=self._config.api_key or None,
            timeout=self._config.timeout_seconds,
        )

    @property
    def client(self) -> anthropic.AsyncAnthropic:
        """Access the underlying Anthropic client (for backward compatibility)."""
        return self._client

    def supports(self, capability: ProviderCapability) -> bool:
        """Claude supports all current capabilities."""
        return capability in {
            ProviderCapability.TOOL_USE,
            ProviderCapability.SYSTEM_PROMPT,
            ProviderCapability.VISION,
        }

    async def _create_message_impl(
        self,
        messages: list[dict[str, Any]],
        *,
        max_tokens: int = 4096,
        system: str | None = None,
        tools: list[dict] | None = None,
        temperature: float | None = None,
    ) -> LLMResponse:
        """Create a message via Anthropic Claude API."""
        kwargs: dict[str, Any] = {
            "model": self._config.model,
            "max_tokens": max_tokens,
            "messages": messages,
        }
        if system:
            kwargs["system"] = system
        if tools:
            kwargs["tools"] = tools
        if temperature is not None:
            kwargs["temperature"] = temperature

        response = await self._client.messages.create(**kwargs)
        return self._to_response(response)

    @staticmethod
    def _to_response(response: Any) -> LLMResponse:
        """Convert Anthropic API response to unified LLMResponse."""
        blocks: list[ContentBlock] = []
        for block in response.content:
            if block.type == "text":
                blocks.append(ContentBlock(type="text", text=block.text))
            elif block.type == "tool_use":
                blocks.append(ContentBlock(
                    type="tool_use",
                    tool_name=block.name,
                    tool_input=block.input,
                    tool_use_id=block.id,
                ))

        return LLMResponse(
            content=blocks,
            stop_reason=response.stop_reason or "end_turn",
            model=response.model,
            input_tokens=response.usage.input_tokens,
            output_tokens=response.usage.output_tokens,
        )

    @classmethod
    def from_client(cls, client: anthropic.AsyncAnthropic, model: str | None = None) -> ClaudeProvider:
        """Create a ClaudeProvider from an existing Anthropic client.

        Useful for backward-compatible wiring where the client already exists.
        """
        config = ProviderConfig(model=model or cls.DEFAULT_MODEL)
        return cls(config=config, client=client)
