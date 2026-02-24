"""
Kovrin Ollama Provider

Wraps the Ollama REST API for local model execution.
No API key needed — runs against a local Ollama instance.

Default URL: http://localhost:11434
Override with OLLAMA_BASE_URL environment variable.

Supports tool use via Ollama's function calling (when the model supports it).

Requires: `pip install openai` (Ollama uses OpenAI-compatible API)
"""

from __future__ import annotations

import os
from typing import Any

from kovrin.providers.base import (
    LLMProvider,
    LLMResponse,
    ProviderCapability,
    ProviderConfig,
)


class OllamaProvider(LLMProvider):
    """Local Ollama provider using OpenAI-compatible API.

    Connects to a local Ollama instance via its OpenAI-compatible endpoint.
    No API key required. Model must be pulled first: `ollama pull llama3.1`
    """

    DEFAULT_MODEL = "llama3.1"
    DEFAULT_BASE_URL = "http://localhost:11434/v1"

    def __init__(self, config: ProviderConfig | None = None):
        super().__init__(config or ProviderConfig(model=self.DEFAULT_MODEL))
        if not self._config.base_url:
            self._config.base_url = os.environ.get("OLLAMA_BASE_URL", self.DEFAULT_BASE_URL)
        self._delegate = self._create_delegate()

    def _create_delegate(self) -> Any:
        """Create OpenAI provider targeting Ollama's API."""
        from kovrin.providers.openai import OpenAIProvider
        config = ProviderConfig(
            api_key="ollama",  # Ollama ignores API key but OpenAI SDK requires it
            model=self._config.model,
            base_url=self._config.base_url,
            timeout_seconds=self._config.timeout_seconds,
            max_retries=1,  # Local — no point in retries for network issues
        )
        return OpenAIProvider(config)

    def supports(self, capability: ProviderCapability) -> bool:
        """Ollama supports vary by model. Tool use requires compatible models."""
        return capability in {
            ProviderCapability.SYSTEM_PROMPT,
            ProviderCapability.TOOL_USE,  # Depends on model, but we expose it
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
        """Delegate to OpenAI provider targeting Ollama."""
        return await self._delegate._create_message_impl(
            messages,
            max_tokens=max_tokens,
            system=system,
            tools=tools,
            temperature=temperature,
        )
