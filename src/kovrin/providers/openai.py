"""
Kovrin OpenAI Provider

Wraps the OpenAI API (compatible with GPT-4o, o1, etc.) behind
the unified LLMProvider interface.

Requires: `pip install openai` or `pip install kovrin[openai]`
Set OPENAI_API_KEY environment variable.

Also compatible with OpenAI-compatible APIs (Azure, Together,
Groq, Fireworks) via base_url override.
"""

from __future__ import annotations

from typing import Any

from kovrin.providers.base import (
    ContentBlock,
    LLMProvider,
    LLMResponse,
    ProviderCapability,
    ProviderConfig,
)


class OpenAIProvider(LLMProvider):
    """OpenAI and OpenAI-compatible provider.

    Uses the official openai Python SDK. Falls back to OPENAI_API_KEY env var.
    Compatible with any OpenAI-compatible API via base_url config.
    """

    DEFAULT_MODEL = "gpt-4o"

    def __init__(self, config: ProviderConfig | None = None):
        super().__init__(config or ProviderConfig(model=self.DEFAULT_MODEL))
        self._client = self._create_client()

    def _create_client(self) -> Any:
        """Create OpenAI async client. Imports openai lazily."""
        try:
            from openai import AsyncOpenAI
        except ImportError as e:
            raise ImportError(
                "OpenAI provider requires the 'openai' package. Install with: pip install openai"
            ) from e

        kwargs: dict[str, Any] = {}
        if self._config.api_key:
            kwargs["api_key"] = self._config.api_key
        if self._config.base_url:
            kwargs["base_url"] = self._config.base_url
        kwargs["timeout"] = self._config.timeout_seconds

        return AsyncOpenAI(**kwargs)

    def supports(self, capability: ProviderCapability) -> bool:
        """OpenAI supports tool use, system prompts, and vision."""
        return capability in {
            ProviderCapability.TOOL_USE,
            ProviderCapability.SYSTEM_PROMPT,
            ProviderCapability.VISION,
            ProviderCapability.JSON_MODE,
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
        """Create a message via OpenAI API."""
        # OpenAI uses system message in messages list
        oai_messages = []
        if system:
            oai_messages.append({"role": "system", "content": system})

        # Convert Anthropic-style messages to OpenAI format
        for msg in messages:
            oai_messages.append(self._convert_message(msg))

        kwargs: dict[str, Any] = {
            "model": self._config.model,
            "max_tokens": max_tokens,
            "messages": oai_messages,
        }

        if tools:
            kwargs["tools"] = self._convert_tools(tools)
        if temperature is not None:
            kwargs["temperature"] = temperature

        response = await self._client.chat.completions.create(**kwargs)
        return self._to_response(response)

    @staticmethod
    def _convert_message(msg: dict[str, Any]) -> dict[str, Any]:
        """Convert Anthropic-style message to OpenAI format."""
        content = msg.get("content", "")

        # Handle tool_result messages
        if msg.get("role") == "user" and isinstance(content, list):
            # Check if this is a tool_result list
            tool_results = [
                c for c in content if isinstance(c, dict) and c.get("type") == "tool_result"
            ]
            if tool_results:
                # OpenAI expects tool messages separately
                # Return the first one (multi-tool results need special handling)
                tr = tool_results[0]
                return {
                    "role": "tool",
                    "tool_call_id": tr.get("tool_use_id", ""),
                    "content": tr.get("content", ""),
                }

        # Handle assistant messages with tool_use content blocks
        if msg.get("role") == "assistant" and isinstance(content, list):
            text_parts = []
            tool_calls = []
            for block in content:
                if hasattr(block, "type"):
                    if block.type == "text":
                        text_parts.append(block.text)
                    elif block.type == "tool_use":
                        import json

                        tool_calls.append(
                            {
                                "id": block.id,
                                "type": "function",
                                "function": {
                                    "name": block.name,
                                    "arguments": json.dumps(block.input),
                                },
                            }
                        )

            result: dict[str, Any] = {
                "role": "assistant",
                "content": "\n".join(text_parts) if text_parts else None,
            }
            if tool_calls:
                result["tool_calls"] = tool_calls
            return result

        return {"role": msg["role"], "content": str(content)}

    @staticmethod
    def _convert_tools(tools: list[dict]) -> list[dict]:
        """Convert Anthropic tool schema to OpenAI function calling format."""
        oai_tools = []
        for tool in tools:
            oai_tools.append(
                {
                    "type": "function",
                    "function": {
                        "name": tool["name"],
                        "description": tool.get("description", ""),
                        "parameters": tool.get("input_schema", {}),
                    },
                }
            )
        return oai_tools

    @staticmethod
    def _to_response(response: Any) -> LLMResponse:
        """Convert OpenAI API response to unified LLMResponse."""
        choice = response.choices[0] if response.choices else None
        if not choice:
            return LLMResponse()

        blocks: list[ContentBlock] = []
        msg = choice.message

        # Text content
        if msg.content:
            blocks.append(ContentBlock(type="text", text=msg.content))

        # Tool calls
        if msg.tool_calls:
            import json

            for tc in msg.tool_calls:
                blocks.append(
                    ContentBlock(
                        type="tool_use",
                        tool_name=tc.function.name,
                        tool_input=json.loads(tc.function.arguments),
                        tool_use_id=tc.id,
                    )
                )

        # Map finish_reason to Anthropic-style stop_reason
        stop_reason_map = {
            "stop": "end_turn",
            "tool_calls": "tool_use",
            "length": "max_tokens",
            "content_filter": "end_turn",
        }
        stop_reason = stop_reason_map.get(choice.finish_reason or "stop", "end_turn")

        usage = response.usage
        return LLMResponse(
            content=blocks,
            stop_reason=stop_reason,
            model=response.model or "",
            input_tokens=usage.prompt_tokens if usage else 0,
            output_tokens=usage.completion_tokens if usage else 0,
        )
