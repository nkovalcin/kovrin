"""Tests for the Kovrin provider abstraction layer.

Covers:
- ClaudeProvider response conversion
- LLMResponse properties
- ProviderConfig defaults
- ModelRouter routing logic
- CircuitBreaker state machine
- Provider factory
"""

from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.providers.base import (
    ContentBlock,
    LLMProvider,
    LLMResponse,
    ProviderCapability,
    ProviderConfig,
)
from kovrin.providers.circuit_breaker import CircuitBreakerProvider, CircuitState
from kovrin.providers.claude import ClaudeProvider
from kovrin.providers.router import ModelRouter, TaskType

# ─── ContentBlock ──────────────────────────────────────────


class TestContentBlock:
    def test_text_block(self):
        block = ContentBlock(type="text", text="Hello")
        assert block.type == "text"
        assert block.text == "Hello"

    def test_tool_use_block(self):
        block = ContentBlock(
            type="tool_use",
            tool_name="calculator",
            tool_input={"expression": "2+2"},
            tool_use_id="tool-123",
        )
        assert block.type == "tool_use"
        assert block.tool_name == "calculator"
        assert block.tool_input == {"expression": "2+2"}


# ─── LLMResponse ──────────────────────────────────────────


class TestLLMResponse:
    def test_text_property(self):
        response = LLMResponse(
            content=[
                ContentBlock(type="text", text="Hello "),
                ContentBlock(type="text", text="world"),
            ],
        )
        assert response.text == "Hello world"

    def test_tool_calls_property(self):
        response = LLMResponse(
            content=[
                ContentBlock(type="text", text="Let me calculate"),
                ContentBlock(type="tool_use", tool_name="calculator"),
            ],
            stop_reason="tool_use",
        )
        assert len(response.tool_calls) == 1
        assert response.tool_calls[0].tool_name == "calculator"

    def test_has_tool_use(self):
        response = LLMResponse(
            content=[ContentBlock(type="tool_use", tool_name="calc")],
            stop_reason="tool_use",
        )
        assert response.has_tool_use is True

    def test_no_tool_use(self):
        response = LLMResponse(
            content=[ContentBlock(type="text", text="No tools")],
            stop_reason="end_turn",
        )
        assert response.has_tool_use is False

    def test_empty_response(self):
        response = LLMResponse()
        assert response.text == ""
        assert response.tool_calls == []
        assert response.has_tool_use is False


# ─── ProviderConfig ────────────────────────────────────────


class TestProviderConfig:
    def test_defaults(self):
        config = ProviderConfig()
        assert config.max_retries == 3
        assert config.timeout_seconds == 30.0
        assert config.retry_base_delay == 1.0

    def test_custom_config(self):
        config = ProviderConfig(
            api_key="test-key",
            model="gpt-4o",
            max_retries=5,
        )
        assert config.api_key == "test-key"
        assert config.model == "gpt-4o"
        assert config.max_retries == 5


# ─── ClaudeProvider ────────────────────────────────────────


class TestClaudeProvider:
    def test_default_model(self):
        assert ClaudeProvider.DEFAULT_MODEL == "claude-sonnet-4-6"

    def test_supports_tool_use(self):
        client = MagicMock()
        provider = ClaudeProvider(client=client)
        assert provider.supports(ProviderCapability.TOOL_USE) is True

    def test_supports_system_prompt(self):
        client = MagicMock()
        provider = ClaudeProvider(client=client)
        assert provider.supports(ProviderCapability.SYSTEM_PROMPT) is True

    def test_does_not_support_json_mode(self):
        client = MagicMock()
        provider = ClaudeProvider(client=client)
        assert provider.supports(ProviderCapability.JSON_MODE) is False

    def test_to_response_text(self):
        """Test converting Anthropic response with text block."""
        mock_response = MagicMock()
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Hello, world!"
        mock_response.content = [text_block]
        mock_response.stop_reason = "end_turn"
        mock_response.model = "claude-sonnet-4-6"
        mock_response.usage = MagicMock(input_tokens=10, output_tokens=5)

        result = ClaudeProvider._to_response(mock_response)
        assert isinstance(result, LLMResponse)
        assert result.text == "Hello, world!"
        assert result.stop_reason == "end_turn"
        assert result.input_tokens == 10
        assert result.output_tokens == 5

    def test_to_response_tool_use(self):
        """Test converting Anthropic response with tool_use block."""
        mock_response = MagicMock()
        tool_block = MagicMock()
        tool_block.type = "tool_use"
        tool_block.name = "calculator"
        tool_block.input = {"expression": "2+2"}
        tool_block.id = "tool-abc"
        mock_response.content = [tool_block]
        mock_response.stop_reason = "tool_use"
        mock_response.model = "claude-sonnet-4-6"
        mock_response.usage = MagicMock(input_tokens=20, output_tokens=15)

        result = ClaudeProvider._to_response(mock_response)
        assert result.has_tool_use is True
        assert len(result.tool_calls) == 1
        assert result.tool_calls[0].tool_name == "calculator"
        assert result.tool_calls[0].tool_use_id == "tool-abc"

    def test_from_client(self):
        """Test creating provider from existing client."""
        client = MagicMock()
        provider = ClaudeProvider.from_client(client)
        assert provider.client is client
        assert provider.model == ClaudeProvider.DEFAULT_MODEL

    def test_from_client_custom_model(self):
        client = MagicMock()
        provider = ClaudeProvider.from_client(client, model="claude-3-haiku-20240307")
        assert provider.model == "claude-3-haiku-20240307"

    @pytest.mark.asyncio
    async def test_create_message_calls_api(self):
        """Test that create_message calls the Anthropic API."""
        client = MagicMock()
        mock_response = MagicMock()
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Response"
        mock_response.content = [text_block]
        mock_response.stop_reason = "end_turn"
        mock_response.model = "claude-sonnet-4-6"
        mock_response.usage = MagicMock(input_tokens=5, output_tokens=3)
        client.messages = MagicMock()
        client.messages.create = AsyncMock(return_value=mock_response)

        provider = ClaudeProvider(client=client)
        result = await provider.create_message(
            messages=[{"role": "user", "content": "Hello"}],
        )

        assert result.text == "Response"
        client.messages.create.assert_called_once()


# ─── ModelRouter ───────────────────────────────────────────


class TestModelRouter:
    def test_safety_critical_always_primary(self):
        client = MagicMock()
        primary = ClaudeProvider(client=client)
        router = ModelRouter(primary=primary)
        selected = router.select(TaskType.SAFETY_CRITICAL)
        assert selected is primary

    def test_cannot_reroute_safety_critical(self):
        client = MagicMock()
        primary = ClaudeProvider(client=client)
        router = ModelRouter(primary=primary)

        mock_provider = MagicMock(spec=LLMProvider)
        router.register_provider("mock", mock_provider)

        with pytest.raises(ValueError, match="Cannot reroute SAFETY_CRITICAL"):
            router.set_route(TaskType.SAFETY_CRITICAL, "mock")

    def test_custom_route(self):
        client = MagicMock()
        primary = ClaudeProvider(client=client)
        router = ModelRouter(primary=primary)

        mock_provider = MagicMock(spec=LLMProvider)
        router.register_provider("cheap", mock_provider)
        router.set_route(TaskType.GENERAL, "cheap")

        selected = router.select(TaskType.GENERAL)
        assert selected is mock_provider

    def test_unrouted_falls_back_to_primary(self):
        client = MagicMock()
        primary = ClaudeProvider(client=client)
        router = ModelRouter(primary=primary)

        selected = router.select(TaskType.EXECUTION)
        assert selected is primary

    def test_lazy_primary_creation(self):
        """Primary is created lazily if not provided."""
        router = ModelRouter()
        # Accessing primary should create a ClaudeProvider
        primary = router.primary
        assert isinstance(primary, ClaudeProvider)

    def test_unknown_provider_in_route(self):
        router = ModelRouter()
        with pytest.raises(ValueError, match="Unknown provider"):
            router.set_route(TaskType.GENERAL, "nonexistent")

    def test_available_providers(self):
        client = MagicMock()
        primary = ClaudeProvider(client=client)
        router = ModelRouter(primary=primary)

        mock = MagicMock(spec=LLMProvider)
        router.register_provider("mock", mock)

        assert "mock" in router.available_providers


# ─── CircuitBreaker ────────────────────────────────────────


class TestCircuitBreaker:
    def _make_provider(self) -> ClaudeProvider:
        client = MagicMock()
        return ClaudeProvider(client=client)

    def test_initial_state_closed(self):
        provider = self._make_provider()
        cb = CircuitBreakerProvider(provider, failure_threshold=3)
        assert cb.state == CircuitState.CLOSED

    @pytest.mark.asyncio
    async def test_success_stays_closed(self):
        provider = self._make_provider()
        mock_response = MagicMock()
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "OK"
        mock_response.content = [text_block]
        mock_response.stop_reason = "end_turn"
        mock_response.model = "test"
        mock_response.usage = MagicMock(input_tokens=1, output_tokens=1)
        provider._client.messages = MagicMock()
        provider._client.messages.create = AsyncMock(return_value=mock_response)

        cb = CircuitBreakerProvider(provider, failure_threshold=3)
        result = await cb.create_message(messages=[{"role": "user", "content": "test"}])
        assert result.text == "OK"
        assert cb.state == CircuitState.CLOSED

    @pytest.mark.asyncio
    async def test_failures_open_circuit(self):
        provider = self._make_provider()
        provider._client.messages = MagicMock()
        provider._client.messages.create = AsyncMock(side_effect=RuntimeError("API down"))

        cb = CircuitBreakerProvider(
            provider,
            failure_threshold=2,
            recovery_timeout=60.0,
        )
        # Config max_retries=1 to avoid retries in the outer provider
        cb._config.max_retries = 1

        for _ in range(2):
            with pytest.raises(RuntimeError):
                await cb.create_message(messages=[{"role": "user", "content": "test"}])

        assert cb._state == CircuitState.OPEN

    def test_reset(self):
        provider = self._make_provider()
        cb = CircuitBreakerProvider(provider, failure_threshold=3)
        cb._state = CircuitState.OPEN
        cb._failure_count = 5
        cb.reset()
        assert cb.state == CircuitState.CLOSED
        assert cb._failure_count == 0

    def test_wrapped_provider(self):
        provider = self._make_provider()
        cb = CircuitBreakerProvider(provider)
        assert cb.wrapped_provider is provider

    def test_supports_delegates(self):
        provider = self._make_provider()
        cb = CircuitBreakerProvider(provider)
        assert cb.supports(ProviderCapability.TOOL_USE) == provider.supports(
            ProviderCapability.TOOL_USE
        )


# ─── Factory ──────────────────────────────────────────────


class TestProviderFactory:
    def test_create_claude(self):
        from kovrin.providers import create_provider

        provider = create_provider("claude")
        assert isinstance(provider, ClaudeProvider)

    def test_create_anthropic_alias(self):
        from kovrin.providers import create_provider

        provider = create_provider("anthropic")
        assert isinstance(provider, ClaudeProvider)

    def test_unknown_provider_raises(self):
        from kovrin.providers import create_provider

        with pytest.raises(ValueError, match="Unknown provider"):
            create_provider("unknown_llm")

    def test_create_openai_requires_package(self):
        """OpenAI provider should raise ImportError if openai not installed."""
        from kovrin.providers import create_provider

        # This may succeed if openai is installed, or raise ImportError
        try:
            provider = create_provider("openai")
            # If it succeeds, it's an OpenAIProvider
            from kovrin.providers.openai import OpenAIProvider

            assert isinstance(provider, OpenAIProvider)
        except ImportError:
            pass  # Expected if openai package is not installed
