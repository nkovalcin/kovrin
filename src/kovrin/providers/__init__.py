"""
Kovrin LLM Provider Abstraction

Multi-model support with unified interface. Providers wrap different
LLM APIs (Anthropic, OpenAI, Ollama) behind a common interface.
The ModelRouter selects the optimal provider based on task requirements.

Usage:
    from kovrin.providers import create_provider, ModelRouter

    # Single provider
    provider = create_provider("claude")
    response = await provider.create_message(messages=[...])

    # Smart routing
    router = ModelRouter()
    provider = router.select(task_type="safety_critical")
"""

from kovrin.providers.base import LLMProvider, LLMResponse, ContentBlock, ProviderConfig
from kovrin.providers.claude import ClaudeProvider
from kovrin.providers.router import ModelRouter

__all__ = [
    "LLMProvider",
    "LLMResponse",
    "ContentBlock",
    "ProviderConfig",
    "ClaudeProvider",
    "ModelRouter",
    "create_provider",
]


def create_provider(
    name: str = "claude",
    *,
    api_key: str | None = None,
    model: str | None = None,
) -> LLMProvider:
    """Factory function to create an LLM provider by name.

    Args:
        name: Provider name ("claude", "openai", "ollama").
        api_key: Optional API key override.
        model: Optional model name override.

    Returns:
        Configured LLMProvider instance.
    """
    name_lower = name.lower()

    if name_lower in ("claude", "anthropic"):
        config = ProviderConfig(api_key=api_key, model=model or ClaudeProvider.DEFAULT_MODEL)
        return ClaudeProvider(config)
    elif name_lower == "openai":
        from kovrin.providers.openai import OpenAIProvider
        config = ProviderConfig(api_key=api_key, model=model or OpenAIProvider.DEFAULT_MODEL)
        return OpenAIProvider(config)
    elif name_lower == "ollama":
        from kovrin.providers.ollama import OllamaProvider
        config = ProviderConfig(model=model or OllamaProvider.DEFAULT_MODEL)
        return OllamaProvider(config)
    else:
        raise ValueError(
            f"Unknown provider: {name}. Supported: claude, openai, ollama"
        )
