"""
Kovrin Model Pricing

Token-to-USD cost calculation for all supported LLM providers.
Prices are per million tokens (as of February 2026).
"""

from __future__ import annotations

# Pricing per 1M tokens (USD)
# Source: provider pricing pages
MODEL_PRICING: dict[str, dict[str, float]] = {
    # Claude models
    "claude-haiku-4-5": {"input": 0.80, "output": 4.00},
    "claude-sonnet-4-6": {"input": 3.00, "output": 15.00},
    "claude-opus-4-6": {"input": 15.00, "output": 75.00},
    # Legacy Claude model IDs (still used in some places)
    "claude-haiku-3-5-20241022": {"input": 0.80, "output": 4.00},
    "claude-sonnet-4-20250514": {"input": 3.00, "output": 15.00},
    "claude-opus-4-20250514": {"input": 15.00, "output": 75.00},
    # OpenAI models
    "gpt-4o": {"input": 2.50, "output": 10.00},
    "gpt-4o-mini": {"input": 0.15, "output": 0.60},
    "o1": {"input": 15.00, "output": 60.00},
    "o1-mini": {"input": 3.00, "output": 12.00},
}

# Default fallback for unknown models
_DEFAULT_PRICING = {"input": 3.00, "output": 15.00}


def calculate_cost(
    model: str,
    input_tokens: int,
    output_tokens: int,
) -> float:
    """Calculate cost in USD for a single LLM call.

    Args:
        model: Model ID string.
        input_tokens: Number of input tokens.
        output_tokens: Number of output tokens.

    Returns:
        Cost in USD (float).
    """
    pricing = MODEL_PRICING.get(model, _DEFAULT_PRICING)
    cost = (
        input_tokens * pricing["input"] / 1_000_000
        + output_tokens * pricing["output"] / 1_000_000
    )
    return round(cost, 8)


def detect_provider(model: str) -> str:
    """Detect provider name from model ID."""
    if model.startswith("claude"):
        return "anthropic"
    if model.startswith(("gpt", "o1")):
        return "openai"
    return "unknown"
