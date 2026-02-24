"""
Kovrin Model Router

Smart routing of LLM requests to the optimal provider based on:
- Task type (safety-critical → Claude, general → configurable)
- Risk level (CRITICAL → strongest model)
- Budget constraints (optional)
- Provider availability (circuit breaker integration)

Safety-critical operations (Constitutional Core, Critics, Risk routing)
always use the strongest available model (Claude by default).
"""

from __future__ import annotations

from enum import Enum

from kovrin.providers.base import LLMProvider


class TaskType(str, Enum):
    """Classification of LLM task types for routing."""

    SAFETY_CRITICAL = "SAFETY_CRITICAL"  # Constitutional, Critics — strongest model
    EXECUTION = "EXECUTION"  # Task execution — configurable
    PARSING = "PARSING"  # Intent parsing — configurable
    ANALYSIS = "ANALYSIS"  # Confidence, PRM — configurable
    GENERAL = "GENERAL"  # Fallback — cheapest model


class ModelRouter:
    """Routes LLM requests to the optimal provider.

    Maintains a registry of providers and routing rules.
    Safety-critical tasks always use the primary provider (Claude).
    Other tasks can be routed to cheaper/faster alternatives.
    """

    def __init__(self, primary: LLMProvider | None = None):
        """Initialize with optional primary provider.

        If no primary is provided, one is created lazily on first use.
        """
        self._primary = primary
        self._providers: dict[str, LLMProvider] = {}
        self._task_routes: dict[TaskType, str] = {}

        if primary:
            self._providers[primary.name] = primary

    @property
    def primary(self) -> LLMProvider:
        """Get the primary provider (creates Claude if needed)."""
        if self._primary is None:
            from kovrin.providers.claude import ClaudeProvider

            self._primary = ClaudeProvider()
            self._providers[self._primary.name] = self._primary
        return self._primary

    def register_provider(self, name: str, provider: LLMProvider) -> None:
        """Register an alternative provider."""
        self._providers[name] = provider

    def set_route(self, task_type: TaskType, provider_name: str) -> None:
        """Set routing rule: task_type → provider_name.

        Safety-critical tasks cannot be rerouted away from primary.
        """
        if task_type == TaskType.SAFETY_CRITICAL:
            raise ValueError(
                "Cannot reroute SAFETY_CRITICAL tasks — they always use the primary provider."
            )
        if provider_name not in self._providers:
            raise ValueError(f"Unknown provider: {provider_name}")
        self._task_routes[task_type] = provider_name

    def select(self, task_type: TaskType = TaskType.GENERAL) -> LLMProvider:
        """Select the best provider for a given task type.

        Safety-critical tasks always use primary. Others follow routing rules.
        """
        if task_type == TaskType.SAFETY_CRITICAL:
            return self.primary

        provider_name = self._task_routes.get(task_type)
        if provider_name and provider_name in self._providers:
            return self._providers[provider_name]

        # Fallback to primary for any unrouted task
        return self.primary

    @property
    def available_providers(self) -> list[str]:
        """List all registered provider names."""
        return list(self._providers.keys())
