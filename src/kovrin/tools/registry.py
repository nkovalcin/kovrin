"""
Kovrin Tool Registry

Central registry for all tools available to agents. Each tool
is registered with safety metadata (ToolRiskProfile) that
determines how the SafeToolRouter handles calls to it.

The registry enforces DCT scope restrictions when filtering
tools for a specific agent/token combination.
"""

from __future__ import annotations

from collections.abc import Awaitable, Callable
from typing import Any

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import DelegationScope, RiskLevel, SpeculationTier, SubTask
from kovrin.tools.models import ToolCategory, ToolRiskProfile


class RegisteredTool:
    """A tool registered in the system with safety metadata.

    Combines the Claude API tool definition, the safety risk profile,
    and the actual handler function that executes the tool.
    """

    def __init__(
        self,
        definition: ToolDefinition,
        risk_profile: ToolRiskProfile,
        handler: Callable[..., Any] | Callable[..., Awaitable[Any]],
    ):
        self.definition = definition
        self.risk_profile = risk_profile
        self.handler = handler

    @property
    def name(self) -> str:
        return self.definition.name

    @property
    def risk_level(self) -> RiskLevel:
        return self.risk_profile.risk_level

    @property
    def speculation_tier(self) -> SpeculationTier:
        return self.risk_profile.speculation_tier

    @property
    def category(self) -> ToolCategory:
        return self.risk_profile.category


class ToolRegistry:
    """Central registry for all available tools with safety classification.

    Tools are registered once at startup and queried per-task. The registry
    can filter tools based on DCT scope restrictions to enforce minimum
    privilege for delegated agents.
    """

    def __init__(self) -> None:
        self._tools: dict[str, RegisteredTool] = {}

    def register(self, tool: RegisteredTool) -> None:
        """Register a tool with its safety profile.

        Raises ValueError if a tool with the same name already exists.
        """
        if tool.name in self._tools:
            raise ValueError(f"Tool '{tool.name}' is already registered")
        self._tools[tool.name] = tool

    def get(self, name: str) -> RegisteredTool | None:
        """Look up a registered tool by name."""
        return self._tools.get(name)

    def get_all(self) -> list[RegisteredTool]:
        """Return all registered tools."""
        return list(self._tools.values())

    def get_for_scope(self, scope: DelegationScope) -> list[RegisteredTool]:
        """Return tools that fall within the given DCT scope.

        Filters by:
        - allowed_capabilities: tool scope_tags must intersect
        - allowed_risk_levels: tool risk must be in the allowed set
        - allowed_tool_categories: tool category must be in the allowed set
          (if the scope defines tool categories; empty means all allowed)
        """
        result: list[RegisteredTool] = []
        for tool in self._tools.values():
            # Check risk level
            if tool.risk_level not in scope.allowed_risk_levels:
                continue

            # Check capabilities (scope_tags vs allowed_capabilities)
            if scope.allowed_capabilities:
                if not set(tool.risk_profile.scope_tags) & set(scope.allowed_capabilities):
                    continue

            # Check tool categories (if scope defines them)
            allowed_cats = getattr(scope, "allowed_tool_categories", [])
            if allowed_cats and tool.category not in allowed_cats:
                continue

            result.append(tool)
        return result

    def get_schemas(self, tools: list[RegisteredTool] | None = None) -> list[dict]:
        """Get Claude API tool schemas for a set of tools.

        If tools is None, returns schemas for all registered tools.
        """
        source = tools if tools is not None else list(self._tools.values())
        return [
            {
                "name": t.definition.name,
                "description": t.definition.description,
                "input_schema": t.definition.input_schema,
            }
            for t in source
        ]

    def get_schemas_for_task(self, subtask: SubTask) -> list[dict]:
        """Get tool schemas appropriate for a given task's risk level.

        Returns tools whose risk_level does not exceed the task's risk level.
        This prevents low-risk tasks from accessing high-risk tools.
        """
        risk_order = [RiskLevel.LOW, RiskLevel.MEDIUM, RiskLevel.HIGH, RiskLevel.CRITICAL]
        max_idx = risk_order.index(subtask.risk_level) if subtask.risk_level in risk_order else 0

        eligible = [t for t in self._tools.values() if risk_order.index(t.risk_level) <= max_idx]
        return self.get_schemas(eligible)

    def __len__(self) -> int:
        return len(self._tools)

    def __contains__(self, name: str) -> bool:
        return name in self._tools
