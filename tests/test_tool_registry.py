"""Tests for the Kovrin Tool Registry.

Covers tool registration, lookup, scope filtering, and schema generation.
"""

import pytest

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import DelegationScope, RiskLevel, SpeculationTier, SubTask
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool, ToolRegistry


def _make_tool(
    name: str,
    risk: RiskLevel = RiskLevel.LOW,
    tier: SpeculationTier = SpeculationTier.FREE,
    category: ToolCategory = ToolCategory.READ_ONLY,
    scope_tags: list[str] | None = None,
) -> RegisteredTool:
    """Helper to create test tools."""
    return RegisteredTool(
        definition=ToolDefinition(
            name=name,
            description=f"Test tool: {name}",
            input_schema={"type": "object", "properties": {}},
        ),
        risk_profile=ToolRiskProfile(
            risk_level=risk,
            speculation_tier=tier,
            category=category,
            scope_tags=scope_tags or [],
        ),
        handler=lambda: f"result from {name}",
    )


class TestToolRegistration:
    """Tests for registering and looking up tools."""

    def test_register_tool(self):
        registry = ToolRegistry()
        tool = _make_tool("test_tool")
        registry.register(tool)
        assert "test_tool" in registry
        assert len(registry) == 1

    def test_register_duplicate_raises(self):
        registry = ToolRegistry()
        tool = _make_tool("test_tool")
        registry.register(tool)
        with pytest.raises(ValueError, match="already registered"):
            registry.register(tool)

    def test_get_existing_tool(self):
        registry = ToolRegistry()
        tool = _make_tool("calc")
        registry.register(tool)
        result = registry.get("calc")
        assert result is not None
        assert result.name == "calc"

    def test_get_nonexistent_tool(self):
        registry = ToolRegistry()
        assert registry.get("nonexistent") is None

    def test_get_all_tools(self):
        registry = ToolRegistry()
        registry.register(_make_tool("a"))
        registry.register(_make_tool("b"))
        registry.register(_make_tool("c"))
        all_tools = registry.get_all()
        assert len(all_tools) == 3
        names = {t.name for t in all_tools}
        assert names == {"a", "b", "c"}


class TestScopeFiltering:
    """Tests for DCT scope-based tool filtering."""

    def test_filter_by_risk_level(self):
        registry = ToolRegistry()
        registry.register(_make_tool("low", risk=RiskLevel.LOW))
        registry.register(_make_tool("med", risk=RiskLevel.MEDIUM))
        registry.register(_make_tool("high", risk=RiskLevel.HIGH))

        scope = DelegationScope(allowed_risk_levels=[RiskLevel.LOW])
        result = registry.get_for_scope(scope)
        assert len(result) == 1
        assert result[0].name == "low"

    def test_filter_by_capabilities(self):
        registry = ToolRegistry()
        registry.register(_make_tool("reader", scope_tags=["read_only"]))
        registry.register(_make_tool("writer", scope_tags=["filesystem"]))
        registry.register(_make_tool("coder", scope_tags=["code_execution"]))

        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_capabilities=["read_only"],
        )
        result = registry.get_for_scope(scope)
        assert len(result) == 1
        assert result[0].name == "reader"

    def test_filter_by_tool_categories(self):
        registry = ToolRegistry()
        registry.register(_make_tool("calc", category=ToolCategory.COMPUTATION))
        registry.register(_make_tool("net", category=ToolCategory.NETWORK))
        registry.register(_make_tool("code", category=ToolCategory.CODE_EXECUTION))

        scope = DelegationScope(
            allowed_risk_levels=[RiskLevel.LOW],
            allowed_tool_categories=[ToolCategory.COMPUTATION],
        )
        result = registry.get_for_scope(scope)
        assert len(result) == 1
        assert result[0].name == "calc"

    def test_empty_scope_allows_all_risk_matched(self):
        """Empty capabilities and categories should not filter."""
        registry = ToolRegistry()
        registry.register(_make_tool("a", risk=RiskLevel.LOW))
        registry.register(_make_tool("b", risk=RiskLevel.LOW))

        scope = DelegationScope(allowed_risk_levels=[RiskLevel.LOW])
        result = registry.get_for_scope(scope)
        assert len(result) == 2


class TestSchemaGeneration:
    """Tests for generating Claude API tool schemas."""

    def test_get_schemas_all(self):
        registry = ToolRegistry()
        registry.register(_make_tool("a"))
        registry.register(_make_tool("b"))
        schemas = registry.get_schemas()
        assert len(schemas) == 2
        assert all("name" in s and "description" in s and "input_schema" in s for s in schemas)

    def test_get_schemas_for_task_risk_filtering(self):
        """Tools with risk higher than task risk should be excluded."""
        registry = ToolRegistry()
        registry.register(_make_tool("low_tool", risk=RiskLevel.LOW))
        registry.register(_make_tool("med_tool", risk=RiskLevel.MEDIUM))
        registry.register(_make_tool("high_tool", risk=RiskLevel.HIGH))

        low_task = SubTask(id="t1", description="test", risk_level=RiskLevel.LOW)
        schemas = registry.get_schemas_for_task(low_task)
        assert len(schemas) == 1
        assert schemas[0]["name"] == "low_tool"

    def test_get_schemas_for_high_risk_task(self):
        """High-risk task should have access to LOW, MEDIUM, and HIGH tools."""
        registry = ToolRegistry()
        registry.register(_make_tool("low_tool", risk=RiskLevel.LOW))
        registry.register(_make_tool("med_tool", risk=RiskLevel.MEDIUM))
        registry.register(_make_tool("high_tool", risk=RiskLevel.HIGH))
        registry.register(_make_tool("crit_tool", risk=RiskLevel.CRITICAL))

        high_task = SubTask(id="t1", description="test", risk_level=RiskLevel.HIGH)
        schemas = registry.get_schemas_for_task(high_task)
        assert len(schemas) == 3
        names = {s["name"] for s in schemas}
        assert names == {"low_tool", "med_tool", "high_tool"}


class TestBuiltinTools:
    """Tests for the built-in tool registration."""

    def test_register_all_builtins(self):
        from kovrin.tools.builtin import register_all_builtins

        registry = ToolRegistry()
        register_all_builtins(registry)
        assert (
            len(registry) == 8
        )  # calc, datetime, json, code, web_search, http, file_read, file_write

    def test_builtin_tool_names(self):
        from kovrin.tools.builtin import register_all_builtins

        registry = ToolRegistry()
        register_all_builtins(registry)
        expected = {
            "calculator",
            "current_datetime",
            "json_formatter",
            "code_execution",
            "web_search",
            "http_request",
            "file_read",
            "file_write",
        }
        actual = {t.name for t in registry.get_all()}
        assert actual == expected

    def test_code_exec_is_high_risk(self):
        from kovrin.tools.builtin import CODE_EXEC_TOOL

        assert CODE_EXEC_TOOL.risk_level == RiskLevel.HIGH
        assert CODE_EXEC_TOOL.speculation_tier == SpeculationTier.GUARDED

    def test_web_search_is_low_risk(self):
        from kovrin.tools.builtin import WEB_SEARCH_TOOL

        assert WEB_SEARCH_TOOL.risk_level == RiskLevel.LOW
        assert WEB_SEARCH_TOOL.speculation_tier == SpeculationTier.FREE
