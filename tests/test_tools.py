"""
Tests for Tool Use system.

Verifies:
- Tool registration and execution
- Built-in tools (calculator, datetime, json_formatter)
- Agent with tools — mock Claude tool_use flow
- Error handling for unknown tools
- ToolExecutor schemas
"""

import asyncio
import json
from unittest.mock import AsyncMock, MagicMock

import pytest

from kovrin.agents.base import Agent
from kovrin.agents.tools import (
    ToolDefinition,
    ToolExecutor,
    _calculator,
    _current_datetime,
    _json_formatter,
    create_default_tools,
)
from kovrin.core.models import AgentRole, SubTask

# ─── Built-in Tools ────────────────────────────────────────


class TestCalculator:
    def test_basic_arithmetic(self):
        assert _calculator("2 + 3") == "5"

    def test_multiplication(self):
        assert _calculator("6 * 7") == "42"

    def test_sqrt(self):
        assert _calculator("sqrt(144)") == "12.0"

    def test_complex_expression(self):
        result = float(_calculator("sqrt(9) + pow(2, 3)"))
        assert result == 11.0

    def test_pi(self):
        result = float(_calculator("pi"))
        assert abs(result - 3.14159) < 0.001

    def test_invalid_expression(self):
        result = _calculator("invalid")
        assert "error" in result.lower()

    def test_no_builtins_access(self):
        result = _calculator("__import__('os').system('ls')")
        assert "error" in result.lower()


class TestCurrentDatetime:
    def test_returns_iso_format(self):
        result = _current_datetime()
        assert "T" in result
        assert "+" in result or "Z" in result or result.endswith("+00:00")


class TestJsonFormatter:
    def test_format_valid_json(self):
        result = _json_formatter('{"a":1,"b":2}')
        parsed = json.loads(result)
        assert parsed == {"a": 1, "b": 2}
        assert "\n" in result  # indented

    def test_invalid_json(self):
        result = _json_formatter("not json")
        assert "Invalid JSON" in result


# ─── ToolExecutor ──────────────────────────────────────────


class TestToolExecutor:
    def test_register_and_execute(self):
        executor = ToolExecutor()
        tool_def = ToolDefinition(
            name="echo",
            description="Echo input",
            input_schema={"type": "object", "properties": {"text": {"type": "string"}}},
        )
        executor.register(tool_def, lambda text="": text)

        result = asyncio.run(executor.execute("echo", {"text": "hello"}, "id-1"))
        assert result.content == "hello"
        assert result.tool_use_id == "id-1"
        assert not result.is_error

    def test_unknown_tool(self):
        executor = ToolExecutor()
        result = asyncio.run(executor.execute("nonexistent", {}, "id-1"))
        assert result.is_error
        assert "Unknown tool" in result.content

    def test_tool_error(self):
        executor = ToolExecutor()
        tool_def = ToolDefinition(name="fail", description="Always fails")

        def fail_handler():
            raise ValueError("boom")

        executor.register(tool_def, fail_handler)
        result = asyncio.run(executor.execute("fail", {}, "id-1"))
        assert result.is_error
        assert "boom" in result.content

    def test_get_schemas(self):
        executor = create_default_tools()
        schemas = executor.get_schemas()
        assert len(schemas) == 3
        names = [s["name"] for s in schemas]
        assert "calculator" in names
        assert "current_datetime" in names
        assert "json_formatter" in names

    def test_tool_names(self):
        executor = create_default_tools()
        assert "calculator" in executor.tool_names
        assert len(executor) == 3

    def test_default_tools_work(self):
        executor = create_default_tools()
        result = asyncio.run(executor.execute("calculator", {"expression": "2+2"}, "id-1"))
        assert result.content == "4"

        result = asyncio.run(executor.execute("current_datetime", {}, "id-2"))
        assert "T" in result.content


# ─── Agent with Tools ──────────────────────────────────────


class TestAgentWithTools:
    @pytest.mark.asyncio
    async def test_agent_without_tools(self):
        """Agent without tools should work as before."""
        client = MagicMock()
        response = MagicMock()
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Analysis complete"
        response.content = [text_block]
        response.stop_reason = "end_turn"
        client.messages = MagicMock()
        client.messages.create = AsyncMock(return_value=response)

        agent = Agent(name="Test", role=AgentRole.RESEARCHER, client=client)
        subtask = SubTask(description="Analyze data")
        result, traces = await agent.execute(subtask)

        assert result == "Analysis complete"
        assert any(t.event_type == "AGENT_COMPLETED" for t in traces)

    @pytest.mark.asyncio
    async def test_agent_with_tool_call(self):
        """Agent should handle tool_use -> tool_result -> final text flow."""
        client = MagicMock()

        # First response: tool_use
        tool_use_block = MagicMock()
        tool_use_block.type = "tool_use"
        tool_use_block.name = "calculator"
        tool_use_block.input = {"expression": "sqrt(144)"}
        tool_use_block.id = "tool-id-1"

        first_response = MagicMock()
        first_response.content = [tool_use_block]
        first_response.stop_reason = "tool_use"

        # Second response: final text
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "The square root of 144 is 12.0"

        second_response = MagicMock()
        second_response.content = [text_block]
        second_response.stop_reason = "end_turn"

        client.messages = MagicMock()
        client.messages.create = AsyncMock(side_effect=[first_response, second_response])

        tools = create_default_tools()
        agent = Agent(name="Math", role=AgentRole.SPECIALIST, client=client, tools=tools)
        subtask = SubTask(description="Calculate sqrt of 144")
        result, traces = await agent.execute(subtask)

        assert result == "The square root of 144 is 12.0"
        assert client.messages.create.call_count == 2

        # Check tool call trace
        tool_traces = [t for t in traces if t.event_type == "TOOL_CALL"]
        assert len(tool_traces) == 1
        assert tool_traces[0].details["tool"] == "calculator"
        assert "12.0" in tool_traces[0].details["result"]

    @pytest.mark.asyncio
    async def test_agent_tool_rounds_in_trace(self):
        """AGENT_COMPLETED trace should include tool_rounds count."""
        client = MagicMock()

        # Direct text response (no tools)
        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Done"
        response = MagicMock()
        response.content = [text_block]
        response.stop_reason = "end_turn"
        client.messages = MagicMock()
        client.messages.create = AsyncMock(return_value=response)

        tools = create_default_tools()
        agent = Agent(name="Test", role=AgentRole.RESEARCHER, client=client, tools=tools)
        subtask = SubTask(description="Test")
        _, traces = await agent.execute(subtask)

        completed = [t for t in traces if t.event_type == "AGENT_COMPLETED"]
        assert len(completed) == 1
        assert completed[0].details["tool_rounds"] == 0

    @pytest.mark.asyncio
    async def test_agent_tools_passed_to_api(self):
        """When agent has tools, they should be passed in the API call."""
        client = MagicMock()

        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Result"
        response = MagicMock()
        response.content = [text_block]
        response.stop_reason = "end_turn"
        client.messages = MagicMock()
        client.messages.create = AsyncMock(return_value=response)

        tools = create_default_tools()
        agent = Agent(name="Test", role=AgentRole.RESEARCHER, client=client, tools=tools)
        subtask = SubTask(description="Test")
        await agent.execute(subtask)

        call_kwargs = client.messages.create.call_args.kwargs
        assert "tools" in call_kwargs
        assert len(call_kwargs["tools"]) == 3

    @pytest.mark.asyncio
    async def test_agent_no_tools_not_in_api(self):
        """When agent has no tools, 'tools' param should NOT be in API call."""
        client = MagicMock()

        text_block = MagicMock()
        text_block.type = "text"
        text_block.text = "Result"
        response = MagicMock()
        response.content = [text_block]
        response.stop_reason = "end_turn"
        client.messages = MagicMock()
        client.messages.create = AsyncMock(return_value=response)

        agent = Agent(name="Test", role=AgentRole.RESEARCHER, client=client)
        subtask = SubTask(description="Test")
        await agent.execute(subtask)

        call_kwargs = client.messages.create.call_args.kwargs
        assert "tools" not in call_kwargs


class TestDefaultAgentsHaveTools:
    def test_default_agents_get_tools(self):
        from kovrin.agents.base import create_default_agents

        agents = create_default_agents()
        for agent in agents:
            assert agent.tools is not None
            assert len(agent.tools) == 3
            assert "calculator" in agent.tools.tool_names
