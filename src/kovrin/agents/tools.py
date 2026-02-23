"""
Kovrin Agent Tool System

Provides tool definitions and execution for agents that need to
interact with external functions (calculator, datetime, etc.).

Tools are defined using Claude API's tool_use format and executed
locally when the agent makes tool calls.
"""

import json
import math
from dataclasses import dataclass, field
from datetime import datetime, timezone
from typing import Any, Callable


@dataclass
class ToolDefinition:
    """A tool that can be used by agents."""
    name: str
    description: str
    input_schema: dict = field(default_factory=dict)


@dataclass
class ToolResult:
    """Result of executing a tool."""
    tool_use_id: str
    content: str
    is_error: bool = False


class ToolExecutor:
    """Manages tool registration and execution."""

    def __init__(self):
        self._tools: dict[str, ToolDefinition] = {}
        self._handlers: dict[str, Callable] = {}

    def register(self, tool_def: ToolDefinition, handler: Callable) -> None:
        """Register a tool with its handler function."""
        self._tools[tool_def.name] = tool_def
        self._handlers[tool_def.name] = handler

    async def execute(self, name: str, tool_input: dict, tool_use_id: str = "") -> ToolResult:
        """Execute a tool by name with given input."""
        handler = self._handlers.get(name)
        if not handler:
            return ToolResult(
                tool_use_id=tool_use_id,
                content=f"Unknown tool: {name}",
                is_error=True,
            )
        try:
            result = handler(**tool_input)
            return ToolResult(
                tool_use_id=tool_use_id,
                content=str(result),
            )
        except Exception as e:
            return ToolResult(
                tool_use_id=tool_use_id,
                content=f"Tool error: {str(e)}",
                is_error=True,
            )

    def get_schemas(self) -> list[dict]:
        """Get tool schemas for Claude API tools parameter."""
        return [
            {
                "name": t.name,
                "description": t.description,
                "input_schema": t.input_schema,
            }
            for t in self._tools.values()
        ]

    @property
    def tool_names(self) -> list[str]:
        return list(self._tools.keys())

    def __len__(self) -> int:
        return len(self._tools)


# ─── Built-in Tools ────────────────────────────────────────


def _calculator(expression: str) -> str:
    """Evaluate a mathematical expression safely."""
    allowed_names = {
        "abs": abs, "round": round, "min": min, "max": max,
        "sum": sum, "pow": pow, "len": len,
        "sqrt": math.sqrt, "log": math.log, "log10": math.log10,
        "sin": math.sin, "cos": math.cos, "tan": math.tan,
        "pi": math.pi, "e": math.e,
        "ceil": math.ceil, "floor": math.floor,
    }
    try:
        result = eval(expression, {"__builtins__": {}}, allowed_names)
        return str(result)
    except Exception as e:
        return f"Calculation error: {str(e)}"


def _current_datetime() -> str:
    """Return the current date and time in ISO format."""
    return datetime.now(timezone.utc).isoformat()


def _json_formatter(data: str) -> str:
    """Format a JSON string with indentation."""
    try:
        parsed = json.loads(data)
        return json.dumps(parsed, indent=2, ensure_ascii=False)
    except json.JSONDecodeError as e:
        return f"Invalid JSON: {str(e)}"


CALCULATOR_TOOL = ToolDefinition(
    name="calculator",
    description="Evaluate a mathematical expression. Supports basic arithmetic, sqrt, log, trig functions.",
    input_schema={
        "type": "object",
        "properties": {
            "expression": {
                "type": "string",
                "description": "The mathematical expression to evaluate (e.g., 'sqrt(144) + 2 * 3')",
            },
        },
        "required": ["expression"],
    },
)

CURRENT_DATETIME_TOOL = ToolDefinition(
    name="current_datetime",
    description="Get the current date and time in UTC ISO format.",
    input_schema={
        "type": "object",
        "properties": {},
    },
)

JSON_FORMATTER_TOOL = ToolDefinition(
    name="json_formatter",
    description="Format a JSON string with proper indentation.",
    input_schema={
        "type": "object",
        "properties": {
            "data": {
                "type": "string",
                "description": "The JSON string to format",
            },
        },
        "required": ["data"],
    },
)


def create_default_tools() -> ToolExecutor:
    """Create a ToolExecutor with the default built-in tools."""
    executor = ToolExecutor()
    executor.register(CALCULATOR_TOOL, _calculator)
    executor.register(CURRENT_DATETIME_TOOL, _current_datetime)
    executor.register(JSON_FORMATTER_TOOL, _json_formatter)
    return executor
