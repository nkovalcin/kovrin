"""
Kovrin Built-in Tools

Production-ready tools with safety profiles that are registered
automatically when tools=True in the Kovrin constructor.
"""

from kovrin.tools.registry import ToolRegistry

from kovrin.tools.builtin.calculator import CALCULATOR_TOOL
from kovrin.tools.builtin.datetime_tool import DATETIME_TOOL
from kovrin.tools.builtin.json_tool import JSON_TOOL
from kovrin.tools.builtin.code_exec import CODE_EXEC_TOOL
from kovrin.tools.builtin.web_search import WEB_SEARCH_TOOL
from kovrin.tools.builtin.http_client import HTTP_CLIENT_TOOL
from kovrin.tools.builtin.file_ops import FILE_READ_TOOL, FILE_WRITE_TOOL

ALL_BUILTIN_TOOLS = [
    CALCULATOR_TOOL,
    DATETIME_TOOL,
    JSON_TOOL,
    CODE_EXEC_TOOL,
    WEB_SEARCH_TOOL,
    HTTP_CLIENT_TOOL,
    FILE_READ_TOOL,
    FILE_WRITE_TOOL,
]


def register_all_builtins(registry: ToolRegistry) -> None:
    """Register all built-in tools with the given registry."""
    for tool in ALL_BUILTIN_TOOLS:
        registry.register(tool)
