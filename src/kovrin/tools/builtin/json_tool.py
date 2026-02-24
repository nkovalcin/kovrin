"""JSON formatter tool — pretty-print JSON strings."""

import json

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool


def _json_formatter(data: str) -> str:
    """Format a JSON string with indentation."""
    try:
        parsed = json.loads(data)
        return json.dumps(parsed, indent=2, ensure_ascii=False)
    except json.JSONDecodeError as e:
        return f"Invalid JSON: {e}"


JSON_TOOL = RegisteredTool(
    definition=ToolDefinition(
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
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        category=ToolCategory.COMPUTATION,
        scope_tags=["computation", "read_only"],
        max_calls_per_task=20,
    ),
    handler=_json_formatter,
)
