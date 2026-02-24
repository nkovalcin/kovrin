"""DateTime tool — current date/time in UTC."""

from datetime import datetime, timezone

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool


def _current_datetime() -> str:
    """Return the current date and time in ISO format."""
    return datetime.now(timezone.utc).isoformat()


DATETIME_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="current_datetime",
        description="Get the current date and time in UTC ISO format.",
        input_schema={
            "type": "object",
            "properties": {},
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.LOW,
        speculation_tier=SpeculationTier.FREE,
        category=ToolCategory.READ_ONLY,
        scope_tags=["read_only"],
        max_calls_per_task=20,
    ),
    handler=_current_datetime,
)
