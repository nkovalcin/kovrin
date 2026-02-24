"""HTTP client tool — make HTTP API calls with domain restrictions.

Risk: MEDIUM — can interact with external services.
Tier: GUARDED — responses can be inspected before committing.
"""

from __future__ import annotations

import json
from urllib.request import urlopen, Request
from urllib.error import URLError, HTTPError

from kovrin.agents.tools import ToolDefinition
from kovrin.core.models import RiskLevel, SpeculationTier
from kovrin.tools.models import ToolCategory, ToolRiskProfile
from kovrin.tools.registry import RegisteredTool
from kovrin.tools.sandbox import SandboxedExecutor, SandboxConfig

_sandbox = SandboxedExecutor(SandboxConfig(
    timeout_seconds=15.0,
    network_allowed=True,
))


async def _http_request(
    url: str,
    method: str = "GET",
    headers: dict | None = None,
    body: str | None = None,
) -> str:
    """Make an HTTP request to the given URL.

    Uses urllib (no external dependencies). Supports GET and POST.
    Domain validation is handled by the SafeToolRouter, not here.
    """
    import asyncio

    def _do_request() -> str:
        req_headers = headers or {}
        req_headers.setdefault("User-Agent", "Kovrin/2.0 (AI Agent Orchestrator)")

        data = body.encode("utf-8") if body else None
        req = Request(url, data=data, headers=req_headers, method=method.upper())

        try:
            with urlopen(req, timeout=15) as resp:  # noqa: S310
                content = resp.read().decode("utf-8", errors="replace")
                status = resp.status
                # Truncate large responses
                if len(content) > 32768:
                    content = content[:32768] + "\n[TRUNCATED]"
                return f"HTTP {status}\n{content}"
        except HTTPError as e:
            body_text = e.read().decode("utf-8", errors="replace")[:2000]
            return f"HTTP {e.code}: {e.reason}\n{body_text}"
        except URLError as e:
            return f"Connection error: {e.reason}"
        except Exception as e:
            return f"Request failed: {type(e).__name__}: {e}"

    # Run in thread pool to avoid blocking the event loop
    return await asyncio.get_event_loop().run_in_executor(None, _do_request)


HTTP_CLIENT_TOOL = RegisteredTool(
    definition=ToolDefinition(
        name="http_request",
        description=(
            "Make HTTP requests to external APIs. Supports GET and POST methods. "
            "Use this to interact with REST APIs, fetch data from endpoints, "
            "or submit data to services."
        ),
        input_schema={
            "type": "object",
            "properties": {
                "url": {
                    "type": "string",
                    "description": "The URL to request",
                },
                "method": {
                    "type": "string",
                    "description": "HTTP method (GET or POST)",
                    "default": "GET",
                    "enum": ["GET", "POST"],
                },
                "headers": {
                    "type": "object",
                    "description": "Optional HTTP headers",
                },
                "body": {
                    "type": "string",
                    "description": "Optional request body (for POST)",
                },
            },
            "required": ["url"],
        },
    ),
    risk_profile=ToolRiskProfile(
        risk_level=RiskLevel.MEDIUM,
        speculation_tier=SpeculationTier.GUARDED,
        category=ToolCategory.NETWORK,
        scope_tags=["network"],
        max_calls_per_task=10,
    ),
    handler=_http_request,
)
