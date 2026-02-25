"""
Orchestrator Agent — Opus-Powered Task Proposal Engine

Analyzes project state using Claude Opus and generates ranked
task proposals. Integrates with ContextInjector (RAG) and
MetricsTracker for informed decision-making.

Falls back gracefully when the Claude API is unavailable.
"""

from __future__ import annotations

import json
import logging
from typing import TYPE_CHECKING

from kovrin.core.models import RiskLevel
from kovrin.superwork.models import (
    ProjectAnalysis,
    TaskCompletionEvent,
    TaskProposal,
)

if TYPE_CHECKING:
    from kovrin.superwork.context_injector import ContextInjector
    from kovrin.superwork.metrics import MetricsTracker

logger = logging.getLogger(__name__)

ORCHESTRATOR_MODEL = "claude-opus-4-6"
ANALYSIS_MAX_TOKENS = 4096

SYSTEM_PROMPT = """\
You are the Kovrin SuperWork Orchestrator — an AI project manager.

Your role:
1. Analyze the current state of a software project based on recent task completions.
2. Identify the most impactful next steps.
3. Propose 3-5 concrete, actionable tasks ranked by priority.

Rules:
- Each task must be specific enough for an AI coding agent to execute independently.
- Estimate token cost (rough: 500-5000 tokens per task).
- Assign risk levels: LOW (refactoring, docs), MEDIUM (new features), \
HIGH (infrastructure, security), CRITICAL (never auto-execute).
- HIGH and CRITICAL risk tasks must NOT have auto_execute set to true.
- Include rationale for why each task matters NOW.
- Consider dependencies between proposed tasks.

Output ONLY a JSON object with this structure:
{
    "summary": "brief analysis of current state",
    "focus_area": "main focus area",
    "proposals": [
        {
            "title": "short title",
            "description": "detailed task description",
            "rationale": "why now",
            "risk_level": "LOW",
            "estimated_tokens": 1500,
            "auto_execute": false,
            "dependencies": [],
            "priority": 0
        }
    ]
}"""


class OrchestratorAgent:
    """Opus-powered project analysis and task proposal engine.

    Analyzes completed tasks, project context, and metrics to
    produce ranked task proposals for human approval.
    """

    def __init__(
        self,
        client=None,
        context_injector: ContextInjector | None = None,
        metrics_tracker: MetricsTracker | None = None,
        model: str = ORCHESTRATOR_MODEL,
    ):
        """Initialize Orchestrator Agent.

        Args:
            client: Anthropic async client. Created lazily if None.
            context_injector: Optional RAG context provider.
            metrics_tracker: Optional metrics source.
            model: Claude model to use for analysis.
        """
        self._client = client
        self._context_injector = context_injector
        self._metrics = metrics_tracker
        self._model = model
        self._task_history: list[TaskCompletionEvent] = []

    def _ensure_client(self):
        """Lazy-initialize the Anthropic client."""
        if self._client is None:
            import anthropic

            self._client = anthropic.AsyncAnthropic()

    def record_completion(self, event: TaskCompletionEvent) -> None:
        """Record a completed task for analysis context.

        Keeps the last 20 events for context window efficiency.

        Args:
            event: Task completion event from Session Watcher.
        """
        self._task_history.append(event)
        if len(self._task_history) > 20:
            self._task_history = self._task_history[-20:]

    async def analyze_and_propose(
        self,
        user_constraints: list[str] | None = None,
    ) -> ProjectAnalysis:
        """Analyze project state and generate task proposals.

        Returns ProjectAnalysis with ``status="api_unavailable"``
        if the Claude API cannot be reached.

        Args:
            user_constraints: Optional list of user-provided constraints.

        Returns:
            ProjectAnalysis with summary, focus area, and proposals.
        """
        self._ensure_client()

        user_message = self._build_context(user_constraints)

        try:
            response = await self._client.messages.create(
                model=self._model,
                max_tokens=ANALYSIS_MAX_TOKENS,
                system=SYSTEM_PROMPT,
                messages=[{"role": "user", "content": user_message}],
            )
            return self._parse_response(response.content[0].text)

        except Exception as e:
            error_type = type(e).__name__
            logger.warning("Orchestrator API error: %s: %s", error_type, e)
            return ProjectAnalysis(
                status="api_unavailable",
                summary=f"Claude API error ({error_type}). Retry later.",
            )

    def _build_context(self, user_constraints: list[str] | None = None) -> str:
        """Build the user message from available context sources."""
        parts: list[str] = []

        # Recent task history
        if self._task_history:
            history_lines = []
            for e in self._task_history[-10:]:
                line = f"- [{e.timestamp.isoformat()[:19]}] {e.completed_task[:100]}"
                if e.errors:
                    line += f" (ERRORS: {', '.join(e.errors[:3])})"
                history_lines.append(line)
            parts.append("RECENT TASK HISTORY:\n" + "\n".join(history_lines))

        # Project context from vector DB
        if self._context_injector:
            query = (
                self._task_history[-1].completed_task
                if self._task_history
                else "project overview, current state, TODO items"
            )
            relevant = self._context_injector.get_relevant_context(query, top_k=5)
            if relevant:
                parts.append(f"RELEVANT PROJECT CONTEXT:\n{relevant}")

        # Metrics
        if self._metrics:
            snap = self._metrics.snapshot()
            parts.append(
                f"METRICS: {snap.tasks_completed} completed, "
                f"{snap.tasks_failed} failed, "
                f"velocity={snap.velocity_tasks_per_hour:.1f}/hr, "
                f"cost=${snap.cost_usd:.2f}"
            )

        # User constraints
        if user_constraints:
            constraints_text = "\n".join(f"- {c}" for c in user_constraints)
            parts.append(f"USER CONSTRAINTS:\n{constraints_text}")

        return "\n\n".join(parts) or "No prior context. Analyze the project from scratch."

    def _parse_response(self, text: str) -> ProjectAnalysis:
        """Parse Opus response into structured ProjectAnalysis.

        Handles both clean JSON and markdown-fenced JSON responses.
        """
        try:
            cleaned = text.strip()
            # Strip markdown code fences (may have preamble text before ```)
            if "```" in cleaned:
                import re

                match = re.search(r"```(?:json)?\s*\n(.*?)```", cleaned, re.DOTALL)
                if match:
                    cleaned = match.group(1).strip()

            data = json.loads(cleaned)
            proposals = [
                TaskProposal(
                    title=p["title"],
                    description=p["description"],
                    rationale=p.get("rationale", ""),
                    risk_level=p.get("risk_level", "LOW"),
                    estimated_tokens=p.get("estimated_tokens", 1500),
                    auto_execute=p.get("auto_execute", False),
                    dependencies=p.get("dependencies", []),
                    priority=p.get("priority", i),
                )
                for i, p in enumerate(data.get("proposals", []))
            ]

            # Safety: never auto_execute HIGH or CRITICAL
            for prop in proposals:
                if prop.risk_level in (RiskLevel.HIGH, RiskLevel.CRITICAL):
                    prop.auto_execute = False

            return ProjectAnalysis(
                summary=data.get("summary", ""),
                focus_area=data.get("focus_area", ""),
                proposals=proposals,
                total_tasks_completed=(self._metrics.tasks_completed if self._metrics else 0),
                total_tasks_failed=(self._metrics.tasks_failed if self._metrics else 0),
                velocity_tasks_per_hour=(self._metrics.velocity if self._metrics else 0.0),
            )
        except (json.JSONDecodeError, KeyError, TypeError) as e:
            logger.warning("Failed to parse orchestrator response: %s", e)
            return ProjectAnalysis(
                summary=text[:500],
                status="parse_error",
            )
