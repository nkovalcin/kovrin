"""
Kovrin LLM-Modulo Critics

Implements the LLM-Modulo verification pattern (Kambhampati et al., ICML 2024):
LLMs generate candidate plans while external critics validate them.

Three specialized critics:
1. SafetyCritic — validates Layer 0 compliance (delegates to ConstitutionalCore)
2. FeasibilityCritic — checks if the task is achievable given capabilities
3. PolicyCritic — validates organizational constraints from the intent

CriticPipeline orchestrates all three. If any critic rejects, the task
is not executed.
"""

import anthropic

from kovrin.core.constitutional import ConstitutionalCore
from kovrin.core.models import ProofObligation, SubTask, Trace


class SafetyCritic:
    """Validates sub-tasks against Layer 0 constitutional axioms.

    Delegates to ConstitutionalCore — the single source of truth
    for safety verification.
    """

    def __init__(self, constitutional_core: ConstitutionalCore):
        self._core = constitutional_core

    async def evaluate(self, subtask: SubTask, intent_context: str = "") -> list[ProofObligation]:
        return await self._core.check(subtask, intent_context)

    @staticmethod
    def passed(obligations: list[ProofObligation]) -> bool:
        return all(o.passed for o in obligations)


class FeasibilityCritic:
    """Evaluates whether a sub-task is actually achievable.

    Checks resource availability, capability matching, and
    technical feasibility using Claude API analysis.
    """

    MODEL = "claude-sonnet-4-6"

    def __init__(
        self,
        client: anthropic.AsyncAnthropic | None = None,
        available_tools: list[str] | None = None,
    ):
        self._client = client or anthropic.AsyncAnthropic()
        self._available_tools = available_tools or []

    async def evaluate(self, subtask: SubTask, context: dict | None = None) -> ProofObligation:
        tools_section = ""
        if self._available_tools:
            tool_list = ", ".join(self._available_tools)
            tools_section = f"""
AVAILABLE TOOLS: The agent has access to the following fully functional tools: {tool_list}

IMPORTANT TOOL CAPABILITIES:
- web_search: Can search the internet for ANY topic. Returns real search results with titles, URLs, and descriptions. This covers general web search, news, academic topics, and any publicly available information.
- http_request: Can make HTTP GET/POST requests to any public API endpoint.
- code_execution: Can execute Python code in a sandboxed environment.
- file_read / file_write: Can read and write files in a sandboxed filesystem.
- calculator: Can evaluate mathematical expressions.
- current_datetime: Can get the current date and time.
- json_formatter: Can format JSON data.

All tools are safety-gated, sandboxed, and fully operational. The agent CAN and WILL use these tools to accomplish tasks."""

        prompt = f"""You are a feasibility critic for an AI orchestration system.

Evaluate whether this sub-task is achievable by an AI agent with access to Claude API and the tools listed below.

SUB-TASK: {subtask.description}
RISK LEVEL: {subtask.risk_level.value}
CONTEXT: {context or "None provided"}
{tools_section}

EVALUATION RULES:
1. If the task can be accomplished using the available tools, it IS feasible. Mark it as feasible.
2. A task that says "search for X" is feasible if web_search is available — even if it mentions specific databases. The agent will use web_search to find information from any source.
3. Tasks involving analysis, summarization, ranking, evaluation, or writing are ALWAYS feasible — these are core AI capabilities.
4. Only reject a task if it requires capabilities that genuinely do not exist (e.g., physical actions, accessing private systems, real-time video processing).
5. When in doubt, mark as feasible. The safety pipeline has other guards (Constitutional Core, Risk Router) to catch truly dangerous tasks.

Respond with JSON:
{{
  "feasible": true/false,
  "reason": "Brief explanation"
}}

Return ONLY JSON, no other text."""

        response = await self._client.messages.create(
            model=self.MODEL,
            max_tokens=256,
            messages=[{"role": "user", "content": prompt}],
        )

        return self._parse(response.content[0].text)

    def _parse(self, text: str) -> ProofObligation:
        import json

        try:
            start = text.find("{")
            end = text.rfind("}") + 1
            data = json.loads(text[start:end])
            return ProofObligation(
                axiom_id=0,
                axiom_name="Feasibility",
                description="Task is achievable by AI agent",
                passed=data.get("feasible", False),
                evidence=data.get("reason", ""),
            )
        except (json.JSONDecodeError, ValueError):
            return ProofObligation(
                axiom_id=0,
                axiom_name="Feasibility",
                description="Task is achievable by AI agent",
                passed=False,
                evidence="Failed to parse feasibility check — fail-safe rejection",
            )


class PolicyCritic:
    """Validates sub-tasks against organizational constraints from the intent.

    Ensures that no sub-task violates the user-defined constraints
    (e.g., "Do not suggest layoffs", "Focus on operational costs only").
    """

    MODEL = "claude-sonnet-4-6"

    def __init__(self, client: anthropic.AsyncAnthropic | None = None):
        self._client = client or anthropic.AsyncAnthropic()

    async def evaluate(self, subtask: SubTask, constraints: list[str]) -> ProofObligation:
        if not constraints:
            return ProofObligation(
                axiom_id=0,
                axiom_name="Policy",
                description="No constraints to check",
                passed=True,
                evidence="No policy constraints defined — auto-pass",
            )

        constraint_list = "\n".join(f"  - {c}" for c in constraints)
        prompt = f"""You are a policy critic for an AI orchestration system.

Evaluate whether this sub-task violates ANY of the user-defined constraints.

SUB-TASK: {subtask.description}
RISK LEVEL: {subtask.risk_level.value}

CONSTRAINTS (must not be violated):
{constraint_list}

Respond with JSON:
{{
  "compliant": true/false,
  "violated_constraints": ["list of violated constraints, empty if compliant"],
  "reason": "Brief explanation"
}}

Return ONLY JSON, no other text."""

        response = await self._client.messages.create(
            model=self.MODEL,
            max_tokens=256,
            messages=[{"role": "user", "content": prompt}],
        )

        return self._parse(response.content[0].text)

    def _parse(self, text: str) -> ProofObligation:
        import json

        try:
            start = text.find("{")
            end = text.rfind("}") + 1
            data = json.loads(text[start:end])
            violated = data.get("violated_constraints", [])
            return ProofObligation(
                axiom_id=0,
                axiom_name="Policy",
                description="Task complies with user constraints",
                passed=data.get("compliant", False),
                evidence=data.get("reason", "") + (f" Violated: {violated}" if violated else ""),
            )
        except (json.JSONDecodeError, ValueError):
            return ProofObligation(
                axiom_id=0,
                axiom_name="Policy",
                description="Task complies with user constraints",
                passed=False,
                evidence="Failed to parse policy check — fail-safe rejection",
            )


class CriticPipeline:
    """Orchestrates all three critics for comprehensive validation.

    A sub-task must pass ALL critics to proceed to execution.
    Results are aggregated into proof obligations attached to the task.
    """

    def __init__(
        self,
        safety: SafetyCritic,
        feasibility: FeasibilityCritic,
        policy: PolicyCritic,
    ):
        self.safety = safety
        self.feasibility = feasibility
        self.policy = policy

    async def evaluate(
        self,
        subtask: SubTask,
        constraints: list[str],
        intent_context: str = "",
        task_context: dict | None = None,
    ) -> tuple[bool, list[ProofObligation]]:
        """Run all critics on a sub-task.

        Returns (all_passed, list_of_obligations).
        """
        # Run safety critic (most important — L0 axioms)
        safety_obligations = await self.safety.evaluate(subtask, intent_context)

        # Run feasibility and policy in parallel
        import asyncio

        feasibility_result, policy_result = await asyncio.gather(
            self.feasibility.evaluate(subtask, task_context),
            self.policy.evaluate(subtask, constraints),
        )

        all_obligations = safety_obligations + [feasibility_result, policy_result]
        all_passed = all(o.passed for o in all_obligations)

        return all_passed, all_obligations

    @staticmethod
    def create_trace(
        subtask: SubTask, passed: bool, obligations: list[ProofObligation], intent_id: str
    ) -> Trace:
        """Create a trace event for the critic pipeline evaluation."""
        failed = [o for o in obligations if not o.passed]
        return Trace(
            intent_id=intent_id,
            task_id=subtask.id,
            event_type="CRITIC_PIPELINE",
            description=f"Critics: {'PASSED' if passed else 'REJECTED'} — {subtask.description[:60]}",
            details={
                "obligations": [o.model_dump() for o in obligations],
                "failed": [{"name": o.axiom_name, "evidence": o.evidence} for o in failed],
            },
            risk_level=subtask.risk_level,
            l0_passed=passed,
        )
