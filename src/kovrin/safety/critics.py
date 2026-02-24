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
from kovrin.core.models import ProofObligation, RiskLevel, SubTask, Trace


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

    MODEL = "claude-sonnet-4-20250514"

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
AVAILABLE TOOLS: The agent has access to the following tools: {tool_list}
These tools are safety-gated and will be executed in sandboxed environments.
The agent CAN use these tools to accomplish tasks that require them."""

        prompt = f"""You are a feasibility critic for an AI orchestration system.

Evaluate whether this sub-task is achievable by an AI agent (Claude API).

SUB-TASK: {subtask.description}
RISK LEVEL: {subtask.risk_level.value}
CONTEXT: {context or "None provided"}
{tools_section}

Consider:
1. Can an AI agent realistically complete this task?
2. Does it require external resources or APIs not available?
3. Is the scope well-defined enough to execute?
4. Are there technical blockers?
5. If the agent has tools available, consider whether those tools enable the task.

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

    MODEL = "claude-sonnet-4-20250514"

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
    def create_trace(subtask: SubTask, passed: bool, obligations: list[ProofObligation], intent_id: str) -> Trace:
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
