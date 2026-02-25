"""
Kovrin Intent Decomposition Engine

Decomposes high-level intents into executable sub-tasks using
HTN-inspired planning via Claude API.

Single-shot decomposition: Claude generates a candidate decomposition,
which is then parsed into structured SubTask objects. On parse failure,
gracefully falls back to a single-task decomposition.

Each sub-task includes:
- Description of the work
- Risk classification
- Speculation tier
- Dependencies on other sub-tasks

Note: Iterative LLM-Modulo refinement (critic feedback loop) is planned
for a future release.
"""

import json

import anthropic

from kovrin.core.models import RiskLevel, SpeculationTier, SubTask
from kovrin.intent.schema import IntentV2


class IntentParser:
    """Decomposes intents into sub-task graphs via Claude API."""

    MODEL = "claude-sonnet-4-6"

    def __init__(self, client: anthropic.AsyncAnthropic | None = None):
        self._client = client or anthropic.AsyncAnthropic()

    async def parse(self, intent: IntentV2) -> list[SubTask]:
        """Decompose an intent into a list of sub-tasks.

        Uses structured output parsing to extract sub-tasks
        with dependencies, risk levels, and speculation tiers.
        """
        constraints_text = (
            "\n".join(f"  - {c}" for c in intent.constraints) if intent.constraints else "  None"
        )
        context_text = (
            json.dumps(intent.context, indent=2, default=str) if intent.context else "  None"
        )

        prompt = f"""You are the intent decomposition engine for Kovrin, a safety-first AI orchestration framework.

Decompose this intent into a set of concrete, executable sub-tasks.

INTENT: {intent.description}

CONSTRAINTS (must not be violated by any sub-task):
{constraints_text}

CONTEXT:
{context_text}

RULES:
1. Each sub-task must be specific and independently executable by an AI agent.
2. Assign a RISK LEVEL to each: LOW (read-only, analysis), MEDIUM (generates content, modifies state), HIGH (external actions, irreversible), CRITICAL (security-sensitive, financial).
3. Assign a SPECULATION TIER: FREE (idempotent, safe to parallelize), GUARDED (reversible, needs sandbox), NONE (irreversible, needs human approval).
4. Define dependencies between tasks using task IDs (task_0, task_1, etc.).
5. Minimize the number of tasks — avoid unnecessary decomposition.
6. Tasks should respect ALL constraints.

Respond with a JSON array:
[
  {{
    "id": "task_0",
    "description": "Clear description of what this task does",
    "risk_level": "LOW|MEDIUM|HIGH|CRITICAL",
    "speculation_tier": "FREE|GUARDED|NONE",
    "dependencies": []
  }},
  {{
    "id": "task_1",
    "description": "...",
    "risk_level": "LOW",
    "speculation_tier": "FREE",
    "dependencies": ["task_0"]
  }}
]

Return ONLY the JSON array, no other text."""

        response = await self._client.messages.create(
            model=self.MODEL,
            max_tokens=2048,
            messages=[{"role": "user", "content": prompt}],
        )

        return self._parse_response(response.content[0].text, intent.id)

    def _parse_response(self, text: str, intent_id: str) -> list[SubTask]:
        """Parse Claude's response into SubTask objects."""
        text = text.strip()
        start = text.find("[")
        end = text.rfind("]") + 1

        if start == -1 or end == 0:
            # Fallback: create a single task from the entire intent
            return [
                SubTask(
                    description="Execute the intent as a single task (decomposition failed)",
                    risk_level=RiskLevel.MEDIUM,
                    parent_intent_id=intent_id,
                )
            ]

        try:
            tasks_data = json.loads(text[start:end])
        except json.JSONDecodeError:
            return [
                SubTask(
                    description="Execute the intent as a single task (JSON parse failed)",
                    risk_level=RiskLevel.MEDIUM,
                    parent_intent_id=intent_id,
                )
            ]

        subtasks = []
        for item in tasks_data:
            risk = RiskLevel.LOW
            try:
                risk = RiskLevel(item.get("risk_level", "LOW"))
            except ValueError:
                pass

            tier = SpeculationTier.FREE
            try:
                tier = SpeculationTier(item.get("speculation_tier", "FREE"))
            except ValueError:
                pass

            subtasks.append(
                SubTask(
                    id=item.get("id", f"task_{len(subtasks)}"),
                    description=item.get("description", "Unknown task"),
                    risk_level=risk,
                    speculation_tier=tier,
                    dependencies=item.get("dependencies", []),
                    parent_intent_id=intent_id,
                )
            )

        return subtasks
