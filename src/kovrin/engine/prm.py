"""
Kovrin Process Reward Model (PRM)

Step-level evaluation of task outputs. Unlike the ConfidenceEstimator
(task-level), the PRM breaks output into reasoning steps and scores
each one individually.

Features:
- Claude-based step decomposition and scoring
- Weighted aggregation (later steps weighted higher)
- Configurable threshold for flagging low-quality outputs
- Trace event generation for the audit log
"""

import json

import anthropic

from kovrin.core.models import PrmScore, PrmStepScore, SubTask, Trace


_PRM_PROMPT = """You are a Process Reward Model evaluating the quality of each reasoning step in an AI-generated output.

TASK DESCRIPTION: {task_description}

INTENT CONTEXT: {intent_context}

OUTPUT TO EVALUATE:
{output}

Break the output into logical reasoning steps and score each step from 0.0 to 1.0:
- 1.0 = perfectly correct, well-reasoned, directly contributes to the task
- 0.7 = good, minor issues
- 0.4 = mediocre, partially correct
- 0.2 = poor, mostly wrong or irrelevant
- 0.0 = completely wrong or harmful

Respond with ONLY valid JSON (no markdown, no code fences):
{{
  "steps": [
    {{"step_index": 0, "description": "brief description of the step", "score": 0.8, "reasoning": "why this score"}},
    ...
  ],
  "overall_reasoning": "brief summary of overall quality"
}}"""


class ProcessRewardModel:
    """Evaluates task outputs at the step level using Claude API."""

    MODEL = "claude-sonnet-4-20250514"

    def __init__(
        self,
        client: anthropic.AsyncAnthropic,
        threshold: float = 0.6,
    ):
        self._client = client
        self._threshold = threshold

    @property
    def threshold(self) -> float:
        return self._threshold

    async def evaluate(
        self,
        subtask: SubTask,
        output: str,
        intent_context: str = "",
    ) -> PrmScore:
        """Evaluate a task output and return step-level scores.

        Args:
            subtask: The task that produced the output.
            output: The raw output text to evaluate.
            intent_context: The original user intent for context.

        Returns:
            PrmScore with per-step scores and weighted aggregate.
        """
        prompt = _PRM_PROMPT.format(
            task_description=subtask.description,
            intent_context=intent_context or "Not provided",
            output=output[:4000],  # Limit to avoid token overflow
        )

        try:
            response = await self._client.messages.create(
                model=self.MODEL,
                max_tokens=2048,
                messages=[{"role": "user", "content": prompt}],
            )
            raw = response.content[0].text.strip()
            return self._parse_response(raw, subtask.id)
        except Exception:
            # API failure → conservative default
            return PrmScore(
                task_id=subtask.id,
                aggregate_score=0.5,
                reasoning="PRM evaluation failed — using default score",
            )

    def _parse_response(self, raw: str, task_id: str) -> PrmScore:
        """Parse Claude's JSON response into a PrmScore."""
        try:
            data = json.loads(raw)
        except json.JSONDecodeError:
            return PrmScore(
                task_id=task_id,
                aggregate_score=0.5,
                reasoning=f"Failed to parse PRM response: {raw[:200]}",
            )

        step_scores: list[PrmStepScore] = []
        for step in data.get("steps", []):
            step_scores.append(PrmStepScore(
                step_index=step.get("step_index", len(step_scores)),
                description=step.get("description", ""),
                score=max(0.0, min(1.0, float(step.get("score", 0.5)))),
                reasoning=step.get("reasoning", ""),
            ))

        aggregate = self._weighted_aggregate(step_scores)
        overall_reasoning = data.get("overall_reasoning", "")

        return PrmScore(
            task_id=task_id,
            step_scores=step_scores,
            aggregate_score=aggregate,
            reasoning=overall_reasoning,
        )

    @staticmethod
    def _weighted_aggregate(steps: list[PrmStepScore]) -> float:
        """Compute weighted mean — later steps have higher weight.

        Weight = 1 + (step_index / total_steps) so last step has ~2x weight.
        """
        if not steps:
            return 0.5

        total_weight = 0.0
        weighted_sum = 0.0
        n = len(steps)

        for step in steps:
            weight = 1.0 + (step.step_index / n)
            weighted_sum += step.score * weight
            total_weight += weight

        return round(weighted_sum / total_weight, 4) if total_weight > 0 else 0.5

    def is_below_threshold(self, score: PrmScore) -> bool:
        """Check if a score falls below the quality threshold."""
        return score.aggregate_score < self._threshold

    @staticmethod
    def create_trace(subtask: SubTask, score: PrmScore, intent_id: str) -> Trace:
        """Create a PRM_EVALUATION trace event."""
        return Trace(
            intent_id=intent_id,
            task_id=subtask.id,
            event_type="PRM_EVALUATION",
            description=f"PRM score={score.aggregate_score:.2f} ({len(score.step_scores)} steps): {subtask.description[:50]}",
            details={
                "aggregate_score": score.aggregate_score,
                "step_count": len(score.step_scores),
                "step_scores": [s.score for s in score.step_scores],
                "reasoning": score.reasoning[:200],
            },
            risk_level=subtask.risk_level,
        )
