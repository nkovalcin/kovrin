"""
Kovrin Confidence Estimation

Lightweight uncertainty quantification using Claude-based
confidence estimation. Avoids heavy ML dependencies (no MAPIE/sklearn).

Approach:
1. Ask Claude to estimate confidence in each output (0-1 scale)
2. Optionally calibrate against historical accuracy data
3. Provide calibrated confidence based on observed outcomes

This is a pragmatic approximation of conformal prediction:
- No formal coverage guarantees
- But cheap, fast, and requires no training data
- Historical calibration improves accuracy over time
"""

import json
from collections import deque

import anthropic

from kovrin.core.models import ConfidenceEstimate, SubTask


class ConfidenceEstimator:
    """Estimates confidence in task outputs via Claude API."""

    MODEL = "claude-sonnet-4-20250514"

    def __init__(
        self,
        client: anthropic.AsyncAnthropic,
        calibration_window: int = 100,
    ):
        self._client = client
        self._history: deque[tuple[float, bool]] = deque(maxlen=calibration_window)

    async def estimate(
        self,
        subtask: SubTask,
        output: str,
        intent_context: str = "",
    ) -> ConfidenceEstimate:
        """Estimate confidence in a task's output."""
        prompt = f"""Rate your confidence in this AI-generated output on a scale of 0.0 to 1.0.

TASK: {subtask.description}
CONTEXT: {intent_context[:200]}
OUTPUT (first 500 chars): {output[:500]}

Consider:
1. Is the output relevant to the task?
2. Is it complete and thorough?
3. Are there factual claims that might be incorrect?
4. Is the reasoning sound?

Respond with JSON:
{{"confidence": 0.85, "reasoning": "Brief explanation"}}

Return ONLY JSON."""

        try:
            response = await self._client.messages.create(
                model=self.MODEL,
                max_tokens=256,
                messages=[{"role": "user", "content": prompt}],
            )
            text = response.content[0].text.strip()
            start = text.find("{")
            end = text.rfind("}") + 1
            if start < 0 or end <= start:
                raise ValueError("No JSON found in response")
            data = json.loads(text[start:end])

            raw_confidence = max(0.0, min(1.0, float(data.get("confidence", 0.5))))
            reasoning = str(data.get("reasoning", ""))

            calibrated = self._calibrate(raw_confidence)

            return ConfidenceEstimate(
                task_id=subtask.id,
                confidence=calibrated,
                reasoning=reasoning,
                calibrated=len(self._history) > 10,
            )
        except Exception:
            return ConfidenceEstimate(
                task_id=subtask.id,
                confidence=0.5,
                reasoning="Confidence estimation failed — default to 0.5",
                calibrated=False,
            )

    def _calibrate(self, raw: float) -> float:
        """Apply Platt-style calibration using historical data."""
        if len(self._history) < 10:
            return raw

        nearby = [
            actual for est, actual in self._history
            if abs(est - raw) < 0.15
        ]
        if not nearby:
            return raw

        observed = sum(1 for a in nearby if a) / len(nearby)
        return round(0.7 * observed + 0.3 * raw, 4)

    def record_outcome(self, estimated: float, was_accurate: bool) -> None:
        """Record actual outcome for future calibration."""
        self._history.append((estimated, was_accurate))
