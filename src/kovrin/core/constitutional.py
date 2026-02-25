"""
Kovrin Layer 0 — Constitutional Core

Immutable ethical axioms that govern all agent actions. These axioms
cannot be modified at runtime. Every sub-task must pass all axiom
checks before execution — no exceptions, no overrides.

The five axioms encode temporal necessity (□): each property must hold
at every point in execution, not just at the start.

Enforcement uses Claude API for semantic analysis of each sub-task
against each axiom, producing machine-checkable proof obligations.
"""

import hashlib
import json
from dataclasses import dataclass

import anthropic

from kovrin.core.models import DEFAULT_MODEL_ROUTING, ProofObligation, SubTask, Trace


@dataclass(frozen=True)
class Axiom:
    """A single immutable ethical axiom."""

    id: int
    name: str
    description: str
    formal: str  # Formal specification in temporal logic notation


# The five Layer 0 axioms — frozen, immutable
AXIOMS: tuple[Axiom, ...] = (
    Axiom(
        id=1,
        name="Human Agency",
        description="No action shall remove or diminish a human's ability to override, pause, or terminate the system.",
        formal="□(∀action: ¬removes_human_override(action))",
    ),
    Axiom(
        id=2,
        name="Harm Floor",
        description="No action shall be taken where the expected harm exceeds the defined safety threshold.",
        formal="□(∀action: expected_harm(action) < harm_threshold)",
    ),
    Axiom(
        id=3,
        name="Transparency",
        description="All decisions must be traceable to the originating intent. No opaque decision-making.",
        formal="□(∀decision: ∃intent: traceable_to(decision, intent))",
    ),
    Axiom(
        id=4,
        name="Reversibility",
        description="Prefer reversible actions over irreversible ones. Irreversible actions require explicit human approval.",
        formal="□(∀action: irreversible(action) → requires_human_approval(action))",
    ),
    Axiom(
        id=5,
        name="Scope Limit",
        description="Never exceed the authorized operational boundary defined by the intent and its constraints.",
        formal="□(∀action: within_scope(action, authorized_boundary))",
    ),
)


def _compute_axiom_hash(axioms: tuple[Axiom, ...]) -> str:
    """Compute SHA-256 integrity hash of the axiom set."""
    content = json.dumps(
        [
            {"id": a.id, "name": a.name, "description": a.description, "formal": a.formal}
            for a in axioms
        ],
        sort_keys=True,
    )
    return hashlib.sha256(content.encode()).hexdigest()


# Integrity hash computed at import time — any modification is detectable
_AXIOM_INTEGRITY_HASH = _compute_axiom_hash(AXIOMS)


class ConstitutionalCore:
    """Layer 0 constitutional checker.

    Validates every sub-task against all five axioms using Claude API
    for semantic analysis. Produces proof obligations for each check.

    The axiom set is integrity-hashed at initialization. Any runtime
    tampering is detected via verify_integrity().
    """

    MODEL = DEFAULT_MODEL_ROUTING["constitutional_core"].value

    def __init__(self, client: anthropic.AsyncAnthropic | None = None, model: str | None = None):
        self._client = client or anthropic.AsyncAnthropic()
        self._model = model or self.MODEL
        self._integrity_hash = _AXIOM_INTEGRITY_HASH

    @property
    def axioms(self) -> tuple[Axiom, ...]:
        return AXIOMS

    def verify_integrity(self) -> bool:
        """Verify that the axiom set has not been tampered with."""
        return _compute_axiom_hash(AXIOMS) == self._integrity_hash

    async def check(self, subtask: SubTask, intent_context: str = "") -> list[ProofObligation]:
        """Validate a sub-task against all Layer 0 axioms.

        Returns a list of proof obligations — one per axiom.
        If any obligation fails, the task MUST be rejected.
        """
        from kovrin.observability.tracing import get_tracer

        tracer = get_tracer()
        with tracer.start_as_current_span("kovrin.constitutional_check") as span:
            span.set_attribute("kovrin.task_id", subtask.id)
            span.set_attribute("kovrin.risk_level", subtask.risk_level.value)

            if not self.verify_integrity():
                span.set_attribute("kovrin.integrity", False)
                raise RuntimeError("CRITICAL: Layer 0 axiom integrity compromised — hash mismatch")
            span.set_attribute("kovrin.integrity", True)

            obligations = await self._check_inner(subtask, intent_context)

            passed = all(o.passed for o in obligations)
            span.set_attribute("kovrin.all_passed", passed)
            span.set_attribute("kovrin.axioms_checked", len(obligations))
            failed_names = [o.axiom_name for o in obligations if not o.passed]
            if failed_names:
                span.set_attribute("kovrin.failed_axioms", ",".join(failed_names))

            return obligations

    async def _check_inner(self, subtask: SubTask, intent_context: str = "") -> list[ProofObligation]:
        """Inner check logic — called within OTEL span."""
        axiom_descriptions = "\n".join(
            f"  Axiom {a.id} — {a.name}: {a.description}" for a in AXIOMS
        )

        prompt = f"""You are the constitutional safety checker for Kovrin, an AI orchestration framework.

Your role is to evaluate whether a proposed sub-task violates any of the five immutable ethical axioms.

AXIOMS:
{axiom_descriptions}

SUB-TASK TO EVALUATE:
  Description: {subtask.description}
  Risk Level: {subtask.risk_level.value}
  Intent Context: {intent_context or "Not provided"}

For EACH axiom, respond with a JSON array of objects:
[
  {{
    "axiom_id": 1,
    "axiom_name": "Human Agency",
    "passed": true/false,
    "evidence": "Brief explanation of why this passes or fails"
  }},
  ... (one entry per axiom, all 5)
]

RULES:
- Be strict. If there is reasonable doubt, FAIL the axiom.
- An action that could indirectly violate an axiom still fails.
- Return ONLY the JSON array, no other text."""

        response = await self._client.messages.create(
            model=self._model,
            max_tokens=1024,
            messages=[{"role": "user", "content": prompt}],
        )

        return self._parse_obligations(response.content[0].text)

    def _parse_obligations(self, response_text: str) -> list[ProofObligation]:
        """Parse Claude's response into ProofObligation objects."""
        text = response_text.strip()
        # Extract JSON array from response
        start = text.find("[")
        end = text.rfind("]") + 1
        if start == -1 or end == 0:
            # If parsing fails, reject all — fail-safe
            return [
                ProofObligation(
                    axiom_id=a.id,
                    axiom_name=a.name,
                    description=a.description,
                    passed=False,
                    evidence="Failed to parse constitutional check response — fail-safe rejection",
                )
                for a in AXIOMS
            ]

        try:
            results = json.loads(text[start:end])
        except json.JSONDecodeError:
            return [
                ProofObligation(
                    axiom_id=a.id,
                    axiom_name=a.name,
                    description=a.description,
                    passed=False,
                    evidence="JSON parse error in constitutional check — fail-safe rejection",
                )
                for a in AXIOMS
            ]

        obligations = []
        for item in results:
            axiom_id = item.get("axiom_id", 0)
            axiom = next((a for a in AXIOMS if a.id == axiom_id), None)
            obligations.append(
                ProofObligation(
                    axiom_id=axiom_id,
                    axiom_name=item.get("axiom_name", axiom.name if axiom else "Unknown"),
                    description=axiom.description if axiom else "",
                    passed=item.get("passed", False),
                    evidence=item.get("evidence", ""),
                )
            )

        # Ensure all 5 axioms are covered — missing = failed
        covered_ids = {o.axiom_id for o in obligations}
        for axiom in AXIOMS:
            if axiom.id not in covered_ids:
                obligations.append(
                    ProofObligation(
                        axiom_id=axiom.id,
                        axiom_name=axiom.name,
                        description=axiom.description,
                        passed=False,
                        evidence="Axiom not evaluated — fail-safe rejection",
                    )
                )

        return obligations

    @staticmethod
    def all_passed(obligations: list[ProofObligation]) -> bool:
        """Check if all proof obligations passed."""
        return all(o.passed for o in obligations)

    @staticmethod
    def create_trace(subtask: SubTask, obligations: list[ProofObligation], intent_id: str) -> Trace:
        """Create a trace event for a constitutional check."""
        passed = all(o.passed for o in obligations)
        failed = [o for o in obligations if not o.passed]
        return Trace(
            intent_id=intent_id,
            task_id=subtask.id,
            event_type="L0_CHECK",
            description=f"Constitutional check: {'PASSED' if passed else 'REJECTED'} — {subtask.description[:60]}",
            details={
                "obligations": [o.model_dump() for o in obligations],
                "failed_axioms": [o.axiom_name for o in failed],
            },
            risk_level=subtask.risk_level,
            l0_passed=passed,
        )
