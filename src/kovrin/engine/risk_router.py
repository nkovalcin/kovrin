"""
Kovrin Risk-Based Router

Routes sub-tasks based on their risk level and speculation tier.
Determines whether a task should be auto-executed, sandboxed for
review, or require human approval.

Routing matrix:
  LOW  + FREE    -> AUTO_EXECUTE
  LOW  + GUARDED -> AUTO_EXECUTE (with logging)
  MED  + FREE    -> AUTO_EXECUTE
  MED  + GUARDED -> SANDBOX_REVIEW
  MED  + NONE    -> HUMAN_APPROVAL
  HIGH + any     -> HUMAN_APPROVAL
  CRIT + any     -> HUMAN_APPROVAL
"""

from __future__ import annotations

import asyncio
from collections.abc import Callable

from kovrin.core.models import (
    ApprovalRequest,
    AutonomyProfile,
    AutonomySettings,
    RiskLevel,
    RoutingAction,
    RoutingDecision,
    SpeculationTier,
    SubTask,
    Trace,
)


class RiskRouter:
    """Routes sub-tasks based on risk level and speculation tier."""

    # Routing matrix: (risk_level, speculation_tier) -> action
    _MATRIX: dict[tuple[RiskLevel, SpeculationTier], RoutingAction] = {
        (RiskLevel.LOW, SpeculationTier.FREE): RoutingAction.AUTO_EXECUTE,
        (RiskLevel.LOW, SpeculationTier.GUARDED): RoutingAction.AUTO_EXECUTE,
        (RiskLevel.LOW, SpeculationTier.NONE): RoutingAction.SANDBOX_REVIEW,
        (RiskLevel.MEDIUM, SpeculationTier.FREE): RoutingAction.AUTO_EXECUTE,
        (RiskLevel.MEDIUM, SpeculationTier.GUARDED): RoutingAction.SANDBOX_REVIEW,
        (RiskLevel.MEDIUM, SpeculationTier.NONE): RoutingAction.HUMAN_APPROVAL,
        (RiskLevel.HIGH, SpeculationTier.FREE): RoutingAction.SANDBOX_REVIEW,
        (RiskLevel.HIGH, SpeculationTier.GUARDED): RoutingAction.HUMAN_APPROVAL,
        (RiskLevel.HIGH, SpeculationTier.NONE): RoutingAction.HUMAN_APPROVAL,
        (RiskLevel.CRITICAL, SpeculationTier.FREE): RoutingAction.HUMAN_APPROVAL,
        (RiskLevel.CRITICAL, SpeculationTier.GUARDED): RoutingAction.HUMAN_APPROVAL,
        (RiskLevel.CRITICAL, SpeculationTier.NONE): RoutingAction.HUMAN_APPROVAL,
    }

    # Autonomy profile overrides (Phase 5)
    _PROFILE_OVERRIDES: dict[
        AutonomyProfile, dict[tuple[RiskLevel, SpeculationTier], RoutingAction]
    ] = {
        AutonomyProfile.DEFAULT: {},
        AutonomyProfile.CAUTIOUS: {
            (RiskLevel.HIGH, SpeculationTier.FREE): RoutingAction.HUMAN_APPROVAL,
            (RiskLevel.MEDIUM, SpeculationTier.GUARDED): RoutingAction.HUMAN_APPROVAL,
            (RiskLevel.MEDIUM, SpeculationTier.FREE): RoutingAction.SANDBOX_REVIEW,
        },
        AutonomyProfile.AGGRESSIVE: {
            (RiskLevel.HIGH, SpeculationTier.FREE): RoutingAction.AUTO_EXECUTE,
            (RiskLevel.HIGH, SpeculationTier.GUARDED): RoutingAction.SANDBOX_REVIEW,
            (RiskLevel.MEDIUM, SpeculationTier.NONE): RoutingAction.SANDBOX_REVIEW,
            (RiskLevel.LOW, SpeculationTier.NONE): RoutingAction.AUTO_EXECUTE,
        },
        AutonomyProfile.LOCKED: {
            (risk, tier): RoutingAction.HUMAN_APPROVAL
            for risk in RiskLevel
            for tier in SpeculationTier
        },
    }

    def route(self, subtask: SubTask, settings: AutonomySettings | None = None) -> RoutingDecision:
        """Determine the routing action for a sub-task.

        Args:
            subtask: The task to route.
            settings: Optional autonomy settings for runtime overrides.
                      If None, uses the hardcoded routing matrix.
        """
        key = (subtask.risk_level, subtask.speculation_tier)
        action = self._MATRIX.get(key, RoutingAction.HUMAN_APPROVAL)

        if settings and settings.profile != AutonomyProfile.DEFAULT:
            # Apply profile overrides
            profile_overrides = self._PROFILE_OVERRIDES.get(settings.profile, {})
            if key in profile_overrides:
                action = profile_overrides[key]

            # Apply cell-level overrides (highest priority)
            cell_key = f"{subtask.risk_level.value}:{subtask.speculation_tier.value}"
            if cell_key in settings.override_matrix:
                try:
                    action = RoutingAction(settings.override_matrix[cell_key])
                except ValueError:
                    pass  # Invalid action string — keep previous

        # Safety guard: CRITICAL always requires human approval
        if subtask.risk_level == RiskLevel.CRITICAL:
            action = RoutingAction.HUMAN_APPROVAL

        reason = self._explain(subtask.risk_level, subtask.speculation_tier, action)

        return RoutingDecision(
            task_id=subtask.id,
            action=action,
            risk_level=subtask.risk_level,
            speculation_tier=subtask.speculation_tier,
            reason=reason,
        )

    def _explain(self, risk: RiskLevel, tier: SpeculationTier, action: RoutingAction) -> str:
        if action == RoutingAction.AUTO_EXECUTE:
            return f"Risk={risk.value}, Tier={tier.value} — safe for automatic execution"
        elif action == RoutingAction.SANDBOX_REVIEW:
            return f"Risk={risk.value}, Tier={tier.value} — requires sandbox review before commit"
        else:
            return f"Risk={risk.value}, Tier={tier.value} — requires human approval"

    async def request_human_approval(
        self,
        subtask: SubTask,
        decision: RoutingDecision,
        approval_callback: Callable[[ApprovalRequest], asyncio.Future[bool]] | None = None,
        timeout: float = 300.0,
    ) -> bool:
        """Request human approval.

        If approval_callback is provided (API mode), creates an ApprovalRequest,
        calls the callback which returns a Future, and awaits the Future with timeout.

        If no callback (CLI mode), falls back to stdin prompt.

        Args:
            subtask: The task requiring approval.
            decision: The routing decision.
            approval_callback: Async callback that accepts ApprovalRequest and returns Future[bool].
            timeout: Seconds to wait before auto-rejecting (default 300s).
        """
        import asyncio

        if approval_callback is not None:
            # API mode: async approval via callback
            request = ApprovalRequest(
                intent_id=subtask.parent_intent_id or "",
                task_id=subtask.id,
                description=subtask.description,
                risk_level=subtask.risk_level,
                speculation_tier=subtask.speculation_tier,
                proof_obligations=subtask.proof_obligations,
                reason=decision.reason,
            )
            try:
                result = approval_callback(request)
                # Handle both sync callbacks (returning Future) and async callbacks (returning coroutine)
                if asyncio.iscoroutine(result):
                    result = await result
                return await asyncio.wait_for(asyncio.ensure_future(result), timeout=timeout)
            except TimeoutError:
                return False

        # CLI mode: stdin prompt
        print(f"\n{'=' * 60}")
        print("HUMAN APPROVAL REQUIRED")
        print(f"{'=' * 60}")
        print(f"Task:   {subtask.description}")
        print(f"Risk:   {subtask.risk_level.value}")
        print(f"Tier:   {subtask.speculation_tier.value}")
        print(f"Reason: {decision.reason}")
        print(f"{'=' * 60}")

        try:
            response = input("Approve? [y/N]: ").strip().lower()
            return response in ("y", "yes")
        except (EOFError, KeyboardInterrupt):
            return False

    @staticmethod
    def create_trace(subtask: SubTask, decision: RoutingDecision, intent_id: str) -> Trace:
        """Create a trace event for a routing decision."""
        return Trace(
            intent_id=intent_id,
            task_id=subtask.id,
            event_type="RISK_ROUTING",
            description=f"Routed: {decision.action.value} — {subtask.description[:60]}",
            details={
                "action": decision.action.value,
                "risk_level": decision.risk_level.value,
                "speculation_tier": decision.speculation_tier.value,
                "reason": decision.reason,
            },
            risk_level=subtask.risk_level,
        )
