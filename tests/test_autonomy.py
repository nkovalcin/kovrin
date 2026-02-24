"""Tests for LATTICE Phase 5 — Autonomy Controls."""

from kovrin.core.models import (
    AutonomyProfile,
    AutonomySettings,
    RiskLevel,
    RoutingAction,
    SpeculationTier,
    SubTask,
    ViewMode,
)
from kovrin.engine.risk_router import RiskRouter

# ─── Model Tests ──────────────────────────────────────────


class TestPhase5Models:
    def test_view_mode_values(self):
        assert ViewMode.OPERATOR == "OPERATOR"
        assert ViewMode.ANALYST == "ANALYST"
        assert ViewMode.DEVELOPER == "DEVELOPER"

    def test_autonomy_profile_values(self):
        assert AutonomyProfile.DEFAULT == "DEFAULT"
        assert AutonomyProfile.CAUTIOUS == "CAUTIOUS"
        assert AutonomyProfile.AGGRESSIVE == "AGGRESSIVE"
        assert AutonomyProfile.LOCKED == "LOCKED"

    def test_autonomy_settings_defaults(self):
        settings = AutonomySettings()
        assert settings.profile == AutonomyProfile.DEFAULT
        assert settings.override_matrix == {}
        assert settings.updated_at is not None

    def test_autonomy_settings_with_overrides(self):
        settings = AutonomySettings(
            profile=AutonomyProfile.CAUTIOUS,
            override_matrix={"HIGH:FREE": "HUMAN_APPROVAL"},
        )
        assert settings.profile == AutonomyProfile.CAUTIOUS
        assert settings.override_matrix["HIGH:FREE"] == "HUMAN_APPROVAL"


# ─── Router Profile Override Tests ────────────────────────


class TestRouterAutonomyOverrides:
    def _task(
        self, risk: RiskLevel = RiskLevel.MEDIUM, tier: SpeculationTier = SpeculationTier.GUARDED
    ) -> SubTask:
        return SubTask(description="Test task", risk_level=risk, speculation_tier=tier)

    def test_default_profile_no_change(self):
        """DEFAULT profile should behave identically to no settings."""
        router = RiskRouter()
        task = self._task(RiskLevel.MEDIUM, SpeculationTier.GUARDED)
        without = router.route(task)
        with_default = router.route(task, AutonomySettings(profile=AutonomyProfile.DEFAULT))
        assert without.action == with_default.action

    def test_cautious_medium_guarded_becomes_human(self):
        """CAUTIOUS: MEDIUM/GUARDED should be upgraded to HUMAN_APPROVAL."""
        router = RiskRouter()
        task = self._task(RiskLevel.MEDIUM, SpeculationTier.GUARDED)
        # Without settings: SANDBOX_REVIEW
        assert router.route(task).action == RoutingAction.SANDBOX_REVIEW
        # With CAUTIOUS: HUMAN_APPROVAL
        settings = AutonomySettings(profile=AutonomyProfile.CAUTIOUS)
        assert router.route(task, settings).action == RoutingAction.HUMAN_APPROVAL

    def test_cautious_high_free_becomes_human(self):
        """CAUTIOUS: HIGH/FREE should be upgraded to HUMAN_APPROVAL."""
        router = RiskRouter()
        task = self._task(RiskLevel.HIGH, SpeculationTier.FREE)
        settings = AutonomySettings(profile=AutonomyProfile.CAUTIOUS)
        assert router.route(task, settings).action == RoutingAction.HUMAN_APPROVAL

    def test_aggressive_high_free_becomes_auto(self):
        """AGGRESSIVE: HIGH/FREE should be downgraded to AUTO_EXECUTE."""
        router = RiskRouter()
        task = self._task(RiskLevel.HIGH, SpeculationTier.FREE)
        settings = AutonomySettings(profile=AutonomyProfile.AGGRESSIVE)
        assert router.route(task, settings).action == RoutingAction.AUTO_EXECUTE

    def test_aggressive_medium_none_becomes_sandbox(self):
        """AGGRESSIVE: MEDIUM/NONE should be downgraded to SANDBOX_REVIEW."""
        router = RiskRouter()
        task = self._task(RiskLevel.MEDIUM, SpeculationTier.NONE)
        settings = AutonomySettings(profile=AutonomyProfile.AGGRESSIVE)
        assert router.route(task, settings).action == RoutingAction.SANDBOX_REVIEW

    def test_locked_all_human(self):
        """LOCKED: all combinations should require HUMAN_APPROVAL."""
        router = RiskRouter()
        settings = AutonomySettings(profile=AutonomyProfile.LOCKED)
        for risk in RiskLevel:
            for tier in SpeculationTier:
                task = self._task(risk, tier)
                assert router.route(task, settings).action == RoutingAction.HUMAN_APPROVAL, (
                    f"LOCKED should force HUMAN for {risk}/{tier}"
                )

    def test_critical_always_human_regardless_of_profile(self):
        """CRITICAL tasks always require HUMAN_APPROVAL — safety guard."""
        router = RiskRouter()
        task = self._task(RiskLevel.CRITICAL, SpeculationTier.FREE)
        for profile in AutonomyProfile:
            settings = AutonomySettings(profile=profile)
            assert router.route(task, settings).action == RoutingAction.HUMAN_APPROVAL, (
                f"CRITICAL should be HUMAN even with profile={profile}"
            )

    def test_cell_override_takes_precedence(self):
        """Cell-level override should override profile-level."""
        router = RiskRouter()
        settings = AutonomySettings(
            profile=AutonomyProfile.CAUTIOUS,
            override_matrix={"MEDIUM:FREE": "AUTO_EXECUTE"},
        )
        task = self._task(RiskLevel.MEDIUM, SpeculationTier.FREE)
        # CAUTIOUS wants SANDBOX_REVIEW for MEDIUM/FREE, but cell override says AUTO
        assert router.route(task, settings).action == RoutingAction.AUTO_EXECUTE

    def test_cell_override_cannot_override_critical(self):
        """Cell override on CRITICAL is ignored — safety guard."""
        router = RiskRouter()
        settings = AutonomySettings(
            profile=AutonomyProfile.DEFAULT,
            override_matrix={"CRITICAL:FREE": "AUTO_EXECUTE"},
        )
        task = self._task(RiskLevel.CRITICAL, SpeculationTier.FREE)
        assert router.route(task, settings).action == RoutingAction.HUMAN_APPROVAL

    def test_invalid_cell_override_ignored(self):
        """Invalid action string in cell override should be ignored."""
        router = RiskRouter()
        settings = AutonomySettings(
            override_matrix={"LOW:FREE": "INVALID_ACTION"},
        )
        task = self._task(RiskLevel.LOW, SpeculationTier.FREE)
        # Should fall back to default (AUTO_EXECUTE)
        assert router.route(task, settings).action == RoutingAction.AUTO_EXECUTE

    def test_no_settings_unchanged(self):
        """Calling route without settings produces same results as before Phase 5."""
        router = RiskRouter()
        # Check a few representative cells
        assert (
            router.route(self._task(RiskLevel.LOW, SpeculationTier.FREE)).action
            == RoutingAction.AUTO_EXECUTE
        )
        assert (
            router.route(self._task(RiskLevel.MEDIUM, SpeculationTier.GUARDED)).action
            == RoutingAction.SANDBOX_REVIEW
        )
        assert (
            router.route(self._task(RiskLevel.HIGH, SpeculationTier.NONE)).action
            == RoutingAction.HUMAN_APPROVAL
        )
