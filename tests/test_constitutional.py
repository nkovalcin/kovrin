"""Tests for LATTICE Layer 0 Constitutional Core."""

import json

import pytest

from kovrin.core.constitutional import (
    AXIOMS,
    ConstitutionalCore,
    _AXIOM_INTEGRITY_HASH,
    _compute_axiom_hash,
)
from kovrin.core.models import ProofObligation, RiskLevel, SubTask


class TestAxioms:
    def test_five_axioms_exist(self):
        assert len(AXIOMS) == 5

    def test_axiom_ids_sequential(self):
        ids = [a.id for a in AXIOMS]
        assert ids == [1, 2, 3, 4, 5]

    def test_axiom_names(self):
        names = [a.name for a in AXIOMS]
        assert "Human Agency" in names
        assert "Harm Floor" in names
        assert "Transparency" in names
        assert "Reversibility" in names
        assert "Scope Limit" in names

    def test_axioms_are_frozen(self):
        """Axioms should not be modifiable at runtime."""
        axiom = AXIOMS[0]
        with pytest.raises(AttributeError):
            axiom.name = "Modified"

    def test_axiom_tuple_is_immutable(self):
        """The axiom collection itself should be immutable."""
        with pytest.raises(TypeError):
            AXIOMS[0] = AXIOMS[1]


class TestIntegrityHash:
    def test_hash_is_consistent(self):
        """Same axioms should produce the same hash."""
        hash1 = _compute_axiom_hash(AXIOMS)
        hash2 = _compute_axiom_hash(AXIOMS)
        assert hash1 == hash2

    def test_hash_matches_stored(self):
        """The computed hash should match the import-time hash."""
        assert _compute_axiom_hash(AXIOMS) == _AXIOM_INTEGRITY_HASH

    def test_hash_is_sha256(self):
        """Hash should be a 64-character hex string (SHA-256)."""
        assert len(_AXIOM_INTEGRITY_HASH) == 64
        assert all(c in "0123456789abcdef" for c in _AXIOM_INTEGRITY_HASH)


class TestConstitutionalCore:
    def test_verify_integrity(self):
        core = ConstitutionalCore(client=None)
        assert core.verify_integrity() is True

    def test_axioms_property(self):
        core = ConstitutionalCore(client=None)
        assert len(core.axioms) == 5
        assert core.axioms is AXIOMS

    def test_all_passed_true(self):
        obligations = [
            ProofObligation(axiom_id=i, axiom_name=f"Axiom {i}", description="", passed=True)
            for i in range(1, 6)
        ]
        assert ConstitutionalCore.all_passed(obligations) is True

    def test_all_passed_false(self):
        obligations = [
            ProofObligation(axiom_id=1, axiom_name="Human Agency", description="", passed=True),
            ProofObligation(axiom_id=2, axiom_name="Harm Floor", description="", passed=False),
        ]
        assert ConstitutionalCore.all_passed(obligations) is False

    def test_create_trace_passed(self, low_risk_task):
        obligations = [
            ProofObligation(axiom_id=i, axiom_name=f"Axiom {i}", description="", passed=True)
            for i in range(1, 6)
        ]
        trace = ConstitutionalCore.create_trace(low_risk_task, obligations, "intent-1")
        assert "PASSED" in trace.description
        assert trace.l0_passed is True
        assert trace.event_type == "L0_CHECK"

    def test_create_trace_rejected(self, unsafe_task):
        obligations = [
            ProofObligation(axiom_id=1, axiom_name="Human Agency", description="", passed=False, evidence="Removes override"),
            ProofObligation(axiom_id=2, axiom_name="Harm Floor", description="", passed=False, evidence="High harm"),
        ]
        trace = ConstitutionalCore.create_trace(unsafe_task, obligations, "intent-1")
        assert "REJECTED" in trace.description
        assert trace.l0_passed is False

    def test_parse_obligations_valid_json(self):
        core = ConstitutionalCore(client=None)
        valid_json = json.dumps([
            {"axiom_id": i, "axiom_name": AXIOMS[i-1].name, "passed": True, "evidence": "OK"}
            for i in range(1, 6)
        ])
        result = core._parse_obligations(valid_json)
        assert len(result) == 5
        assert all(o.passed for o in result)

    def test_parse_obligations_invalid_json_failsafe(self):
        """Invalid JSON should result in all-fail (fail-safe)."""
        core = ConstitutionalCore(client=None)
        result = core._parse_obligations("not valid json at all")
        assert len(result) == 5
        assert all(not o.passed for o in result)

    def test_parse_obligations_missing_axiom_fills_gap(self):
        """If only 3 axioms returned, missing 2 should auto-fail."""
        core = ConstitutionalCore(client=None)
        partial_json = json.dumps([
            {"axiom_id": 1, "axiom_name": "Human Agency", "passed": True, "evidence": "OK"},
            {"axiom_id": 2, "axiom_name": "Harm Floor", "passed": True, "evidence": "OK"},
            {"axiom_id": 3, "axiom_name": "Transparency", "passed": True, "evidence": "OK"},
        ])
        result = core._parse_obligations(partial_json)
        # 3 passed + 2 auto-failed
        passed = [o for o in result if o.passed]
        failed = [o for o in result if not o.passed]
        assert len(passed) == 3
        assert len(failed) == 2
