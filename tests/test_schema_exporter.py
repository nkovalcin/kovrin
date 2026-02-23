"""
Tests for LATTICE Schema Exporter.

Verifies JSON Schema generation, TypeScript generation, parity validation,
and CLI functionality.
"""

import json
import subprocess
import sys
import tempfile
from pathlib import Path

import pytest

from kovrin.schema.exporter import SchemaExporter


@pytest.fixture
def exporter():
    return SchemaExporter()


# ─── Model / Enum Registration ──────────────────────────────


class TestRegistration:
    """Verify all models and enums are registered."""

    def test_all_models_registered(self, exporter):
        """At least 25 models must be registered."""
        assert len(exporter.MODELS) >= 25

    def test_all_enums_registered(self, exporter):
        """At least 13 enums must be registered."""
        assert len(exporter.ENUMS) >= 13

    def test_no_duplicate_models(self, exporter):
        """No model should be registered twice."""
        names = [m.__name__ for m in exporter.MODELS]
        assert len(names) == len(set(names))

    def test_no_duplicate_enums(self, exporter):
        """No enum should be registered twice."""
        names = [e.__name__ for e in exporter.ENUMS]
        assert len(names) == len(set(names))

    def test_critical_models_present(self, exporter):
        """Key safety-critical models must be registered."""
        names = {m.__name__ for m in exporter.MODELS}
        required = {
            "SubTask", "Trace", "ExecutionResult", "WatchdogAlert",
            "ProofObligation", "ApprovalRequest", "DelegationToken",
            "IntentV2", "PrmScore", "AgentDriftMetrics",
        }
        missing = required - names
        assert not missing, f"Missing critical models: {missing}"

    def test_critical_enums_present(self, exporter):
        """Key enums must be registered."""
        names = {e.__name__ for e in exporter.ENUMS}
        required = {
            "RiskLevel", "TaskStatus", "SpeculationTier", "RoutingAction",
            "ContainmentLevel", "AgentRole", "DriftLevel",
        }
        missing = required - names
        assert not missing, f"Missing critical enums: {missing}"


# ─── JSON Schema ─────────────────────────────────────────────


class TestJsonSchema:
    """Verify JSON Schema export."""

    def test_all_models_produce_schema(self, exporter):
        """Every registered model must produce a valid JSON Schema."""
        schemas = exporter.export_json_schemas()
        assert len(schemas) == len(exporter.MODELS)

    def test_schema_has_properties(self, exporter):
        """Each schema must have a 'properties' key."""
        schemas = exporter.export_json_schemas()
        for name, schema in schemas.items():
            assert "properties" in schema, f"{name} schema missing 'properties'"

    def test_schema_is_serializable(self, exporter):
        """Every schema must be JSON-serializable."""
        schemas = exporter.export_json_schemas()
        for name, schema in schemas.items():
            try:
                json.dumps(schema)
            except (TypeError, ValueError) as e:
                pytest.fail(f"{name} schema not JSON-serializable: {e}")

    def test_write_json_schemas(self, exporter):
        """write_json_schemas creates individual .json files."""
        with tempfile.TemporaryDirectory() as tmpdir:
            exporter.write_json_schemas(tmpdir)
            files = list(Path(tmpdir).glob("*.json"))
            assert len(files) == len(exporter.MODELS)
            # Each file should be valid JSON
            for f in files:
                data = json.loads(f.read_text())
                assert "properties" in data


# ─── TypeScript ──────────────────────────────────────────────


class TestTypeScript:
    """Verify TypeScript generation."""

    def test_ts_contains_all_enums(self, exporter):
        """Generated TS must contain all enum types."""
        ts = exporter.export_typescript()
        for enum_cls in exporter.ENUMS:
            assert f"export type {enum_cls.__name__}" in ts, \
                f"Missing TS type for {enum_cls.__name__}"

    def test_ts_contains_all_interfaces(self, exporter):
        """Generated TS must contain all model interfaces."""
        ts = exporter.export_typescript()
        for model in exporter.MODELS:
            assert f"export interface {model.__name__}" in ts, \
                f"Missing TS interface for {model.__name__}"

    def test_ts_enum_values_match(self, exporter):
        """Enum values in TS must match Python."""
        ts = exporter.export_typescript()
        from kovrin.core.models import RiskLevel
        for member in RiskLevel:
            assert f"'{member.value}'" in ts

    def test_ts_write_file(self, exporter):
        """write_typescript creates a valid file."""
        with tempfile.NamedTemporaryFile(suffix=".ts", delete=False, mode="w") as f:
            path = f.name
        try:
            exporter.write_typescript(path)
            content = Path(path).read_text()
            assert "export type RiskLevel" in content
            assert "export interface SubTask" in content
        finally:
            Path(path).unlink()

    def test_ts_nullable_types(self, exporter):
        """Nullable fields should generate `| null` in TS."""
        ts = exporter.export_typescript()
        # SubTask.output is str | None
        assert "string | null" in ts

    def test_ts_array_types(self, exporter):
        """List fields should generate array types in TS."""
        ts = exporter.export_typescript()
        # SubTask.dependencies is list[str]
        assert "string[]" in ts


# ─── Parity Validation ──────────────────────────────────────


class TestParityValidation:
    """Verify drift detection between Python models and TS file."""

    def test_validates_against_existing_ts(self, exporter):
        """Validation against the hand-written TS file finds known discrepancies."""
        ts_path = Path(__file__).parent.parent / "dashboard" / "src" / "types" / "kovrin.ts"
        if not ts_path.exists():
            pytest.skip("Dashboard TS file not found")
        issues = exporter.validate_parity(str(ts_path))
        # We know there are discrepancies
        assert len(issues) > 0

    def test_validates_generated_ts_full_parity(self, exporter):
        """Validation against generated TS should have zero discrepancies."""
        with tempfile.NamedTemporaryFile(suffix=".ts", delete=False, mode="w") as f:
            path = f.name
        try:
            exporter.write_typescript(path)
            issues = exporter.validate_parity(path)
            assert issues == [], f"Generated TS has discrepancies: {issues}"
        finally:
            Path(path).unlink()

    def test_detects_missing_interface(self, exporter):
        """Parity check should detect a missing interface."""
        ts_content = "export type RiskLevel = 'LOW'\n"
        with tempfile.NamedTemporaryFile(suffix=".ts", delete=False, mode="w") as f:
            f.write(ts_content)
            path = f.name
        try:
            issues = exporter.validate_parity(path)
            missing = [i for i in issues if "MISSING_INTERFACE" in i]
            assert len(missing) > 0
        finally:
            Path(path).unlink()

    def test_detects_missing_field(self, exporter):
        """Parity check should detect a missing field in an interface."""
        # Write a SubTask with only 'id' field
        ts_content = (
            "export type RiskLevel = 'LOW'\n"
            "export interface SubTask {\n"
            "  id: string\n"
            "}\n"
        )
        with tempfile.NamedTemporaryFile(suffix=".ts", delete=False, mode="w") as f:
            f.write(ts_content)
            path = f.name
        try:
            issues = exporter.validate_parity(path)
            missing_fields = [i for i in issues if "MISSING_FIELD: SubTask." in i]
            assert len(missing_fields) > 0
        finally:
            Path(path).unlink()


# ─── CLI ─────────────────────────────────────────────────────


class TestCLI:
    """Test command-line interface."""

    def test_cli_list(self):
        """--list should output model and enum counts."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.schema.exporter", "--list"],
            capture_output=True, text=True,
        )
        assert "Models:" in result.stdout
        assert "Enums:" in result.stdout
        assert "Total:" in result.stdout

    def test_cli_json_schema(self):
        """--json-schema should create JSON files."""
        with tempfile.TemporaryDirectory() as tmpdir:
            result = subprocess.run(
                [sys.executable, "-m", "kovrin.schema.exporter", "--json-schema", tmpdir],
                capture_output=True, text=True,
            )
            assert result.returncode == 0
            files = list(Path(tmpdir).glob("*.json"))
            assert len(files) >= 25

    def test_cli_typescript(self):
        """--typescript should create a .ts file."""
        with tempfile.NamedTemporaryFile(suffix=".ts", delete=False) as f:
            path = f.name
        try:
            result = subprocess.run(
                [sys.executable, "-m", "kovrin.schema.exporter", "--typescript", path],
                capture_output=True, text=True,
            )
            assert result.returncode == 0
            assert Path(path).stat().st_size > 0
        finally:
            Path(path).unlink()

    def test_cli_validate_finds_issues(self):
        """--validate against hand-written TS exits with code 1."""
        ts_path = Path(__file__).parent.parent / "dashboard" / "src" / "types" / "kovrin.ts"
        if not ts_path.exists():
            pytest.skip("Dashboard TS file not found")
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.schema.exporter", "--validate", str(ts_path)],
            capture_output=True, text=True,
        )
        assert result.returncode == 1
        assert "discrepancies" in result.stdout
