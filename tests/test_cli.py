"""Tests for Kovrin CLI.

Tests the CLI commands using subprocess to avoid import side effects.
"""

import subprocess
import sys

import pytest


class TestCLIBasic:
    """Basic CLI invocation tests."""

    def test_version(self):
        """CLI should display version."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "--version"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        # argparse fallback uses --version
        assert "2.0.0-alpha" in result.stdout or "2.0.0-alpha" in result.stderr

    def test_no_command_shows_help(self):
        """CLI with no args should show help."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        # Should exit cleanly (argparse shows help and exits 0 or 2)
        assert result.returncode in (0, 2)

    def test_status_command(self):
        """Status command should show framework info."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "status"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert "Kovrin Framework Status" in result.stdout
        assert "2.0.0-alpha" in result.stdout
        assert "Dependencies" in result.stdout

    def test_verify_command(self):
        """Verify command should run without errors."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "verify"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert "Merkle Chain Verification" in result.stdout

    def test_audit_no_id(self):
        """Audit without intent_id should list pipelines."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "audit"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert "Recent Pipelines" in result.stdout or "No pipelines found" in result.stdout


class TestCLIImports:
    """Verify CLI module imports correctly."""

    def test_cli_importable(self):
        from kovrin.cli import cli
        assert callable(cli)

    def test_internal_functions_exist(self):
        from kovrin.cli import _run_pipeline, _audit, _verify, _serve, _status
        assert callable(_run_pipeline)
        assert callable(_audit)
        assert callable(_verify)
        assert callable(_serve)
        assert callable(_status)
