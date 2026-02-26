"""Tests for Kovrin CLI.

Tests the CLI commands using subprocess to avoid import side effects.
"""

import subprocess
import sys


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
        assert "2.0.0a1" in result.stdout or "2.0.0a1" in result.stderr

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
        assert "2.0.0a1" in result.stdout
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


    def test_help_flag(self):
        """--help should show usage info."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0
        assert "usage" in result.stdout.lower() or "kovrin" in result.stdout.lower()

    def test_run_subcommand_help(self):
        """run --help should show run-specific options."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "run", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0
        assert "intent" in result.stdout.lower() or "run" in result.stdout.lower()

    def test_serve_subcommand_help(self):
        """serve --help should show serve-specific options."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "serve", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0
        assert "port" in result.stdout.lower() or "serve" in result.stdout.lower()

    def test_invalid_subcommand(self):
        """Invalid subcommand should fail."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "nonexistent"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode != 0

    def test_status_shows_version_info(self):
        """Status command should show version and Python info."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "status"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert "Version" in result.stdout
        assert "Python" in result.stdout
        assert "Dependencies" in result.stdout

    def test_verify_shows_integrity(self):
        """Verify command should show integrity status."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "verify"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0
        # Should show chain status
        assert "Chain" in result.stdout or "chain" in result.stdout or "Verification" in result.stdout


class TestCLIImports:
    """Verify CLI module imports correctly."""

    def test_cli_importable(self):
        from kovrin.cli import cli

        assert callable(cli)

    def test_internal_functions_exist(self):
        from kovrin.cli import _audit, _run_pipeline, _serve, _status, _verify

        assert callable(_run_pipeline)
        assert callable(_audit)
        assert callable(_verify)
        assert callable(_serve)
        assert callable(_status)

    def test_shell_function_exists(self):
        """Shell subcommand function should exist."""
        from kovrin.cli import _shell

        assert callable(_shell)


class TestCLISubcommandHelp:
    """All subcommands should have --help."""

    def test_shell_help(self):
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "shell", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0

    def test_audit_help(self):
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "audit", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0

    def test_verify_help(self):
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "verify", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0

    def test_status_help(self):
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "status", "--help"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0


class TestCLIOutputFormat:
    """Verify CLI output contains expected structured content."""

    def test_status_shows_tools(self):
        """Status should show tool information."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "status"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0
        # Status should show framework info
        assert "Kovrin" in result.stdout

    def test_verify_exits_zero(self):
        """Verify with clean state should exit 0."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "verify"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        assert result.returncode == 0

    def test_audit_with_fake_id(self):
        """Audit with nonexistent intent_id should handle gracefully."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "audit", "nonexistent-intent-xyz"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        # Should not crash
        assert result.returncode in (0, 1)

    def test_run_without_intent_fails(self):
        """Run without intent argument should fail."""
        result = subprocess.run(
            [sys.executable, "-m", "kovrin.cli", "run"],
            capture_output=True,
            text=True,
            timeout=10,
        )
        # argparse should error on missing required argument
        assert result.returncode != 0
