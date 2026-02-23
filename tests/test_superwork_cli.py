"""Tests for SuperWork CLI."""

import pytest


class TestCLIImport:
    def test_import_main(self):
        from kovrin.superwork.cli import main

        assert callable(main)

    def test_import_run_superwork(self):
        from kovrin.superwork.cli import _run_superwork

        assert callable(_run_superwork)


class TestRunSuperwork:
    @pytest.mark.asyncio
    async def test_run_superwork_is_coroutine(self):
        """Verify _run_superwork is an async function."""
        import asyncio

        from kovrin.superwork.cli import _run_superwork

        assert asyncio.iscoroutinefunction(_run_superwork)
