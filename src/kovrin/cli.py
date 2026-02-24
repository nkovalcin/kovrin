"""
Kovrin CLI

Command-line interface for the Kovrin framework.

Commands:
    kovrin run "intent"          — Execute a pipeline
    kovrin run --tools "intent"  — Execute with tool execution
    kovrin verify                — Verify Merkle chain integrity
    kovrin audit [intent_id]     — View audit trail
    kovrin serve                 — Start API server
    kovrin status                — Show framework status

Usage:
    pip install kovrin[cli]
    kovrin run "Analyze expenses and suggest cost savings"
"""

from __future__ import annotations

import asyncio
import sys


def cli() -> None:
    """Main CLI entry point. Uses click if available, falls back to argparse."""
    try:
        import click  # noqa: F401

        _click_cli()
    except ImportError:
        _argparse_cli()


def _click_cli() -> None:
    """Click-based CLI (requires pip install kovrin[cli])."""
    import click

    @click.group()
    @click.version_option(version="2.0.0-alpha", prog_name="kovrin")
    def app() -> None:
        """Kovrin — Safety-First AI Agent Orchestration Framework"""
        pass

    @app.command()
    @click.argument("intent")
    @click.option("--tools", is_flag=True, help="Enable safety-gated tool execution")
    @click.option("--watchdog", is_flag=True, help="Enable watchdog monitoring")
    @click.option("--agents", is_flag=True, help="Enable multi-agent coordination")
    @click.option("--constraints", "-c", multiple=True, help="Add constraints (repeatable)")
    @click.option("--json-output", is_flag=True, help="Output as JSON")
    def run(
        intent: str,
        tools: bool,
        watchdog: bool,
        agents: bool,
        constraints: tuple[str, ...],
        json_output: bool,
    ) -> None:
        """Execute a Kovrin pipeline from an intent."""
        asyncio.run(
            _run_pipeline(
                intent=intent,
                tools=tools,
                watchdog=watchdog,
                agents=agents,
                constraints=list(constraints),
                json_output=json_output,
            )
        )

    @app.command()
    @click.argument("intent_id", required=False)
    def audit(intent_id: str | None) -> None:
        """View audit trail for a pipeline run."""
        _audit(intent_id)

    @app.command()
    def verify() -> None:
        """Verify Merkle chain integrity of stored traces."""
        _verify()

    @app.command()
    @click.option("--host", default="0.0.0.0", help="Bind address")
    @click.option("--port", default=8000, type=int, help="Port number")
    @click.option("--reload", is_flag=True, help="Auto-reload on changes")
    def serve(host: str, port: int, reload: bool) -> None:
        """Start the Kovrin API server."""
        _serve(host, port, reload)

    @app.command()
    def status() -> None:
        """Show Kovrin framework status and configuration."""
        _status()

    app()


def _argparse_cli() -> None:
    """Fallback argparse CLI (no extra dependencies)."""
    import argparse

    parser = argparse.ArgumentParser(
        prog="kovrin",
        description="Kovrin — Safety-First AI Agent Orchestration Framework",
    )
    parser.add_argument("--version", action="version", version="kovrin 2.0.0-alpha")
    subparsers = parser.add_subparsers(dest="command")

    # run
    run_parser = subparsers.add_parser("run", help="Execute a pipeline")
    run_parser.add_argument("intent", help="The intent to execute")
    run_parser.add_argument("--tools", action="store_true", help="Enable tools")
    run_parser.add_argument("--watchdog", action="store_true", help="Enable watchdog")
    run_parser.add_argument("--agents", action="store_true", help="Enable multi-agent")
    run_parser.add_argument("-c", "--constraint", action="append", dest="constraints", default=[])
    run_parser.add_argument("--json", action="store_true", dest="json_output")

    # audit
    audit_parser = subparsers.add_parser("audit", help="View audit trail")
    audit_parser.add_argument("intent_id", nargs="?", help="Pipeline intent ID")

    # verify
    subparsers.add_parser("verify", help="Verify Merkle chain integrity")

    # serve
    serve_parser = subparsers.add_parser("serve", help="Start API server")
    serve_parser.add_argument("--host", default="0.0.0.0")
    serve_parser.add_argument("--port", type=int, default=8000)
    serve_parser.add_argument("--reload", action="store_true")

    # status
    subparsers.add_parser("status", help="Show framework status")

    args = parser.parse_args()

    if args.command == "run":
        asyncio.run(
            _run_pipeline(
                intent=args.intent,
                tools=args.tools,
                watchdog=args.watchdog,
                agents=args.agents,
                constraints=args.constraints,
                json_output=args.json_output,
            )
        )
    elif args.command == "audit":
        _audit(args.intent_id)
    elif args.command == "verify":
        _verify()
    elif args.command == "serve":
        _serve(args.host, args.port, args.reload)
    elif args.command == "status":
        _status()
    else:
        parser.print_help()


async def _run_pipeline(
    intent: str,
    tools: bool = False,
    watchdog: bool = False,
    agents: bool = False,
    constraints: list[str] | None = None,
    json_output: bool = False,
) -> None:
    """Execute a Kovrin pipeline and print results."""
    from kovrin import Kovrin
    from kovrin.audit.trace_logger import ImmutableTraceLog

    _print_header("Kovrin Pipeline")
    print(f"  Intent: {intent}")
    print(f"  Tools: {'enabled' if tools else 'disabled'}")
    print(f"  Watchdog: {'enabled' if watchdog else 'disabled'}")
    print(f"  Agents: {'enabled' if agents else 'disabled'}")
    if constraints:
        print(f"  Constraints: {', '.join(constraints)}")
    print()

    engine = Kovrin(tools=tools, watchdog=watchdog, agents=agents)
    trace_log = ImmutableTraceLog()

    # Subscribe to trace events for live output
    if not json_output:

        async def _on_trace(hashed: object) -> None:
            t = hashed.trace  # type: ignore[attr-defined]
            risk_str = f" [{t.risk_level.value}]" if t.risk_level else ""
            l0_str = " [L0:PASS]" if t.l0_passed else ""
            print(f"  [{t.event_type:24s}]{risk_str}{l0_str} {t.description}")

        trace_log.subscribe(_on_trace)

    try:
        result = await engine.run(
            intent=intent,
            constraints=constraints,
            trace_log=trace_log,
        )
    except KeyboardInterrupt:
        print("\n  Pipeline interrupted.")
        sys.exit(1)

    print()
    if json_output:
        import json

        print(json.dumps(result.model_dump(), indent=2, default=str))
    else:
        _print_header("Result")
        print(f"  Status: {'SUCCESS' if result.success else 'FAILED'}")
        print(f"  Intent ID: {result.intent_id}")
        print(f"  Tasks: {len(result.sub_tasks)} total, {len(result.rejected_tasks)} rejected")
        print(f"  Traces: {len(result.traces)}")
        print()
        if result.output:
            print(result.output[:2000])
            if len(result.output) > 2000:
                print(f"\n  ... (truncated, {len(result.output)} chars total)")


def _audit(intent_id: str | None) -> None:
    """View audit trail from stored results."""
    import os

    from kovrin.storage.repository import PipelineRepository

    db_url = os.environ.get("DATABASE_URL", "kovrin.db")
    repo = PipelineRepository(db_url)

    if intent_id:
        traces = repo.get_traces_with_hashes(intent_id)
        if not traces:
            print(f"  No traces found for intent: {intent_id}")
            return

        _print_header(f"Audit Trail: {intent_id}")
        for row in traces:
            risk_str = f" [{row['risk_level']}]" if row.get("risk_level") else ""
            hash_str = row.get("hash", "")[:12]
            print(
                f"  #{row['sequence']:3d} {row['event_type']:24s}{risk_str} {row['description'][:60]}  [{hash_str}]"
            )
    else:
        # List recent pipelines
        pipelines = repo.list_pipelines(limit=20)
        _print_header("Recent Pipelines")
        if not pipelines:
            print("  No pipelines found.")
            return
        for p in pipelines:
            status = "SUCCESS" if p.get("success") else "FAILED"
            print(
                f"  {p['intent_id'][:12]}  [{status:7s}]  {p.get('intent', '')[:50]}  ({p.get('created_at', '')})"
            )


def _verify() -> None:
    """Verify Merkle chain integrity."""
    import os

    from kovrin.storage.repository import PipelineRepository

    db_url = os.environ.get("DATABASE_URL", "kovrin.db")
    repo = PipelineRepository(db_url)

    _print_header("Merkle Chain Verification")

    pipelines = repo.list_pipelines(limit=100)
    if not pipelines:
        print("  No pipelines to verify.")
        return

    total = 0
    valid = 0
    broken = 0

    for p in pipelines:
        intent_id = p["intent_id"]
        traces = repo.get_traces_with_hashes(intent_id)
        total += 1

        if not traces:
            continue

        chain_ok = True
        for i in range(1, len(traces)):
            prev_hash = traces[i].get("previous_hash")
            actual_prev = traces[i - 1].get("hash")
            if prev_hash and actual_prev and prev_hash != actual_prev:
                chain_ok = False
                break

        if chain_ok:
            valid += 1
        else:
            broken += 1
            print(f"  BROKEN: {intent_id[:12]} — chain integrity violation detected")

    print(f"\n  Total: {total} pipelines")
    print(f"  Valid: {valid}")
    print(f"  Broken: {broken}")
    if broken == 0:
        print("  All chains verified — integrity intact.")


def _serve(host: str, port: int, reload: bool) -> None:
    """Start the Kovrin API server."""
    try:
        import uvicorn
    except ImportError:
        print("Error: uvicorn not installed. Run: pip install kovrin[api]")
        sys.exit(1)

    _print_header("Kovrin API Server")
    print(f"  Binding: {host}:{port}")
    print(f"  Reload: {'enabled' if reload else 'disabled'}")
    print()

    uvicorn.run(
        "kovrin.api.server:app",
        host=host,
        port=port,
        reload=reload,
    )


def _status() -> None:
    """Show framework status."""
    import importlib

    _print_header("Kovrin Framework Status")

    # Version
    from kovrin import __version__

    print(f"  Version: {__version__}")

    # Python
    print(f"  Python: {sys.version.split()[0]}")

    # Check optional dependencies
    deps = {
        "anthropic": "Anthropic SDK",
        "fastapi": "API Server",
        "openai": "OpenAI Provider",
        "click": "CLI (enhanced)",
        "rich": "CLI (rich output)",
        "chromadb": "SuperWork (vector DB)",
    }

    print("\n  Dependencies:")
    for pkg, label in deps.items():
        try:
            mod = importlib.import_module(pkg)
            version = getattr(mod, "__version__", "installed")
            print(f"    {label:24s} {pkg:20s} {version}")
        except ImportError:
            print(f"    {label:24s} {pkg:20s} NOT INSTALLED")

    # Check env vars
    import os

    print("\n  Environment:")
    env_vars = ["ANTHROPIC_API_KEY", "BRAVE_SEARCH_API_KEY", "OPENAI_API_KEY", "DATABASE_URL"]
    for var in env_vars:
        value = os.environ.get(var)
        if value:
            masked = value[:4] + "..." + value[-4:] if len(value) > 10 else "***"
            print(f"    {var:30s} {masked}")
        else:
            print(f"    {var:30s} NOT SET")


def _print_header(title: str) -> None:
    """Print a formatted header."""
    print(f"\n  {'=' * 60}")
    print(f"  {title}")
    print(f"  {'=' * 60}\n")


if __name__ == "__main__":
    cli()
