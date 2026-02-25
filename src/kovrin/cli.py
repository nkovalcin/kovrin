"""
Kovrin CLI

Command-line interface for the Kovrin framework.

Commands:
    kovrin run "intent"          — Execute a pipeline
    kovrin run --tools "intent"  — Execute with tool execution
    kovrin shell                 — Interactive REPL (continuous mode)
    kovrin verify                — Verify Merkle chain integrity
    kovrin audit [intent_id]     — View audit trail
    kovrin serve                 — Start API server
    kovrin status                — Show framework status

Usage:
    pip install kovrin[cli]
    kovrin run "Analyze expenses and suggest cost savings"
    kovrin shell   # interactive mode — runs continuously
"""

from __future__ import annotations

import asyncio
import sys


def _build_model_routing(preset: str) -> dict[str, str] | None:
    """Build model routing dict from a named preset.

    Presets:
        smart  — Haiku for parsing/classification, Sonnet for execution/safety, Opus for orchestration
        sonnet — All components use Sonnet (legacy behavior)
        opus   — All components use Opus (max quality, expensive)
    """
    from kovrin.core.models import ModelTier

    if preset == "smart":
        return None  # Use DEFAULT_MODEL_ROUTING (already smart)
    elif preset == "sonnet":
        return {k: ModelTier.SONNET.value for k in [
            "intent_parser", "feasibility_critic", "policy_critic",
            "confidence_estimator", "prm", "task_executor", "safety_critic",
            "constitutional_core", "base_agent", "watchdog", "orchestrator",
        ]}
    elif preset == "opus":
        return {k: ModelTier.OPUS.value for k in [
            "intent_parser", "feasibility_critic", "policy_critic",
            "confidence_estimator", "prm", "task_executor", "safety_critic",
            "constitutional_core", "base_agent", "watchdog", "orchestrator",
        ]}
    return None


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

    from kovrin import __version__

    @click.group()
    @click.version_option(version=__version__, prog_name="kovrin")
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
    @click.option(
        "--routing",
        type=click.Choice(["smart", "sonnet", "opus"]),
        default="smart",
        help="Model routing preset (smart=Haiku/Sonnet/Opus, sonnet=all Sonnet, opus=all Opus)",
    )
    def run(
        intent: str,
        tools: bool,
        watchdog: bool,
        agents: bool,
        constraints: tuple[str, ...],
        json_output: bool,
        routing: str,
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
                model_routing=_build_model_routing(routing),
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

    @app.command()
    @click.option("--no-tools", is_flag=True, help="Disable tool execution")
    @click.option("--watchdog", is_flag=True, help="Enable watchdog monitoring")
    @click.option("--agents", is_flag=True, help="Enable multi-agent coordination")
    @click.option(
        "--routing",
        type=click.Choice(["smart", "sonnet", "opus"]),
        default="smart",
        help="Model routing preset (smart=Haiku/Sonnet/Opus, sonnet=all Sonnet, opus=all Opus)",
    )
    def shell(no_tools: bool, watchdog: bool, agents: bool, routing: str) -> None:
        """Interactive Kovrin shell — continuous REPL mode."""
        asyncio.run(
            _shell(
                tools=not no_tools,
                watchdog=watchdog,
                agents=agents,
                model_routing=_build_model_routing(routing),
            )
        )

    app()


def _argparse_cli() -> None:
    """Fallback argparse CLI (no extra dependencies)."""
    import argparse

    parser = argparse.ArgumentParser(
        prog="kovrin",
        description="Kovrin — Safety-First AI Agent Orchestration Framework",
    )
    from kovrin import __version__

    parser.add_argument("--version", action="version", version=f"kovrin {__version__}")
    subparsers = parser.add_subparsers(dest="command")

    # run
    run_parser = subparsers.add_parser("run", help="Execute a pipeline")
    run_parser.add_argument("intent", help="The intent to execute")
    run_parser.add_argument("--tools", action="store_true", help="Enable tools")
    run_parser.add_argument("--watchdog", action="store_true", help="Enable watchdog")
    run_parser.add_argument("--agents", action="store_true", help="Enable multi-agent")
    run_parser.add_argument("-c", "--constraint", action="append", dest="constraints", default=[])
    run_parser.add_argument("--json", action="store_true", dest="json_output")
    run_parser.add_argument(
        "--routing", choices=["smart", "sonnet", "opus"], default="smart",
        help="Model routing preset",
    )

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

    # shell
    shell_parser = subparsers.add_parser("shell", help="Interactive REPL mode")
    shell_parser.add_argument("--no-tools", action="store_true", help="Disable tools")
    shell_parser.add_argument("--watchdog", action="store_true", help="Enable watchdog")
    shell_parser.add_argument("--agents", action="store_true", help="Enable multi-agent")
    shell_parser.add_argument(
        "--routing", choices=["smart", "sonnet", "opus"], default="smart",
        help="Model routing preset",
    )

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
                model_routing=_build_model_routing(args.routing),
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
    elif args.command == "shell":
        asyncio.run(
            _shell(
                tools=not args.no_tools,
                watchdog=args.watchdog,
                agents=args.agents,
                model_routing=_build_model_routing(args.routing),
            )
        )
    else:
        parser.print_help()


async def _run_pipeline(
    intent: str,
    tools: bool = False,
    watchdog: bool = False,
    agents: bool = False,
    constraints: list[str] | None = None,
    json_output: bool = False,
    model_routing: dict[str, str] | None = None,
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
    routing_label = "smart" if model_routing is None else "custom"
    if model_routing and all(v == model_routing.get("intent_parser") for v in model_routing.values()):
        routing_label = model_routing["intent_parser"].split("-")[1]  # e.g. "sonnet" or "opus"
    print(f"  Routing: {routing_label}")
    print()

    engine = Kovrin(tools=tools, watchdog=watchdog, agents=agents, model_routing=model_routing)
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


async def _shell(
    tools: bool = True,
    watchdog: bool = False,
    agents: bool = False,
    model_routing: dict[str, str] | None = None,
) -> None:
    """Interactive Kovrin shell — continuous REPL mode.

    Initializes the engine once and runs tasks in a loop.
    Special commands: /help, /audit, /verify, /status, /tools, /history, /exit
    """
    import os
    import time

    # Load .env if present (for ANTHROPIC_API_KEY, BRAVE_SEARCH_API_KEY)
    env_path = os.path.join(os.getcwd(), ".env")
    if os.path.exists(env_path):
        with open(env_path) as f:
            for line in f:
                line = line.strip()
                if line and not line.startswith("#") and "=" in line:
                    key, _, value = line.partition("=")
                    key = key.strip()
                    value = value.strip()
                    if key and not os.environ.get(key):
                        os.environ[key] = value

    from kovrin import Kovrin, __version__
    from kovrin.audit.trace_logger import ImmutableTraceLog
    from kovrin.storage.repository import PipelineRepository

    # Initialize engine once
    engine = Kovrin(tools=tools, watchdog=watchdog, agents=agents, model_routing=model_routing)
    trace_log = ImmutableTraceLog()

    # Track session
    run_count = 0
    session_history: list[dict] = []

    # Count available tools
    tool_count = 0
    if engine._tool_registry:
        tool_count = len(engine._tool_registry.get_all())

    # Banner
    print(f"\n  {'=' * 62}")
    print(f"  Kovrin Interactive Shell v{__version__}")
    print(f"  {'=' * 62}")
    routing_label = "smart (Haiku/Sonnet/Opus)"
    if model_routing and all(v == model_routing.get("intent_parser") for v in model_routing.values()):
        tier = model_routing["intent_parser"].split("-")[1]  # e.g. "sonnet" or "opus"
        routing_label = f"{tier} (all {tier.title()})"
    print(f"  Tools: {tool_count} enabled" if tools else "  Tools: disabled")
    print(f"  Watchdog: {'on' if watchdog else 'off'} | Agents: {'on' if agents else 'off'} | Routing: {routing_label}")
    print("  Type /help for commands, /exit to quit")
    print(f"  {'=' * 62}\n")

    while True:
        # Prompt
        try:
            user_input = input("  kovrin> ").strip()
        except (EOFError, KeyboardInterrupt):
            print("\n  Goodbye.")
            break

        if not user_input:
            continue

        # Handle special commands
        if user_input.startswith("/"):
            cmd = user_input.lower().split()[0]

            if cmd in ("/exit", "/quit", "/q"):
                print("  Goodbye.")
                break

            elif cmd == "/help":
                _shell_help()
                continue

            elif cmd == "/status":
                _status()
                continue

            elif cmd == "/tools":
                _shell_tools(engine)
                continue

            elif cmd == "/audit":
                parts = user_input.split(maxsplit=1)
                intent_id = parts[1] if len(parts) > 1 else None
                _audit(intent_id)
                continue

            elif cmd == "/verify":
                _verify()
                continue

            elif cmd == "/history":
                _shell_history(session_history)
                continue

            elif cmd == "/clear":
                # Reset trace log for new session
                trace_log = ImmutableTraceLog()
                run_count = 0
                session_history.clear()
                print("  Session cleared.\n")
                continue

            else:
                print(f"  Unknown command: {cmd}. Type /help for commands.\n")
                continue

        # Execute as Kovrin intent
        run_count += 1
        run_id = f"#{run_count}"

        # Subscribe to live trace output
        async def _on_trace(hashed: object) -> None:
            t = hashed.trace  # type: ignore[attr-defined]
            risk_str = f" [{t.risk_level.value}]" if t.risk_level else ""
            l0_str = " [L0:PASS]" if t.l0_passed else ""
            print(f"    [{t.event_type:24s}]{risk_str}{l0_str} {t.description}")

        # Fresh trace log per run (but we keep session history)
        run_trace_log = ImmutableTraceLog()
        run_trace_log.subscribe(_on_trace)

        print(f"\n  --- Run {run_id} ---")
        start = time.monotonic()

        try:
            result = await engine.run(
                intent=user_input,
                trace_log=run_trace_log,
            )
            elapsed = time.monotonic() - start

            # Print summary
            status_str = "SUCCESS" if result.success else "FAILED"
            tasks_total = len(result.sub_tasks)
            tasks_rejected = len(result.rejected_tasks)
            traces_count = len(result.traces)

            print(f"\n  {status_str} | {tasks_total} tasks | {tasks_rejected} rejected | {traces_count} traces | {elapsed:.1f}s")

            # Print output (truncated)
            if result.output and result.success:
                print(f"  {'─' * 50}")
                output_lines = result.output[:3000]
                for line in output_lines.split("\n"):
                    print(f"  {line}")
                if len(result.output) > 3000:
                    print(f"  ... ({len(result.output)} chars total)")
                print(f"  {'─' * 50}")

            # Save to history
            session_history.append({
                "run": run_count,
                "intent": user_input,
                "success": result.success,
                "tasks": tasks_total,
                "rejected": tasks_rejected,
                "elapsed": round(elapsed, 1),
                "intent_id": result.intent_id,
            })

            # Persist to DB
            try:
                import os
                db_url = os.environ.get("DATABASE_URL", "kovrin.db")
                repo = PipelineRepository(db_url)
                repo.save_pipeline(result)
            except Exception:
                pass  # Non-critical — don't break shell on DB error

        except KeyboardInterrupt:
            elapsed = time.monotonic() - start
            print(f"\n  CANCELLED after {elapsed:.1f}s")
            session_history.append({
                "run": run_count,
                "intent": user_input,
                "success": False,
                "tasks": 0,
                "rejected": 0,
                "elapsed": round(elapsed, 1),
                "intent_id": "cancelled",
            })
        except Exception as e:
            elapsed = time.monotonic() - start
            print(f"\n  ERROR: {type(e).__name__}: {e}")
            print(f"  Failed after {elapsed:.1f}s")
            session_history.append({
                "run": run_count,
                "intent": user_input,
                "success": False,
                "tasks": 0,
                "rejected": 0,
                "elapsed": round(elapsed, 1),
                "intent_id": "error",
            })

        print()


def _shell_help() -> None:
    """Print shell help."""
    print()
    print("  COMMANDS:")
    print("    /help       Show this help")
    print("    /tools      List available tools")
    print("    /status     Show framework status")
    print("    /audit      List recent pipelines")
    print("    /audit <id> Show audit trail for pipeline")
    print("    /verify     Verify Merkle chain integrity")
    print("    /history    Show session history")
    print("    /clear      Reset session state")
    print("    /exit       Exit shell")
    print()
    print("  USAGE:")
    print("    Type any text to run it as a Kovrin pipeline.")
    print("    The full safety pipeline runs for every intent:")
    print("      Intent -> Decompose -> Critics -> Risk Route -> Execute -> Audit")
    print()
    print("  EXAMPLES:")
    print('    kovrin> Search for the latest AI safety news')
    print('    kovrin> Read the file pyproject.toml and summarize it')
    print('    kovrin> What is 2^128 in decimal?')
    print('    kovrin> What time is it in UTC?')
    print()


def _shell_tools(engine: object) -> None:
    """Print available tools."""
    from kovrin import Kovrin

    if not isinstance(engine, Kovrin) or not engine._tool_registry:
        print("  Tools are disabled.\n")
        return

    print()
    print("  AVAILABLE TOOLS:")
    for tool in engine._tool_registry.get_all():
        risk = tool.risk_profile.risk_level.value
        tier = tool.risk_profile.speculation_tier.value
        print(f"    {tool.definition.name:16s} [{risk:8s}] [{tier:8s}] {tool.definition.description[:60]}")
    print()


def _shell_history(history: list[dict]) -> None:
    """Print session history."""
    if not history:
        print("  No runs in this session.\n")
        return

    print()
    print("  SESSION HISTORY:")
    for h in history:
        status = "OK" if h["success"] else "FAIL"
        print(
            f"    #{h['run']:3d} [{status:4s}] {h['elapsed']:5.1f}s "
            f"| {h['tasks']} tasks, {h['rejected']} rejected "
            f"| {h['intent'][:50]}"
        )
    print()


def _print_header(title: str) -> None:
    """Print a formatted header."""
    print(f"\n  {'=' * 60}")
    print(f"  {title}")
    print(f"  {'=' * 60}\n")


if __name__ == "__main__":
    cli()
