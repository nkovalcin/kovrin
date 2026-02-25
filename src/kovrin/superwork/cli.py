"""
SuperWork CLI — Supervisor Mode Entry Point

Starts the SuperWork supervisor platform from the command line.
Monitors Claude Code sessions, indexes project context, and
provides real-time orchestration feedback.

Usage::

    kovrin-superwork --project ~/projects/bidbox
"""

from __future__ import annotations

import asyncio
import logging
import os
import signal
import sys

logger = logging.getLogger(__name__)


def main() -> None:
    """Entry point for the SuperWork CLI.

    Lazily imports ``click`` so that the base ``kovrin`` package
    does not require the superwork extras.
    """
    try:
        import click
    except ImportError:
        print(
            "SuperWork requires additional dependencies.\n"
            "Install them with: pip install kovrin[superwork]"
        )
        sys.exit(1)

    @click.command("superwork")
    @click.option(
        "--project",
        "-p",
        required=True,
        type=click.Path(exists=True),
        help="Path to the project directory to monitor.",
    )
    @click.option(
        "--database-url",
        default=None,
        help="Database URL (postgresql:// or SQLite path). Defaults to DATABASE_URL env var, then kovrin.db.",
    )
    @click.option(
        "--model",
        default=None,
        help="Claude model for the Orchestrator Agent. Defaults to Opus.",
    )
    def superwork(project: str, database_url: str | None, model: str | None) -> None:
        """Start the Kovrin SuperWork supervisor."""
        from kovrin.core.models import DEFAULT_MODEL_ROUTING

        db_url = database_url or os.environ.get("DATABASE_URL", "kovrin.db")
        resolved_model = model or DEFAULT_MODEL_ROUTING["orchestrator"].value
        asyncio.run(_run_superwork(project, db_url, resolved_model))

    superwork()


async def _run_superwork(project_path: str, db_url: str, model: str) -> None:
    """Main async loop for the SuperWork supervisor."""
    from rich.console import Console

    from kovrin.superwork.context_injector import ContextInjector
    from kovrin.superwork.metrics import MetricsTracker
    from kovrin.superwork.models import SuperWorkSession
    from kovrin.superwork.orchestrator import OrchestratorAgent
    from kovrin.superwork.repository import SuperWorkRepository
    from kovrin.superwork.session_watcher import SessionWatcher

    console = Console()
    console.print(f"\n[bold green]KOVRIN SuperWork[/] starting for: {project_path}\n")

    # Initialize components
    repo = SuperWorkRepository(db_url)
    metrics = MetricsTracker()
    context = ContextInjector(project_path)
    orchestrator = OrchestratorAgent(
        context_injector=context,
        metrics_tracker=metrics,
        model=model,
    )
    watcher = SessionWatcher(project_path)

    # Index project
    console.print("[dim]Indexing project context...[/]")
    chunks = await context.index_project()
    console.print(f"[dim]Indexed {chunks} chunks[/]")

    # Create session
    session = SuperWorkSession(project_path=project_path, status="WATCHING")
    repo.save_session(session)

    # Wire up event flow
    async def on_task_complete(event) -> None:
        metrics.record_completion(event)
        orchestrator.record_completion(event)
        repo.save_event(session.id, event)

        task_desc = event.completed_task[:60] or "unknown task"
        if event.errors:
            console.print(f"  [red]x[/] Failed: {task_desc}")
        else:
            console.print(f"  [green]+[/] Completed: {task_desc}")

        # Show metrics
        snap = metrics.snapshot()
        console.print(
            f"  [dim]Tasks: {snap.tasks_completed} done, "
            f"{snap.tasks_failed} failed | "
            f"Velocity: {snap.velocity_tasks_per_hour:.1f}/hr | "
            f"Cost: ${snap.cost_usd:.2f}[/]"
        )

        # Trigger new analysis
        console.print("\n[dim]Analyzing project state...[/]")
        analysis = await orchestrator.analyze_and_propose()

        if analysis.status != "ok":
            console.print(f"  [yellow]Orchestrator: {analysis.summary}[/]")
            return

        if analysis.proposals:
            console.print(f"\n[bold]Orchestrator proposes {len(analysis.proposals)} tasks:[/]")
            for i, p in enumerate(analysis.proposals):
                risk_color = {
                    "LOW": "green",
                    "MEDIUM": "yellow",
                    "HIGH": "red",
                    "CRITICAL": "bold red",
                }.get(p.risk_level.value, "white")
                console.print(f"  {i + 1}. [{risk_color}]{p.risk_level.value}[/] {p.title}")
                if p.rationale:
                    console.print(f"     [dim]{p.rationale[:80]}[/]")
                repo.save_proposal(p, session.id)

    watcher.subscribe(on_task_complete)

    # Start watching
    await watcher.start()
    console.print(
        f"[bold green]Watching[/] for Claude Code activity...\n"
        f"[dim]Session: {session.id}[/]\n"
        f"[dim]Press Ctrl+C to stop[/]\n"
    )

    # Keep alive until interrupted
    stop_event = asyncio.Event()
    loop = asyncio.get_running_loop()

    for sig in (signal.SIGINT, signal.SIGTERM):
        loop.add_signal_handler(sig, stop_event.set)

    try:
        await stop_event.wait()
    finally:
        await watcher.stop()
        repo.close()
        console.print("\n[bold red]SuperWork stopped.[/]")


if __name__ == "__main__":
    main()
