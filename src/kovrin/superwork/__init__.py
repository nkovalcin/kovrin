"""
Kovrin SuperWork — Supervisor Platform Layer

SuperWork is the human oversight layer built on top of the KOVRIN
safety framework. It enables real-time monitoring of AI agents,
task approval workflows, and project-level orchestration.

Requires optional dependencies::

    pip install kovrin[superwork]

Components:
    - SessionWatcher: monitors Claude Code session files
    - ContextInjector: ChromaDB-based project context (RAG)
    - OrchestratorAgent: Opus-powered task proposal engine
    - MetricsTracker: velocity, cost, and completion prediction
    - SuperWorkRepository: SQLite persistence for sessions/proposals
"""

from kovrin.superwork.models import (
    MetricsSnapshot,
    PredictionResult,
    ProjectAnalysis,
    ProposalStatus,
    SessionStatus,
    SuperWorkSession,
    TaskCompletionEvent,
    TaskProposal,
)

__all__ = [
    "MetricsSnapshot",
    "PredictionResult",
    "ProjectAnalysis",
    "ProposalStatus",
    "SessionStatus",
    "SuperWorkSession",
    "TaskCompletionEvent",
    "TaskProposal",
]
