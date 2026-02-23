"""
SuperWork API Routes

FastAPI router providing REST endpoints and WebSocket for the
SuperWork supervisor platform. Mounted conditionally on the main
app — only available when ``kovrin[superwork]`` extras are installed.

Endpoints:
    POST /api/superwork/start — initialize a supervisor session
    GET  /api/superwork/session — current session state
    GET  /api/superwork/proposals — trigger analysis + list proposals
    POST /api/superwork/proposals/{id}/approve — approve a proposal
    POST /api/superwork/proposals/{id}/skip — skip a proposal
    GET  /api/superwork/metrics — current metrics snapshot
    POST /api/superwork/predict — completion prediction
    GET  /api/superwork/sessions — list all sessions
    WS   /api/superwork/ws — real-time event stream
"""

from __future__ import annotations

import json
import logging
import os

from fastapi import APIRouter, WebSocket, WebSocketDisconnect
from pydantic import BaseModel

from kovrin.superwork.models import ProposalStatus, SuperWorkSession

logger = logging.getLogger(__name__)

router = APIRouter(prefix="/api/superwork", tags=["superwork"])


# ─── Request/Response Models ────────────────────────────────


class StartRequest(BaseModel):
    """Request body for starting a SuperWork session."""

    project_path: str


class ProposalActionResponse(BaseModel):
    """Response for proposal approve/skip actions."""

    proposal_id: str
    status: str
    message: str = ""


class PredictRequest(BaseModel):
    """Request body for completion prediction."""

    remaining_tasks: int = 10


# ─── SuperWork Manager ──────────────────────────────────────


class SuperWorkManager:
    """Manages the SuperWork session lifecycle for the API layer.

    Holds references to all SuperWork components and coordinates
    the event flow between them.
    """

    def __init__(self) -> None:
        self._initialized = False
        self._session: SuperWorkSession | None = None
        self._watcher = None
        self._context = None
        self._orchestrator = None
        self._metrics = None
        self._repo = None
        self._ws_connections: list[WebSocket] = []

    @property
    def is_initialized(self) -> bool:
        """Whether a SuperWork session is active."""
        return self._initialized

    async def initialize(self, project_path: str, db_url: str | None = None) -> SuperWorkSession:
        """Initialize all SuperWork components and start watching.

        Args:
            project_path: Path to the project to monitor.
            db_url: Database URL. Falls back to DATABASE_URL env var, then "kovrin.db".

        Returns:
            The created SuperWork session.
        """
        from kovrin.superwork.context_injector import ContextInjector
        from kovrin.superwork.metrics import MetricsTracker
        from kovrin.superwork.orchestrator import OrchestratorAgent
        from kovrin.superwork.repository import SuperWorkRepository
        from kovrin.superwork.session_watcher import SessionWatcher

        _db_url = db_url or os.environ.get("DATABASE_URL", "kovrin.db")
        self._repo = SuperWorkRepository(_db_url)
        self._metrics = MetricsTracker()
        self._context = ContextInjector(project_path)
        self._orchestrator = OrchestratorAgent(
            context_injector=self._context,
            metrics_tracker=self._metrics,
        )
        self._watcher = SessionWatcher(project_path)
        self._watcher.subscribe(self._on_task_complete)

        # Index project context
        chunks = await self._context.index_project()
        logger.info("Indexed %d chunks for project %s", chunks, project_path)

        # Start file watcher
        await self._watcher.start()

        # Create session
        self._session = SuperWorkSession(project_path=project_path)
        self._session.status = "WATCHING"
        self._repo.save_session(self._session)
        self._initialized = True

        return self._session

    async def _on_task_complete(self, event) -> None:
        """Handle task completion event from Session Watcher."""
        if self._metrics:
            self._metrics.record_completion(event)
        if self._orchestrator:
            self._orchestrator.record_completion(event)
        if self._repo and self._session:
            self._repo.save_event(self._session.id, event)
            self._repo.save_metrics(self._session.id, self._metrics.snapshot())
        await self._broadcast({"type": "task_complete", "data": event.model_dump(mode="json")})

    async def _broadcast(self, message: dict) -> None:
        """Broadcast message to all connected WebSocket clients."""
        dead: list[WebSocket] = []
        for ws in self._ws_connections:
            try:
                await ws.send_json(message)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self._ws_connections.remove(ws)

    async def shutdown(self) -> None:
        """Stop all components gracefully."""
        if self._watcher:
            await self._watcher.stop()
        if self._repo:
            self._repo.close()
        self._initialized = False


# Global instance — shared across all requests
sw_manager = SuperWorkManager()


# ─── Endpoints ──────────────────────────────────────────────


@router.post("/start")
async def start_superwork(body: StartRequest) -> dict:
    """Start a new SuperWork supervisor session."""
    session = await sw_manager.initialize(body.project_path)
    return session.model_dump(mode="json")


@router.get("/session")
async def get_session() -> dict:
    """Get the current active session."""
    if not sw_manager._session:
        return {"error": "No active SuperWork session"}
    return sw_manager._session.model_dump(mode="json")


@router.get("/proposals")
async def get_proposals() -> dict:
    """Trigger orchestrator analysis and return proposals."""
    if not sw_manager._orchestrator:
        return {"proposals": [], "total": 0}
    analysis = await sw_manager._orchestrator.analyze_and_propose()
    # Persist proposals
    if sw_manager._repo and sw_manager._session:
        for p in analysis.proposals:
            sw_manager._repo.save_proposal(p, sw_manager._session.id)
    return analysis.model_dump(mode="json")


@router.post("/proposals/{proposal_id}/approve")
async def approve_proposal(proposal_id: str) -> ProposalActionResponse:
    """Approve a task proposal for execution."""
    if sw_manager._repo:
        sw_manager._repo.update_proposal_status(proposal_id, ProposalStatus.APPROVED)
    await sw_manager._broadcast({"type": "proposal_approved", "proposal_id": proposal_id})
    return ProposalActionResponse(proposal_id=proposal_id, status="approved")


@router.post("/proposals/{proposal_id}/skip")
async def skip_proposal(proposal_id: str) -> ProposalActionResponse:
    """Skip a task proposal."""
    if sw_manager._repo:
        sw_manager._repo.update_proposal_status(proposal_id, ProposalStatus.SKIPPED)
    await sw_manager._broadcast({"type": "proposal_skipped", "proposal_id": proposal_id})
    return ProposalActionResponse(proposal_id=proposal_id, status="skipped")


@router.get("/metrics")
async def get_metrics() -> dict:
    """Get current session metrics."""
    if not sw_manager._metrics:
        return {"error": "No active session"}
    return sw_manager._metrics.snapshot().model_dump(mode="json")


@router.post("/predict")
async def predict_completion(body: PredictRequest) -> dict:
    """Predict completion time and cost for remaining tasks."""
    if not sw_manager._metrics:
        return {"error": "No active session"}
    return sw_manager._metrics.predict(body.remaining_tasks).model_dump(mode="json")


@router.get("/sessions")
async def list_sessions() -> dict:
    """List all SuperWork sessions."""
    if not sw_manager._repo:
        return {"sessions": [], "total": 0}
    sessions = sw_manager._repo.list_sessions()
    return {
        "sessions": [s.model_dump(mode="json") for s in sessions],
        "total": len(sessions),
    }


# ─── WebSocket ──────────────────────────────────────────────


@router.websocket("/ws")
async def superwork_websocket(websocket: WebSocket) -> None:
    """Real-time event stream for the SuperWork dashboard."""
    await websocket.accept()
    sw_manager._ws_connections.append(websocket)
    try:
        while True:
            data = await websocket.receive_text()
            msg = json.loads(data)
            if msg.get("type") == "ping":
                await websocket.send_json({"type": "pong"})
    except WebSocketDisconnect:
        if websocket in sw_manager._ws_connections:
            sw_manager._ws_connections.remove(websocket)
