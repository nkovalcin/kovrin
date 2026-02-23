"""
Kovrin API Server

FastAPI backend with WebSocket support for the dashboard UI.
Provides REST endpoints for pipeline execution, trace retrieval,
and human approval. WebSocket streams real-time events.

Usage:
    uvicorn kovrin.api.server:app --reload
"""

import asyncio
import json
import os
from contextlib import asynccontextmanager

from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, Field

from kovrin import Kovrin
from kovrin.audit.trace_logger import HashedTrace, ImmutableTraceLog
from kovrin.core.models import (
    ApprovalRequest,
    AutonomyProfile,
    AutonomySettings,
    CounterfactualResult,
    ExecutionResult,
    ReplayFrame,
    ReplaySession,
    RiskLevel,
    RoutingAction,
    RoutingDecision,
    SpeculationTier,
    SubTask,
    WatchdogAlert,
)
from kovrin.engine.risk_router import RiskRouter
from kovrin.storage.repository import PipelineRepository


# ─── Request/Response Models ────────────────────────────────

class RunRequest(BaseModel):
    intent: str
    constraints: list[str] = Field(default_factory=list)
    context: dict = Field(default_factory=dict)


class RunResponse(BaseModel):
    intent_id: str
    status: str = "running"


class StatusResponse(BaseModel):
    running_pipelines: int
    completed_pipelines: int
    pending_approvals: int = 0
    version: str = "2.0.0-alpha"


class ApproveRequest(BaseModel):
    approved: bool
    reason: str = ""


class AutonomyUpdateRequest(BaseModel):
    profile: str = "DEFAULT"
    override_matrix: dict[str, str] = Field(default_factory=dict)


class CounterfactualEvalRequest(BaseModel):
    profile: str = "DEFAULT"
    override_matrix: dict[str, str] = Field(default_factory=dict)


# ─── Pipeline Manager ───────────────────────────────────────

class PipelineManager:
    """Manages running and completed pipelines."""

    def __init__(self, db_url: str | None = None):
        self._running: dict[str, asyncio.Task] = {}
        self._results: dict[str, ExecutionResult] = {}
        self._ws_connections: list[WebSocket] = []

        # Approval queue: key = "{intent_id}:{task_id}" -> Future[bool]
        self._pending_approvals: dict[str, asyncio.Future] = {}
        self._approval_requests: dict[str, ApprovalRequest] = {}

        # Persistence
        _db_url = db_url or os.environ.get("DATABASE_URL", "kovrin.db")
        self._repo = PipelineRepository(_db_url)

        # Load persisted autonomy settings
        self._autonomy_settings = self._repo.get_autonomy_settings()

        # Create Kovrin with approval callback and autonomy settings
        self._kovrin = Kovrin(
            watchdog=False,
            approval_callback=self._handle_approval,
            autonomy_settings=self._autonomy_settings,
        )

    def update_autonomy_settings(self, settings: AutonomySettings) -> None:
        """Update autonomy settings: memory + Kovrin + DB + broadcast."""
        self._autonomy_settings = settings
        self._kovrin.update_autonomy_settings(settings)
        self._repo.save_autonomy_settings(settings)
        asyncio.create_task(self._broadcast({
            "type": "autonomy_updated",
            "data": {
                "profile": settings.profile.value,
                "override_matrix": settings.override_matrix,
                "updated_at": settings.updated_at.isoformat(),
            },
        }))

    def _handle_approval(self, request: ApprovalRequest) -> "asyncio.Future[bool]":
        """Approval callback called by RiskRouter when human approval is needed.

        Creates a Future, stores it in the pending queue, and broadcasts
        the approval request to WS clients. Returns the Future which will
        be resolved when the user approves/rejects via the API.
        """
        loop = asyncio.get_event_loop()
        future = loop.create_future()

        key = f"{request.intent_id}:{request.task_id}"
        self._pending_approvals[key] = future
        self._approval_requests[key] = request

        # Broadcast to WS clients (fire and forget)
        asyncio.create_task(self._broadcast({
            "type": "approval_request",
            "intent_id": request.intent_id,
            "data": {
                "intent_id": request.intent_id,
                "task_id": request.task_id,
                "description": request.description,
                "risk_level": request.risk_level.value,
                "speculation_tier": request.speculation_tier.value,
                "reason": request.reason,
                "proof_obligations": [
                    {"axiom_name": po.axiom_name, "passed": po.passed, "evidence": po.evidence}
                    for po in request.proof_obligations
                ],
                "timestamp": request.timestamp.isoformat(),
            },
        }))

        return future

    def resolve_approval(self, intent_id: str, task_id: str, approved: bool) -> bool:
        """Resolve a pending approval request.

        Returns True if the approval was found and resolved, False otherwise.
        """
        key = f"{intent_id}:{task_id}"
        future = self._pending_approvals.pop(key, None)
        self._approval_requests.pop(key, None)

        if future and not future.done():
            future.set_result(approved)
            return True
        return False

    async def start_pipeline(self, request: RunRequest) -> str:
        """Start a new pipeline and return its intent_id."""
        from kovrin.intent.schema import IntentV2
        intent_obj = IntentV2.simple(
            description=request.intent,
            constraints=request.constraints,
            context=request.context,
        )
        intent_id = intent_obj.id

        task = asyncio.create_task(self._run(intent_id, request))
        self._running[intent_id] = task
        return intent_id

    async def _run(self, intent_id: str, request: RunRequest) -> None:
        trace_log = ImmutableTraceLog()
        hashed_trace_data: list[dict] = []

        async def _on_trace(hashed: HashedTrace) -> None:
            """Broadcast each trace event to WS clients and collect hash data."""
            t = hashed.trace
            hashed_trace_data.append({
                "trace_id": t.id,
                "hash": hashed.hash,
                "previous_hash": hashed.previous_hash,
                "sequence": hashed.sequence,
            })
            await self._broadcast({
                "type": "trace",
                "intent_id": t.intent_id or intent_id,
                "data": {
                    "id": t.id,
                    "timestamp": t.timestamp.isoformat(),
                    "intent_id": t.intent_id,
                    "task_id": t.task_id,
                    "event_type": t.event_type,
                    "description": t.description,
                    "details": t.details or {},
                    "risk_level": t.risk_level.value if t.risk_level else None,
                    "l0_passed": t.l0_passed,
                },
            })

        trace_log.subscribe(_on_trace)

        try:
            result = await self._kovrin.run(
                intent=request.intent,
                constraints=request.constraints,
                context=request.context,
                trace_log=trace_log,
            )
            self._results[intent_id] = result
        except Exception as e:
            self._results[intent_id] = ExecutionResult(
                intent_id=intent_id,
                success=False,
                output=f"Pipeline error: {str(e)}",
            )
        finally:
            trace_log.unsubscribe(_on_trace)
            self._running.pop(intent_id, None)

        # Persist to SQLite with hash chain data
        try:
            self._repo.save_result(
                self._results[intent_id],
                intent=request.intent,
                constraints=request.constraints,
                context=request.context,
                hashed_traces=hashed_trace_data if hashed_trace_data else None,
            )
        except Exception:
            pass  # Persistence errors should not break the pipeline

        await self._broadcast({
            "type": "pipeline_complete",
            "intent_id": intent_id,
            "success": self._results[intent_id].success,
        })

    async def _broadcast(self, message: dict) -> None:
        """Send a message to all connected WebSocket clients."""
        dead = []
        for ws in self._ws_connections:
            try:
                await ws.send_json(message)
            except Exception:
                dead.append(ws)
        for ws in dead:
            self._ws_connections.remove(ws)

    def get_result(self, intent_id: str) -> ExecutionResult | None:
        # In-memory cache first, then DB fallback
        result = self._results.get(intent_id)
        if result:
            return result
        try:
            return self._repo.get_result(intent_id)
        except Exception:
            return None

    @property
    def pending_approvals(self) -> list[dict]:
        """Return list of pending approval requests as dicts."""
        return [
            {
                "intent_id": req.intent_id,
                "task_id": req.task_id,
                "description": req.description,
                "risk_level": req.risk_level.value,
                "speculation_tier": req.speculation_tier.value,
                "reason": req.reason,
                "timestamp": req.timestamp.isoformat(),
            }
            for req in self._approval_requests.values()
        ]

    @property
    def status(self) -> StatusResponse:
        return StatusResponse(
            running_pipelines=len(self._running),
            completed_pipelines=len(self._results),
            pending_approvals=len(self._pending_approvals),
        )


# ─── App ─────────────────────────────────────────────────────

manager = PipelineManager()


@asynccontextmanager
async def lifespan(app: FastAPI):
    yield


app = FastAPI(
    title="Kovrin API",
    description="Safety-first intent-based AI orchestration",
    version="2.0.0-alpha",
    lifespan=lifespan,
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Mount SuperWork router if extras are installed
try:
    from kovrin.api.superwork_router import router as superwork_router

    app.include_router(superwork_router)
except ImportError:
    pass


# ─── REST Endpoints ──────────────────────────────────────────

@app.get("/api/status")
async def get_status() -> StatusResponse:
    return manager.status


@app.post("/api/run")
async def run_pipeline(request: RunRequest) -> RunResponse:
    intent_id = await manager.start_pipeline(request)
    return RunResponse(intent_id=intent_id, status="running")


@app.get("/api/traces/{intent_id}")
async def get_traces(intent_id: str) -> dict:
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found or still running", "intent_id": intent_id}
    return {
        "intent_id": intent_id,
        "traces": [t.model_dump() for t in result.traces],
        "total": len(result.traces),
    }


@app.get("/api/graph/{intent_id}")
async def get_graph(intent_id: str) -> dict:
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found or still running", "intent_id": intent_id}
    return {
        "intent_id": intent_id,
        "graph": result.graph_summary,
    }


@app.get("/api/result/{intent_id}")
async def get_result(intent_id: str) -> dict:
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found or still running", "intent_id": intent_id}
    return result.model_dump()


@app.get("/api/pipelines")
async def list_pipelines(limit: int = 50, offset: int = 0) -> dict:
    """List all pipeline runs from persistent storage."""
    try:
        pipelines = manager._repo.list_pipelines(limit=limit, offset=offset)
        return {"pipelines": pipelines, "total": manager._repo.pipeline_count}
    except Exception:
        return {"pipelines": [], "total": 0}


@app.get("/api/approvals")
async def get_approvals() -> dict:
    """Get list of pending approval requests."""
    return {
        "approvals": manager.pending_approvals,
        "total": len(manager.pending_approvals),
    }


@app.post("/api/approve/{intent_id}/{task_id}")
async def approve_task(intent_id: str, task_id: str, body: ApproveRequest) -> dict:
    """Approve or reject a pending task."""
    resolved = manager.resolve_approval(intent_id, task_id, body.approved)
    if not resolved:
        return {"error": "Approval request not found or already resolved"}
    return {
        "status": "approved" if body.approved else "rejected",
        "intent_id": intent_id,
        "task_id": task_id,
    }


# ─── Autonomy Endpoints ─────────────────────────────────────

@app.get("/api/autonomy")
async def get_autonomy() -> dict:
    """Get current autonomy settings."""
    s = manager._autonomy_settings
    return {
        "profile": s.profile.value,
        "override_matrix": s.override_matrix,
        "updated_at": s.updated_at.isoformat(),
    }


@app.post("/api/autonomy")
async def update_autonomy(body: AutonomyUpdateRequest) -> dict:
    """Update autonomy settings. Persists to DB and broadcasts via WS."""
    from datetime import datetime, timezone
    settings = AutonomySettings(
        profile=AutonomyProfile(body.profile),
        override_matrix=body.override_matrix,
        updated_at=datetime.now(timezone.utc),
    )
    manager.update_autonomy_settings(settings)
    return {
        "status": "updated",
        "profile": settings.profile.value,
        "override_matrix": settings.override_matrix,
        "updated_at": settings.updated_at.isoformat(),
    }


# ─── Replay Endpoints ──────────────────────────────────────

@app.get("/api/replay/{intent_id}")
async def get_replay(intent_id: str) -> dict:
    """Build a replay session from stored traces with hash chain data."""
    rows = manager._repo.get_traces_with_hashes(intent_id)
    if not rows:
        return {"error": "No traces found for this pipeline", "intent_id": intent_id}

    # Verify hash chain
    chain_valid = True
    chain_message = ""
    for i, row in enumerate(rows):
        if i == 0:
            continue
        if row["previous_hash"] and rows[i - 1]["hash"]:
            if row["previous_hash"] != rows[i - 1]["hash"]:
                chain_valid = False
                chain_message = f"Chain broken at frame {i}"
                break

    if chain_valid:
        chain_message = f"All {len(rows)} frames verified — chain intact"

    frames = [
        ReplayFrame(
            sequence=row["sequence"],
            trace_id=row["trace_id"],
            hash=row["hash"],
            previous_hash=row["previous_hash"],
            event_type=row["event_type"],
            description=row["description"],
            risk_level=RiskLevel(row["risk_level"]) if row["risk_level"] else None,
            l0_passed=row["l0_passed"],
            details=row["details"],
            task_id=row["task_id"],
            timestamp=row["timestamp"],
        ).model_dump()
        for row in rows
    ]

    session = ReplaySession(
        intent_id=intent_id,
        total_frames=len(frames),
        frames=[ReplayFrame(**f) for f in frames],
        chain_valid=chain_valid,
        chain_message=chain_message,
    )
    return session.model_dump()


@app.post("/api/replay/{intent_id}/evaluate")
async def evaluate_counterfactual(intent_id: str, body: CounterfactualEvalRequest) -> dict:
    """Re-evaluate routing decisions with hypothetical autonomy settings."""
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found", "intent_id": intent_id}

    hypothetical = AutonomySettings(
        profile=AutonomyProfile(body.profile),
        override_matrix=body.override_matrix,
    )
    router = RiskRouter()

    diffs: list[dict] = []
    for subtask in result.sub_tasks:
        # Get actual routing (without settings)
        actual = router.route(subtask)
        # Get hypothetical routing (with settings)
        counterfactual = router.route(subtask, hypothetical)

        changed = actual.action != counterfactual.action
        diffs.append(CounterfactualResult(
            task_id=subtask.id,
            task_description=subtask.description[:80],
            actual_action=actual.action,
            counterfactual_action=counterfactual.action,
            changed=changed,
            risk_level=subtask.risk_level,
            speculation_tier=subtask.speculation_tier,
        ).model_dump())

    return {
        "intent_id": intent_id,
        "hypothetical_profile": body.profile,
        "diffs": diffs,
        "total_changed": sum(1 for d in diffs if d["changed"]),
    }


# ─── Phase 6: PRM, Tokens, Topology, Drift Endpoints ────────

@app.get("/api/prm/{intent_id}")
async def get_prm_scores(intent_id: str) -> dict:
    """Get PRM (Process Reward Model) scores for a pipeline's tasks."""
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found", "intent_id": intent_id}

    # Extract PRM_EVALUATION traces
    prm_traces = [
        t for t in result.traces
        if t.event_type == "PRM_EVALUATION"
    ]

    scores = []
    for t in prm_traces:
        d = t.details or {}
        scores.append({
            "task_id": t.task_id,
            "aggregate_score": d.get("aggregate_score", 0.0),
            "step_count": d.get("step_count", 0),
            "step_scores": d.get("step_scores", []),
            "reasoning": d.get("reasoning", ""),
            "timestamp": t.timestamp.isoformat(),
        })

    return {
        "intent_id": intent_id,
        "scores": scores,
        "total": len(scores),
    }


@app.get("/api/tokens")
async def get_active_tokens() -> dict:
    """Get active delegation capability tokens."""
    if not hasattr(manager._kovrin, '_token_authority') or not manager._kovrin._token_authority:
        return {"tokens": [], "total": 0, "enabled": False}

    tokens = manager._kovrin._token_authority.active_tokens
    return {
        "tokens": [
            {
                "id": t.id,
                "agent_id": t.agent_id,
                "scope": {
                    "allowed_risk_levels": [r.value for r in t.scope.allowed_risk_levels],
                    "allowed_actions": [a.value for a in t.scope.allowed_actions],
                    "max_tasks": t.scope.max_tasks,
                    "max_depth": t.scope.max_depth,
                },
                "issued_at": t.issued_at.isoformat(),
                "expires_at": t.expires_at.isoformat(),
                "parent_token_id": t.parent_token_id,
                "tasks_executed": t.tasks_executed,
                "revoked": t.revoked,
            }
            for t in tokens
        ],
        "total": len(tokens),
        "enabled": True,
    }


@app.get("/api/topology/{intent_id}")
async def get_topology(intent_id: str) -> dict:
    """Get topology recommendation for a pipeline."""
    result = manager.get_result(intent_id)
    if not result:
        return {"error": "Pipeline not found", "intent_id": intent_id}

    # Extract TOPOLOGY_SELECTED trace
    topo_traces = [
        t for t in result.traces
        if t.event_type == "TOPOLOGY_SELECTED"
    ]

    if not topo_traces:
        return {
            "intent_id": intent_id,
            "topology": None,
            "message": "Topology analysis not enabled for this pipeline",
        }

    d = topo_traces[0].details or {}
    return {
        "intent_id": intent_id,
        "topology": d.get("topology", "SEQUENTIAL"),
        "confidence": d.get("confidence", 0.0),
        "reasoning": d.get("reasoning", ""),
        "metrics": d.get("metrics", {}),
    }


@app.get("/api/drift")
async def get_drift_metrics() -> dict:
    """Get per-agent drift metrics from the watchdog."""
    if not hasattr(manager._kovrin, '_watchdog') or not manager._kovrin._watchdog:
        return {"agents": [], "total": 0, "enabled": False}

    tracker = manager._kovrin._watchdog.drift_tracker
    if not tracker:
        return {"agents": [], "total": 0, "enabled": False}

    metrics = tracker.get_all_metrics()
    return {
        "agents": [
            {
                "agent_name": m.agent_name,
                "total_executions": m.total_executions,
                "average_prm_score": m.average_prm_score,
                "success_rate": m.success_rate,
                "drift_level": m.drift_level.value,
                "recent_prm_scores": m.recent_prm_scores,
            }
            for m in metrics
        ],
        "total": len(metrics),
        "enabled": True,
    }


# ─── WebSocket ───────────────────────────────────────────────

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    manager._ws_connections.append(websocket)
    try:
        while True:
            data = await websocket.receive_text()
            try:
                msg = json.loads(data)
                if msg.get("type") == "ping":
                    await websocket.send_json({"type": "pong"})
                elif msg.get("type") == "approve":
                    # WS-based approval (alternative to REST endpoint)
                    intent_id = msg.get("intent_id", "")
                    task_id = msg.get("task_id", "")
                    approved = msg.get("approved", False)
                    manager.resolve_approval(intent_id, task_id, approved)
            except json.JSONDecodeError:
                pass
    except WebSocketDisconnect:
        if websocket in manager._ws_connections:
            manager._ws_connections.remove(websocket)
