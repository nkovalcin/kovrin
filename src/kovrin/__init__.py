"""
Kovrin — Safety-First Intent-Based AI Orchestration Framework

Usage:
    from kovrin import Kovrin

    engine = Kovrin()
    result = await engine.run(
        intent="Analyze monthly expenses and suggest cost savings",
        constraints=["Do not suggest layoffs"],
        context={"budget": 15000}
    )

    # With multi-agent coordination:
    engine = Kovrin(agents=True)

    # With watchdog monitoring:
    engine = Kovrin(watchdog=True)
"""

import asyncio

import anthropic

from kovrin.agents.coordinator import AgentCoordinator
from kovrin.agents.registry import AgentRegistry
from kovrin.audit.trace_logger import ImmutableTraceLog
from kovrin.core.constitutional import ConstitutionalCore
from kovrin.core.models import (
    AutonomySettings,
    ExplorationResult,
    ExecutionResult,
    SubTask,
    TaskStatus,
    Trace,
)
from kovrin.engine.executor import TaskExecutor
from kovrin.engine.graph import ExecutionGraph, GraphExecutor
from kovrin.engine.risk_router import RiskRouter
from kovrin.intent.parser import IntentParser
from kovrin.intent.schema import IntentV2
from kovrin.safety.critics import CriticPipeline, FeasibilityCritic, PolicyCritic, SafetyCritic
from kovrin.safety.watchdog import WatchdogAgent

__version__ = "2.0.0-alpha"

__all__ = [
    # Main API
    "Kovrin",
    "__version__",
    # Core
    "ConstitutionalCore",
    # Models
    "AutonomySettings",
    "ExplorationResult",
    "ExecutionResult",
    "SubTask",
    "TaskStatus",
    "Trace",
    # Intent
    "IntentParser",
    "IntentV2",
    # Engine
    "ExecutionGraph",
    "GraphExecutor",
    "RiskRouter",
    "TaskExecutor",
    # Safety
    "CriticPipeline",
    "FeasibilityCritic",
    "PolicyCritic",
    "SafetyCritic",
    "WatchdogAgent",
    # Audit
    "ImmutableTraceLog",
    # Agents
    "AgentCoordinator",
    "AgentRegistry",
]


class Kovrin:
    """Main Kovrin orchestrator — the public API.

    Pipeline:
    1. Parse intent into IntentV2
    2. Decompose into sub-tasks via IntentParser
    3. Validate each sub-task through CriticPipeline (L0 + feasibility + policy)
    4. Route approved tasks via RiskRouter
    5. Build ExecutionGraph from tasks and dependencies
    6. Execute graph (parallel where possible, with optional multi-agent)
    7. Log everything to ImmutableTraceLog (with optional watchdog monitoring)
    8. Return ExecutionResult
    """

    def __init__(
        self,
        api_key: str | None = None,
        max_concurrent: int = 5,
        auto_approve_sandbox: bool = True,
        watchdog: bool = False,
        agents: bool = False,
        approval_callback=None,
        explore: bool = False,
        mcts_iterations: int = 5,
        beam_width: int = 1,
        enable_confidence: bool = False,
        autonomy_settings: AutonomySettings | None = None,
        enable_prm: bool = False,
        enable_tokens: bool = False,
        topology: bool = False,
        tools: bool = False,
    ):
        """Initialize Kovrin.

        Args:
            api_key: Anthropic API key. If None, reads from ANTHROPIC_API_KEY env var.
            max_concurrent: Maximum parallel task executions.
            auto_approve_sandbox: If True, SANDBOX_REVIEW tasks execute with logging.
            watchdog: If True, enables independent watchdog monitoring.
            agents: If True, enables multi-agent coordination with specialized roles.
            approval_callback: Async callback for human approval (API mode).
                               Signature: (ApprovalRequest) -> Future[bool]
            explore: If True, enables MCTS decomposition exploration.
            mcts_iterations: Number of MCTS iterations (only used if explore=True).
            beam_width: Number of parallel beams (1=single path, >1=beam search).
            enable_confidence: If True, enables Claude-based confidence estimation.
            autonomy_settings: Optional runtime autonomy settings for risk routing overrides.
            enable_prm: If True, enables Process Reward Model step-level evaluation.
            enable_tokens: If True, enables Delegation Capability Tokens for agents.
            topology: If True, enables automatic topology selection for task graphs.
            tools: If True, enables safety-gated tool execution (code, web, file ops).
        """
        self._client = anthropic.AsyncAnthropic(api_key=api_key) if api_key else anthropic.AsyncAnthropic()
        self._constitutional = ConstitutionalCore(self._client)
        self._parser = IntentParser(self._client)
        self._router = RiskRouter()

        # Phase 6: PRM
        self._prm = None
        if enable_prm:
            from kovrin.engine.prm import ProcessRewardModel
            self._prm = ProcessRewardModel(self._client)

        # Safety-gated tool execution system
        self._tools_enabled = tools
        self._tool_registry = None
        self._tool_router = None
        if tools:
            from kovrin.tools.registry import ToolRegistry
            from kovrin.tools.router import SafeToolRouter
            from kovrin.tools.builtin import register_all_builtins

            self._tool_registry = ToolRegistry()
            register_all_builtins(self._tool_registry)
            self._tool_router = SafeToolRouter(
                registry=self._tool_registry,
                risk_router=self._router,
                constitutional_core=self._constitutional,
                token_authority=None,  # Set below after token_authority init
                approval_callback=approval_callback,
            )

        self._executor = TaskExecutor(
            self._client, self._router,
            approval_callback=approval_callback,
            autonomy_settings=autonomy_settings,
            prm=self._prm,
            tool_registry=self._tool_registry,
            tool_router=self._tool_router,
        )
        self._graph_executor = GraphExecutor(max_concurrent)
        self._safety_critic = SafetyCritic(self._constitutional)
        self._feasibility_critic = FeasibilityCritic(self._client)
        self._policy_critic = PolicyCritic(self._client)
        self._critics = CriticPipeline(self._safety_critic, self._feasibility_critic, self._policy_critic)
        self._auto_approve_sandbox = auto_approve_sandbox

        # Watchdog (enable agent drift when both agents and watchdog are on)
        self._watchdog_enabled = watchdog
        self._watchdog: WatchdogAgent | None = None
        self._enable_agent_drift = watchdog and agents

        # Phase 6: Token authority
        self._token_authority = None
        if enable_tokens:
            from kovrin.engine.tokens import TokenAuthority
            self._token_authority = TokenAuthority()
            # Wire token authority into tool router for DCT scope checks
            if self._tool_router:
                self._tool_router._token_authority = self._token_authority

        # Multi-agent
        self._agents_enabled = agents
        self._registry: AgentRegistry | None = None
        self._coordinator: AgentCoordinator | None = None
        if agents:
            self._registry = AgentRegistry(self._client)
            self._registry.register_defaults()
            self._coordinator = AgentCoordinator(
                self._registry, self._client,
                token_authority=self._token_authority,
            )

        # Phase 6: Topology
        self._topology_enabled = topology
        self._topology_analyzer = None
        if topology:
            from kovrin.engine.topology import TopologyAnalyzer
            self._topology_analyzer = TopologyAnalyzer()

        # Phase 4: Exploration
        self._explore = explore
        self._mcts_iterations = mcts_iterations
        self._beam_width = beam_width
        self._enable_confidence = enable_confidence
        self._mcts = None
        self._beam_executor = None
        self._confidence = None

        if explore:
            from kovrin.engine.mcts import CriticBasedScorer, MCTSExplorer
            scorer = CriticBasedScorer(self._critics)
            self._mcts = MCTSExplorer(
                parser=self._parser,
                scorer=scorer,
                client=self._client,
                max_iterations=mcts_iterations,
            )
        if beam_width > 1:
            from kovrin.engine.beam_search import BeamSearchExecutor
            self._beam_executor = BeamSearchExecutor(
                beam_width=beam_width,
                max_concurrent_per_beam=max_concurrent,
            )
        if enable_confidence:
            from kovrin.engine.confidence import ConfidenceEstimator
            self._confidence = ConfidenceEstimator(self._client)

    def update_autonomy_settings(self, settings: AutonomySettings | None) -> None:
        """Update autonomy settings at runtime. Forwards to executor."""
        self._executor.update_autonomy_settings(settings)

    async def run(
        self,
        intent: str,
        constraints: list[str] | None = None,
        context: dict | None = None,
        trace_log: ImmutableTraceLog | None = None,
    ) -> ExecutionResult:
        """Execute a Kovrin pipeline from intent to result.

        Args:
            intent: The user's intent description.
            constraints: Optional constraints for the pipeline.
            context: Optional context dict.
            trace_log: Optional external trace log (e.g., from API server for streaming).
                       If None, a fresh ImmutableTraceLog is created.
        """
        if trace_log is None:
            trace_log = ImmutableTraceLog()

        # Wire trace log into tool router for Merkle audit of tool calls
        if self._tool_router:
            self._tool_router._trace_log = trace_log

        # Start watchdog if enabled
        if self._watchdog_enabled:
            self._watchdog = WatchdogAgent(
                client=self._client,
                enable_agent_drift=self._enable_agent_drift,
            )
            await self._watchdog.start(trace_log, intent)

        try:
            return await self._run_pipeline(intent, constraints, context, trace_log)
        finally:
            if self._watchdog:
                await self._watchdog.stop()

    async def _run_pipeline(
        self,
        intent: str,
        constraints: list[str] | None,
        context: dict | None,
        trace_log: ImmutableTraceLog,
    ) -> ExecutionResult:
        """Internal pipeline execution."""

        # 1. Create IntentV2
        intent_obj = IntentV2.simple(
            description=intent,
            constraints=constraints,
            context=context,
        )

        await trace_log.append_async(Trace(
            intent_id=intent_obj.id,
            event_type="INTENT_RECEIVED",
            description=f"Intent: {intent[:80]}",
            details={
                "constraints": constraints or [],
                "context": context or {},
                "watchdog": self._watchdog_enabled,
                "agents": self._agents_enabled,
            },
        ))

        # 2. Decompose into sub-tasks
        exploration_info = None
        all_candidates = None

        if self._explore and self._mcts:
            best, all_candidates = await self._mcts.explore(
                intent_obj, constraints, context
            )
            subtasks = best.subtasks
            exploration_info = ExplorationResult(
                candidates_explored=len(all_candidates),
                best_decomposition_id=best.id,
                mcts_iterations=self._mcts_iterations,
                beam_width=self._beam_width,
            )
            await trace_log.append_async(Trace(
                intent_id=intent_obj.id,
                event_type="MCTS_EXPLORATION",
                description=f"MCTS explored {len(all_candidates)} decompositions, best score={best.score:.2f}",
                details={
                    "candidates": len(all_candidates),
                    "best_score": best.score,
                    "best_variant": best.prompt_variant,
                },
            ))
        else:
            subtasks = await self._parser.parse(intent_obj)

        await trace_log.append_async(Trace(
            intent_id=intent_obj.id,
            event_type="DECOMPOSITION",
            description=f"Decomposed into {len(subtasks)} sub-tasks",
            details={"tasks": [{"id": t.id, "description": t.description[:60]} for t in subtasks]},
        ))

        # 3. Validate each sub-task through critic pipeline
        approved_tasks: list[SubTask] = []
        rejected_tasks: list[SubTask] = []

        for subtask in subtasks:
            subtask.parent_intent_id = intent_obj.id

            # Check watchdog kill signal
            if self._watchdog and self._watchdog.is_killed:
                await trace_log.append_async(Trace(
                    intent_id=intent_obj.id,
                    event_type="WATCHDOG_KILLED",
                    description="Pipeline killed by watchdog during validation",
                ))
                break

            passed, obligations = await self._critics.evaluate(
                subtask=subtask,
                constraints=constraints or [],
                intent_context=intent,
                task_context=context,
            )

            subtask.proof_obligations = obligations
            await trace_log.append_async(CriticPipeline.create_trace(subtask, passed, obligations, intent_obj.id))

            if passed:
                approved_tasks.append(subtask)
            else:
                subtask.status = TaskStatus.REJECTED_BY_L0
                rejected_tasks.append(subtask)

        if not approved_tasks:
            await trace_log.append_async(Trace(
                intent_id=intent_obj.id,
                event_type="PIPELINE_ABORTED",
                description="All sub-tasks rejected by critics — pipeline aborted",
            ))
            trace_log.print_summary()
            return ExecutionResult(
                intent_id=intent_obj.id,
                output="All sub-tasks were rejected by the safety/policy critics. No execution performed.",
                success=False,
                sub_tasks=subtasks,
                rejected_tasks=rejected_tasks,
                traces=[e.trace for e in trace_log.get_events()],
            )

        # 4. Build execution graph
        graph = ExecutionGraph(intent_id=intent_obj.id)
        task_map = {t.id: t for t in approved_tasks}
        approved_ids = set(task_map.keys())

        for task in approved_tasks:
            valid_deps = {d for d in task.dependencies if d in approved_ids}
            graph.add_node(task, valid_deps)

        optimizations = graph.optimize()
        if optimizations:
            await trace_log.append_async(Trace(
                intent_id=intent_obj.id,
                event_type="GRAPH_OPTIMIZATION",
                description=f"Graph optimized: {', '.join(optimizations)}",
                details={"optimizations": optimizations, "waves": graph.execution_order},
            ))

        # 4b. Topology analysis (optional)
        if self._topology_analyzer:
            from kovrin.engine.topology import TopologyAnalyzer
            recommendation = self._topology_analyzer.analyze(graph)
            await trace_log.append_async(
                TopologyAnalyzer.create_trace(recommendation, intent_obj.id)
            )

        # 5. Choose execution function
        if self._agents_enabled and self._coordinator:
            execute_fn = self._coordinator.execute_with_agent
            await trace_log.append_async(Trace(
                intent_id=intent_obj.id,
                event_type="MULTI_AGENT_MODE",
                description=f"Multi-agent execution with {len(self._registry)} agents",
                details={"agents": [a.info.model_dump() for a in self._registry.agents]},
            ))
        else:
            execute_fn = self._executor.execute_for_graph

        # 6. Execute graph
        await trace_log.append_async(Trace(
            intent_id=intent_obj.id,
            event_type="EXECUTION_START",
            description=f"Executing {len(approved_tasks)} tasks across {len(graph.execution_order)} waves",
        ))

        if self._beam_executor and all_candidates and len(all_candidates) > 1:
            valid_candidates = [c for c in all_candidates if c.critic_pass_rate > 0]
            if valid_candidates:
                results, winning_state = await self._beam_executor.execute(
                    valid_candidates, execute_fn, intent_id=intent_obj.id
                )
                if exploration_info:
                    exploration_info.beams_pruned = self._beam_executor.beams_pruned
            else:
                results = await self._graph_executor.execute(graph, execute_fn)
        else:
            results = await self._graph_executor.execute(graph, execute_fn)

        # 6b. Confidence estimation (optional)
        if self._enable_confidence and self._confidence and results:
            confidence_estimates = []
            for task_id, result_text in results.items():
                task = task_map.get(task_id)
                if task:
                    est = await self._confidence.estimate(task, result_text, intent)
                    confidence_estimates.append(est)
            if exploration_info:
                exploration_info.confidence_estimates = confidence_estimates

        # 7. Synthesize output
        output_parts = []
        for task_id, result in results.items():
            task = task_map.get(task_id)
            if task:
                output_parts.append(f"## {task.description}\n{result}")

        final_output = "\n\n---\n\n".join(output_parts) if output_parts else "No results produced."

        # 8. Watchdog summary
        watchdog_info = {}
        if self._watchdog:
            watchdog_info = {
                "alerts": len(self._watchdog.alerts),
                "killed": self._watchdog.is_killed,
                "paused": self._watchdog.is_paused,
            }

        await trace_log.append_async(Trace(
            intent_id=intent_obj.id,
            event_type="PIPELINE_COMPLETE",
            description=f"Pipeline complete: {len(results)}/{len(approved_tasks)} tasks succeeded",
            details={
                "completed": len(results),
                "total": len(approved_tasks),
                "watchdog": watchdog_info,
            },
        ))

        trace_log.print_summary()

        return ExecutionResult(
            intent_id=intent_obj.id,
            output=final_output,
            success=len(results) > 0,
            sub_tasks=subtasks,
            rejected_tasks=rejected_tasks,
            traces=[e.trace for e in trace_log.get_events()],
            graph_summary=graph.to_dict(),
            exploration=exploration_info,
        )

    def run_sync(
        self,
        intent: str,
        constraints: list[str] | None = None,
        context: dict | None = None,
    ) -> ExecutionResult:
        """Synchronous wrapper for run(). Convenience for scripts."""
        return asyncio.run(self.run(intent, constraints, context))
