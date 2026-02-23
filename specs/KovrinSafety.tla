---------------------------- MODULE KovrinSafety -----------------------------
(*
 * Kovrin v2 — Top-Level Safety Composition
 *
 * Composes the critical safety invariants from all Kovrin modules into
 * a single unified model. This spec instantiates a minimal pipeline:
 *   L0 Check → Routing → Speculative Execution → Trace Logging → Watchdog
 *
 * Verifies that the composition of all subsystems maintains:
 * - Axiom Safety: rejected tasks never execute
 * - Critical Routing: CRITICAL → HUMAN_APPROVAL always
 * - Hash Chain Integrity: tamper-evident logging
 * - Rollback Correctness: GUARDED rollback restores prior state
 * - Kill Irreversibility: watchdog KILL is permanent
 * - Pipeline Termination: all tasks eventually reach terminal state
 *
 * Individual module specs verify component-level properties.
 * This spec verifies cross-component properties and composition safety.
 *
 * Maps to: The full Kovrin pipeline
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Tasks,              \* Set of task IDs (small: {"t1", "t2", "t3"})
    MaxEvents           \* Bound on trace log events

VARIABLES
    \* — Task Lifecycle —
    task_status,        \* Function: task -> Status
    l0_result,          \* Function: task -> {"PASS", "FAIL", "PENDING"}

    \* — Routing —
    risk_level,         \* Function: task -> RiskLevel
    routed_action,      \* Function: task -> RoutingAction

    \* — Speculation —
    spec_tier,          \* Function: task -> {"FREE", "GUARDED", "NONE"}
    checkpoint,         \* Function: task -> {"NONE", "SNAPSHOT"}
    committed,          \* Set of tasks whose results are committed

    \* — Trace Log —
    trace_chain,        \* Sequence of trace events
    trace_head,         \* Current chain head hash

    \* — Watchdog —
    watchdog_state      \* {"RUNNING", "PAUSED", "KILLED"}

\* ─── Constants ───
TaskStates == {"PENDING", "READY", "RUNNING", "COMPLETED", "FAILED",
               "REJECTED_BY_L0", "SKIPPED", "ROLLED_BACK"}
RiskLevels == {"LOW", "MEDIUM", "HIGH", "CRITICAL"}
RoutingActions == {"AUTO_EXECUTE", "SANDBOX_REVIEW", "HUMAN_APPROVAL"}
SpecTiers == {"FREE", "GUARDED", "NONE"}
L0Results == {"PASS", "FAIL", "PENDING"}

GENESIS == "GENESIS"
Hash(content, prev) == <<content, prev>>

\* ─── Type Invariant ───
TypeOK ==
    /\ task_status \in [Tasks -> TaskStates]
    /\ l0_result \in [Tasks -> L0Results]
    /\ risk_level \in [Tasks -> RiskLevels]
    /\ routed_action \in [Tasks -> RoutingActions]
    /\ spec_tier \in [Tasks -> SpecTiers]
    /\ checkpoint \in [Tasks -> {"NONE", "SNAPSHOT"}]
    /\ committed \subseteq Tasks
    /\ watchdog_state \in {"RUNNING", "PAUSED", "KILLED"}

\* ─── Initial State ───
Init ==
    /\ task_status = [t \in Tasks |-> "PENDING"]
    /\ l0_result = [t \in Tasks |-> "PENDING"]
    /\ risk_level \in [Tasks -> RiskLevels]
    /\ routed_action = [t \in Tasks |-> "HUMAN_APPROVAL"]  \* Safe default
    /\ spec_tier \in [Tasks -> SpecTiers]
    /\ checkpoint = [t \in Tasks |-> "NONE"]
    /\ committed = {}
    /\ trace_chain = <<>>
    /\ trace_head = GENESIS
    /\ watchdog_state = "RUNNING"

\* ─── L0 Constitutional Check ───
L0Check(t) ==
    /\ task_status[t] = "PENDING"
    /\ l0_result[t] = "PENDING"
    /\ \E result \in {"PASS", "FAIL"} :
        /\ l0_result' = [l0_result EXCEPT ![t] = result]
        /\ IF result = "FAIL"
           THEN task_status' = [task_status EXCEPT ![t] = "REJECTED_BY_L0"]
           ELSE task_status' = [task_status EXCEPT ![t] = "READY"]
        /\ UNCHANGED <<risk_level, routed_action, spec_tier, checkpoint,
                       committed, trace_chain, trace_head, watchdog_state>>

\* ─── Route Task (with CRITICAL guard) ───
RouteTask(t) ==
    /\ task_status[t] = "READY"
    /\ routed_action' = [routed_action EXCEPT ![t] =
        IF risk_level[t] = "CRITICAL"
        THEN "HUMAN_APPROVAL"
        ELSE CASE risk_level[t] = "LOW" /\ spec_tier[t] = "FREE" -> "AUTO_EXECUTE"
               [] risk_level[t] = "LOW" /\ spec_tier[t] = "GUARDED" -> "AUTO_EXECUTE"
               [] risk_level[t] = "LOW" /\ spec_tier[t] = "NONE" -> "SANDBOX_REVIEW"
               [] risk_level[t] = "MEDIUM" /\ spec_tier[t] = "FREE" -> "AUTO_EXECUTE"
               [] risk_level[t] = "MEDIUM" /\ spec_tier[t] = "GUARDED" -> "SANDBOX_REVIEW"
               [] risk_level[t] = "MEDIUM" /\ spec_tier[t] = "NONE" -> "HUMAN_APPROVAL"
               [] risk_level[t] = "HIGH" /\ spec_tier[t] = "FREE" -> "SANDBOX_REVIEW"
               [] risk_level[t] = "HIGH" /\ spec_tier[t] = "GUARDED" -> "HUMAN_APPROVAL"
               [] risk_level[t] = "HIGH" /\ spec_tier[t] = "NONE" -> "HUMAN_APPROVAL"
               [] OTHER -> "HUMAN_APPROVAL"]
    /\ UNCHANGED <<task_status, l0_result, risk_level, spec_tier, checkpoint,
                   committed, trace_chain, trace_head, watchdog_state>>

\* ─── Execute Task (checkpoint if GUARDED) ───
ExecuteTask(t) ==
    /\ task_status[t] = "READY"
    /\ l0_result[t] = "PASS"
    /\ watchdog_state # "KILLED"
    \* Checkpoint for GUARDED tasks
    /\ checkpoint' = IF spec_tier[t] = "GUARDED"
                     THEN [checkpoint EXCEPT ![t] = "SNAPSHOT"]
                     ELSE checkpoint
    /\ task_status' = [task_status EXCEPT ![t] = "RUNNING"]
    \* Log the execution start
    /\ LET new_hash == Hash("EXEC_START", trace_head)
       IN /\ trace_chain' = Append(trace_chain, [task |-> t, action |-> "EXEC_START", hash |-> new_hash])
          /\ trace_head' = new_hash
    /\ UNCHANGED <<l0_result, risk_level, routed_action, spec_tier,
                   committed, watchdog_state>>

\* ─── Complete Task ───
CompleteTask(t) ==
    /\ task_status[t] = "RUNNING"
    /\ task_status' = [task_status EXCEPT ![t] = "COMPLETED"]
    /\ committed' = committed \cup {t}
    \* Log completion
    /\ LET new_hash == Hash("COMPLETE", trace_head)
       IN /\ trace_chain' = Append(trace_chain, [task |-> t, action |-> "COMPLETE", hash |-> new_hash])
          /\ trace_head' = new_hash
    /\ UNCHANGED <<l0_result, risk_level, routed_action, spec_tier,
                   checkpoint, watchdog_state>>

\* ─── Fail Task ───
FailTask(t) ==
    /\ task_status[t] = "RUNNING"
    /\ task_status' = [task_status EXCEPT ![t] = "FAILED"]
    /\ LET new_hash == Hash("FAIL", trace_head)
       IN /\ trace_chain' = Append(trace_chain, [task |-> t, action |-> "FAIL", hash |-> new_hash])
          /\ trace_head' = new_hash
    /\ UNCHANGED <<l0_result, risk_level, routed_action, spec_tier,
                   checkpoint, committed, watchdog_state>>

\* ─── Rollback GUARDED Task ───
RollbackGuarded(t) ==
    /\ task_status[t] = "RUNNING"
    /\ spec_tier[t] = "GUARDED"
    /\ checkpoint[t] = "SNAPSHOT"
    /\ task_status' = [task_status EXCEPT ![t] = "ROLLED_BACK"]
    /\ LET new_hash == Hash("ROLLBACK", trace_head)
       IN /\ trace_chain' = Append(trace_chain, [task |-> t, action |-> "ROLLBACK", hash |-> new_hash])
          /\ trace_head' = new_hash
    /\ UNCHANGED <<l0_result, risk_level, routed_action, spec_tier,
                   checkpoint, committed, watchdog_state>>

\* ─── Watchdog: Detect violated rule → KILL ───
WatchdogKill ==
    /\ \E t \in Tasks :
        /\ l0_result[t] = "FAIL"
        /\ task_status[t] = "RUNNING"  \* Violation: rejected task is running
    /\ watchdog_state' = "KILLED"
    /\ UNCHANGED <<task_status, l0_result, risk_level, routed_action,
                   spec_tier, checkpoint, committed, trace_chain, trace_head>>

\* ─── Next-State ───
Next ==
    \/ \E t \in Tasks :
        \/ L0Check(t)
        \/ RouteTask(t)
        \/ ExecuteTask(t)
        \/ CompleteTask(t)
        \/ FailTask(t)
        \/ RollbackGuarded(t)
    \/ WatchdogKill

vars == <<task_status, l0_result, risk_level, routed_action, spec_tier,
          checkpoint, committed, trace_chain, trace_head, watchdog_state>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ═══════════════════════════════════════════════════════════════════════
\* COMPOSED SAFETY INVARIANTS
\* ═══════════════════════════════════════════════════════════════════════

\* 1. AXIOM SAFETY: Rejected tasks never execute
\*    (from TaskStateMachine.tla + AxiomValidation.tla)
AxiomSafety ==
    \A t \in Tasks :
        l0_result[t] = "FAIL" => task_status[t] # "RUNNING"

\* 2. CRITICAL ROUTING: CRITICAL tasks always routed to HUMAN_APPROVAL
\*    (from RoutingMatrix.tla)
CriticalAlwaysHumanApproved ==
    \A t \in Tasks :
        risk_level[t] = "CRITICAL" => routed_action[t] = "HUMAN_APPROVAL"

\* 3. HASH CHAIN INTEGRITY: trace head matches last event hash
\*    (from HashChain.tla)
TraceChainIntegrity ==
    trace_chain # <<>> => trace_head = trace_chain[Len(trace_chain)].hash

\* 4. ROLLBACK CORRECTNESS: rolled-back tasks are never committed
\*    (from SpeculationModel.tla)
RolledBackNotCommitted ==
    \A t \in Tasks :
        task_status[t] = "ROLLED_BACK" => t \notin committed

\* 5. GUARDED CHECKPOINT: GUARDED tasks have checkpoint when running
\*    (from SpeculationModel.tla)
GuardedHasCheckpoint ==
    \A t \in Tasks :
        (spec_tier[t] = "GUARDED" /\ task_status[t] = "RUNNING") =>
            checkpoint[t] = "SNAPSHOT"

\* 6. KILL IRREVERSIBILITY: watchdog KILL cannot revert to RUNNING
\*    (from WatchdogMonitor.tla)
KillIsIrreversible ==
    watchdog_state = "KILLED" =>
        [][watchdog_state' = "KILLED"]_vars

\* 7. ONLY COMPLETED COMMITTED: only COMPLETED tasks are in committed set
\*    (from SpeculationModel.tla)
OnlyCompletedCommitted ==
    \A t \in committed : task_status[t] = "COMPLETED"

\* 8. L0 GATE: execution requires L0 pass
\*    (cross-component: AxiomValidation + TaskStateMachine)
ExecutionRequiresL0Pass ==
    \A t \in Tasks :
        task_status[t] = "RUNNING" => l0_result[t] = "PASS"

\* 9. NO DEADLOCK: system can always take a step or all tasks terminal
NoDeadlock ==
    (\A t \in Tasks : task_status[t] \in {"COMPLETED", "FAILED", "REJECTED_BY_L0", "SKIPPED", "ROLLED_BACK"})
    \/ ENABLED(Next)

\* ─── Liveness ───

\* Pipeline eventually terminates
PipelineTermination ==
    <>(\A t \in Tasks :
        task_status[t] \in {"COMPLETED", "FAILED", "REJECTED_BY_L0", "SKIPPED", "ROLLED_BACK"})

\* ─── Theorems ───
THEOREM Spec => []TypeOK
THEOREM Spec => []AxiomSafety
THEOREM Spec => []CriticalAlwaysHumanApproved
THEOREM Spec => []TraceChainIntegrity
THEOREM Spec => []RolledBackNotCommitted
THEOREM Spec => []GuardedHasCheckpoint
THEOREM Spec => []OnlyCompletedCommitted
THEOREM Spec => []ExecutionRequiresL0Pass
THEOREM Spec => []NoDeadlock
THEOREM Spec => PipelineTermination

================================================================================
