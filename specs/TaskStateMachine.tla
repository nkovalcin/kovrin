---------------------------- MODULE TaskStateMachine ----------------------------
(*
 * Kovrin v2 — Task Lifecycle State Machine
 *
 * Models the state transitions of sub-tasks through the execution pipeline.
 * Verifies that rejected tasks never execute, completed tasks were previously
 * executing, and all tasks eventually reach a terminal state.
 *
 * Maps to: src/kovrin/core/models.py (TaskStatus enum)
 *          src/kovrin/engine/graph.py (GraphNode, ExecutionGraph)
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Tasks,          \* Set of task IDs (e.g., {"t1", "t2", "t3"})
    Dependencies    \* Function: task -> set of dependency task IDs

VARIABLES
    status,         \* Function: task -> Status
    executed,       \* Set of tasks that have entered EXECUTING state
    rejected        \* Set of tasks rejected by L0

\* Task status values (matching Python TaskStatus enum)
Status == {"PENDING", "READY", "EXECUTING", "COMPLETED",
           "FAILED", "REJECTED_BY_L0", "AWAITING_HUMAN", "SKIPPED"}

\* Terminal states — no further transitions allowed
Terminal == {"COMPLETED", "FAILED", "REJECTED_BY_L0", "SKIPPED"}

\* Type invariant
TypeOK ==
    /\ status \in [Tasks -> Status]
    /\ executed \subseteq Tasks
    /\ rejected \subseteq Tasks

\* ─── Initial State ───
Init ==
    /\ status = [t \in Tasks |-> "PENDING"]
    /\ executed = {}
    /\ rejected = {}

\* ─── State Transitions ───

\* Dependencies satisfied → PENDING to READY
BecomeReady(t) ==
    /\ status[t] = "PENDING"
    /\ \A dep \in Dependencies[t] : status[dep] = "COMPLETED"
    /\ status' = [status EXCEPT ![t] = "READY"]
    /\ UNCHANGED <<executed, rejected>>

\* READY → EXECUTING
StartExecution(t) ==
    /\ status[t] = "READY"
    /\ status' = [status EXCEPT ![t] = "EXECUTING"]
    /\ executed' = executed \cup {t}
    /\ UNCHANGED <<rejected>>

\* EXECUTING → COMPLETED
Complete(t) ==
    /\ status[t] = "EXECUTING"
    /\ status' = [status EXCEPT ![t] = "COMPLETED"]
    /\ UNCHANGED <<executed, rejected>>

\* EXECUTING → FAILED (+ cascade skip dependents)
Fail(t) ==
    /\ status[t] = "EXECUTING"
    /\ status' = [s \in Tasks |->
        IF s = t THEN "FAILED"
        ELSE IF status[s] = "PENDING" /\ t \in Dependencies[s] THEN "SKIPPED"
        ELSE status[s]]
    /\ UNCHANGED <<executed, rejected>>

\* PENDING → REJECTED_BY_L0 (L0 check fails)
RejectByL0(t) ==
    /\ status[t] = "PENDING"
    /\ status' = [s \in Tasks |->
        IF s = t THEN "REJECTED_BY_L0"
        ELSE IF status[s] = "PENDING" /\ t \in Dependencies[s] THEN "SKIPPED"
        ELSE status[s]]
    /\ rejected' = rejected \cup {t}
    /\ UNCHANGED <<executed>>

\* PENDING → SKIPPED (dependency failed or rejected)
Skip(t) ==
    /\ status[t] = "PENDING"
    /\ \E dep \in Dependencies[t] : status[dep] \in {"FAILED", "REJECTED_BY_L0", "SKIPPED"}
    /\ status' = [status EXCEPT ![t] = "SKIPPED"]
    /\ UNCHANGED <<executed, rejected>>

\* ─── Next-State Relation ───
Next ==
    \E t \in Tasks :
        \/ BecomeReady(t)
        \/ StartExecution(t)
        \/ Complete(t)
        \/ Fail(t)
        \/ RejectByL0(t)
        \/ Skip(t)

\* ─── Specification ───
vars == <<status, executed, rejected>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ─── Safety Invariants ───

\* CRITICAL: Rejected tasks must NEVER execute
AxiomSafety == rejected \cap executed = {}

\* A completed task must have been through EXECUTING
CompletedWasExecuting ==
    \A t \in Tasks : status[t] = "COMPLETED" => t \in executed

\* No task is in two terminal states simultaneously (implicit from function)
\* Tasks in terminal states don't transition further (enforced by guards)

\* ─── Liveness Properties ───

\* Every task eventually reaches a terminal state
EventualTermination ==
    \A t \in Tasks : <>(status[t] \in Terminal)

\* ─── Theorems ───
THEOREM Spec => []AxiomSafety
THEOREM Spec => []CompletedWasExecuting
THEOREM Spec => EventualTermination

================================================================================
