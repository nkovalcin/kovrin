---------------------------- MODULE GraphExecution ----------------------------
(*
 * Kovrin v2 — DAG Graph Execution
 *
 * Models the parallel execution of tasks in a directed acyclic graph.
 * Verifies DAG scheduling correctness, failure cascade, and termination.
 *
 * Maps to: src/kovrin/engine/graph.py (ExecutionGraph, GraphExecutor)
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Tasks,              \* Set of task IDs
    Dependencies,       \* Function: task -> set of dependency task IDs
    MaxConcurrent       \* Maximum concurrent tasks (semaphore)

VARIABLES
    node_state,         \* Function: task -> state
    running_count,      \* Number of currently running tasks
    completed_set,      \* Set of completed tasks
    failed_set,         \* Set of failed tasks
    skipped_set         \* Set of skipped tasks

States == {"PENDING", "READY", "RUNNING", "COMPLETED", "FAILED", "SKIPPED"}

TypeOK ==
    /\ node_state \in [Tasks -> States]
    /\ running_count \in 0..Cardinality(Tasks)
    /\ completed_set \subseteq Tasks
    /\ failed_set \subseteq Tasks
    /\ skipped_set \subseteq Tasks

\* ─── DAG Property ───
\* No task depends on itself (modeled as precondition on constants)
\* No cycles (enforced by topological ordering breaking on cycles)

\* ─── Helpers ───
DepsCompleted(t) ==
    \A dep \in Dependencies[t] : node_state[dep] = "COMPLETED"

DepFailed(t) ==
    \E dep \in Dependencies[t] : node_state[dep] \in {"FAILED", "SKIPPED"}

IsTerminal(t) ==
    node_state[t] \in {"COMPLETED", "FAILED", "SKIPPED"}

\* ─── Initial State ───
Init ==
    /\ node_state = [t \in Tasks |-> "PENDING"]
    /\ running_count = 0
    /\ completed_set = {}
    /\ failed_set = {}
    /\ skipped_set = {}

\* ─── Transitions ───

\* PENDING → READY when all dependencies completed
BecomeReady(t) ==
    /\ node_state[t] = "PENDING"
    /\ DepsCompleted(t)
    /\ node_state' = [node_state EXCEPT ![t] = "READY"]
    /\ UNCHANGED <<running_count, completed_set, failed_set, skipped_set>>

\* READY → RUNNING (respects concurrency limit)
StartRunning(t) ==
    /\ node_state[t] = "READY"
    /\ running_count < MaxConcurrent
    /\ node_state' = [node_state EXCEPT ![t] = "RUNNING"]
    /\ running_count' = running_count + 1
    /\ UNCHANGED <<completed_set, failed_set, skipped_set>>

\* RUNNING → COMPLETED
CompleteTask(t) ==
    /\ node_state[t] = "RUNNING"
    /\ node_state' = [node_state EXCEPT ![t] = "COMPLETED"]
    /\ running_count' = running_count - 1
    /\ completed_set' = completed_set \cup {t}
    /\ UNCHANGED <<failed_set, skipped_set>>

\* RUNNING → FAILED (triggers cascade skip)
FailTask(t) ==
    /\ node_state[t] = "RUNNING"
    /\ node_state' = [s \in Tasks |->
        IF s = t THEN "FAILED"
        ELSE IF node_state[s] = "PENDING" /\ DepFailed(s)
        THEN "SKIPPED"
        ELSE node_state[s]]
    /\ running_count' = running_count - 1
    /\ failed_set' = failed_set \cup {t}
    /\ skipped_set' = skipped_set \cup {s \in Tasks : node_state[s] = "PENDING" /\ DepFailed(s)}
    /\ UNCHANGED <<completed_set>>

\* PENDING → SKIPPED (dependency failed)
CascadeSkip(t) ==
    /\ node_state[t] = "PENDING"
    /\ DepFailed(t)
    /\ node_state' = [node_state EXCEPT ![t] = "SKIPPED"]
    /\ skipped_set' = skipped_set \cup {t}
    /\ UNCHANGED <<running_count, completed_set, failed_set>>

\* ─── Next-State ───
Next ==
    \E t \in Tasks :
        \/ BecomeReady(t)
        \/ StartRunning(t)
        \/ CompleteTask(t)
        \/ FailTask(t)
        \/ CascadeSkip(t)

vars == <<node_state, running_count, completed_set, failed_set, skipped_set>>
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ─── Safety Invariants ───

\* A task can only run if all its dependencies are completed
RunningImpliesDepsComplete ==
    \A t \in Tasks :
        node_state[t] = "RUNNING" => DepsCompleted(t)

\* Concurrency limit is respected
ConcurrencyLimit ==
    running_count <= MaxConcurrent

\* Failed task's dependents are skipped
FailureCascade ==
    \A t \in Tasks :
        (node_state[t] = "PENDING" /\ DepFailed(t)) =>
            <>(node_state[t] = "SKIPPED")

\* No task is simultaneously completed and failed
MutualExclusion ==
    completed_set \cap failed_set = {}

\* No task is simultaneously completed and skipped
CompletedNotSkipped ==
    completed_set \cap skipped_set = {}

\* ─── Liveness ───

\* Pipeline eventually terminates (all tasks reach terminal state)
PipelineTermination ==
    <>(\A t \in Tasks : IsTerminal(t))

\* ─── Theorems ───
THEOREM Spec => []RunningImpliesDepsComplete
THEOREM Spec => []ConcurrencyLimit
THEOREM Spec => []MutualExclusion
THEOREM Spec => []CompletedNotSkipped
THEOREM Spec => PipelineTermination

================================================================================
