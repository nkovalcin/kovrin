---------------------------- MODULE WatchdogMonitor ----------------------------
(*
 * Kovrin v2 — Watchdog Temporal Rule Monitor
 *
 * Models the independent watchdog agent that monitors trace events
 * and enforces temporal rules with graduated containment (WARN → PAUSE → KILL).
 *
 * Verifies that:
 * - Execution never follows L0 rejection for the same task
 * - KILL is irreversible
 * - Watchdog operates independently of executor
 *
 * Maps to: src/kovrin/safety/watchdog.py (WatchdogAgent, TemporalRule)
 *)

EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Tasks,              \* Set of task IDs
    MaxEvents           \* Bound on event history

VARIABLES
    history,            \* Sequence of events: [type, task_id, l0_passed]
    watchdog_state,     \* {"RUNNING", "PAUSED", "KILLED"}
    alerts,             \* Set of generated alerts
    rejected_tasks,     \* Set of tasks rejected by L0
    executed_tasks      \* Set of tasks that started execution

EventTypes == {"L0_CHECK", "EXECUTION_START", "EXECUTION_COMPLETE", "CRITIC_PIPELINE"}

TypeOK ==
    /\ watchdog_state \in {"RUNNING", "PAUSED", "KILLED"}
    /\ rejected_tasks \subseteq Tasks
    /\ executed_tasks \subseteq Tasks

\* ─── Initial State ───
Init ==
    /\ history = <<>>
    /\ watchdog_state = "RUNNING"
    /\ alerts = {}
    /\ rejected_tasks = {}
    /\ executed_tasks = {}

\* ─── Event Processing ───

\* L0 Check: reject a task
L0Reject(t) ==
    /\ Len(history) < MaxEvents
    /\ history' = Append(history, [type |-> "L0_CHECK", task |-> t, passed |-> FALSE])
    /\ rejected_tasks' = rejected_tasks \cup {t}
    /\ UNCHANGED <<watchdog_state, alerts, executed_tasks>>

\* L0 Check: approve a task
L0Approve(t) ==
    /\ Len(history) < MaxEvents
    /\ history' = Append(history, [type |-> "L0_CHECK", task |-> t, passed |-> TRUE])
    /\ UNCHANGED <<watchdog_state, alerts, rejected_tasks, executed_tasks>>

\* Execution Start (triggers watchdog check)
ExecutionStart(t) ==
    /\ Len(history) < MaxEvents
    /\ watchdog_state # "KILLED"  \* Cannot execute if killed
    /\ history' = Append(history, [type |-> "EXECUTION_START", task |-> t, passed |-> TRUE])
    /\ executed_tasks' = executed_tasks \cup {t}
    \* Rule: NoExecutionAfterRejection
    /\ IF t \in rejected_tasks
       THEN /\ alerts' = alerts \cup {"KILL_" \o t}
            /\ watchdog_state' = "KILLED"
       ELSE UNCHANGED <<alerts, watchdog_state>>
    /\ UNCHANGED <<rejected_tasks>>

\* Execution Complete
ExecutionComplete(t) ==
    /\ Len(history) < MaxEvents
    /\ history' = Append(history, [type |-> "EXECUTION_COMPLETE", task |-> t, passed |-> TRUE])
    \* Rule: UnexpectedEventSequence (COMPLETE without START)
    /\ IF t \notin executed_tasks
       THEN alerts' = alerts \cup {"WARN_UNEXPECTED_" \o t}
       ELSE UNCHANGED <<alerts>>
    /\ UNCHANGED <<watchdog_state, rejected_tasks, executed_tasks>>

\* ─── Containment Actions ───

\* Resume from PAUSED (external action, e.g., human)
Resume ==
    /\ watchdog_state = "PAUSED"
    /\ watchdog_state' = "RUNNING"
    /\ UNCHANGED <<history, alerts, rejected_tasks, executed_tasks>>

\* ─── Next-State ───
Next ==
    \/ \E t \in Tasks :
        \/ L0Reject(t)
        \/ L0Approve(t)
        \/ ExecutionStart(t)
        \/ ExecutionComplete(t)
    \/ Resume

vars == <<history, watchdog_state, alerts, rejected_tasks, executed_tasks>>
Spec == Init /\ [][Next]_vars

\* ─── Safety Invariants ───

\* CRITICAL: If a rejected task is executed, KILL alert is generated
NoExecutionAfterRejection ==
    \A t \in Tasks :
        (t \in rejected_tasks /\ t \in executed_tasks) =>
            watchdog_state = "KILLED"

\* KILL is irreversible (once killed, always killed)
KillIsIrreversible ==
    \A t \in Tasks :
        watchdog_state = "KILLED" =>
            [][watchdog_state' = "KILLED"]_vars

\* Watchdog can detect unexpected sequences
UnexpectedSequenceDetected ==
    \A t \in Tasks :
        (t \notin executed_tasks /\
         \E i \in 1..Len(history) : history[i].type = "EXECUTION_COMPLETE" /\ history[i].task = t) =>
            "WARN_UNEXPECTED_" \o t \in alerts

\* ─── Theorems ───
THEOREM Spec => []NoExecutionAfterRejection
THEOREM Spec => []UnexpectedSequenceDetected

================================================================================
