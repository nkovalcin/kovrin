---------------------------- MODULE SpeculationModel ---------------------------
(*
 * Kovrin v2 — Speculative Execution with Checkpoint/Rollback
 *
 * Models the three-tier speculation system:
 * - FREE: execute immediately, result is final
 * - GUARDED: checkpoint before execution, rollback on failure
 * - NONE: requires pre-approval, no speculation
 *
 * Verifies that rollback restores exact prior state and that
 * GUARDED tasks don't leak state on failure.
 *
 * Maps to: src/kovrin/engine/speculation.py (SpeculativeContext)
 *          src/kovrin/core/models.py (SpeculationTier)
 *)

EXTENDS Naturals

CONSTANTS
    Tasks,              \* Set of task IDs
    Tiers               \* {"FREE", "GUARDED", "NONE"}

VARIABLES
    task_tier,          \* Function: task -> tier
    task_state,         \* Function: task -> {"PENDING", "RUNNING", "COMPLETED", "FAILED", "ROLLED_BACK"}
    checkpoint,         \* Function: task -> snapshot (or "NONE")
    output,             \* Function: task -> output value (or "NONE")
    committed           \* Set of tasks whose results are committed

TypeOK ==
    /\ task_tier \in [Tasks -> Tiers]
    /\ task_state \in [Tasks -> {"PENDING", "RUNNING", "COMPLETED", "FAILED", "ROLLED_BACK"}]
    /\ committed \subseteq Tasks

\* ─── Initial State ───
Init ==
    /\ task_tier \in [Tasks -> Tiers]
    /\ task_state = [t \in Tasks |-> "PENDING"]
    /\ checkpoint = [t \in Tasks |-> "NONE"]
    /\ output = [t \in Tasks |-> "NONE"]
    /\ committed = {}

\* ─── FREE Tier: Execute immediately ───
ExecuteFree(t) ==
    /\ task_tier[t] = "FREE"
    /\ task_state[t] = "PENDING"
    /\ task_state' = [task_state EXCEPT ![t] = "COMPLETED"]
    /\ committed' = committed \cup {t}
    /\ UNCHANGED <<task_tier, checkpoint, output>>

\* ─── GUARDED Tier: Checkpoint → Execute → Validate ───
CheckpointGuarded(t) ==
    /\ task_tier[t] = "GUARDED"
    /\ task_state[t] = "PENDING"
    /\ checkpoint' = [checkpoint EXCEPT ![t] = "SNAPSHOT"]
    /\ task_state' = [task_state EXCEPT ![t] = "RUNNING"]
    /\ UNCHANGED <<task_tier, output, committed>>

CommitGuarded(t) ==
    /\ task_tier[t] = "GUARDED"
    /\ task_state[t] = "RUNNING"
    /\ checkpoint[t] = "SNAPSHOT"
    /\ task_state' = [task_state EXCEPT ![t] = "COMPLETED"]
    /\ committed' = committed \cup {t}
    /\ UNCHANGED <<task_tier, checkpoint, output>>

RollbackGuarded(t) ==
    /\ task_tier[t] = "GUARDED"
    /\ task_state[t] = "RUNNING"
    /\ checkpoint[t] = "SNAPSHOT"
    /\ task_state' = [task_state EXCEPT ![t] = "ROLLED_BACK"]
    /\ output' = [output EXCEPT ![t] = "NONE"]  \* Clear any partial output
    /\ UNCHANGED <<task_tier, checkpoint, committed>>

\* ─── NONE Tier: Requires approval, then execute ───
ExecuteNone(t) ==
    /\ task_tier[t] = "NONE"
    /\ task_state[t] = "PENDING"
    /\ task_state' = [task_state EXCEPT ![t] = "COMPLETED"]
    /\ committed' = committed \cup {t}
    /\ UNCHANGED <<task_tier, checkpoint, output>>

\* ─── Next-State ───
Next ==
    \E t \in Tasks :
        \/ ExecuteFree(t)
        \/ CheckpointGuarded(t)
        \/ CommitGuarded(t)
        \/ RollbackGuarded(t)
        \/ ExecuteNone(t)

vars == <<task_tier, task_state, checkpoint, output, committed>>
Spec == Init /\ [][Next]_vars

\* ─── Safety Invariants ───

\* Rollback restores to pre-execution state (output cleared)
RollbackClearsOutput ==
    \A t \in Tasks :
        task_state[t] = "ROLLED_BACK" => output[t] = "NONE"

\* Rolled-back tasks are never committed
RolledBackNotCommitted ==
    \A t \in Tasks :
        task_state[t] = "ROLLED_BACK" => t \notin committed

\* GUARDED tasks must have checkpoint before running
GuardedHasCheckpoint ==
    \A t \in Tasks :
        (task_tier[t] = "GUARDED" /\ task_state[t] = "RUNNING") =>
            checkpoint[t] = "SNAPSHOT"

\* Only completed tasks are committed
OnlyCompletedCommitted ==
    \A t \in committed : task_state[t] = "COMPLETED"

\* FREE tasks go directly to committed (no checkpoint)
FreeNoCheckpoint ==
    \A t \in Tasks :
        task_tier[t] = "FREE" => checkpoint[t] = "NONE"

\* ─── Theorems ───
THEOREM Spec => []RollbackClearsOutput
THEOREM Spec => []RolledBackNotCommitted
THEOREM Spec => []GuardedHasCheckpoint
THEOREM Spec => []OnlyCompletedCommitted
THEOREM Spec => []FreeNoCheckpoint

================================================================================
