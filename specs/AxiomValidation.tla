---------------------------- MODULE AxiomValidation ----------------------------
(*
 * Kovrin v2 — Layer 0 Axiom Validation
 *
 * Models the all-or-nothing constitutional check. Every sub-task must
 * pass ALL 5 axioms to be approved. Missing axioms default to FAIL.
 *
 * Maps to: src/kovrin/core/constitutional.py (ConstitutionalCore)
 *          src/kovrin/core/models.py (ProofObligation)
 *)

EXTENDS Naturals, FiniteSets

CONSTANTS
    Tasks,          \* Set of task IDs
    NumAxioms       \* Number of axioms (= 5)

VARIABLES
    axiom_results,  \* Function: (task, axiom_id) -> {"PASS", "FAIL", "MISSING"}
    task_approved,  \* Function: task -> BOOLEAN
    task_executed    \* Set of tasks that have started execution

Axioms == 1..NumAxioms
ResultValues == {"PASS", "FAIL", "MISSING"}

TypeOK ==
    /\ axiom_results \in [Tasks \X Axioms -> ResultValues]
    /\ task_approved \in [Tasks -> BOOLEAN]
    /\ task_executed \subseteq Tasks

\* ─── Initial State ───
Init ==
    /\ axiom_results = [p \in Tasks \X Axioms |-> "MISSING"]
    /\ task_approved = [t \in Tasks |-> FALSE]
    /\ task_executed = {}

\* ─── Axiom Check ───

\* Set result for one axiom of one task
SetAxiomResult(t, a, result) ==
    /\ axiom_results' = [axiom_results EXCEPT ![<<t, a>>] = result]
    /\ UNCHANGED <<task_approved, task_executed>>

\* Finalize check: approve only if ALL axioms passed
\* Missing axioms count as FAIL (fail-safe)
FinalizeCheck(t) ==
    LET all_pass == \A a \in Axioms : axiom_results[<<t, a>>] = "PASS"
    IN /\ task_approved' = [task_approved EXCEPT ![t] = all_pass]
       /\ UNCHANGED <<axiom_results, task_executed>>

\* Execute task (only if approved)
ExecuteTask(t) ==
    /\ task_approved[t] = TRUE
    /\ task_executed' = task_executed \cup {t}
    /\ UNCHANGED <<axiom_results, task_approved>>

\* ─── Next-State ───
Next ==
    \E t \in Tasks :
        \/ \E a \in Axioms, r \in {"PASS", "FAIL"} : SetAxiomResult(t, a, r)
        \/ FinalizeCheck(t)
        \/ ExecuteTask(t)

vars == <<axiom_results, task_approved, task_executed>>
Spec == Init /\ [][Next]_vars

\* ─── Safety Invariants ───

\* CRITICAL: Only approved tasks can execute
OnlyApprovedExecute ==
    \A t \in task_executed : task_approved[t] = TRUE

\* Approval requires ALL axioms to pass
ApprovalRequiresAll ==
    \A t \in Tasks :
        task_approved[t] = TRUE =>
            \A a \in Axioms : axiom_results[<<t, a>>] = "PASS"

\* Missing axioms prevent approval (fail-safe)
MissingAxiomPreventsApproval ==
    \A t \in Tasks :
        (\E a \in Axioms : axiom_results[<<t, a>>] = "MISSING") =>
            task_approved[t] = FALSE

\* No task with ANY failed axiom can execute
NoFailedAxiomExecutes ==
    \A t \in task_executed :
        \A a \in Axioms : axiom_results[<<t, a>>] = "PASS"

\* ─── Theorems ───
THEOREM Spec => []OnlyApprovedExecute
THEOREM Spec => []ApprovalRequiresAll
THEOREM Spec => []MissingAxiomPreventsApproval
THEOREM Spec => []NoFailedAxiomExecutes

================================================================================
