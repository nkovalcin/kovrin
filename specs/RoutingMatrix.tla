---------------------------- MODULE RoutingMatrix ----------------------------
(*
 * Kovrin v2 — Risk-Based Routing Matrix
 *
 * Models the deterministic routing of sub-tasks based on risk level
 * and speculation tier. Verifies that CRITICAL tasks ALWAYS require
 * human approval, regardless of autonomy profile or cell overrides.
 *
 * Maps to: src/kovrin/engine/risk_router.py (RiskRouter)
 *)

EXTENDS Naturals

CONSTANTS
    RiskLevels,         \* {"LOW", "MEDIUM", "HIGH", "CRITICAL"}
    SpeculationTiers,   \* {"FREE", "GUARDED", "NONE"}
    RoutingActions,     \* {"AUTO_EXECUTE", "SANDBOX_REVIEW", "HUMAN_APPROVAL"}
    AutonomyProfiles    \* {"DEFAULT", "CAUTIOUS", "AGGRESSIVE", "LOCKED"}

VARIABLES
    risk_level,         \* Current task's risk level
    speculation_tier,   \* Current task's speculation tier
    autonomy_profile,   \* Active autonomy profile
    cell_override,      \* Cell-level override action (or "NONE" for no override)
    routed_action       \* Resulting routing action

\* ─── Default Routing Matrix ───
DefaultRoute(risk, tier) ==
    CASE risk = "LOW"      /\ tier = "FREE"    -> "AUTO_EXECUTE"
      [] risk = "LOW"      /\ tier = "GUARDED" -> "AUTO_EXECUTE"
      [] risk = "LOW"      /\ tier = "NONE"    -> "SANDBOX_REVIEW"
      [] risk = "MEDIUM"   /\ tier = "FREE"    -> "AUTO_EXECUTE"
      [] risk = "MEDIUM"   /\ tier = "GUARDED" -> "SANDBOX_REVIEW"
      [] risk = "MEDIUM"   /\ tier = "NONE"    -> "HUMAN_APPROVAL"
      [] risk = "HIGH"     /\ tier = "FREE"    -> "SANDBOX_REVIEW"
      [] risk = "HIGH"     /\ tier = "GUARDED" -> "HUMAN_APPROVAL"
      [] risk = "HIGH"     /\ tier = "NONE"    -> "HUMAN_APPROVAL"
      [] risk = "CRITICAL" /\ tier = "FREE"    -> "HUMAN_APPROVAL"
      [] risk = "CRITICAL" /\ tier = "GUARDED" -> "HUMAN_APPROVAL"
      [] risk = "CRITICAL" /\ tier = "NONE"    -> "HUMAN_APPROVAL"

\* ─── Apply Profile Override ───
ProfileOverride(profile, risk, tier, base) ==
    IF profile = "LOCKED"
    THEN "HUMAN_APPROVAL"
    ELSE IF profile = "AGGRESSIVE"
    THEN CASE risk = "HIGH"   /\ tier = "FREE"    -> "AUTO_EXECUTE"
           [] risk = "HIGH"   /\ tier = "GUARDED" -> "SANDBOX_REVIEW"
           [] risk = "MEDIUM" /\ tier = "NONE"    -> "SANDBOX_REVIEW"
           [] risk = "LOW"    /\ tier = "NONE"    -> "AUTO_EXECUTE"
           [] OTHER                               -> base
    ELSE IF profile = "CAUTIOUS"
    THEN CASE risk = "HIGH"   /\ tier = "FREE"    -> "HUMAN_APPROVAL"
           [] risk = "MEDIUM" /\ tier = "GUARDED" -> "HUMAN_APPROVAL"
           [] risk = "MEDIUM" /\ tier = "FREE"    -> "SANDBOX_REVIEW"
           [] OTHER                               -> base
    ELSE base  \* DEFAULT profile

\* ─── Route Task ───
\* Complete routing: base matrix → profile → cell override → CRITICAL guard
RouteTask(risk, tier, profile, override) ==
    LET base     == DefaultRoute(risk, tier)
        profiled == ProfileOverride(profile, risk, tier, base)
        celled   == IF override \in RoutingActions THEN override ELSE profiled
    IN  \* CRITICAL SAFETY GUARD: unconditional, applied LAST
        IF risk = "CRITICAL"
        THEN "HUMAN_APPROVAL"
        ELSE celled

\* ─── Initial State ───
Init ==
    /\ risk_level \in RiskLevels
    /\ speculation_tier \in SpeculationTiers
    /\ autonomy_profile \in AutonomyProfiles
    /\ cell_override \in RoutingActions \cup {"NONE"}
    /\ routed_action = RouteTask(risk_level, speculation_tier, autonomy_profile, cell_override)

\* ─── Next-State: try all combinations ───
Route ==
    /\ risk_level' \in RiskLevels
    /\ speculation_tier' \in SpeculationTiers
    /\ autonomy_profile' \in AutonomyProfiles
    /\ cell_override' \in RoutingActions \cup {"NONE"}
    /\ routed_action' = RouteTask(risk_level', speculation_tier', autonomy_profile', cell_override')

Next == Route
vars == <<risk_level, speculation_tier, autonomy_profile, cell_override, routed_action>>
Spec == Init /\ [][Next]_vars

\* ─── Safety Invariants ───

\* CRITICAL INVARIANT: CRITICAL tasks ALWAYS require HUMAN_APPROVAL
\* Regardless of autonomy profile, cell overrides, or any other setting.
\* This models the unconditional guard at risk_router.py lines 98-99.
CriticalAlwaysHumanApproved ==
    risk_level = "CRITICAL" => routed_action = "HUMAN_APPROVAL"

\* Routing is deterministic: same inputs always produce same output
\* (This is implicit in functional definition — no nondeterminism in RouteTask)

\* Routing always produces a valid action
ValidAction ==
    routed_action \in RoutingActions

\* LOCKED profile always requires human approval for everything
LockedAlwaysHumanApproved ==
    (autonomy_profile = "LOCKED" /\ risk_level # "CRITICAL") =>
        routed_action = "HUMAN_APPROVAL"

\* ─── Theorems ───
THEOREM Spec => []CriticalAlwaysHumanApproved
THEOREM Spec => []ValidAction
THEOREM Spec => []LockedAlwaysHumanApproved

================================================================================
