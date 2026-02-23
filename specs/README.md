# Kovrin v2 — TLA+ Formal Specifications

Machine-checked safety proofs for the Kovrin orchestration framework.

## Modules

| Module | What it models | Key invariants |
|--------|---------------|----------------|
| `TaskStateMachine.tla` | Task lifecycle (PENDING → COMPLETED/FAILED) | AxiomSafety, CompletedWasExecuting |
| `AxiomValidation.tla` | L0 all-or-nothing constitutional check | OnlyApprovedExecute, MissingAxiomPreventsApproval |
| `RoutingMatrix.tla` | Risk × Tier routing with profile overrides | CriticalAlwaysHumanApproved, LockedAlwaysHumanApproved |
| `GraphExecution.tla` | DAG parallel execution with semaphore | RunningImpliesDepsComplete, ConcurrencyLimit, PipelineTermination |
| `WatchdogMonitor.tla` | Temporal rule monitoring, graduated containment | NoExecutionAfterRejection, KillIsIrreversible |
| `SpeculationModel.tla` | FREE/GUARDED/NONE tiers, checkpoint/rollback | RollbackClearsOutput, GuardedHasCheckpoint |
| `HashChain.tla` | Append-only Merkle hash chain | IntegrityIfClean, TamperingDetected |
| `KovrinSafety.tla` | **Top-level composition** of all invariants | AxiomSafety, CriticalRouting, TraceIntegrity, NoDeadlock |

## Prerequisites

Install the TLA+ Toolbox or use the VS Code extension:

- **TLA+ Toolbox**: https://lamport.azurewebsites.net/tla/toolbox.html
- **VS Code extension**: `alygin.vscode-tlaplus`
- **CLI (TLC)**: https://github.com/tlaplus/tlaplus/releases

## Running the Model Checker

### Option 1: TLA+ Toolbox (GUI)

1. Open the Toolbox → File → Open Spec → Add New Spec
2. Select any `.tla` file
3. TLC Model Checker → New Model
4. Set constants (see bounds below)
5. Add invariants to check
6. Run

### Option 2: Command Line (TLC)

```bash
# Download tla2tools.jar from GitHub releases
java -jar tla2tools.jar -config TaskStateMachine.cfg TaskStateMachine.tla
```

### Option 3: VS Code

1. Install `alygin.vscode-tlaplus`
2. Open `.tla` file
3. Cmd+Shift+P → "TLA+: Check model with TLC"

## Model Checking Bounds

Small state space for tractable checking:

| Constant | Recommended value | Notes |
|----------|------------------|-------|
| `Tasks` | `{"t1", "t2", "t3"}` | 3 tasks covers all interaction patterns |
| `NumAxioms` | `5` | Matches Kovrin's 5 constitutional axioms |
| `MaxEvents` | `6` | 2× task count for trace logs |
| `MaxConcurrent` | `2` | Tests semaphore with contention |
| `Dependencies` | `[t1 |-> {}, t2 |-> {"t1"}, t3 |-> {"t2"}]` | Linear chain |
| `RiskLevels` | `{"LOW", "MEDIUM", "HIGH", "CRITICAL"}` | Full enumeration |
| `SpeculationTiers` | `{"FREE", "GUARDED", "NONE"}` | Full enumeration |
| `RoutingActions` | `{"AUTO_EXECUTE", "SANDBOX_REVIEW", "HUMAN_APPROVAL"}` | Full enumeration |
| `AutonomyProfiles` | `{"DEFAULT", "CAUTIOUS", "AGGRESSIVE", "LOCKED"}` | Full enumeration |
| `Tiers` | `{"FREE", "GUARDED", "NONE"}` | For SpeculationModel |
| `EventContents` | `{"e1", "e2", "e3"}` | For HashChain |

### SYMMETRY Optimization

For modules with `Tasks`, use SYMMETRY sets to reduce state space:

```tla
SYMMETRY Permutations(Tasks)
```

This reduces exploration by eliminating equivalent states where task IDs are permuted.

## Example TLC Configuration

### TaskStateMachine.cfg

```
CONSTANTS
    Tasks = {"t1", "t2", "t3"}
    Dependencies = [t1 |-> {}, t2 |-> {"t1"}, t3 |-> {"t2"}]

INVARIANTS
    TypeOK
    AxiomSafety
    CompletedWasExecuting

PROPERTIES
    EventualTermination
```

### RoutingMatrix.cfg

```
CONSTANTS
    RiskLevels = {"LOW", "MEDIUM", "HIGH", "CRITICAL"}
    SpeculationTiers = {"FREE", "GUARDED", "NONE"}
    RoutingActions = {"AUTO_EXECUTE", "SANDBOX_REVIEW", "HUMAN_APPROVAL"}
    AutonomyProfiles = {"DEFAULT", "CAUTIOUS", "AGGRESSIVE", "LOCKED"}

INVARIANTS
    CriticalAlwaysHumanApproved
    ValidAction
    LockedAlwaysHumanApproved
```

### KovrinSafety.cfg

```
CONSTANTS
    Tasks = {"t1", "t2", "t3"}
    MaxEvents = 6

INVARIANTS
    TypeOK
    AxiomSafety
    CriticalAlwaysHumanApproved
    TraceChainIntegrity
    RolledBackNotCommitted
    GuardedHasCheckpoint
    OnlyCompletedCommitted
    ExecutionRequiresL0Pass
    NoDeadlock

PROPERTIES
    PipelineTermination
```

## Invariant Summary

### Safety (always true)

| Invariant | Module | Property |
|-----------|--------|----------|
| AxiomSafety | TaskStateMachine, KovrinSafety | Rejected tasks never execute |
| CriticalAlwaysHumanApproved | RoutingMatrix, KovrinSafety | CRITICAL → HUMAN_APPROVAL unconditionally |
| OnlyApprovedExecute | AxiomValidation | Only L0-approved tasks can execute |
| MissingAxiomPreventsApproval | AxiomValidation | Missing axiom defaults to FAIL |
| RunningImpliesDepsComplete | GraphExecution | DAG ordering enforced |
| ConcurrencyLimit | GraphExecution | Semaphore respected |
| NoExecutionAfterRejection | WatchdogMonitor | Watchdog kills on rejected execution |
| RollbackClearsOutput | SpeculationModel | GUARDED rollback clears state |
| IntegrityIfClean | HashChain | Clean chain passes verification |
| TamperingDetected | HashChain | Tampered chain fails verification |

### Liveness (eventually true)

| Property | Module | Guarantee |
|----------|--------|-----------|
| EventualTermination | TaskStateMachine | All tasks reach terminal state |
| PipelineTermination | GraphExecution, KovrinSafety | Full pipeline completes |
| FailureCascade | GraphExecution | Failed task's dependents are skipped |

## Relationship to Python Implementation

Each TLA+ module maps to specific Python source files:

| TLA+ Module | Python Source |
|-------------|--------------|
| TaskStateMachine | `src/kovrin/core/models.py` (TaskStatus) |
| AxiomValidation | `src/kovrin/core/constitutional.py` (ConstitutionalCore) |
| RoutingMatrix | `src/kovrin/engine/risk_router.py` (RiskRouter) |
| GraphExecution | `src/kovrin/engine/graph.py` (GraphExecutor) |
| WatchdogMonitor | `src/kovrin/safety/watchdog.py` (WatchdogAgent) |
| SpeculationModel | `src/kovrin/engine/speculation.py` (SpeculativeContext) |
| HashChain | `src/kovrin/audit/trace_logger.py` (ImmutableTraceLog) |
| KovrinSafety | Full pipeline composition |

The TLA+ specs model the **abstract** safety properties. The Python implementation
is the **concrete** realization. Property-based tests (`tests/test_adversarial.py`)
bridge the gap by testing the Python code against the same invariants.
