# Kovrin

**Safety-First Intent-Based AI Orchestration Framework**

> Formerly LATTICE — Language for Autonomous Thinking, Transformation, and Intelligent Coordination at Emergent Scale

Kovrin is an open-source framework for safe, intent-based AI orchestration where formal verification, constitutional constraints, and cryptographic audit trails are **architectural guarantees** — not runtime afterthoughts.

## Quick Start

```bash
git clone https://github.com/YOUR_USERNAME/kovrin.git
cd kovrin
pip install -e .
export ANTHROPIC_API_KEY=your_key_here
```

```python
from kovrin import Kovrin

engine = Kovrin()
result = engine.run(
    intent="Analyze our monthly expenses and suggest 3 cost-saving measures",
    constraints=["Do not suggest layoffs", "Maintain service quality"],
    context={"monthly_budget": 15000, "team_size": 12}
)
```

## Architecture

```
Intent → HTN Decomposition → Layer 0 Constitutional Check → Risk Routing → Execution → Audit
                                    │                            │              │
                              5 Axioms (immutable)        FREE/GUARDED/NONE   Merkle Hash Chain
                              All-or-nothing              Risk × Tier Matrix   Tamper-evident
```

### Layer 0 — Constitutional Core

5 immutable ethical axioms checked **before** every action:

| Axiom | Guarantee |
|-------|-----------|
| Human Agency | No action removes human override ability |
| Harm Floor | Expected harm never exceeds threshold |
| Transparency | All decisions traceable to intent |
| Reversibility | Prefer reversible over irreversible |
| Scope Limit | Never exceed authorized boundary |

SHA-256 integrity hash. All-or-nothing — one axiom fails = task rejected. No exceptions.

### Key Components

- **Graph Execution Engine** — DAG-based parallel execution with failure cascade
- **Risk Router** — `(RiskLevel × SpeculationTier) → RoutingAction` matrix. CRITICAL always → HUMAN_APPROVAL
- **Speculative Execution** — FREE (auto), GUARDED (checkpoint/rollback), NONE (human approval)
- **LLM-Modulo Critics** — Safety, Feasibility, Policy critics validate every task
- **Watchdog Agent** — Independent monitor with temporal rules and graduated containment (WARN → PAUSE → KILL)
- **Merkle Audit Trail** — SHA-256 hash chain, append-only, tamper-evident
- **MCTS + Beam Search** — Multi-path decision exploration before commitment
- **Process Reward Models** — Step-level alignment scoring
- **Delegation Capability Tokens** — HMAC-SHA256 signed, scope narrowing, cascading revocation
- **TLA+ Formal Verification** — 8 modules, 10 safety invariants, machine-checked proofs

## Testing

```bash
pip install -e ".[dev]"
pytest tests/ -v          # 480 tests
pytest -m adversarial     # 41 adversarial attack tests
```

## Project Structure

```
src/kovrin/
├── core/           # Models, Constitutional Core (Layer 0)
├── intent/         # IntentV2 schema, HTN parser
├── engine/         # Graph executor, risk router, MCTS, beam search, speculation, PRM, tokens, topology
├── safety/         # Critics pipeline, watchdog agent
├── audit/          # Immutable trace logger (Merkle chain)
├── agents/         # Agent coordinator, registry
├── api/            # FastAPI server
├── schema/         # JSON Schema + TypeScript exporter
└── storage/        # Persistence layer

specs/              # TLA+ formal verification (8 modules)
dashboard/          # React/TypeScript dashboard
docs/               # Whitepaper, competitive analysis
tests/              # 480 tests (unit + adversarial + integration)
```

## Schema Export

```bash
python -m kovrin.schema.exporter --list                    # List 29 models, 13 enums
python -m kovrin.schema.exporter --json-schema schemas/    # Export JSON Schema
python -m kovrin.schema.exporter --typescript types.ts     # Generate TypeScript
python -m kovrin.schema.exporter --validate existing.ts    # Detect drift
```

## License

MIT

## Author

Built by [Norbert Kovalčín](https://nkovalcin.com) — AI Engineer & Digital Solutions Architect, DIGITAL SPECIALISTS s.r.o.

---

*"The question isn't whether we'll build AGI. The question is whether we'll build the safety infrastructure first."*
