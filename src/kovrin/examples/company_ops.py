"""
Kovrin Example — Company Operations

Demonstrates the full Kovrin pipeline:
1. Define an intent with constraints and context
2. Automatic decomposition into sub-tasks
3. Constitutional validation (Layer 0)
4. Risk-based routing
5. Parallel execution
6. Immutable audit trail

Usage:
    python -m kovrin.examples.company_ops
"""

import asyncio

from kovrin import Kovrin


async def main():
    print("=" * 60)
    print("Kovrin v2 — Company Operations Example")
    print("=" * 60)

    engine = Kovrin()

    result = await engine.run(
        intent="Analyze our monthly expenses and suggest 3 cost-saving measures",
        constraints=[
            "Do not suggest layoffs or salary cuts",
            "Maintain current service quality",
            "Focus on operational costs only",
        ],
        context={
            "monthly_budget": 15000,
            "team_size": 12,
            "industry": "software development",
            "major_expenses": [
                "cloud infrastructure (AWS): $4,500/mo",
                "SaaS tools and licenses: $2,800/mo",
                "office rent: $3,200/mo",
                "contractor fees: $2,500/mo",
                "misc operational: $2,000/mo",
            ],
        },
    )

    print("\n" + "=" * 60)
    print("EXECUTION RESULT")
    print("=" * 60)
    print(f"Success: {result.success}")
    print(f"Intent ID: {result.intent_id}")
    print(f"Total sub-tasks: {len(result.sub_tasks)}")
    print(f"Rejected tasks: {len(result.rejected_tasks)}")
    print(f"Trace events: {len(result.traces)}")

    if result.rejected_tasks:
        print(f"\nRejected tasks:")
        for task in result.rejected_tasks:
            failed = [o for o in task.proof_obligations if not o.passed]
            print(f"  - {task.description[:60]}")
            for o in failed:
                print(f"    FAILED: {o.axiom_name} — {o.evidence[:80]}")

    print(f"\n{'='*60}")
    print("OUTPUT")
    print("=" * 60)
    print(result.output[:3000] if result.output else "No output")


if __name__ == "__main__":
    asyncio.run(main())
