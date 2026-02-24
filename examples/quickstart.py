"""Kovrin quickstart — run a safety-gated AI pipeline in 10 lines."""

from kovrin import Kovrin

engine = Kovrin(tools=True)
result = engine.run_sync(
    intent="Search for Python 3.13 features and summarize them",
    constraints=["Be concise", "Focus on developer-relevant features"],
)

print(f"Success: {result.success}")
print(f"Tasks: {len(result.sub_tasks)} completed, {len(result.rejected_tasks)} rejected")
print(f"\n{result.output}")
