"""
Kovrin MCTS Decomposition Explorer

Generates multiple candidate decompositions via Monte Carlo Tree Search.
Each iteration:
1. SELECT: Traverse tree using UCB1 to find promising node
2. EXPAND: Generate a new decomposition variant from that node
3. EVALUATE: Score via CriticPipeline pass rate
4. BACKPROPAGATE: Update scores up the tree

The result is the highest-scoring decomposition(s) for beam search.
"""

import json
import math
import time
from typing import Protocol

import anthropic

from kovrin.core.models import (
    DecompositionCandidate,
    MCTSNode,
    SubTask,
)
from kovrin.intent.parser import IntentParser
from kovrin.intent.schema import IntentV2


class DecompositionScorer(Protocol):
    """Protocol for scoring a decomposition candidate."""

    async def score(
        self,
        candidate: DecompositionCandidate,
        constraints: list[str],
        intent_context: str,
        task_context: dict | None,
    ) -> float: ...


class CriticBasedScorer:
    """Scores decompositions by running CriticPipeline on each subtask."""

    def __init__(self, critics):
        self._critics = critics

    async def score(
        self,
        candidate: DecompositionCandidate,
        constraints: list[str],
        intent_context: str,
        task_context: dict | None,
    ) -> float:
        if not candidate.subtasks:
            return 0.0

        passed = 0
        for subtask in candidate.subtasks:
            ok, _ = await self._critics.evaluate(
                subtask=subtask,
                constraints=constraints,
                intent_context=intent_context,
                task_context=task_context,
            )
            if ok:
                passed += 1

        rate = passed / len(candidate.subtasks)
        candidate.critic_pass_rate = rate
        task_penalty = max(0, len(candidate.subtasks) - 8) * 0.05
        candidate.score = max(0.0, rate - task_penalty)
        return candidate.score


# Prompt variant instructions for diverse decompositions
PROMPT_VARIANTS = [
    "default",
    "minimal",
    "fine_grained",
    "risk_conservative",
    "parallel_friendly",
]

_VARIANT_INSTRUCTIONS = {
    "default": "",
    "minimal": "\nIMPORTANT: Use the MINIMUM number of tasks possible. Combine related work into single tasks.",
    "fine_grained": "\nIMPORTANT: Break work into small, highly specific atomic tasks for maximum granularity.",
    "risk_conservative": "\nIMPORTANT: Prefer LOW risk approaches. Avoid irreversible actions. Use GUARDED or FREE tiers.",
    "parallel_friendly": "\nIMPORTANT: Maximize tasks that can run in parallel. Minimize dependencies between tasks.",
}


class MCTSExplorer:
    """MCTS-based decomposition explorer.

    Generates multiple candidate decompositions and selects
    the best one using UCB1 tree search.
    """

    def __init__(
        self,
        parser: IntentParser,
        scorer: DecompositionScorer,
        client: anthropic.AsyncAnthropic,
        exploration_constant: float = 1.414,
        max_iterations: int = 5,
        max_children: int = 3,
    ):
        self._parser = parser
        self._scorer = scorer
        self._client = client
        self._c = exploration_constant
        self._max_iterations = max_iterations
        self._max_children = max_children
        self._nodes: dict[str, MCTSNode] = {}

    async def explore(
        self,
        intent: IntentV2,
        constraints: list[str] | None = None,
        context: dict | None = None,
    ) -> tuple[DecompositionCandidate, list[DecompositionCandidate]]:
        """Run MCTS exploration and return (best, all_candidates).

        Returns:
            Tuple of (best_candidate, all_candidates_explored)
        """
        start = time.monotonic()
        constraints = constraints or []
        self._nodes.clear()

        # Root: generate initial decomposition with default parser
        root_subtasks = await self._parser.parse(intent)
        root_candidate = DecompositionCandidate(
            subtasks=root_subtasks,
            prompt_variant="default",
            temperature=1.0,
        )
        root_score = await self._scorer.score(
            root_candidate, constraints, intent.description, context
        )
        root_node = MCTSNode(
            candidate=root_candidate,
            visits=1,
            total_reward=root_score,
        )
        self._nodes[root_node.id] = root_node

        # MCTS iterations
        for i in range(self._max_iterations):
            # SELECT
            node = self._select(root_node)

            # EXPAND
            child = await self._expand(node, intent, constraints, context, i)
            if child is None:
                continue

            # EVALUATE (already done in _expand)
            reward = child.candidate.score

            # BACKPROPAGATE
            self._backpropagate(child, reward)

        # Collect all candidates
        all_candidates = [n.candidate for n in self._nodes.values()]
        best = max(all_candidates, key=lambda c: c.score)

        elapsed = (time.monotonic() - start) * 1000

        return best, all_candidates

    def _select(self, node: MCTSNode) -> MCTSNode:
        """Select a node to expand using UCB1."""
        current = node
        while current.children:
            children = [
                self._nodes[cid]
                for cid in current.children
                if cid in self._nodes
            ]
            if not children:
                break

            # Prefer unexplored children
            unexplored = [c for c in children if c.visits == 0]
            if unexplored:
                return unexplored[0]

            # UCB1 selection
            total_parent_visits = sum(c.visits for c in children)
            for child in children:
                exploit = child.total_reward / child.visits if child.visits > 0 else 0
                explore = self._c * math.sqrt(
                    math.log(max(total_parent_visits, 1)) / max(child.visits, 1)
                )
                child.ucb1_score = exploit + explore

            current = max(children, key=lambda c: c.ucb1_score)
        return current

    async def _expand(
        self,
        parent: MCTSNode,
        intent: IntentV2,
        constraints: list[str],
        context: dict | None,
        iteration: int,
    ) -> MCTSNode | None:
        """Expand by generating a new decomposition variant."""
        if len(parent.children) >= self._max_children:
            return None

        variant = PROMPT_VARIANTS[iteration % len(PROMPT_VARIANTS)]
        temperature = min(0.7 + (iteration * 0.1), 1.2)

        subtasks = await self._generate_variant(intent, variant, temperature)

        candidate = DecompositionCandidate(
            subtasks=subtasks,
            parent_id=parent.candidate.id,
            prompt_variant=variant,
            temperature=temperature,
        )

        await self._scorer.score(candidate, constraints, intent.description, context)

        child_node = MCTSNode(
            candidate=candidate,
            parent_id=parent.id,
            visits=1,
            total_reward=candidate.score,
        )
        self._nodes[child_node.id] = child_node
        parent.children.append(child_node.id)

        return child_node

    async def _generate_variant(
        self, intent: IntentV2, variant: str, temperature: float
    ) -> list[SubTask]:
        """Generate a decomposition variant with modified prompt/temperature."""
        extra = _VARIANT_INSTRUCTIONS.get(variant, "")

        constraints_text = (
            "\n".join(f"  - {c}" for c in intent.constraints)
            if intent.constraints
            else "  None"
        )
        context_text = (
            json.dumps(intent.context, indent=2, default=str)
            if intent.context
            else "  None"
        )

        prompt = f"""You are the intent decomposition engine for Kovrin, a safety-first AI orchestration framework.

Decompose this intent into concrete, executable sub-tasks.

INTENT: {intent.description}

CONSTRAINTS:
{constraints_text}

CONTEXT:
{context_text}

RULES:
1. Each sub-task must be specific and independently executable.
2. Assign RISK LEVEL: LOW, MEDIUM, HIGH, or CRITICAL.
3. Assign SPECULATION TIER: FREE, GUARDED, or NONE.
4. Define dependencies using task IDs (task_0, task_1, etc.).
5. Minimize unnecessary decomposition.
6. Respect ALL constraints.
{extra}

Respond with a JSON array. Return ONLY the JSON array."""

        response = await self._client.messages.create(
            model=self._parser.MODEL,
            max_tokens=2048,
            temperature=temperature,
            messages=[{"role": "user", "content": prompt}],
        )

        return self._parser._parse_response(response.content[0].text, intent.id)

    def _backpropagate(self, node: MCTSNode, reward: float) -> None:
        """Propagate reward up to root."""
        current_id = node.id
        while current_id:
            n = self._nodes.get(current_id)
            if not n:
                break
            n.visits += 1
            n.total_reward += reward
            current_id = n.parent_id

    @property
    def nodes(self) -> dict[str, MCTSNode]:
        """Access the MCTS tree nodes (for testing/inspection)."""
        return dict(self._nodes)
