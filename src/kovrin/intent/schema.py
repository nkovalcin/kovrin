"""
Kovrin v2 Intent Schema

Intents in Kovrin v2 are expressed as AMR-inspired graph structures
with speech act performatives, semantic frames, and contextual metadata.

This draws from six philosophical/linguistic traditions:
- Wittgenstein's language games (context-dependent meaning)
- Fodor's Language of Thought (compositionality, systematicity)
- AMR (who did what to whom as rooted DAGs)
- Speech Act Theory (performative types)
- Frame Semantics (structured role templates)
- Iverson's Notation as Tool of Thought (suggestive composability)
"""

import uuid
from datetime import datetime, timezone
from enum import Enum
from typing import Any

from pydantic import BaseModel, Field

from kovrin.core.models import RiskLevel, SpeculationTier


# ─── Speech Act Types (Austin/Searle) ───
class Performative(str, Enum):
    """What is done by expressing the intent.

    Based on FIPA-ACL performatives, simplified for
    AI orchestration contexts.
    """
    REQUEST = "REQUEST"       # Ask agent to perform action
    INFORM = "INFORM"         # Share information/data
    PROPOSE = "PROPOSE"       # Suggest a course of action
    QUERY = "QUERY"           # Request information
    CONFIRM = "CONFIRM"       # Verify/validate something
    REFUSE = "REFUSE"         # Decline a task (used by agents)
    AGREE = "AGREE"           # Accept a task (used by agents)


# ─── Semantic Frames (Fillmore) ───
class SemanticFrame(str, Enum):
    """Structured templates defining expected participants
    and outcomes for common operation types.
    """
    DATA_PROCESSING = "DATA_PROCESSING"
    ANALYSIS = "ANALYSIS"
    OPTIMIZATION = "OPTIMIZATION"
    GENERATION = "GENERATION"
    COMMUNICATION = "COMMUNICATION"
    MONITORING = "MONITORING"
    TRANSFORMATION = "TRANSFORMATION"
    VERIFICATION = "VERIFICATION"
    CUSTOM = "CUSTOM"


# ─── Intent Content Node (AMR-inspired) ───
class IntentNode(BaseModel):
    """A node in the AMR-inspired intent graph.

    Represents a concept (action, entity, property) with
    PropBank-style semantic roles linking to other nodes.
    """
    id: str = Field(default_factory=lambda: f"n-{uuid.uuid4().hex[:8]}")
    concept: str = Field(..., description="The concept this node represents (e.g., 'analyze-01', 'dataset', 'cost')")
    roles: dict[str, str | list[str]] = Field(
        default_factory=dict,
        description="PropBank-style roles: arg0 (agent), arg1 (patient/theme), purpose, manner, etc."
    )
    properties: dict[str, Any] = Field(default_factory=dict)


# ─── Precondition ───
class Precondition(BaseModel):
    """A condition that must hold before intent execution."""
    expression: str = Field(..., description="e.g., 'agent_has_capability(analyzer, data_processing)'")
    verified: bool = False
    verification_method: str = "runtime_check"


# ─── Expected Effect ───
class ExpectedEffect(BaseModel):
    """The desired state after successful intent execution."""
    state: str = Field(..., description="e.g., 'expenses_analyzed'")
    confidence_threshold: float = Field(0.8, ge=0.0, le=1.0)
    verification_criteria: list[str] = Field(default_factory=list)


# ─── Language Game Context (Wittgenstein) ───
class LanguageGameContext(BaseModel):
    """Contextual metadata specifying which operational domain
    governs interpretation of the intent.

    The same intent token can mean different things in different
    language games — 'optimize' means something different in
    ML training vs supply chain management.
    """
    game: str = Field(..., description="e.g., 'ml_pipeline', 'business_ops', 'software_dev'")
    ontology: str | None = Field(None, description="URI to domain ontology")
    authority_level: str = Field("direct", description="direct, delegated, or advisory")
    cultural_context: str | None = Field(None, description="e.g., 'enterprise_eu', 'startup_us'")


# ═══════════════════════════════════════════
# THE Kovrin v2 INTENT
# ═══════════════════════════════════════════
class IntentV2(BaseModel):
    """A Kovrin v2 Intent — the primary input to the system.

    Combines:
    - Speech act performative (what kind of communication)
    - Semantic frame (what category of operation)
    - AMR-inspired content graph (structured meaning)
    - Preconditions and expected effects (verification)
    - Language game context (interpretation rules)
    - Constraints (boundaries that must not be violated)

    This is dramatically richer than a string-based intent.
    It preserves meaning across agent boundaries and enables
    formal verification of intent compliance.
    """
    # Identity
    id: str = Field(default_factory=lambda: str(uuid.uuid4()))
    created_at: datetime = Field(default_factory=lambda: datetime.now(timezone.utc))

    # Speech Act (Austin/Searle)
    performative: Performative = Performative.REQUEST

    # Semantic Frame (Fillmore)
    frame: SemanticFrame = SemanticFrame.CUSTOM

    # Content (AMR-inspired graph)
    description: str = Field(..., description="Human-readable intent description")
    content_graph: list[IntentNode] = Field(
        default_factory=list,
        description="AMR-inspired graph of concepts and roles"
    )
    root_node_id: str | None = Field(None, description="ID of the root node in content graph")

    # Constraints
    constraints: list[str] = Field(default_factory=list)

    # Context
    context: dict[str, Any] = Field(default_factory=dict)
    language_game: LanguageGameContext | None = None

    # Verification
    preconditions: list[Precondition] = Field(default_factory=list)
    expected_effects: list[ExpectedEffect] = Field(default_factory=list)

    # Execution hints
    risk_level: RiskLevel | None = None
    speculation_tier: SpeculationTier | None = None
    max_decomposition_depth: int = Field(5, ge=1, le=20)
    timeout_seconds: int | None = None

    # Provenance
    parent_intent_id: str | None = Field(None, description="If this was decomposed from another intent")
    conversation_id: str | None = None

    @classmethod
    def simple(
        cls,
        description: str,
        constraints: list[str] | None = None,
        context: dict | None = None,
    ) -> "IntentV2":
        """Create a simple intent from a string — backward compatible with v1."""
        return cls(
            description=description,
            constraints=constraints or [],
            context=context or {},
        )

    @classmethod
    def structured(
        cls,
        description: str,
        performative: Performative = Performative.REQUEST,
        frame: SemanticFrame = SemanticFrame.CUSTOM,
        constraints: list[str] | None = None,
        context: dict | None = None,
        game: str = "general",
        preconditions: list[str] | None = None,
        expected_state: str | None = None,
    ) -> "IntentV2":
        """Create a structured intent with full metadata."""
        return cls(
            description=description,
            performative=performative,
            frame=frame,
            constraints=constraints or [],
            context=context or {},
            language_game=LanguageGameContext(game=game),
            preconditions=[Precondition(expression=p) for p in (preconditions or [])],
            expected_effects=[ExpectedEffect(state=expected_state)] if expected_state else [],
        )


# ─── Backward Compatibility ───
Intent = IntentV2  # Alias for v1 compatibility
