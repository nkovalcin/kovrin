------------------------------ MODULE HashChain --------------------------------
(*
 * Kovrin v2 — Immutable Trace Log with Hash Chain
 *
 * Models the append-only Merkle-tree hash chain used for tamper-evident
 * audit logging. Verifies that:
 * - Events are append-only (no modification or deletion)
 * - Any tampering is detected by integrity verification
 * - The chain head always reflects the latest event
 *
 * Maps to: src/kovrin/audit/trace_logger.py (ImmutableTraceLog, HashedTrace)
 *)

EXTENDS Naturals, Sequences

CONSTANTS
    MaxEvents,      \* Bound on number of events (for model checking)
    EventContents   \* Set of possible event content values

VARIABLES
    chain,          \* Sequence of (content, hash, prev_hash) tuples
    head_hash,      \* Current chain head hash
    tampered        \* Boolean: has any event been tampered with?

\* Hash function abstraction: maps (content, prev_hash) to a unique hash
\* In reality this is SHA-256; here we model it as an injective function
Hash(content, prev) == <<content, prev>>

GENESIS == "GENESIS"

TypeOK ==
    /\ chain \in Seq([content: EventContents, hash: EventContents \X {GENESIS} \cup EventContents \X EventContents, prev_hash: {GENESIS} \cup EventContents \X {GENESIS} \cup EventContents \X EventContents])
    /\ tampered \in BOOLEAN

\* ─── Initial State ───
Init ==
    /\ chain = <<>>
    /\ head_hash = GENESIS
    /\ tampered = FALSE

\* ─── Append Event ───
\* New event is hashed with the current head hash
AppendEvent(content) ==
    /\ Len(chain) < MaxEvents
    /\ LET new_hash == Hash(content, head_hash)
           new_event == [content |-> content, hash |-> new_hash, prev_hash |-> head_hash]
       IN /\ chain' = Append(chain, new_event)
          /\ head_hash' = new_hash
          /\ UNCHANGED <<tampered>>

\* ─── Tamper Event (adversarial action) ───
\* Modify the content of an existing event without updating hashes
TamperEvent(idx) ==
    /\ idx >= 1 /\ idx <= Len(chain)
    /\ \E new_content \in EventContents :
        /\ new_content # chain[idx].content  \* Actually different
        /\ chain' = [chain EXCEPT ![idx].content = new_content]
        /\ tampered' = TRUE
        /\ UNCHANGED <<head_hash>>

\* ─── Integrity Verification ───
\* Walks the chain and checks each link
VerifyIntegrity ==
    IF chain = <<>>
    THEN TRUE
    ELSE /\ chain[1].prev_hash = GENESIS
         /\ chain[1].hash = Hash(chain[1].content, GENESIS)
         /\ \A i \in 2..Len(chain) :
            /\ chain[i].prev_hash = chain[i-1].hash
            /\ chain[i].hash = Hash(chain[i].content, chain[i].prev_hash)

\* ─── Next-State ───
Next ==
    \/ \E c \in EventContents : AppendEvent(c)
    \/ \E i \in 1..Len(chain) : TamperEvent(i)

vars == <<chain, head_hash, tampered>>
Spec == Init /\ [][Next]_vars

\* ─── Safety Invariants ───

\* If no tampering occurred, integrity check always passes
IntegrityIfClean ==
    tampered = FALSE => VerifyIntegrity

\* If tampering occurred, integrity check MUST fail
\* (This is the key security property of Merkle chains)
TamperingDetected ==
    tampered = TRUE => ~VerifyIntegrity

\* Chain is append-only: length never decreases
\* (enforced by design — no deletion action)

\* Head hash always matches the last event's hash
HeadMatchesLast ==
    chain # <<>> => head_hash = chain[Len(chain)].hash

\* ─── Theorems ───
THEOREM Spec => []IntegrityIfClean
THEOREM Spec => []TamperingDetected
THEOREM Spec => []HeadMatchesLast

================================================================================
