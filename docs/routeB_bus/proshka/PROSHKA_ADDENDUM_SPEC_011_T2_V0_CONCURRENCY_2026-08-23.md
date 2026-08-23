# STATUS: CONDITIONAL — T2 LOCAL PLANTS PASS ACCEPTED; DURABLE CONTEXT-COHERENT MATCHER RECEIPT REMAINS OPEN

```yaml
PRIMARY: RATIFY_T2_V0_EXPERIMENTAL_PASS_AND_OPEN_T2_1_DURABLE_CONTEXT_GATE
OPERATIVE_CLASS: TRY_T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT
DOCUMENT_ROLE: CONCURRENCY_ADDENDUM_TO_SPEC_011_AUDIT

REPO: Malaeu/chen_q3
BRANCH: rh_clean
DATE: 2026-08-23

BASE_VERDICT:
  path: docs/routeB_bus/proshka/PROSHKA_VERDICT_SPEC_011_TYPED_DISCOVERY_COMPILER_AUDIT_2026-08-23.md
  commit: dbf09fa30c45ebc760f885b63e365965ece13a3c
  review_head_recorded: 4984a1071b6728ab64fee318ebaf0e3ee07bf5fb

CONCURRENT_REPORT:
  path: docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_V0_2026-08-23.md
  commit: 3a97a093dd40827c01e94df1be0fbc4142dc3cb7
  blob: fc6df3cd273dfc9485c5119b8d0135394e443018
  report_preceded_base_verdict_commit: true

RATIFIED_FROM_REPORT:
  P1_P5_CLASSIFICATIONS: PASS_5_OF_5
  NC1_NC2_POSITIVE_CONTROLS: PRESENT
  WRONG_OBJECT_ESCAPE_REPORTED: ZERO
  EXACT_TYPE_CAPTURE_FROM_CHECK: REPORTED_PASS
  LIVE_ROUTE_MUTATION: NONE
  CLOSED_GAP: T2_PORT_MATCHER_LOCAL_PLANTS

NOT_RATIFIED_AS_DURABLE_ENGINE:
  matcher_source_committed: false
  harnesses_committed: false
  schema_hash_receipt: absent
  fixture_manifest_hash: absent
  matcher_blob_receipt: absent
  shared_dependent_context_plant: absent
  evidence_bearing_refinement_schema: absent
  reproducible_release_gate: open

SEMANTIC_REPAIR:
  old_adapter_id: A_ISOMETRY_TO_POINTWISE_FOURIER
  corrected_adapter_id: A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE
  reason: CHECKED_THEOREM_CONCLUDES_AE_EQUALITY_NOT_POINTWISE_EQUALITY
  pointwise_consumer_status: ADAPTER_REQUIRED_OR_REFINEMENT_LOSS

NEXT_LOAD_BEARING_GAP:
  T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT

T3_TYPED_GAP_INTEGRATION:
  status: HOLD_UNTIL_T2_1
  reason: SESSION_MATCHER_AND_UNHASHED_REGISTRY_ARE_NOT_A_DURABLE_INPUT_TO_CHEAP_PY

CLOSES:
  - T2_PORT_MATCHER_LOCAL_PLANTS
  - NEGATIVE_ONLY_TEST_SUITE_CONCERN
  - CONCURRENCY_RECEIPT_AMBIGUITY

OPENS:
  - T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT

SCOPE: FINITE_CELL
VERIFIER: PAPER
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

EXECUTION_AUTHORIZED_BY_THIS_FILE: false
OWNER_GOAL_SCOPED_GRANT_REQUIRED: true
LIVE_ROUTE_MUTATION: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Concurrency fact

The SPEC-011 audit was reasoned against head `4984a107...`. Before its commit,
Linux landed `3a97a093...`, a report of the already owner-granted T2 V0 run. The
Proshka audit then committed on top of that report.

This is not a content conflict. It changes the stage status:

```text
before concurrent report:
  T2 local matcher plants OPEN;

after concurrent report:
  T2 local matcher plants PASS as a bounded experiment;
  durable/materialized matcher still OPEN.
```

The base verdict remains valid for the architecture repairs. This addendum
supersedes only its statement that T2 had not yet run.

`[FINITE_CELL][PAPER]`

### 2. What the report legitimately closes

The report contains:

```text
P1 wrong source family                     -> HARD_MISMATCH
P2 finite offered as cofinal               -> HARD_MISMATCH
P3 L2 isometry offered as pointwise        -> ADAPTER_REQUIRED
P4 full endpoint offered as midpoint       -> REFINEMENT_LOSS
P5 Rayleigh scalar offered as residual     -> HARD_MISMATCH
NC1 legal adapter control                  -> EXPLICIT_ADAPTER_MATCH
NC2 legal exact self edge                  -> EXACT_MATCH
```

It reports all expected outcomes, two positive controls, zero wrong-object
escapes, and exact Lean `#check` extraction for the kernel types.

Therefore the narrow gap

```text
T2_PORT_MATCHER_LOCAL_PLANTS
```

is accepted as closed by experimental evidence.

This does not test candidate-volume pruning, global path search, or contextual
composition across several dependent inputs.

`[FINITE_CELL][PAPER]`

### 3. Why this is not yet a durable T2 engine

The matcher source and temporary Lean harnesses remained in a session scratchpad.
The repository contains the report, not the executable matcher.

A prose statement that 140 lines are reproducible from the report is not a code
receipt. The current artifact lacks:

```text
matcher blob;
schema hash;
fixture manifest hash;
toolchain-bound receipt;
committed harnesses;
replay command against the same bytes.
```

Consequently:

```text
EXPERIMENTAL_CLASSIFICATION_PASS: yes;
DURABLE_MATCHER_RELEASE: no.
```

T3 must not import an uncommitted session registry as if it were a stable project
component.

### 4. Shared dependent context is still untested

The report tests individual port pairs. It does not test the decisive dependent
AND-edge failure:

```text
A(m1,N1) ∧ B(m2,N2) ∧ C(m3,N3)
```

being offered to a consumer requiring:

```text
A(m,N) ∧ B(m,N) ∧ C(m,N).
```

The surface types may all match after metavariable erasure while the shared
source object does not.

Add one mandatory plant:

```text
C2_SHARED_CONTEXT_INCOHERENCE:
  same surface theorem shapes;
  different source-family/index substitution;
  expected: HARD_MISMATCH.
```

The matcher must produce one substitution environment for the entire hyperedge,
not one local match per port.

`[ABSTRACT][PAPER]` **[C04]**

### 5. Adapter naming repair

The checked theorem shown in the report has conclusion:

```lean
... =ᵐ[volume] fun t => FourierTransform.fourier ... t
```

This is almost-everywhere equality. It is not pointwise equality.

Therefore the registry name

```text
A_ISOMETRY_TO_POINTWISE_FOURIER
```

is semantically too strong.

Rename it:

```text
A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE.
```

It may discharge a consumer requiring an a.e. representative or an `Lp` class.
It may not discharge a pointwise evaluation consumer without another theorem.
For a pointwise consumer, the result remains:

```text
ADAPTER_REQUIRED
```

or:

```text
REFINEMENT_LOSS.
```

This is an instance of **C04 SAME-COORDINATES-TWO-LAWS** and **C10
FUNCTIONAL-NOT-SURROGATE**.

### 6. Adapter registry evidence remains incomplete

The report lists:

```text
A_L2_TO_L1_FINITE_WINDOW
A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE
A_AE_TO_LP_CLASS
```

The durable registry must attach to every entry:

```text
exact theorem name;
source file and line;
source commit/blob;
exact #check type;
loss ledger;
scope;
verifier;
shared parameter context.
```

An adapter name and a short prose proof sketch are candidate metadata, not a
verified registry entry.

## FINAL PROPOSAL

Preserve the V0 report as a successful bounded experiment.

Do not rerun P1-P5 from zero.

The next local target is only:

```text
T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT.
```

It must:

1. materialize the matcher and fixtures in the existing comparator layer;
2. add the shared-context plant;
3. convert refinements and adapter entries to evidence-bearing records;
4. repair the a.e./pointwise adapter identity;
5. emit a content-addressed versioned receipt;
6. replay the already successful P1-P5 and NC1-NC2 without changing expected
   outcomes.

Only then may T3 modify `cheap.py`.

## STRONGEST ATTACK

The strongest objection to this addendum is:

> The report already says PASS. Requiring committed code is bureaucracy.

No. The project intends to use this matcher as an input to future automated
routing. A session-only implementation cannot be inspected, replayed, versioned,
or bound to a schema. It can establish that the design is feasible; it cannot
serve as durable infrastructure.

Second objection:

> The a.e. crosswalk is close enough to pointwise Fourier evaluation.

That is exactly the object mismatch the matcher exists to prevent. Equality in
`Lp` or almost everywhere does not justify pointwise evaluation at a selected
frequency. A named pointwise theorem is required.

## REGISTERED PREDICTION FATES

```yaml
P_SPEC011_1:
  prediction: shared-context unification catches false edges unseen by pairwise surface matching
  fate: UNTESTED

P_SPEC011_2:
  prediction: at least one illustrative refinement lacks source-backed evidence
  fate: CONFIRMED

P_SPEC011_3:
  prediction: first defects are schema/provenance defects rather than graph-search defects
  fate: CONFIRMED_PARTIALLY
  evidence:
    - matcher source is not durable
    - adapter registry lacks content-addressed evidence
    - a.e. adapter was named pointwise

P_SPEC011_4:
  prediction: surviving gaps are mostly genuine missing theorem modules
  fate: UNTESTED

P_TIO_1:
  fate: UNTESTED
  reason: no real depth-2 corpus scored

P_TIO_2:
  fate: UNTESTED

P_TIO_3:
  fate: PARTIAL_EVIDENCE
  evidence: one legal W1 adapter was recognized

P_TIO_4:
  fate: UNTESTED
```

## CODEX DIRECTIVE — FUTURE OWNER-GRANTED EXECUTION

This block is not executable without an explicit owner goal-scoped grant.

```text
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_T2_1_DURABLE

OBJECTIVE:
  Materialize and replay the already successful V0 matcher with context
  coherence, evidence-bearing refinements, correct a.e. semantics, and a
  versioned receipt.

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_V0_2026-08-23.md
  docs/routeB_bus/proshka/
    PROSHKA_VERDICT_SPEC_011_TYPED_DISCOVERY_COMPILER_AUDIT_2026-08-23.md
  docs/cartographer/comparator/README.md

MODE:
  BOUNDED_EXPLORATION
  NO_LIVE_ROUTE_MUTATION

WRITE_ONLY:
  docs/cartographer/typed_io_schema_v1_1.yaml
  docs/cartographer/comparator/port_matcher.py
  docs/cartographer/comparator/test_port_matcher.py
  docs/cartographer/comparator/fixtures/**
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_1_DURABLE_2026-08-23.md

DO_NOT_EDIT:
  production Lean source
  active goals or answers
  runtime/state files
  AGENTS.md
  docs/CODEX_CONTROL.md
  SESSION_ENTRY.md
  CLAUDE.md

MANDATORY_REPLAY:
  P1-P5
  NC1-NC2
  C2_SHARED_CONTEXT_INCOHERENCE

MANDATORY_REPAIR:
  rename A_ISOMETRY_TO_POINTWISE_FOURIER to
    A_ISOMETRY_TO_AE_FOURIER_REPRESENTATIVE;
  refuse that adapter for pointwise consumers;
  attach exact evidence to every adapter/refinement;
  emit T2_PORT_MATCHER_RECEIPT_V1.

PASS:
  all prior controls preserve their outcomes;
  C2 is HARD_MISMATCH;
  a.e. adapter is accepted only for a.e./Lp consumer;
  pointwise consumer remains unclosed;
  matcher source and fixtures are committed;
  content-addressed receipt is complete;
  wrong-object escape = 0;
  false rejection = 0.

NEXT_IF_PASS:
  T3_TYPED_GAP_SIGNATURE_IN_CHEAP.
```

## META CLOSEOUT

**What became smaller?**

T2 is no longer an untested design. Only its durable, context-coherent release
remains open.

**What was killed?**

```text
T2 must be rebuilt from zero;
negative-only detector concern;
pointwise naming for an a.e. theorem;
scratchpad source as durable infrastructure;
pairwise matching as sufficient for dependent AND-edges.
```

**What must not be tried again?**

Do not move the scratchpad registry into `cheap.py` by copy-paste. Materialize,
source-lock, replay, and receipt it first.

**Current smallest named gap:**

```text
T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT.
```

**Next cheapest decisive test:**

The shared-context incoherence plant plus the pointwise-versus-a.e. consumer
plant on the committed matcher.

```yaml
iteration:
  target: T2_TYPED_IO_PORT_MATCHER
  status: PROGRESS
  failed_strategy: SESSION_ONLY_PAIRWISE_MATCHER_AS_DURABLE_ENGINE
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: T2_1_DURABLE_CONTEXT_COHERENT_MATCHER_RECEIPT
  invariant_learned: all hyperedge inputs share one substitution and a.e. equality never discharges pointwise evaluation
  forbidden_future_move: T3_import_of_uncommitted_matcher_or_unhashed_registry
  next_decisive_test: committed_context_plant_and_ae_pointwise_replay
  progress_class: PROOF_PROGRESS
  route_score: 5
```
