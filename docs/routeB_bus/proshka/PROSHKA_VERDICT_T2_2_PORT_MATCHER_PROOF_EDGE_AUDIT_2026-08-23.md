# STATUS: FATAL — T2.2 CLOSES THE PRIOR FOUR KILLS, BUT ITS POSITIVE LABELS ARE NOT YET PROOF-GRADE

```yaml
PRIMARY: KILL_T2_2_AS_PRODUCTION_PROOF_EDGE_MATCHER
OPERATIVE_CLASS: TRY_T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE
DOCUMENT_ROLE: POST_REPORT_ADVERSARIAL_VERDICT

ANSWERS_TASK: Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED
REPO: Malaeu/chen_q3
BRANCH: rh_clean
REVIEW_HEAD: 145a87015d576fe816c3cdbd986d4af6da929e0d
DATE: 2026-08-23

SOURCE_LOCK:
  REPORT_PATH: docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED_2026-08-23.md
  REPORT_BLOB: 008706bfffefcd32a768d98ff13a88137287baf5
  SCHEMA_PATH: docs/cartographer/typed_io_schema_v1_2.yaml
  SCHEMA_BLOB: 2bb6d67b9927a4b3c891c1852434795b92eca2d5
  MATCHER_PATH: docs/cartographer/comparator/port_matcher.py
  MATCHER_BLOB: 805ee5a96e77612a4809e841eb3952fe9ad45873
  TESTS_PATH: docs/cartographer/comparator/test_port_matcher.py
  TESTS_BLOB: 614262d4fc4453538f5ce47513db65e06aa92789
  PLANTS_BLOB: ac255f7efc1edeab1529aa860d1e31a40d3d8b66
  ADAPTER_REGISTRY_BLOB: 582b7dd42a985afb14e4f0798752a407c8b9e6ea

RATIFIED_FROM_REPORT:
  PRIOR_KILLS_REPRODUCED_BEFORE_REPAIR: true
  P1_P10_FROZEN_REPLAY: PASS
  NC1_NC2_NC4_NC5_POSITIVE_REPLAY: PASS
  C2_AND_C2_POS_REPLAY: PASS
  REPORTED_WRONG_OBJECT_ESCAPE: 0
  REPORTED_FALSE_REJECTION: 0
  RECEIPT_FIELDS_TOOLCHAIN_AND_RESULTS: PRESENT
  MATCHER_AND_FIXTURES_MATERIALIZED: true
  LIVE_ROUTE_MUTATION: false

RELEASE_VERDICT:
  durable_metadata_prefilter: PROGRESS
  frozen_fixture_classifier: PASS
  verified_proof_edge_certifier: FATAL
  T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE: PARTIALLY_CLOSED
  T3_TYPED_GAP_SIGNATURE_IN_CHEAP: HOLD
  T4_BIDIRECTIONAL_MEET_IN_THE_MIDDLE: HOLD

FATALS:
  - CONSUMER_REQUIRED_REFINEMENT_MAY_BE_ABSENT_ON_PROVIDER_AND_STILL_EXACT
  - VERIFIER_FLOOR_HAS_NO_SOUND_COMPATIBILITY_RELATION
  - ADAPTER_EVIDENCE_IS_SHAPE_CHECKED_NOT_SOURCE_CHECKED
  - DEPENDENT_CONSTRUCTION_WITNESS_IS_A_STRING_TAG
  - SCHEMA_AND_RUNTIME_PORT_SHAPES_DIVERGE
  - HYPEREDGE_UNIFIER_IGNORES_CONSUMER_BINDING_VALUES
  - ADAPTER_SCOPE_DROPS_AND_SHARED_CONTEXT_ARE_NOT_ENFORCED
  - INDEPENDENT_KEY_ADAPTERS_ARE_NOT_A_COMPOSED_PORT_TRANSFORM
  - EXACT_MATCH_IS_STRING_EQUALITY_NOT_A_KERNEL_CHECK

CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

CLOSES:
  - T2_1_MISSING_METADATA_DEFAULTS_TO_EXACT_AND_LEAN
  - T2_1_MALFORMED_ADAPTER_ROW_ACCEPTANCE
  - T2_1_AE_REPRESENTATIVE_TO_LP_CLASS_CONFLATION
  - T2_1_RECEIPT_SCHEMA_NONCONFORMANCE
  - T2_2_RELEASE_STATUS_AMBIGUITY

OPENS:
  - T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE

NEXT_LOAD_BEARING_GAP: T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE

SCOPE: ABSTRACT
TARGET_VALIDATION_SCOPE: FINITE_CELL
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 5

EXECUTION_AUTHORIZED_BY_THIS_FILE: false
OWNER_GOAL_SCOPED_GRANT_REQUIRED: true
LIVE_ROUTE_MUTATION: false
LEAN_SOURCE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

T2.2 is a materially better prototype than T2.1. It honestly reproduced the four old kills before repair, removed the permissive trust default, separated `MemLp.toLp` from `Lp.ext`, added positive controls, materialized a receipt, and added ten self-attacks.

The narrow statement is accepted:

```text
T2.2 classifies its frozen metadata corpus as reported.
```

The production statement is rejected:

```text
T2.2 may emit active proof edges from source-faithful evidence.
```

The matcher still turns several incomplete or merely well-shaped metadata records into `EXACT_MATCH` or `EXPLICIT_ADAPTER_MATCH`. Therefore T3 must not consume its positive labels.

`[ABSTRACT][PAPER]`

## FATAL 1 — a consumer demand may be absent on the provider

Port validation requires only:

```text
provider: kernel_type, source_family, trust
consumer: kernel_type, source_family, trust_floor.
```

For scope and every hard/soft refinement, the matcher uses the effective rule:

```python
if provider_value is None or consumer_value is None:
    continue
```

It then emits `EXACT_MATCH` when the two `kernel_type` strings are equal.

Static counterexample:

```yaml
P11_MISSING_PROVIDER_SCOPE:
  provider:
    kernel_type: T
    source_family: F
    trust: LEAN
  consumer:
    kernel_type: T
    source_family: F
    trust_floor: LEAN
    scope: COFINAL_FAMILY
  required: UNVERIFIED
  source_semantics: EXACT_MATCH
```

The same escape exists when the consumer requires a normalization, quantifier spine, units, object identity, carrier, topology, summation method, or representative and the provider omits that field.

Absence on the provider is not a wildcard when the consumer has declared a requirement.

`[ABSTRACT][PAPER]` **[C04]**

## FATAL 2 — verifier compatibility is not an order

The only active trust test rejects a weak provider when:

```text
provider not in {LEAN, ARB_INTERVAL}
and consumer trust_floor == LEAN.
```

Consequently a `PAPER` provider may feed an `ARB_INTERVAL` consumer, and an `ARB_INTERVAL` row may feed an arbitrary `LEAN` proposition, provided the surface strings match.

Static counterexample:

```yaml
P12_PAPER_TO_ARB_FLOOR:
  provider:
    kernel_type: T
    source_family: F
    trust: PAPER
  consumer:
    kernel_type: T
    source_family: F
    trust_floor: ARB_INTERVAL
  required: UNVERIFIED
  source_semantics: EXACT_MATCH
```

`LEAN`, `ARB_INTERVAL`, and `PAPER` are different verifier categories, not a single scalar strength order. Cross-verifier transport requires an explicit certificate-import theorem or receipt.

`[ABSTRACT][PAPER]`

## FATAL 3 — complete-looking forged evidence is accepted

`validate_adapter` checks that evidence fields are present and nonempty. It does not establish that:

```text
the declaration exists;
the source file contains it;
the source blob matches the pinned commit;
the pasted #check type is the declaration type;
the direction is the theorem direction;
the loss ledger follows from the theorem;
the verifier actually checked the claimed edge.
```

A fabricated row with twelve populated fields, six populated evidence fields, and `VERIFIER: LEAN` licenses an `EXPLICIT_ADAPTER_MATCH`.

The old P9 tests missing evidence. It does not test forged complete evidence.

```yaml
P13_FULLY_SHAPED_FORGED_ADAPTER:
  registry_row:
    theorem_name: Fake.theorem
    source_file: fake.lean
    source_commit: deadbeef
    source_blob: deadbeef
    check_type: A_to_B
    VERIFIER: LEAN
    all_other_fields: populated
  required: UNVERIFIED
```

A registry entry is not evidence merely because its evidence-shaped record is complete.

`[ABSTRACT][PAPER]` **[C10]**

## FATAL 4 — `MemLp` remains a string witness

The repaired adapter direction is mathematically correct:

```text
MemLp.toLp constructs an Lp element;
Lp.ext compares two existing Lp elements.
```

But the matcher authorizes the construction by checking only:

```python
provider["construction_witness"] == "MemLp"
```

It does not carry or unify a proof of:

```lean
MeasureTheory.MemLp f p μ
```

for the same `f`, `p`, and `μ` consumed by `MemLp.toLp`.

Thus NC4 is a useful metadata control, not a proof-grade dependent application.

```yaml
P14_STRING_MEMLP_WITNESS:
  provider:
    construction_witness: MemLp
    no_typed_proof_term: true
  required: UNVERIFIED
```

`[ABSTRACT][PAPER]` **[C04][C10]**

## FATAL 5 — the schema is not the runtime data model

Schema v1.2 declares nested records:

```yaml
KERNEL:
  exact_type:
REFINEMENTS:
  source_family:
  normalization:
CONTEXT:
  vars:
TRUST:
  verifier:
```

The matcher consumes flat records:

```yaml
kernel_type:
source_family:
normalization:
context:
trust:
```

It does not parse or validate a port against `typed_io_schema_v1_2.yaml`. Hashing the schema and matcher in one receipt binds their bytes, not their semantics.

Therefore the claim “validate every port against the schema” remains open.

`[ABSTRACT][PAPER]`

## FATAL 6 — shared context checks provider agreement, not consumer substitution

The hyperedge matcher reads the keys of the consumer context but discards each consumer value. It only checks that all providers bind a key to one common value.

Therefore a consumer fixed at `m = 13` can be supplied by a coherent provider bundle at `m = 7`.

```yaml
P15_FIXED_CONSUMER_CONTEXT_IGNORED:
  consumer_context: {m: 13}
  provider_contexts: [{m: 7}, {m: 7}, {m: 7}]
  required: HARD_MISMATCH
```

The report correctly names the adjacent hole: `SHARED_PARAMETER_CONTEXT` is shape-checked but never compared with the actual edge substitution. Both defects belong to the same missing unification layer.

`[ABSTRACT][PAPER]` **[C04]**

## FATAL 7 — adapters are collected per key, not composed as typed maps

The matcher may find one adapter for `object_identity`, another for `carrier`, and another for `topology`, append their names to one list, and emit `EXPLICIT_ADAPTER_MATCH`.

It does not:

```text
apply an adapter to the full current port state;
check the intermediate port;
order the adapters;
verify shared parameters across the chain;
propagate scope and verifier;
compose rate/loss ledgers;
check that one adapter does not drop a later consumer requirement.
```

Mandatory attacks:

```yaml
P16_NONCOMPOSABLE_VALID_ADAPTERS:
  expected: UNVERIFIED

P17_FINITE_ADAPTER_IN_COFINAL_CHAIN:
  expected: HARD_MISMATCH

P18_ADAPTER_DROPS_CONSUMER_REQUIRED_REFINEMENT:
  expected: REFINEMENT_LOSS
```

The current code validates `SCOPE`, `DROPS`, `LOSS_LEDGER`, and `SHARED_PARAMETER_CONTEXT` only as metadata shapes. It does not enforce their mathematical content.

`[ABSTRACT][PAPER]` **[C04][C10]**

## FATAL 8 — `EXACT_MATCH` is string equality, not a kernel judgement

The terminal positive test is:

```python
provider["kernel_type"] == consumer["kernel_type"]
```

The corpus contains abbreviated strings and does not require the local environment, implicit binders, universes, declaration identity, or a comparator harness.

Two equal strings are a candidate equality. They are not a Lean proof edge.

```yaml
P19_SAME_PRINTED_STRING_DIFFERENT_ENVIRONMENT:
  expected: UNVERIFIED_OR_COMPARATOR_REQUIRED
```

A production `EXACT_MATCH` must be backed by one of:

```text
definitional equality checked by Lean;
an explicit term checked by Lean;
a content-addressed comparator harness against the exact local environments.
```

`[ABSTRACT][PAPER]`

## FINAL PROPOSAL

Preserve commit `145a8701...` as a useful fail-closed metadata prototype and adversarial corpus. Do not delete or rewrite its report.

Ratify the repaired statement:

```text
T2.2 is a durable metadata prefilter whose frozen fixture suite passes.
```

Kill the stronger statement:

```text
T2.2 certifies active proof edges.
```

The next node is:

```text
T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE.
```

It must separate two outputs:

```text
CANDIDATE_MATCH:
  metadata-compatible route candidate;

VERIFIED_PROOF_EDGE:
  exact consumer discharged by a source-checked theorem application.
```

Only `VERIFIED_PROOF_EDGE` may reduce T3's `current_k`.

## STRONGEST ATTACK

The strongest objection is:

> This matcher is only a search prefilter. The positive labels need not be proofs.

That repair is valid only after renaming the labels. `EXACT_MATCH` and `EXPLICIT_ADAPTER_MATCH` currently sound like active compositional facts and are intended to feed T3/T4. A heuristic prefilter may output `CANDIDATE_MATCH`; it may not silently subtract a proof obligation.

A second objection is:

> All newly named attacks are outside the frozen corpus.

Correct. That is the point of an adversarial release audit. Passing a finite corpus never establishes universal soundness. Here the attacks are not exotic: they instantiate ordinary consumer demands, dependent binders, verifier mismatch, source provenance, scope, and adapter composition—the exact structures SPEC-011 claims to preserve.

## REGISTERED PREDICTION FATES

```yaml
P_SPEC011_1:
  prediction: shared-context unification catches false edges unseen by pairwise matching
  fate: PARTIALLY_CONFIRMED
  note: C2 catches provider-provider disagreement; fixed consumer bindings and adapter context remain unchecked

P_SPEC011_2:
  prediction: at least one refinement lacks source-backed evidence
  fate: CONFIRMED_AND_GENERALIZED

P_SPEC011_3:
  prediction: first defects are provenance/schema defects before graph-search defects
  fate: CONFIRMED

P_TIO_1:
  prediction: reject at least 95 percent of naive depth-2 edges
  fate: UNTESTED

P_TIO_2:
  prediction: surviving gaps are mostly genuine missing theorems
  fate: UNTESTED

P_TIO_3:
  prediction: adapter registry closes material low-cost gaps
  fate: PARTIAL_EVIDENCE_ONLY

RETROACTIVE_REPAIR: false
```

## CODEX DIRECTIVE — FUTURE OWNER-GRANTED EXECUTION

```text
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_T2_3_SOURCE_FAITHFUL

OBJECTIVE:
  Separate metadata candidate generation from verified proof-edge creation,
  and make every positive proof-edge label source-faithful, context-coherent,
  verifier-compatible, and loss-aware.

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED_2026-08-23.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_T2_2_PORT_MATCHER_PROOF_EDGE_AUDIT_2026-08-23.md
  docs/cartographer/typed_io_schema_v1_2.yaml
  docs/cartographer/comparator/port_matcher.py

MODE:
  BOUNDED_EXPLORATION
  NO_LIVE_ROUTE_MUTATION

WRITE_ONLY:
  docs/cartographer/typed_io_schema_v1_3.yaml
  docs/cartographer/comparator/port_matcher.py
  docs/cartographer/comparator/test_port_matcher.py
  docs/cartographer/comparator/fixtures/**
  docs/cartographer/comparator/lean_harness/**
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_3_SOURCE_FAITHFUL_2026-08-23.md

MANDATORY_REPAIR:
  1. Parse one canonical runtime port shape derived from schema v1.3.
  2. If the consumer declares a refinement, the provider must declare and
     discharge it or return UNVERIFIED/ADAPTER_REQUIRED.
  3. Replace the trust shortcut with an explicit verifier-compatibility table;
     cross-verifier promotion requires a named import certificate.
  4. Verify adapter provenance against exact commit/blob/declaration/#check;
     a complete-looking forged row must fail.
  5. Represent construction witnesses as exact typed input ports under the
     same dependent context; string witness tags cannot license a theorem.
  6. Unify consumer constants and variables with provider terms under one
     substitution for the entire AND-edge.
  7. Apply adapters to the whole port state in order; propagate scope,
     verifier, drops, loss/rate ledger, and shared context.
  8. Emit CANDIDATE_MATCH separately from VERIFIED_PROOF_EDGE.
  9. Emit VERIFIED_PROOF_EDGE only after a content-addressed Lean comparator
     or explicit theorem-application harness passes.

MANDATORY_REPLAY:
  preserve all T2.2 frozen outcomes at candidate-classification level;
  add P11-P19;
  add positive controls for exact Lean definitional equality and a lawful
  two-adapter composition;
  wrong-object proof-edge escape = 0;
  false rejection on lawful proof edges = 0.

PASS:
  no P11-P19 attack emits VERIFIED_PROOF_EDGE;
  consumer fixed bindings are enforced;
  forged complete evidence is rejected;
  MemLp construction uses the exact f/p/mu witness;
  adapter scope/drops/context/losses are propagated;
  every VERIFIED_PROOF_EDGE has a replayable Lean receipt.

NEXT_IF_PASS:
  T3_TYPED_GAP_SIGNATURE_IN_CHEAP_CANDIDATE_AND_VERIFIED_COUNTS_SEPARATED.

FAILURE_CODES:
  T2_3_CONSUMER_DEMAND_OMISSION
  T2_3_VERIFIER_PROMOTION_ESCAPE
  T2_3_FORGED_EVIDENCE_ACCEPTED
  T2_3_DEPENDENT_WITNESS_STRING_ACCEPTED
  T2_3_CONTEXT_CONSTANT_IGNORED
  T2_3_NONCOMPOSABLE_ADAPTER_CHAIN_ACCEPTED
  T2_3_LOSS_OR_SCOPE_NOT_PROPAGATED
  T2_3_STRING_EQUALITY_AS_PROOF_EDGE
```

## META CLOSEOUT

**What became smaller?**

The old four T2.1 defects are genuinely repaired. The remaining issue is no longer generic “fail closed”; it is exactly the boundary between metadata eligibility and a verified theorem application.

**What was killed?**

```text
frozen fixture replay = production soundness;
complete-looking metadata = source evidence;
string witness = dependent proof;
provider agreement = consumer unification;
per-key adapter collection = typed composition;
printed type string equality = Lean proof edge.
```

**What must not be tried again?**

Do not connect positive T2.2 labels to `cheap.py`, reduce `current_k`, or launch T4 route synthesis.

**Current smallest named gap:**

```text
T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE.
```

**Next cheapest decisive test:**

Run P11-P15 directly against the current matcher before any redesign; then freeze the candidate/proof-edge split.

```yaml
iteration:
  target: T2_2_FAIL_CLOSED_PORT_MATCHER
  status: FATAL
  failed_strategy: SHAPE_VALIDATED_METADATA_AS_PROOF_EDGE
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: T2_3_SOURCE_FAITHFUL_COMPOSITION_GATE
  invariant_learned: positive proof edges require exact consumer discharge under one source-checked dependent context
  forbidden_future_move: do_not_rank_or_close_gaps_from_metadata_only_positive_labels
  next_decisive_test: P11_P15_SOURCE_SEMANTICS
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```
