# STATUS: FATAL — T2.1 MATERIALIZATION EXISTS, BUT THE PRODUCTION MATCHER IS NOT FAIL-CLOSED

```yaml
PRIMARY: KILL_T2_1_AS_PRODUCTION_PORT_MATCHER
OPERATIVE_CLASS: TRY_T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE
DOCUMENT_ROLE: POST_REPORT_ADVERSARIAL_VERDICT

ANSWERS_TASK: Q3_TYPED_IO_PORT_MATCHER_T2_1_DURABLE
REPO: Malaeu/chen_q3
BRANCH: rh_clean
REVIEW_HEAD: 460b017a4effe3755b4b8b99f45689575dd46564
DATE: 2026-08-23

MATERIALIZATION:
  matcher_source_committed: true
  fixtures_committed: true
  replay_suite_runs_as_reported: accepted_from_report
  P1_P6_reported_pass: true
  NC1_NC3_reported_pass: true
  C2_context_plant_reported_pass: true

RELEASE_VERDICT:
  durable_files_exist: true
  bounded_fixture_replay: PASS
  production_fail_closed_semantics: FATAL
  T2_PORT_MATCHER_RECEIPT_V1_COMPLETE: false
  T3_TYPED_GAP_SIGNATURE_IN_CHEAP: HOLD

FATALS:
  - MISSING_METADATA_DEFAULTS_TO_EXACT_AND_LEAN
  - ADAPTER_EVIDENCE_NOT_VALIDATED
  - AE_REPRESENTATIVE_TO_LP_CLASS_FALSE_EXACT_MATCH
  - RECEIPT_SCHEMA_NONCONFORMANCE

CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

CLOSES:
  - T2_1_MATERIALIZATION_EXISTENCE
  - T2_1_PAIRWISE_AND_SHARED_CONTEXT_REPLAY
  - T2_1_RELEASE_STATUS_AMBIGUITY

OPENS:
  - T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE

NEXT_LOAD_BEARING_GAP: T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE

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
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

The T2.1 transaction successfully materialized the matcher, fixtures, schema, replay suite and a content-addressed hash set. The report's narrow claim that the frozen fixtures replay with the expected labels is accepted.

The stronger claim that this is a fail-closed durable production matcher is rejected. Four independent source-level attacks survive.

### 1. Missing metadata is silently upgraded to Lean-exact

`match_port` uses:

```python
provider.get("trust", "LEAN")
consumer.get("trust_floor", "LEAN")
```

and skips every hard or soft refinement when either side is absent. It then returns `EXACT_MATCH` whenever the two `kernel_type` strings are equal.

Therefore this plant is accepted:

```python
provider = {"kernel_type": "T"}
consumer = {"kernel_type": "T"}
```

Expected fail-closed result:

```text
UNVERIFIED
```

or schema rejection.

Actual source result:

```text
EXACT_MATCH
```

This violates the declared rule that metadata may restrict composability only when it is evidence-bearing. Missing evidence is not Lean evidence.

### 2. Adapter evidence is never checked

`_find_adapter` matches only `FROM_PORT` and `TO_PORT`. It does not verify:

```text
EVIDENCE presence;
theorem name;
source blob;
verifier;
direction;
scope;
loss ledger;
shared parameter context.
```

A fabricated registry row with the correct two strings is enough to produce `EXPLICIT_ADAPTER_MATCH`. The registry is therefore trusted as an axiom table rather than checked as evidence-bearing data.

### 3. `NC3` is a false positive

The positive control says:

```text
ae representative -> Lp class = EXACT_MATCH.
```

But both fixture endpoints are assigned the same fake kernel string `ℝ → ℂ`. In Lean an `Lp` element is not definitionally an arbitrary function. Constructing an `Lp` element requires the relevant membership/integrability data and a constructor such as `MemLp.toLp`; `MeasureTheory.Lp.ext` only proves equality of two already existing `Lp` elements from an a.e. equality.

Thus the current `A_AE_TO_LP_CLASS` evidence points in the wrong logical direction. `NC3` must not be an exact control. It is an instance of C04 and C10.

### 4. The receipt is incomplete under its own schema

`RECEIPT_V1` declares mandatory fields:

```text
toolchain
results
```

The emitted `receipt()` and report JSON contain neither. A prose toolchain note outside the receipt does not satisfy the machine-readable schema. Therefore `T2_PORT_MATCHER_RECEIPT_V1_COMPLETE` is false.

## FINAL PROPOSAL

Preserve commit `460b017a...` as a useful adversarial prototype and fixture corpus. Do not delete it and do not rewrite its report.

Do not connect this matcher to `cheap.py` yet.

The next node is one bounded repair:

```text
T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE
```

Required changes:

1. validate every port against the schema before matching;
2. missing required field or missing evidence returns `UNVERIFIED`, never `EXACT_MATCH`;
3. trust has no permissive default;
4. validate adapter evidence, scope, direction, losses and shared context before use;
5. replace NC3 with a real `MemLp -> Lp` construction plant and a separate `Lp.ext` equality plant;
6. include `toolchain` and frozen plant results inside the receipt;
7. add the four plants below and retain all existing plants unchanged.

## STRONGEST ATTACK

The strongest objection is:

> The matcher is only a heuristic prefilter. Why require proof-grade schema validation?

Because the next stage intends to feed its output into gap ranking and route synthesis. A permissive prefilter may generate candidates, but it cannot label an edge `EXACT_MATCH` or `EXPLICIT_ADAPTER_MATCH`. Those labels enter the active proof graph and must be fail-closed.

A weaker repaired statement is valid now:

```text
T2.1 is a durable prototype that correctly classifies its frozen fixture suite.
```

The stronger statement is killed:

```text
T2.1 is a production-safe typed port matcher.
```

## REGISTERED PLANTS FOR T2.2

```yaml
P7_MISSING_METADATA:
  provider: {kernel_type: T}
  consumer: {kernel_type: T}
  expected: UNVERIFIED

P8_MISSING_TRUST:
  provider:
    kernel_type: T
    source_family: F
  consumer:
    kernel_type: T
    source_family: F
    trust_floor: LEAN
  expected: UNVERIFIED

P9_FAKE_ADAPTER_EVIDENCE:
  registry_row:
    FROM_PORT: {object_identity: A}
    TO_PORT: {object_identity: B}
  expected: UNVERIFIED

P10_AE_TO_LP_WITHOUT_MEMLP:
  provider: arbitrary_ae_representative
  consumer: Lp_element
  expected: ADAPTER_REQUIRED
  required_adapter_input: MemLp
```

Positive controls:

```yaml
NC4_MEMLP_TO_LP:
  evidence: exact pinned MemLp.toLp declaration
  expected: EXPLICIT_ADAPTER_MATCH

NC5_LP_EXT_EQUALITY:
  inputs: two existing Lp elements plus ae equality
  expected: EXPLICIT_ADAPTER_MATCH
```

## CODEX DIRECTIVE — FUTURE OWNER-GRANTED EXECUTION

```text
TASK_ID: Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED

OBJECTIVE:
  Repair the durable matcher so absent metadata, absent evidence and wrong-way
  representative conversions cannot create active proof edges.

READ_FIRST:
  docs/CODEX_CONTROL.md
  docs/routeB_bus/SUPPLIER_CONTRACT.md
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_1_DURABLE_2026-08-23.md
  docs/routeB_bus/proshka/PROSHKA_VERDICT_T2_1_DURABLE_PORT_MATCHER_FAIL_CLOSED_AUDIT_2026-08-23.md
  docs/cartographer/typed_io_schema_v1_1.yaml
  docs/cartographer/comparator/port_matcher.py
  docs/cartographer/comparator/test_port_matcher.py

MODE:
  BOUNDED_EXPLORATION
  NO_LIVE_ROUTE_MUTATION

WRITE_ONLY:
  docs/cartographer/typed_io_schema_v1_2.yaml
  docs/cartographer/comparator/port_matcher.py
  docs/cartographer/comparator/test_port_matcher.py
  docs/cartographer/comparator/fixtures/**
  docs/routeB_bus/CODEX_REPORT_Q3_TYPED_IO_PORT_MATCHER_T2_2_FAIL_CLOSED_2026-08-23.md

MANDATORY_REPLAY:
  preserve P1-P6, NC1-NC3, C2, C2_POS outcomes except NC3, which must be
  replaced by the source-faithful pair NC4/NC5;
  add P7-P10;
  wrong-object escape = 0;
  false rejection = 0.

PASS:
  all required schema fields validated;
  missing evidence -> UNVERIFIED;
  no permissive trust default;
  fake adapter rejected;
  ae function cannot become Lp without MemLp construction;
  receipt contains schema/matcher/tests/fixtures/toolchain/results hashes;
  replay is content-addressed and reproducible.

NEXT_IF_PASS:
  T3_TYPED_GAP_SIGNATURE_IN_CHEAP.

FAILURE_CODES:
  T2_2_MISSING_METADATA_ACCEPTED
  T2_2_FAKE_ADAPTER_ACCEPTED
  T2_2_AE_LP_CONFLATION
  T2_2_RECEIPT_INCOMPLETE
```

## META CLOSEOUT

**What became smaller?**

The question is no longer whether T2 can classify ports. It can. The remaining gap is exactly whether its positive labels are source-faithful and fail-closed.

**What was killed?**

```text
missing metadata = Lean evidence;
registry strings = verified theorem adapters;
ae representative = Lp element;
partial receipt = complete receipt;
T3 immediately after T2.1.
```

**What must not be tried again?**

Do not add more route-ranking logic before positive match labels are proof-grade.

**Current smallest named gap:**

```text
T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE
```

**Next cheapest decisive test:**

Run P7-P10 directly against the current matcher. Each is source-determined and requires no Lean build.

```yaml
iteration:
  target: T2_1_DURABLE_PORT_MATCHER
  status: FATAL
  failed_strategy: FIXTURE_PASS_AS_PRODUCTION_RELEASE
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: T2_2_FAIL_CLOSED_SCHEMA_EVIDENCE_GATE
  invariant_learned: absence of metadata or evidence never upgrades to a proof edge
  forbidden_future_move: rank routes before positive edge labels are fail_closed
  next_decisive_test: P7_P10
  progress_class: FALSIFICATION_PROGRESS
  route_score: 5
```
