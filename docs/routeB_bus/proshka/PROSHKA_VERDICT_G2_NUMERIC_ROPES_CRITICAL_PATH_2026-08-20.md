# STATUS: FATAL FOR G2 NUMERIC ROPES AS ROOF-CRITICAL — THE `(13,120)` CELL IS VALIDATION, NOT A `SlotH2a` SUPPLIER

```yaml
PRIMARY: REMOVE_G2_M13_NUMERIC_ROPES_FROM_CRITICAL_PATH
PRIMARY_COUNT: 1

REQUEST:
  ID: REQ-2026-08-20-B
  STATUS_IN_QUEUE: OPEN_AT_AUDIT

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  AUDITED_HEAD: ccb664b6dc1225e1080a6e09eba8246c4e271a25

DELIVERY:
  DOC_ONLY: true
  LEAN_WRITTEN: false
  KERNEL_GATE_REQUIRED: false

CLOSES:
  - G2_NUMERIC_ROPES_CRITICAL_PATH_ADJUDICATION
OPENS: []

DECISION:
  M13_N120_NUMERIC_ROPES_ON_CLASSICAL_ROOF_CRITICAL_PATH: false
  M13_N120_NUMERIC_ROPES_ON_ROUTE058_CRITICAL_PATH: false
  EXACT_ROLE: FINITE_CELL_VALIDATION_AND_FALSIFIER
  MAY_SUPPORT_FUTURE_FAMILY_THEOREM_DESIGN: true
  MAY_INHABIT_SLOT_H2A_BY_ITSELF: false

CONSUMER_AUDIT:
  SLOT_H2A_QUANTIFIER: FOR_ALL_K_ON_ONE_PARENT_COFINAL_PATH
  CONTROL_CELL_QUANTIFIER: ONE_FIXED_PAIR_M13_N120
  DIRECT_LEAN_EDGE_CONTROL_CELL_TO_SLOT_H2A: absent
  REQUIRED_G2_SUPPLIER_CLASS:
    - SIEG_OF_PENALTY_ON_THE_FAMILY
    - OR_COFINAL_SIMPLE_EVEN_GROUND_PACKAGE

ROPE_RECLASSIFICATION:
  OLD_LABEL: NUMERIC
  NEW_LABEL: VALIDATION_ONLY_ARB_INTERVAL
  ROUTE_COST: ZERO_ON_CRITICAL_PATH
  OPTIONAL_FORMALIZATION_COST: CERTIFICATE_WALL

COUNTS_AFTER_VERDICT:
  CLASSICAL_ROUTE:
    BEFORE: 17
    REMOVE: 3
    AFTER: 14
  ROUTE058:
    BEFORE: 14
    REMOVE: 0
    AFTER: 14
  SIMPLE_EVEN_DEDUP_FLAG:
    status: STILL_PENDING
    note: SIMPLE_EVEN_15_may_coincide_with_N1_after_N1_is_constructed

OPTIONAL_VALIDATION_REPRESENTATIONS:
  - code: KEEP_ARB_INTERVAL_ARTIFACT
    role: VALIDATION_ONLY
    kill_power: 5/10
    cost: 0/10
    route_effect: NONE
  - code: PARITY_BLOCK_INTERVAL_LDL_IMPORT
    role: MACHINE_CHECKABLE_ONE_CELL_COMPANION
    kill_power: 6/10
    cost: 5/10
    route_effect: NONE_WITHOUT_FAMILY_TRANSFER
  - code: RATIONAL_WEIGHTED_SQUARE_241
    role: EXACT_ONE_CELL_POSSEMIDEF_CERTIFICATE
    kill_power: 7/10
    cost: 10/10
    route_effect: NONE_WITHOUT_FAMILY_TRANSFER
  - code: SMALLER_CONTROL_CELL
    role: CHEAP_REGRESSION_PLANT
    kill_power: 2/10
    cost: 2/10
    route_effect: NONE

MINIMAL_MISSING_IDENTITY: >-
  Construct one source-locked cofinal family and prove the penalty/simple-even
  package at every parent index; no theorem about the single cell (13,120)
  can replace this universal parent-path obligation.

REGISTERED_PREDICTIONS:
  PRETEST_PREDICTION: NONE
  SCORE: NOT_APPLICABLE
  DISCIPLINE_NOTE: the queue already supplied the exact quantifier mismatch

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: FALSIFICATION_PROGRESS
COGNITIVE_OPERATOR: UNIT_AUDIT
ROUTE_SCORE: 5
```

## ROUTE MAP

### V-a — the three numeric items are not roof ropes

The roof type is decisive:

```lean
SlotH2a C H2aAt := ∀ k, H2aAt (C.parent k).
```

It consumes the whole fixed parent path.  The control-cell result proves one
statement at the single truncation `(m,N)=(13,120)`.  Its own closeout states
explicitly that it is not `SlotH2a`, not an all-parameter input, not a uniform
operator gap, and not a limit theorem.

Therefore there is no legal implication

```text
finite certificate at (13,120)
→ SlotH2a on a cofinal parent family.
```

The missing edge is not a tactic or certificate-format issue.  It is a
quantifier mismatch:

```text
FINITE_CELL
≠
COFINAL_FAMILY.
```

No production theorem consumes the `(13,120)` artifact and returns
`SlotH2a`.  The actual consumer must be a family theorem such as
`SIEG_of_penalty`, or the cofinal ground package used by Route 058.

### V-b — do not spend the rational-certificate wall on a noncritical cell

Since the cell is not a roof dependency, the cheapest correct action is to
retain its existing Arb interval certificate as a validation/falsification
artifact and stop.

If a later publication or regression policy separately requires a
machine-checked one-cell companion, the cheapest plausible representation is
the already exposed even/odd block decomposition followed by an imported
interval LDL certificate.  This is substantially cheaper than generating one
giant exact weighted-square identity for the full `241×241` matrix.  It still
proves only the same finite cell.

A smaller cell is useful as a parser/sign/normalization plant, but its
mathematical kill-power against the roof is low.  Direct Lean interval
arithmetic would require new checker infrastructure and is irrational while
no cofinal consumer exists.

### V-c — corrected route arithmetic

The three entries were labelled **NUMERIC**, which visually suggested cheap
remaining proof work.  That label was wrong in both possible readings:

- as roof inputs, their cost is **zero**, because they are not on the path;
- as optional machine formalization, their cost is a **certificate wall**.

The corrected counts are therefore:

```text
classical route: 17 − 3 = 14;
Route 058:       14 − 0 = 14.
```

The separate dedup flag `SIMPLE_EVEN:15 ~ N1` remains unresolved until N1 is
constructed.  This verdict does not pre-score that future identification.

## STRONGEST ATTACK

> A successful `(13,120)` certificate could seed or calibrate the future
> family theorem, so deleting it from the roof undercounts useful work.

It can seed a conjecture, choose a certificate language, falsify signs and
normalizations, and provide a regression cell.  None of those roles is a
logical premise of `SlotH2a`.  A calibration artifact becomes roof-critical
only after an explicit theorem transports it to every parent index.  No such
transport exists, and finite numerics cannot occupy the universal quantifier.

The repaired statement is exact:

```text
The `(13,120)` certificate is valuable finite evidence and validation.
It is not one of the logical ropes from the source family to the RH roof.
```

## FINAL PROPOSAL

Remove the three NUMERIC cell entries from both critical-path ledgers.  Keep a
single validation node off to the side:

```text
CCM_CONTROL_CELL_M13_N120_INTERVAL_VALIDATION
```

Do not launch the `241×241` rational weighted-square generator for roof
closure.  Spend G2 effort only on the family-level supplier:

```text
COFINAL_SIMPLE_EVEN_GROUND_SUPPLIER
```

or on a theorem that constructs `SIEG_of_penalty` on the same precommitted
parent path.

## CODEX DIRECTIVE

```text
NO LEAN EXECUTION FOR REQ-2026-08-20-B.

Cartographer/state body only:
  remove the three m=13 NUMERIC entries from critical-path counts;
  retain one off-path ARB_INTERVAL validation node;
  set classical count to 14;
  leave Route 058 count at 14;
  preserve the pending SIMPLE_EVEN:15 ~ N1 dedup flag.
```

## META CLOSEOUT

**What became smaller?**  The apparent roof count loses three non-consuming
finite-cell entries.

**What was killed?**  The implication `one m=13 certificate → family SlotH2a`.

**What must not be tried again?**  Do not promote one fixed cell, however
accurately certified, into a cofinal family supplier.

**Current smallest named G2 gap?**

```text
COFINAL_SIMPLE_EVEN_GROUND_SUPPLIER.
```

**Next cheapest decisive test?**  Source-lock the exact family theorem head and
check whether any existing cofinal penalty/floor supplier inhabits all of its
premises.

**Prediction fate?**  None was registered before the disk measurement; none is
invented retroactively.
