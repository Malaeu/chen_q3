# GOAL 056 — K8 Müntz-v3 to strict SlotS2 bridge — Phase 0

```yaml
GOAL: 056
PARENT: null
KIND: STANDING_ROOT
BUS: NONE
STATUS: PHASE0_INTERFACE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD

OPERATIVE_CLASS: TRY_G6_S2_K8_SOURCE_FAITHFUL_BRIDGE_PHASE0
PROSHKA_RESPONSE_MESSAGE_ID: beb7b7d4-ec38-4844-b0e9-63e5f9d2fb98
PIN: 1efda3f80580eb036680f5fd272d3f5112b59283

CANON_ROOF:
  path: q3.lean.aristotle/aristotle_output/output-final_aristotle/RequestProject/Main.lean
  sha256: d7fe57b57ae0d08bd474de6f283565168bac9e33dd55d6719289466c7065e90f
  status: NOT_PROOF_NOT_PROMOTED_RAW_ARISTOTLE

STRICT_CONSUMER:
  slot: Q3.RouteB.CanonicalRHRoute.SlotS2
  assembly: Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots

K6_OUTCOME_EXACTLY_ONE:
  - S2_BRIDGE_LOCAL_VIABLE
  - S2_BRIDGE_NEEDS_NAMED_WEAKENING
  - S2_SLOT_SEMANTIC_GAP
```

All other `RequestProject/Main.lean` files under `aristotle_output/` are
`NON_CANON_FOR_056`.  `CANON_ROOF` selects a working theorem-shape object only;
it supplies no proof and authorizes no production import.

## K6 object precommit

```yaml
K6_OBJECT_PRECOMMIT:
  canonical_family:
    Q3.RouteB.CanonicalRHRoute.selectedFamily
      (Q3.RouteB.D0Pstar.canonicalApproximation D)
  canonical_raw_object:
    Q3.RouteB.D0Pstar.centeredPstarFamily D.kTrial
  source_trial:
    Q3.RouteB.D0Pstar.prolateCombination P
  source_identity:
    EStarMuntzZeroMassContinuation.
      continued_window_identity_prolateCombination_v3Class_of_modeLipschitz
  producer_function:
    Gwin (Q3.RouteB.D0Pstar.prolateCombination P) Λ
  strict_consumer:
    Q3.RouteB.CanonicalRHRoute.SlotS2
      (Q3.RouteB.D0Pstar.canonicalApproximation D)
  direct_downstream:
    Q3.RouteB.CanonicalRHRoute.rh_of_canonical_strip_slots
  relation_under_test: >-
    exact equality or locally-uniform-on-compacts defect-to-zero between the
    canonical selected family and the normalized source Müntz representation
    on the same parent/extract sequence
  invariant_cargo:
    - exact source trial
    - independent pair carrier (m,N)
    - parent and nested extraction
    - centered coordinate orientation
    - anchor normalization
    - zero-free gauge
    - finite-Galerkin error
    - Rminus and Rplus terms
    - compact-by-compact topology
    - every-ClusterData quantifier
  forbidden_substitutions:
    - fixed PL2 or any independently selected window
    - independent diagonal or subsequence
    - fitted scalar normalization
    - tail analyticity relabeled as tail smallness
    - raw Aristotle SlotS2 relabeled as production SlotS2
```

`[COFINAL_FAMILY][CONDITIONAL]`.  This object is frozen before the Phase-0
plants fire; any repaired object is a new named transaction.

## Phase-0 task

1. Verify the numbered-object inventory and every hash gate before mint.
2. Compare exact types for `CanonicalApproximation`, `selectedFamily`,
   `ClusterData`, production `SlotS2`, `centeredPstarFamily`, `parent`,
   `extract`, `Gwin`, `ZetaMellinPoleSub`, `Rminus`, `Rplus`, `ProlatePair`,
   `prolateCombination`, `centeredGauge`, the raw roof `SlotS2`/`supply_S2`,
   and `rh_of_canonical_strip_slots`.
3. Classify each required equality as `DEFINITIONAL`, `PROVED`,
   `CONDITIONAL`, or `MISSING`.
4. Run an untracked proposition/typecheck harness with no `sorry`, `admit`,
   `axiom`, `opaque`, or `native_decide`.  Separately check the production
   project and the exact request-project source if their module paths differ;
   report that split as packaging, not mathematics.  Delete the harness after
   recording its SHA-256 and stdout.
5. Fire all five plants and return exactly one K6 outcome.

## Plants

```yaml
P056_1:
  mutation: replace the source-prolate D0 family by fixed PL2
  expected: SURROGATE_OBJECT_REJECTED
P056_2:
  mutation: replace every ClusterData quantifier by one chosen cluster
  expected: NOT_LOCAL_VIABLE_WITHOUT_NAMED_WEAKENING
P056_3:
  mutation: infer tail convergence from Rminus/Rplus analyticity
  expected: TAIL_ANALYTICITY_NOT_TAIL_SMALLNESS
P056_4:
  mutation: flip centered z sign or rawFplus orientation
  expected: CENTERED_PHASE_ORIENTATION_MISMATCH
P056_5:
  mutation: use an independent Müntz extraction
  expected: SAME_COFINAL_FAMILY_VIOLATION
```

## Outcome contract

- `S2_BRIDGE_LOCAL_VIABLE` requires an exact minimal theorem on the production
  types, the same D0 parent/extract family, centered orientation and gauge,
  explicit finite-Galerkin error and tails, and literal production `SlotS2`.
- `S2_BRIDGE_NEEDS_NAMED_WEAKENING` requires the exact dropped quantifier or
  domain plus a separately named, hole-free roof theorem showing that the
  weakened slot still feeds the honest consumer.
- `S2_SLOT_SEMANTIC_GAP` must state the missing implication exactly and select
  one smallest executable object/test.  The preferred object is
  `D0PstarToMuntzSameFamilyLocallyUniformCrosswalk`; a sufficient-strategy
  failure does not kill the bridge family.

## Validation and boundaries

- direct Lean: `CanonicalRHRouteSkeleton.lean`,
  `D0CanonicalApproximation.lean`, `S2GaugeNonvanishing.lean`,
  `MuntzV3ExactClassClosure.lean`, and
  `MuntzV3ProlateCombinationReceiver.lean`;
- canon/mirror goal and answer byte equality;
- exactly one K6 outcome; `routeb_status.py --check`; `git diff --check`;
- no production Lean edit, Aristotle submission, physical Bus 010, Goal-055
  change, raw-roof proof import, silent `SlotS2` weakening, Route-B promotion,
  or PX/RH claim.

```text
STOP: G6_S2_K8_BRIDGE_PHASE0_UNCLASSIFIED
SUCCESS: G6_S2_K8_BRIDGE_PHASE0_K6_CLASSIFIED
```

`CHALLENGER / NOT_RH`; Bus 010 `VOID`; Goal 055 `HOLD`;
`ARISTOTLE_SUBMISSION: NONE`; `PX_RH_CLAIM: NOT_MADE`.
