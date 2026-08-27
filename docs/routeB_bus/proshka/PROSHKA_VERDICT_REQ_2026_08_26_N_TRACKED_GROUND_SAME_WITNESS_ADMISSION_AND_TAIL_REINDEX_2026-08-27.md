# STATUS: PROVED — TRACKED GROUND SAME-WITNESS FINITE LOCK IS KERNEL-GREEN; EVENTUAL-FLOOR TAIL API REMAINS
```yaml
PRIMARY: RATIFY_SELECTED_FERRERS_TRACKED_GROUND_SAME_WITNESS_LEAN
PRIMARY_COUNT: 1

QUEUE:
  QUEUE_REQ_ID: REQ-2026-08-26-N
  ADJUDICATION_ROLE: POST_GATE_CLOSEOUT
  SOURCE_QUEUE: docs/routeB_bus/PROSHKA_QUEUE.md
  QUEUE_STATUS_MUTATED: false
  STALE_OPEN_ENTRY_OBSERVED: REQ-2026-08-21-P_HAS_PRIOR_VERDICT_AND_IS_NOT_REANSWERED

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  HEAD: cd930f545af434339d3283e5b7b40b07c4968a8e
  HEAD_IS_ORIGIN_RH_CLEAN_AT_AUDIT: true
  PARENT: 2d69179687b9b0a5e8f284d5ea7807fc76ee0584
  COMMIT_MESSAGE: "[Linux-Claude][rh_clean][Goal058] Tracked ground transform: real zeros and pointwise tracking"
  FILE_DELTA:
    - docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM_2026-08-27.md
    - q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  UNRELATED_FILES_CHANGED: false

LEAN_ARTIFACT:
  path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  git_blob: 0296bb09885805e78b22183cbf14c70023265d8a
  sha256: d65c282a2760f63f72008fa974129b18f689dc33279f7791653f692f730469df
  lines: 668
  public_surface:
    - selectedFerrersTrackedGroundEigenvalue
    - selectedFerrersTrackedGroundVector
    - selectedFerrersTrackedGroundVector_spec
    - selectedFerrersTrackedGroundOverlap
    - selectedFerrersTrackedGroundResidualFloorRatio
    - selectedFerrersTrackedGroundScale
    - selectedFerrersTrackedGroundTransform
    - selectedFerrersTrackedGroundTransform_realZeros_and_pointwiseTracking_of_sectorFloors

SOURCE_RECORD:
  path: docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TRANSFORM_2026-08-27.md
  git_blob: 0f18b43381820810fecaad3c201ab07dbeb1d317
  process_nonconformities:
    - MARKDOWN_HEADING_PRECEDES_YAML
    - COMMIT_FIELD_IS_PLACEHOLDER
    - SOURCE_RECORD_BLOB_MISSING_FROM_YAML
    - AXIOM_PROFILE_NOT_LISTED_FOR_PUBLIC_THEOREM_selectedFerrersTrackedGroundVector_spec
  receipt_repair: THIS_VERDICT_PINS_THE_EXACT_COMMIT_AND_BLOBS

KERNEL_GATE:
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_LAKE_BUILD: false
  JUDGE_RERAN_Q3_CHECK: false
  LINUX_REPORTED_DIRECT_LEAN_EXIT: 0
  LINUX_REPORTED_TARGET_BUILD: "OK, 7927 jobs"
  LINUX_REPORTED_HOLE_SCAN: 0
  LINUX_REPORTED_Q3_CHECK: ok
  REPORTED_AXIOM_PROFILE_FOR_MAIN_THEOREM:
    - propext
    - Classical.choice
    - Quot.sound
  SEMANTIC_SOURCE_AUDIT: PASS

ADJUDICATION:
  theorem_statement_preserved: true
  theorem_weakened: false
  exact_selected_index_preserved: true
  exact_source_matrix_preserved: true
  exact_trial_rayleigh_shift_preserved: true
  tracked_ground_vector_selected_once: true
  real_eta_normalized_representative_selected_independently: true
  eigenvalue_equality_proved: true
  same_one_dimensional_ground_line_proved: true
  source_order_to_P59_reversed_label_crosswalk_proved: true
  production_argument_reflection_preserved: true
  final_scalar_nonzero_proved: true
  real_zeros_and_tracking_on_same_named_function: true
  trial_equals_ground_assumption: false
  asymptotic_transfer_of_real_rootedness: false
  second_ground_function_used_for_tracking: false
  numerical_input: false
  schedule_change: false

API_SCOPE_CORRECTION:
  current_transform_parameter:
    hfloor_shape: "forall j, literal complement floor at j with one fixed beta"
  available_source_floor_shape:
    status: EVENTUAL
    theorem: selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
  consequence:
    finite_same_witness_mathematics: CLOSED
    direct_eventual_floor_consumability: OPEN
    broad_cofinal_rate_assembly_authorized_now: false
  corrected_next_gap: SELECTED_FERRERS_EVENTUAL_FLOOR_TO_TRACKED_GROUND_TAIL_REINDEX

CLOSES:
  - SELECTED_FERRERS_TRACKED_GROUND_FUNCTION_SAME_WITNESS_LOCK_UNDER_GLOBAL_FLOOR_DATA
  - SELECTED_FERRERS_SOURCE_ORDER_P59_EVEN_ROW_CROSSWALK
  - SELECTED_FERRERS_TRACKED_GROUND_REAL_ZERO_AND_POINTWISE_TRACKING_PAIR
OPENS: []
CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_EVENTUAL_FLOOR_TO_TRACKED_GROUND_TAIL_REINDEX
  - SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY

SCOPE: FINITE_CELL
VERIFIER: LEAN
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_TRACKED_GROUND_EVENTUAL_TAIL_REINDEX
  MODE: LEAN_SOURCE_TRANSACTION
  MODIFY_APPEND_ONLY:
    - q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  CREATE:
    - q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean
    - docs/routeB_bus/LINUX_SOURCE_RECORD_GOAL058_SELECTED_FERRERS_TRACKED_GROUND_TAIL_REINDEX_2026-08-27.md
  PUBLIC_TARGETS:
    - selectedFerrersTrackedGroundTransformAt_realZeros_and_pointwiseTracking_of_sectorFloors
    - selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors
  SUCCESS_CODE: SELECTED_FERRERS_TRACKED_GROUND_EVENTUAL_TAIL_REINDEX_LEAN
  FAILURE_CODE: GOAL058_TRACKED_GROUND_POINTWISE_FLOOR_OR_TAIL_REINDEX_API_GAP

NEXT_AFTER_SEMANTIC_ADMISSION_ONLY:
  TASK_ID: GOAL058_SELECTED_FERRERS_GROUND_COFINAL_RATE_ASSEMBLY
  REQUIRED_RATE_OBJECT: >-
    compact centering-factor times source kernel envelope times
    sqrt(selectedFerrersTrackedGroundResidualFloorRatio) tends to zero
    along the exact tail reindex

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. Kernel admission

The execution commit is one direct child of the prior Proshka verdict and adds exactly the authorized Lean source plus its source record. Linux reports direct Lean exit `0`, a successful target build, zero holes, `q3_check ok`, and the standard axiom triple for the main public theorem. The judge did not rerun the toolchain. `[FINITE_CELL][LEAN]`

The source theorem has the ordered conclusion required by the prior verdict:

```text
one named tracked ground transform;
ZerosRealOn Set.univ for that transform;
one exact pointwise tracking bound for that same transform.
```

No theorem statement was weakened. `[FINITE_CELL][LEAN]`

### 2. The same-witness objection is actually killed

The tracked complex ground vector and the real eta-normalized ground representative are obtained by independent choices. The proof does not identify them by prose or by shared carrier. It proves:

1. the two bottom eigenvalues are equal, by testing each bottom inequality on an eigenvector belonging to the other package;
2. the complexification of the real representative lies on the tracked one-dimensional ground line, using the positive complement gap;
3. the proportionality scalar is nonzero, because the eta-normalized real vector is nonzero.

Thus the independent choices differ only by one proved nonzero scalar on the same ground line. This kills the prior **C04 SAME-COORDINATES-TWO-LAWS** objection at the finite-cell boundary. `[FINITE_CELL][LEAN]` **[C04]**

### 3. The exact function carrying real zeros is the tracked function

For an even real row, the source-ordered coefficients and the Proposition-59 reversed-label coefficients agree on the entire finite carrier. The proof retains the production argument reflection:

\[
\operatorname{sourceOrderedRaw}(\xi_R,z)
=
\operatorname{P59}(\xi_R,-z).
\]

Reality of zeros is then transported through `z ↦ -z` and through a proved nonzero scalar. Nonvanishing is paid by all three required factors:

```text
centeredXi(0) != 0;
rawFplus(k,0) != 0;
tracked overlap != 0 from ratio < 1.
```

Therefore the theorem is about the exact transform used by the tracking inequality, not a neighboring Lagrange polynomial, trial transform, or independently selected ground transform. This passes **C10 FUNCTIONAL-NOT-SURROGATE**. `[FINITE_CELL][LEAN]` **[C10]**

### 4. The pointwise tracking estimate is exact

The second conclusion is the literal estimate

\[
\|G_k(z)-P_k(z)\|
\le
\left\|\frac{\Xi(0)}{\operatorname{rawFplus}_k(0)}\right\|
\operatorname{KernelL2}_k(z)
\sqrt{\operatorname{ResidualFloorRatio}_k}.
\]

It uses the exact selected trial row, exact source-ordered kernel, exact projective overlap, and the literal residual energy divided by `beta^2`. No asymptotic notation, fitted constant, or numerical replacement occupies a quantifier. `[FINITE_CELL][LEAN]`

### 5. Scope correction: the next gap is one API seam earlier than the source record says

The current named tracked transform accepts

```lean
hfloor : forall j, complementFloor(j, beta).
```

The existing source theorem supplies only

```lean
eventually j, complementFloor(j, beta0 / 2).
```

A global floor family cannot be manufactured from an eventual floor by filling the finite prefix with nonexistent proofs. Nor may the finite prefix be silently discarded without an exact cofinal reindex receipt. `[COFINAL_FAMILY][PAPER]` **[C04]**

This does **not** invalidate the proved finite same-witness theorem. It narrows its executable boundary:

```text
finite same-witness function lock under global floor data:
  PROVED.

eventual source floor -> total tracked cofinal family:
  OPEN, assembly-only.
```

Accordingly, the source-record code

```text
SELECTED_FERRERS_GROUND_CANONICAL_FAMILY_SAME_WITNESS_LOCK
```

is accepted only with the qualifier `UNDER_GLOBAL_FLOOR_DATA`. The broad cofinal rate assembly is delayed by exactly one typed tail-reindex node.

### 6. Required next transaction

The next source transaction must expose a pointwise tracked transform whose construction takes only the floor at the current cell. Existing global declarations remain unchanged and may become wrappers around the pointwise declarations.

A minimum public shape is:

```lean
noncomputable def selectedFerrersTrackedGroundTransformAt
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : Nat) (beta : Real)
    (hfloorAt :
      complexTrialComplementFloor
        (sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k))
        (selectedFerrersFiniteCCMRow P k)
        (((selectedFerrersFiniteCCMRayleigh P k : Real) : Complex))
        beta) : Complex -> Complex
```

and:

```lean
theorem selectedFerrersTrackedGroundTransformAt_realZeros_and_pointwiseTracking_of_sectorFloors
    ...
    (hfloorAt : <floor at k>)
    (hoddFloorAt : <odd-sector floor at k>)
    (hratio : selectedFerrersTrackedGroundResidualFloorRatio P beta k < 1) :
    ZerosRealOn Set.univ
      (selectedFerrersTrackedGroundTransformAt P k beta hfloorAt) /\
    forall z,
      norm
        (selectedFerrersTrackedGroundTransformAt P k beta hfloorAt z -
          (selectedFerrersCofinalSourceData P).centeredPstar k z) <=
        <the exact existing right-hand side>
```

The new tail layer must then consume eventual floor, eventual odd-sector floor, and eventual `ratio < 1`, and return one precommitted additive shift `phi(n)=n+k0` with:

```text
StrictMono phi;
Tendsto phi atTop atTop;
exact index/pair/sourceScale inherited from the same selected shell;
real zeros for every shifted tracked transform;
the exact pointwise tracking bound at phi(n).
```

No second diagonal, independently selected subsequence, or alternate shell is permitted.

### 7. Forbidden shortcuts

```text
- assume the eventual floor on the discarded finite prefix;
- replace an eventual floor by a global floor hypothesis in the final source route;
- select one tail for real zeros and another tail for the rate;
- choose a new source shell without exact index/pair/sourceScale receipts;
- change any existing public theorem statement;
- identify trial and ground rows;
- transfer real-rootedness through closeness;
- reopen W5 or N2/N3/N4;
- claim cofinal H2a, SlotS2, route promotion, or RH.
```

### 8. Validation gate

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersTrackedGroundTailReindex

WORKDIR: repo root
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTransform.lean
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersTrackedGroundTailReindex.lean
```

Expected profile for every public theorem:

```text
[propext, Classical.choice, Quot.sound]
```

After semantic admission of the tail receipt, the next theorem may combine the same tail transform with the compact kernel-times-ratio rate and the already proved selected-trial convergence to `centeredXi`.

## FINAL PROPOSAL

Ratify the execution theorem at its exact finite-cell boundary. Do not jump directly to a cofinal convergence wrapper that assumes a global floor stronger than the available eventual supplier. First expose the pointwise floor API and one exact tail reindex; then run the cofinal rate assembly on that same reindexed family.

Registered predictions:

```yaml
P_GROUND_SAME_WITNESS_LOCK_1:
  prior_probability: 0.88
  fate: CONFIRMED

P_GROUND_SAME_WITNESS_LOCK_2:
  prior_probability: 0.74
  fate: NOT_TRIGGERED
  note: the reversed-label and argument-reflection normal form was solved; no kernel failure occurred

P_GROUND_TAIL_REINDEX_1:
  probability: 0.93
  prediction: >-
    A pointwise floor-parametrized tracked transform plus one additive tail
    shift closes the eventual/global API seam without a new analytic input.

P_GROUND_COFINAL_RATE_1:
  probability: 0.76
  prediction: >-
    After the tail receipt, the first substantive remaining failure is the
    compact kernel-envelope times sqrt residual/floor ratio rate, not object
    identity or zero-set provenance.
```

## STRONGEST ATTACK

The strongest objection to the execution report is not the old two-witness attack; that attack is dead. The strongest remaining objection is:

> The theorem's family object requires a complement-floor proof for every natural index, while the actual source pipeline proves the floor only eventually. Therefore the current object cannot yet be instantiated from the source theorem on the exact cofinal route.

This objection is valid but repairable. It is a type/API seam, not a mathematical counterexample to the same-witness theorem. The repaired statement is the pointwise transform plus one exact tail reindex above.

## META CLOSEOUT

**What became smaller?**

The ground real-zero object and the ground tracking object are now one exact named function. The former source-family identity wall has collapsed to a finite-prefix/tail API seam.

**What was killed?**

```text
two independent ground functions under one name;
real-rootedness transfer through asymptotic closeness;
missing reversed-label and argument-orientation crosswalk;
zero projective overlap hidden by a zero scalar.
```

**What must not be tried again?**

Do not glue two `Classical.choose` outputs by saying “the ground state is simple.” Prove their common line. Do not feed an eventual floor into a global-floor family without a reindex receipt.

**Current smallest named gap:**

```text
SELECTED_FERRERS_EVENTUAL_FLOOR_TO_TRACKED_GROUND_TAIL_REINDEX
```

**Next cheapest decisive test:**

Compile the pointwise floor-parametrized tracked transform and the one additive cofinal tail receipt.

**Prediction fates:**

```text
P_GROUND_SAME_WITNESS_LOCK_1: CONFIRMED.
P_GROUND_SAME_WITNESS_LOCK_2: NOT_TRIGGERED.
```

**Memory entry:**

```yaml
iteration:
  target: selected_Ferrers_tracked_ground_same_witness
  status: PROGRESS
  failed_strategy: global_floor_indexed_family_as_direct_consumer_of_eventual_floor
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_EVENTUAL_FLOOR_TO_TRACKED_GROUND_TAIL_REINDEX
  invariant_learned: one_ground_function_must_carry_real_zeros_and_tracking_on_one_exact_tail
  forbidden_future_move: do_not_replace_eventual_floor_by_global_floor_without_reindex
  next_decisive_test: compile_pointwise_tracked_ground_and_additive_tail_receipt
```
