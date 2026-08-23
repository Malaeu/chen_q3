# STATUS: PROVED — H2A.1 SEMANTICALLY ADMITTED; EXACT FULL COMPLEMENT-FLOOR TRANSPORT CLOSED; H2A.2 SELECTED SOURCE-QUANTITIES LOCK AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 5716c749792c334f6d4f682be7b34007aea89186
  SOURCE_COMMIT: 5716c749792c334f6d4f682be7b34007aea89186
  ACTUAL_PARENT: 95d4502961b37bcd579b2a85037e8eb9f6d3d450
  CLAIMED_PARENT: 95d4502961b37bcd579b2a85037e8eb9f6d3d450
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean
  LEAN_GIT_BLOB: fe1f65d028002e11f404d46e2c05937f61ac33b1
  LEAN_SHA256_REPORTED: 28c78e58692c1cdecf32a07c509fffd1881ad4dab9cbccf3ea0ad45b074f196f
  LEAN_LINES_REPORTED: 800
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: ddb1b72c63053e526a43bf2f12fe7262f340eaf5
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7795_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    oddMass_without_residual_control_does_not_force_complementFloor_plant:
      - propext
      - Classical.choice
      - Quot.sound
    complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_FINITE_REFLECTION_CONTAMINATION_TRANSPORT
  PRIMARY_THEOREM: Q3.RouteB.complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
  OUTPUT_PREDICATE: Q3.RouteB.complexTrialComplementFloor
  OUTPUT_DOMAIN: FULL_LITERAL_Q_ORTHOGONAL_COMPLEMENT
  PARITY_ONLY_SURROGATE_USED: false
  TRIAL_REPLACED_BY_EVEN_PROJECTION: false
  EXACT_TRIAL_PARITY_ASSUMED: false
  REALIFICATION_ASSUMED: false
  FIXED_OR_FITTED_SHIFT_ASSUMED: false
  RESIDUAL_INPUT_LOAD_BEARING: true
  SECTOR_FLOORS_LOAD_BEARING: true
  ODD_MASS_LOAD_BEARING: true
  FULL_Q_PERP_PROJECTOR_PLUMBING_EXACT: true
  C04_OBJECT_AUDIT: PASS
  C10_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

EXACT_FORMULA_AUDIT:
  ETA:
    definition: norm_square_of_half_q_minus_Jq
    range_used: 0_le_eta_and_eta_lt_1
  BASE_SECTOR_FLOOR: min_betaPlus_betaMinus
  EFFECTIVE_FLOOR: >-
    betaEff = min(betaPlus,betaMinus) * (1-eta)
      - ((2*sqrt(eta)+eta)/sqrt(1-eta)) * rho
  FORMULA_PROVED_VERBATIM: true
  FORMULA_WEAKENED: false
  FITTED_CONSTANT_USED: false
  NUMERIC_CERTIFICATE_USED: false

KEY_GEOMETRY:
  EVEN_ODD_PROJECTORS: P=(I+J)/2_and_M=(I-J)/2
  TRIAL_SPLIT: q=qPlus+qMinus
  TEST_SPLIT: v=vPlus+vMinus
  EVEN_COMPONENT_SPLIT: vPlus=u+w_with_u_parallel_qPlus_and_w_orthogonal_qPlus
  Q_ORTHOGONALITY_IDENTITY: inner(qPlus,vPlus)=-inner(qMinus,vMinus)
  DECISIVE_BOUND: norm(u)^2_le_eta_times_norm(v)^2
  DECISIVE_BOUND_SOURCE: >-
    Cauchy-Schwarz first gives norm(u)^2*(1-eta) <= eta*norm(vMinus)^2;
    the exact Pythagorean identity also gives
    norm(vMinus)^2 <= norm(v)^2-norm(u)^2;
    combining both cancels the apparent extra denominator and yields
    norm(u)^2 <= eta*norm(v)^2.
  RESIDUAL_TRANSPORT: >-
    S=K-aI commutes with J, so S(qPlus) is the even component of S(q),
    hence norm(S(qPlus)) <= norm(S(q)) <= rho and
    norm(S(normalized_qPlus)) <= rho/sqrt(1-eta).
  CONTAMINATION_TERMS: one_quadratic_plus_two_cross_terms
  CONTAMINATION_LOSS: ((2*sqrt(eta)+eta)/sqrt(1-eta))*rho

PLANT_AUDIT:
  PLANT: oddMass_without_residual_control_does_not_force_complementFloor_plant
  STATUS: PASS
  CARRIER: Fin_3
  K: matrix_0_100_0__100_1_0__0_0_1
  J: diagonal_1_1_minus1
  Q: [60/61,0,11/61]
  ODD_MASS: 121/3721
  ODD_MASS_LT_ONE_OVER_25: true
  EVEN_SECTOR_FLOOR: 1
  ODD_SECTOR_FLOOR: 1
  Q_PERP_NEGATIVE_VECTOR: [11/61,-1,-60/61]
  NEGATIVE_ENERGY: -126879/3721
  MEANING: >-
    Sector floors and arbitrarily small reflection contamination do not force
    a positive floor on the literal q-perpendicular complement when the
    coupling from the even trial direction is uncontrolled. The rho input
    cannot be deleted or replaced by an informal boundedness claim.

MINOR_TYPE_NOTE:
  PUBLIC_HETA_NONNEG_HYPOTHESIS_REDUNDANT_FROM_EXACT_ETA_IDENTITY: true
  SEMANTIC_DEFECT: false
  ACTION: KEEP_VERBATIM_DIRECTIVE_SHAPE

H2A_BOUNDARY:
  GENERIC_REFLECTION_CONTAMINATION_TRANSPORT: CLOSED
  FULL_COMPLEMENT_FLOOR_FROM_QUANTITATIVE_INPUTS: CLOSED
  SELECTED_FERRERS_FINITE_ROW_OBJECT_LOCK: CLOSED_BY_H2A_0
  SELECTED_COMPLEX_REFLECTION_OBJECT: OPEN
  SELECTED_RAYLEIGH_AND_RESIDUAL_OBJECTS: OPEN
  SELECTED_ODD_MASS_PHYSICAL_REPRESENTATION: OPEN
  SELECTED_SECTOR_FLOORS: OPEN
  SELECTED_ODD_MASS_RATE: OPEN
  SELECTED_RESIDUAL_RATE: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  GROUND_PARITY: OPEN
  REAL_GROUND_REPRESENTATIVE: OPEN
  ETA_NORMALIZATION_OF_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN

BROAD_NEXT_GAP_REPAIR:
  REJECT_AS_ONE_TRANSACTION: SELECTED_FERRERS_SECTOR_FLOORS_ODD_MASS_RESIDUAL_RATE_SUPPLY
  REASON: >-
    This name conflates four heterogeneous source obligations: exact reflection
    and shift objects, odd-mass representation/rate, residual representation/rate,
    and two sector floors. Formalizing them in one node would hide object
    mismatches and violate one-goal/one-semantic-bridge discipline.
  SELECTED_FIRST_SUBFLOOR: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED
  CODE: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
    - Q3.Proofs.RouteB.CCMComplexTrialReflectionContaminationFloor
  PRIMARY_ROLE: >-
    Bind H2A.1 to the exact theorem-generated selected Ferrers shell without
    proving any analytic rate: expose the exact complex reflection, Rayleigh
    shift, residual, odd mass and physical reflection-defect representation,
    then provide the literal selected-source H2A.1 receiver.
  PUBLIC_SURFACE_REQUIRED:
    - ccmComplexReflectionMatrix
    - ccmComplexReflectionMatrix_mulVec
    - ccmComplexReflectionMatrix_isHermitian
    - ccmComplexReflectionMatrix_sq
    - sourceCCMFiniteMatrix_commutes_ccmComplexReflectionMatrix
    - selectedFerrersFiniteCCMRayleigh
    - selectedFerrersFiniteCCMResidual
    - selectedFerrersFiniteCCMOddPart
    - selectedFerrersFiniteCCMOddMass
    - selectedFerrersFiniteCCMReflectionDefect
    - ccmFiniteSynthesis_selectedFerrersFiniteCCMRow_eq_kTrial
    - selectedFerrersFiniteCCMOddMass_eq_quarter_norm_reflectionDefect_sq
    - selectedFerrersFiniteCCMResidual_orthogonal
    - selectedFerrersFiniteCCMComplementFloor_of_sectorFloors_oddMass_residual
  PUBLIC_SURFACE_POLICY: >-
    Helper declarations may be private only when no later source-rate theorem
    needs them. The exact row, index, shift and reflection used by the final
    receiver must remain inspectable; do not hide object identity behind simp.
  REQUIRED_PRIVATE_PLANTS:
    - unit_norm_does_not_determine_reflection_mass_plant
    - wrong_shift_breaks_residual_orthogonality_plant
  CLOSES:
    - SELECTED_FERRERS_COMPLEX_REFLECTION_OBJECT_LOCK
    - SELECTED_FERRERS_RAYLEIGH_RESIDUAL_OBJECT_LOCK
    - SELECTED_FERRERS_ODD_MASS_OBJECT_LOCK
    - SELECTED_FERRERS_ODD_MASS_PHYSICAL_REFLECTION_DEFECT_REPRESENTATION
    - SELECTED_FERRERS_H2A1_LITERAL_SOURCE_RECEIVER
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY

H2A_2_EXACT_OBJECTS:
  INDEX: (selectedFerrersCofinalSourceData P).index k
  ROW: selectedFerrersFiniteCCMRow P k
  MATRIX: D0Pstar.sourceCCMFiniteMatrix_of_the_same_selected_index
  REFLECTION_ACTION: row_j_maps_to_row_at_ccmNegFinite
  RAYLEIGH: real_part_of_star_row_dot_matrix_mul_row
  RESIDUAL: matrix_mul_row_minus_Rayleigh_smul_row
  ODD_PART: half_row_minus_reflected_row
  ODD_MASS: sum_of_complex_normSq_of_exact_odd_part
  PHYSICAL_DEFECT: >-
    exact selected kTrial synthesis minus finite synthesis of the reflected
    selected coefficient row, on the same selected PairIndex.
  EFFECTIVE_FLOOR: >-
    min(betaPlus,betaMinus)*(1-selectedOddMass)
      - ((2*sqrt(selectedOddMass)+selectedOddMass)
          /sqrt(1-selectedOddMass))*rho

H2A_2_PROOF_ROUTE:
  - Run ask.sh preflight before editing.
  - Define the complex reflection permutation on the literal CCM carrier.
  - Prove its mulVec action, Hermitian property and square identity from
    ccmNegFinite_involutive; do not import or coerce the old real trial row.
  - Prove the selected complex source matrix commutes with this reflection
    from the existing exact centrosymmetry theorem.
  - Define Rayleigh and residual from the exact selected row; prove residual
    orthogonality using the selected unit theorem and Hermitian Rayleigh
    reality, not by choosing a convenient shift.
  - Reprove publicly that finite synthesis of the selected row is the exact
    selected kTrial. The corresponding H2A.0 helper is private and may not be
    invoked through an interface substitution.
  - Prove selected odd mass equals one quarter of the squared norm of the
    exact physical reflection defect using orthonormal finite synthesis.
  - Instantiate H2A.1 literally. The final theorem may leave only the actual
    quantitative sector-floor, eta<1, rho-bound and betaEff-positive inputs.
  - Print axioms for every public theorem and both plants.

H2A_2_PLANTS:
  unit_norm_does_not_determine_reflection_mass_plant: >-
    On Fin 3 with reflection swapping coordinates 0 and 2, use the two unit
    rows [2/3,1/3,2/3] and [1,0,0]. The first has odd mass 0; the second has
    odd mass 1/2. Same carrier and unit norm do not identify reflection
    geometry.
  wrong_shift_breaks_residual_orthogonality_plant: >-
    Use a two-dimensional Hermitian diagonal matrix and a unit coordinate
    vector. The exact Rayleigh shift makes the residual orthogonal to the
    vector; replacing it by a different scalar gives a nonzero parallel
    component. A fixed or fitted shift is not the source residual.

FORBIDDEN:
  - replace_selectedFerrersCofinalSourceData_by_ProlateCanonicalSourceData
  - reuse_old_sourceCCMComplexRow_as_if_definitionally_equal
  - coerce_the_selected_complex_row_to_a_real_row
  - infer_exact_parity_from_unit_norm_or_source_evenness
  - replace_the_selected_row_by_its_even_projection
  - use_a_fixed_or_fitted_shift_instead_of_the_exact_selected_Rayleigh_value
  - hide_reflection_or_carrier_identity_behind_an_unproved_simp_bridge
  - add_sector_floor_rate_or_residual_rate_as_a_structure_field
  - bundle_cofinal_effective_floor_simple_ground_Theorem510_or_real_zeros
  - edit_H2A_0_or_H2A_1_or_L73_3_through_L73_8
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

VALIDATION:
  WORKDIR_Q3:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities
  WORKDIR_REPO_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
  EXPECTED_AXIOM_PROFILE_FOR_EVERY_PUBLIC_THEOREM_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound

SUCCESS: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN
FAILURE: H2A_2_SELECTED_COMPLEX_REFLECTION_RAYLEIGH_OR_PHYSICAL_ODD_MASS_CROSSWALK_GAP

CLOSES:
  - REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR
OPENS: []

NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_COMPLEX_REFLECTION_RAYLEIGH_RESIDUAL_ODD_MASS_SOURCE_LOCK
NEXT_CHEAPEST_DECISIVE_TEST: >-
  Prove the selected odd-mass physical reflection-defect identity before any
  asymptotic estimate. If that identity cannot be stated on the same selected
  row and PairIndex, the proposed source-rate lane is the wrong object.

REGISTERED_PREDICTIONS:
  P_H2A2_1:
    claim: exact_complex_reflection_matrix_properties_and_commutation_close_from_ccmNeg_involution_and_centrosymmetry
    probability: 0.95
  P_H2A2_2:
    claim: selected_odd_mass_physical_identity_reuses_H2A0_finite_synthesis_and_orthonormality_without_new_analysis
    probability: 0.92
  P_H2A2_3:
    claim: selected_source_receiver_is_a_literal_specialization_of_H2A1_after_object_lock
    probability: 0.97
  LIKELIEST_FAILURE: DEPENDENT_SELECTED_INDEX_OR_COMPLEX_REFLECTION_MATRIX_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A1_1:
    probability: 0.84
    fate: CONFIRMED
  P_H2A1_2:
    probability: 0.98
    fate: CONFIRMED
  P_H2A1_3:
    probability: 0.995
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: COMPLEX_REFLECTION_PROJECTOR_OR_SQRT_NORMAL_FORM
    fate: OBSERVED
  RETROACTIVE_REPAIR: false

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN
ARISTOTLE_AUTHORIZED: false
QUEUE_STATUS_MUTATED: false

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5
SCOPE: ABSTRACT
VERIFIER: LEAN
```

## ROUTE MAP

### H2A.1 semantic admission

The theorem proves the exact quantity consumed downstream: a positive lower
floor for the shifted matrix on the **full literal orthogonal complement of the
original complex trial row**. It does not replace the row by its even part and
it does not certify only the two reflection sectors separately. The final
matrix layer applies the pointwise bound to the existing Hermitian idempotent
trial-line complement, so the output is exactly `complexTrialComplementFloor`.
`[ABSTRACT][LEAN]`

The load-bearing estimate is

\[
\|u\|^2\le \eta\,\|v\|^2.
\]

A naive use of Cauchy--Schwarz alone appears to lose a factor
`1/(1-eta)`. The proof recovers the sharp bound by also using the complete
Pythagorean identity for `v`: the odd mass available to cancel the parallel
even component is itself bounded by `norm(v)^2-norm(u)^2`. Therefore the base
sector floor loses exactly the factor `1-eta`, while the residual coupling
alone pays the denominator `sqrt(1-eta)`. This yields the stated `betaEff`
without fitting or theorem weakening. `[ABSTRACT][LEAN]`

### Why the plant is decisive

The rational three-dimensional plant has both sector floors equal to one and
odd mass below `1/25`, but a strictly negative vector in the literal
`q`-orthogonal complement. The only quantity allowed to grow is the coupling
from the even trial direction into its even complement. Therefore the plant
kills the residual-free theorem exactly; it does not merely show that one
proof technique fails. `[ABSTRACT][LEAN]` **[C10]**

### Why the broad next gap must be split

H2A.1 is generic finite geometry. The selected Ferrers route still needs to
show that its **same theorem-generated complex row** is the row used by the
reflection, Rayleigh shift, residual, odd-mass measurement and sector floors.
The old `ProlateCanonicalSourceData` layer contains similar definitions, but
substituting that interface would be a same-coordinates/two-laws error. The
first selected-source node therefore locks the exact objects and proves the
physical re-representation of odd mass before any rate theorem is attempted.
`[COFINAL_FAMILY][LEAN]` **[C04][C10]**

## FINAL PROPOSAL

Freeze H2A.1. Do not build another abstract floor theorem and do not optimize
the constant yet.

The next transaction is the source-object firewall. It must leave the four
actual analytic obligations visible:

```text
selected even-sector floor;
selected odd-sector floor;
selected odd-mass decay;
selected residual bound/decay.
```

It must not attempt to prove them in the same file. Its purpose is to ensure
that every later rate theorem targets the same selected row, same carrier,
same reflection and same Rayleigh shift consumed by H2A.1.

### Validation

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
  lake build Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
```

Expected profile for every public theorem and both plants:

```text
[propext, Classical.choice, Quot.sound]
```

## STRONGEST ATTACK

> The exact effective-floor formula is too optimistic. Orthogonality to the
> contaminated trial gives only a parallel-even coefficient of size
> `sqrt(eta/(1-eta))`, so the sector-floor term should lose an extra
> denominator.

This attack would be fatal if the proof used only Cauchy--Schwarz. It does not.
The exact norm decomposition gives

\[
d^2(1-\eta)\le \eta\|v_-\|^2,
\qquad
\|v_-\|^2\le\|v\|^2-d^2.
\]

Combining them yields

\[
d^2\le\eta\|v\|^2.
\]

The denominator survives only in the estimate of the normalized even trial
direction under the shifted operator. That is exactly the residual term in the
reported formula. The Lean source proves both steps separately before the final
real-arithmetic assembly. `[ABSTRACT][LEAN]`

A second attack is that H2A.1 may be correct but useless because the selected
source lane could silently measure odd mass or residual on another row. That
attack is also correct against an immediate rate theorem and is why H2A.2 is an
object lock, not a rate claim. `[COFINAL_FAMILY][CONDITIONAL]` **[C04]**

## CODEX DIRECTIVE

```text
TASK:
  H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN

BASE_HEAD:
  Use this Proshka verdict commit, then run `git rev-parse HEAD` immediately
  before editing and record the exact parent.

CREATE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersH2aSourceQuantities.lean

CREATE IN THE SAME COMMIT:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_2026-08-23.md

FIRST ACTION:
  ./ask.sh "selected Ferrers complex reflection Rayleigh residual odd mass physical reflection defect"

PRIMARY OUTPUT:
  An exact selected-source instantiation of H2A.1 on
  `selectedFerrersFiniteCCMRow P k`, preceded by the source-object and physical
  odd-mass identities listed in the YAML header.

STOP CONDITION:
  If the physical reflection-defect identity cannot be proved for the same
  selected row and PairIndex without substituting `ProlateCanonicalSourceData`,
  stop with
  `H2A_2_SELECTED_COMPLEX_REFLECTION_RAYLEIGH_OR_PHYSICAL_ODD_MASS_CROSSWALK_GAP`.

DO NOT:
  prove a rate;
  realify or symmetrize the row;
  change the shift;
  add a sector-floor assumption to a structure;
  bundle a ground-state or real-zero result.
```

## META CLOSEOUT

**What became smaller?**

The abstract finite-dimensional passage

```text
sector floors + exact odd mass + exact residual
→ full literal complement floor
```

is no longer an open wall. `[ABSTRACT][LEAN]`

**What was killed?**

- exact parity as a mandatory pre-gate;
- odd-mass decay without residual control;
- sector-only positivity relabeled as a full complement floor;
- replacement of the original trial by its even projection.

**What must not be tried again?**

Do not remove the residual input, fit a global operator norm, or reuse the old
all-index source interface as if it were definitionally equal to the selected
Ferrers shell.

**Current smallest named gap:**

```text
SELECTED_FERRERS_COMPLEX_REFLECTION_RAYLEIGH_RESIDUAL_ODD_MASS_SOURCE_LOCK
```

**Next cheapest decisive test:**

Prove the exact selected odd-mass physical reflection-defect identity. It
immediately decides whether the planned source-rate theorem measures the object
consumed by H2A.1.

**Fate of prior predictions:**

All three H2A.1 predictions were confirmed. The predicted projector/square-root
normal-form failure occurred. No registered prediction was edited after the
run.

```yaml
iteration:
  target: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR
  status: PROGRESS
  failed_strategy: residual_free_odd_mass_transport
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_COMPLEX_REFLECTION_RAYLEIGH_RESIDUAL_ODD_MASS_SOURCE_LOCK
  invariant_learned: the full q-perp floor needs both reflection contamination and coupling control on the exact complex selected row
  forbidden_future_move: replace the selected row by an even projection or old-source surrogate
  next_decisive_test: selected odd mass equals one quarter of the physical reflection-defect norm square
```
