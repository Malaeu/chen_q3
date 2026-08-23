# STATUS: PROVED — H2A.0 SEMANTICALLY ADMITTED; EXACT SELECTED CCM ROW LOCK CLOSED; H2A.1 ODD-MASS FLOOR BRIDGE AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: d1040ad08e4022fb2bc587d63b844c18a83b8f50
  SOURCE_COMMIT: d1040ad08e4022fb2bc587d63b844c18a83b8f50
  ACTUAL_PARENT: 4df7b14a26abee5bcd589d7a5ad04e5e5f2f5523
  CLAIMED_PARENT: 4df7b14a26abee5bcd589d7a5ad04e5e5f2f5523
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFiniteCCMSourceRow.lean
  LEAN_GIT_BLOB: 21c23251f3db4494f9fb8ba06a74ed4c24b8a97a
  LEAN_SHA256_REPORTED: 5938530f617e53106abb6912e117d09cabda3fc12ab5e66bbfb384c5564f45d3
  LEAN_LINES_REPORTED: 296
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 7925f144a428e4fbc7c8bafaef0e1bd3427d669e
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7919_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS:
    selectedFerrersFiniteCCMRow_apply:
      - propext
      - Classical.choice
      - Quot.sound
    selectedFerrersFiniteCCMRow_unit:
      - propext
      - Classical.choice
      - Quot.sound
    sourceOrderedCCMRawTransform_selectedFerrersFiniteCCMRow_eq_rawFplus:
      - propext
      - Classical.choice
      - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SELECTED_SOURCE_ROW_LOCK
  CONDITIONAL_PARAMETER:
    name: P
    type: CCMLemma73PreAnchorPort_selectedFerrersPreAnchorData
    hidden: false
  EXACT_SHELL: selectedFerrersCofinalSourceData P
  EXACT_INDEX: selectedFerrersCofinalSourceData_P_index_k
  EXACT_PAIR: selectedFerrersCofinalSourceData_P_pair_k
  EXACT_ROW: selectedFerrersFiniteCCMRow P k
  EXACT_ROW_FORMULA: c_n_of_shell_index_pair_memLp_trialNonzero_at_ccmModeFinite
  EXACT_FINITE_CARRIER: CCMModeFinite_of_shell_index_N
  EXACT_SOURCE_VECTOR: normalized_projected_kTrial_m_N_of_the_same_shell
  EXACT_TRANSFORM: sourceOrderedCCMRawTransform
  EXACT_REFERENCE_TRANSFORM: SelectedProlateCofinalSourceData.rawFplus
  UNIT_NORMALIZATION_SOURCE: finite_synthesis_plus_norm_kTrial_m_N
  GRAM_SURROGATE_USED: false
  OLD_PROLATE_CANONICAL_SOURCE_DATA_SUBSTITUTED: false
  ARBITRARY_UNIT_ROW_SUBSTITUTED: false
  TAIL_SHIFT_CHANGED: false
  SELECTED_PAIR_OR_SCHEDULE_CHANGED: false
  C04_OBJECT_AUDIT: PASS
  C09_PRECOMMITTED_SCHEDULE_AUDIT: PASS
  C10_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

PLANT_AUDIT:
  PLANT: unit_rows_do_not_identify_source_row_plant
  STATUS: PASS
  MEANING: same_carrier_plus_unit_norm_does_not_identify_the_source_row

H2A_BOUNDARY:
  TRIAL_ROW_OBJECT_LOCK: CLOSED
  ROW_UNIT_NORMALIZATION: CLOSED
  ROW_TO_PROPOSITION59_RAW_TRANSFORM_CROSSWALK: CLOSED
  COMPLEMENT_FLOOR: OPEN
  PENALTY_OR_GRAM_CERTIFICATE: OPEN
  SECTOR_FLOORS: OPEN
  ODD_MASS_RATE: OPEN
  RESIDUAL_RATE: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  GROUND_PARITY: OPEN
  REAL_GROUND_REPRESENTATIVE: OPEN
  ETA_NORMALIZATION_OF_GROUND: OPEN
  COFINAL_SIMPLE_EVEN_GROUND_SUPPLIER: OPEN
  THEOREM_510_APPLICATION: OPEN

CRITICAL_GUARD:
  SELECTED_ROW_IS_COMPLEX: true
  SELECTED_ROW_EXACTLY_REAL_PROVED: false
  SELECTED_ROW_EXACTLY_REFLECTION_EVEN_PROVED: false
  UNIT_NORM_IMPLIES_REAL_OR_EVEN: false
  RAW_TRANSFORM_EQUALITY_IMPLIES_GROUND_STATE: false
  FIXED_CELL_OCCUPIES_COFINAL_QUANTIFIER: false

CLOSES:
  - SELECTED_FERRERS_COFINAL_SOURCE_SHELL_EXPOSED
  - SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_OBJECT_LOCK
  - SELECTED_FERRERS_FINITE_ROW_UNIT_NORMALIZATION
  - SELECTED_FERRERS_FINITE_ROW_TO_RAW_TRANSFORM_CROSSWALK
OPENS: []

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED
  CODE: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_2026-08-23.md
  PRIMARY_THEOREM: complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
  REQUIRED_ROLE: finite_dimensional_reflection_contamination_transport
  REQUIRED_OUTPUT: complexTrialComplementFloor_on_the_full_literal_q_orthogonal_complement
  REQUIRED_EXACT_EFFECTIVE_FLOOR: >-
    betaEff = min(betaPlus,betaMinus) * (1-eta)
      - ((2*sqrt(eta)+eta)/sqrt(1-eta)) * rho
  REQUIRED_HYPOTHESES:
    - finite_complex_Hilbert_carrier
    - K_Hermitian
    - J_Hermitian_unitary_involution
    - K_commutes_with_J
    - q_unit
    - a_real_shift
    - eta_is_exact_squared_norm_of_the_J_odd_part_of_q
    - zero_le_eta_and_eta_lt_one
    - even_sector_floor_on_vectors_orthogonal_to_the_normalized_even_part_of_q
    - odd_sector_floor
    - rho_bounds_norm_of_K_minus_aI_applied_to_q
    - zero_lt_betaEff
  REQUIRED_PRIVATE_PLANT: oddMass_without_residual_control_does_not_force_complementFloor_plant
  PLANT_REQUIREMENT: >-
    Use an exact finite-dimensional reflection-commuting Hermitian example with
    positive even and odd sector floors, nonzero odd mass below 1/25, and a
    negative direction in the literal q-perp complement when the coupling is
    allowed to grow. The plant must reject the theorem with the rho/residual
    hypothesis deleted.
  CLOSES:
    - REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: SELECTED_FERRERS_SECTOR_FLOORS_ODD_MASS_RESIDUAL_RATE_SUPPLY

FORBIDDEN:
  - create_a_thin_selected_wrapper_around_hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
  - call_the_row_real_or_even_from_unit_normalization
  - replace_q_by_its_even_projection
  - assume_exact_source_row_parity
  - drop_the_residual_or_coupling_input
  - replace_the_full_q_perp_floor_by_two_sector_only_floors
  - replace_the_source_residual_by_a_fitted_operator_norm
  - introduce_a_fixed_shift_or_Rayleigh_proximity_input_in_H2A_1
  - claim_a_cofinal_floor
  - claim_simple_even_ground
  - claim_Theorem510_or_real_zeros
  - edit_H2A_0_or_L73_3_through_L73_8
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

SUCCESS: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_LEAN
FAILURE: H2A_1_COMPLEX_REFLECTION_DECOMPOSITION_OR_EFFECTIVE_FLOOR_MISMATCH

NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_SECTOR_FLOORS_ODD_MASS_RESIDUAL_RATE_SUPPLY
NEXT_CHEAPEST_DECISIVE_TEST: >-
  First prove the exact finite contamination theorem and its coupling plant.
  Only after that ask the selected Ferrers source for the three genuine
  analytic inputs: even-sector floor, odd-sector floor, and odd-mass/residual
  rate. Do not spend a source estimate before the finite loss formula is
  kernel-checked.

PREDICTION_FATES:
  P_H2A0_1:
    prior_probability: 0.92
    fate: CONFIRMED
  P_H2A0_2:
    prior_probability: 0.96
    fate: CONFIRMED
  P_H2A0_3:
    prior_probability: 0.84
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: DEPENDENT_SELECTED_TAIL_INDEX_OR_CCM_MODE_CARRIER_NORMAL_FORM
    fate: PARTIALLY_OBSERVED_AS_ELABORATION_FRICTION_ONLY
  RETROACTIVE_REPAIR: false

REGISTERED_PREDICTIONS_NEXT:
  P_H2A1_1:
    claim: the_exact_betaEff_formula_is_provable_by_finite_Hermitian_reflection_geometry_without_new_analysis
    probability: 0.84
  P_H2A1_2:
    claim: the_three_dimensional_coupling_plant_rejects_the_residual_free_statement_exactly
    probability: 0.98
  P_H2A1_3:
    claim: no_new_axiom_or_paper_input_is_needed_for_H2A_1
    probability: 0.995
  LIKELIEST_FAILURE: COMPLEX_REFLECTION_PROJECTOR_OR_SQRT_NORMAL_FORM

ARSENAL_MANDATE: ACCEPTED_STANDING
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED_NOW: true
AUTHORIZED_TARGET: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_LEAN
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
SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_CONDITIONAL_ON_EXPLICIT_L73_PORT
```

## ROUTE MAP

### 1. H2A.0 is an exact source-object theorem, not a spectral theorem

The new file stays on the selected Ferrers shell generated from the conditional
L73.8 port. Its finite row is not imported from the old all-index
`ProlateCanonicalSourceData` interface. It is rebuilt literally from the
selected shell's own index, pair, `eStar_memLp`, `trialNonzero`, and `c_n`.

The unit theorem is source-bearing: finite synthesis reconstructs the exact
normalized projected `kTrial_m_N`, and `norm_kTrial_m_N` supplies norm one. No
Gram-matrix surrogate appears. The raw-transform theorem also preserves the
actual coefficient transport: equality is proved only on the shared finite
summation set, where the two carrier equivalences agree. No false global
coefficient extensionality is used.

Therefore H2A.0 closes the C04/C10 object firewall and is semantically admitted
as `[COFINAL_FAMILY][LEAN]`, conditional only on the explicit L73.8 port value.

### 2. What H2A.0 deliberately does not prove

The row is complex. Neither unit norm nor equality of its Proposition-59
transform with `rawFplus` proves that the row is coordinatewise real,
reflection-even, an eigenvector, or a ground vector.

The repository already contains the generic receiver

```text
hermitian_unit_trialLine_complementFloor_gives_ground_gap_tracking
```

which turns a positive literal complement floor into a bottom eigenpair, an
orthogonal Rayleigh gap, and a residual-over-floor projective estimate. Writing
one more selected-only wrapper around that theorem would not shrink the
mathematics. It is therefore rejected under the supplier contract.

The exact remaining finite spectral input is the full positive floor of the
shifted matrix on the orthogonal complement of this exact complex row.

### 3. Why H2A.1 uses odd mass instead of assuming exact parity

The CCM matrix commutes with reflection, but the full source pipeline

```text
prolateCombination -> E_star -> finite projection -> normalization -> c_n
```

does not currently export exact reflection-evenness of the final complex row.
Replacing the row by its even projection would change the Rayleigh value,
residual, trial line, and transform. That is a C04/C10 object switch.

Exact parity is also stronger than needed. Let `eta` be the squared norm of the
odd part of the unit row, let `rho` bound the shifted residual, and let the
shifted form have floors `betaPlus` and `betaMinus` on the exact even and odd
sectors. Finite reflection geometry gives the full literal floor

\[
\beta_{\mathrm{eff}}
=
\min(\beta_+,\beta_-)(1-\eta)
-
\frac{2\sqrt\eta+\eta}{\sqrt{1-\eta}}\rho.
\]

The residual term is load-bearing. Small odd mass alone does not control the
coupling from the even trial direction into its even complement. H2A.1 must
therefore ship an exact counterexample plant that fails when this input is
removed.

### 4. State after H2A.1

A green H2A.1 will not prove a selected Ferrers complement floor. It will prove
the exact finite implication that consumes the three source-side inputs without
requiring illegal exact parity:

```text
even-sector floor
+ odd-sector floor
+ selected odd mass and residual control
-> full literal complement floor.
```

At that point the remaining H2a source problem becomes sharply named:

```text
SELECTED_FERRERS_SECTOR_FLOORS_ODD_MASS_RESIDUAL_RATE_SUPPLY.
```

The existing generic spectral receiver can then construct and track the bottom
ground state. Real representative, evenness, eta normalization, and the final
cofinal package remain separate obligations and may not be inferred from the
row lock or from a single fixed cell.

## FINAL PROPOSAL

Freeze `G6N1SelectedFerrersFiniteCCMSourceRow.lean`. Do not reopen its carrier,
normalization, or transform convention.

The next source transaction is the finite reflection-contamination theorem.
Its mathematical statement is fixed by the displayed `betaEff`; the executor
may choose the existing matrix-involution API or an equivalent exact complex
reflection decomposition after `ask.sh` preflight, but may not weaken the full
`q^perp` conclusion or add exact parity.

### Verification

```text
WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean
  lake build Q3.Proofs.RouteB.CCMComplexTrialReflectionContaminationFloor

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean
```

Expected axiom profile for the primary theorem and plant:

```text
[propext, Classical.choice, Quot.sound]
```

## STRONGEST ATTACK

> The file only identifies the projected trial row. It does not construct a
> simple-even ground state, so calling it H2a progress is bookkeeping.

The objection is correct against any claim that G1 or H2a is closed. Those
claims are explicitly rejected. It is not correct against the object-lock
status: before this transaction, the L73 limit lived on the selected shell
while the finite spectral machinery lived on a different all-index interface.
No legal H2a theorem could even name the exact row carried by the L73 family.
H2A.0 closes that source-target type mismatch and opens nothing.

The strongest attack against the next route is also accepted:

> Sector floors and odd-mass decay alone do not imply a full complement floor.

That statement is false. H2A.1 retains the exact residual/coupling term and
requires a plant exhibiting the failure without it. Failure of the sufficient
`betaEff > 0` condition will not be mislabeled as failure of the spectral
property itself.

## META CLOSEOUT

**What became smaller?** The selected L73 family now exposes one exact finite
CCM coefficient row with its unit norm and literal Proposition-59 transform.
The old-interface substitution is gone.

**What was killed?** Arbitrary unit-row substitution, false coefficient
extensionality outside the summation set, a separate shell-only transaction,
and the interpretation that unit norm or transform equality supplies a ground
state.

**What must not be tried again?** Do not realify, symmetrize, or call the row
even without a theorem. Do not write a thin wrapper around an already-green
complement-floor receiver. Do not promote a fixed cell into the cofinal
quantifier.

**Current smallest named gap:**

```text
REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR.
```

**Next cheapest decisive test:** kernel-check the exact `betaEff` transport and
the residual-free counterexample plant before spending effort on any cofinal
source estimate.

**Fate of prior predictions:** all three H2A.0 predictions are confirmed. The
predicted dependent-index failure appeared only as elaboration friction. No
retroactive repair.

```yaml
iteration:
  target: H2A_0_SELECTED_FERRERS_FINITE_CCM_SOURCE_ROW_LOCK
  status: PROGRESS
  failed_strategy: reuse_old_all_index_row_or_write_shell_only_wrapper
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR
  invariant_learned: H2a must consume the exact complex row generated by the same selected shell that carries the L73 limit
  forbidden_future_move: infer realness, parity, or ground status from unit norm or raw-transform equality
  next_decisive_test: exact finite betaEff theorem with coupling plant
```
