# STATUS: PROVED — H2A.2 SEMANTICALLY ADMITTED; EXACT SELECTED H2A SOURCE-QUANTITIES LOCK CLOSED; H2A.3 ODD-MASS DECAY AUTHORIZED
```yaml
PRIMARY: ADMIT_H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V
FOLLOWUP_FLOOR: H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_LOCK_LEAN

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REVIEW_HEAD: 35da26cdb8d2eacb9b1ac3bed91751a45efafff3
  SOURCE_COMMIT: 35da26cdb8d2eacb9b1ac3bed91751a45efafff3
  ACTUAL_PARENT: 7a090cd04727eeedcd53251f6457073420f21291
  CLAIMED_PARENT: 7a090cd04727eeedcd53251f6457073420f21291
  CLAIMED_PARENT_IS_ACTUAL_PARENT: true
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersH2aSourceQuantities.lean
  LEAN_GIT_BLOB: 2ef1c66a6489f54f8722459f0755f3105f852123
  LEAN_SHA256_REPORTED: 2b0a049ca073cbf36812f01c39c0dc2466690eebe6fd824f6bd7a8b7ae61727b
  LEAN_LINES_REPORTED: 616
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_2_SELECTED_FERRERS_H2A_SOURCE_QUANTITIES_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: f3e6605f698a5346a38f9db8d44d6cbc6a31a43d
  LEAN_DRIFT_AFTER_SOURCE: false

KERNEL_GATE:
  LINUX_REPORTED_LAKE_ENV_LEAN: PASS
  LINUX_REPORTED_TARGET_BUILD: PASS_7921_JOBS
  LINUX_REPORTED_Q3_CHECK: PASS_EXIT_0
  LINUX_REPORTED_AXIOMS_FOR_ALL_8_PUBLIC_THEOREMS_AND_2_PLANTS:
    - propext
    - Classical.choice
    - Quot.sound
  LINUX_REPORTED_SORRY_AX: false
  JUDGE_RERAN_LAKE_BUILD: false

SEMANTIC_ADMISSION:
  STATUS: SEMANTICALLY_ADMITTED_AS_EXACT_SELECTED_SOURCE_OBJECT_LOCK
  SELECTED_SHELL: selectedFerrersCofinalSourceData
  FINITE_ROW: selectedFerrersFiniteCCMRow
  MATRIX: sourceCCMFiniteMatrix_at_the_same_selected_index
  REFLECTION: ccmComplexReflectionMatrix_on_the_same_CCMModeFinite_carrier
  RAYLEIGH_SHIFT: selectedFerrersFiniteCCMRayleigh
  RESIDUAL: selectedFerrersFiniteCCMResidual
  ODD_PART: selectedFerrersFiniteCCMOddPart
  ODD_MASS: selectedFerrersFiniteCCMOddMass
  PHYSICAL_DEFECT: selectedFerrersFiniteCCMReflectionDefect
  OLD_PROLATE_CANONICAL_SOURCE_INTERFACE_SUBSTITUTED: false
  SELECTED_COMPLEX_ROW_REALIFIED: false
  ROW_REPLACED_BY_EVEN_PROJECTION: false
  FIXED_OR_FITTED_SHIFT_USED: false
  H2A1_RECEIVER_INSTANTIATED_LITERALLY: true
  C04_OBJECT_AUDIT: PASS
  C09_PRECOMMIT_AUDIT: PASS
  C10_FUNCTIONAL_NOT_SURROGATE_AUDIT: PASS

EXACT_IDENTITY_AUDIT:
  REFLECTION_ACTION: "(R_N *ᵥ x)_j = x_(ccmNegFinite N j)"
  REFLECTION_HERMITIAN: true
  REFLECTION_SQUARE: "R_N * R_N = 1"
  MATRIX_REFLECTION_COMMUTATION: "K_i * R_N = R_N * K_i"
  MATRIX_REFLECTION_COMMUTATION_DOMAIN: every_PairIndex
  UPSTREAM_VACUOUS_hN_REMOVED_BY_LOCAL_PROOF: true
  SYNTHESIS: selected_row_reconstructs_exact_selected_kTrial_m_N
  ODD_MASS: "eta_k = (1/4) * norm(reflectionDefect_k)^2"
  ODD_MASS_SAME_ROW_AND_PAIR_INDEX: true
  RESIDUAL_ORTHOGONALITY: "star(q_k) dot residual_k = 0"
  RESIDUAL_SHIFT_IS_EXACT_RAYLEIGH: true
  EFFECTIVE_FLOOR_RECEIVER: exact_H2A1_formula_on_full_literal_q_perp

PLANT_AUDIT:
  UNIT_NORM_DOES_NOT_DETERMINE_REFLECTION_MASS:
    STATUS: PASS
    CARRIER: Fin_3
    REFLECTION: swap_0_and_2
    UNIT_ROW_1: [2/3,1/3,2/3]
    ODD_MASS_1: 0
    UNIT_ROW_2: [1,0,0]
    ODD_MASS_2: 1/2
  WRONG_SHIFT_BREAKS_RESIDUAL_ORTHOGONALITY:
    STATUS: PASS
    MATRIX: diag_0_1
    UNIT_ROW: e0
    EXACT_RAYLEIGH_RESIDUAL_INNER_PRODUCT: 0
    SHIFT_ONE_RESIDUAL_INNER_PRODUCT: -1

H2A_BOUNDARY:
  SELECTED_COMPLEX_REFLECTION_OBJECT: CLOSED
  SELECTED_RAYLEIGH_AND_RESIDUAL_OBJECTS: CLOSED
  SELECTED_ODD_MASS_OBJECT: CLOSED
  SELECTED_ODD_MASS_PHYSICAL_REPRESENTATION: CLOSED
  SELECTED_H2A1_LITERAL_RECEIVER: CLOSED
  SELECTED_ODD_MASS_DECAY: OPEN_NEXT
  SELECTED_RESIDUAL_RATE: OPEN
  SELECTED_EVEN_SECTOR_FLOOR: OPEN
  SELECTED_ODD_SECTOR_FLOOR: OPEN
  POSITIVE_COFINAL_EFFECTIVE_FLOOR: OPEN
  SIMPLE_BOTTOM_GROUND: OPEN
  THEOREM_510_APPLICATION: OPEN
  REAL_ZEROS: OPEN

NEXT_AUTHORIZATION:
  STATUS: AUTHORIZED
  CODE: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN
  BASE_HEAD_POLICY: USE_THIS_PROSHKA_VERDICT_COMMIT_AND_RECHECK_WITH_GIT_REV_PARSE_HEAD
  CREATE_EXACTLY_ONE_LEAN_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
  CREATE_SOURCE_RECORD_SAME_COMMIT: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_2026-08-23.md
  DIRECT_IMPORTS:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities
    - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
    - Q3.Proofs.RouteB.D0PstarInversionCoefficientCrosswalk
  PRIMARY_ROLE: >-
    Derive a theorem-facing cofinal decay rate for the exact selected-shell
    odd mass from the already-ratified mode/chi inputs. The proof must use the
    same selected row and PairIndex as H2A.2, the factor-four full E-star error,
    the exact inversion-even CCM limit packet, and the nonzero central anchor.
    No free odd-mass-rate hypothesis is permitted.
  PUBLIC_SURFACE_REQUIRED:
    - selectedFerrersCofinalPreAnchorRank
    - selectedFerrersCofinalSourceData_index_eq_preAnchorIndex
    - selectedFerrersCofinalSourceData_pair_eq_preAnchorPair
    - selectedFerrersCofinalSourceData_sourceScale_eq_preAnchorScale
    - selectedFerrersCofinalPreAnchorRank_tendsto
    - selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
    - selectedFerrersFiniteCCMOddMass_tendsto_zero_of_modeAndChiRates
  PUBLIC_SURFACE_POLICY: >-
    The final-shell/pre-anchor rank crosswalk is public because the residual
    and sector-floor floors will consume the same theorem-generated tail.
    Do not leave the private tail-shift seam to be reconstructed again.
  REQUIRED_PRIVATE_PLANT:
    - vanishing_unnormalized_error_without_anchor_does_not_control_normalized_oddMass_plant
  CLOSES:
    - SELECTED_FERRERS_FINAL_SHELL_TO_PREANCHOR_RANK_CROSSWALK
    - SELECTED_FERRERS_ODD_MASS_LOG_OVER_SQRT_RATE
    - SELECTED_FERRERS_ODD_MASS_DECAY
  OPENS: []
  NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: H2A_4_SELECTED_FERRERS_RESIDUAL_RATE

H2A_3_EXACT_RATE_TARGET:
  LAMBDA: "lambda_m(i_k) = sqrt(m_k)"
  LOG_LENGTH: "L_m(i_k) = log(m_k)"
  POINTWISE_FULL_ESTAR_ERROR: "C / (lambda_k * sqrt(u))"
  WINDOW_L2_ERROR_SQUARED: "O(1 / lambda_k)"
  CENTRAL_PROJECTED_NORM_SQUARED_LOWER: "Omega(1 / L_m(i_k))"
  ODD_MASS_UPPER: "O(L_m(i_k) / lambda_m(i_k))"
  SCHEDULE_FORM: "O(log(m_k) / sqrt(m_k))"
  LIMIT: 0

H2A_3_REQUIRED_THEOREM_SHAPES:
  QUANTITATIVE: |-
    theorem selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
        (C0 C4 Cchi : Real)
        (hC0 : 0 <= C0) (hC4 : 0 <= C4) (hCchi : 0 <= Cchi)
        (hmode : EXACT_L73_MODE_RATE_PREMISE)
        (hchi : EXACT_L73_CHI_RATE_PREMISE) :
      let P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
        C0 C4 Cchi hC0 hC4 hCchi hmode hchi
      exists C : Real, 0 <= C and
        forall_eventually k atTop,
          selectedFerrersFiniteCCMOddMass P k <=
            C * Real.log (((selectedFerrersCofinalSourceData P).index k).m : Real) /
              Real.sqrt (((selectedFerrersCofinalSourceData P).index k).m : Real)
  LIMIT: |-
    theorem selectedFerrersFiniteCCMOddMass_tendsto_zero_of_modeAndChiRates
        (C0 C4 Cchi : Real)
        (hC0 : 0 <= C0) (hC4 : 0 <= C4) (hCchi : 0 <= Cchi)
        (hmode : EXACT_L73_MODE_RATE_PREMISE)
        (hchi : EXACT_L73_CHI_RATE_PREMISE) :
      let P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
        C0 C4 Cchi hC0 hC4 hCchi hmode hchi
      Tendsto (fun k => selectedFerrersFiniteCCMOddMass P k)
        Filter.atTop (nhds 0)
  EXACT_PREMISE_POLICY: >-
    Copy the hmode and hchi types verbatim from
    selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates. Do not replace
    them by a new bundled rate object or an odd-mass hypothesis.

H2A_3_PROOF_ROUTE:
  - Run ask.sh preflight before editing.
  - Construct the exact conditional port P from the same hmode/hchi inputs.
  - Expose the final-shell rank by m_k - 2 and prove exact index, pair and
    source-scale crosswalks to the precommitted pre-anchor schedule. Prove that
    this recovered rank tends to atTop. This is the first decisive gate.
  - Combine the public L73.3 main-error theorem, the public L73.4 exact split,
    and the public target-tail theorem to obtain the full pointwise E-star
    error C/(lambda*sqrt u) on the recovered rank.
  - Integrate its square against dStar on I_m. Use the exact log-window
    transport. The integral must give O(1/lambda), not O(log(lambda)/lambda)
    and not a fitted estimate.
  - Use E_star_explicitCCMLimitH_inv to make the factor-four target exactly
    inversion even. Use inner_V_neg_eq_inner_V_of_inversion_even to obtain
    exact reflected retained coefficients. Do not symmetrize the selected row.
  - Lower-bound the scaled projected source norm from the zero mode:
    preAnchorGwin_zero_eq_sqrtL_mul_innerV0 plus the selected-shell muntzLimit
    at z=0 and centeredXi_zero_ne_zero give an eventual Omega(1/sqrt(L_m))
    norm floor. Pointwise sourceScale_ne alone is not sufficient.
  - Apply Bessel/orthonormal finite synthesis to the exact selected row. The
    source scale cancels between the physical approximation error and the
    projected norm. Obtain eta <= C*L_m/lambda_m.
  - Use the final-shell m-cofinality and log(m)/sqrt(m) -> 0 to prove the
    public Tendsto theorem.
  - Print axioms for every public theorem and the plant.

H2A_3_PLANT:
  vanishing_unnormalized_error_without_anchor_does_not_control_normalized_oddMass_plant: >-
    On Fin 2 with reflection diag(1,-1), use raw vectors p_n=(0,1/(n+1)).
    Their unnormalized norm tends to zero and their error to the zero even
    target tends to zero, but after normalization every row is the odd unit
    vector and has odd mass one. This rejects any proof that divides by a
    merely pointwise nonzero projected norm. The central-anchor lower bound is
    load-bearing.

FORBIDDEN:
  - substitute_ProlateCanonicalSourceData_for_the_selected_shell
  - assume_the_final_shell_rank_or_private_tail_shift_without_a_public_crosswalk
  - assume_odd_mass_decay
  - infer_normalized_decay_from_unnormalized_error_without_anchor_control
  - use_sourceScale_ne_as_a_uniform_lower_bound
  - symmetrize_or_even_project_the_selected_row
  - replace_the_factor_four_target
  - use_an_unscaled_or_neighboring_target_packet
  - fit_a_normalization_constant
  - add_residual_or_sector_floor_claims
  - bundle_H2A_4_or_a_simple_ground_receiver
  - edit_H2A_0_H2A_1_H2A_2_or_L73_3_through_L73_8
  - paper_axiom
  - sorry
  - admit
  - typed_hole
  - theorem_weakening

VALIDATION:
  WORKDIR_Q3:
    - lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
    - lake build Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
  WORKDIR_REPO_ROOT:
    - scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
  EXPECTED_AXIOM_PROFILE_FOR_EVERY_PUBLIC_THEOREM_AND_PLANT:
    - propext
    - Classical.choice
    - Quot.sound

SUCCESS: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN
FAILURE: H2A_3_PRIVATE_TAIL_REINDEX_OR_NORMALIZED_DENOMINATOR_GAP

CLOSES:
  - SELECTED_FERRERS_COMPLEX_REFLECTION_OBJECT_LOCK
  - SELECTED_FERRERS_RAYLEIGH_RESIDUAL_OBJECT_LOCK
  - SELECTED_FERRERS_ODD_MASS_OBJECT_LOCK
  - SELECTED_FERRERS_ODD_MASS_PHYSICAL_REFLECTION_DEFECT_REPRESENTATION
  - SELECTED_FERRERS_H2A1_LITERAL_SOURCE_RECEIVER
OPENS: []

NEXT_LOAD_BEARING_GAP: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY
NEXT_CHEAPEST_DECISIVE_TEST: >-
  Before any cofinal floor work, prove the final-shell/pre-anchor rank
  crosswalk and then the normalized odd-mass rate. If the source scale cannot
  cancel against the projected norm on the same selected object, stop: the
  proposed physical rate is attached to the wrong family.

REGISTERED_PREDICTIONS:
  P_H2A3_1:
    claim: the_full_Estar_C_over_lambda_sqrt_u_rate_integrates_to_window_L2_error_squared_O_one_over_lambda
    probability: 0.88
  P_H2A3_2:
    claim: central_port_convergence_supplies_projected_norm_squared_Omega_one_over_log_m_and_hence_eta_O_log_m_over_sqrt_m
    probability: 0.82
  P_H2A3_3:
    claim: exact_inversion_of_the_factor_four_target_gives_reflected_coefficients_without_source_symmetrization
    probability: 0.94
  LIKELIEST_FAILURE: PRIVATE_TAIL_RANK_OR_MEMLP_LOG_WINDOW_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A2_1:
    probability: 0.95
    fate: CONFIRMED
  P_H2A2_2:
    probability: 0.92
    fate: CONFIRMED
  P_H2A2_3:
    probability: 0.97
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    predicted: DEPENDENT_SELECTED_INDEX_OR_COMPLEX_REFLECTION_MATRIX_NORMAL_FORM
    observed: PARTIALLY_OBSERVED
    details: private_selected_index_visibility_and_one_exact_mod_cast_direction_only
  RETROACTIVE_REPAIR: false

ARSENAL:
  MANDATE_ACCEPTED: true
  CARDS_USED_IN_AUDIT:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
    - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: LEAN_FOR_H2A2_CONDITIONAL_FOR_H2A3
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### H2A.2 is an exact object lock, not a renamed old interface

The selected complex reflection acts on the literal carrier of the exact
selected row, is Hermitian and involutive, and commutes with the same selected
source matrix. The selected Rayleigh and residual are then built from that
same row and matrix. No `ProlateCanonicalSourceData` value is inserted as a
surrogate. `[FINITE_CELL][LEAN]`

The strongest C04 attack therefore fails: the old generic source interface and
the theorem-generated selected Ferrers shell have similar coordinates, but the
proof does not identify them through those coordinates. It reconstructs the
required objects directly on the selected shell. `[FINITE_CELL][LEAN]` **[C04]**

### The physical odd-mass identity is exact

The public synthesis theorem reconstructs the normalized projected selected
`kTrial_m_N`. Orthonormality of the exact finite modes then gives

\[
\eta_k
=
\frac14\left\|k_{m,N}-\operatorname{Synthesis}(Jq_k)\right\|^2.
\]

The same PairIndex occurs on both sides. This is the decisive C10 firewall:
the downstream contamination theorem consumes the literal odd mass of the
literal source row, not a nearby physical diagnostic. `[FINITE_CELL][LEAN]`
**[C10]**

### The Rayleigh shift is source-defined

The residual is

\[
r_k=K_kq_k-a_kq_k,
\qquad
a_k=\operatorname{Re}\langle q_k,K_kq_k\rangle.
\]

Hermitian reality and unit normalization prove

\[
\langle q_k,r_k\rangle=0.
\]

The wrong-shift plant proves that this property would fail for an arbitrary
fixed or fitted shift. `[FINITE_CELL][LEAN]`

### The receiver is correctly conditional

H2A.2 instantiates H2A.1 on the exact selected objects. It does not manufacture
any of the remaining quantitative hypotheses. The output is a full literal
`q_k`-complement floor only after supplying sector floors, `eta<1`, the residual
bound and positivity of the exact effective-floor expression. `[FINITE_CELL][LEAN]`

Thus H2A.2 closes five object/provenance gaps and opens none. It does not close
H2a itself. `[ABSTRACT][PAPER]`

## FINAL PROPOSAL

Proceed with H2A.3, but do not formalize an abstract statement of the form
`oddMassRate -> oddMass tends to zero`. The next node must derive the rate from
the already-ratified selected Ferrers mode/chi inputs.

The representation is deliberately scale-invariant. L73 supplies

\[
\left\|s_kE_\star(h_k)(u)-4E_\star(h)(u)\right\|
\le
\frac{C}{\lambda_k\sqrt u}.
\]

Squaring and integrating against `du/u` over
`[lambda_k^{-1},lambda_k]` costs only `O(lambda_k^{-1})`. The factor-four
target is exactly inversion even. The central port convergence supplies the
missing normalized denominator:

\[
\|s_kP_NE_\star(h_k)\|^2
\gtrsim
\frac1{L_k}.
\]

Therefore the exact normalized selected odd mass obeys

\[
\boxed{
\eta_k
\le
C\frac{L_k}{\lambda_k}
=
C\frac{\log m_k}{\sqrt{m_k}}
\longrightarrow0.
}
\]

This is the first substantive cofinal quantitative input for the H2A.1
receiver. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The dangerous false argument is:

```text
scaled source packet approaches an even target;
therefore the normalized selected row becomes even.
```

It is false if the scaled projected norm collapses. The required plant makes
this explicit: arbitrarily small unnormalized odd vectors normalize to the
same pure odd unit vector. Pointwise `sourceScale_ne` does not repair this.

The repaired statement uses the exact zero-mode identity and locally uniform
port convergence at zero to obtain an eventual quantitative lower bound on
the same scaled projected source. Only then may the physical approximation
error be divided by the projected norm. `[ABSTRACT][LEAN]`

## CODEX DIRECTIVE

```text
TASK:
  H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN

BASE_HEAD:
  use the commit containing this verdict;
  run `git rev-parse HEAD` immediately before editing.

FILES:
  q3.lean.aristotle/Q3/Proofs/RouteB/
    G6N1SelectedFerrersOddMassDecay.lean

  docs/routeB_bus/
    LINUX_SOURCE_RECORD_REQ_V_H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_2026-08-23.md

DO:
  1. Run `./ask.sh` for the exact target and supplier names.
  2. Expose the final-shell/pre-anchor rank crosswalk publicly.
  3. Derive the full E-star pointwise rate from L73.3 plus L73.4.
  4. Integrate the squared rate in the exact dStar unit.
  5. Use the exact inversion-even factor-four target.
  6. Obtain the projected-norm floor from the central anchor.
  7. Prove the quantitative `log(m)/sqrt(m)` odd-mass bound.
  8. Prove odd mass tends to zero.
  9. Run the three required gates and print all axiom profiles.

DO NOT:
  assume odd-mass decay;
  substitute the old canonical-source interface;
  symmetrize the selected row;
  use a merely pointwise nonzero denominator;
  bundle residual or sector-floor results.

SUCCESS:
  H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN

FAILURE:
  H2A_3_PRIVATE_TAIL_REINDEX_OR_NORMALIZED_DENOMINATOR_GAP
```

## META CLOSEOUT

**What became smaller?**

The H2a source side no longer has an object-identity ambiguity. Reflection,
Rayleigh, residual, odd mass, physical defect and the H2A.1 receiver now refer
to one selected row on one selected carrier. `[FINITE_CELL][LEAN]`

**What was killed?**

- substituting `ProlateCanonicalSourceData` for the selected shell;
- inferring parity from unit normalization;
- replacing the exact Rayleigh by a convenient shift;
- treating a physical reflection defect on another object as selected odd mass.

**What must not be tried again?**

Do not write a theorem whose input is `selected odd mass tends to zero` and call
that H2A.3. The available L73 rate and central anchor must be consumed to derive
it.

**Current smallest named gap:**

```text
H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY
```

**Next cheapest decisive test:**

Prove the final-shell/pre-anchor rank crosswalk, then verify the exact integral

\[
\int_{1/\lambda}^{\lambda}
\frac{C^2}{\lambda^2u}\,\frac{du}{u}
\le
\frac{C^2}{\lambda}.
\]

If either object alignment or unit accounting fails, stop before building the
normalization layer.

```yaml
iteration:
  target: H2A.2 selected Ferrers H2a source quantities
  status: PROGRESS
  failed_strategy: old-interface substitution
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY
  invariant_learned: selected row, carrier, reflection, Rayleigh and physical defect must remain one literal object
  forbidden_future_move: infer normalized parity decay from unnormalized approximation without an anchor floor
  next_decisive_test: final-shell rank crosswalk plus exact dStar integral
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
