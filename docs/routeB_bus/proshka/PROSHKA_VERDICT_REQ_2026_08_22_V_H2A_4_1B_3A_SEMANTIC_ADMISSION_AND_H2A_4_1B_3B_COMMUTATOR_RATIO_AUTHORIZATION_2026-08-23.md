# STATUS: PROVED — H2A.4.1B.3A SEMANTICALLY ADMITTED; DIRECT WEIGHTED-RATE CLAIM REPAIRED TO AN EXACT COMMUTATOR-RATIO LOCK
```yaml
PRIMARY: ADMIT_BETA_MOMENT_ODD_MASS_LOCK_AND_AUTHORIZE_COMMUTATOR_RESIDUAL_RATIO
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_COMMIT: 89a74b338721482dc1c4a4d39db59f182d3c678f
  SOURCE_PARENT: af4ca2194537f6104c696e6ac4642d928e5909ff
  SOURCE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean
  SOURCE_GIT_BLOB: bb9156e9990210c4c8eb51d6c685b7e8dcd8d0ff
  SOURCE_SHA256: e6faf993d43c1d934200b91a0a5bfe428b5fb8a5cc4f778bb8f382928944abcf
  SOURCE_LINES: 394
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 9e45e3e62eed255caff2107ae39e9574b026cdc1
  HEAD_AT_AUDIT: 89a74b338721482dc1c4a4d39db59f182d3c678f
  PARENT_EXACT: true

H2A_4_1B_3A:
  SEMANTIC_ADMISSION: PROVED
  SCOPE: COFINAL_FAMILY
  VERIFIER: LEAN
  CENTER_ACTION_SOURCE_CROSSWALK: CLOSED
  BETA_ODD_PART_IDENTITY: CLOSED
  BETA_MOMENT_ODD_MASS_BOUND: CLOSED
  BETA_ENERGY_GROWTH: OPEN
  WEIGHTED_RESIDUAL_SOURCE_RATE: OPEN

PLANTS:
  ALL_ONES_MOMENT_DOES_NOT_DETERMINE_BETA_MOMENT: RATIFIED
  SOURCE_BETA_ODDNESS_IS_LOAD_BEARING: RATIFIED

GATE_RELIANCE:
  JUDGE_RERAN_LEAN: false
  LINUX_LAKE_ENV_LEAN: PASS
  LINUX_TARGET_BUILD: PASS_7925_JOBS
  LINUX_Q3_CHECK: PASS
  OBSERVED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound
  SORRY_AX: false

OUTCOME_REPAIR:
  REQUESTED_NEXT_CODE: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_DEFECT_WEIGHTED_RATE
  REQUESTED_NEXT_CODE_STATUS: REJECTED_AS_PREMATURE_RATE_CLAIM
  REPAIRED_NEXT_CODE: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN
  REASON: >-
    H2A.4.1B.3A identifies and bounds one scalar moment, but neither controls
    the full combined commutator defect nor proves any selected-schedule
    beta-energy growth.  The next Lean floor must first identify the exact
    mode-weighted residual and reduce the full residual energy to one
    source-faithful commutator ratio.  The source-derived decay of that ratio
    remains the subsequent analytic floor.

NEXT_AUTHORIZATION:
  CODE: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN
  STATUS: AUTHORIZED
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_DEFECT_2026-08-23.md
  DIRECT_IMPORTS_EXACT:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersBetaMomentOddMass
    - Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance
  LEAN_WRITE_AUTHORIZED: true
  ARISTOTLE_AUTHORIZED: false

  CLOSES:
    - SELECTED_FERRERS_COMPLEX_COMMUTATOR_RESIDUAL_IDENTITY
    - SELECTED_FERRERS_MODE_WEIGHTED_RESIDUAL_ENERGY_LOCK
    - SELECTED_FERRERS_CENTER_COEFFICIENT_NONVANISHING
    - SELECTED_FERRERS_CENTER_WEIGHTED_RESIDUAL_BOUND
    - SELECTED_FERRERS_BETA_CORRECTION_ODD_MASS_BUDGET
    - SELECTED_FERRERS_COMMUTATOR_RATIO_TO_WEIGHTED_RESIDUAL_RECEIVER
  OPENS:
    - SELECTED_FERRERS_WEIGHTED_COMMUTATOR_RATIO_SOURCE_RATE

SUCCESS: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN
FAILURE: H2A_4_1B_3B_COMPLEX_COMMUTATOR_CAST_OR_CENTER_RESIDUAL_ENERGY_GAP

NEXT_LOAD_BEARING_GAP_AFTER_ADMISSION:
  H2A_4_1B_3C_SELECTED_FERRERS_WEIGHTED_COMMUTATOR_RATIO_SOURCE_RATE

REGISTERED_PREDICTIONS:
  P_H2A41B3B_1:
    claim: exact_source_commutator_gives_Gamma_k_equal_D_k_times_literal_residual
    probability: 0.96
  P_H2A41B3B_2:
    claim: selected_raw_zero_nonvanishing_gives_pointwise_nonzero_center_coefficient
    probability: 0.94
  P_H2A41B3B_3:
    claim: unit_norm_plus_residual_orthogonality_gives_abs_q0_sq_times_residualEnergy_le_GammaEnergy
    probability: 0.88
  P_H2A41B3B_4:
    claim: beta_correction_energy_is_bounded_by_carrier_cardinality_times_betaEnergy_times_oddMass
    probability: 0.97
  LIKELIEST_FAILURE: COMPLEX_MATRIX_CAST_OR_CENTER_EXCLUSION_FINSET_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A41B3A_1:
    fate: CONFIRMED
  P_H2A41B3A_2:
    fate: CONFIRMED
  P_H2A41B3A_3:
    fate: CONFIRMED
  LIKELIEST_FAILURE:
    fate: PARTIALLY_OBSERVED_DOTPRODUCT_SUM_NORMAL_FORMS_ONLY
  RETROACTIVE_REPAIR: false

ARSENAL_MANDATE:
  STATUS: PREVIOUSLY_ACCEPTED
  ACCEPTANCE_FILE: docs/routeB_bus/proshka/PROSHKA_VERDICT_ARSENAL_ACCEPTANCE_2026-08-17.md
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. H2A.4.1B.3A proves the intended finite source statements

For the exact selected index and row write

\[
 i_k=(\operatorname{selectedFerrersCofinalSourceData}P).\operatorname{index}(k),
 \qquad
 q_k=\operatorname{selectedFerrersFiniteCCMRow}(P,k).
\]

The new source defines

\[
 \beta_{k,j}=n_{k,j}\,M_{k,j0},
 \qquad
 B_k=\sum_j\beta_{k,j}q_{k,j},
\]

where \(M_k\) is the literal selected source CCM matrix and \(0\) is its
central mode.  It then proves

\[
 \boxed{B_k=(M_kD_kq_k)_0}.
\]

The proof uses the exact source definition of \(\beta\), the exact symmetry of
`ccmWeilMatFinite`, the same selected carrier, and one finite sum.  It does not
replace the mode-weighted action by a zero-mode, Mellin, or all-ones value.
`[COFINAL_FAMILY][LEAN]`

Because the source beta vector is reflection-odd, its pairing with the exact
reflection-even part of the selected row vanishes.  Hence

\[
 \boxed{B_k=\beta_k\mathbin{\cdot}q_k^-}.
\]

Finite Cauchy--Schwarz then gives the exact bound

\[
 \boxed{
 |B_k|^2
 \le
 E_{\beta,k}\,\eta_k,
 }
\]

where

\[
 E_{\beta,k}=\sum_j\beta_{k,j}^2,
 \qquad
 \eta_k=\operatorname{selectedFerrersFiniteCCMOddMass}(P,k).
\]

The complex carrier causes no object change: beta is real and explicitly cast
to complex coordinates.  The dot-product orientation is therefore compatible
with the source commutator. `[COFINAL_FAMILY][LEAN]`

### 2. Both plants are semantic firewalls

The first plant gives two rows with the same all-ones moment but distinct beta
moments.  It kills the substitution

```text
ccmEtaFinite dot q
or an unweighted transform value
for beta dot q.
```

The second plant gives an exactly even row and an arbitrary even beta vector
with nonzero beta moment.  Thus the odd-mass estimate is valid because the
literal source beta is reflection-odd, not because every vector called beta has
that property. `[ABSTRACT][LEAN]`

### 3. Hard boundary: B3A is a source lock, not a rate theorem

The theorem intentionally leaves \(E_{\beta,k}\) uncontrolled.  This is
load-bearing.  In particular, the explicit `W02` central-column component has

\[
 n\,W02(L;n,0)
 =
 \frac{32L\sinh^2(L/4)\,n}{L^2+16\pi^2n^2}.
\]

On the selected schedule \(m=N\), \(L=\log m\), its separate component has
size of order \(\sqrt m\) for modes \(n\asymp L\), across order-\(L\) many
modes.  Therefore a componentwise absolute-value estimate can naturally carry
an order-\(mL\) beta-energy budget.  The full source beta may have cancellations
between `W02`, archimedean and prime pieces, but those cancellations are exactly
what a componentwise triangle estimate discards.

Consequently the implication

```text
oddMass -> 0
therefore betaMoment -> 0
```

is not available from B3A alone.  This is a direct **C10** warning: the
consumer needs the full source functional, not the absolute-value majorant of
its components. `[COFINAL_FAMILY][PAPER]`

### 4. The exact next representation

Set

\[
 S_k=M_k-a_kI,
 \qquad
 r_k=S_kq_k,
 \qquad
 A_k=\mathbf 1\mathbin{\cdot}q_k,
 \qquad
 B_k=\beta_k\mathbin{\cdot}q_k.
\]

The source commutator is

\[
 D_kS_k-S_kD_k
 =
 \beta_k\otimes\mathbf1-\mathbf1\otimes\beta_k.
\]

Therefore the combined defect

\[
 \boxed{
 \Gamma_k
 :=
 S_k(D_kq_k)+A_k\beta_k-B_k\mathbf1
 }
\]

must satisfy the exact identity

\[
 \boxed{\Gamma_k=D_kr_k.}
\]

This preserves the cancellation inside the full commutator defect.  The next
transaction must not replace \(\|\Gamma_k\|\) by the sum of norms of its three
terms as though that were the exact consumer.

Define

\[
 G_k:=\|\Gamma_k\|^2
     =\sum_j n_{k,j}^2|r_{k,j}|^2.
\]

Let \(q_{0,k}\) be the exact center coefficient.  Unit normalization and
\(q_k^*r_k=0\) imply

\[
 \boxed{
 |q_{0,k}|^2\,\|r_k\|^2\le G_k.
 }
\]

Indeed, off the center one has \(|n_{k,j}|\ge1\), while orthogonality controls
the center residual by the noncentral residual.  This step is finite Hermitian
geometry; it requires no operator norm and no rate hypothesis.

The selected source record already contains exact nonvanishing of the finite
raw central value.  Together with

\[
 \operatorname{rawFplus}_k(0)=\sqrt{L_k}\,q_{0,k},
 \qquad L_k>0,
\]

it gives

\[
 \boxed{q_{0,k}\ne0}
\]

pointwise on the selected tail.

Hence the single source ratio

\[
 \boxed{
 \mathcal R_k
 :=
 \frac{\eta_kG_k}{|q_{0,k}|^2}
 }
\]

majorizes the exact squared weighted residual:

\[
 \eta_k\,\|r_k\|^2\le\mathcal R_k.
\]

Therefore

\[
 \mathcal R_k\to0
 \quad\Longrightarrow\quad
 \sqrt{\eta_k}\,\|r_k\|\to0.
\]

This is the correct next compression.  The source-derived proof that
\(\mathcal R_k\to0\) is **not** part of B3B.

### 5. Beta correction ledger

The all-ones correction in \(\Gamma_k\) has exact energy

\[
 \|B_k\mathbf1\|^2=(2N_k+1)|B_k|^2.
\]

B3A therefore yields

\[
 \boxed{
 \|B_k\mathbf1\|^2
 \le
 (2N_k+1)E_{\beta,k}\eta_k.
 }
\]

This theorem is useful for any source estimate of \(\Gamma_k\), but it remains
an auxiliary one-sided budget.  It must not force a termwise decomposition of
the combined defect when source cancellation is available.

## FINAL PROPOSAL

Authorize one exact algebraic transaction.  It closes the selected complex
commutator identity, the mode-weighted residual energy, the central-mode
reconstruction inequality, and the receiver

\[
 \mathcal R_k\to0
 \Longrightarrow
 \sqrt{\eta_k}\sqrt{E_{\mathrm{res},k}}\to0.
\]

The subsequent analytic task is exactly

```text
H2A_4_1B_3C_SELECTED_FERRERS_WEIGHTED_COMMUTATOR_RATIO_SOURCE_RATE
```

with target \(\mathcal R_k\to0\) from the existing mode/chi source inputs and
no newly assumed rate.

Two candidate representations remain if the ratio route stalls:

```text
R1 — combined commutator ratio Gamma / q0
kill-power: 10/10
cost: 4/10

R2 — source form-dual residual restricted to the center-anchored hyperplane
kill-power: 9/10
cost: 7/10
```

## STRONGEST ATTACK

The strongest objection is that a small beta moment does not control the full
commutator defect.  This objection is correct.

A diagonal matrix commuting with the mode diagonal can have beta vector zero,
while a non-eigenvector trial has a nonzero mode-weighted Rayleigh residual.
Therefore B3A cannot be promoted directly to a residual rate.  The repaired B3B
keeps the exact combined quantity \(\Gamma_k=D_kr_k\).

A second obstruction is the kernel of \(D_k\): it annihilates the center mode.
Without the center coefficient, \(D_kr_k\) cannot control \(r_k\).  The next file
must include this mandatory plant:

```text
center_mode_kernel_is_load_bearing_plant
```

For `Fin 2`, take `D = diag(0,1)`, `K = [[0,1],[1,0]]`, and `q = e1`.
Then the exact Rayleigh residual is `e0`, so `D r = 0` while
`residualEnergy = 1`; also the center coefficient of `q` is zero.  This kills
every theorem omitting the center anchor.

The second mandatory plant is:

```text
beta_moment_zero_does_not_control_commutator_defect_plant
```

Take `D = diag(0,1)`, `K = diag(0,1)`, `beta = 0`, and the unit row
`q = (3/5,4/5)`.  The source-style commutator is zero and the beta moment is
zero, but the exact Rayleigh residual has nonzero mode-weighted component.
This kills the shortcut `B_k = 0 -> Gamma_k = 0`.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN

BASE_HEAD:
  use live `git rev-parse HEAD`; expected parent is the Proshka verdict commit
  directly above source commit 89a74b33.

LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersCommutatorResidualDefect.lean

SOURCE RECORD:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_DEFECT_2026-08-23.md

DIRECT IMPORTS — EXACTLY TWO:
  import Q3.Proofs.RouteB.G6N1SelectedFerrersBetaMomentOddMass
  import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMResidualVariance

PREFLIGHT:
  ./ask.sh "selected Ferrers commutator residual defect"
  ./ask.sh "mode weighted residual center coefficient"

PUBLIC OBJECTS:
  selectedFerrersFiniteCCMAllOnesVector
  selectedFerrersFiniteCCMAllOnesMoment
  selectedFerrersFiniteCCMCenterCoefficient
  selectedFerrersFiniteCCMShiftedSourceMatrix
  selectedFerrersFiniteCCMCommutatorResidualDefect
  selectedFerrersFiniteCCMCommutatorResidualDefectEnergy
  selectedFerrersFiniteCCMWeightedCommutatorRatio

PUBLIC THEOREMS:
  selectedFerrersFiniteCCMCommutatorResidualDefect_eq_modeDiag_residual
  selectedFerrersFiniteCCMCommutatorResidualDefectEnergy_eq_modeWeightedResidualEnergy
  selectedFerrersFiniteCCMCenterCoefficient_ne
  selectedFerrersFiniteCCMCenterCoeff_normSq_mul_residualEnergy_le_commutatorDefectEnergy
  selectedFerrersFiniteCCMBetaCorrectionEnergy_le_card_mul_betaEnergy_mul_oddMass
  selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio

EXACT DEFINITIONS:
  i_k := (selectedFerrersCofinalSourceData P).index k
  q_k := selectedFerrersFiniteCCMRow P k
  a_k := selectedFerrersFiniteCCMRayleigh P k
  S_k := sourceCCMFiniteMatrix i_k - (a_k : C) • 1
  A_k := allOnesVector dot q_k
  B_k := selectedFerrersFiniteCCMBetaMoment P k

  Gamma_k :=
    S_k *v selectedFerrersFiniteCCMModeWeightedRow P k
    + A_k • selectedFerrersFiniteCCMBetaVector P k
    - B_k • allOnesVector

  GammaEnergy_k := sum_j normSq (Gamma_k j)

  WeightedCommutatorRatio_k :=
    selectedFerrersFiniteCCMOddMass P k * GammaEnergy_k /
      normSq (centerCoefficient_k)

MANDATORY IDENTITIES:
  Gamma_k j = (mode_j : C) * selectedFerrersFiniteCCMResidual P k j

  GammaEnergy_k =
    sum_j (mode_j : R)^2 * normSq (selectedFerrersFiniteCCMResidual P k j)

  normSq(centerCoefficient_k) *
    selectedFerrersFiniteCCMResidualEnergy P k <= GammaEnergy_k

  card * normSq(B_k) <=
    card * selectedFerrersFiniteCCMBetaEnergy P k *
      selectedFerrersFiniteCCMOddMass P k

MANDATORY PLANTS:
  center_mode_kernel_is_load_bearing_plant
  beta_moment_zero_does_not_control_commutator_defect_plant

PROOF ROUTE:
  1. Run both ask.sh preflights.
  2. Build the exact selected shifted matrix and all-ones objects.
  3. Cast or specialize the source rank-two commutator without changing
     orientation; apply it to the exact selected row.
  4. Prove Gamma = D residual before taking norms.
  5. Prove the weighted-energy identity entrywise.
  6. Prove centerCoefficient != 0 from selected rawZeroNonzero and the exact
     raw-zero = sqrt(L) * c0 theorem; do not use a numerical floor.
  7. Prove the center-weighted residual bound from unit q, q*residual = 0,
     Cauchy--Schwarz off the center, and |mode| >= 1 off the center.
  8. Import B3A only for the beta-correction budget; preserve Gamma as one
     combined vector.
  9. Derive the Tendsto receiver by squeeze and sqrt continuity.
  10. Print axioms of every public theorem and both plants.

FORBIDDEN:
  - no claim that betaEnergy is small or polylogarithmic;
  - no inference betaMoment -> residual;
  - no replacement of Gamma by a sum of component norms as the exact object;
  - no identification of allOnesMoment with Gwin(0), Mellin anchor, betaMoment,
    or the center coefficient;
  - no uniform lower bound on centerCoefficient added as a hypothesis;
  - no ambient associated operator or compression claim;
  - no residual-decay assumption;
  - no sector-floor supplier, simple ground, Theorem 5.10, or RH claim;
  - no source-action split into target/error imported as a substitute;
  - no row sums, ambient opNorm, numerics, paper axiom, sorry, admit, typed hole,
    or theorem weakening.

GATE:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersCommutatorResidualDefect

  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN

FAILURE:
  H2A_4_1B_3B_COMPLEX_COMMUTATOR_CAST_OR_CENTER_RESIDUAL_ENERGY_GAP
```

## META CLOSEOUT

**What became smaller?**

The undefined phrase “commutator defect weighted rate” is replaced by one exact
source scalar:

\[
 \mathcal R_k
 =
 \eta_k\|\Gamma_k\|^2/|q_{0,k}|^2.
\]

**What was killed?**

- beta moment smallness as a substitute for residual control;
- mode-diagonal defect without a center anchor;
- componentwise absolute estimates as the mandatory route;
- direct promotion from B3A to the full weighted-residual source rate.

**What must not be tried again?**

Do not infer a rate from odd mass without beta-energy/source-action control, and
do not split the exact combined commutator before checking source cancellation.

**Current smallest named gap:**

```text
H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN
```

**Next cheapest decisive test:**

Compile the exact complex commutator identity and the center-weighted residual
inequality.  If either fails semantically, the structured source-action route is
misidentified before any asymptotic work begins.

**Fate of prior predictions:**

All three B3A predictions are confirmed.  The predicted failure class was only
partially observed as dot-product/sum normal-form friction.  No retroactive
repair occurred.

```yaml
iteration:
  target: H2A.4.1B.3A beta-moment source lock
  status: PROGRESS
  failed_strategy: direct_betaMoment_to_residual_rate
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_RATIO_LOCK_LEAN
  invariant_learned: preserve_the_exact_combined_commutator_and_the_center_anchor
  forbidden_future_move: betaMoment_or_componentwise_majorants_as_full_residual_surrogate
  next_decisive_test: kernel_check_Gamma_equals_D_residual_and_center_weighted_energy_bound
  progress_class: PROOF_PROGRESS
  route_score: 5
```
