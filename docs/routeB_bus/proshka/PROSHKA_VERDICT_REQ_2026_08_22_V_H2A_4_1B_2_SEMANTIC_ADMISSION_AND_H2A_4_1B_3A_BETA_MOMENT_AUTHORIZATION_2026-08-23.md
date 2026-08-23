# STATUS: PROVED — H2A.4.1B.2 SEMANTICALLY ADMITTED; H2A.4.1B.3 SOURCE-RATE TARGET LOCKED; B.3A BETA-MOMENT SOURCE BOUND AUTHORIZED
```yaml
PRIMARY: ADMIT_WEIGHTED_RESIDUAL_COMPLEMENT_FLOOR_AND_AUTHORIZE_BETA_MOMENT_SOURCE_LOCK
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_COMMIT: 65c1cf3cc45e594c0e3a14c324522880da27fd71
  SOURCE_PARENT: b3e0e6ea2d19a398df184f81d0de7917e54718b4
  SOURCE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersWeightedResidualComplementFloor.lean
  SOURCE_GIT_BLOB: 3840090d77d04b4881e539a86a3924e310df31a0
  SOURCE_SHA256: c761d2b83b30a929c36bae7fb8757f3314e1088bac420a6e5c98a5f5589d72c5
  SOURCE_LINES: 357
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_2_WEIGHTED_RESIDUAL_COMPLEMENT_FLOOR_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: 015d5a05acfba9e2dc7c349f1e99b3defafdc6e6
  HEAD_AT_AUDIT: 65c1cf3cc45e594c0e3a14c324522880da27fd71
  PARENT_EXACT: true

H2A_4_1B_2:
  SEMANTIC_ADMISSION: PROVED
  SCOPE: COFINAL_FAMILY
  VERIFIER: LEAN
  PUBLIC_THEOREM: selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
  FIXED_OUTPUT_FLOOR: beta0_over_2
  SOURCE_RATE_PROVED: false
  SECTOR_FLOOR_SUPPLIERS_PROVED: false
  SIMPLE_GROUND_PROVED: false
  THEOREM_510_PROVED: false
  RH_CLAIMED: false

PLANTS:
  WEIGHTED_RESIDUAL_IS_LOAD_BEARING: RATIFIED
  RESIDUAL_DECAY_IS_NOT_NECESSARY: RATIFIED

GATE_RELIANCE:
  JUDGE_RERAN_LEAN: false
  LINUX_LAKE_ENV_LEAN: PASS
  LINUX_TARGET_BUILD: PASS_7927_JOBS
  LINUX_Q3_CHECK: PASS
  OBSERVED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound
  SORRY_AX: false

H2A_4_1B_3_FINAL_CONTRACT:
  CODE: H2A_4_1B_3_SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
  STATUS: OPEN_NOT_AUTHORIZED_DIRECTLY
  REQUIRED_CONCLUSION: >-
    sqrt(selectedFerrersFiniteCCMOddMass P k) multiplied by
    sqrt(selectedFerrersFiniteCCMResidualEnergy P k) tends to zero
    along atTop, for the exact port P built from the existing hmode/hchi inputs.
  NEW_RATE_HYPOTHESIS_ALLOWED: false
  RESIDUAL_DECAY_REQUIRED: false
  EXACT_SELECTED_ROW_REQUIRED: true
  EXACT_RAYLEIGH_SHIFT_REQUIRED: true
  EXACT_PRECOMMITTED_SCHEDULE_REQUIRED: true

NEXT_AUTHORIZATION:
  CODE: H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN
  STATUS: AUTHORIZED
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_2026-08-23.md
  DIRECT_IMPORTS_EXACT:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
    - Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne
  CLOSES:
    - SELECTED_FERRERS_BETA_MOMENT_SOURCE_CROSSWALK
    - SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND
  OPENS: []
  LEAN_WRITE_AUTHORIZED: true
  ARISTOTLE_AUTHORIZED: false

SUCCESS: H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN
FAILURE: H2A_4_1B_3A_SELECTED_BETA_ODDNESS_OR_COMPLEX_CAUCHY_SCHWARZ_GAP

NEXT_LOAD_BEARING_GAP_AFTER_ADMISSION:
  H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_DEFECT_WEIGHTED_RATE

REGISTERED_PREDICTIONS:
  P_H2A41B3A_1:
    claim: beta_moment_equals_center_coordinate_of_source_M_times_mode_weighted_selected_row
    probability: 0.96
  P_H2A41B3A_2:
    claim: source_beta_oddness_makes_beta_moment_depend_only_on_exact_selected_odd_part
    probability: 0.95
  P_H2A41B3A_3:
    claim: exact_complex_Cauchy_Schwarz_gives_normSq_betaMoment_le_betaEnergy_times_oddMass
    probability: 0.90
  LIKELIEST_FAILURE: COMPLEX_DOTPRODUCT_WITHLP_OR_SELECTED_TAIL_HN_NORMAL_FORM

PRIOR_PREDICTION_FATES:
  P_H2A41B2_1:
    fate: CONFIRMED
  P_H2A41B2_2:
    fate: CONFIRMED
  P_H2A41B2_3:
    fate: PARTIALLY_OBSERVED_NORMAL_FORMS_ONLY
  LIKELIEST_FAILURE:
    fate: PARTIALLY_OBSERVED
  RETROACTIVE_REPAIR: false

ARSENAL_MANDATE:
  STATUS: PREVIOUSLY_ACCEPTED
  ACCEPTANCE_FILE: docs/routeB_bus/proshka/PROSHKA_VERDICT_ARSENAL_ACCEPTANCE_2026-08-17.md
  CARDS_APPLIED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. H2A.4.1B.2 proves the intended consumer

Put

\[
\eta_k=
\operatorname{selectedFerrersFiniteCCMOddMass}(P,k),
\qquad
\rho_k=
\sqrt{\operatorname{selectedFerrersFiniteCCMResidualEnergy}(P,k)}.
\]

The exact H2A.1 effective floor at a common sector floor \(\beta_0>0\) is

\[
F_k=
\beta_0(1-\eta_k)
-
\frac{2\sqrt{\eta_k}+\eta_k}{\sqrt{1-\eta_k}}\rho_k.
\]

The source proves the exact factorization

\[
(2\sqrt{\eta_k}+\eta_k)\rho_k
=
(2+\sqrt{\eta_k})(\sqrt{\eta_k}\rho_k).
\]

Therefore

\[
\eta_k\to0,
\qquad
\sqrt{\eta_k}\rho_k\to0
\]

imply

\[
F_k\to\beta_0.
\]

The Lean proof then obtains eventually \(F_k\ge\beta_0/2\), invokes the literal selected-source H2A.1 receiver at the exact row, matrix, Rayleigh shift, odd mass and residual, and downgrades the resulting varying floor to the fixed predicate

\[
\operatorname{complexTrialComplementFloor}(K_k,q_k,a_k,\beta_0/2).
\]

The downgrade is legitimate because it multiplies \(\beta_0/2\le F_k\) by the nonnegative squared norm of the exact projected vector. It does not change the source object or invoke a new spectral theorem. `[COFINAL_FAMILY][LEAN]`

### 2. The residual-energy normalization is exact

The theorem chooses

\[
\rho_k=\sqrt{E_k},
\qquad
E_k=\operatorname{selectedFerrersFiniteCCMResidualEnergy}(P,k).
\]

H2A.4.0 already identifies \(E_k\) with the real Hermitian norm-square of the literal selected residual. The new proof uses nonnegativity and

\[
E_k=(\sqrt{E_k})^2
\]

exactly. No operator norm, fitted shift, Galerkin residual or physical \(L^2\) surrogate enters. `[COFINAL_FAMILY][LEAN]`

### 3. Both plants are semantic guards, not decoration

The first plant takes

\[
\eta_n=(n+2)^{-2},
\qquad
\rho_n=(n+2)^2.
\]

Then \(\eta_n\to0\), but \(\sqrt{\eta_n}\rho_n=n+2\), and the effective floor is negative. Thus odd-mass decay alone does not close the consumer.

The second plant takes \(\eta_n=0\) and an unbounded \(\rho_n=n\). The contamination term vanishes identically and the effective floor remains exactly \(1\). Thus plain residual decay was never necessary. `[ABSTRACT][LEAN]`

### 4. Hard boundary

H2A.4.1B.2 does **not** prove any of the following:

```text
sqrt(oddMass_k) * residualNorm_k -> 0;
uniform even-sector floor;
uniform odd-sector floor;
positive cofinal complement floor without those suppliers;
simple bottom ground;
Theorem 5.10;
real zeros;
RH.
```

The theorem is a correct conditional consumer. The source-rate wall remains open. `[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

### The final H2A.4.1B.3 theorem shape

The eventual source theorem remains:

```lean
theorem selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_modeAndChiRates
    (C0 C4 Cchi : ℝ)
    (hC0 : 0 ≤ C0)
    (hC4 : 0 ≤ C4)
    (hCchi : 0 ≤ Cchi)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4
              (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hchi :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cchi / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cchi / (selectedFerrersPaperLambda k) ^ 2) :
    let P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
      C0 C4 Cchi hC0 hC4 hCchi hmode hchi
    Filter.Tendsto
      (fun k =>
        Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
          Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
      Filter.atTop (nhds 0)
```

This theorem is **not authorized for direct implementation yet**. The current repository does not contain a legal source derivation of its conclusion. Adding the conclusion as a new hypothesis would merely rename the wall.

### Why the beta moment is the cheapest discriminator

Let

\[
i_k=(\operatorname{selectedFerrersCofinalSourceData}P).\operatorname{index}(k),
\qquad
q_k=\operatorname{selectedFerrersFiniteCCMRow}(P,k),
\]

\[
\beta_k=\operatorname{ccmBetaFinite}(i_k.m,i_k.N).
\]

The exact structured commutator contains the scalar

\[
\beta_k\cdot q_k.
\]

This scalar is **not** the all-ones moment `ccmEtaFinite dot q`, not the ordinary zero-mode anchor, and not a Mellin value already supplied by L73. It is the center coordinate of the source action on the mode-weighted row:

\[
\boxed{
\beta_k\cdot q_k
=
\bigl(M_k(D_kq_k)\bigr)_{\mathrm{center}}.
}
\]

That equality is the required C04/C10 source lock.

The source beta vector is reflection-odd. Consequently it annihilates the exact reflection-even part of the selected row and sees only the selected odd part:

\[
\boxed{
\beta_k\cdot q_k
=
\beta_k\cdot q_k^{-}.
}
\]

Finite complex Cauchy–Schwarz should then give the exact bound

\[
\boxed{
|\beta_k\cdot q_k|^2
\le
\left(\sum_j\beta_{k,j}^2\right)\eta_k.
}
\]

This does not prove the weighted residual source rate. It turns one previously unmapped source-action moment into a product of an explicit source beta-energy and the already-proved odd mass. That is the cheapest belief-changing theorem before any prime/archimedean rate analysis.

## STRONGEST ATTACK

### Attack on H2A.4.1B.2

A reviewer may object that the theorem silently replaced a large residual by a small one. It did not. The residual can grow without bound. The proof only assumes that its growth is killed by the vanishing odd contamination:

\[
\sqrt{\eta_k}\rho_k\to0.
\]

The second plant demonstrates the extreme case \(\eta_k=0\), where the residual is completely irrelevant to the effective floor. The first plant demonstrates that odd-mass decay alone is insufficient. The theorem therefore proves exactly the consumer and no stronger narrative.

### Attack on the beta-moment proposal

The ordinary center/all-ones moment cannot be substituted for \(\beta\cdot q\). On `Fin 3`, take

```text
all-ones vector: (1,1,1)
beta vector:     (-1,0,1)
q1:              (1,0,0)
q2:              (0,1,0)
```

Both rows have the same all-ones moment `1`, but their beta moments are `-1` and `0`. This is a direct **C04 SAME-COORDINATES-TWO-LAWS** and **C10 FUNCTIONAL-NOT-SURROGATE** falsifier.

Likewise beta oddness is load-bearing: with the reflection swapping coordinates `0` and `2`, the even unit row `(0,1,0)` has odd mass zero. An arbitrary even beta vector `(0,1,0)` nevertheless has beta moment one. Therefore the odd-mass bound is valid only for the exact source beta vector with its proved reflection-odd law.

The weakest repaired statement is precisely the source-locked beta-moment theorem below.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN

BASE_HEAD:
  use live git rev-parse HEAD immediately before editing;
  expected current parent is the Proshka verdict commit produced by this file.

PREFLIGHT:
  ./ask.sh "selected Ferrers beta moment odd mass"
  ./ask.sh "ccmBetaFinite odd part Cauchy Schwarz"

LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersBetaMomentOddMass.lean

SOURCE RECORD:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_2026-08-23.md

DIRECT IMPORTS — EXACTLY TWO:
  import Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay
  import Q3.Proofs.RouteB.CCMFiniteWeilShiftedRankOne

PUBLIC SURFACE:
  selectedFerrersFiniteCCMBetaVector
  selectedFerrersFiniteCCMBetaMoment
  selectedFerrersFiniteCCMBetaEnergy
  selectedFerrersFiniteCCMModeWeightedRow
  selectedFerrersFiniteCCMBetaMoment_eq_center_modeWeighted_sourceAction
  selectedFerrersFiniteCCMBetaMoment_eq_beta_dot_oddPart
  selectedFerrersFiniteCCMBetaMoment_normSq_le_betaEnergy_mul_oddMass

MANDATORY MATHEMATICAL SHAPES:

  betaVector_k(j) = complex_cast(ccmBetaFinite(i_k.m, i_k.N, j)).

  betaMoment_k = betaVector_k dot selectedRow_k.

  betaEnergy_k = sum_j (ccmBetaFinite(i_k.m, i_k.N, j))^2.

  modeWeightedRow_k(j) = complex_cast(ccmModeFinite(i_k.N,j)) * selectedRow_k(j).

  betaMoment_k =
    (sourceCCMFiniteMatrix(i_k) * modeWeightedRow_k)[ccmCenterFinite(i_k.N)].

  betaMoment_k = betaVector_k dot selectedOddPart_k.

  Complex.normSq(betaMoment_k)
    <= betaEnergy_k * selectedFerrersFiniteCCMOddMass(P,k).

PROOF ROUTE:
  1. Recover the exact pre-anchor rank using the public H2A.3 crosswalk.
     Obtain m=N=rank+2 and hence the hypotheses needed by the existing
     source beta-oddness theorem. Do not inspect the private tail shift.
  2. Prove the center-action identity from the literal definition
     beta_j = mode_j * M_{j,center}, the exact source matrix symmetry,
     and one finite sum. Preserve the complex cast explicitly.
  3. Use ccmBetaFinite_neg and the reflection reindexing to show the beta
     vector annihilates the selected even part. Conclude that betaMoment
     equals its pairing with selectedFerrersFiniteCCMOddPart.
  4. Apply finite-dimensional complex Cauchy–Schwarz in the exact Euclidean
     carrier. Rewrite the beta-vector norm-square as betaEnergy and the
     odd-part norm-square as selectedFerrersFiniteCCMOddMass.
  5. Print axioms for every public theorem and both plants.

MANDATORY PLANTS:
  allOnesMoment_does_not_determine_betaMoment_plant
    Fin 3; all-ones=(1,1,1), beta=(-1,0,1), q1=(1,0,0), q2=(0,1,0).
    Both all-ones moments are 1; beta moments differ.

  beta_oddness_is_load_bearing_plant
    Fin 3 reflection swaps 0 and 2; q=(0,1,0) is exactly even and has
    odd mass 0; arbitrary beta=(0,1,0) has beta moment 1.

FORBIDDEN:
  - Do not identify betaMoment with ccmEtaFinite dot q.
  - Do not identify betaMoment with Gwin(0), a Mellin anchor, or the
    ordinary center coefficient.
  - Do not claim betaMoment tends to zero from oddMass tends to zero
    without controlling betaEnergy.
  - Do not use absolute row sums or an ambient operator norm.
  - Do not add a beta-energy rate hypothesis.
  - Do not claim the weighted residual source rate.
  - Do not change the selected row, source matrix, exact Rayleigh shift,
    tail shift, source scale or precommitted schedule.
  - Do not import H2A.4.1A merely to rename its triangle budget.
  - No numerics, paper axiom, sorry, admit, typed hole or weakening.

CLOSES:
  SELECTED_FERRERS_BETA_MOMENT_SOURCE_CROSSWALK
  SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND

OPENS:
  none

VERIFICATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersBetaMomentOddMass

  WORKDIR repository root:
    scripts/q3_check.sh \
      Q3/Proofs/RouteB/G6N1SelectedFerrersBetaMomentOddMass.lean

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN

FAILURE:
  H2A_4_1B_3A_SELECTED_BETA_ODDNESS_OR_COMPLEX_CAUCHY_SCHWARZ_GAP
```

## META CLOSEOUT

**What became smaller?**

The downstream H2A consumer is no longer asking for residual decay. It now asks only for the source quantity actually present in the contamination loss:

\[
\sqrt{\eta_k}\rho_k\to0.
\]

The first structured moment inside the source commutator is reduced to a precise finite theorem: center action, odd-part identity and Cauchy–Schwarz bound.

**What was killed?**

```text
oddMass decay alone closes H2A;
rho must tend to zero;
beta dot q is the L73 zero-mode anchor;
all-ones moment can substitute for beta moment;
arbitrary beta vectors satisfy the odd-mass bound.
```

**What must not be tried again?**

Do not return to the separated `A_k+T_k -> 0` demand as though it were necessary. Do not replace the mode-weighted source-action functional by an unweighted transform value. Do not declare betaMoment small before its source beta-energy is controlled.

**Current smallest named gap:**

```text
H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN
```

**Next cheapest decisive test:**

Kernel-check the exact beta-moment source lock. If the theorem passes, inspect the selected-schedule growth of `betaEnergy` and the exact commutator defect before attempting the full weighted residual rate.

**Fate of prior predictions:**

```text
P_H2A41B2_1: CONFIRMED.
P_H2A41B2_2: CONFIRMED.
P_H2A41B2_3: PARTIALLY OBSERVED — normal-form friction only.
Retroactive repair: false.
```

```yaml
iteration:
  target: H2A.4.1B.2 semantic admission and H2A.4.1B.3 source-rate decomposition
  status: PROGRESS
  failed_strategy: direct_full_weighted_residual_rate_without_beta_moment_source_lock
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: H2A_4_1B_3A_SELECTED_FERRERS_BETA_MOMENT_ODD_MASS_BOUND_LEAN
  invariant_learned: mode-weighted beta moment is a distinct source functional and sees only the exact odd part because source beta is reflection-odd
  forbidden_future_move: substitute all-ones or Mellin anchor for beta moment
  next_decisive_test: kernel-check exact center-action and odd-mass beta bound
  progress_class: PROOF_PROGRESS
  route_score: 5
```
