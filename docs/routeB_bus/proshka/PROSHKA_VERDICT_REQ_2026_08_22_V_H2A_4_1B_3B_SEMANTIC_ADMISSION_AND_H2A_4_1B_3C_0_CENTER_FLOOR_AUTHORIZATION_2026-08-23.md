# STATUS: PROVED — H2A.4.1B.3B SEMANTICALLY ADMITTED; DIRECT 3C RATE SPLIT AT THE CENTER-COEFFICIENT FLOOR

```yaml
PRIMARY: ADMIT_COMMUTATOR_RATIO_LOCK_AND_AUTHORIZE_CENTER_FLOOR_REDUCTION
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_COMMIT: 854f333cd3aad56b0e6bf95208fa5daca8f4486b
  SOURCE_PARENT: 4abf5ac2129bf3fda67b428e87be3fd2423c9a1b
  SOURCE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean
  SOURCE_GIT_BLOB: 8b6f85f449efe559565dd8cb902e8ec1fbc2b354
  SOURCE_SHA256: 28f382ee884138d15b166f943b3606efa416ac9be60a4045dea86825a5a3b253
  SOURCE_LINES: 761
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3B_SELECTED_FERRERS_COMMUTATOR_RESIDUAL_DEFECT_2026-08-23.md
  HEAD_AT_AUDIT: 854f333cd3aad56b0e6bf95208fa5daca8f4486b
  PARENT_EXACT: true

H2A_4_1B_3B:
  SEMANTIC_ADMISSION: PROVED
  SCOPE: COFINAL_FAMILY
  VERIFIER: LEAN
  EXACT_COMMUTATOR_RESIDUAL_IDENTITY: CLOSED
  MODE_WEIGHTED_RESIDUAL_ENERGY: CLOSED
  POINTWISE_CENTER_NONVANISHING: CLOSED
  CENTER_WEIGHTED_RESIDUAL_BOUND: CLOSED
  RATIO_TO_WEIGHTED_RESIDUAL_RECEIVER: CLOSED
  RATIO_SOURCE_RATE: OPEN

PLANTS:
  CENTER_MODE_KERNEL_IS_LOAD_BEARING: RATIFIED
  BETA_MOMENT_ZERO_DOES_NOT_CONTROL_COMMUTATOR_DEFECT: RATIFIED

GATE_RELIANCE:
  JUDGE_RERAN_LEAN: false
  LINUX_LAKE_ENV_LEAN: PASS
  LINUX_TARGET_BUILD: PASS_7928_JOBS
  LINUX_Q3_CHECK: PASS
  OBSERVED_AXIOMS:
    - propext
    - Classical.choice
    - Quot.sound
  SORRY_AX: false

ARSENAL_MANDATE:
  ACCEPTED: true
  CARDS_USED:
    - C04_SAME_COORDINATES_TWO_LAWS
    - C10_FUNCTIONAL_NOT_SURROGATE
    - C12_BOUNDED_POTENTIAL_EXCLUSION

REQUESTED_NEXT:
  CODE: H2A_4_1B_3C_SELECTED_FERRERS_WEIGHTED_COMMUTATOR_RATIO_SOURCE_RATE
  DIRECT_IMPLEMENTATION_STATUS: REJECTED_AS_PREMATURE
  REASON: >-
    The ratio is a valid sufficient consumer, but its denominator is only
    pointwise nonzero.  Pointwise nonvanishing supplies legal division, not an
    asymptotic lower envelope.  Before attacking the numerator, the selected
    source must prove the natural center scale
      L_k * |q_{0,k}|^2 >= c_center > 0 eventually.
    Without this floor a proof of ratio decay can fail solely through center
    normalization and would not diagnose the source action.

NEXT_AUTHORIZATION:
  CODE: H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN
  STATUS: AUTHORIZED
  LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_FLOOR_2026-08-23.md
  DIRECT_IMPORTS_EXACT:
    - Q3.Proofs.RouteB.G6N1SelectedFerrersCommutatorResidualDefect
  LEAN_WRITE_AUTHORIZED: true
  ARISTOTLE_AUTHORIZED: false
  CLOSES:
    - SELECTED_FERRERS_CENTER_COEFFICIENT_ANCHOR_IDENTITY
    - SELECTED_FERRERS_CENTER_COEFFICIENT_INVERSE_LOG_FLOOR
    - SELECTED_FERRERS_RATIO_DENOMINATOR_REMOVAL
    - SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_TO_WEIGHTED_RESIDUAL_RECEIVER
  OPENS:
    - SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE

SUCCESS: H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN
FAILURE: H2A_4_1B_3C_0_TARGET_GLOBAL_L2_OR_CENTER_NORMALIZATION_GAP

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### Semantic admission

The selected objects are exact and shared throughout:

```text
matrix:
  sourceCCMFiniteMatrix i_k

row:
  selectedFerrersFiniteCCMRow P k

shift:
  selectedFerrersFiniteCCMRayleigh P k

residual:
  selectedFerrersFiniteCCMResidual P k

odd mass:
  selectedFerrersFiniteCCMOddMass P k

mode diagonal:
  ccmModeFinite labels on the same carrier
```

`[COFINAL_FAMILY][LEAN]`

The source commutator has the orientation

\[
D_kM_k-M_kD_k=\beta_k\otimes\mathbf 1-\mathbf 1\otimes\beta_k.
\]

Applying it to the exact selected row gives

\[
D_kM_kq_k-M_kD_kq_k
=\beta_k(\mathbf1\!\cdot q_k)-\mathbf1(\beta_k\!\cdot q_k).
\]

Therefore, for \(S_k=M_k-a_kI\),

\[
\Gamma_k
:=S_kD_kq_k
 +(\mathbf1\!\cdot q_k)\beta_k
 -(\beta_k\!\cdot q_k)\mathbf1
=D_k(M_kq_k-a_kq_k)=D_kr_k.
\]

The Lean theorem proves this identity entrywise before taking norms.  No
transpose, conjugation, realification, target/error split, or componentwise
majorant replaces the combined vector.  This passes the C04/C10 object test.

`[FINITE_CELL][LEAN]`

The energy theorem then gives exactly

\[
\|\Gamma_k\|^2
=\sum_j n_{k,j}^2|r_{k,j}|^2.
\]

`[FINITE_CELL][LEAN]`

The center estimate is also correct.  Unit normalization and
\(q_k^*r_k=0\) imply, after separating the center coordinate and applying
Cauchy--Schwarz off the center,

\[
|q_{0,k}|^2\|r_k\|^2
\le \sum_{j\ne0}|r_{k,j}|^2
\le \sum_j n_{k,j}^2|r_{k,j}|^2
=\|\Gamma_k\|^2.
\]

The proof uses \(|n_j|\ge1\) only off the exact center.  The mandatory plant
shows that the mode diagonal can annihilate a nonzero center residual when the
center coefficient is zero.

`[FINITE_CELL][LEAN]`

The theorem

```text
selectedFerrersFiniteCCMCenterCoefficient_ne
```

is source-faithful: the selected shell already proves the exact raw transform is
nonzero at zero, and

\[
\operatorname{rawFplus}_k(0)=\sqrt{L_k}\,q_{0,k}.
\]

Hence \(q_{0,k}\ne0\) for every selected index.  No numerical floor is fitted.

`[COFINAL_FAMILY][LEAN]`

Finally, with

\[
\mathcal R_k
=\eta_k\frac{\|\Gamma_k\|^2}{|q_{0,k}|^2},
\]

the center estimate gives

\[
\eta_k\|r_k\|^2\le\mathcal R_k.
\]

Thus \(\mathcal R_k\to0\) implies

\[
\sqrt{\eta_k}\,\|r_k\|\to0,
\]

which is exactly the weighted-residual consumer ratified in H2A.4.1B.2.
The square-root/squeeze proof is semantically correct.

`[COFINAL_FAMILY][LEAN]`

### Exact boundary

H2A.4.1B.3B does **not** prove:

```text
R_k -> 0;
betaEnergy growth;
center coefficient lower envelope;
sector floors;
simple ground;
Theorem 5.10;
RH.
```

The correct progress class is `REPRESENTATION_PROGRESS`: the full residual has
been compressed to one exact scalar ratio, but that ratio still needs source
analysis.

## STRONGEST ATTACK

The direct next theorem

```text
hmode + hchi -> R_k -> 0
```

is not yet source-supported.

The reason is not a cosmetic denominator.  The existing theorem gives only

\[
q_{0,k}\ne0.
\]

It does not give any positive lower envelope.  A sequence of unit vectors can
have nonzero center coefficient at every index while that coefficient tends to
zero arbitrarily fast.  Thus pointwise nonvanishing cannot be used as a rate.
This is the C12 boundedness attack: division is legal, but the iterated ratio may
still be unbounded because its normalization scale is uncontrolled.

The natural selected-source scale is not a constant floor for \(|q_{0,k}|\).
Since the zero Fourier mode is normalized by \(L_k^{-1/2}\), the expected
statement is

\[
\boxed{
  \exists c_{\rm center}>0,\quad
  c_{\rm center}\le L_k|q_{0,k}|^2
  \quad\text{eventually}.
}
\]

This scale is forced by the exact identity

\[
Gwin_k(0)=\sqrt{L_k}\,\langle V_0,g_k\rangle.
\]

It is also the weakest useful floor: a uniform lower bound on \(|q_{0,k}|\)
would generally be too strong.

Once this floor is proved,

\[
\mathcal R_k
\le c_{\rm center}^{-1}
  L_k\eta_k\|\Gamma_k\|^2
\quad\text{eventually}.
\]

The denominator disappears.  The remaining source quantity is explicit:

\[
\boxed{
  L_k\eta_k\|\Gamma_k\|^2.
}
\]

H2A.3 already gives \(\eta_k=O(L_k/\sqrt{m_k})\), so a sufficient numerator
condition becomes

\[
\frac{L_k^2}{\sqrt{m_k}}\|\Gamma_k\|^2\to0,
\]

or equivalently

\[
\|\Gamma_k\|=o(m_k^{1/4}/L_k).
\]

This is the actual post-denominator analytic wall.  It is not proved here.

## FINAL PROPOSAL

Close the center normalization before any full source-rate attempt.

The decisive exact identity to expose is

\[
\boxed{
L_k|q_{0,k}|^2
=
\frac{|s_kGwin_k(0)|^2}
     {\|s_kP_{m_k,N_k}g_k\|^2}.
}
\]

Here:

```text
s_k:
  the exact selected sourceScale;

g_k:
  the exact selected unnormalized physical trial;

P_{m_k,N_k}:
  the exact selected Galerkin projection;

q_{0,k}:
  the exact center coefficient of the normalized selected row.
```

The numerator is eventually bounded below by the selected-shell convergence at
`z = 0` and `centeredXi_zero_ne_zero`.

The denominator is eventually bounded above because:

1. the L73.3 + L73.4 full physical error gives
   \(\|s_kg_k-G\|=O(\lambda_k^{-1/2})\);
2. orthogonal projection is contractive;
3. the factor-four target \(G=E_\star(4h)\) has a fixed global
   \(L^2(d^*u)\) norm, from its exact two-sided \(u^{7/2}/u^{-7/2}\) decay.

No bound on `sourceScale` itself is needed; it stays inside the scaled vector.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN

BASE_HEAD:
  use live `git rev-parse HEAD` after fetching rh_clean;
  expected parent is this verdict commit.

PREFLIGHT, BEFORE EDITING:
  ./ask.sh "selected Ferrers center coefficient log floor"
  ./ask.sh "scaled projection norm target global L2"

ONE LEAN FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersCenterCoefficientFloor.lean

ONE SOURCE RECORD, SAME COMMIT:
  docs/routeB_bus/
  LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_FLOOR_2026-08-23.md

EXACT DIRECT IMPORT:
  import Q3.Proofs.RouteB.G6N1SelectedFerrersCommutatorResidualDefect
```

### Required public surface

```lean
selectedFerrersFiniteCCM_log_mul_centerCoeff_normSq_eq_anchor_div_scaledProjectionNormSq

selectedFerrersFiniteCCMCenterCoefficient_eventually_inv_log_floor_of_modeAndChiRates

selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates
```

### Target shape 1 — exact anchor identity

For every exact selected port `P` and rank `k`, prove the exact scalar identity

\[
L_k|q_{0,k}|^2
=
\frac{|s_kGwin_k(0)|^2}
     {\|s_kP_{m_k,N_k}g_k\|^2}.
\]

The Lean statement may name the exact projected trial explicitly, but it must use:

```text
(selectedFerrersCofinalSourceData P).sourceScale k;
(selectedFerrersCofinalSourceData P).index k;
(selectedFerrersCofinalSourceData P).pair k;
selectedFerrersFiniteCCMCenterCoefficient P k;
gTrial_m_N;
preAnchorGwinTransformCoordinate ... 0.
```

Do not replace the denominator by a fitted normalizer or a neighboring target.

### Target shape 2 — source-derived inverse-log floor

Use the exact `hmode` and `hchi` types copied verbatim from

```lean
selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
```

and define

```lean
P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
  C0 C4 Cchi hC0 hC4 hCchi hmode hchi
```

Then prove:

```lean
∃ cCenter : ℝ, 0 < cCenter ∧
  ∀ᶠ k in Filter.atTop,
    cCenter ≤
      L_m ((selectedFerrersCofinalSourceData P).index k) *
        Complex.normSq
          (selectedFerrersFiniteCCMCenterCoefficient P k)
```

The target global `L²(dStar)` bound must be derived from the exact factor-four
`explicitCCMLimitH` packet.  A window bound growing like `lambda^5` does not
close this theorem and is forbidden as the final estimate.

### Target shape 3 — denominator-free receiver

With the same exact mode/chi inputs, assume only

```lean
Filter.Tendsto
  (fun k =>
    L_m ((selectedFerrersCofinalSourceData P).index k) *
      selectedFerrersFiniteCCMOddMass P k *
      selectedFerrersFiniteCCMCommutatorResidualDefectEnergy P k)
  Filter.atTop (nhds 0)
```

and conclude

```lean
Filter.Tendsto
  (fun k =>
    Real.sqrt (selectedFerrersFiniteCCMOddMass P k) *
      Real.sqrt (selectedFerrersFiniteCCMResidualEnergy P k))
  Filter.atTop (nhds 0)
```

Proof route: inverse-log center floor -> ratio tends to zero -> existing 3B
receiver.  Do not assume `R_k -> 0` separately.

### Mandatory plants

```text
pointwise_center_nonzero_without_log_floor_plant
```

A unit sequence with every center coefficient nonzero but
`L_k * |q0_k|^2 -> 0`.  This kills `q0 != 0 -> inverse-log floor`.

```text
anchor_without_scaled_projection_upper_bound_does_not_force_center_floor_plant
```

Keep `|s_k Gwin_k(0)| = 1` while the scaled projected norm diverges, so the
center floor vanishes.  This proves that the target/global-norm upper bound is
load-bearing.

### Forbidden

```text
No uniform constant lower bound on |q0_k|.
No pointwise-nonzero-as-rate inference.
No fitted sourceScale bound.
No lambda^5 target norm as the final floor.
No betaEnergy rate.
No claim that GammaEnergy already tends to zero.
No row sums or ambient operator norm.
No target/error termwise split replacing the combined Gamma.
No sector floors, simple ground, Theorem 5.10, or RH.
No edits to H2A.3 or H2A.4.1B.3B.
No sorry, admit, typed hole, paper axiom, numerics, or weakening.
```

### Gate

```bash
# WORKDIR: q3.lean.aristotle
lake env lean \
  Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean

lake build \
  Q3.Proofs.RouteB.G6N1SelectedFerrersCenterCoefficientFloor

# WORKDIR: repository root
scripts/q3_check.sh \
  Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean
```

Expected profile for all public theorems and both plants:

```text
[propext, Classical.choice, Quot.sound]
```

```text
SUCCESS:
  H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN

FAILURE:
  H2A_4_1B_3C_0_TARGET_GLOBAL_L2_OR_CENTER_NORMALIZATION_GAP
```

The next floor after separate semantic admission is:

```text
H2A_4_1B_3C_1_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE
```

It is not authorized now.

## PREDICTION FATES

```text
P_H2A41B3B_1 = 0.96:
  CONFIRMED.
  Gamma = D residual closed by exact commutator algebra.

P_H2A41B3B_2 = 0.94:
  CONFIRMED.
  rawZeroNonzero gives pointwise center nonvanishing.

P_H2A41B3B_3 = 0.88:
  CONFIRMED.
  Unit norm + residual orthogonality give the center-weighted energy bound.

P_H2A41B3B_4 = 0.97:
  CONFIRMED.
  The beta-correction one-sided budget compiled.

LIKELIEST_FAILURE:
  COMPLEX_MATRIX_CAST_OR_CENTER_EXCLUSION_FINSET_NORMAL_FORM.

FATE:
  OBSERVED EXACTLY.

RETROACTIVE_REPAIR:
  false.
```

New predictions:

```text
P_H2A41B3C0_1 = 0.91:
  The exact anchor/center identity closes without new analysis.

P_H2A41B3C0_2 = 0.82:
  The factor-four target has a uniform global L2(dStar) bound sufficient for
  the eventual inverse-log center floor.

P_H2A41B3C0_3 = 0.94:
  The denominator-free receiver closes by eventual inequalities and the
  existing ratio receiver.

LIKELIEST_FAILURE:
  TARGET_GLOBAL_L2_MEMLP_OR_PROJECTED_NORM_NORMAL_FORM.
```

## META CLOSEOUT

```text
PROGRESS_CLASS:
  REPRESENTATION_PROGRESS.

WHAT_BECAME_SMALLER:
  Full weighted residual control is reduced to one exact ratio; the ratio is
  now split into a source-derived center floor and one denominator-free
  log-weighted commutator-energy rate.

WHAT_WAS_KILLED:
  - betaMoment = 0 as a residual theorem;
  - mode-weighted residual without a center anchor;
  - pointwise center nonvanishing as an asymptotic floor;
  - direct H2A.4.1B.3C implementation before normalization control.

DO_NOT_TRY_AGAIN:
  - divide by q0 merely because q0 != 0;
  - separate Gamma into component norms as the exact consumer;
  - infer source action from L73 L2 convergence without the required norm.

CURRENT_SMALLEST_NAMED_GAP:
  H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN.

NEXT_CHEAPEST_DECISIVE_TEST:
  Prove the exact anchor ratio and the global target L2 bound; if the latter
  cannot be made uniform, stop before any commutator-rate work.

MEMORY_ENTRY:
  target: weighted commutator ratio source supply
  status: PROGRESS
  failed_strategy: direct ratio rate from pointwise q0 nonvanishing
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: selected center inverse-log floor
  invariant_learned: keep sourceScale inside the scaled projected vector
  forbidden_future_move: no pointwise-nonzero-as-rate
  next_decisive_test: uniform global target L2 bound plus exact anchor identity

ROUTE_SCORE:
  5
```
