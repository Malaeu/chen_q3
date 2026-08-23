# STATUS: PROVED — H2A.4.1B.3C.0 SEMANTICALLY ADMITTED; DIRECT 3C.1 RATE THEOREM DEFERRED TO ONE SOURCE-RATE PREFLIGHT

```yaml
PRIMARY: ADMIT_CENTER_FLOOR_AND_AUTHORIZE_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-22-V

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_COMMIT: 03ed411e94fbf80d6462295a25d724274470a76a
  SOURCE_PARENT: 580e0a003ae269100cd46561b3469d85b4ab0548
  SOURCE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean
  SOURCE_GIT_BLOB: a237de2ae6457423ab25ff016a649494cd944e66
  SOURCE_SHA256: dc98d27049f366eab9898c8c78baa8c1a3ce3591f220cf4400a937657db41e18
  SOURCE_LINES: 1500
  SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_FLOOR_2026-08-23.md
  SOURCE_RECORD_GIT_BLOB: bf1e75b73b59f882c96d9186f754069d6d9d1aa4
  HEAD_AT_AUDIT: 03ed411e94fbf80d6462295a25d724274470a76a
  PARENT_EXACT: true

H2A_4_1B_3C_0:
  SEMANTIC_ADMISSION: PROVED
  SCOPE: COFINAL_FAMILY
  VERIFIER: LEAN
  EXACT_CENTER_ANCHOR_IDENTITY: CLOSED
  UNIFORM_WINDOW_TARGET_L2_CAP: CLOSED
  INVERSE_LOG_CENTER_FLOOR: CLOSED
  RATIO_DENOMINATOR_REMOVAL: CLOSED
  LOG_WEIGHTED_COMMUTATOR_TO_WEIGHTED_RESIDUAL_RECEIVER: CLOSED
  LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE: OPEN

PLANTS:
  POINTWISE_CENTER_NONZERO_WITHOUT_LOG_FLOOR: RATIFIED
  ANCHOR_WITHOUT_SCALED_PROJECTION_CAP: RATIFIED

GATE_RELIANCE:
  JUDGE_RERAN_LEAN: false
  LINUX_LAKE_ENV_LEAN: PASS
  LINUX_TARGET_BUILD: PASS_7929_JOBS
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
  CODE: H2A_4_1B_3C_1_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE
  DIRECT_LEAN_IMPLEMENTATION: NOT_AUTHORIZED
  REASON: >-
    The current file proves the exact denominator-free consumer, not a source
    upper envelope for the combined commutator energy.  Writing a theorem with
    the desired Tendsto as a new hypothesis would only rename the remaining
    analytic wall.  One bounded source-rate preflight must first identify an
    unconditional envelope from the literal selected row and literal CCM source
    action, while preserving the cancellation inside Gamma.

NEXT_AUTHORIZATION:
  CODE: H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT
  MODE: READ_ONLY
  LEAN_EDIT: false
  ARISTOTLE_AUTHORIZED: false
  NUMERICS: false
  REPORT_PATH: docs/routeB_bus/H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT_2026-08-23.md
  RETURN_EXACTLY_ONE:
    - COMBINED_GAMMA_SUBCRITICAL_SOURCE_ENVELOPE_FOUND
    - LOG_COORDINATE_SOBOLEV_ENVELOPE_FOUND_PRIME_OPEN
    - PRIME_OSCILLATION_ONLY_SOURCE_GAP
    - HMODE_HCHI_INSUFFICIENT_FOR_GAMMA_SOURCE_RATE
    - CURRENT_COMMUTATOR_REPRESENTATION_RATE_FATAL

RATE_DISCRIMINATOR:
  KNOWN_ODD_MASS_RATE: eta_k <= C * L_k / sqrt(m_k)
  REQUIRED_CONSUMER: L_k * eta_k * GammaEnergy_k -> 0
  SUFFICIENT_SOURCE_ENVELOPE: GammaEnergy_k = o(sqrt(m_k) / L_k^2)
  POLYNOMIAL_LOG_TEST: >-
    If GammaEnergy_k <= C * m_k^alpha * L_k^beta eventually, the current
    consumer closes whenever alpha < 1/2; at alpha = 1/2 it requires beta < -2.

CANDIDATE_REPRESENTATIONS:
  PRIMARY:
    CODE: R1_COMBINED_LOG_COORDINATE_SOURCE_DEFECT
    DESCRIPTION: >-
      Identify the synthesis of Gamma with the mode derivative of the literal
      finite Riesz defect, then derive a selected-vector source estimate in the
      exact log-window units.  Any use of an ambient associated operator requires
      a proved crosswalk; finite Riesz = ambient compression may not be assumed.
    KILL_POWER: 10/10
    COST: 5/10
  RUNNER_UP:
    CODE: R2_LOEWNER_ABEL_VON_MANGOLDT_COMBINED_ACTION
    DESCRIPTION: >-
      Expand the exact combined Gamma through the Loewner divided-difference
      law and the retained finite von-Mangoldt kernel, use summation by parts or
      an exact generating identity, and keep all cancellations before norms.
    KILL_POWER: 9/10
    COST: 6/10

SUCCESS: H2A_4_1B_3C_0_SELECTED_FERRERS_CENTER_COEFFICIENT_INV_LOG_FLOOR_LEAN
FAILURE: H2A_4_1B_3C_1_SOURCE_RATE_REPRESENTATION_UNMAPPED

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

### Semantic admission

The three public theorems operate on one exact selected family:

```text
index:
  (selectedFerrersCofinalSourceData P).index k

row:
  selectedFerrersFiniteCCMRow P k

center coefficient:
  the exact zero-mode entry of that row

source scale:
  (selectedFerrersCofinalSourceData P).sourceScale k

projected trial:
  gTrial_m_N at the same index, pair and MemLp witness

commutator defect:
  selectedFerrersFiniteCCMCommutatorResidualDefect P k
```

No neighboring target row, fitted normalization, independent subsequence or
ambient compression enters the public statements.  `[COFINAL_FAMILY][LEAN]`

#### Exact center identity

The source row is the normalized projected trial.  At the center mode,

\[
q_{0,k}
= sT_k\,\langle V_0,g_k\rangle,
\qquad
sT_k=\|P_k g_k\|^{-1}.
\]

The public zero-coordinate identity gives

\[
Gwin_k(0)=\sqrt{L_k}\,\langle V_0,g_k\rangle.
\]

Therefore, with the exact source scale kept inside both terms,

\[
\boxed{
L_k|q_{0,k}|^2
=
\frac{|s_kGwin_k(0)|^2}
     {\|s_kP_kg_k\|^2}.
}
\]

The proof divides only after proving `sourceScale != 0` and the projected-trial
norm is positive.  This is an identity, not an asymptotic comparison.
`[COFINAL_FAMILY][LEAN]`

#### Uniform target cap

The factor-four target satisfies, for `u >= 1`,

\[
\|G(u)\|\le C u^{-7/2},
\]

and exact inversion gives, for `0<u<=1`,

\[
\|G(u)\|\le C u^{7/2}.
\]

Since `d*u = du/u`, the squared majorants become `C^2 u^{-8}` and
`C^2 u^6`.  Splitting every source window at `u=1` gives the fixed bound

\[
\boxed{
\|G\|_{L^2(I_m,d^*u)}^2
\le \frac{2(132 Z_4)^2}{7},
}
\]

independent of the selected index.  The older `lambda^5` window estimate is not
used.  The phrase “global cap” means uniform over all expanding selected
windows; the proved theorem itself remains a window `H_m` statement.
`[ABSTRACT][LEAN]`

#### Inverse-log floor

The selected-shell limit at `z=0` and `centeredXi(0) != 0` give eventually

\[
|s_kGwin_k(0)|\ge \|\Xi(0)\|/2.
\]

The complete L73 physical error gives eventually `||e_k|| <= 1`; projection
contractivity and the fixed target cap give

\[
\|s_kP_kg_k\|\le 1+\sqrt{M_t}.
\]

Substitution into the exact identity yields an explicit constant

\[
c_{\rm center}
=
\frac{\|\Xi(0)\|^2/4}{(1+\sqrt{M_t})^2}>0
\]

such that

\[
\boxed{
c_{\rm center}\le L_k|q_{0,k}|^2
\quad\text{eventually}.}
\]

Pointwise nonvanishing was used only to legalize divisions elsewhere, never as
an asymptotic floor.  The two plants correctly kill both forbidden shortcuts.
`[COFINAL_FAMILY][LEAN]` **[C12]**

#### Denominator-free receiver

For

\[
\mathcal R_k
=
\eta_k\frac{\|\Gamma_k\|^2}{|q_{0,k}|^2},
\]

the inverse-log floor gives eventually

\[
0\le \mathcal R_k
\le
\frac{L_k\eta_k\|\Gamma_k\|^2}{c_{\rm center}}.
\]

Hence

\[
L_k\eta_k\|\Gamma_k\|^2\to0
\Longrightarrow
\mathcal R_k\to0.
\]

The already-ratified ratio receiver then yields

\[
\sqrt{\eta_k}\sqrt{E_{\rm res,k}}\to0.
\]

The theorem does not assume ratio decay and does not claim a source rate for
`Gamma`.  `[COFINAL_FAMILY][LEAN]`

### Exact boundary

This node does **not** prove:

```text
L_k * eta_k * GammaEnergy_k -> 0;
GammaEnergy_k is bounded or decaying;
betaEnergy growth;
even-sector or odd-sector floors;
simple ground;
Theorem 5.10;
real zeros;
RH.
```

The source-derived numerator rate is the sole remaining H2A.4.1B.3C wall.

## STRONGEST ATTACK

The tempting next move is to write

```lean
selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_modeAndChiRates
```

with a new hypothesis asserting exactly

```text
L_k * eta_k * GammaEnergy_k -> 0.
```

That would compile a thin receiver while closing no source input.  It is rejected
by **C10 FUNCTIONAL-NOT-SURROGATE**: the consumer needs the literal combined
source action, not a renamed convergence assumption.  It also violates the
supplier ledger rule because it opens the same analytic supplier it pretends to
close. **[C10]**

A second forbidden move is to bound the three terms in

\[
\Gamma_k=S_kD_kq_k+A_k\beta_k-B_k\mathbf1
\]

independently and declare their norm sum the exact object.  Earlier plants show
that the combined defect can vanish by cancellation while both separated action
terms remain large.  Componentwise bounds are permitted only as a sufficient
route after they meet the final exponent ledger; they are not the definition of
the consumer. **[C04][C10]**

Finally, the coordinate identity between mode weights and a log-window
derivative does not by itself authorize

```text
finite Riesz operator = compression of an ambient associated operator.
```

That crosswalk is absent and remains forbidden. **[C04]**

## FINAL PROPOSAL

Run exactly one read-only source-rate preflight before any new Lean source.

The arithmetic threshold is now sharp and denominator-free.  H2A.3 gives

\[
\eta_k\le C\frac{L_k}{\sqrt{m_k}}.
\]

Therefore

\[
L_k\eta_k\|\Gamma_k\|^2
\le
C\frac{L_k^2}{\sqrt{m_k}}\|\Gamma_k\|^2.
\]

The decisive question is no longer whether the center coefficient collapses.
It is exactly whether the literal selected source action supplies

\[
\boxed{
\|\Gamma_k\|^2=o\!\left(\frac{\sqrt{m_k}}{L_k^2}\right).
}
\]

A source envelope below this threshold authorizes the final Lean rate theorem.
An envelope at or above the threshold kills that proof route, not necessarily
the weighted-residual conclusion.

## CODEX DIRECTIVE

```text
TASK:
  H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT

MODE:
  READ_ONLY
  NO LEAN EDIT
  NO ARISTOTLE
  NO NUMERICS

BASE_HEAD:
  use the live rh_clean HEAD after fetching; expected parent of this verdict
  is 03ed411e94fbf80d6462295a25d724274470a76a.

OUTPUT:
  docs/routeB_bus/
  H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT_2026-08-23.md

RUN FIRST FROM REPO ROOT:
  ./ask.sh "selected Ferrers log weighted commutator energy"
  ./ask.sh "mode weighted finite Riesz defect"
  ./ask.sh "selected source prime oscillation bound"
  ./ask.sh "selected source arch graph derivative bound"

INSPECT AT MINIMUM:
  Q3/Proofs/RouteB/G6N1SelectedFerrersCommutatorResidualDefect.lean
  Q3/Proofs/RouteB/G6N1SelectedFerrersCenterCoefficientFloor.lean
  Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
  Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean
  Q3/Proofs/RouteB/D0PstarSourceWeilSesquilinearForm.lean
  Q3/Proofs/RouteB/D0PstarShiftedArchSesquilinearForm.lean
  Q3/Proofs/RouteB/D0PstarExactArchSymbolLogDomination.lean
  Q3/Proofs/RouteB/D0PstarVModeLogWeightedL2.lean
  Q3/Proofs/RouteB/D0PstarSourcePrimeModePairing.lean
  Q3/Proofs/RouteB/CCMFiniteWeilSourceCommutator.lean
  Q3/Proofs/RouteB/CCMFiniteWeilShiftedRankOne.lean
  Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrix.lean

MANDATORY TEST 1 — RATE THRESHOLD:
  Re-derive, without prose shortcuts,
    eta_k <= C L_k/sqrt(m_k)
    and
    L_k eta_k GammaEnergy_k -> 0.
  For every proposed envelope GammaEnergy <= C m^alpha L^beta, print the
  resulting exponent pair and whether it is strictly subcritical.

MANDATORY TEST 2 — EXACT OBJECT:
  Keep Gamma as the literal combined vector already proved equal to D*r.
  Do not replace it by a sum of component norms before the rate test.

MANDATORY TEST 3 — R1 LOG-COORDINATE ROUTE:
  Decide whether there is an exact source theorem, or a theorem-sized derivation,
  identifying the synthesis of Gamma with a controlled log-coordinate derivative
  of the literal finite Riesz defect.  Distinguish:
    coefficient identity;
    finite Riesz source-form identity;
    ambient associated-operator/compression identity.
  The third may not be inferred from the first two.

MANDATORY TEST 4 — R2 LOEWNER/PRIME ROUTE:
  Expand the exact combined Gamma using the Loewner divided-difference law and
  the retained finite von-Mangoldt kernel.  Preserve cancellation.  Determine
  whether Abel summation, a generating identity, or an existing source pairing
  theorem yields a strict envelope below sqrt(m)/L^2.

MANDATORY TEST 5 — COMPONENT LEDGER:
  Give separate honest exponent ledgers for W02, shifted archimedean and prime
  contributions, but do not treat their norm sum as the exact consumer.  For the
  prime part, an absolute von-Mangoldt sum is allowed only as a kill bound; it is
  not an accepted positive route if it misses the threshold.

MANDATORY TEST 6 — INPUT SUFFICIENCY:
  State whether the existing exact hmode/hchi contracts and already-ratified
  source facts logically supply every input of the proposed envelope.  Any new
  paper hypothesis, rate assumption or ambient compression theorem must be named
  as OPEN and prevents a green source-rate contract.

MANDATORY FALSIFIER:
  Exhibit a finite Fourier family with Hilbert norm tending to zero but
  mode-weighted energy at or above the critical sqrt(m)/L^2 scale.  This guards
  against silently reusing the L73 L2 estimate as a derivative estimate.

RETURN EXACTLY ONE OUTCOME_CODE:
  COMBINED_GAMMA_SUBCRITICAL_SOURCE_ENVELOPE_FOUND
  LOG_COORDINATE_SOBOLEV_ENVELOPE_FOUND_PRIME_OPEN
  PRIME_OSCILLATION_ONLY_SOURCE_GAP
  HMODE_HCHI_INSUFFICIENT_FOR_GAMMA_SOURCE_RATE
  CURRENT_COMMUTATOR_REPRESENTATION_RATE_FATAL

IF GREEN:
  Return one exact Lean theorem statement with no new analytic hypothesis and
  exact direct imports for H2A_4_1B_3C_1.

IF NOT GREEN:
  Name the minimal missing identity and give both candidate representations with
  updated kill-power/cost.  Do not write Lean.

FORBIDDEN:
  new rate hypothesis;
  row-sum or ambient-opNorm proof relabeled source-specific;
  finite Riesz = ambient compression without theorem;
  termwise replacement of Gamma;
  fitted constants;
  numerics occupying a cofinal quantifier;
  edits to H2A.3, H2A.4.1B.3B or H2A.4.1B.3C.0;
  sector floors, simple ground, Theorem 5.10 or RH bundling.
```

## META CLOSEOUT

**What became smaller?**

The moving denominator disappeared.  The remaining H2A source wall is the one
explicit scalar sequence

\[
L_k\eta_k\|\Gamma_k\|^2.
\]

**What was killed?**

- pointwise `q0 != 0` as an asymptotic floor;
- the `lambda^5` target-window bound as the center denominator estimate;
- separate ratio decay as an additional hypothesis;
- direct 3C.1 formalization with a renamed source-rate premise.

**What must not be tried again?**

- splitting the combined defect before checking the final rate;
- using bare L73 Hilbert error as mode-weighted control;
- importing an ambient operator compression that the source has not proved.

**Current smallest named gap:**

```text
SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE
```

**Next cheapest decisive test:**

The read-only R1/R2 source-envelope preflight above.

**Prior prediction fates:**

```text
P_H2A41B3C0_1 = 0.91:
  CONFIRMED.

P_H2A41B3C0_2 = 0.82:
  CONFIRMED.

P_H2A41B3C0_3 = 0.94:
  CONFIRMED.

LIKELIEST_FAILURE:
  TARGET_GLOBAL_L2_MEMLP_OR_PROJECTED_NORM_NORMAL_FORM.

FATE:
  PARTIALLY OBSERVED — normal-form friction only.

RETROACTIVE_REPAIR:
  false.
```

**New registered predictions:**

```text
P_H2A41B3C1_0_1 = 0.95:
  no existing theorem already proves the full subcritical Gamma envelope.

P_H2A41B3C1_0_2 = 0.78:
  W02 and shifted-arch selected-vector contributions admit subcritical
  polynomial-log envelopes once exact source units are retained.

P_H2A41B3C1_0_3 = 0.82:
  the retained prime contribution remains the sole load-bearing source gap,
  requiring an oscillatory/Abel identity rather than an absolute sum.

LIKELIEST_FAILURE:
  SOURCE_PRIME_OSCILLATION_OR_AMBIENT_ACTION_CROSSWALK_GAP.
```

**Memory entry:**

```yaml
iteration:
  target: H2A_4_1B_3C_0 center coefficient inverse-log floor
  status: PROGRESS
  failed_strategy: pointwise center nonvanishing as a rate
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_ENERGY_SOURCE_RATE
  invariant_learned: keep source scale inside the exact anchor/projection ratio
  forbidden_future_move: do not formalize the remaining rate as a new hypothesis
  next_decisive_test: combined Gamma source-envelope preflight
```
