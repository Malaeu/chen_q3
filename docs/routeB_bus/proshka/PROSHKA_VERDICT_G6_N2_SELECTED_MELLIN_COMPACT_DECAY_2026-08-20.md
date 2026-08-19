# STATUS: OPEN — N2 IS NOT PROVABLE FROM THE CURRENT SELECTED-SHELL FIELDS; NO LEAN SOURCE WRITTEN

```yaml
PRIMARY: G6_N2_SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY_OPEN
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_HEAD: 95b8e6d22b53570caf29fbdd5ef02483ee6a4439
  N1_LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1PreAnchorLimitZeroModeAndSelectedShell.lean
  OLD_RESIDUAL_CROSSWALK: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
  OLD_L2_RECEIVER: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarGalerkinResidualDecay.lean
  OLD_PHYSICAL_RECEIVER: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarPhysicalFourierEnergyControl.lean

CLOSES:
  - N2_EXACT_THEOREM_SHAPE
  - N2_NORMALIZER_CANCELLATION_REPRESENTATION
  - N2_COUNTEREXAMPLE_AND_RATE_DISCRIMINATOR
OPENS: []

LEAN_SOURCE_WRITTEN: false
SOURCE_RECORD_WRITTEN: false
REASON_NO_SOURCE:
  - current selected shell does not supply the paper-port inhabitant
  - independent m-cofinality and N-cofinality do not imply physical bandwidth cofinality
  - Hilbert-norm residual decay does not imply compact-open Mellin decay
  - a free compact-rate premise would merely restate the target and violate W9

DEPENDENCY_GATE:
  REQUIRED_FIRST:
    - SELECTED_PROLATE_PREANCHOR_DATA_INHABITANT
    - CCM_LEMMA_7_3_PREANCHOR_PORT_INHABITANT
  N2_EXECUTION_BEFORE_DEPENDENCY: FORBIDDEN

TARGET:
  NAME: SelectedNormalizedGalerkinMellinCompactDecay
  SCOPE: COFINAL_FAMILY
  REQUIRED_OUTPUT: for every compact K in centeredCriticalStrip, the centered finite-minus-anchored-main error tends uniformly to zero on K
  FREE_COMPACT_RATE_ARGUMENT_ALLOWED: false

REPRESENTATION_SHIFT:
  OLD_FORM:
    expression: bounded selectedTrialNormalizer times Hilbert residual tending to zero
    defect: loses the exact central-anchor cancellation and still does not control Mellin evaluation growth
  NEW_FORM:
    expression: sourceScale-weighted unnormalized projection residual in compact Mellin topology
    exact_budget: abs(sourceScale_k) * kernelEnvelope_K(m_k) * norm(P_k g_k - g_k) -> 0

NORMALIZER_CANCELLATION:
  finite_centered: centeredXi(0) / raw_k(0) * raw_k(z)
  anchored_main: centeredXi(0) / Gwin_k(0) * Gwin_k(z)
  exact_zero_mode: raw_k(0) = sTrial_k * Gwin_k(0)
  consequence: finite_centered - anchored_main = centeredXi(0) / Gwin_k(0) * Mellin(P_k g_k - g_k)
  SelectedTrialNormalizerBounded_needed_for_N2: false

COMPACT_KERNEL_ENVELOPE:
  sigma_K: sup_{z in K} abs(Im z)
  lambda_k: sqrt(m_k)
  L_k: log(m_k)
  bound: sup_{z in K} norm(u^(-i*z))_L2(du/u,[lambda^-1,lambda]) <= sqrt(L_k) * lambda_k^sigma_K
  harmless_absolute_constant: allowed

MINIMAL_MISSING_IDENTITY:
  name: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
  formula: for every sigma with 0 <= sigma < 1/2,
           abs(sourceScale_k) * sqrt(log(m_k)) * m_k^(sigma/2)
           * norm(P_(m_k,N_k) g_k - g_k) -> 0
  must_be_derived_from:
    - exact sourceScale formula from CCM Lemma 7.3
    - literal prolate/Ferrers source coefficient decay or Sobolev energy
    - one precommitted joint schedule (m_k,N_k)
  may_not_be_assumed_as_new_field: true

INTERNAL_FLOORS:
  N2_0_SELECTED_SHELL_RESIDUAL_OBJECT_LOCK:
    character: DEFINITIONAL_PORT
    output: literal projection-minus-full residual and its Mellin coordinate on SelectedProlateCofinalSourceData
    new_input: false
  N2_1_ANCHORED_MAIN_LIMIT:
    character: TOPOLOGICAL_ASSEMBLY
    output: centeredXi(0)/muntz_k(0) * muntz_k(z) tends locally uniformly to centeredXi
    input: actual N1 limit inhabitant
    new_input: false
  N2_2_CENTER_NORMALIZER_CANCELLATION:
    character: EXACT_IDENTITY
    output: finite centered error equals centeredXi(0)/Gwin_k(0) times the unnormalized projection-residual Mellin coordinate
    new_input: false
  N2_3_COMPACT_MELLIN_KERNEL_ENVELOPE:
    character: EXPLICIT_ANALYTIC_LEMMA
    output: Cauchy-Schwarz envelope sqrt(L_k)*lambda_k^sigma_K
    new_input: false
  N2_4_SOURCE_FOURIER_TAIL_BOUND:
    character: SOURCE_ANALYTIC_FLOOR
    output: norm(P_k g_k-g_k) bounded by an explicit weighted coefficient tail
    new_input: false
  N2_5_SCALE_ENERGY_SCHEDULE_BUDGET:
    character: MAIN_ANALYTIC_WALL
    output: sourceScale * compact envelope * source projection tail tends to zero
    new_input: false
  N2_6_COMPACT_DECAY_ASSEMBLY:
    character: ASSEMBLY
    output: N2 target
    new_input: false

CURRENT_REPO_INPUT_AUDIT:
  SelectedProjectionTailDecay:
    status: DEFINITION_ONLY_WITH_CONDITIONAL_RECEIVERS
    sufficient_for_N2: false
  SelectedTrialNormalizerBounded:
    status: DEFINITION_ONLY
    necessary_after_exact_anchor_cancellation: false
  SelectedPhysicalFourierEnergyControl:
    status: DEFINITION_ONLY
    sufficient_with_bandwidth_cofinality_alone: false
  SelectedPhysicalBandwidthCofinal:
    status: DEFINITION_ONLY
    follows_from_independent_m_and_N_cofinality: false
  order_one_tail_receiver:
    status: LEAN_PROVED_CONDITIONAL
    role: one internal estimate, not N2 closure

KILL_PLANTS:
  P_N2_1_INDEPENDENT_COFINALITY:
    schedule: log(m_k)=k^2, N_k=k
    result: m_k and N_k both tend to infinity but physical bandwidth 2*pi*(N_k+1)/log(m_k) tends to zero
    kills: independent cofinality implies projection resolution
  P_N2_2_HILBERT_NORM_NOT_COMPACT_MELLIN:
    object: first omitted logarithmic Fourier mode, scaled so its Hilbert norm tends to zero
    evaluation: choose the matching physical frequency z_k, which remains in a fixed compact when bandwidth fails to diverge
    result: compact Mellin supremum stays bounded away from zero
    kills: L2 residual decay implies compact-open Mellin decay
  P_N2_3_BANDWIDTH_WITHOUT_RATE:
    data: bandwidth tends to infinity arbitrarily slowly while sourceScale*sqrt(L)*lambda^sigma grows faster
    result: projection norm can tend to zero while the weighted compact budget does not
    kills: bandwidth cofinality plus unweighted tail decay is sufficient

CANDIDATE_REPRESENTATIONS:
  R1_WEIGHTED_FOURIER_TAIL_WITH_EXPLICIT_SCHEDULE:
    rank: PRIMARY
    kill_power: 10/10
    cost: 7/10
    route: derive order-r source energy and choose/prove one precommitted schedule making the full weighted budget vanish
  R2_COMPLEX_LOG_STRIP_COEFFICIENT_DECAY:
    rank: RUNNER_UP
    kill_power: 9/10
    cost: 8/10
    route: prove a uniform complex-log-strip extension of the source trial, obtain exponential Fourier coefficient decay, then close the same weighted budget
  R3_CLUSTERWISE_SUBSEQUENCE:
    rank: REJECTED
    kill_power: 5/10
    cost: 6/10
    reason: selects a new subsequence after seeing decay and violates the one-schedule precommit

DISCRIMINATOR:
  name: STRICT_WEIGHTED_MELLIN_TAIL_RATE
  pass: explicit upper bound tends to zero for every fixed sigma<1/2 on the precommitted schedule
  zero_consistent_or_bounded_only: INCONCLUSIVE

COUNTER_EFFECT:
  TOP_LEVEL_G6_WALLS_AFTER_ACTUAL_N0_N1_SUPPLY:
    - N2_SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
    - N3_SAME_FAMILY_LIMIT_ASSEMBLY
    - N4_SLOT_S2_ASSEMBLY
  CURRENT_UNCONDITIONAL_COUNT_CHANGE: 0

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C12_BOUNDED_POTENTIAL_EXCLUSION

NEXT_LOAD_BEARING_GAP:
  SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE

SCOPE: COFINAL_FAMILY
VERIFIER: CONDITIONAL
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
```

## ROUTE MAP

The next source is not ready.

The existing tree proves several exact identities for the old all-index `ProlateCanonicalSourceData` route:

```text
literal normalized projection-minus-full residual;
Mellin-coordinate linearity;
exact raw-minus-scaled-Gwin crosswalk;
conditional Hilbert-norm tail receiver;
conditional order-one physical Fourier-energy receiver.
```

None of those theorems supplies compact-open decay.  The new selected-only shell also has a different type, so the old residual definitions cannot be reused by definitional equality without a selected-shell port.

More importantly, the desired theorem is false from the current structure fields.  `mCofinal` and `nCofinal` only say that the two coordinates diverge separately.  They do not imply that the first omitted physical frequency

\[
B_k=\frac{2\pi(N_k+1)}{\log m_k}
\]

diverges.  The precommitted schedule

\[
\log m_k=k^2,\qquad N_k=k
\]

is a direct counterexample: both coordinates are cofinal while `B_k -> 0`.

Even Hilbert-norm residual decay is not enough.  Mellin evaluation on a compact has a carrier-dependent norm.  If

\[
\sigma_K=\sup_{z\in K}|\operatorname{Im}z|,
\]

then Cauchy-Schwarz gives, up to one absolute constant,

\[
\sup_{z\in K}|M(r_k)(z)|
\le
\sqrt{\log m_k}\,m_k^{\sigma_K/2}\,\|r_k\|.
\]

The factor on the right can grow.  Therefore `||r_k|| -> 0` cannot occupy the compact-open quantifier.

## The exact normalization repair

The old two-premise Hilbert receiver highlights `SelectedTrialNormalizerBounded`.  That condition is useful for uncentered normalized residuals, but it is not the sharp N2 consumer.

Let

```text
raw_k(z)  = transform of s_k P_k g_k;
G_k(z)    = full pre-anchor Gwin transform;
raw_k(0)  = s_k G_k(0).
```

The centered finite function is

\[
F_k(z)=\frac{\Xi(0)}{raw_k(0)}raw_k(z).
\]

The exactly anchored continuum main term is

\[
A_k(z)=\frac{\Xi(0)}{G_k(0)}G_k(z).
\]

Hence

\[
F_k(z)-A_k(z)
=
\frac{\Xi(0)}{G_k(0)}
M(P_k g_k-g_k)(z).
\]

The finite projection normalizer `s_k` cancels exactly.  Consequently a separate bound for `s_k` must not be exported as an N2 premise.

The N1 paper scale gives a cleaner equivalent budget.  If `a_k G_k -> Xi` and `a_k G_k(0) -> Xi(0) != 0`, then

\[
\frac{\Xi(0)}{a_kG_k(0)}\to1.
\]

Thus N2 reduces to the source-scale weighted residual:

\[
\sup_{z\in K}|a_k M(P_k g_k-g_k)(z)|\to0.
\]

This is the right source-facing object.  It removes one fake normalizer wall but leaves the real scale-tail wall exposed.

## Internal floor plan

### N2.0 — selected-shell residual object lock

Define the literal `P_k g_k-g_k` residual and Mellin coordinate using `SelectedProlateCofinalSourceData.index`, `.pair`, `.eStar_memLp` and `.trialNonzero`.  No old all-index record and no surrogate scalar defect.

### N2.1 — anchored main-term limit

From the actual N1 inhabitant prove that

\[
\frac{\Xi(0)}{M_k(0)}M_k(z)\to\Xi(z)
\]

locally uniformly, where `M_k = D.muntzApproximation k`.  This is a field/topology assembly because `M_k(0)->Xi(0)!=0`.

### N2.2 — exact center-normalizer cancellation

Prove the displayed finite-minus-anchored identity.  This is an exact algebraic theorem and is the first useful Lean floor once N0/N1 inhabitants exist.

### N2.3 — compact Mellin kernel envelope

Prove the explicit carrier bound uniformly on every compact.  This names the evaluation amplification instead of hiding it behind continuity.

### N2.4 — source Fourier tail

Use the exact logarithmic Fourier basis to estimate the projection tail from weighted coefficient energy.  The current order-one theorem is a valid starting point but not yet the final budget.

### N2.5 — scale, energy and schedule budget

This is the substantive wall.  It must derive

\[
|a_k|\sqrt{\log m_k}m_k^{\sigma/2}
\|P_kg_k-g_k\|\to0
\]

for every `sigma<1/2`, from an explicit source scale, source regularity and one frozen schedule.  The theorem may not take this convergence as a field.

### N2.6 — compact decay assembly

Combine N2.1–N2.5 and close the top-level N2 input.  Only after this may N3 and N4 be written.

## FINAL PROPOSAL

Do not write another conditional receiver.

First close the two actual N0/N1 inhabitants identified by the recount verdict.  Then perform a read-only source preflight for the primary representation:

```text
1. extract the exact CCM Lemma-7.3 sourceScale;
2. choose or recover the already precommitted joint schedule;
3. derive an explicit Fourier/Sobolev energy bound for the literal prolate trial;
4. test the complete exponent ledger
     sourceScale * sqrt(log m) * m^(sigma/2) * projectionTail;
5. write Lean only when the ledger tends to zero without a new premise.
```

If no source estimate can beat the Mellin amplification on one fixed schedule, kill this representation with

```text
G6_N2_SOURCE_SCALED_MELLIN_TAIL_RATE_FATAL.
```

Do not hide the failure by selecting a faster subsequence afterwards.

## STRONGEST ATTACK

A reviewer can object that compactness of `K` makes Mellin evaluation uniformly bounded.

It is uniformly bounded for each fixed carrier, but the carrier itself changes with `k`.  The evaluation norm grows like `sqrt(log m_k) * m_k^(sigma_K/2)`.  Compactness in `z` does not provide uniformity in the moving window.  This is exactly why a raw `L² -> compact-open` bridge is false.

A second objection is that `SelectedPhysicalBandwidthCofinal` plus bounded physical energy already proves the result.  It proves only unweighted Hilbert tail decay.  The bandwidth can diverge too slowly compared with the source scale and Mellin amplification.  A quantitative rate, not mere cofinality, is load-bearing.

## CODEX DIRECTIVE

```text
NO LEAN EDIT AUTHORIZED.

READ-ONLY PREFLIGHT:
  target = SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE

Return exactly:
  - exact CCM Lemma-7.3 sourceScale formula;
  - exact current selected schedule formula;
  - best source-locked order-r physical Fourier energy estimate;
  - exponent ledger for every sigma < 1/2;
  - one of:
      N2_RATE_SOURCE_READY
      N2_SCHEDULE_TOO_SLOW
      N2_SOURCE_ENERGY_BOUND_MISSING
      N2_SOURCE_SCALE_NORMALIZATION_MISMATCH

Forbidden:
  - add a compactRate field;
  - assume SelectedPhysicalFourierEnergyControl;
  - assume SelectedPhysicalBandwidthCofinal;
  - assume SelectedTrialNormalizerBounded;
  - select a post-hoc subsequence;
  - write N3 or N4 first.
```

## META CLOSEOUT

**What became smaller?**  N2 is reduced from vague compact decay to one explicit weighted source-tail rate.  The finite projection normalizer drops out exactly.

**What was killed?**  Independent cofinality as a schedule theorem, unweighted `L²` decay as compact-open decay, and a free compact-rate premise.

**What must not be tried again?**  Another receiver whose strongest assumption is the desired weighted convergence under a new name.

**Current smallest named gap:** `SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE`.

**Next cheapest decisive test:** extract the exact sourceScale and schedule, then compare their exponents with the first available source Fourier-tail bound.

**Prior predictions:** the prediction that N2 is the first genuine analytic wall is confirmed.  The earlier suggestion that bounded normalizer is a necessary N2 supplier is refuted by the exact anchor cancellation representation.

```yaml
iteration:
  target: G6_N2_SELECTED_NORMALIZED_GALERKIN_MELLIN_COMPACT_DECAY
  status: OPEN
  failed_strategy: unweighted_Hilbert_tail_plus_bounded_normalizer
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SOURCE_SCALED_MELLIN_PROJECTION_TAIL_RATE
  invariant_learned: moving-window Mellin evaluation amplification must be paid on the same schedule
  forbidden_future_move: export the weighted compact rate as a premise
  next_decisive_test: sourceScale_schedule_energy_exponent_ledger
```
