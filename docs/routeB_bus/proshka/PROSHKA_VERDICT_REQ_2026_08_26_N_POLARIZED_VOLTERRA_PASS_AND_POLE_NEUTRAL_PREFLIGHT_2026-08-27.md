# STATUS: PROVED — POLARIZED VOLTERRA/HILBERT IDENTITY; CONSUMER RATE REMAINS OPEN

```yaml
PRIMARY: RATIFY_POLARIZED_VOLTERRA_HILBERT_IDENTITY_AND_RUN_LITERAL_POLE_NEUTRAL_CROSSWALK
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  BASE_REPORT_COMMIT: b9e7c5896f984929c5a2f0ccea400c3033ad2be2
  BASE_REPORT_PATH: docs/routeB_bus/LINUX_VOLTERRA_HILBERT_ARE_ONE_INSTRUMENT_GOAL058_2026-08-27.md
  BASE_REPORT_BLOB: 75daacb36d47729b09752437ed252bfcc37ed221
  ONE_MEASURE_CORRECTION_COMMIT: 0f4eb2117edcfec1fcef8a69ae82c4ecb5eee32d
  CENTER_NORMAL_FORM_LEAN_COMMIT: 2aaff3e765d75de4a7bafcee40876d2332aa68f7
  CENTER_NORMAL_FORM_LEAN_BLOB: aa7b9eed261ad86885b61e36dde17a87c0526656
  PRIMARY_PAPER: arXiv:2607.02828

ADJUDICATION:
  REPORTED_DISCRIMINATOR: PASS
  REPORTED_CODE: HILBERT_CURRENT_IS_THE_VOLTERRA_COEFFICIENT
  DECISION: PASS_RATIFIED_WITH_TWO_FORMULA_REPAIRS

  POLARIZATION_TO_ARBITRARY_COMPLEX_PAIR: PAPER_PROVED
  FINITE_COEFFICIENT_CLASS_MEMBERSHIP_GAP: RETRACTED_AS_TYPE_GAP
  UNIFORM_MODE_INDEX_CONTROL_FOR_X: OPEN
  CONSUMER_STRENGTH_RATE: OPEN
  TRACKING_CORRIDOR_THAWED: false

EXACT_REPAIRS:
  BAND_EDGE:
    reported: G(pi)=0
    correct: G(2*pi)=0
  KERNEL_SCOPE:
    reported_headline: G_is_the_odd_part_of_the_full_Volterra_kernel
    correct: G_is_the_odd_part_of_pi_times_the_constant_coefficient_part_K_alpha
    full_kernel_also_contains: beta_k_omega_exp_2piikomega
  MINIMAL_REGULARITY_TARGET:
    for_offdiagonal_test_G: sum_k_abs_nk_mul_abs_omega_k
    not_required_here: one_plus_abs_k_weight
  FULL_KERNEL_TARGET:
    requires_both:
      - weighted_control_of_omega_k
      - weighted_control_of_2_conj_xk_qk

POLE_NEUTRAL_ROUTE:
  CURRENT_SOURCE_ROW_MAY_BE_CHANGED: false
  ONLY_LEGAL_QUESTION: literal_selected_Ferrers_row_already_satisfies_the_pole_neutral_equation
  POST_HOC_PROJECTION_INTO_POLE_NEUTRAL_HYPERPLANE: forbidden
  EXACT_CONDITION: v0/beta^2 + sqrt(2)*sum_{k=1}^N v_k/(k^2+beta^2) = 0
  beta: L/(4*pi)
  PAYOFF_IF_TRUE: Q_pole_q_eq_zero_and_all_mixed_pole_pairings_vanish

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_LITERAL_POLE_NEUTRALITY_CROSSWALK_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: SELECTED_FERRERS_LITERAL_ROW_IS_EXACTLY_POLE_NEUTRAL
  HOLD: POLE_FUNCTIONAL_EXPLICIT_BUT_COFINAL_SIZE_UNCONTROLLED
  FAIL: SELECTED_FERRERS_LITERAL_ROW_NOT_POLE_NEUTRAL_AND_POST_HOC_PROJECTION_FORBIDDEN

LEAN_FORMALIZATION:
  POLARIZED_VOLTERRA_BRIDGE: SEMANTICALLY_ADMISSIBLE
  EXECUTION_NOW: DEFERRED_BY_CHEAPEST_DECISIVE_TEST_FIRST

CLOSES:
  - POLARIZATION_OF_THE_VOLTERRA_KERNEL_TO_A_MIXED_PAIR
  - FINITE_VECTOR_TO_TRIGONOMETRIC_POLYNOMIAL_TYPE_GAP
  - COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY_AS_AN_UNKNOWN_FUNCTION

OPENS: []

CARRIES_OPEN:
  - WEIGHTED_MODE_MOMENT_BOUND_FOR_GRAPH_RESOLVENT_VECTOR
  - LITERAL_CCM_DIAGONAL_SOURCE_ACTION_OR_FULL_MIXED_SOURCE_CALCULUS
  - COMPLETED_MEASURE_DISCREPANCY_RATE_AT_CONSUMER_STRENGTH
  - GROUND_TRACKING_COMPACT_RATE

CANDIDATE_REPRESENTATIONS:
  R1_LITERAL_POLE_NEUTRALITY:
    rank: PRIMARY
    kill_power: 10/10
    cost: 1/10
  R2_QPERP_FULL_MIXED_VOLTERRA_RESIDUAL:
    rank: RUNNER_UP
    kill_power: 9/10
    cost: 2/10
  R3_WEIGHTED_L2_CARLESON_CURRENT:
    rank: RESERVE
    kill_power: 8/10
    cost: 5/10

REGISTERED_PREDICTIONS:
  P_POLE_NEUTRAL_1:
    probability: 0.76
    prediction: literal_selected_Ferrers_row_fails_exact_pole_neutrality
  P_POLE_NEUTRAL_2:
    probability: 0.19
    prediction: pole_functional_is_nonzero_but_has_a_useful_cofinal_decay
  P_POLE_NEUTRAL_3:
    probability: 0.05
    prediction: exact_source_identity_places_the_literal_row_in_the_hyperplane
  P_VOLTHILBERT_LEAN_1:
    probability: 0.88
    prediction: finite_polarized_identity_compiles_after_mode_injectivity_and_orientation_are_explicit

PRIOR_PREDICTIONS:
  P_COMPLETED_SPECTRUM_1_0_70: CONFIRMED

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: FINITE_CELL
VERIFIER: PAPER
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| The mixed Volterra kernel exists for arbitrary complex finite vectors | Proved by finite expansion and termwise integration. | `[FINITE_CELL][PAPER]` |
| Its constant Fourier coefficient is the polarized Hilbert-current weight divided by `pi*i` | Proved, with the repository orientation `H_ij = (n_i-n_j)^(-1)`. | `[FINITE_CELL][PAPER]` |
| Reality or evenness is required for the polarized identity | Rejected.  Those hypotheses are required only for Groskin's quadratic real-even presentation, not for the finite bilinear expansion. | `[FINITE_CELL][PAPER]` |
| `x = C^{-1} kappa` fails to define a trigonometric polynomial | Rejected as a type objection.  On every finite CCM cell, every vector on the carrier defines a finite exponential polynomial. | `[FINITE_CELL][PAPER]` |
| The required cofinal regularity rate follows automatically | Not proved.  Quantitative mode-index control of `x` is still absent. | `[COFINAL_FAMILY][CONDITIONAL]` |
| The current Ferrers row may be projected into Groskin's pole-neutral hyperplane | Rejected without a same-family theorem. | `[COFINAL_FAMILY][PAPER]` |

## 1. Exact polarized identity

Let the finite mode labels `n_i` be distinct integers and define

\[
H_{ij}=\begin{cases}
0,&i=j,\\
(n_i-n_j)^{-1},&i\ne j.
\end{cases}
\]

For arbitrary complex vectors `x,q`, put

\[
T_{\bar x}(t)=\sum_i\overline{x_i}e^{2\pi i n_i t},
\qquad
T_q(t)=\sum_iq_i e^{2\pi i n_i t},
\]

and

\[
K_{x,q}(\omega)=\int_0^\omega
\bigl(T_{\bar x}(t)T_q(\omega-t)+T_q(t)T_{\bar x}(\omega-t)\bigr)\,dt.
\]

Finite expansion gives

\[
K_{x,q}(\omega)
=
\sum_i(\alpha_i+\delta_i\omega)e^{2\pi i n_i\omega},
\]

where

\[
\alpha_i=
\frac{1}{\pi i}
\left[
\overline{x_i}(Hq)_i+\overline{(Hx)_i}q_i
\right],
\qquad
\delta_i=2\overline{x_i}q_i.
\]

Thus, with

\[
\Omega_i(x,q)=
\overline{x_i}(Hq)_i+\overline{(Hx)_i}q_i,
\]

we have exactly

\[
\boxed{\alpha_i=\Omega_i(x,q)/(\pi i).}
\]

This is not an analogy with the Hilbert-current work.  It is the same coefficient.

The distinctness of the mode labels must be explicit in a Lean theorem.  Without it the exponential polynomial still exists, but the coefficient indexed by an individual carrier element is not uniquely recoverable after frequency collisions.

## 2. Relation to the current test function

The completed-spectrum report uses

\[
G(t)=\sum_i\Omega_i(x,q)\sin(n_it).
\]

Writing `t=2*pi*omega` and

\[
K_\alpha(\omega)=\sum_i\alpha_i e^{2\pi i n_i\omega},
\]

we obtain

\[
\boxed{
G(t)=\frac{\pi}{2}
\left(K_\alpha(\omega)-K_\alpha(-\omega)\right).
}
\]

Therefore `G` is the odd part of `pi*K_alpha`.

It is not literally the odd part of the entire `K_{x,q}` unless the linear-in-`omega` diagonal part is separately included and its reflection is tracked.  This is the first C04 repair.

The report also contains one harmless but exact typo:

```text
reported: G(pi)=0
correct:  G(2*pi)=0
```

because `S_t=diag(sin(n_i*t))` vanishes at `t=2*pi` for integer modes.  Nothing downstream uses the erroneous `pi` endpoint.

## 3. Minimal regularity ledger

For the off-diagonal spectral test itself,

\[
G'(t)=\sum_i n_i\Omega_i(x,q)\cos(n_it),
\]

hence

\[
\boxed{
\|G'\|_{L^\infty[0,2\pi]}
\le
\sum_i|n_i|\,|\Omega_i(x,q)|.
}
\]

Because `G(0)=0`, this derivative bound also controls `G` itself.  The minimal open quantity is therefore

\[
\boxed{
\sum_i|n_i|\,|\Omega_i(x_k(z),q_k)|,
}
\]

not an unspecified modulus of continuity and not necessarily the larger
`sum (1+|n_i|)|Omega_i|`.

If the route instead uses the full mixed Volterra kernel, then the derivative ledger also contains

\[
\delta_i=2\overline{x_i}q_i.
\]

The report's full-kernel derivative estimate is correct, but it cannot then declare only the `Omega` sum open.  One must choose one of two honest representations:

```text
A. off-diagonal G + separately carried diagonal source action;
B. full mixed source calculus + both alpha and delta coefficients.
```

Mixing A's open ledger with B's headline would lose the diagonal channel.

## 4. A stronger exact runner-up

Let

\[
r=(M-aI)q,
\qquad
\langle q,r\rangle=0,
\]

and let

\[
x_\perp=x-\langle q,x\rangle q.
\]

Then

\[
\langle x,r\rangle=\langle x_\perp,r\rangle,
\qquad
\langle x_\perp,q\rangle=0,
\]

so

\[
\langle x,(M-aI)q\rangle
=
\langle x_\perp,Mq\rangle.
\]

Once the mixed version of Groskin's finite source calculus is source-locked to the literal CCM matrix, this becomes one full Volterra-measure pairing.  The Rayleigh shift disappears exactly instead of being bounded.

This is representation `R2_QPERP_FULL_MIXED_VOLTERRA_RESIDUAL`.  It is not authorized now only because the pole-neutral test is cheaper.

## 5. Pole-neutral attack

Groskin's Corollary 2.7 gives, for the real even-sector coefficient vector `v`,

\[
\ell_{\beta}(v)
=
\frac{v_0}{\beta^2}
+
\sqrt2\sum_{k=1}^N\frac{v_k}{k^2+\beta^2},
\qquad
\beta=\frac{L}{4\pi}.
\]

The pole form is a positive rank-one square proportional to

\[
\ell_\beta(v)^2.
\]

Consequently,

\[
\ell_\beta(q)=0
\quad\Longrightarrow\quad
Q_{\rm pole}q=0
\quad\Longrightarrow\quad
\langle x,Q_{\rm pole}q\rangle=0
\]

for every left vector `x`.

This would remove the pole mass before any majorization and is therefore the cheapest decision-changing test now available.

But the legal question is only whether the literal source-locked selected Ferrers row already satisfies the equation.  Replacing it by a nearby vector in the large pole-neutral space changes the trial family that carries all existing Ferrers, Sturm, W5, normalization and trial-to-`Xi` suppliers.  That is a post-hoc object switch under C09 and a wrong-functional substitution under C10.

## 6. Exact next transaction

```text
TASK_ID:
  GOAL058_SELECTED_FERRERS_LITERAL_POLE_NEUTRALITY_CROSSWALK_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY
```

Required output:

```text
1. Write the exact map from the literal full CCM selected row q_k to
   Groskin's real even coordinates v_0,...,v_N, including sqrt(2), signs,
   mode order and normalization.

2. Prove or refute the exact identity

     ell_beta(v_k)=0

   for the same precommitted selected schedule.

3. Keep beta = log(m)/(4*pi) exact.

4. If exact zero is unavailable, derive the exact expression whose cofinal
   size would have to be bounded.  Do not call numerical smallness zero.

5. Do not alter q_k, project q_k, or select a new vector from P_N(c).

6. State what happens to the mixed pole pairing, not merely the quadratic
   value.
```

Discriminators:

```text
PASS:
  SELECTED_FERRERS_LITERAL_ROW_IS_EXACTLY_POLE_NEUTRAL

HOLD:
  POLE_FUNCTIONAL_EXPLICIT_BUT_COFINAL_SIZE_UNCONTROLLED

FAIL:
  SELECTED_FERRERS_LITERAL_ROW_NOT_POLE_NEUTRAL_AND_POST_HOC_PROJECTION_FORBIDDEN
```

No Lean, numerics, Aristotle or Codex execution is authorized by this verdict.

## STRONGEST ATTACK

The strongest objection is not to the Volterra algebra.  It is to the proposed use of pole-neutrality:

> The pole-neutral subspace is large, so why not choose a better trial vector in it?

Because the route's suppliers are source-locked to the selected Ferrers row.  A large alternative subspace is irrelevant unless an independent theorem transports all of the following:

```text
same trial-to-Xi limit;
same normalization;
same residual identity;
same W5 and projection-tail rates;
same real-zero ground consumer;
same cofinal schedule.
```

No such theorem exists.  The only cheap legal test is membership of the existing row.

The second objection is that smoothness of `G` may still be far too weak.  Correct.  An explicit derivative bound does not itself give cancellation of the completed signed measure.  A source discrepancy estimate at consumer strength remains necessary.  Failure of an absolute coefficient bound would kill only that sufficient bound, not the exact signed pairing.

## META CLOSEOUT

**What became smaller?**

```text
unknown consumer-side modulus of continuity
→ explicit finite weighted mode moment of the literal Hilbert current.
```

**What was killed?**

```text
complex polarization as a genuine mathematical gap;
finite coefficient-class membership as a type gap;
claim that G is the odd part of the full kernel without qualification;
G(pi)=0 endpoint statement.
```

**What must not be tried again?**

```text
another generic smoothness search;
post-hoc projection of the selected trial into a convenient hyperplane;
dropping the diagonal coefficient when using the full kernel;
treating a numerical near-zero pole value as exact pole-neutrality.
```

**Current smallest named gap:**

```text
SELECTED_FERRERS_LITERAL_POLE_NEUTRALITY_CROSSWALK
```

**Next cheapest decisive test:** the single exact pole-neutral functional on the literal selected row.

**Prediction fate:**

```text
P_COMPLETED_SPECTRUM_1 (0.70): CONFIRMED.
The identity exists; consumer-strength localization rate did not follow.
```

**Memory entry:**

```yaml
iteration:
  target: COMPLETED_SPECTRAL_TEST_FUNCTION_REGULARITY
  status: PROGRESS
  failed_strategy: generic_modulus_of_continuity_search
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_LITERAL_POLE_NEUTRALITY_CROSSWALK
  invariant_learned: preserve_literal_Ferrers_row_and_full_diagonal_channel
  forbidden_future_move: project_trial_into_pole_neutral_space_post_hoc
  next_decisive_test: exact_pole_neutral_functional_on_literal_row
```
