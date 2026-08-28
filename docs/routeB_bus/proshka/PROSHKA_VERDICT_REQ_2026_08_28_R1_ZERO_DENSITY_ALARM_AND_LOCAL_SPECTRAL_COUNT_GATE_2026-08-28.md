# STATUS: OPEN — ZERO-DENSITY ALARM RATIFIED; SINE-LATTICE KILL REJECTED; LOCAL SPECTRAL COUNT IS THE DECISIVE R1 GATE

```yaml
PRIMARY: RATIFY_ZERO_DENSITY_ALARM_AND_INSERT_LITERAL_LOCAL_SPECTRAL_COUNT_GATE
PRIMARY_COUNT: 1

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 7c5f2a50353032986c0c10f3e08915dc0992ea99
  REPORT_PATH: docs/routeB_bus/LINUX_ZERO_DENSITY_SELF_TEST_GOAL058_2026-08-28.md
  PRIOR_VERDICT: 4bbd4e0b4ab5eeeaa17dea080ba751ff6022c010

ADJUDICATION:
  COS_NZ_DENSE_ZERO_GRID_ARGUMENT: PAPER_PASS
  KILL_IS_ABOUT_ZERO_DENSITY_NOT_GAUGE: RATIFIED
  GENERIC_R1_A_EXACT: FATAL_CONFIRMED

  CENTERED_CRITICAL_STRIP_VARIABLE_MATCH: CLOSED
  centered_strip_coordinate: literal_P59_z
  hidden_L_rescaling_in_roof_compact: false

  SINE_LATTICE_FORCES_DENSE_LITERAL_ZEROS: REJECTED
  LITERAL_TRANSFORM_INTERLACES_LATTICE: NOT_PROVED
  reason: >-
    Included lattice points are removable evaluation points, not automatic
    zeros.  Interlacing requires residue signs or a separate spectral theorem.

  EXTERIOR_LATTICE_ZERO_ESCAPE: PAPER_PASS
  selected_schedule: m_k=N_k=k+2
  L_k: log(m_k)
  nearest_exterior_zero_scale: 2*pi*(N_k+1)/L_k
  tends_to_infinity: true

  INCLUDED_LATTICE_ZERO_CRITERION: PAPER_PASS
  statement: >-
    At the included pole labelled j, the transform value is a nonzero explicit
    scalar times the corresponding coefficient xi_j; the point is a zero iff
    that coefficient is zero.

  OFF_LATTICE_ZERO_OBJECT: FINITE_LAGRANGE_OR_FINITE_PERTURBED_SPECTRUM
  OFF_LATTICE_LOCAL_ZERO_COUNT: OPEN

  MODEL_GAUSSIAN_HERMITE_ZERO_COUNT: DIAGNOSTIC_ONLY
  LITERAL_SELECTED_GROUND_ZERO_DENSITY: UNRESOLVED

R1_STATUS:
  R1_0_LITERAL_GROUND_FAMILY_OBJECT_LOCK: CLOSED
  R1_B_COMPACT_TIGHTNESS_IF_CLUSTER_EXISTS: CLOSED
  R1_A_GENERIC_GLOBAL_GAUGE: FATAL
  R1_LITERAL_FAMILY: HOLD_BEHIND_ZERO_COUNT_GATE
  R1_ROUTE_FATAL: false

PRECEDENCE:
  PRIOR_NEXT_TASK:
    GOAL058_R1_ANCHORED_LOG_DERIVATIVE_HERGLOTZ_PREFLIGHT
  status: SUPERSEDED_UNTIL_ZERO_COUNT_GATE
  reason: >-
    The representing measure of the logarithmic derivative is the zero-counting
    measure.  If its local mass diverges, the log-derivative representation
    cannot rescue a nonzero compact-open cluster.

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_R1_LITERAL_GROUND_LOCAL_SPECTRAL_COUNT_PREFLIGHT
  MODE: PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  statement: >-
    For every compact real interval I, the number, counted with multiplicity, of
    finite perturbed-scaling eigenvalues of the literal selected ground cell in
    I is eventually bounded independently of k.

DISCRIMINATOR:
  PASS:
    code: R1_LITERAL_GROUND_LOCAL_SPECTRAL_COUNT_TIGHT
    requirement: >-
      Exact source decomposition plus a source theorem gives eventual uniform
      local finiteness of the finite perturbed spectrum on every compact.
  HOLD:
    code: R1_ZERO_DIVISOR_EXACT_BUT_LOCAL_FINITE_SPECTRUM_UNCONTROLLED
    requirement: >-
      Exterior lattice zeros are proved to escape and the remaining zeros are
      exactly identified with a finite spectrum, but no cofinal local count
      bound or divergence theorem exists.
  FAIL:
    code: R1_LITERAL_GROUND_ZERO_COUNT_DIVERGES_ON_FIXED_COMPACT
    requirement: >-
      A source-locked theorem proves that on one fixed compact the literal
      ground zero count is unbounded in a way forcing every compact-open cluster
      to vanish identically.  Numerics or a model row do not qualify.

CANDIDATE_REPRESENTATIONS:
  R1:
    name: FINITE_GROUND_SPECTRAL_COUNTING_MEASURE
    object: nu_k=sum_{t in Spec(Dprime_k)} multiplicity(t)*delta_t
    kill_power: 10/10
    proof_cost: 2/10
  R2:
    name: RELATIVE_RANK_ONE_PERTURBATION_DETERMINANT
    object: >-
      det(Dprime_k-s)/det(D_k-s)=-s*sum_j xi_{k,j}/(j-s), with the free lattice
      factor removed exactly and zeros/poles retained as a spectral-shift object.
    kill_power: 9/10
    proof_cost: 4/10

STOP_RULE:
  - do_not_count_the_sine_lattice_as_zeros_inside_the_finite_carrier
  - do_not_infer_interlacing_without_residue_sign_or_a_named_spectral_theorem
  - do_not_promote_model_row_numerics_to_the_literal_ground_family
  - do_not_run_Herglotz_or_Montel_wrappers_before_local_spectral_count_is_classified
  - one_HOLD_returns_to_judge_for_R1_closeout_or_owner_rerank

REGISTERED_PREDICTIONS:
  P_R1_ZERODENSITY_1:
    probability: 0.98
    prediction: exterior_lattice_zeros_escape_every_fixed_compact_on_the_selected_schedule
  P_R1_ZERODENSITY_2:
    probability: 0.76
    prediction: no_existing_source_theorem_supplies_uniform_local_count_for_the_finite_perturbed_spectrum
  P_R1_ZERODENSITY_3:
    probability: 0.42
    prediction: literal_ground_zero_counts_on_low_fixed_intervals_remain_bounded_and_track_the_target_zero_count

PRIOR_PREDICTION_FATE:
  P_R1_LOGDERIV_1_0_66: SUSPENDED_BEHIND_ZERO_COUNT_GATE
  P_R1_HERGLOTZ_1_0_34: SUSPENDED_BEHIND_ZERO_COUNT_GATE
  P_R1_IDENTIFICATION_2_0_27: NOT_TESTED
  P_R1_CLOSEOUT_1_0_61: NOT_TESTED

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: MINIMAL_LEMMA
ROUTE_SCORE: 5

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

| Claim | Verdict | Tags |
|---|---|---|
| Dense zeros kill every zero-free gauge | Ratified.  The obstruction is the preserved zero divisor, not the choice of gauge. | `[ABSTRACT][PAPER]` |
| The roof compact uses a hidden rescaled variable | Rejected.  `centeredCriticalStrip` is the literal P59 `z`-coordinate with `|Im z|<1/2`. | `[ABSTRACT][LEAN]` |
| Sine spacing `2*pi/L` by itself forces dense zeros | Rejected.  Inside the carrier the sine zeros are removable points and are cancelled whenever the corresponding coefficient is nonzero. | `[FINITE_CELL][PAPER]` |
| Exterior sine zeros threaten fixed compacts | Rejected on the selected schedule.  Their nearest absolute location grows as `2*pi*(N+1)/L`, and `N=m=k+2`, `L=log m`. | `[COFINAL_FAMILY][PAPER]` |
| Remaining finite zeros | Exactly the roots of the source Lagrange polynomial, equivalently the finite self-adjoint perturbed-scaling spectrum after the source hypotheses. | `[FINITE_CELL][LEAN]` |
| Uniform local count of those finite zeros | Open.  Neither real-rootedness nor exact factorization supplies it. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. The report found the correct obstruction class

The reverse-Hurwitz argument is exact.  If zeros of a family become dense on a
fixed real interval, then no zero-free multiplier can produce both a locally
bounded family and a compact-tight nonzero cluster.  Every locally uniform
cluster would vanish on that interval and hence vanish identically.

Thus the generic `R1_A_EXACT` class is dead for a stronger reason than vertical
growth: zero-free gauges preserve the zero divisor.

## 2. The literal P59 sine lattice does not yet instantiate the kill

For a finite carrier `{-N,...,N}`, the P59 transform is

\[
T_{L,N,\xi}(z)=L^{-1/2}\,2\sin(Lz/2)
 \sum_{j=-N}^{N}\frac{\xi_j}{z-2\pi j/L}
\]

off the finite lattice, with canonical removable values on the lattice.

At an included node `z=2*pi*j/L`, every summand except the `j`-summand vanishes,
and the removable value is

\[
T_{L,N,\xi}(2\pi j/L)=\sqrt L\,(-1)^j\xi_j
\]

up to the already source-locked pole-label sign convention.  Therefore an
included lattice point is a zero exactly when the matching coefficient is zero.
It is not an automatic sine zero.

For `|j|>N` there is no compensating pole and the lattice point remains a zero.
But the selected schedule is

\[
m_k=N_k=k+2,\qquad L_k=\log m_k.
\]

Hence the nearest exterior lattice zero has magnitude

\[
\frac{2\pi(N_k+1)}{L_k}\longrightarrow\infty.
\]

So the free lattice contributes no zeros to any fixed compact for all sufficiently
large `k`.

This is the exact **C04** distinction: lattice locations and transform zeros use
the same coordinates but obey different laws after removable extension.

## 3. The true question is the finite perturbed spectrum

Away from the finite lattice, a transform zero is a zero of the finite Cauchy
sum and therefore a zero of the source Lagrange polynomial in the coordinate

\[
s=-Lz/(2\pi).
\]

The source real-zero engine identifies this polynomial with the nonzero
characteristic factor of the rank-one corrected scaling operator.  The full
transform zero divisor is therefore the union of:

1. the finite perturbed-scaling spectrum;
2. any included lattice nodes whose coefficient vanishes;
3. the exterior free lattice `|j|>N`.

The third set escapes.  The second has no density theorem.  The first is the
load-bearing object.

The source paper proves only realness and the exact spectral identification; its
numerical section reports approximation of low zeta zeros.  It does not prove a
uniform local eigenvalue-count theorem along the selected cofinal schedule.

The model Gaussian-Hermite count in `7c5f2a50` is therefore a valuable alarm and
nothing more.  Replacing the literal ground eigenvector by the model row here
would be a direct **C10** surrogate error.

## 4. Why the logarithmic-derivative preflight must wait

The logarithmic derivative of an entire real-rooted function is the Cauchy
transform of its zero-counting measure plus gauge terms.  Anchoring removes the
linear gauge, but it does not remove mass from the zero measure.

Therefore the first question for any Herglotz or de Branges compactness theorem
is exactly:

\[
\sup_k \nu_k(I)<\infty
\]

for every compact interval `I`, where `nu_k` is the finite perturbed spectral
counting measure.  Running the Herglotz audit before this classification would
hide the same obstruction in a measure hypothesis.

## STRONGEST ATTACK

The strongest objection to this verdict is:

> The finite self-adjoint operator has only `2N` eigenvalues, so its count on a
> fixed interval is automatically finite.

Finite per cell is irrelevant.  R1 requires a cofinal family.  The needed claim
is uniform in `k`; the bound `2N_k` diverges and occupies no cofinal quantifier.

The opposite overclaim is:

> A rank-one perturbation of a diagonal operator interlaces the diagonal
> lattice, so density follows automatically.

Not here.  The corrected scaling operator is self-adjoint in the quotient metric
induced by the shifted Weil form, not as a standard Hermitian rank-one
perturbation of the diagonal matrix in the Euclidean metric.  No Cauchy
interlacing theorem may be imported without an exact metric/intertwiner
crosswalk.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION AUTHORIZED.

TASK_ID:
  GOAL058_R1_LITERAL_GROUND_LOCAL_SPECTRAL_COUNT_PREFLIGHT

MODE:
  PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY

DELIVER EXACTLY:

1. Exact zero-divisor decomposition of the literal selected ground transform:
   finite perturbed spectrum, included zero coefficients, exterior lattice.
2. Exact proof that exterior lattice zeros escape every fixed compact on
   `m=N=k+2`, `L=log m`.
3. Exact spectral-counting measure for the finite rank-one corrected operator.
4. Shelf and primary-source audit for:
   local eigenvalue-count bounds;
   residue-sign/interlacing theorems;
   spectral-shift or relative-determinant compactness;
   convergence of finite spectral measures.
5. Classification PASS/HOLD/FAIL under the discriminator above.
6. If HOLD, compare the two precommitted representations R1 and R2 by
   kill-power and proof cost; do not open another wrapper.

MANDATORY PLANTS:

P1_INCLUDED_LATTICE_NOT_AUTOMATIC_ZERO:
  one nonzero coefficient at the matching mode makes the removable lattice value
  nonzero.

P2_EXTERIOR_LATTICE_ESCAPE:
  use the literal selected schedule, not an arbitrary `N(L)`.

P3_STANDARD_INTERLACING_METRIC_MISMATCH:
  a matrix self-adjoint in a changing positive metric is not automatically a
  standard Hermitian rank-one perturbation of the diagonal lattice.

P4_MODEL_ROW_NOT_GROUND_ROW:
  the Gaussian-Hermite diagnostic does not occupy the literal eigenvector
  quantifier.

FORBIDDEN:
  Lean edits;
  numerics;
  ground-to-trial tracking;
  graph resolvents;
  another zero-free gauge search;
  an interlacing claim without a named source theorem and exact metric adapter.
```

## META CLOSEOUT

**What became smaller?**

The vague zero-density alarm is reduced to one object:

```text
finite perturbed-scaling spectral counting measure on fixed compact intervals.
```

**What was killed?**

- the generic global-gauge theorem;
- the inference `sine spacing -> literal zero spacing`;
- exterior free-lattice zeros as a fixed-compact obstruction.

**What must not be tried again?**

Do not count removable lattice points as zeros.  Do not infer interlacing from
real-rootedness.  Do not substitute a model packet for the literal ground row.

**Current smallest named gap:**

```text
SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS.
```

**Next cheapest decisive test:**

Audit whether the finite rank-one corrected spectrum has a source-locked local
count or spectral-measure convergence theorem.  If absent, R1 returns HOLD rather
than spawning another compactness wrapper.

**Memory entry:**

```yaml
iteration:
  target: literal_R1_zero_density
  status: OPEN
  failed_strategy: sine_lattice_as_zero_set
  cognitive_operator_used: MINIMAL_LEMMA
  new_gap_name: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  invariant_learned: removable_extension_changes_lattice_zero_geometry
  forbidden_future_move: model_row_or_standard_interlacing_as_literal_source_fact
  next_decisive_test: local_finite_spectral_count_source_audit
```
