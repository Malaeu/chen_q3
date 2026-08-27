# STATUS: OPEN — CORRECTION 12 RATIFIED; THE Q-PROJECTED CONSUMER RECOMBINES AS ONE ORIENTED FULL-VOLTERRA FUNCTIONAL

```yaml
PRIMARY: HOLD_QPROJECTED_DIAGONAL_ACCEPT_ORIENTED_FULL_VOLTERRA_REPAIR
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-26-N
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean

  CORRECTION_12_COMMIT: 5ada7019881f83d067cafc4f0453a6d68f1efb48
  CORRECTION_12_PATH: docs/routeB_bus/LINUX_CORRECTION_12_QPROJECTION_AND_A_TESTED_DEAD_END_GOAL058_2026-08-28.md
  CORRECTION_12_GIT_BLOB: 1922fc4db7c3d7fdbca41be151dd20d4e231527a

  REPORT_COMMIT: e89acb7ab029f062808e38eb59c6e2e28a06fc71
  REPORT_PATH: docs/routeB_bus/LINUX_QPROJECTED_DIAGONAL_PREFLIGHT_GOAL058_2026-08-28.md
  REPORT_GIT_BLOB: b77530086bb37482cf1473d6e57e77524ec5f371
  REPORT_LINES: 140

  PARENT_VERDICT_COMMIT: 87e5ea2fec935d70c9f0aab0c515fd25e8e0c06e
  HEAD_READ: 190b268fce2380592e323a4f3304e82b56037b1c
  REPORT_IS_ANCESTOR_OF_HEAD: true
  INTERVENING_COMMIT_IS_MATHEMATICALLY_UNRELATED: true

MODE:
  REPORT_MODE: PAPER_AND_SOURCE_READ_ONLY_PLUS_DECLARED_DIAGNOSTIC_NUMERIC_TEST
  JUDGE_RERAN_LEAN: false
  JUDGE_RERAN_NUMERICS: false
  NUMERICS_OCCUPY_QUANTIFIER: false

ADJUDICATION:
  CORRECTION_12: RATIFIED
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: QPROJECTED_DIAGONAL_IDENTITY_WITHOUT_SOURCE_RATE
  DECISION: HOLD_RATIFIED_WITH_MINIMAL_ACTION_AND_SOURCE_ORIENTATION_REPAIRS

  QPROJECTED_ZERO_MASS_WEIGHT: PAPER_PASS
  DIAGONAL_COSINE_TEST_SECOND_ORDER_ENDPOINT_ZERO: PAPER_PASS
  TEST_LEVEL_EVEN_ODD_SPLIT: PAPER_PASS
  RAW_UNREFLECTED_ONE_WEIGHT_COSINE_TRANSFORM: KILLED_EXACTLY
  FULL_SOURCE_RATE: OPEN

  REPORT_NEXT_GAP_FOLDED_VARIABLE_DIAGONAL_UNIFICATION:
    status: SUPERSEDED_AS_NONMINIMAL
    reason: >-
      The full Volterra test is not periodic. Folding W02 forgets its winding
      number and necessarily creates a first-moment cocycle. The cheaper exact
      representation leaves W02 unfolded and reflects only Arch+Prime.

EXACT_QPROJECTED_OBJECT:
  q_normalized: true
  P: "q q*"
  Q: "I-P"
  x: "C^(-1) kappa"
  y: "Qx = C^(-1)Qkappa"
  residual: "r=(M-aI)q"
  identities:
    - "<x,r>=<y,r>"
    - "<y,(M-aI)q>=<y,Mq>"
    - "<y,q>=0"
    - "every scalar diagonal cI is invisible to the consumer"

DIAGONAL_ACTION_REPAIR:
  D: "diag(M_nn)"
  exact_identity: "D_perp=<y,Dq>=<y,QDq>"
  minimal_bound: "|D_perp| <= ||y||_2 * ||Q D q||_2"
  exact_variance: >-
    ||Q D q||_2^2 = sum_n |M_nn|^2 |q_n|^2
    - |sum_n M_nn |q_n|^2|^2.
  report_raw_weighted_norm: VALID_BUT_NONMINIMAL_UPPER_BOUND

ORIENTED_FULL_VOLTERRA_REPAIR:
  L: "log(m)"
  reflection: "R(theta)=2*pi-theta"
  source_functional: >-
    sigma_m = mu_W02_raw - R_*(mu_arch + mu_prime), with mu_W02_raw
    kept on (0,infinity).  sigma_m is an endpoint-compensated functional,
    not asserted to be a finite signed measure.
  test_functions:
    B_yq(t): "sum_n conj(y_n) q_n cos(n t)"
    G_yq(t): "the polarized Hilbert-current sine test"
    J_yq(t): "G_yq(t) + t * B_yq(t)"
  endpoint_laws:
    - "J_yq(0)=0"
    - "J_yq(2*pi)=0"
  exact_consumer_identity: >-
    Psi_m(z)=<y,Mq>=<sigma_m,J_yq> as a convergent source functional;
    the n-independent archimedean scalar is absent because <y,q>=0.
  relation_to_prior_representation: >-
    This is the one-functional, nonperiodic form of the same polarized
    Hilbert/Volterra identity.  The prior formula
    D_perp + (1/2)Phi(G) remains correct but is not minimal.

FOLDING_FALSIFIER_AND_REPAIR:
  a: "L/(4*pi)"
  q_m: "exp(-2*pi*a)=m^(-1/2)"
  exact_first_moment_fold: >-
    sum_{r>=0} (t+2*pi*r) exp(-a(t+2*pi*r))
    = exp(-a*t)/(1-q_m) * (t + 2*pi*q_m/(1-q_m)).
  winding_shadow: "2*pi/(sqrt(m)-1)"
  conclusion: >-
    A folded single-weight formula without the winding shadow is false.
    This is a C04 loss-of-winding obstruction, not a numerical anomaly.

CLOSES:
  - CORRECTION_12_QPROJECTION_RETRACTIONS
  - QPROJECTED_CONSTANT_DIAGONAL_ERASURE
  - RAW_UNREFLECTED_UNIFORM_COSINE_TRANSFORM
  - NON_QPROJECTED_DIAGONAL_WEIGHTED_NORM_AS_MINIMAL_OBJECT
  - FOLDED_VARIABLE_DIAGONAL_UNIFICATION_AS_THE_NEXT_MINIMAL_GAP
  - SEPARATE_DIAGONAL_CHANNEL_AS_A_PRIMARY_REPRESENTATION

OPENS: []

CARRIES_OPEN:
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - QPROJECTED_P59_KERNEL_COMPACT_RATE
  - SELECTED_FINITE_ROW_MODE_ENERGY_ADAPTER
  - SelectedPhysicalFourierEnergyControl
  - COMPENSATED_REFLECTION_DISCREPANCY_SOURCE_BOUND
  - COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_SELECTED_FERRERS_ORIENTED_FULL_VOLTERRA_SOURCE_RATE_PREFLIGHT
  MODE: PAPER_AND_SOURCE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false

NEXT_DISCRIMINATOR:
  PASS: ORIENTED_FULL_VOLTERRA_CONSUMER_RATE_READY
  HOLD: ORIENTED_FULL_VOLTERRA_IDENTITY_WITHOUT_SOURCE_RATE
  FAIL: ORIENTED_FULL_VOLTERRA_REIMPORTS_STIELTJES_DISCREPANCY_OR_GRAPH_FLOOR_WALL

CANDIDATE_REPRESENTATIONS:
  R1_ORIENTED_FULL_VOLTERRA_SOURCE_FUNCTIONAL:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 3/10
    object: >-
      Keep W02 unfolded, reflect Arch+Prime, and estimate the literal full
      kernel J=G+tB against one oriented source functional.  Preserve all
      component cancellation until the final scalar.
  R2_QPROJECTED_VARIANCE_PLUS_ODD_REFLECTION:
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 3/10
    object: >-
      Retain the two-channel formula, but price the even channel by ||Q D q||
      rather than ||Dq|| and keep the odd channel in the compensated-reflection
      functional.  Use only if R1 fails its source-rate discriminator.

REGISTERED_PREDICTIONS:
  P_ORIENTED_VOLTERRA_1:
    probability: 0.72
    prediction: >-
      The exact oriented one-functional identity survives, but the final rate
      remains blocked by the von-Mangoldt Stieltjes discrepancy and the
      complement floor; result HOLD.
  P_ORIENTED_VOLTERRA_2:
    probability: 0.20
    prediction: >-
      Exact continuous-main cancellation, W02 tail decay and endpoint vanishing
      jointly produce a consumer-strength compact rate.
  P_ORIENTED_VOLTERRA_3:
    probability: 0.08
    prediction: >-
      A normalization, star-first orientation or endpoint-category correction
      is required before the full source identity is exact.

PRIOR_PREDICTION_FATE:
  P_QPROJECTED_DIAGONAL_1_0_76: CONFIRMED_AND_STRENGTHENED
  P_QPROJECTED_DIAGONAL_2_0_18: NOT_REALIZED
  P_QPROJECTED_DIAGONAL_3_0_06: NOT_REALIZED_FOR_THE_TWO_CHANNEL_IDENTITY

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE
  - C13_RESTORE_SYMMETRY_BY_EXPLICIT_SHADOW

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PROGRESS_CLASS:
  - FALSIFICATION_PROGRESS
  - REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
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
| `y=Q C^{-1}kappa` is the minimal left vector seen by the residual | Accepted. | `[FINITE_CELL][PAPER]` |
| `sum_n conj(y_n)q_n=0` | Accepted; it is exact orthogonality, not a new hypothesis. | `[FINITE_CELL][PAPER]` |
| The cosine test `B(t)` vanishes to second order at `0` and `2*pi` | Accepted for the finite integer-mode carrier. | `[FINITE_CELL][PAPER]` |
| The sine and cosine tests are the odd/even test-space parts | Accepted. This does not by itself put them against one common source functional. | `[FINITE_CELL][PAPER]` |
| The Euler/log head, Rayleigh shift and constant WR subtraction must be estimated | Rejected. They disappear after finite summation against the Q-projected weight. | `[FINITE_CELL][PAPER]` |
| One raw `t`-weighted cosine transform of the unreflected completed measure gives the diagonal | Killed exactly; W02 uses `t`, while the literal Prime/Arch diagonal uses the reflected weight `2*pi-t`. | `[FINITE_CELL][PAPER]` |
| Folding W02 without extra data repairs the full consumer | Rejected. The nonperiodic diagonal remembers the winding number. | `[FINITE_CELL][PAPER]` |
| The full Q-projected consumer has a one-functional representation | Accepted after orienting the source: W02 remains unfolded and Arch+Prime are reflected. | `[FINITE_CELL][PAPER]` |
| This representation supplies the compact rate | Not proved. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Correction 12 is correct

The three retractions are accepted.

First, every `n`-independent diagonal term acts as a scalar multiple of the
identity.  Since `y` is in `q^perp`, its pairing with `q` is zero.  The
Euler–Mascheroni/logarithmic head and the Rayleigh shift therefore disappear.
The constant `-2` inside the archimedean integrand must be cancelled **under the
finite mode sum before integration**; it must not be split off as a divergent
integral.  With that category guard, the cancellation is exact.

Second, aperiodicity of the full Volterra kernel kills only absorption into the
same periodic odd reflection functional.  It does not kill every possible
representation shift.

Third, the raw uniform-cosine hypothesis is false for an exact algebraic reason.
The numerical value in Correction 12 is corroboration only.  The source formulas
already distinguish the weights `t` and `2*pi-t`.

## 2. The report's finite-cell identities survive

For

\[
b_n=\overline{y_n}q_n,
\qquad
B(t)=\sum_n b_n\cos(nt),
\]

orthogonality gives

\[
B(0)=B(2\pi)=0.
\]

The derivative of every cosine vanishes at both endpoints, so the zeros have
order at least two.  Thus the diagonal test overcompensates the archimedean
`1/t` endpoint singularity.

The off-diagonal sine test is reflection-odd and the diagonal cosine test is
reflection-even.  This is an exact decomposition of the **test space**.  It is
not yet an identity of source functionals because the source orientations are
different.

## 3. The diagonal norm has one further exact Q-reduction

Let `D=diag(M_nn)`.  The report uses the valid estimate

\[
|\langle y,Dq\rangle|
\le \|y\|\,\|Dq\|.
\]

But it is not minimal.  Since `y=Qy`,

\[
\boxed{
\langle y,Dq\rangle=\langle y,QDq\rangle.
}
\]

Hence

\[
\boxed{
|D_\perp|\le \|y\|_2\,\|QDq\|_2.
}
\]

For unit `q` and real diagonal entries,

\[
\boxed{
\|QDq\|_2^2
=
\sum_n |M_{nn}|^2|q_n|^2
-
\left|\sum_n M_{nn}|q_n|^2\right|^2.
}
\]

The true separate-channel object is therefore a weighted **variance**, not a raw
weighted second moment.  This is the runner-up representation, not the selected
mainline.

## 4. The exact one-functional repair

Let `mu_02^raw` be the exponential W02 measure on `(0,infinity)` that represents
the W02 beta sequence.  Let `mu_AP` be the archimedean-plus-prime angle
functional on `(0,2*pi]`, and let

\[
R(t)=2\pi-t.
\]

Define the oriented source functional

\[
\boxed{
\sigma_m=\mu_{02}^{\rm raw}-R_*\mu_{AP}.
}
\]

For integer modes, reflection changes

\[
\sin(n(2\pi-t))=-\sin(nt),
\qquad
\cos(n(2\pi-t))=\cos(nt).
\]

Therefore the same orientation gives both the off-diagonal beta values and the
literal reflected derivative weight on the diagonal.

For the finite pair `(y,q)`, let

\[
J_{y,q}(t)=G_{y,q}(t)+tB_{y,q}(t),
\]

where `G` is the polarized Hilbert-current sine test.  Then, after the
Q-invisible scalar diagonal has been removed,

\[
\boxed{
\Psi_m(z)=\langle y,Mq\rangle
        =\langle\sigma_m,J_{y,q}\rangle.
}

This is an equality of convergent **functionals**, not an assertion that
`sigma_m` is a finite signed measure.  At the reflected archimedean endpoint,

\[
J_{y,q}(2\pi)=0,
\]

so the simple endpoint pole is paired legally.  The identity is the nonperiodic,
one-functional form of the already ratified Hilbert/Volterra mechanism.

## 5. Why the proposed fold is not the next gap

The full kernel contains `t B(t)` and is not periodic.  Folding W02 therefore
forgets the winding count.

With

\[
a=\frac{L}{4\pi},
\qquad
q_m=e^{-2\pi a}=m^{-1/2},
\]

the exact first-moment fold is

\[
\sum_{r\ge0}(t+2\pi r)e^{-a(t+2\pi r)}
=
\frac{e^{-at}}{1-q_m}
\left(t+\frac{2\pi q_m}{1-q_m}\right).
\]

Thus folding creates the explicit winding shadow

\[
\frac{2\pi}{\sqrt m-1}.
\]

A fold without this cocycle is a **C04 same-coordinates/two-laws** error: integer
sine samples forget the winding, while the diagonal derivative remembers it.
The report's proposed `FOLDED_VARIABLE_DIAGONAL_UNIFICATION` is therefore not the
minimal next node.

## 6. What remains hard

The representation has become smaller, but the rate has not been earned.
The next audit must preserve the complete oriented source and decide whether:

1. the leading W02 density cancels the reflected continuous prime main;
2. the W02 tail beyond `2*pi` is harmless for the nonperiodic kernel;
3. the von-Mangoldt Stieltjes remainder is controlled on this literal test;
4. the Duhamel regularity budget from `||y||`, `||q||=1` and `||Mode*q||`
   survives the selected schedule;
5. the complement floor and the Q-projected P59 envelope do not erase the gain.

The strongest attack is unchanged: an exact integral representation can still be
only the original linear solve written in source coordinates.  PASS requires an
actual compact rate, not elegance.

## CODEX DIRECTIVE

```text
NO LEAN, NUMERICS, ARISTOTLE, OR CODEX EXECUTION.

TASK_ID:
  GOAL058_SELECTED_FERRERS_ORIENTED_FULL_VOLTERRA_SOURCE_RATE_PREFLIGHT

MODE:
  PAPER_AND_SOURCE_READ_ONLY

SOURCE OBJECTS:
  y_k(z) = Q_k C_k^(-1) kappa_k(z)
  q_k    = literal selected normalized finite row
  sigma_k = mu_W02_raw - R_*(mu_arch + mu_prime)
  J_k,z(t) = G_k,z(t) + t B_k,z(t)

DELIVER EXACTLY:
  1. Source-locked signs and constants for sigma_k.
  2. Exact star-first proof of
       <y_k(z), M_k q_k> = <sigma_k, J_k,z>.
  3. Endpoint admissibility at t=0 and t=2*pi.
  4. Exact continuous-main cancellation on (0,2*pi).
  5. Explicit W02 tail ledger on (2*pi,infinity).
  6. Exact von-Mangoldt Stieltjes remainder and lower-end corrections.
  7. Duhamel/Volterra regularity bound using the literal Q-projected y_k.
  8. Final compact-rate product, or the smallest named surviving wall.

FORBIDDEN:
  - folding the nonperiodic full kernel without the winding cocycle;
  - splitting W02, Arch and Prime by absolute norms;
  - replacing y by unprojected C^(-1)kappa;
  - using ||Dq|| where ||QDq|| is the exact channel object;
  - treating sigma_k as a finite measure without endpoint audit;
  - numerical fitting or componentwise prime estimates.

PASS:
  ORIENTED_FULL_VOLTERRA_CONSUMER_RATE_READY

HOLD:
  ORIENTED_FULL_VOLTERRA_IDENTITY_WITHOUT_SOURCE_RATE

FAIL:
  ORIENTED_FULL_VOLTERRA_REIMPORTS_STIELTJES_DISCREPANCY_OR_GRAPH_FLOOR_WALL
```

## META CLOSEOUT

**What became smaller?**

The permanent two-channel ledger was replaced by one oriented full-Volterra
functional.  The separate diagonal norm was reduced from a raw weighted moment
to the exact Q-projected variance as a fallback.

**What was killed?**

```text
raw unreflected one-weight cosine transform;
folding the full kernel without winding data;
raw trial-weighted diagonal L2 norm as the minimal object;
"the diagonal can never be reabsorbed" as a universal claim.
```

**What must not be tried again?**

Do not fold a nonperiodic test and then reason only from its values on integer
frequencies.  The derivative channel remembers the lost winding number.

**Current smallest named gap**

```text
COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE
```

with the exact source object repaired to the oriented full-Volterra functional.

**Next cheapest decisive test**

The paper-only rate preflight above.

**Prediction closeout**

```text
P_QPROJECTED_DIAGONAL_1 (0.76): confirmed and strengthened.
P_QPROJECTED_DIAGONAL_2 (0.18): not realized.
P_QPROJECTED_DIAGONAL_3 (0.06): not realized for the exact two-channel identity.
```

**Memory entry**

```yaml
iteration:
  target: QPROJECTED_DIAGONAL_SOURCE_ACTION
  status: PROGRESS
  failed_strategy: RAW_UNREFLECTED_UNIFORM_COSINE_TRANSFORM
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: COMPLETED_REFLECTION_DUHAMEL_CONSUMER_RATE
  invariant_learned: >-
    W02 must remain unfolded for the nonperiodic derivative channel; reflecting
    Arch+Prime, not folding W02, preserves both integer values and diagonal weights.
  forbidden_future_move: FOLD_NONPERIODIC_KERNEL_WITHOUT_WINDING_COCYCLE
  next_decisive_test: ORIENTED_FULL_VOLTERRA_SOURCE_RATE_PREFLIGHT
```
