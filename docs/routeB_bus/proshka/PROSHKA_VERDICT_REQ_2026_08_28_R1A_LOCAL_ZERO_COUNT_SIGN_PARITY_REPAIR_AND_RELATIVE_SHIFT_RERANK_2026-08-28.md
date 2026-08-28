# STATUS: OPEN — REPORT HOLD RATIFIED; SIGN-PATTERN-ONLY REDUCTION FATAL; RELATIVE SPECTRAL SHIFT RERANKED

```yaml
PRIMARY: RATIFY_HOLD_KILL_SIGN_ONLY_REDUCTION_RERANK_RELATIVE_SPECTRAL_SHIFT
PRIMARY_COUNT: 1

QUEUE:
  REQ_ID: REQ-2026-08-28-R1A
  REPORT_TASK_ID: GOAL058_R1_LITERAL_GROUND_LOCAL_SPECTRAL_COUNT_PREFLIGHT
  QUEUE_STATUS_MUTATED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  REPORT_COMMIT: 5c5a5bef6224a3cb69ecfe3fa9b23c51ddeb276a
  REPORT_PATH: docs/routeB_bus/LINUX_R1_LOCAL_SPECTRAL_COUNT_PREFLIGHT_GOAL058_2026-08-28.md
  PRIOR_VERDICT: afd27ddfba21661ef77672c4bd0dd3d1d665106c

REPORT_ADJUDICATION:
  REPORTED_DISCRIMINATOR: HOLD
  REPORTED_CODE: R1_ZERO_DIVISOR_EXACT_BUT_LOCAL_FINITE_SPECTRUM_UNCONTROLLED
  HOLD_CODE: RATIFIED

  INCLUDED_LATTICE_REMOVABLE_VALUE: PAPER_PASS
  EXTERIOR_LATTICE_ESCAPE: PAPER_PASS
  OFF_LATTICE_SECULAR_FUNCTION: PAPER_PASS
  ALL_NONZERO_RESIDUES_ONE_SIGN_IMPLIES_ONE_ZERO_PER_GAP: PAPER_PASS

  SIGN_PATTERN_ENTIRELY_DETERMINES_LOCAL_ZERO_COUNT: KILLED
  MIXED_SIGNS_IMPLY_OR_CERTIFY_LOCAL_COUNT_TIGHTNESS: KILLED
  SELECTED_GROUND_VECTOR_SIGN_PATTERN_CONTROLS_R1_OUTRIGHT: KILLED

  EXACT_GAP_PARITY_LAW:
    status: PAPER_PASS
    statement: >-
      For consecutive nonzero residues xi_j, xi_(j+1), the number of real
      Lagrange roots in the open pole gap (j,j+1), counted with multiplicity,
      is odd iff xi_j*xi_(j+1)>0 and even iff xi_j*xi_(j+1)<0.

  SAME_SIGN_ADJACENCY_LOWER_BOUND:
    status: PAPER_PASS
    statement: >-
      The local root count is at least the number of adjacent same-sign residue
      pairs whose pole gaps lie in the interval.

  NEAR_ALTERNATION:
    status: NECESSARY_NOT_SUFFICIENT_FOR_R1_SURVIVAL
    statement: >-
      Uniform local zero-count tightness requires only O(1) same-sign adjacency
      defects in every central O(log m) mode window, but this does not exclude
      two or more roots in opposite-sign gaps.

EXACT_SOURCE_CLASS_PLANT:
  carrier: [-2,-1,0,1,2]
  common_properties:
    - even_row
    - eta_dot_xi_equals_1
    - monic_even_source_Lagrange_polynomial
    - all_roots_real
    - coefficient_sign_pattern_plus_minus_plus_minus_plus
  family_A:
    polynomial: (s^2-1/16)*(s^2-1/4)
    row: [315/512,-15/128,1/256,-15/128,315/512]
    roots_in_minus1_1: 4
  family_B:
    polynomial: (s^2-25/16)*(s^2-9/4)
    row: [91/512,-15/128,225/256,-15/128,91/512]
    roots_in_minus1_1: 0
  conclusion: >-
    Same source carrier, parity, eta normalization, real-rootedness and exact
    coefficient sign pattern do not determine the local zero count.

RICCI_DOOB_LINK:
  GENERIC_DIAGONAL_SIGN_GAUGE_IMPLIES_LITERAL_ONE_SIGN_ROW: false
  reason: >-
    A nonconstant diagonal gauge makes the gauged eigenvector one-signed; the
    literal row inherits the gauge sign pattern, not a constant sign.
  SOURCE_STRICT_ODD_BETA_CASE:
    status: CONDITIONAL_ONE_WAY_KILL
    guards:
      - pairwise_distinct_beta_values
      - strict_decrease_in_literal_mode_order
      - nonzero_connected_offdiagonal_support
      - lowest_eigenvector_uniqueness
    implication: >-
      The identity gauge already makes all literal off-diagonal entries negative;
      Perron-Frobenius then makes the literal real ground row strictly one-signed,
      which gives dense interlacing zeros and kills raw R1.
  SIGN_GATE_FAIL_IMPLIES_R1_SURVIVES: false

PROCESS_AUDIT:
  PRIOR_NUMERICAL_PROBE_AUTHORIZED: false
  REPORT_NUMERIC_TABLE: UNAUTHORIZED_DIAGNOSTIC_NONLOADBEARING
  mathematical_verdict_depends_on_table: false
  replacement: EXACT_SOURCE_CLASS_PLANT_ABOVE

R1_STATUS:
  RAW_GROUND_TRANSFORM_MONTEL_PROGRAM: HOLD_NO_FURTHER_WRAPPERS
  RAW_PROGRAM_ROUTE_FATAL: false
  LOCAL_COUNT_TIGHTNESS: OPEN
  SIGN_ONLY_SHORTCUT: FATAL
  LOG_DERIVATIVE_OF_RAW_ZERO_MEASURE: STILL_BLOCKED_BY_LOCAL_MASS

MINIMAL_MISSING_IDENTITY:
  name: SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
  statement: >-
    For every compact real interval I, the number, counted with multiplicity, of
    finite perturbed-scaling eigenvalues of the literal selected ground cell in I
    is eventually bounded independently of k.

SELECTED_REPRESENTATION:
  name: RELATIVE_PERTURBATION_DETERMINANT_SPECTRAL_SHIFT
  object: >-
    The exact ratio det(Dprime_k-s)/det(D_k-s), equivalently the signed
    zero-minus-pole spectral-shift measure, with the free lattice background
    retained as poles rather than discarded.
  reason: >-
    Absolute zero mass can diverge while the relative spectral shift remains
    locally bounded. This is a real representation change, not another Montel
    wrapper around the same counting measure.

RUNNER_UP:
  name: CENTRAL_SAME_SIGN_ADJACENCY_DIVERGENCE_KILL
  role: KILL_ONLY_SUFFICIENT_TEST
  implication: >-
    Unbounded adjacent same-sign count in one central O(log m) window proves
    unbounded local zero count and kills raw R1.
  nonimplication: >-
    Bounded same-sign adjacency count does not prove local zero-count tightness.

NEXT_TRANSACTION:
  AUTHORIZED: true
  TASK_ID: GOAL058_R1_RELATIVE_PERTURBATION_DETERMINANT_SPECTRAL_SHIFT_PREFLIGHT
  MODE: PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY
  LEAN_EDIT_AUTHORIZED: false
  NUMERICAL_PROBE_AUTHORIZED: false
  ARISTOTLE_AUTHORIZED: false
  CODEX_AUTHORIZED: false
  NEW_GROUND_FAMILY_AUTHORIZED: false

NEXT_TRANSACTION_OUTPUTS:
  - exact_relative_determinant_ratio_with_all_scalars_and_coordinates
  - exact_free_and_perturbed_operator_objects_in_one_fixed_metric
  - rank_one_and_sign_of_perturbation_audit
  - relative_spectral_count_or_spectral_shift_bound
  - anchored_log_derivative_of_the_relative_ratio
  - exact_target_limit_and_normalization_crosswalk_to_centeredXi
  - proof_that_no_stopped_ground_to_trial_tracking_rate_is_imported

DISCRIMINATOR:
  PASS:
    code: R1_RELATIVE_SPECTRAL_SHIFT_NORMALITY_AND_TARGET_SOURCE_READY
    requirement: >-
      A source-locked fixed-metric self-adjoint rank-one relation gives a uniform
      local relative spectral-shift bound, and the same relative determinant has
      an exact noncircular target-limit crosswalk.
  HOLD:
    code: R1_RELATIVE_DETERMINANT_EXACT_WITHOUT_FIXED_METRIC_OR_TARGET_LIMIT
    requirement: >-
      The ratio is exact, but either the common self-adjoint metric, perturbation
      sign, relative-count bound or target identification remains absent.
  FAIL:
    code: R1_BACKGROUND_DIVISOR_SUBTRACTION_CHANGES_TARGET_OR_REIMPORTS_DEAD_TRACKING
    requirement: >-
      The relative object is not the source target, or its identification requires
      the stopped residual/graph-resolvent tracking rate under another name.

CANDIDATE_REPRESENTATIONS:
  R1_RELATIVE_SPECTRAL_SHIFT:
    rank: PRIMARY
    kill_power: 10/10
    proof_cost: 5/10
  R2_CENTRAL_ADJACENCY_LOWER_ENVELOPE:
    rank: KILL_ONLY_RUNNER_UP
    kill_power: 8/10
    proof_cost: 2/10

REGISTERED_PREDICTIONS:
  P_R1_RELSHIFT_1:
    probability: 0.62
    prediction: >-
      The exact determinant ratio closes, but the source does not supply one fixed
      positive metric and a signed rank-one interlacing theorem together; HOLD.
  P_R1_RELSHIFT_2:
    probability: 0.25
    prediction: >-
      The quotient construction yields a genuine bounded spectral-shift measure
      and a viable relative normal-family object; PASS.
  P_R1_RELSHIFT_3:
    probability: 0.13
    prediction: >-
      The quotient removes or changes the target divisor, or target identification
      imports the dead tracking wall; FAIL.

PRIOR_PREDICTION_FATE:
  P_R1_ZERODENSITY_1_0_98: CONFIRMED
  P_R1_ZERODENSITY_2_0_76: CONFIRMED
  P_R1_ZERODENSITY_3_0_42: NOT_DECIDED
  note: model-row and sign-pattern diagnostics do not test the literal local count

ARSENAL_MANDATE: ACCEPTED_STANDING
SHADOW_DISCOVERY_COMPILER_MANDATE: ACKNOWLEDGED_NOT_EXECUTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C10_FUNCTIONAL_NOT_SURROGATE

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
| Included lattice values and exterior escape | Ratified exactly as reported. | `[COFINAL_FAMILY][PAPER]` |
| Off-lattice secular function | Ratified: the finite zeros are roots of the exact Cauchy sum/source Lagrange polynomial. | `[FINITE_CELL][LEAN+PAPER]` |
| One-signed nonzero real row | Sufficient for strict one-root-per-gap interlacing; on a fixed `z` compact the count grows like `log m`. Raw R1 then dies. | `[COFINAL_FAMILY][CONDITIONAL]` |
| Arbitrary mixed signs | They destroy monotonicity, but do not imply bounded zero count. | `[ABSTRACT][PAPER]` |
| Sign pattern alone | It determines only the parity of the root count in each pole gap, not the exact count. | `[ABSTRACT][PAPER]` |
| Ricci/Doob sign gate | Only a guarded one-way supplier of the fatal one-sign case. It is not equivalent to the literal ground-row sign pattern or to local count tightness. | `[COFINAL_FAMILY][CONDITIONAL]` |
| Current exact gap | Still the uniform local counting measure of the finite perturbed spectrum. The report did not reduce it to a binary sign question. | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. What the report closed

The report correctly accepts the two earlier repairs.

Inside the finite carrier, a P59 lattice point is a removable evaluation point and
is a zero exactly when the corresponding coefficient vanishes. On the selected
schedule `m=N=k+2`, the exterior free lattice escapes every fixed compact.
Therefore the remaining load-bearing divisor is the finite source Lagrange/
perturbed-scaling spectrum.

It also proves a useful sufficient kill. For nonzero residues of one sign,

\[
S(s)=\sum_j\frac{\xi_j}{j-s}
\]

is strictly monotone in every pole gap and has one zero there. Since a fixed
`z`-interval corresponds to an `s`-interval containing order `L=log m` gaps, the
local zero count diverges. No zero-free gauge can repair this divisor.

## 2. The exact law is parity, not count

Let

\[
P(s)=\sum_j\xi_j\prod_{\ell\ne j}(\ell-s)
\]

be the source Lagrange polynomial, and assume `xi_j` and `xi_(j+1)` are nonzero.
At consecutive nodes, the two barycentric products have opposite signs. Hence

\[
\operatorname{sgn}(P(j)P(j+1))
=-\operatorname{sgn}(\xi_j\xi_{j+1}).
\]

Because all roots of the ground polynomial are real, the number of roots in
`(j,j+1)`, counted with multiplicity, is odd exactly when
`xi_j*xi_(j+1)>0`, and even exactly when the product is negative.

Therefore every adjacent same-sign pair forces at least one root, but an
opposite-sign pair may contain zero, two, four, or another even number of roots.
Their number depends on the coefficient magnitudes, not only their signs.

This gives the legitimate one-sided lower envelope:

\[
N_k(I)\ge
\#\{j:[j,j+1]\subset I,\ \xi_{k,j}\xi_{k,j+1}>0\}.
\]

If the right side diverges in the central `O(log m)` window corresponding to one
fixed `z` compact, raw R1 is fatal. If it stays bounded, R1 is not proved viable.

## 3. Exact plant inside the source class

The sign-only reduction fails even after retaining the exact source-level
invariants: symmetric carrier, even row, eta normalization and real-rootedness.

Use the carrier

\[
-2,-1,0,1,2.
\]

First polynomial:

\[
P_A(s)=(s^2-1/16)(s^2-1/4).
\]

Its Lagrange residue row is

\[
\xi^A=
(315/512,-15/128,1/256,-15/128,315/512).
\]

Second polynomial:

\[
P_B(s)=(s^2-25/16)(s^2-9/4),
\]

with row

\[
\xi^B=
(91/512,-15/128,225/256,-15/128,91/512).
\]

Both rows are even, both satisfy `sum xi = 1`, both have the identical sign
pattern `+ - + - +`, and both source polynomials have only real roots. Yet
`P_A` has four roots in `(-1,1)`, while `P_B` has none there.

Thus the report's phrase “entirely governed by the sign pattern” is refuted in
the literal source category. This is a direct **C10** kill: coefficient signs are
a useful surrogate lower bound, not the root-count functional consumed by R1.

## 4. The Ricci/Doob link is only one-way

A generic diagonal sign gauge does not make the literal row one-signed. It makes
the gauged eigenvector one-signed; undoing the gauge restores the gauge's sign
pattern.

There is one useful source-specific special case. If the completed odd beta field
is pairwise distinct and strictly decreasing in the literal mode order, then the
identity gauge already makes every off-diagonal Loewner entry negative. If the
support graph is connected, Perron-Frobenius makes the literal lowest real
eigenvector strictly one-signed. That implies full interlacing and kills raw R1.

But the implications are only:

```text
strict source monotonicity + irreducibility
  -> literal one-sign ground
  -> dense local zeros
  -> raw R1 fatal.
```

Neither converse is available. In particular:

```text
Ricci sign gate FAIL
  does not imply alternating ground signs;
  does not imply bounded local zero count;
  does not make R1 pass.
```

## FINAL PROPOSAL

Do not open a theorem named only `SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN`.
It is the wrong consumer.

The raw-transform Montel program remains on HOLD, and no further raw Herglotz or
normal-family wrapper is authorized. The correct representation shift is the
precommitted relative determinant:

\[
\frac{\det(D'_k-sI)}{\det(D_k-sI)}.
\]

Its signed zero-minus-pole measure can remain locally bounded even when the
absolute zero count diverges. The next audit must decide whether the project has
one fixed self-adjoint metric and a signed rank-one perturbation theorem strong
enough to control this relative spectral shift, and whether that relative object
still has the exact target limit required by Route B.

## STRONGEST ATTACK

The strongest attack on the selected representation is:

> Subtracting the free lattice divisor may make the family normal only by changing
> the target. The raw transform is the object carrying the real-zero theorem; a
> relative determinant may converge to a ratio or logarithmic derivative rather
> than to centered Xi.

That attack is fatal unless the next preflight provides an exact target
crosswalk. “Same zeros after background subtraction” is not enough; the final
consumer requires the exact same normalized family or a new rigorously typed
closure theorem for the relative object.

The strongest attack on the sign shortcut is the source-class plant above. It
preserves every claimed invariant and changes the local root count from four to
zero without changing the sign pattern.

## CODEX DIRECTIVE

```text
NO CODEX EXECUTION AUTHORIZED.

TASK_ID:
  GOAL058_R1_RELATIVE_PERTURBATION_DETERMINANT_SPECTRAL_SHIFT_PREFLIGHT

MODE:
  PAPER_SOURCE_AND_PRIMARY_LITERATURE_READ_ONLY

DELIVER EXACTLY:

1. The exact determinant ratio, including all constants, signs, carrier order and
   the coordinate map between `s` and the P59 `z` variable.
2. The free and corrected scaling operators as operators on one declared space.
3. The exact metric in which each operator is self-adjoint.
4. Whether their difference is rank one and sign-definite in that same metric.
5. The strongest valid relative eigenvalue-count / spectral-shift bound.
6. The anchored logarithmic derivative of the relative determinant.
7. The exact source target of the relative object and a noncircular crosswalk to
   centeredXi or the final roof consumer.
8. A proof that no stopped residual/graph-resolvent tracking rate is imported.

MANDATORY PLANTS:

P1_SAME_SIGN_PATTERN_DIFFERENT_COUNT:
  Use the two exact even eta-normalized rows in this verdict.

P2_GAUGED_PERRON_NOT_LITERAL_PERRON:
  Use a nonconstant diagonal sign gauge; the transformed eigenvector is positive
  while the literal vector has the gauge sign pattern.

P3_RANK_ONE_WITHOUT_SIGN:
  A rank-one difference without sign definiteness does not give one-sided
  interlacing or a bounded monotone spectral shift.

P4_RELATIVE_OBJECT_WRONG_TARGET:
  A normal determinant ratio does not identify the raw ground transform or
  centeredXi without an exact adapter.

FORBIDDEN:
  another raw Montel wrapper;
  sign pattern as an exact root-count theorem;
  generic Perron after an unnamed gauge;
  Euclidean interlacing for an operator self-adjoint only in an undeclared metric;
  numerical zero counts as a cofinal theorem;
  reusing the stopped ground-to-trial tracking rate under a new name.
```

## META CLOSEOUT

**What became smaller?**

The sign information was compressed to its exact content: a parity law and a
one-sided lower bound on the local zero count.

**What was killed?**

- sign pattern as the exact local zero-count functional;
- mixed signs as evidence of count tightness;
- generic Ricci/Doob gauge PASS as literal one-sign without source guards.

**What must not be tried again?**

Do not open `SELECTED_GROUND_VECTOR_COEFFICIENT_SIGN_PATTERN` as if it decided
R1. Do not run another raw log-derivative or Montel wrapper before changing the
object.

**Current smallest named gap?**

```text
SELECTED_FERRERS_GROUND_LOCAL_SPECTRAL_COUNT_TIGHTNESS
```

for the raw family; and, for the selected representation shift:

```text
R1_RELATIVE_SPECTRAL_SHIFT_FIXED_METRIC_AND_TARGET_CROSSWALK
```

**Next cheapest decisive test?**

Audit whether the exact free/corrected scaling pair is a sign-definite rank-one
perturbation in one fixed positive metric and whether its relative determinant
has the correct target.

**Prior predictions?**

- exterior lattice escape: confirmed;
- no existing uniform local-count source theorem: confirmed;
- literal low-interval count bounded: not tested.

**Memory entry?**

```yaml
iteration:
  target: R1 literal ground local zero-count classification
  status: PROGRESS
  failed_strategy: coefficient sign pattern as exact zero-count law
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: R1_RELATIVE_SPECTRAL_SHIFT_FIXED_METRIC_AND_TARGET_CROSSWALK
  invariant_learned: >-
    Adjacent residue signs control only root-count parity; exact local mass
    depends on magnitudes and the full relative determinant.
  forbidden_future_move: >-
    Do not use mixed signs, a diagonal Perron gauge or model-row counts as a
    cofinal local-count theorem.
  next_decisive_test: >-
    Fixed-metric sign-definite rank-one spectral-shift and exact target audit.
```
