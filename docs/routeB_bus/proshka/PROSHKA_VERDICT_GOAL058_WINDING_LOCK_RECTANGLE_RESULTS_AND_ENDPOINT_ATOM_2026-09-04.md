# STATUS: OPEN — SINGLE-ENDPOINT ATOM IS FALSE; FULL-BOUNDARY RECTANGLE CONTROL REMAINS THE MINIMAL COUNT LOCK
```yaml
PRIMARY: KILL_SINGLE_ENDPOINT_ATOM_AS_RECTANGLE_ROUCHE_CERTIFICATE
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_FULL_RECTANGLE_BOUNDARY_ROUCHE_OR_WINDING_CONTROL
DEFAULT_SCOPE: COFINAL_FAMILY
DEFAULT_VERIFIER: PAPER
TAG_INHERITANCE: "section scope/verifier apply to nested claims unless explicitly overridden"

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-WINDLOCK
  BOUNDARY_ID: GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM
  REQUEST_COMMIT: 84a783a4d4cabe3de40f1ae86f75dfda2d4cd558
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_WINDING_LOCK_RESULTS_2026-09-04.txt
  REQUEST_GIT_BLOB: 1373897d09bea6c12aaebd49e8d4e5f32ddabf59
  REQUEST_SHA256: 9c24892101a090b4e92e1b41adb13719bef16861c10274d50005944b1b1a15b8
  REQUEST_BYTES: 7466
  REQUEST_LINES: 80
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WINDING_LOCK_RECTANGLE_RESULTS_AND_ENDPOINT_ATOM_2026-09-04.md
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY
  POST_REQUEST_RESULTS_USED: false

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: cd56b8f0011e74a99ec488bdd6668c3c404c6cce
  PARENT_VERDICT_LEAKAGE: 9a202947a0de5ac3c139ac81ce8d4bd3e2034cc9
  PARENT_VERDICT_ZEROPIN: 1529837d895f531330acfa4d81d96c83779a75d7
  PREFLIGHT_PATH: docs/routeB_bus/AGENT_REPORT_2026-09-04_GOAL058_WINDING_LOCK_FIXED_COMPACT_PREFLIGHT.md
  PREFLIGHT_GIT_BLOB: 4fc06e4215d2428cc1656279f3164adeea3fe874

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

Q1_RECTANGLE_LOCK:
  FULL_BOUNDARY_ROUCHE:
    theorem_shape: VALID
    hypotheses:
      - "F and X holomorphic on a neighborhood of the closed rectangle"
      - "X is nonzero on the whole boundary"
      - "sup_boundary |F-X| < inf_boundary |X|"
    conclusion: "equal numbers of zeros with multiplicity in the rectangle"
    scope: ABSTRACT
    verifier: PAPER
  SINGLE_ENDPOINT_REDUCTION:
    theorem_shape: FALSE
    endpoint_quantity: "e(R)=|F(R)-X(R)|/|X(R)|"
    what_it_certifies: "at most nonvanishing and the same real sign at ±R"
    what_it_does_not_certify:
      - "the Rouché inequality on either vertical edge"
      - "the Rouché inequality on the horizontal edges"
      - "equal zero counts"
      - "locations or multiplicities of individual zeros"
      - "local-uniform convergence"
    scope: ABSTRACT
    verifier: PAPER
  LAGUERRE_POLYA_VERTICAL_MODULUS:
    individual_function_fact: "for a real-rooted polynomial P, |P(x+iy)| >= |P(x)|"
    ratio_or_difference_consequence: false
    Xi_application_without_RH: CIRCULAR
    h_independence: DIAGNOSTIC_ONLY
  ENDPOINT_KILL_PLANT:
    target: "X(z)=1"
    approximant: "F(z)=(1-z^2/a^2)(1-z^2/b^2)"
    parameters: "R>0, 0<a<R, b=sqrt(R^2-a^2)"
    identities:
      - "F(0)=X(0)=1"
      - "F(R)=X(R)=1"
      - "e(R)=0"
    divisor_difference: "F has four real zeros ±a, ±b inside the rectangle; X has none"
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_EVEN_REALROOTED_POLYNOMIAL_COUNTEREXAMPLE
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  scope: ABSTRACT
  verifier: PAPER

Q2_ENDPOINT_SUPPLIERS:
  INDEPENDENT_SOURCE_SUPPLIER_FOUND: false
  RANKING:
    - rank: 1
      code: ONE_NODE_PROJECTIVE_GROUND_TO_TRIAL_TRANSFER
      status: BEST_SOURCE_FAITHFUL_REPAIR_NOT_A_BYPASS
      kill_power: 9/10
      proof_cost: 5/10
      first_uncontrolled_term: "same-anchor projective coefficient error, including anchor nondegeneracy"
    - rank: 2
      code: EXACT_NODE_PLUS_WEIL_ZERO_SUM_IDENTITY
      status: DOES_NOT_IDENTIFY_THE_TARGET_VALUE
      kill_power: 6/10
      proof_cost: 4/10
      first_uncontrolled_term: "indefinite signed zero-side correlation/tail, or equivalently generic-node leverage"
    - rank: 3
      code: OUTSIDE_WINDOW_LEAKAGE
      status: KILLED_AS_ENDPOINT_MARGIN_SUPPLIER
      kill_power: 10/10
      proof_cost: 1/10
      reason: "small F/X gives e(R)->1, with the side determined by sign; fixed R is eventually inside the growing window"
  NODE_DECOMPOSITION:
    formula: >-
      e_m(x_n) is bounded by the relative same-anchor ground-to-trial node
      error plus the relative trial-to-Xi node error.
    component_I_relation: "this is a one-node restriction of component I, not an independent supplier"
  LEAKAGE_LIMIT:
    if_F_over_X_tends_to_zero: "e(R) tends to 1, not to a strict margin below 1"
    approach_side: "below only with an additional eventual same-sign theorem; above if signs oppose"
    if_X_is_smaller_than_leakage: "e(R) can diverge"
  scope: COFINAL_FAMILY
  verifier: PAPER

Q3_DIVISOR_CONVERGENCE:
  ENDPOINT_ERRORS_EQUIVALENT_TO_COMPLETE_DIVISOR_CONVERGENCE: false
  REPAIRED_FIXED_COMPACT_SUFFICIENT_CERTIFICATE:
    - "strict Rouché or certified winding control on the entire outer boundary"
    - "strict control on the entire boundary of each local isolating domain"
    - "target multiplicities in the isolating domains"
    - "sum of local counts equals the outer count, excluding extra zeros in the complement"
    - "repeat for arbitrarily small isolating domains"
  NECESSITY: false
  necessity_counterexample: "F(z)=exp(a z^2) X(z) has the same divisor and anchor but can violate Rouché value bounds"
  FIXED_COMPACT_NEEDS_TAIL_OR_SECOND_JET: false
  GLOBAL_PRODUCT_IDENTIFICATION_STILL_NEEDS:
    - "escape/tightness of unmatched zeros, e.g. reciprocal-square tail control"
    - "anchor normalization"
    - "local boundedness or an explicit canonical-product tail theorem"
    - "second-jet/curvature convergence to kill exp(a z^2), unless an order-one/type theorem replaces it"
  scope: COFINAL_FAMILY
  verifier: PAPER

Q4_LEAN:
  PINNED_MATHLIB:
    version: v4.26.0
    commit: 2df2f0150c275ad53cb3c90f7c98ec15a56a1a67
  POLYNOMIAL_CIRCLE_ARGUMENT_PRINCIPLE:
    status: LEANABLE_WITH_NEW_LOCAL_THEOREM
    general_winding_number_required: false
    exact_ingredients:
      - "Polynomial.Splits.eval_eq_prod_roots"
      - "logDeriv_prod"
      - "logDeriv_const_mul"
      - "circleIntegral.integral_sub_inv_of_mem_ball"
      - "Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable"
      - "finite-sum linearity of circleIntegral"
    boundary_guard: "no polynomial root lies on the circle"
    output: "circle integral of p'/p equals 2*pi*i times the root multiset count inside"
  POLYNOMIAL_RECTANGLE_ARGUMENT_PRINCIPLE:
    status: NEW_ANALYTIC
    reason: "the pinned library has rectangle Cauchy-Goursat but no index/winding or inside-pole count theorem"
  DIVISOR_ALGEBRA:
    status: LEAN_READY
    use: "cancel the common P59 prefactor at divisor or log-derivative level"
    does_not_supply: "the contour-to-count interpretation"
  CENTERED_XI:
    function_on_shelf: true
    theorem: Q3.RouteB.differentiable_centeredXi
    divisor_available_in_principle: true
    missing_for_rectangle:
      - "a rectangle argument principle or Rouché theorem"
      - "boundary nonvanishing"
      - "a finite target zero-count/multiplicity interface"
  FIRST_KERNEL_CHECKABLE_TARGET: P59_SINGLE_ENDPOINT_ATOM_KILL_PLANT
  scope: ABSTRACT
  verifier: PAPER

DISCRIMINATOR:
  NAME: FULL_RECTANGLE_BOUNDARY_ROUCHE_MARGIN
  FORMULA: "inf_{z in boundary D}|X(z)| - sup_{z in boundary D}|F(z)-X(z)|"
  PASS_CONDITION: "a rigorous lower envelope is strictly positive"
  FAIL_CONDITION: "a rigorous upper envelope is negative, or the endpoint plant has different counts"
  ZERO_CONSISTENT_RESULT: INCONCLUSIVE
  PLANTED_FAILURE: P59_SINGLE_ENDPOINT_SAME_VALUE_EXTRA_FOUR_REAL_ROOTS
  scope: FINITE_CELL
  verifier: CONDITIONAL

CANDIDATE_REREPRESENTATIONS:
  - code: R1_FULL_BOUNDARY_PROJECTIVE_TRANSFER
    rank: PRIMARY_ANALYTIC_REPAIR
    target: "ground-to-trial coefficient control plus trial-to-Xi control on the full thin-rectangle boundary"
    kill_power: 10/10
    proof_cost: 8/10
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL
  - code: R2_POLYNOMIAL_CIRCLE_ROOT_COUNT
    rank: CHEAP_SAME_LATTICE_TOOL
    target: "circle-only root-count formula for P_g and P_t after exact common-factor cancellation"
    kill_power: 7/10
    proof_cost: 3/10
    scope: ABSTRACT
    verifier: PAPER
  - code: R3_LOG_DERIVATIVE_FAR_TAIL_PAIRING
    rank: GLOBAL_PRODUCT_RUNNER_UP
    target: "pair far ground and Xi zeros with summable reciprocal-square discrepancy"
    kill_power: 9/10
    proof_cost: 8/10
    scope: COFINAL_FAMILY
    verifier: CONDITIONAL

RANKED_NEXT_ACTION:
  CODE: CODEX_FORMALIZE_P59_SINGLE_ENDPOINT_ATOM_KILL_PLANT
  EXECUTION_AUTHORIZED: false
  TARGET_FILE: q3.lean.aristotle/Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean
  CLOSES:
    - SINGLE_ENDPOINT_ATOM_AS_RECTANGLE_COUNT_CERTIFICATE
  OPENS: []
  SUCCESS_CODE: P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_KERNEL_GREEN
  FAILURE_CODE: P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_LEAN_GAP
  NEXT_ANALYTIC_GAP: P59_GROUND_XI_FULL_THIN_RECTANGLE_BOUNDARY_MARGIN
  scope: ABSTRACT
  verifier: CONDITIONAL

SCOPED_KILLS:
  SINGLE_ENDPOINT_ATOM:
    CODE: KILL_SINGLE_ENDPOINT_ATOM_AS_RECTANGLE_ROUCHE_CERTIFICATE
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXPLICIT_EVEN_REALROOTED_POLYNOMIAL_COUNTEREXAMPLE
    PINNED_EVIDENCE: "EXPECTED_VERDICT_PATH, Q1_ENDPOINT_KILL_PLANT"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    scope: ABSTRACT
    verifier: PAPER
  XI_LAGUERRE_POLYA_BOUNDARY_PROPAGATION:
    CODE: DO_NOT_USE_XI_LAGUERRE_POLYA_BEFORE_RH
    KILL_SCOPE: ATTEMPT
    KILL_EVIDENCE_KIND: CIRCULAR_TARGET_PROPERTY
    PINNED_EVIDENCE: "SOURCE_BASE_COMMIT:q3.lean.aristotle/Q3/Proofs/RouteB/ClassicalXiInterface.lean, rh_iff_centeredXi_zeros_real"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD_AS_UNCONDITIONAL_ARGUMENT
    scope: ABSTRACT
    verifier: PAPER
  OUTSIDE_WINDOW_LEAKAGE_ENDPOINT:
    CODE: KILL_LEAKAGE_TO_STRICT_ENDPOINT_MARGIN
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: LIMIT_EQUALS_BOUNDARY_OF_ROUCHE_CONDITION
    PINNED_EVIDENCE: "EXPECTED_VERDICT_PATH, Q2_LEAKAGE_LIMIT"
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
    scope: COFINAL_FAMILY
    verifier: PAPER

PREDICTION_FATES:
  P_RECT_LOCK_R28_IMPROVES:
    probability: 0.70
    fate: UNRESOLVED_UNRUN_AT_REQUEST_LOCK
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_RECT_LOCK_R40_FAILS_AT_M13:
    probability: 0.60
    fate: UNRESOLVED_UNRUN_AT_REQUEST_LOCK
    scope: FINITE_CELL
    verifier: CONDITIONAL
  PREFLIGHT_SINGLE_REAL_ENDPOINT_IS_WORST:
    probability: null
    fate: CONFIRMED_ONLY_AS_SUPPLIED_FINITE_CELL_DIAGNOSTIC_REFUTED_AS_ABSTRACT_THEOREM
    scope: FINITE_CELL
    verifier: CONDITIONAL
  P_ENDPOINT_ATOM_IS_COMPONENT_I:
    probability: 0.75
    fate: REFUTED_AS_STATED
    repair: "one-node component I is useful only after a separate endpoint-to-full-boundary theorem"
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_ENDPOINT_SUPPLIER_FROM_LEAKAGE:
    probability: 0.35
    fate: REFUTED
    scope: COFINAL_FAMILY
    verifier: PAPER
  P_POLY_ARGUMENT_PRINCIPLE_LEANABLE:
    probability: 0.55
    fate: CONFIRMED_WITH_CIRCLE_ONLY_DOMAIN_REPAIR
    scope: ABSTRACT
    verifier: PAPER

K8A:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: >-
    The same normalized finite-ground family must converge locally uniformly
    to centeredXi, or an equivalent complete-divisor-plus-tail-and-gauge
    package must identify that limit.
  ORIGINAL_REQUESTED_OBJECT: "one relative endpoint error e(R)<1"
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  KNOWN_WEAKER_INTERFACES:
    - "full-boundary Rouché margin implies equal count"
    - "certified winding-number difference zero implies equal count"
    - "local isolating counts plus outer count imply complete fixed-compact divisor matching"
  NOVELTY_AXIS: ENDPOINT_TO_BOUNDARY_PROPAGATION
  scope: COFINAL_FAMILY
  verifier: PAPER

PROGRESS_CLASS: FALSIFICATION_AND_REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 5

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## ROUTE MAP

### Source and transport lock

The authoritative request was fetched from GitHub at commit
`84a783a4d4cabe3de40f1ae86f75dfda2d4cd558`. Its Git blob is
`1373897d09bea6c12aaebd49e8d4e5f32ddabf59`. Independent UTF-8 byte
reconstruction gives exactly 7,466 bytes, 80 LF-terminated lines, and SHA-256
`9c24892101a090b4e92e1b41adb13719bef16861c10274d50005944b1b1a15b8`.
`[ABSTRACT][PAPER]`

The six-field phase key is unchanged. This adjudication uses the request-locked
evidence only. Later branch commits are not used to repair or score the
registered predictions. `[ABSTRACT][PAPER]`

### Q1 — the rectangle theorem and the endpoint kill

The valid Rouché theorem shape is the ordinary full-boundary statement. Let
\(D_{R,h}\) be the interior of the rectangle
\([-R,R]\times[-h,h]\). Let \(F\) and \(X\) be holomorphic on a neighborhood of
\(\overline D_{R,h}\). If

\[
X(z)\ne0\quad(z\in\partial D_{R,h})
\]

and

\[
\sup_{\partial D_{R,h}}|F-X|
<
\inf_{\partial D_{R,h}}|X|,
\]

then \(F\) and \(X\) have the same number of zeros in \(D_{R,h}\), counted with
multiplicity. `[ABSTRACT][PAPER]`

That conclusion is only a total count. It does not pair individual zeros,
locate them, show equality of local multiplicities, rule out a displacement
that preserves the total count, imply convergence, or say anything outside the
rectangle. `[ABSTRACT][PAPER]`

The proposed reduction of the whole boundary inequality to

\[
e(R)=\frac{|F(R)-X(R)|}{|X(R)|}<1
\]

at one real endpoint is false. A decisive plant exists entirely inside the
claimed class. Fix \(R>0\), choose \(0<a<R\), and set

\[
b=\sqrt{R^{2}-a^{2}},\qquad
X(z)=1,\qquad
F(z)=\left(1-\frac{z^{2}}{a^{2}}\right)
     \left(1-\frac{z^{2}}{b^{2}}\right).
\]

Then

\[
F(0)=X(0)=1
\]

and

\[
F(R)
=
\left(-\frac{R^{2}-a^{2}}{a^{2}}\right)
\left(-\frac{a^{2}}{R^{2}-a^{2}}\right)
=1=X(R).
\]

Hence \(e(R)=0\). Nevertheless, \(F\) has the four real zeros
\(\pm a,\pm b\) inside every thin rectangle of height \(h>0\), while \(X\) has
none. Both functions are even, real on \(\mathbb R\), real-rooted, normalized
at the anchor, and of exponential type zero. `[ABSTRACT][PAPER]`

This plant also defeats the proposed Laguerre–Pólya repair. For each
real-rooted polynomial \(P\),

\[
|P(x+iy)|\ge |P(x)|
\]

does hold factor by factor. It controls each modulus separately. It gives no
upper bound for \(|F-X|\), no monotonicity for \(|F-X|/|X|\), and no maximum
principle placing that ratio at the real endpoint. Applying a
Laguerre–Pólya property to centered \(\Xi\) is moreover unavailable
unconditionally: real-zero control of centered \(\Xi\) is the target.
`[ABSTRACT][PAPER]`

Thus the supplied observation that the sampled maximum occurred near the real
end is a legitimate finite-cell diagnostic. It is not a theorem, and the
near-independence from \(h\) cannot be promoted. `[FINITE_CELL][CONDITIONAL]`

What \(e(R)<1\) does prove is much smaller. Since the two normalized values are
real and \(X(R)\ne0\),

\[
\left|\frac{F(R)}{X(R)}-1\right|<1
\]

implies

\[
0<\frac{F(R)}{X(R)}<2.
\]

Therefore the two endpoint values are nonzero and have the same sign. Evenness
gives the same fact at \(-R\). Nothing on the other boundary points follows.
`[ABSTRACT][PAPER]`

### Q2 — no independent endpoint supplier was found

At a lattice node \(x_n=2\pi n/L\), the project already has the exact source
identity

\[
F_g(x_n)=\sqrt L\,(-1)^n\,\xi_n,
\qquad
F_g(0)=\sqrt L\,\xi_0.
\]

Therefore

\[
\frac{F_g(x_n)}{F_g(0)}
=
(-1)^n\frac{\xi_n}{\xi_0}.
\]

This makes the endpoint quantity computable from one coefficient ratio. It
does not estimate that ratio against \(\Xi(x_n)/\Xi(0)\).
`Proposition59EntireTransform.lean` supplies
`proposition59PoleKernel_sum_at_lattice`,
`proposition59RawTransform_at_zero_eq_sqrt`, and the node-safe transform;
`Proposition59ExplicitProductCurvatureBridge.lean` supplies the matching
numerator evaluation. `[FINITE_CELL][LEAN]`

The best source-faithful decomposition uses the trial row \(q\):

\[
\begin{aligned}
e_m(x_n)
\le&
\frac{\left|
(-1)^n\left(\frac{\xi_n}{\xi_0}-\frac{q_n}{q_0}\right)
\right|}
{\left|\Xi(x_n)/\Xi(0)\right|}
\\
&+
\frac{\left|
(-1)^n\frac{q_n}{q_0}-\Xi(x_n)/\Xi(0)
\right|}
{\left|\Xi(x_n)/\Xi(0)\right|}.
\end{aligned}
\]

The second term is a one-point specialization of the known trial-to-\(\Xi\)
limit. The first term is the same-anchor projective ground-to-trial problem,
including lower bounds for the anchor coordinates. It is a cheaper scalar
consumer than a full compact norm, but it is not an independent supplier and
does not bypass the main same-family wall. `[COFINAL_FAMILY][CONDITIONAL]`

The cutoff-free Weil identity does not close the first term. Combining the
ground eigen-equation with

\[
K=\sum_zE(z)E(z)^{T}
\]

gives a correlation identity of the form

\[
\lambda_1\xi_n
=
\sum_z F_\xi(z)F_{e_n}(z).
\]

Off RH this sum is real but indefinite. No one-sided bound, target value, or
tail cancellation follows. At a generic endpoint the request's own range data
show that the corresponding leverage object is enormous away from a zeta
zero. `[FINITE_CELL][PAPER]`

The leakage proposal fails more directly. If for a moving point beyond the
window one somehow proves

\[
\frac{F_g(R)}{\Xi(R)}\to0,
\]

then

\[
e(R)=\left|\frac{F_g(R)}{\Xi(R)}-1\right|\to1,
\]

which is the boundary of the strict Rouché condition, not a positive margin.
It approaches from below only after an additional eventual same-sign theorem;
with the opposite sign it approaches from above. If \(\Xi(R)\) decays faster
than the leakage, the ratio can instead diverge. For a fixed \(R\), the growing
production window eventually contains \(R\), so the outside-window regime is
not even stable under the cofinal quantifier. `[COFINAL_FAMILY][PAPER]`

The ranking is therefore:

1. one-node projective ground-to-trial transfer plus trial-to-\(\Xi\);
2. exact node/eigen-equation/Weil identity, which still leaves an indefinite
   global correlation;
3. outside-window leakage, killed as a strict-margin supplier.

The first uncontrolled term of the best route is the same-anchor projective
coefficient error, including anchor nondegeneracy. `[COFINAL_FAMILY][PAPER]`

### Q3 — fixed-compact divisor convergence and global product identification

The statement

> for every \(R,\delta\), all corresponding real endpoint errors are eventually
> \(<1\)

is not equivalent to complete divisor convergence on compacts. It does not
control the complex boundary, and moving extra zeros can evade every fixed
finite set of real sample points. `[COFINAL_FAMILY][PAPER]`

A repaired sufficient certificate on a fixed compact is:

1. choose an outer Jordan rectangle whose boundary avoids the target divisor;
2. prove strict Rouché dominance, or a certified winding count, on the entire
   outer boundary;
3. choose disjoint local Jordan domains around every target zero in the
   compact, with the required multiplicities;
4. prove the same full-boundary certificate on every local domain;
5. verify that the sum of local counts equals the outer count;
6. let the local diameters tend to zero.

This gives local matching with multiplicity and excludes extra zeros in the
complement. `[COFINAL_FAMILY][PAPER]`

Even that Rouché package is sufficient, not necessary, for divisor convergence.
The zero-free gauge plant

\[
F(z)=e^{az^{2}}X(z),\qquad F(0)=X(0),
\]

has exactly the same divisor as \(X\) but can violate any prescribed
value-based Rouché bound on a sufficiently large boundary. This is why divisor
convergence and function-value convergence must not be conflated.
`[ABSTRACT][PAPER]`

For the count or divisor on one fixed compact, reciprocal-square tail mass and
the second jet are not needed once the full local and outer counts are
certified. They remain load-bearing for global product identification:

- local divisor convergence does not control zeros escaping to infinity;
- reciprocal-square tightness, or an equivalent canonical-product tail
  theorem, controls their effect on compact values;
- the anchor removes a scalar;
- local boundedness or an explicit product-tail theorem gives a function
  limit;
- equality of the second jet pins the residual \(e^{az^{2}}\) gauge for the
  current order-two envelope.

An independently proved uniform order-one/type theorem can replace the
second-jet gauge pin. `[COFINAL_FAMILY][PAPER]`

### Q4 — what is Lean-ready

The exact pinned dependency is Mathlib `v4.26.0` at
`2df2f0150c275ad53cb3c90f7c98ec15a56a1a67`.
`q3.lean.aristotle/lake-manifest.json` fixes that commit.
`[ABSTRACT][LEAN]`

A circle-only polynomial argument principle is derivable without first
formalizing a general winding number. Over \(\mathbb C\), factor a nonzero
polynomial with

```lean
Polynomial.Splits.eval_eq_prod_roots
```

and expand its logarithmic derivative with

```lean
logDeriv_prod
logDeriv_const_mul
```

from `Mathlib/Analysis/Calculus/LogDeriv.lean`. For each root inside the circle,
use

```lean
circleIntegral.integral_sub_inv_of_mem_ball
```

from `Mathlib/MeasureTheory/Integral/CircleIntegral.lean`. For each root outside
the closed disk, use

```lean
Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
```

from `Mathlib/Analysis/Complex/CauchyIntegral.lean`. Finite-sum linearity then
gives

\[
\frac{1}{2\pi i}\oint_{|z-c|=R}\frac{p'(z)}{p(z)}\,dz
=
\#\{r\in p.\mathrm{roots}:|r-c|<R\},
\]

with multiplicity, provided no root lies on the circle.
`[ABSTRACT][PAPER]`

This is a new local theorem, not an existing argument-principle API. It is
nevertheless finite and kernel-checkable. The divisor algebra in
`Mathlib/Analysis/Meromorphic/Divisor.lean` can already cancel the common P59
prefactor, but it does not identify a contour integral with a count.
`[ABSTRACT][LEAN]`

The thin-rectangle version is not obtained for free. The pinned library has
`Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable`,
which is rectangle Cauchy–Goursat for a pole-free integrand. It has no theorem
computing the index of an inside pole, no rectangle argument principle, and no
Rouché theorem. That layer remains `NEW_ANALYTIC`.
`[ABSTRACT][PAPER]`

The request understates the existing target interface slightly. The project
already defines

```lean
Q3.RouteB.centeredXi
Q3.RouteB.differentiable_centeredXi
```

in `Q3/Proofs/RouteB/ClassicalXiInterface.lean`. Thus centered \(\Xi\) is
already an entire Lean function and can in principle carry
`MeromorphicOn.divisor`. What is absent is not the function itself. The absent
interfaces are:

1. rectangle Rouché or argument principle;
2. certified nonvanishing on the selected boundary;
3. a finite target zero-count and multiplicity ledger for that rectangle.

No global new definition of \(\Xi\) is required. `[ABSTRACT][LEAN]`

## FINAL PROPOSAL

Kill the single-endpoint atom as a count certificate. Preserve the thin
rectangle as a useful finite-cell diagnostic, but rename its analytic demand:

\[
\boxed{
\texttt{P59\_GROUND\_XI\_FULL\_THIN\_RECTANGLE\_BOUNDARY\_MARGIN}.
}
\]

The best source-faithful route to that margin is still the ground-to-trial
same-family bridge followed by the already known trial-to-\(\Xi\) convergence,
now consumed only on the selected boundary. The one-node endpoint estimate can
be an auxiliary input, but only after a separate endpoint-to-boundary theorem;
the endpoint estimate cannot replace that theorem. `[COFINAL_FAMILY][PAPER]`

Registered prediction before any further test:

```text
P_WINDLOCK_REPAIR:
  A direct source theorem controlling the full rectangle boundary will require
  the same ground-to-trial projective error that the endpoint atom was meant to
  avoid.
  probability: 0.80
```

Cheapest decisive test: formalize the endpoint counterexample. It closes a
false theorem shape without opening a new supplier and prevents future agents
from re-promoting sampled endpoint behavior into a universal boundary theorem.
`[ABSTRACT][PAPER]`

## STRONGEST ATTACK

The strongest objection to this verdict is:

> The numerical cells show that the maximum really sits at the real endpoint.
> Why kill a reduction that works on every tested cell?

Because the consumer is universal and the proposed theorem is false even in
the smallest claimed class. The plant has even real-rooted polynomials,
identical anchor and endpoint values, zero boundary roots, and a different
interior zero count. More precision or more cells cannot repair a false
implication. `[ABSTRACT][PAPER]`

The weakest repaired statement is exactly the full-boundary Rouché theorem.
A source-specific monotonicity theorem for the ratio on the four boundary
segments could reduce the checking burden, but that theorem must be proved and
must not assume that centered \(\Xi\) is Laguerre–Pólya. No such theorem is
currently supplied. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
TASK:
  Formalize exactly one kill plant:
  P59_SINGLE_ENDPOINT_ATOM_KILL_PLANT.

TARGET FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean

THEOREM SHAPE:
  For R>0 and 0<a<R, set b=sqrt(R^2-a^2) and

    p(z)=(1-z^2/a^2)(1-z^2/b^2).

  Prove:
    p(0)=1;
    p(R)=1;
    p(a)=0;
    p(-a)=0;
    p(b)=0;
    p(-b)=0;
    0<b<R.

  The theorem must make explicit that endpoint agreement and anchor agreement
  coexist with additional real interior roots.

CLOSES:
  SINGLE_ENDPOINT_ATOM_AS_RECTANGLE_COUNT_CERTIFICATE

OPENS:
  none

FORBIDDEN:
  general Rouché;
  general argument principle;
  centeredXi;
  numerics;
  sorry/admit;
  new axioms;
  theorem weakening.

VALIDATION:
  WORKDIR q3.lean.aristotle:
    lake env lean Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean
    lake build Q3.Proofs.RouteB.P59SingleEndpointAtomCounterexample

  WORKDIR repo root:
    scripts/q3_check.sh Q3/Proofs/RouteB/P59SingleEndpointAtomCounterexample.lean

EXPECTED AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_KERNEL_GREEN

FAILURE:
  P59_SINGLE_ENDPOINT_ATOM_COUNTEREXAMPLE_LEAN_GAP
```

This directive is not authorization under the present request. The present
write scope is the verdict document only.

## META CLOSEOUT

**What became smaller?**

The vague claim “one endpoint controls a thin rectangle” has been replaced by
the exact minimal demand

\[
\inf_{\partial D}|X|-\sup_{\partial D}|F-X|>0.
\]

**What was killed?**

- a single endpoint value as a rectangle count certificate;
- Laguerre–Pólya propagation applied to centered \(\Xi\) before RH;
- outside-window leakage as a strict endpoint-margin supplier.

**What must not be tried again?**

Do not promote the sampled location of a boundary maximum into a theorem. Do
not use individual vertical modulus monotonicity to control a difference ratio.
Do not interpret \(e(R)\to1\) as a strict Rouché margin.

**Current smallest named gap**

```text
P59_GROUND_XI_FULL_THIN_RECTANGLE_BOUNDARY_MARGIN
```

**Next cheapest decisive test**

Formalize the polynomial endpoint plant above. After that, paper-preflight the
one-node projective decomposition and identify whether any noncircular
endpoint-to-full-boundary propagation theorem exists.

**Prediction score**

The probabilities remain unchanged. The two unrun rectangle predictions remain
unresolved at the request lock. The endpoint/component-I and leakage predictions
are refuted as stated. The polynomial circle argument-principle prediction is
confirmed after restricting the domain from rectangles to circles.

**Memory entry**

```yaml
iteration:
  target: P59 single-endpoint winding lock
  status: FATAL_FOR_THEOREM_SHAPE
  failed_strategy: infer full boundary control from one real endpoint
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: P59_GROUND_XI_FULL_THIN_RECTANGLE_BOUNDARY_MARGIN
  invariant_learned: zero counts require a full boundary certificate
  forbidden_future_move: LP vertical modulus does not control a difference ratio
  next_decisive_test: formalize the endpoint counterexample
```
