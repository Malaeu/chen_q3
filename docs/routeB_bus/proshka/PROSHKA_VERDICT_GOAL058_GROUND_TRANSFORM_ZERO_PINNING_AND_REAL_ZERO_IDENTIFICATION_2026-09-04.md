# STATUS: OPEN — PARTIAL REAL-ZERO PINNING DOES NOT IDENTIFY \(\Xi\); COMPLETE ZERO-DIVISOR CONTROL IS THE NEW ATOM
```yaml
PRIMARY: KILL_PARTIAL_REAL_ZERO_PINNING_AS_XI_IDENTIFICATION
PRIMARY_COUNT: 1
STATUS: OPEN
OPERATIVE_CLASS: TRY_P59_COMPLETE_ZERO_DIVISOR_TIGHTNESS_AND_TARGET_CROSSWALK

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-04-ZEROPIN
  BOUNDARY_ID: GOAL058_GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION
  REQUEST_COMMIT: ea2bffe9f7657e17f3e2b38f894c63a2dbc04041
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_ZERO_PINNING_2026-09-04.txt
  REQUEST_GIT_BLOB: 4e251ccf6205d7c7e8906423e6a2f8be862c50e1
  REQUEST_SHA256: a5f4a85f03dc619b24228eacf8e3a9eb62d59f3e52379c4cd97944b9823fef99
  REQUEST_BYTES: 7846
  REQUEST_LINES: 80
  FINAL_LF: true
  HASH_VERIFIED_FROM_GITHUB_BYTES: true
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION_2026-09-04.md
  REVIEW_BOUNDARY: PAPER_ADJUDICATION_ONLY
  WRITE_SCOPE: VERDICT_DOC_ONLY

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: 764b172ee6c94addc66d00895d841d292f4c802b
  PARENT_VERDICT_QUASIEIGEN: 9b8226246adda225c10bca322d75782c8c98dd5e
  PARENT_VERDICT_SHELLSEARCH: 99927f01a210df283fce15b3e846f595ec1fd629

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

Q1_IDENTIFICATION:
  FROM_BOUNDED_KAPPA_REAL_ZEROS_LOW_ZERO_CONVERGENCE: REJECTED
  SCOPED_KILL: PARTIAL_REAL_ZERO_SET_PLUS_SECOND_JET_DOES_NOT_IDENTIFY_XI
  NORMALITY_FROM_BOUNDED_KAPPA: LEAN_PROVED_FINITE_PRODUCT_BRIDGE
  MISSING_FOR_IDENTIFICATION:
    - local_zero_count_convergence_with_multiplicity
    - excess_zero_tightness_on_every_compact
    - escaping_reciprocal_square_mass_control
    - complete_target_divisor_crosswalk
  ORDER_TWO_GAUGE:
    formula: "G(z) = exp(a*z^2) * X(z)"
    pin: "a = kappa_X - kappa_G"
    second_jet_sufficient_only_after_complete_divisor_equality: true
  ORDER_ONE_VARIANT:
    curvature_needed: false
    current_uniform_order_one_supplier: absent
  ROBIN_COSINE_PLANT:
    excluded: true
    reason: DIFFERENT_ZERO_DIVISOR
  NONSPECTRAL_IDENTIFICATION:
    status: CONDITIONAL_CLOSED_FORM
    exact_boundary: COMPLETE_DIVISOR_EQUALITY_IS_LOAD_BEARING

Q2_ZERO_SUPPLIER:
  GROSKIN_2607_02828:
    finite_dictionary: PAPER_PROVED
    ground_zero_convergence_to_XI: NOT_PROVED
  CCM_THEOREM_5_10:
    finite_ground_transform_real_zeros: PAPER_PROVED_UNDER_SIMPLE_EVEN
    zero_locations_converge_to_XI: NOT_PROVED
  CCM_LEMMA_7_3:
    trial_transform_to_XI: PAPER_PROVED
    same_as_finite_ground_family: false
  CCM_SECTION_8:
    ground_to_trial_zero_convergence: EXPLICITLY_OPEN
  UNCONDITIONAL_ZERO_SUPPLIER:
    available_import: false
    mathematical_impossibility_claimed: false
    status: OPEN_NEW_ANALYTIC
  S9:
    observed_scaling: DIAGNOSTIC_ONLY
    exact_identity_in_audited_sources: NOT_FOUND
    candidate_source_identity: P59_ZETA_ZERO_EVALUATION_RANGE_IDENTITY
    candidate_formula: "evaluationVector(m,N,gamma) = K(m,N) * b(m,N,gamma)"
    consequence_on_ground: "F_ground(gamma) = lambda1 * inner(b, ground)"
    required_bound: "b(m,N,gamma) bounded on each fixed gamma-compact"
    additional_zero_location_input:
      - local_slope_or_boundary_lower_bound
      - multiplicity_and_separation_control
    complete_divisor_supply: false

Q3_NOT_RH_BRANCH:
  HURWITZ_CONTRADICTION_IF_COMPLETE_ZERO_SUPPLIER_EXISTS: true
  FIRST_FAILURE_OF_CURRENT_ARGUMENT: PARTIAL_TO_COMPLETE_DIVISOR_JUMP
  LOW_ONLINE_ZERO_CONVERGENCE_COMPATIBLE_WITH_NOT_RH: true
  COMPLETE_XI_ZERO_CONVERGENCE_FROM_REAL_ROOTS:
    implication: RH
    status: NOT_AN_AVAILABLE_WEAKER_INPUT
  PAPER_ROUTE_FIRST_OPEN_BRIDGE: GROUND_TO_TRIAL_SAME_FAMILY_CONVERGENCE
  ZERO_ROUTE_CLASSIFICATION: VALID_REPRESENTATION_OF_THE_OPEN_BRIDGE_NOT_A_CLOSURE

Q4_LEAN_READY_VS_ANALYTIC:
  LEAN_READY_OR_ALREADY_LEAN:
    - P59 finite Cauchy numerator
    - numerator root implies transform root
    - even real-rooted finite quadratic product
    - node-safe included-factor identity
    - Euler sine tail representation off the real axis
    - exact curvature second jet
    - Gaussian compact envelope from bounded curvature
    - terminal real-zero locally-uniform ZeroEscape consumer
  NEW_ANALYTIC:
    - complete zero-divisor convergence with multiplicity
    - excess-zero escape plus reciprocal-square tightness
    - kappa convergence to the chosen complete target divisor
    - source-specific S9 evaluation-range identity and compact bound
    - target crosswalk from the canonical real-zero product to normalized Xi
  HADAMARD_MATHLIB_REQUIRED: false
  FINITE_PRODUCT_ROUTE_SELECTED: true
  FIRST_LEAN_LOCAL_TARGET: QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND

DISCRIMINATOR:
  name: COMPLETE_ZERO_DIVISOR_TIGHTNESS_ON_COMPACTS
  pass_condition: >-
    For every radius R whose boundary avoids the target divisor, the positive
    P59 zero multiset inside [0,R] matches the target multiset with multiplicity
    for all sufficiently large indices, and the unmatched reciprocal-square
    mass tends to zero.
  zero_consistent_result: INCONCLUSIVE
  partial_low_zero_tracking_is_pass: false

CANDIDATE_REREPRESENTATIONS:
  - code: R1_EXPLICIT_PRODUCT_ZERO_MEASURE_AND_CURVATURE_TIGHTNESS
    rank: PRIMARY_ZERO_ROUTE
    kill_power: 9/10
    proof_cost: 6/10
  - code: R2_P59_EVALUATION_RANGE_IDENTITY
    rank: CHEAPEST_SOURCE_TEST
    kill_power: 8/10
    proof_cost: 4/10
  - code: R3_ANCHORED_LOG_DERIVATIVE_RESOLVENT
    rank: RUNNER_UP
    kill_power: 8/10
    proof_cost: 7/10

PREDICTION_FATES:
  P_ZERO_IDENTIFICATION_CLOSES_INPUT_A:
    probability: 0.55
    fate: REFUTED_AS_STATED
  P_EXCESS_ZEROS_ESCAPE:
    probability: 0.60
    fate: UNRESOLVED
  P_KAPPA_CONVERGES_TO_KAPPA_XI:
    probability: 0.70
    fate: UNRESOLVED
  P_S9_IS_SOURCE_IDENTITY:
    probability: 0.50
    fate: UNRESOLVED_ADVERSE
  P_ZERO_SUPPLIER_UNCONDITIONAL:
    probability: 0.25
    fate: REFUTED_AS_AVAILABLE_IMPORT
  P_JUDGE_NAMES_ZERO_ROUTE_AS_PRIMARY:
    probability: 0.60
    fate: REFUTED

SCOPED_KILLS:
  PARTIAL_REAL_ZERO_SET_PLUS_SECOND_JET:
    code: KILL_PARTIAL_ZERO_JET_XI_UNIQUENESS
    kill_scope: THEOREM_SHAPE
    evidence: "P(z) and P(z)*(1+epsilon*z^4) have the same real zeros, anchor, second jet, parity, reality and order, but different complex zeros"
    epistemic_status: MATHEMATICALLY_DEAD
  SMALL_WEIL_ENERGY_TO_ZERO_PINNING:
    code: DO_NOT_REOPEN_SMALL_ENERGY_POINTWISE_PINNING
    kill_scope: THEOREM_SHAPE
    evidence: PARENT_VERDICT_99927F01
    epistemic_status: MATHEMATICALLY_DEAD_WITHOUT_RH_SIGN
  TRIAL_TO_GROUND_SUBSTITUTION:
    code: DO_NOT_SUBSTITUTE_CCM_LEMMA_7_3_FOR_GROUND_CONVERGENCE
    kill_scope: SOURCE_FAMILY
    evidence: CCM_SECTION_8
    epistemic_status: WRONG_OBJECT

NEXT_LOAD_BEARING_GAP:
  P59_COMPLETE_ZERO_DIVISOR_TIGHTNESS_AND_TARGET_CROSSWALK

CHEAPEST_NEXT_ACTION:
  code: FORMALIZE_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND
  purpose: "make the explicit-product uniqueness route quantitative without Hadamard"

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
`ea2bffe9f7657e17f3e2b38f894c63a2dbc04041`. Its Git blob is
`4e251ccf6205d7c7e8906423e6a2f8be862c50e1`. Independent byte reconstruction
gives exactly 7,846 bytes, 80 LF-terminated lines, and SHA-256
`a5f4a85f03dc619b24228eacf8e3a9eb62d59f3e52379c4cd97944b9823fef99`.
`[ABSTRACT][PAPER]`

The phase key, source family, centered coordinate and terminal consumer remain
unchanged. The convention card fixes the full coefficient ratio \(x_n\), not
the even-coordinate ratio \(y_n=\sqrt2x_n\), as the P59 sampling coordinate.
`[COFINAL_FAMILY][PAPER]`

### Q1 — identification through zeros

The proposed implication from

\[
\sup_k\kappa_k<\infty,\qquad Z(F_k)\subset\mathbb R,\qquad
\rho_{k,j}\to\gamma_j\quad\text{for each fixed low }j
\]

to

\[
\frac{F_k}{F_k(0)}\longrightarrow\frac{\Xi}{\Xi(0)}
\]

is rejected. Bounded curvature gives a normal family through the already
formalized estimate

\[
\left|\frac{F_k(z)}{F_k(0)}\right|\le e^{\kappa_k|z|^2}.
\]

It does not identify a cluster. Low-root convergence only forces the listed
\(\pm\gamma_j\) to be zeros of a cluster; it neither excludes additional
bounded real zeros nor controls a cloud of roots escaping to infinity.
`[COFINAL_FAMILY][LEAN]`

The exact Hadamard-level theorem is narrower:

> Let \(G\) and \(X\) be normalized even real entire functions of finite order
> at most two. If their **complete zero divisors agree with multiplicity**, then
> \(G(z)=e^{a z^2}X(z)\) for a real constant \(a\). If additionally
> \[
> -\frac{G''(0)}2=-\frac{X''(0)}2,
> \]
> then \(a=0\) and \(G=X\).

Here \(G(0)=X(0)=1\), and

\[
a=\kappa_X-\kappa_G.
\]

Thus the second jet pins the quadratic zero-free gauge only **after** complete
divisor equality is known. `[ABSTRACT][PAPER]`

If a uniform order-at-most-one theorem were available, the zero-free factor
would have degree at most one; evenness and normalization would already kill
it. The present Gaussian envelope supplies order at most two, not a uniform
order-one bound, because the individual exponential types grow with \(L_k\).
`[COFINAL_FAMILY][PAPER]`

The Robin-cosine plant is outside the repaired theorem: it may agree on the
sampled lattice, but it has a different zero divisor. No value-based selector
is used. `[ABSTRACT][PAPER]`

The decisive boundary is the word **complete**. If \(\{\pm\gamma_j\}\) denotes
only the known critical-line zeros of \(\Xi\), then

\[
Z(\Xi)=\{\pm\gamma_j\}
\]

is already RH. It cannot be inserted as an identification hypothesis while
calling the supplier unconditional. `[ABSTRACT][PAPER]`

### Finite-product repair of Q1

Generic Hadamard factorization is unnecessary for the source family. The
project already proves the exact ingredients of a source-specific product: a
removable-node-safe finite identity and convergence of the Euler sine tail off
the real axis. It does **not** yet expose one global normalized product equality
at every removable node. The intended representation is

\[
\frac{F_k(z)}{F_k(0)}=
\prod_{\rho\in R_k^+}\left(1-\frac{z^2}{\rho^2}\right)
\prod_{n>N_k}\left(1-\frac{z^2}{x_{k,n}^2}\right),
\]

with the equality obtained from the node-safe identity rather than illegal
cancellation. The project also proves the reciprocal-square curvature ledger.
`[FINITE_CELL][LEAN]`

A Hadamard-free cofinal theorem can use three exact inputs:

1. local multiset convergence of roots, with multiplicity;
2. escape of every unmatched bounded root;
3. vanishing unmatched reciprocal-square mass.

The third input removes the residual factor \(e^{-a z^2}\) generated by many
roots escaping together. “Each excess zero tends to infinity” does not control
their collective mass. `[COFINAL_FAMILY][PAPER]`

This identifies the limit with the canonical product of the prescribed real
divisor. A separate theorem must identify that product with
\(\Xi/\Xi(0)\). If the divisor lists only on-line zeros, that separate theorem
is RH-equivalent. `[ABSTRACT][PAPER]`

### Q2 — supplier for zero convergence

Groskin, arXiv:2607.02828, Theorem 2.5 proves an exact finite
Guinand-Weil dictionary:

\[
\langle v,Q_\infty v\rangle=\sum_\rho g_v(\rho)
\]

for the induced finite test function \(g_v\). It does not state that zeros of
the P59 ground transform converge to zeros of \(\Xi\).
`[FINITE_CELL][PAPER]`

CCM Theorem 5.10 proves that a simple-even finite ground vector has an entire
transform with only real zeros. CCM Lemma 7.3 proves locally uniform
trial-transform convergence to \(\Xi\). Section 8 explicitly names the missing
step: the prolate trial must approximate the actual Weil ground state strongly
enough to justify convergence of the ground-transform zeros. These are
different families until that bridge is proved. `[COFINAL_FAMILY][PAPER]`

No unconditional zero-convergence supplier was found in the cited sources.
This is a result about the available theorem corpus, not a claim of
mathematical impossibility. `[COFINAL_FAMILY][PAPER]`

The S9 observation suggests one exact algebraic mechanism. Let
\(e_{m,N,\gamma}\) represent P59 evaluation at \(\gamma\). If

\[
e_{m,N,\gamma}=K_{m,N}b_{m,N,\gamma},
\]

then for \(K_{m,N}\xi_{m,N}=\lambda_{1,m,N}\xi_{m,N}\),

\[
F_{m,N}(\gamma)=
\lambda_{1,m,N}\langle b_{m,N,\gamma},\xi_{m,N}\rangle.
\]

This is the exact theorem shape that would explain the measured
\(F_k(\gamma)=\lambda_1G_k(\gamma)\). No such range identity was found in the
audited project or papers. `[FINITE_CELL][CONDITIONAL]`

A compact bound on \(b_{m,N,\gamma}\) makes \(G_k(\gamma)\) bounded, but a small
value at \(\gamma\) alone does not prove a nearby zero. A local slope lower
bound, or a Rouché boundary lower bound with multiplicity control, is also
required. `[COFINAL_FAMILY][PAPER]`

Pinning each fixed on-line zero is not complete divisor convergence. It does
not address a hypothetical off-line zero of \(\Xi\). `[ABSTRACT][PAPER]`

### Q3 — the not-RH branch

If an unconditional theorem said that **every** zero of \(\Xi\) in every
compact is the limit, with multiplicity, of zeros of the same real-zero ground
family, RH would follow immediately: a limit of real numbers is real. That is
the intended Hurwitz contradiction. `[ABSTRACT][PAPER]`

The current argument fails earlier. The measured supplier tracks selected
known on-line zeros. Such tracking is compatible with not-RH: \(\Xi\) could
possess additional nonreal zeros that the ground zeros never approach. The
first invalid step is

\[
\text{selected low on-line zeros converge}
\Longrightarrow
\text{the complete zero divisor of the limit is }Z(\Xi).
\]

`[COFINAL_FAMILY][PAPER]`

In CCM, the finite real-zero theorem and trial-to-\(\Xi\) theorem concern
different families. The missing ground-to-trial same-family convergence is
where the contradiction must be earned. The zero route is a valid
re-representation of that open bridge, not a shortcut around it.
`[COFINAL_FAMILY][PAPER]`

### Q4 — Lean-ready versus new analysis

The project already has Lean theorems for the finite Cauchy numerator, its real
roots, the removable-node-safe product, the Euler tail off the real axis, the
second jet, the curvature sum, and the Gaussian compact envelope. Generic
Hadamard or Laguerre-Pólya APIs are not needed for the next local step.
`[FINITE_CELL][LEAN]`

The genuinely new analytic suppliers are cofinal:

- complete zero-count convergence on every compact, with multiplicity;
- reciprocal-square tightness of unmatched roots;
- convergence of curvature to the complete target divisor;
- the S9 evaluation-range identity and compact bound;
- the source-faithful crosswalk from the canonical product to normalized
  \(\Xi\).

`[COFINAL_FAMILY][CONDITIONAL]`

The first useful Lean lemma is the elementary bound

\[
\left|\prod_{a\in c}(1-a z^2)-1\right|
\le
\exp\!\left(|z|^2\sum_{a\in c}a\right)-1,
\qquad a\ge0.
\]

With \(a=\rho^{-2}\), reciprocal-square tightness becomes uniform product-tail
control on compact balls. This is the finite-product replacement for
Hadamard. `[ABSTRACT][PAPER]`

## FINAL PROPOSAL

Do not promote the zero route to the primary proof front. Preserve it as a
high-value secondary representation with one discriminator:

```text
COMPLETE_ZERO_DIVISOR_TIGHTNESS_ON_COMPACTS
```

A pass requires eventual zero-count agreement with multiplicity on every
compact and vanishing unmatched reciprocal-square mass. Tracking finitely many
or each fixed on-line zero without completeness remains `INCONCLUSIVE`.
`[COFINAL_FAMILY][CONDITIONAL]`

The cheapest source-changing test is the S9 range identity

\[
e_{m,N,\gamma}=K_{m,N}b_{m,N,\gamma}.
\]

It can explain the \(\lambda_1\)-scale without a complement-gap estimate and
can produce a rigorous low-zero supplier when paired with a local Rouché/slope
bound. It cannot close the complete-divisor gap by itself.
`[FINITE_CELL][CONDITIONAL]`

Registered failure response:

```text
if only selected on-line roots are pinned:
  keep a compact zero-location theorem;
  do not identify the cluster with Xi.

if unmatched reciprocal-square mass does not vanish:
  record the surviving Gaussian factor exp(-a z^2);
  do not increase computation.

if complete Xi-divisor convergence is proposed as an assumption:
  classify it as an RH-strength supplier, not a lower-cost bridge.
```

## STRONGEST ATTACK

Let \(P\) be any normalized even real entire function whose zeros are all real.
For \(\varepsilon>0\), set

\[
X_\varepsilon(z)=P(z)(1+\varepsilon z^4).
\]

Then

\[
X_\varepsilon(0)=P(0)=1,\qquad X_\varepsilon''(0)=P''(0),
\]

and \(X_\varepsilon\) has the same real zeros as \(P\), with the same
multiplicities. It is even and real on the real axis; multiplication by a
polynomial does not increase a positive finite order. But
\(1+\varepsilon z^4\) contributes four nonreal zeros.

Therefore

\[
\boxed{
\text{same real zeros + same anchor + same second jet + same order}
\not\Rightarrow
\text{same entire function}.}
\]

`[ABSTRACT][PAPER]`

This kills Q1 as stated. The weakest repair is **complete complex zero-divisor
equality**, not convergence of known real zeros. Once complete divisor equality
holds, the order-two zero-free gauge is quadratic exponential and the second
jet pins it. `[ABSTRACT][PAPER]`

## CODEX DIRECTIVE

```text
TASK: FORMALIZE_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND

Boundary:
- one local Lean theorem;
- no route promotion;
- no Xi theorem;
- no zero-convergence assumption;
- no Hadamard/Weierstrass API;
- no new sorry, admit, axiom or opaque constant.

Target file:
q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean

Target mathematical content:

  theorem norm_quadProduct_sub_one_le_exp_sub_one
      (c : Multiset ℝ)
      (hc : ∀ a ∈ c, 0 ≤ a)
      (z : ℂ) :
      ‖(c.map (fun a : ℝ => 1 - (a : ℂ) * z ^ 2)).prod - 1‖
        ≤ Real.exp (‖z‖ ^ 2 * c.sum) - 1

A harmless algebraic reformulation is allowed only if it preserves the
inequality direction and the zero-at-empty-tail behavior.

Proof route:
1. Induct on the multiset or use a telescoping product identity.
2. Prove ‖prod(1+w_i)-1‖ ≤ prod(1+‖w_i‖)-1.
3. Apply the finite exponential product bound with ‖w_i‖=a_i‖z‖².
4. Do not invoke any infinite product or entire-function factorization.

Mandatory plants:
A. empty multiset gives 0 = 0;
B. singleton exposes the scale a*‖z‖²;
C. a negative coefficient is rejected unless the theorem is explicitly
   repaired with absolute values;
D. z = 0 gives 0 = 0.

Validation:
  lake env lean \
    Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean

  lake build \
    Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge

  scripts/q3_check.sh \
    Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean

Success code:
  P59_QUAD_PRODUCT_TAIL_SUB_ONE_EXP_BOUND_LEAN

Failure code:
  P59_QUAD_PRODUCT_TAIL_BOUND_API_OR_DIRECTION_MISMATCH

Report:
- exact theorem type;
- files touched;
- commands and stdout;
- axiom profile;
- whether all four plants compile;
- next missing cofinal theorem, without claiming it proved.
```

## META CLOSEOUT

**What became smaller?**

```text
vague Hadamard uniqueness
→ finite-product tail control
+ complete zero-divisor tightness
+ explicit target crosswalk.
```

`[ABSTRACT][PAPER]`

**What was killed?**

```text
bounded curvature
+ real zeros
+ convergence of selected low real zeros
+ matching second jet
=> Xi
```

is mathematically dead. `[ABSTRACT][PAPER]`

**What must not be tried again?**

Do not infer absence of off-line zeros from convergence of known on-line zeros.
Do not use Groskin's zero-sum dictionary or CCM Lemma 7.3 as a ground-zero
convergence theorem. `[COFINAL_FAMILY][PAPER]`

**Current smallest named gap**

```text
P59_COMPLETE_ZERO_DIVISOR_TIGHTNESS_AND_TARGET_CROSSWALK
```

`[COFINAL_FAMILY][CONDITIONAL]`

**Next cheapest decisive test**

```text
P59_ZETA_ZERO_EVALUATION_RANGE_IDENTITY:
  evaluationVector = K * boundedPreimage
```

This decides whether S9 is a source identity or only a finite-cell numerical
law. `[FINITE_CELL][CONDITIONAL]`

**Fate of prior registered predictions**

Two predictions are refuted as stated, three remain unresolved, and one is
refuted as an available import. No probability or theorem statement was
retroactively repaired. `[ABSTRACT][PAPER]`

**Memory entry**

```yaml
iteration:
  target: identify normalized P59 ground-transform clusters from zero data
  status: PROGRESS
  failed_strategy: partial real-zero set plus curvature/second jet
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  new_gap_name: P59_COMPLETE_ZERO_DIVISOR_TIGHTNESS_AND_TARGET_CROSSWALK
  invariant_learned: complete zero divisor with multiplicity is distinct from the real-zero subset
  forbidden_future_move: treat convergence of known on-line zeros as convergence of the Xi divisor
  next_decisive_test: derive or kill evaluationVector = K * boundedPreimage
```
