# STATUS: CONDITIONAL — P59 EXPLICIT-PRODUCT CURVATURE BRIDGE PAPER-PROVED; STANDARD HILBERT–SCHMIDT IDENTITY REPAIRED BY A FACTOR 1/2
```yaml
PRIMARY: FORMALIZE_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE
PRIMARY_COUNT: 1
STATUS: CONDITIONAL
OPERATIVE_CLASS: FORMALIZE_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE

REQUEST_LOCK:
  REQUEST_ID: REQ-2026-09-03-CURVBRIDGE
  BOUNDARY_ID: GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION
  REQUEST_COMMIT: 851a79702d6e9b5d77ebdebb70f478bcb301bb97
  REQUEST_PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.txt
  REQUEST_GIT_BLOB: 9e2853367058fcebec86bc4181d8427dd20d7fed
  REQUEST_SHA256: c56b427d1de7bcbaaa4e77b27d62d58ce907daf2b3bc869be99733dc6c7f864b
  REQUEST_BYTES: 8118
  REQUEST_LINES: 121
  FINAL_LF: true
  ATTACHMENT_MATCHES_COMMITTED_BYTES: true

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SOURCE_BASE_COMMIT: c8fc4cdbba005d9c87cf08b13d8421b9b9f6bdc7
  PARENT_VERDICT_CURVRITZ: 0c0a2b37dadea72fff0e3a9048b05bc36d3a98f3
  PARENT_VERDICT_SCHURLOEWNER: d7c7df3681d1031df55a3c0622e64dc8a3afbd73
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.md

PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_G1_G3_COFINAL_GROUND_TRACKING
  SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_BOTTOM_GROUND_FAMILY
  TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false

PART_1:
  P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE:
    status: PAPER_PROVED_AT_LEAN_GRANULARITY
    scope: FINITE_CELL
    verifier: PAPER
    lean_kernel_status: NOT_RUN
    generic_hadamard_factorization_required: false
    mathlib_gap: NONE
  KAPPA_TYPE_REPAIR:
    kappa_type: REAL
    complex_identity: "-iteratedDeriv 2 F 0 / (2 * F 0) = (kappa_F : Complex)"
    nonnegative: true
  REQUIRED_MATHLIB_FACTS:
    - Complex.tendsto_euler_sin_prod
    - Polynomial.Splits.eq_prod_roots_of_monic
    - Polynomial.Splits.eval_eq_prod_roots_of_monic
    - Real.prod_one_add_le_exp_sum
    - hasSum_zeta_two
  LOCAL_GLUE_LEMMAS:
    - P59_FINITE_CAUCHY_NUMERATOR_IDENTITY
    - P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT
    - P59_REMOVABLE_LATTICE_PRODUCT_EXTENSION
    - P59_EULER_TAIL_SECOND_JET
  ROOF_CONSEQUENCE:
    bounded_kappa_subsequence_implies_local_boundedness_on_C: true
    supplies_normal_family_input: true
    supplies_cofinal_kappa_bound: false

PART_2:
  THEOREM_5_10_SPECTRUM:
    space: "E'_N direct_sum E_N_perp"
    finite_block_metric: "restriction of QW_lambda^N - epsilon_N <.,.>"
    full_zero_divisor_equals_full_spectrum: true
    forced_lattice_is_spectrum: true
  HS_IDENTITY_AS_REQUESTED:
    status: REFUTED_FACTOR_TWO
    reason: "standard HS norm counts both +mu and -mu, while kappa sums one positive representative from each even pair"
  HS_IDENTITY_REPAIRED:
    formula: "kappa_F = (1/2) * norm_HS((D_log^(lambda,N))^(-1))^2"
    assumptions:
      - even ground row
      - F(0) != 0
      - Theorem 5.10 spectrum-with-multiplicity correspondence
    scope: FINITE_CELL
    verifier: PAPER
  FORCED_PART:
    positive_half: "(L^2/(4*pi^2)) * sum_{k>N} 1/k^2"
    full_HS: "(L^2/(2*pi^2)) * sum_{k>N} 1/k^2"
    production_schedule_limit: ZERO
  NAIVE_KERNEL_ATTACK:
    status: REJECTED_AS_TYPED
    reason: "ordinary L2 kernel norm is not the HS norm for the modified finite-block metric"
  HS_SOURCE_BOUND:
    status: OPEN
    first_gap: MODIFIED_METRIC_GREEN_KERNEL_OR_TRACE_BOUND_WITHOUT_COMPLEMENT_FLOOR

REPRESENTATION_RANKING:
  1:
    code: R_SECULAR_BORDERED_SLOPE
    status: PRIMARY_ANALYTIC_ATTACK
    kill_power: 9/10
    cost: 3/10
  2:
    code: R_HS_REDUCED_DIRAC_TRACE
    status: EXACT_REPRESENTATION_OPEN_BOUND
    kill_power: 8/10
    cost: 6/10
  3:
    code: R_ZERO_LEDGER_REPULSION_COUNTING
    status: EXACT_REPRESENTATION_OPEN_BOUND
    kill_power: 7/10
    cost: 8/10

SCOPED_KILLS:
  KAPPA_EQUALS_FULL_HS_NORM_SQUARED:
    CODE: KILL_HS_IDENTITY_WITHOUT_HALF_FACTOR
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: EXACT_SYMMETRIC_SPECTRAL_MULTIPLICITY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  ORDINARY_L2_GREEN_KERNEL_COMPUTES_MODIFIED_HS:
    CODE: KILL_NAIVE_FREE_DIRAC_KERNEL_NORM
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: SOURCE_METRIC_MISMATCH
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  LEMMA_7_3_GIVES_GROUND_ZERO_REPULSION:
    CODE: KILL_TRIAL_TO_GROUND_ZERO_REPULSION_SUBSTITUTION
    KILL_SCOPE: THEOREM_SHAPE
    KILL_EVIDENCE_KIND: WRONG_SOURCE_FAMILY
    EPISTEMIC_STATUS: MATHEMATICALLY_DEAD

Q2_3:
  BOUNDED_KAPPA_IMPLIES_UNIFORM_ZERO_FREE_RADIUS: true
  ZERO_FREE_RADIUS_ALONE_IMPLIES_BOUNDED_KAPPA: false
  ADDITIONAL_REQUIREMENT: UNIFORM_INVERSE_SQUARE_COUNTING_OR_TRACE_BOUND
  TRIAL_LEMMA_7_3: WRONG_FAMILY_FOR_GROUND_ZERO_REPULSION
  FINITE_DIRAC_REAL_SPECTRUM: INSUFFICIENT_FOR_UNIFORM_INVERTIBILITY
  FIRST_EXACT_FAILURE: REDUCED_FINITE_BLOCK_UNIFORM_ZERO_FREE_BOUND_MISSING

PREDICTION_FATES:
  P_EXPLICIT_PRODUCT_BRIDGE_PROOF:
    probability: 0.85
    fate: CONFIRMED_AT_PAPER_LEAN_GRANULARITY
    note: "Pinned Mathlib contains the Euler sine product, polynomial split/product facts, the finite exponential product bound, and Basel sum."
  P_HS_REPRESENTATION_EXACT:
    probability: 0.80
    fate: REFUTED_AS_STATED
    note: "The exact standard identity is kappa_F = one_half times HS-norm-squared."
  P_HS_ATTACK_FOUND:
    probability: 0.25
    fate: UNRESOLVED_ADVERSE
    note: "The obvious ordinary-L2 Green-kernel route is invalid in the modified metric; no cheaper gap-free uniform bound was recovered."

CHEAPEST_NEXT_ACTION:
  code: CODEX_FORMALIZE_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE
  duplicate_work: false
  target_file: q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  closes:
    - P59_SPECIFIC_CURVATURE_TO_LOCAL_BOUNDEDNESS
    - CODEX_ITEM_5_MATHLIB_GAP_NAMED
  opens: []
  falsifier:
    code: P59_PRODUCT_BRIDGE_REMOVABLE_NODE_MISMATCH
    condition: "The proposed normalized product disagrees with exact P59 sampling at any included lattice node."
  success:
    code: P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE_KERNEL_GREEN
    condition: "The exact product, zero-sum curvature, nonnegativity, and compact envelope compile with the standard axiom triple."

NEXT_ANALYTIC_GAP:
  P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND

DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
  ACTUAL_CONSUMER_REQUIREMENT: "The same normalized entire real-zero family converges locally uniformly to centeredXi."
  ORIGINAL_REQUESTED_OBJECT: "generic order-at-most-one Hadamard curvature bridge"
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACE: "P59 explicit finite-polynomial times Euler-tail product"
  FAILURE_TYPE: FORMALIZATION_COST
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "source-specific explicit zero divisor"
  REMAINING_RESEARCH_DEBT: "uniform cofinal source bound on kappa for the same ground family"

CANDIDATE_REPRESENTATIONS:
  R_HS_KREIN_TRACE:
    kill_power: 8/10
    cost: 6/10
    discriminator: "derive a rank-one resolvent-trace formula whose L-scaled terms cancel before any metric comparison"
  R_ZERO_COUNTING_JENSEN:
    kill_power: 7/10
    cost: 8/10
    discriminator: "prove one common-path zero-free radius plus a uniform spectral counting law strong enough for the inverse-square sum"

LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
JUDGE_KERNEL_RERUN: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID

PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
CURRENT_SMALLEST_GAP: P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND
```

## ROUTE MAP

| Object | Verdict | Decisive statement | Residual risk | Tags |
|---|---|---|---|---|
| P59 explicit-product curvature bridge | **Paper-proved at Lean granularity** | Exact finite polynomial product times Euler sine tail | Local root-pairing and removable-node glue still need a kernel run | `[FINITE_CELL][PAPER]` |
| Bounded curvature → local boundedness | **Proved once the bridge is imported** | \(\|F(z)/F(0)\|\le e^{\kappa_F\|z\|^2}\) | Does not provide the cofinal bound on \(\kappa_F\) | `[ABSTRACT][PAPER]` |
| Bordered secular slope | **Primary analytic representation** | \(\partial_t\Phi(0,\lambda_1)=O(L^{-2})\) before taking a resolvent norm | May merely rename the same cancellation | `[COFINAL_FAMILY][CONDITIONAL]` |
| Reduced Dirac Hilbert–Schmidt trace | **Exact after factor-\(1/2\) repair** | \(\kappa_F=\frac12\|D^{-1}\|_{\mathrm{HS}}^2\) | Correct HS metric is nonstandard on the finite quotient block | `[FINITE_CELL][PAPER]` |
| Positive-zero ledger | **Exact, least attackable** | Uniform inverse-square zero sum | No source theorem gives ground zero repulsion plus uniform counting | `[COFINAL_FAMILY][CONDITIONAL]` |

## 1. Source lock

The authoritative request is `REQ-2026-09-03-CURVBRIDGE`, boundary
`GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION`, fixed by request commit
`851a79702d6e9b5d77ebdebb70f478bcb301bb97`, Git blob
`9e2853367058fcebec86bc4181d8427dd20d7fed`, and SHA-256
`c56b427d1de7bcbaaa4e77b27d62d58ce907daf2b3bc869be99733dc6c7f864b`.

The six-field phase key is unchanged. The source object is still the Proposition-59 transform of the finite CCM bottom-ground row, and the terminal consumer is still
`Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi`. `[COFINAL_FAMILY][PAPER]`

At the source pin, Lean already provides:

- the globally entire removable-pole transform;
- exact sampling at every finite lattice node;
- \(F(0)=\sqrt L\,v_0\);
- the exact second jet at zero;
- the \(1/80\) second-jet functional bound;
- the conditional real-zero transfer for the same CCM transform.

These facts are source-locked finite suppliers. `[FINITE_CELL][LEAN]`

## 2. Part 1 — exact P59 curvature bridge

### 2.1 Correct Lean-typed theorem

The request writes
\[
\kappa_F=-\frac{F''(0)}{2F(0)}\ge0.
\]

In Lean, the quotient on the right is complex and cannot itself carry `≤`. The exact typed statement must introduce a real number \(\kappa_F\) and prove the complex coercion identity:

\[
\boxed{
-\frac{F''(0)}{2F(0)}=(\kappa_F:\mathbb C),
\qquad
0\le\kappa_F.
}
\]

Let
\[
I_N=\{-N,\ldots,N\},\qquad x_k=\frac{2\pi k}{L},
\]
and let
\[
F(z)=L^{-1/2}\sum_{k\in I_N}v_k\,K_{L,k}(z),
\]
where \(v_k\in\mathbb R\), \(v_{-k}=v_k\), and \(K_{L,k}\) is the canonical removable kernel.

Then there is a finite multiset \(R_N^+\) of positive real numbers, the positive roots with multiplicity of the finite Cauchy numerator, such that

\[
\boxed{
\kappa_F
=
\sum_{\rho\in R_N^+}\frac1{\rho^2}
+
\frac{L^2}{4\pi^2}\sum_{k>N}\frac1{k^2}
}
\]

and, for every \(z\in\mathbb C\),

\[
\boxed{
\|F(z)\|
\le
\|F(0)\|
\exp\!\left(\kappa_F\|z\|^2\right).
}
\]

Moreover,

\[
\boxed{
\kappa_F
=
\frac{L^2}{2}
\left[
\frac1{12}
+
\frac{1}{2\pi^2v_0}
\sum_{\substack{k\in I_N\\k\ne0}}\frac{v_k}{k^2}
\right].
}
\]

The assumptions are used exactly as follows:

- \(L>0\): distinct real lattice, nonzero square-root normalization, and Euler scaling;
- real coefficients: the finite numerator has real coefficients;
- evenness \(v_{-k}=v_k\): the finite numerator and \(F\) are even, so roots pair as \(\pm\rho\);
- `ZerosRealOn Set.univ F`: every root of the finite numerator is real;
- \(F(0)\ne0\): \(v_0\ne0\), the finite numerator is nonzero at zero, and normalization by \(F(0)\) is legal.

`N ≥ 1` is retained because the request fixes it, although the argument has a harmless \(N=0\) specialization. `[FINITE_CELL][PAPER]`

### 2.2 Finite Cauchy numerator

Define

\[
D_N(z)=\prod_{k\in I_N}(z-x_k),
\]

\[
P_N(z)=
\sum_{k\in I_N}
v_k\prod_{\substack{j\in I_N\\j\ne k}}(z-x_j).
\]

For \(z\notin\{x_k:k\in I_N\}\),

\[
\sum_{k\in I_N}\frac{v_k}{z-x_k}
=
\frac{P_N(z)}{D_N(z)}.
\]

This is the finite identity obtained by multiplying each summand by \(D_N(z)\). Each summand in \(P_N\) has degree \(2N\), hence
\[
\deg P_N\le2N.
\]

No infinite-function theorem enters here. `[FINITE_CELL][PAPER]`

At an included lattice point \(x_j\),

\[
P_N(x_j)
=
v_j\prod_{k\ne j}(x_j-x_k).
\]

All factors in the product are nonzero. Therefore

\[
P_N(x_j)=0
\quad\Longleftrightarrow\quad
v_j=0.
\]

The exact removable-node sampling theorem gives

\[
F(x_j)=\sqrt L\,(-1)^jv_j.
\]

Consequently, every root of \(P_N\), including a root coinciding with an included lattice point, is a root of \(F\). Hence `ZerosRealOn Set.univ F` forces every complex root of \(P_N\) to be real. This removable-node branch is mandatory; proving the quotient formula only off the lattice is insufficient. `[FINITE_CELL][PAPER]`

### 2.3 Evenness and finite real-root product

The denominator \(D_N\) is odd because its factors are \(z\) and
\((z-x_k)(z+x_k)=z^2-x_k^2\).

The Cauchy sum is odd:

\[
\sum_k\frac{v_k}{-z-x_k}
=
-\sum_k\frac{v_{-k}}{z-x_k}
=
-\sum_k\frac{v_k}{z-x_k}.
\]

Thus \(P_N=D_N\cdot(\text{Cauchy sum})\) is even away from a finite set. Polynomial identity then gives

\[
P_N(-z)=P_N(z)
\]

for every \(z\).

The central formula gives \(F(0)=\sqrt L\,v_0\); hence \(F(0)\ne0\) implies \(v_0\ne0\). Also,

\[
P_N(0)
=
v_0\prod_{k\ne0}(-x_k)\ne0.
\]

Thus zero is not a root of \(P_N\). Since \(P_N\) is even and all its roots are real, its roots occur in pairs
\(\pm\rho\) with equal multiplicity. If \(R_N^+\) lists the positive roots with multiplicity, then

\[
\boxed{
\frac{P_N(z)}{P_N(0)}
=
\prod_{\rho\in R_N^+}
\left(1-\frac{z^2}{\rho^2}\right).
}
\]

At the Mathlib level, monic normalization followed by

```text
Polynomial.Splits.eq_prod_roots_of_monic
Polynomial.Splits.eval_eq_prod_roots_of_monic
```

supplies the finite factorization. The only project-local glue is the multiset pairing of the roots of an even, nonzero-at-zero, real-rooted polynomial. That is a local finite-polynomial lemma, not a missing library theory. `[FINITE_CELL][PAPER]`

### 2.4 Euler tail and exact normalized product

For \(M\ge N\), write

\[
T_{N,M}(z)
=
\prod_{k=N+1}^{M}
\left(1-\frac{z^2}{x_k^2}\right).
\]

With \(w=Lz/(2\pi)\), Mathlib's theorem

```text
Complex.tendsto_euler_sin_prod
```

states

\[
\pi w\prod_{k=1}^{M}
\left(1-\frac{w^2}{k^2}\right)
\longrightarrow
\sin(\pi w).
\]

After the substitution \(w=Lz/(2\pi)\),

\[
\frac{\sin(zL/2)}{zL/2}
=
\lim_{M\to\infty}
\prod_{k=1}^{M}
\left(1-\frac{z^2}{x_k^2}\right).
\]

Off the included lattice, the exact Cauchy formula and the value at zero give

\[
\frac{F(z)}{F(0)}
=
\frac{P_N(z)}{P_N(0)}
\frac{\sin(zL/2)}{zL/2}
\prod_{k=1}^{N}
\left(1-\frac{z^2}{x_k^2}\right)^{-1}.
\]

Hence

\[
\boxed{
\frac{F(z)}{F(0)}
=
\prod_{\rho\in R_N^+}
\left(1-\frac{z^2}{\rho^2}\right)
\lim_{M\to\infty}T_{N,M}(z).
}
\]

Both sides are continuous. The complement of the finite included lattice is dense, so the identity extends to all \(z\), including removable nodes. This extension must be explicit in Lean; cancellation under a quotient is not allowed at a node where its denominator vanishes. `[FINITE_CELL][PAPER]`

A useful negative plant is the even row with \(N=1\), \(v_0=1\), and \(v_{\pm1}=0\). Then
\(F(z)/F(0)=\sin(zL/2)/(zL/2)\), while the finite polynomial contributes exactly the two included factors at \(\pm x_1\). Any implementation that starts the remaining product at \(k=1\) or loses the removable-node contribution fails this plant.

### 2.5 Product bound

For real \(r\ne0\),

\[
\left|1-\frac{z^2}{r^2}\right|
\le
1+\frac{\|z\|^2}{r^2}
\le
\exp\!\left(\frac{\|z\|^2}{r^2}\right).
\]

The first inequality is the triangle inequality and
\(\|z^2\|=\|z\|^2\). The second is `Real.add_one_le_exp`; for finite products the bundled theorem

```text
Real.prod_one_add_le_exp_sum
```

closes the exponential estimate.

Therefore

\[
\left|
\prod_{\rho\in R_N^+}
\left(1-\frac{z^2}{\rho^2}\right)
\right|
\le
\exp\!\left(
\|z\|^2\sum_{\rho\in R_N^+}\rho^{-2}
\right),
\]

and

\[
|T_{N,M}(z)|
\le
\exp\!\left(
\|z\|^2\sum_{k=N+1}^{M}x_k^{-2}
\right).
\]

Letting \(M\to\infty\) gives

\[
\left|\lim_M T_{N,M}(z)\right|
\le
\exp\!\left(
\|z\|^2\sum_{k>N}x_k^{-2}
\right).
\]

Multiplying the two bounds proves

\[
\left|\frac{F(z)}{F(0)}\right|
\le
e^{\kappa_F\|z\|^2}.
\]

No generic Hadamard factorization, entire-function order predicate, or Laguerre–Pólya library is needed. `[FINITE_CELL][PAPER]`

### 2.6 Exact curvature identity

The finite product gives

\[
\left(\frac{P_N}{P_N(0)}\right)'(0)=0,
\qquad
\left(\frac{P_N}{P_N(0)}\right)''(0)
=
-2\sum_{\rho\in R_N^+}\rho^{-2}.
\]

For the full sine product,

\[
\frac{\sin(zL/2)}{zL/2}
=
1-\frac{L^2z^2}{24}+O(z^4),
\]

so its second derivative at zero is \(-L^2/12\). The finite inverse product contributes

\[
2\sum_{k=1}^{N}x_k^{-2}.
\]

Mathlib's

```text
hasSum_zeta_two
```

gives

\[
\sum_{k\ge1}\frac1{k^2}=\frac{\pi^2}{6},
\]

and therefore

\[
\sum_{k\ge1}x_k^{-2}
=
\frac{L^2}{4\pi^2}\frac{\pi^2}{6}
=
\frac{L^2}{24}.
\]

Hence the tail factor has second derivative

\[
-2\sum_{k>N}x_k^{-2}.
\]

All first derivatives at zero vanish. Differentiating the product at zero therefore yields

\[
\frac{F''(0)}{F(0)}
=
-2\left(
\sum_{\rho\in R_N^+}\rho^{-2}
+
\sum_{k>N}x_k^{-2}
\right).
\]

Define

\[
\kappa_F
=
\sum_{\rho\in R_N^+}\rho^{-2}
+
\sum_{k>N}x_k^{-2}.
\]

Then

\[
-\frac{F''(0)}{2F(0)}=(\kappa_F:\mathbb C),
\qquad
\kappa_F\ge0.
\]

Finally, the existing exact Lean formulas

\[
F(0)=\sqrt L\,v_0
\]

and

\[
F''(0)
=
-L^2\sqrt L
\left[
\frac{v_0}{12}
+
\frac1{2\pi^2}
\sum_{\substack{k\in I_N\\k\ne0}}\frac{v_k}{k^2}
\right]
\]

give

\[
\boxed{
\frac{L^2}{2}
\left[
\frac1{12}
+
\frac1{2\pi^2v_0}
\sum_{\substack{k\in I_N\\k\ne0}}\frac{v_k}{k^2}
\right]
=
\sum_{\rho\in R_N^+}\rho^{-2}
+
\frac{L^2}{4\pi^2}\sum_{k>N}k^{-2}.
}
\]

This proves the requested P59 bridge on paper at the granularity required for a Lean transaction. `[FINITE_CELL][PAPER]`

### 2.7 Roof consequence

Let \(G_j=F_j/F_j(0)\) on any subsequence for which

\[
\sup_j\kappa_{F_j}\le C<\infty.
\]

For a compact \(K\subset\mathbb C\), put

\[
R_K=\sup_{z\in K}\|z\|.
\]

Then

\[
\sup_j\sup_{z\in K}|G_j(z)|
\le
e^{CR_K^2}.
\]

Thus the normalized family is locally uniformly bounded on all of \(\mathbb C\), and therefore on the centered critical strip. This supplies the normal-family input to Vitali/Montel. It does not prove the cofinal estimate
\(\sup_j\kappa_{F_j}<\infty\); that remains the source wall. `[ABSTRACT][PAPER]`

## 3. Part 2 — the exact Hilbert–Schmidt representation

### 3.1 What Theorem 5.10 actually identifies

Under the simple-even hypothesis and the normalization \(\delta_N(\xi)=1\), CCM Theorem 5.10 realizes
\(D_{\log}^{(\lambda,N)}\) as selfadjoint on

\[
\mathcal H_{\lambda,N}
=
E'_N\oplus E_N^\perp,
\qquad
E'_N=E_N/\mathbb C\xi,
\]

where \(E'_N\) carries the inner product induced by

\[
QW_\lambda^N-\epsilon_N\langle\cdot,\cdot\rangle.
\]

The killed ground line \(\mathbb C\xi\) has been quotiented out. Therefore the statement that the rank-one perturbation kills \(\xi\) does not force zero into the spectrum of this reduced selfadjoint realization.

The determinant identity is

\[
\det_{\mathrm{reg}}(D_{\log}^{(\lambda,N)}-z)
=
-i\lambda^{-iz}\widehat\xi(z).
\]

The factor \(-i\lambda^{-iz}\) is zero-free. The proof factors the determinant into:

1. the characteristic polynomial of the finite selfadjoint block on \(E'_N\);
2. the regularized determinant on \(E_N^\perp\), whose zero set is exactly
   \[
   \left\{\frac{2\pi j}{L}:j\in\mathbb Z,\ |j|>N\right\}.
   \]

Therefore the **whole zero divisor** of the Proposition-59 transform, with multiplicity, is the **whole spectrum** of the reduced selfadjoint operator. It is not only the finite \(P_N\)-zero set. The forced exterior lattice zeros are genuine spectral points of the \(E_N^\perp\) block. `[FINITE_CELL][PAPER]`

### 3.2 Factor-\(1/2\) repair

Assume \(F(0)\ne0\). Then \(0\) is not in the reduced spectrum, so
\(D_{\log}^{(\lambda,N)}\) is invertible on \(\mathcal H_{\lambda,N}\). Its inverse is Hilbert–Schmidt: the finite block is finite-dimensional and the exterior eigenvalues are \(2\pi j/L\), whose reciprocal squares are summable.

Because the row is even, \(F\) is even. Hence its zero divisor, and therefore the spectrum with multiplicity, is symmetric under
\(\mu\mapsto-\mu\).

The standard Hilbert–Schmidt norm counts both signs:

\[
\begin{aligned}
\left\|
(D_{\log}^{(\lambda,N)})^{-1}
\right\|_{\mathrm{HS}(\mathcal H_{\lambda,N})}^2
&=
\sum_{\mu\in\operatorname{Spec}D}
\frac{m_D(\mu)}{\mu^2}\\
&=
2\sum_{\rho\in R_N^+}\frac1{\rho^2}
+
\frac{L^2}{2\pi^2}\sum_{k>N}\frac1{k^2}\\
&=
2\kappa_F.
\end{aligned}
\]

Therefore the exact standard identity is

\[
\boxed{
\kappa_F
=
\frac12
\left\|
(D_{\log}^{(\lambda,N)})^{-1}
\right\|_{\mathrm{HS}}^2.
}
\]

The request's identity without the factor \(1/2\) is false unless
“Hilbert–Schmidt norm” is redefined to sum only over the positive spectrum. That would not be the standard Hilbert–Schmidt norm. `[FINITE_CELL][PAPER]`

The forced contribution is:

\[
\kappa_F^{\mathrm{forced}}
=
\frac{L^2}{4\pi^2}\sum_{k>N}\frac1{k^2}
\]

on the positive half-spectrum, and twice this number in the full Hilbert–Schmidt norm. Along \(m=N=k+2\), it tends to zero because \((\log m)^2/m\to0\). `[COFINAL_FAMILY][LEAN]`

### 3.3 Can the inverse kernel prove the uniform bound?

At one fixed cell, the source decomposition makes the trace computable in either of two exact ways:

\[
\|D^{-1}\|_{\mathrm{HS}}^2
=
\operatorname{Tr}(D^{-2}),
\]

or

\[
\|D^{-1}\|_{\mathrm{HS}}^2
=
-\left.
\frac{d^2}{dz^2}
\log\det_{\mathrm{reg}}(D-z)
\right|_{z=0}.
\]

Using the determinant theorem, the zero-free factor \(\lambda^{-iz}\) contributes no second logarithmic derivative. The result is

\[
-\frac{F''(0)}{F(0)}=2\kappa_F.
\]

This is an exact re-representation. It is not a new estimate.

The naive Green-kernel argument is not typed. On \(E'_N\), the relevant Hilbert norm is not ordinary \(L^2\); it is the norm induced by
\(QW_\lambda^N-\epsilon_N I\). Integrating the squared modulus of the ordinary-\(L^2\) kernel computes an ordinary-\(L^2\) Hilbert–Schmidt norm, not the norm in which Theorem 5.10 makes the finite block selfadjoint.

To turn the ordinary kernel into the required norm, one needs either:

- the exact metric kernel/Gram operator and a direct trace computation; or
- a uniform equivalence between the modified metric and ordinary \(L^2\).

The obvious metric comparison uses the smallest eigenvalue of
\(QW_\lambda^N-\epsilon_N I\) on the quotient, namely the absolute complement gap. That is precisely the denominator this route is supposed to avoid.

The modified metric changes the law, not the eigenvalue list. It supplies no automatic inequality in a favorable direction relative to the free periodic Dirac norm. Consequently the naive positive-half free value \(L^2/24\) is neither an upper nor a lower bound for the modified finite block.

The source-faithful decomposition does isolate the exterior tail, whose positive-half contribution is
\(O(L^2/N)\). The remaining finite quotient trace is exactly the intrinsic curvature wall. `[FINITE_CELL][PAPER]`

### 3.4 Ranking

#### Rank 1 — bordered secular slope

The curvature-specific rank-two deformation from the parent verdict evaluates the mixed curvature row directly before any norm:

\[
\frac12\partial_t\Phi(0,\lambda_1)
=
\frac1{12}
-
\langle c,(D-\lambda_1)^{-1}b\rangle.
\]

It remains the cheapest source-faithful attack. The falsifier is exact: if every estimate after the determinant rewrite begins with
\(\|(D-\lambda_1)^{-1}\|\), the representation only renamed the old wall. `[COFINAL_FAMILY][CONDITIONAL]`

#### Rank 2 — reduced Dirac Hilbert–Schmidt trace

The repaired identity is exact and avoids the CCM complement resolvent at the statement level. A potentially useful attack is a Kreĭn/rank-one resolvent-trace identity comparing the reduced operator with the free periodic scaling operator, with cancellation performed before absolute values.

Its first failure point is the modified finite-block metric: no source theorem currently bounds the relevant trace or transforms the ordinary Green kernel without importing the absolute complement floor. `[COFINAL_FAMILY][CONDITIONAL]`

#### Rank 3 — positive-zero ledger

The zero sum is the most transparent representation but supplies no mechanism. A bound requires both:

1. a uniform zero-free radius near zero;
2. a uniform inverse-square counting estimate for the remaining finite roots.

The exterior lattice tail is explicit, but the finite polynomial contributes a growing number of roots. A zero-free radius alone does not bound their inverse-square sum. `[COFINAL_FAMILY][CONDITIONAL]`

## 4. Q2.3 — zero repulsion

Bounded curvature implies

\[
\rho_{\min}(k)\ge\kappa_k^{-1/2}
\]

whenever the positive zero set is nonempty. The converse is false without a uniform counting or trace bound: a growing number of roots bounded away from zero can still make
\(\sum\rho^{-2}\) diverge.

CCM Lemma 7.3 cannot supply ground zero repulsion. It proves locally uniform convergence for the explicit **trial** transform \(k_\lambda\), not for the finite **ground** transform \(\widehat\xi_{\lambda,N}\). Importing its zero-free neighborhood into the ground family before proving the ground-to-trial same-family bridge is a C10 object substitution.

The finite Dirac construction supplies:

- reality and discreteness of the spectrum;
- the exact exterior lattice tail;
- cellwise invertibility when \(F(0)\ne0\).

It does not supply a uniform lower bound on the absolute value of the finite quotient eigenvalues. A family of finite selfadjoint blocks may have an eigenvalue converging to zero while remaining invertible at every cell.

The first exact missing statement is therefore

\[
\boxed{
\inf_k
\operatorname{dist}
\left(
0,\operatorname{Spec}
D_{\log}^{(\lambda_k,N_k)}|_{E'_{N_k}}
\right)>0
}
\]

or a strictly weaker trace/counting theorem implying the same inverse-square budget. No such theorem follows from Theorem 5.10 or Lemma 7.3. `[COFINAL_FAMILY][CONDITIONAL]`

## 5. Premise → source → consumer → gap matrix

| Premise / object | Exact source | Consumer | Residual gap | Tags |
|---|---|---|---|---|
| Entire removable P59 transform | `Proposition59EntireTransform.lean` | Explicit product | None | `[FINITE_CELL][LEAN]` |
| Exact central value and second jet | `proposition59RawTransform_at_zero_eq_sqrt`; `proposition59RawTransform_secondDerivative_zero` | Curvature identity | None | `[FINITE_CELL][LEAN]` |
| Real zeros of the same transform | `ZerosRealOn`; conditional P59 ground/Lagrange bridge | Real-rooted finite numerator | Spectral hypotheses for each production cell remain external to this theorem | `[FINITE_CELL][LEAN]` |
| Euler sine product | `Complex.tendsto_euler_sin_prod` | Exterior lattice product | Local removable-node extension | `[ABSTRACT][LEAN]` |
| Finite polynomial factorization | `Polynomial.Splits.eq_prod_roots_of_monic` | Positive paired root product | Local even-root multiset pairing | `[FINITE_CELL][LEAN]` |
| Basel sum | `hasSum_zeta_two` | Exact forced curvature | None | `[ABSTRACT][LEAN]` |
| Theorem 5.10 determinant/spectrum | CCM, Theorem 5.10 and proof | Reduced Dirac spectrum | Conditional simple-even hypothesis | `[FINITE_CELL][PAPER]` |
| Uniform P59 curvature bound | Not supplied | Local boundedness / Vitali | `P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND` | `[COFINAL_FAMILY][CONDITIONAL]` |
| Input A on same family | Parent route | ZeroEscape convergence | Common-path projective or lattice error | `[COFINAL_FAMILY][CONDITIONAL]` |

## 6. Lean-ready work versus new mathematics

### Lean-ready

The whole Part-1 bridge is Lean-ready:

1. finite Cauchy numerator and degree bound;
2. parity and real coefficients;
3. transfer of every numerator root to an exact P59 zero, including included lattice nodes;
4. finite paired-root factorization;
5. Euler-tail identity from `Complex.tendsto_euler_sin_prod`;
6. finite-product exponential bound;
7. exact tail second jet using `hasSum_zeta_two`;
8. real-valued/nonnegative curvature;
9. compact local-boundedness corollary.

The generic Hadamard factorization and an entire-function order predicate remain absent from pinned Mathlib, but they are no longer dependencies.

The finite standard-HS factor-\(1/2\) identity is also Lean-ready only after a project representation of the paper's reduced Hilbert space and selfadjoint operator exists. That operator is not yet a native Lean object in this transaction.

### New analytic work

The remaining new mathematics is:

- a uniform source bound on the bordered secular slope, or an equivalent uniform curvature bound;
- a gap-free trace estimate for the reduced Dirac finite block, if the HS runner-up is pursued;
- uniform ground zero repulsion plus counting, if the zero-ledger route is pursued;
- Input A on the same cofinal family.

All are `[COFINAL_FAMILY][CONDITIONAL]`.

## FINAL PROPOSAL

Close the finite bridge now. It removes the generic Hadamard formalization wall and turns bounded normalized curvature into a kernel-checkable normal-family supplier on the exact P59 family.

Do not switch the analytic mainline to Hilbert–Schmidt language merely because the representation is elegant. The standard identity has a factor \(1/2\), and the direct Green-kernel estimate is in the wrong metric. Keep the bordered secular slope as the primary source attack.

The exact division of labor is:

```text
Codex:
  formalize the finite P59 explicit-product curvature bridge.

Analytic front:
  continue P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND.

HS representation:
  retain as a runner-up trace/Krein formulation;
  do not use ordinary-L2 kernel norm or free-Dirac scaling as a bound.
```

## STRONGEST ATTACK

The strongest objection to Part 1 is the removable lattice:

> The quotient formula is proved only where \(D_N(z)\ne0\). At an included sine zero, the sine factor and denominator both vanish, so a formal cancellation can manufacture the wrong zero divisor.

The proof survives because it separately uses

\[
P_N(x_j)=v_j\prod_{k\ne j}(x_j-x_k)
\]

and the exact P59 sampling identity

\[
F(x_j)=\sqrt L\,(-1)^jv_j.
\]

Thus an included lattice point is a zero exactly when the finite polynomial supplies the corresponding factor. The normalized product then extends by continuity from the complement of the finite lattice. Any Lean proof that cancels denominators globally without this branch is rejected.

The strongest objection to Part 2 is the factor count:

> \(\kappa_F\) is a positive-half zero sum, while the standard Hilbert–Schmidt norm counts the full symmetric spectrum.

That objection is fatal to the identity as written. The repaired statement with one half is exact.

## CODEX DIRECTIVE

```text
TASK_ID:
  GOAL058_P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE

BOUNDARY:
  finite P59 bridge only;
  no cofinal curvature estimate;
  no route promotion;
  no RH claim.

TARGET_FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  Proposition59ExplicitProductCurvatureBridge.lean

IMPORT:
  Q3.Proofs.RouteB.Proposition59EntireTransform
  Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge
  Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
  Mathlib.NumberTheory.ZetaValues

PROVE IN THIS ORDER:

1. P59_FINITE_CAUCHY_NUMERATOR_IDENTITY
   Define D_N and P_N.
   Prove the off-lattice Cauchy quotient and
   P_N(x_j)=v_j*prod_{k!=j}(x_j-x_k).

2. P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT
   Split included-lattice and off-lattice cases.
   Use proposition59PoleKernel_at_lattice_sign for the included case.

3. P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT
   From real coefficients, evenness, P_N(0)!=0, and real roots,
   produce the positive-root multiset and normalized quadratic product.
   Use Polynomial.Splits.eq_prod_roots_of_monic.
   Do not assume a generic Hadamard theorem.

4. P59_NORMALIZED_EULER_TAIL_PRODUCT
   Use Complex.tendsto_euler_sin_prod.
   Cancel only off the finite lattice.
   Extend to all z by continuity/density.

5. P59_PRODUCT_CURVATURE_BOUND
   Use Real.prod_one_add_le_exp_sum.
   Define kappa as a real zero sum.
   Prove the complex second-jet identity and kappa >= 0.

6. P59_CURVATURE_ZERO_SUM
   Use hasSum_zeta_two plus the existing exact P59 second derivative.

7. P59_CURVATURE_COMPACT_ENVELOPE
   For compact K and kappa <= C, prove
     sup_{z in K} norm(F z / F 0) <= exp(C * R_K^2).

MANDATORY PLANTS:

A. N=1, v_0=1, v_{-1}=v_1=0:
   the included ±x_1 factors must come from P_N.

B. N=1, v_{-1}=v_0=v_1=1:
   included lattice values are nonzero and must not remain as sine zeros.

C. Non-even row:
   the paired quadratic product theorem must be unavailable.

D. F(0)=0:
   normalization theorem must be unavailable.

FORBIDDEN:

- new axiom, sorry, admit, exact?;
- generic Hadamard factorization;
- entire-function order predicate;
- global denominator cancellation at removable nodes;
- defining kappa as an ordered Complex number;
- claiming a cofinal bound from the finite theorem.

VALIDATION:

WORKDIR: q3.lean.aristotle
  lake env lean Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean
  lake build Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge

WORKDIR: repository root
  scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean

EXPECTED_AXIOMS:
  [propext, Classical.choice, Quot.sound]

SUCCESS:
  P59_EXPLICIT_PRODUCT_CURVATURE_BRIDGE_KERNEL_GREEN

FAILURE:
  report exactly one smallest code:
    P59_PRODUCT_BRIDGE_REMOVABLE_NODE_MISMATCH
    P59_EVEN_ROOT_MULTISET_PAIRING_API_GAP
    P59_EULER_TAIL_LIMIT_API_GAP
    P59_CURVATURE_SECOND_JET_NORMAL_FORM_GAP
```

## META CLOSEOUT

- **What became smaller?** The abstract Hadamard/order formalization wall collapsed to four finite/local glue lemmas around an existing Euler sine product.
- **What was killed?** The identity \(\kappa_F=\|D^{-1}\|_{\mathrm{HS}}^2\) without a factor \(1/2\); the ordinary-\(L^2\) Green-kernel norm as the modified-metric HS norm; Lemma 7.3 as a ground-family zero-repulsion supplier.
- **What must not be tried again?** Generic Hadamard formalization for this family, global cancellation through removable nodes, free-Dirac \(L^2/24\) scaling as a bound for the modified finite block, or trial-to-ground zero transfer without a same-family theorem.
- **Current smallest named gap:** `P59_CURVATURE_BORDERED_SECULAR_SLOPE_SOURCE_BOUND`.
- **Next cheapest decisive test:** kernel-check the P59-specific product bridge with both removable-node plants.
- **Prediction fates:** one confirmed at paper/Lean granularity, one refuted by an exact factor two, one unresolved with adverse source-metric evidence.
- **Memory entry:** normalized P59 curvature is both a positive-half zero sum and one half of the reduced Dirac inverse HS-square; the finite bridge is formalization-ready, while the cofinal bound remains analytic.

No Lean source was edited. No numerical run was started. No route promotion or RH claim was made.
