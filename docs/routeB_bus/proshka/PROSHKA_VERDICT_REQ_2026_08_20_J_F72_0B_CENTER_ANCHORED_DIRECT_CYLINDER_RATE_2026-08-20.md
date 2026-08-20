# STATUS: CONDITIONAL — R2 CENTER-ANCHORED DIRECT CYLINDER RATE SELECTED; THE LITERAL REPRESENTATIVE SURVIVES ONLY AS A PRIVATE SOURCE SEAM
```yaml
PRIMARY: SELECT_R2_CENTER_ANCHORED_DIRECT_CYLINDER_RATE
PRIMARY_COUNT: 1
REQ_ID: REQ-2026-08-20-J

SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  INPUT_HEAD: fc93696601ada3eeff04c6f3569ba6685fee48a4
  QUEUE_PATH: docs/routeB_bus/PROSHKA_QUEUE.md
  F72_0A_COMMIT: a61eb04bd784cfab40288ac079e06cec9aaa7b1d
  F72_1B_COMMIT: 0c6a96473e7c01276ee006c2f31820b435f0898a
  F72_1B_LEAN_BLOB: 5253ef9a46438bf99c15c2b456a216631405119f
  F72_1B_GATE: docs/routeB_bus/LINUX_GATE_F72_1B_CYLINDER_GREEN_2026-08-20.md
  SATZ9_CARD: docs/routeB_bus/litreview/MEIXNER_SCHAEFKE_1954_USAGE_CARDS.md
  CCM_CARD: docs/routeB_bus/litreview/CCM_ZST_USAGE_CARDS.md

FORK:
  R2_CENTER_ANCHORED_DIRECT_CYLINDER_RATE:
    status: SELECTED_PRIMARY
    kill_power: 10/10
    repriced_cost: 5/10
    public_paper_h0_h4_objects_required: false
    literal_ps_representative_required_publicly: false
    independent_source_representative_required_inside_proof: true
  R1_PUBLIC_LITERAL_REPRESENTATIVE_BIND:
    status: RUNNER_UP_NOT_SELECTED
    kill_power: 10/10
    repriced_cost: 6/10
    reason: OVERBUILDS_PUBLIC_OBJECT_GRAPH_AFTER_EXACT_CYLINDER_TARGET_LOCK

KEY_REPRESENTATION:
  name: CENTER_ANCHORED_SCALE_FREE_SATZ9_TRANSFER
  project_modes:
    - f_0_k
    - f_4_k
  cylinder_targets:
    d_0: D_0_sqrt_4pi_x
    d_4: D_4_sqrt_4pi_x
  target_centers:
    d_0_at_zero: 1
    d_4_at_zero: 3
  precommitted_scales:
    a_0_k: 1 / f_0_k(0)
    a_4_k: 3 / f_4_k(0)
  target_rate: >-
    eventually, uniformly for abs(x) <= lambda_k,
    abs(a_n_k * f_n_k(x) - d_n(x)) <= C * lambda_k^(-2), n in {0,4}

EXACT_PACKET_LOCK:
  formula: explicitCCMLimitH = (1/16)*d_4 - (3/16)*d_0
  status: LEAN_PROVED
  consequence: FIXED_HERMITE_H0_H4_PUBLIC_OBJECTS_NOT_LOAD_BEARING

SOURCE_SEAM:
  exact_name: CENTER_NORMALIZED_SELECTED_FERRERS_TO_SATZ9_SOURCE_BIND
  status: OPEN_LOAD_BEARING
  required_content:
    - independent_literal_Satz9_representative
    - same_project_gamma_and_separation_eigenvalue
    - same_even_regular_ODE_class
    - nonzero_center
    - center_normalized_equality_to_selected_Ferrers_mode
  forbidden:
    - define_paper_ps_to_be_project_mode
    - assume_the_target_rate_as_a_hypothesis
    - choose_a_n_k_after_minimizing_the_observed_sup_error

KERNEL_FLOORS:
  F72_0B0_EXACT_CYLINDER_PACKET_TARGET:
    status: CLOSED_LEAN
  F72_0B1_CENTER_ANCHOR_SCALAR_LOCK:
    status: NEXT_LEAN_READY
    cost: 1/10
  F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND:
    status: OPEN_SOURCE_BIND
    cost: 3/10
  F72_1A_CENTER_NORMALIZED_SATZ9_RATE:
    status: OPEN_PAPER_TO_PROJECT_PORT
    cost: 3/10
  F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE:
    status: OPEN_COMPOSITION
    cost: 2/10
  F72_4_CENTER_INTEGRAL_RATE_FROM_CHI:
    status: OPEN_AFTER_F72_3
    cost: 2/10
  F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY:
    status: OPEN_FINITE_ALGEBRA
    cost: 2/10

DISCRIMINATOR:
  name: STRICT_CENTER_ANCHORED_SELECTED_FERRERS_CYLINDER_RATE
  formula: >-
    lambda_k^2 * sup_{abs(x)<=lambda_k}
      abs(a_n_k*f_n_k(x)-d_n(x)), n in {0,4}
  pass: EVENTUALLY_BOUNDED_WITH_A_N_K_FIXED_BY_CENTER_BEFORE_RATE
  zero_consistent: INCONCLUSIVE
  c10_kill: SOURCE_REPRESENTATIVE_DEFINED_BY_PROJECT_TARGET
  c09_kill: SCALAR_FITTED_AFTER_ERROR_INSPECTION

REGISTERED_PREDICTIONS:
  P_J1: exact_D0_D4_packet_decomposition_removes_public_h0_h4_objects
  P_J2: literal_source_bind_does_not_disappear_but_shrinks_to_private_center_normalized_seam
  P_J3: center_anchor_cancels_the_paper_prefactor_and_preserves_lambda_minus_two_rate
  P_J4: first_implementation_failure_if_any_is_source_eigenvalue_or_ODE_crosswalk_not_cylinder_algebra

ARSENAL_MANDATE: ACCEPTED
CARDS_APPLIED:
  - C04_SAME_COORDINATES_TWO_LAWS
  - C09_PRECOMMIT_AND_STRENGTHEN_INVARIANT
  - C10_FUNCTIONAL_NOT_SURROGATE

CODEX_AUTHORIZED: false
ARISTOTLE_AUTHORIZED: false
LEAN_SOURCE_WRITTEN: false
QUEUE_STATUS_MUTATED: false

NEXT_EXECUTABLE_NODE: F72_0B1_CENTER_ANCHOR_SCALAR_LOCK
NEXT_LOAD_BEARING_GAP: CENTER_NORMALIZED_SELECTED_FERRERS_TO_SATZ9_SOURCE_BIND

PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 5

SCOPE: COFINAL_FAMILY
VERIFIER: PAPER_PLUS_LEAN_SOURCE_AUDIT
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
ROUTE_PROMOTION: false
RH_CLAIM: false
```

## ROUTE MAP

### 1. The new decomposition changes the correct public target

F72.1B proves, on the literal project object,

\[
\boxed{
 h(x)=\operatorname{explicitCCMLimitH}(x)
 =\frac1{16}D_4(\sqrt{4\pi}\,x)
  -\frac3{16}D_0(\sqrt{4\pi}\,x).
}
\]

The quartic coefficient fixes `1/16`; the quadratic and constant coefficients
then agree independently. This is an exact target identification, not a fitted
basis decomposition. `[ABSTRACT][LEAN]`

Consequently the fixed Hermite functions called `h_0` and `h_4` in CCM are no
longer load-bearing **public project objects** for the L73.2 port. The final
consumer can be stated entirely with the already-defined cylinder functions
`D_0`, `D_4` and `explicitCCMLimitH`. `[COFINAL_FAMILY][LEAN]`

This changes the fork. R1 would materialize two external representatives and
their normalizations as persistent project objects even though no downstream
consumer needs those names. R2 can instead expose only the exact rate that the
consumer needs. `[COFINAL_FAMILY][CONDITIONAL]`

### 2. The representative bind is reduced, not deleted

The decomposition pins the **limit side**. It does not prove that an arbitrary
selected Ferrers solution is the spheroidal function to which Satz 9 applies.
Satz 9 is a theorem about the independently defined representative

\[
\operatorname{ps}^{0}_{n}(z;\gamma^2),\qquad n\in\{0,4\}.
\]

The selected project modes and the paper representative must still be shown to
belong to the same one-dimensional regular even eigenspace at the same
separation value. Same ODE-shaped notation is not equality of objects.
`[COFINAL_FAMILY][PAPER]` **[C04]**

The project already contains the hard local engine

```lean
complex_prolate_divergence_solution_unique_of_center
```

which proves equality on the open physical window for two solutions of the
same prolate divergence-form ODE after their center value and center derivative
are matched. Evenness supplies the zero derivative. Thus the remaining bind
need not become a general spheroidal-function library. It can remain a private
proof seam that consumes an independent Satz-9 representative and produces a
center-normalized equality. `[ABSTRACT][LEAN]`

Defining the paper representative to be the selected project mode would make
the equality tautological and would import none of Satz 9's provenance. That is
fatal to the proposed proof, although not fatal to the wider route.
`[COFINAL_FAMILY][PAPER]` **[C10]**

### 3. The center anchor is the cheaper normalization

Let

\[
f_{0,k},\ f_{4,k}
\]

be the two selected unit-`L2` physical Ferrers modes, and set

\[
d_0(x):=D_0(\sqrt{4\pi}\,x),\qquad
 d_4(x):=D_4(\sqrt{4\pi}\,x).
\]

F72.1B gives

\[
d_0(0)=1,\qquad d_4(0)=3.
\]

The selected Ferrers center values are real and nonzero. Therefore define,
before any rate is inspected,

\[
\boxed{
 a_{0,k}:=\frac1{f_{0,k}(0)},\qquad
 a_{4,k}:=\frac3{f_{4,k}(0)}.
}
\]

Then

\[
a_{0,k}f_{0,k}(0)=1,\qquad
 a_{4,k}f_{4,k}(0)=3.
\]

These are source-derived signed ratios, not fitted minimizers.
`[COFINAL_FAMILY][CONDITIONAL]` **[C09]**

Suppose the literal paper representative satisfies the raw Satz-9 estimate

\[
p_{n,k}(x)=A_{n,k}d_n(x)+r_{n,k}(x),
\qquad
 \|r_{n,k}\|_\infty\le C_n\gamma_k^{-3/4},
\]

where `A_{n,k}` is a nonzero constant of order `gamma_k^(1/4)`. Center
normalization gives the exact cancellation

\[
 d_n(0)\frac{p_{n,k}(x)}{p_{n,k}(0)}-d_n(x)
 =
 \frac{d_n(0)r_{n,k}(x)-d_n(x)r_{n,k}(0)}{p_{n,k}(0)}.
\]

Because `d_0(0)=1`, `d_4(0)=3`, both are nonzero. The leading center term gives
an eventual lower bound

\[
|p_{n,k}(0)|\gg\gamma_k^{1/4}.
\]

The numerator is `O(gamma_k^(-3/4))`; division therefore gives

\[
O(\gamma_k^{-1})=O(\lambda_k^{-2}).
\]

Thus the exact paper prefactor cancels from the public theorem. It remains
needed only to prove the denominator lower bound and may not be guessed or
fitted. `[COFINAL_FAMILY][PAPER]`

Combining this scale-free paper estimate with the center-normalized ODE bind
gives the direct project theorem

\[
\boxed{
 \exists C\ge0,\ \forall^{\infty}k,\ \forall |x|\le\lambda_k,
 \quad
 |a_{n,k}f_{n,k}(x)-d_n(x)|
 \le C\lambda_k^{-2},
 \qquad n\in\{0,4\}.
}
\]

This is the repaired R2. `[COFINAL_FAMILY][CONDITIONAL]`

### 4. Why the cylinder target also simplifies the integral assembly

Let

\[
I_{0,k}:=\int_{\mathbb R}f_{0,k},\qquad
 I_{4,k}:=\int_{\mathbb R}f_{4,k}.
\]

At Fourier frequency zero, the exact selected finite-Fourier eigenrelations
give

\[
I_{0,k}=\chi_{0,k}f_{0,k}(0),\qquad
 I_{4,k}=\chi_{4,k}f_{4,k}(0),
\]

where the project field called `chi2` is the full-degree-four scalar
`chi_{4,k}`. Therefore the center anchors yield exact identities

\[
\boxed{
 a_{0,k}I_{0,k}=\chi_{0,k},\qquad
 a_{4,k}I_{4,k}=3\chi_{4,k}.
}
\]

F72.3 supplies `chi_{0,k},chi_{4,k}=1+O(lambda_k^(-2))`; no integration of a
uniform pointwise error over an expanding window is needed. This avoids the
otherwise weaker `O(lambda_k^(-1))` budget produced by multiplying a
`lambda_k^(-2)` sup error by a window of length `2 lambda_k`.
`[COFINAL_FAMILY][CONDITIONAL]`

For the normalized zero-mass combination

\[
q_k=
\frac{I_{4,k}f_{0,k}-I_{0,k}f_{4,k}}
     {\sqrt{I_{0,k}^2+I_{4,k}^2}},
\]

define the source scale

\[
\boxed{
 s_k:=-\frac{a_{0,k}a_{4,k}}{16}
       \sqrt{I_{0,k}^2+I_{4,k}^2}.
}
\]

Then exact algebra gives

\[
\boxed{
 s_kq_k
 =\frac{\chi_{0,k}}{16}(a_{4,k}f_{4,k})
  -\frac{3\chi_{4,k}}{16}(a_{0,k}f_{0,k}).
}
\]

The two direct cylinder rates and the two Fuchs defects therefore imply

\[
s_kq_k\longrightarrow
 \frac1{16}d_4-\frac3{16}d_0
 =\operatorname{explicitCCMLimitH}
\]

with the same `O(lambda_k^(-2))` rate. The later port factor `4` remains exactly
where REQ-E placed it and is not inserted into either individual mode scale.
`[COFINAL_FAMILY][CONDITIONAL]`

## FINAL PROPOSAL

### Selected route

Select **R2**, repaired as

```text
R2_CENTER_ANCHORED_DIRECT_CYLINDER_RATE
```

with the following public contract:

```text
selected Ferrers mode
+ center-derived nonzero scalar
+ direct uniform rate to D_0 or D_4
```

Do not expose `h_0`, `h_4`, `ps_0^0`, or `ps_4^0` as persistent public Route-B
objects merely to reach the limit packet. The literal `ps` representative is
allowed only as an independently defined local/source witness used to invoke
Satz 9 and the existing same-ODE uniqueness engine. `[COFINAL_FAMILY][CONDITIONAL]`

### Kernel floors

#### `F72_0B0_EXACT_CYLINDER_PACKET_TARGET` — CLOSED

Consumes the already-green F72.1B source and exports

```lean
explicitCCMLimitH_eq_cylinder_combination
```

with `D_0`, `D_4`, centers `1`, `3`, and the exact coefficients `1/16`,
`-3/16`. `[ABSTRACT][LEAN]`

#### `F72_0B1_CENTER_ANCHOR_SCALAR_LOCK` — NEXT LEAN-READY NODE

For the exact selected pre-anchor pair, define the two real center values and

```text
a0(k) = 1 / f0(k,0)
a4(k) = 3 / f4(k,0).
```

Prove:

```text
f0(k,0) != 0;
f4(k,0) != 0;
a0(k) != 0;
a4(k) != 0;
a0(k) * f0(k,0) = 1;
a4(k) * f4(k,0) = 3.
```

This closes the scalar orientation and precommit firewall; it opens no analytic
input. `[COFINAL_FAMILY][LEAN_READY]`

#### `F72_0B2_CENTER_NORMALIZED_SATZ9_SOURCE_BIND` — LOAD-BEARING SOURCE SEAM

Given an independently defined `ps_n^0` representative with the exact project
parameter/eigenvalue dictionary, prove on the physical window

\[
\frac{f_{n,k}(x)}{f_{n,k}(0)}
 =
 \frac{p_{n,k}(x)}{p_{n,k}(0)}.
\]

Use the existing center-initial-data ODE uniqueness theorem. Extend the open
window equality to endpoints by continuity. `[COFINAL_FAMILY][CONDITIONAL]`

#### `F72_1A_CENTER_NORMALIZED_SATZ9_RATE` — PAPER PORT

Convert raw Satz 9 into

\[
\sup_{|x|\le\lambda_k}
\left|
 d_n(0)\frac{p_{n,k}(x)}{p_{n,k}(0)}-d_n(x)
\right|
\le C\lambda_k^{-2}.
\]

The proof must include an eventual explicit denominator lower bound. A raw
big-O citation without the denominator ledger is insufficient.
`[COFINAL_FAMILY][PAPER]`

#### `F72_1C_SELECTED_FERRERS_DIRECT_CYLINDER_RATE` — COMPOSITION

Compose F72.0B1, F72.0B2 and F72.1A to obtain the two public project rates for
`n=0,4`. `[COFINAL_FAMILY][CONDITIONAL]`

#### `F72_4_CENTER_INTEGRAL_RATE_FROM_CHI` — AFTER F72.3

Use the zero-frequency eigenrelations to prove

```text
a0(k) * I0(k) = chi0(k)
a4(k) * I4(k) = 3 * chi4(k)
```

and consume the Fuchs defect bounds. `[COFINAL_FAMILY][CONDITIONAL]`

#### `F72_5_ZERO_MASS_CYLINDER_PACKET_ASSEMBLY` — FINITE ALGEBRA

Use the displayed exact scale `s_k`, the two mode rates, the two eigenvalue
defect rates, and `explicitCCMLimitH_eq_cylinder_combination` to close the
selected zero-mass rate. `[COFINAL_FAMILY][CONDITIONAL]`

### Registered prediction

The direct route should fail first, if it fails, at the exact paper
separation-eigenvalue/ODE source crosswalk inside F72.0B2. It should not fail at
the D0/D4 algebra, center scalar, or zero-mass finite assembly, all of which
are already source-shaped. `[COFINAL_FAMILY][CONDITIONAL]`

## STRONGEST ATTACK

The strongest reviewer objection is:

> The direct rate merely hides the old representative bind inside an
> existential scalar. Nothing has actually become cheaper.

That objection kills the naive R2, but not the center-anchored repair.

The naive statement

\[
\exists a_{n,k}\ne0,
\quad
\|a_{n,k}f_{n,k}-d_n\|_\infty\le C\lambda_k^{-2}
\]

allows `a_{n,k}` to be chosen after the error is observed. It is weaker than a
source transfer and violates precommit. **[C09]**

The repaired statement fixes

\[
a_{n,k}=d_n(0)/f_{n,k}(0)
\]

before applying Satz 9. The paper normalization disappears through a proved
center-normalized identity, not through a fitted scalar. The literal paper
representative remains independent and must supply the same ODE/eigenvalue and
Satz-9 estimate. Therefore no functional surrogate is substituted. **[C10]**

A second attack is that the exact cylinder decomposition concerns only the
limit packet. Correct. It does not itself bind the selected source modes to
Satz 9. That is why F72.0B2 remains explicitly open rather than being declared
closed by the decomposition. **[C04]**

Weakest repaired statement if F72.0B2 fails:

```text
The exact D0/D4 target decomposition remains proved.
The selected Ferrers direct cylinder rate remains conditional on an
independent same-eigenspace source theorem.
No Lemma-7.2 selected-mode or zero-mass rate is claimed.
```

## CODEX DIRECTIVE

```text
EXECUTION: NOT AUTHORIZED BY THIS VERDICT.

NEXT EXACT TASK WHEN AUTHORIZED:
  F72_0B1_CENTER_ANCHOR_SCALAR_LOCK

TARGET FILE:
  q3.lean.aristotle/Q3/Proofs/RouteB/
  G6N1SelectedFerrersCylinderCenterScales.lean

DIRECT IMPORTS:
  Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
  Q3.Proofs.RouteB.G6N1ParabolicCylinderD0D4Exact

CLOSES:
  SELECTED_FERRERS_CYLINDER_SCALE_ORIENTATION
  SELECTED_FERRERS_CYLINDER_SCALE_PRECOMMIT

OPENS:
  []

REQUIRED PUBLIC SURFACE:
  selectedFerrersCylinderCenter0
  selectedFerrersCylinderCenter4
  selectedFerrersCylinderScale0
  selectedFerrersCylinderScale4
  selectedFerrersCylinderScale0_ne_zero
  selectedFerrersCylinderScale4_ne_zero
  selectedFerrersCylinderScale0_mul_center
  selectedFerrersCylinderScale4_mul_center

MATHEMATICAL DEFINITIONS:
  center0(k) = the exact real center of the selected normalized physical mode 0
  center4(k) = the exact real center of the selected normalized physical mode 4
  scale0(k)  = 1 / center0(k)
  scale4(k)  = 3 / center4(k)

PROOF ROUTE:
  - reuse selectedFerrersPreAnchorPair_h0_eq_selectedMode;
  - reuse selectedFerrersPreAnchorPair_h4_eq_selectedMode;
  - unfold normalizedPhysicalMode only as far as needed to expose a real center;
  - reuse the existing center-value nonvanishing theorem;
  - use the already-proved D0/D4 center values 1 and 3;
  - prove signed nonzero ratios; do not prove positivity unless already on shelf.

FORBIDDEN:
  - define ps_n or paper h_n;
  - add a Satz-9 hypothesis;
  - choose scales by minimising a norm;
  - insert the port factor 4;
  - weaken the selected source family;
  - touch Q3.Main or route state.

VALIDATION:
  WORKDIR q3.lean.aristotle
    lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersCylinderCenterScales.lean
    lake build Q3.Proofs.RouteB.G6N1SelectedFerrersCylinderCenterScales
  WORKDIR repository root
    scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersCylinderCenterScales.lean

EXPECTED_AXIOMS:
  every printed theorem: [propext, Classical.choice, Quot.sound]

SUCCESS:
  F72_0B1_CENTER_ANCHOR_SCALAR_LOCK_LEAN

FAILURE:
  F72_0B1_SELECTED_CENTER_REAL_OR_NONZERO_INTERFACE_GAP
```

## META CLOSEOUT

**What became smaller?**

The fork is resolved. The public theorem no longer needs four persistent paper
objects (`h_0`, `h_4`, `ps_0^0`, `ps_4^0`). The missing source bind is reduced
to one scale-free center-normalized seam. `[COFINAL_FAMILY][CONDITIONAL]`

**What was killed?**

- public R1 as the primary route;
- fitted existential scales;
- defining paper Hermite modes by the already-known cylinder formulas;
- integrating the sup error across the expanding window;
- any claim that F72.1B alone closes F72.0B.

**What must not be tried again?**

Do not define an external representative by the project function and then use
that tautological identity to import Satz 9. Do not select the scalar after
seeing the approximation error. **[C09] [C10]**

**Current smallest named gap:**

```text
CENTER_NORMALIZED_SELECTED_FERRERS_TO_SATZ9_SOURCE_BIND
```

**Next cheapest decisive test:**

Prove the center-anchor scalar lock without introducing any paper object. Then
audit whether the literal Satz-9 representative exposes the exact same
separation value and physical divergence-form ODE required by the existing
center uniqueness theorem.

**Fate of prior registered predictions:**

```text
P_G_D2:
  CONFIRMED_WITH_REPAIR.
  A representative seam remains, but no public normalized paper object is
  needed after the exact cylinder target lock.

P_I_R1_PRIMARY:
  REFUTED_BY_NEW_LEAN_FACT.
  The exact packet decomposition changes the public consumer and makes the
  center-anchored direct route cheaper.

P_I_D0_D4_ALGEBRA_CHEAP:
  CONFIRMED.
  F72.1B is kernel-green on the standard axiom triple.
```

```yaml
iteration:
  target: F72.0B representative fork
  status: PROGRESS
  failed_strategy: public_literal_representative_object_graph
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: CENTER_NORMALIZED_SELECTED_FERRERS_TO_SATZ9_SOURCE_BIND
  invariant_learned: scalar_is_fixed_by_center_before_rate_and_source_representative_remains_independent
  forbidden_future_move: fitted_scalar_or_tautological_ps_alias
  next_decisive_test: center_anchor_scalar_lock_then_exact_source_ODE_eigenvalue_audit
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
```
