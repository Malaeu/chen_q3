# Agent report — Goal 058: P59 anchored log-derivative winding lock on a fixed compact

Basis line (Convention card rule): every coefficient row below is in FULL mode coordinates
`v = (v_k)_{k∈[-N,N]}`, `x_k = 2πk/L`, `L = log m`; the P59 sample ratio carries no `√2`.
Where the EVEN orthonormal block is meant it is said explicitly.

```yaml
TASK_ID: GOAL058_P59_ANCHORED_LOG_DERIVATIVE_FIXED_COMPACT_PREFLIGHT
TASK_FILE: docs/Codex/TASK_2026-09-04_goal058_winding_lock_fixed_compact_preflight.md
DATE: 2026-09-04
MODE: PAPER_AND_SOURCE_READ_ONLY
HONESTY_STATE: CHALLENGER_NOT_RH
PX_RH_CLAIM: NOT_MADE
ROUTE_PROMOTION: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
NEW_FILES: 1 (this report)
VERDICTS_READ:
  - PROSHKA_VERDICT_GOAL058_WINDOW_WEIL_IDENTITY_AND_LEAKAGE_MECHANISM_2026-09-04.md
  - PROSHKA_VERDICT_GOAL058_GROUND_TRANSFORM_ZERO_PINNING_AND_REAL_ZERO_IDENTIFICATION_2026-09-04.md
HEADLINE:
  P_COMMON_LATTICE_FACTOR_CANCELS_IN_LOG_DERIVATIVE: CONFIRMED_AND_STRONGER_THAN_STATED
  LENGTH_FORM_INTERFACE_SCOPE: SAME_LATTICE_P59_PAIRS_ONLY
  GROUND_VS_XI_LENGTH_FORM: STRUCTURALLY_OUT_OF_BUDGET_ON_THE_WHOLE_CERTIFIED_SCHEDULE
  CONCENTRIC_DISK_WINDING_IS_BLIND_TO: THE_NOT_RH_CONFIGURATION_ITSELF
```

---

## 0. Objects, exactly as the project defines them

From `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59EntireTransform.lean`:

* `proposition59Pole L k = 2πk/L =: x_k`
* `proposition59Numerator L z = 2 sin(zL/2)`
* `proposition59PoleKernel L k = dslope (2 sin(·L/2)) x_k` — entire, removable at `x_k`
* `proposition59RawTransform L S v z = L^{-1/2} Σ_{k∈S} v_k · K_k(z)`, and
  (`proposition59RawTransform_eq_paper_formula`, off the lattice)

$$
F_v(z)\;=\;\frac{2\sin(zL/2)}{\sqrt L}\sum_{k\in S}\frac{v_k}{z-x_k},
\qquad S=[-N,N]\cap\mathbb Z .
$$

From `Proposition59ExplicitProductCurvatureBridge.lean`:

* `proposition59CauchyDenominator L S = Q(z) = ∏_{k∈S}(z-x_k)` — degree `2N+1`
* `proposition59CauchyNumerator L S v = P_v(z) = Σ_{k∈S} v_k ∏_{j≠k}(z-x_j)` — degree `≤ 2N`,
  leading coefficient `Σ_{k∈S} v_k`
* `proposition59_finite_cauchy_numerator_identity`: off the lattice `Σ v_k/(z-x_k) = P_v(z)/Q(z)`
* `proposition59CauchyNumerator_eval_at_lattice`: `P_v(x_j) = v_j ∏_{k≠j}(x_j-x_k)`
* `proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff`: `P_v(x_j)=0 ⇔ v_j=0`
* `proposition59CauchyNumerator_eval_neg`: `P_v` is even for even `v` on a symmetric window
* `proposition59CauchyNumerator_normalized_product`: under `ZerosRealOn` and `v_0≠0`,
  `P_v(z)/P_v(0) = ∏_{ρ∈R^+}(1-z²/ρ²)`
* `proposition59_explicit_product_identity`: the node-safe global form
  `F·∏_{k≠0}(1-z/x_k) = F(0)·∏_ρ(1-z²/ρ²)·sinc(zL/2)`

So, as meromorphic functions on `ℂ`,

$$
\boxed{\;F_v(z)=\underbrace{\frac{2}{\sqrt L}\cdot\frac{\sin(zL/2)}{Q(z)}}_{\text{depends only on }(L,N)}\cdot P_v(z)\;}
$$

The prefactor is **independent of the coefficient row `v`**. It is entire (the `2N+1` zeros of
`sin` at `x_k`, `|k|≤N`, are exactly cancelled by `Q`), and its zero divisor is
`{x_k : |k|>N}`, each simple.

Consequently, for `R < x_{N+1}`:

$$
N_D(F_v)=N_D(P_v)\qquad(D=\{|z|<R\}).
$$

Certified schedule (from `docs/routeB_bus/phase5_scripts/edge_ledger_relritz.py`, module docstring):
the k1/g04 prolate trial generator is faithful (its hard-coded `MAX_DEGREE = 180` is converged)
exactly at `(m,N) ∈ {(13,13),(13,26),(23,23),(43,43),(43,86)}` plus the bonus cell `(13,120)`;
`m ∈ {83,163}` are `TRIAL_GENERATOR_NOT_PARAMETRIZABLE`. Ground-only tests are not bound by that
restriction (`λ₁(163)` exists in the ledger).

| cell | `L=log m` | `2π/L` | `x_N` |
|---|---|---|---|
| (13,13) | 2.564949 | 2.449701 | 31.846 |
| (13,26) | 2.564949 | 2.449701 | 63.692 |
| (23,23) | 3.135494 | 2.003934 | 46.090 |
| (43,43) | 3.761200 | 1.670573 | 71.835 |
| (43,86) | 3.761200 | 1.670573 | 143.669 |
| (13,120) | 2.564949 | 2.449701 | 293.964 |

All exceed `R = 28`, so on every disk used below the lattice tail contributes **no** zeros and
`N_D(F) = N_D(P)` holds cell-wise.

---

## 1. Item (1) — the exact statement, with the common factor cancelled

### 1.1 The cancellation is exact and is *larger* than the judge stated

The judge asked to "cancel the common Proposition-5.9 sine/lattice factor". In the project's
objects the common factor is not only `2L^{-1/2} sin(zL/2)` but the whole prefactor
`2L^{-1/2} sin(zL/2)/Q(z)`, because two rows compared **at the same `(m,N)`** share the same
`L` and the same carrier `S`, hence the same `Q`. Therefore, as an identity of meromorphic
functions on all of `ℂ`,

$$
\frac{F_g'}{F_g}-\frac{F_t'}{F_t}
\;=\;
\frac{P_g'}{P_g}-\frac{P_t'}{P_t}.
$$

`P_g, P_t` are two polynomials of degree `2N` (degree exactly `2N` iff `Σ_k v_k ≠ 0`; see plant 4).
Nothing transcendental survives. This is `P_COMMON_LATTICE_FACTOR_CANCELS_IN_LOG_DERIVATIVE`
(judge probability 0.90): **CONFIRMED, and by pure finite algebra** — `logDeriv_mul`,
`logDeriv_div`, `logDeriv_const_mul` (Mathlib `Analysis/Calculus/LogDeriv.lean`) applied to
`F_v = c·s/Q·P_v`. No limit, no Euler tail, no analytic input.

Two corollaries that matter operationally:

1. **The boundary guard is weaker than it looks.** For the *difference*, `∂D` must avoid the zeros
   of `P_g` and `P_t` only. It need **not** avoid the lattice `{x_k}` nor the far zeros `x_k`,
   `|k|>N`: those are common and cancel identically. A radius equal to a node is legal.
2. **The count difference is the numerator count difference**, unconditionally in `R`:
   `N_D(F_g) − N_D(F_t) = N_D(P_g) − N_D(P_t)` for every `D` whose boundary misses `Z(P_g)∪Z(P_t)`,
   because the common entire factor contributes the same divisor to both.

### 1.2 The winding lock

Let `D ⊂ ℂ` be a bounded domain with rectifiable positively oriented boundary `∂D`, and suppose
`P_g(z) ≠ 0 ≠ P_t(z)` for all `z ∈ ∂D`. Then

$$
\frac{1}{2\pi i}\oint_{\partial D}\left(\frac{F_g'}{F_g}-\frac{F_t'}{F_t}\right)dz
=\frac{1}{2\pi i}\oint_{\partial D}\left(\frac{P_g'}{P_g}-\frac{P_t'}{P_t}\right)dz
= N_D(P_g)-N_D(P_t)\in\mathbb Z ,
$$

with multiplicity. Two sufficient interfaces make that integer `0`:

**(I) Rouché form.**
$$
\sup_{z\in\partial D}\bigl|P_g(z)-P_t(z)\bigr| \;<\; \inf_{z\in\partial D}\bigl|P_t(z)\bigr|
\;\Longrightarrow\; N_D(P_g)=N_D(P_t).
$$
(equivalently `|h−1|<1` on `∂D` for `h = P_g/P_t`; it forces both boundary guards by itself.)

**(II) Length form (the judge's `SUFFICIENT_INTERFACE`).**
$$
\frac{\operatorname{length}(\partial D)}{2\pi}\,
\sup_{z\in\partial D}\left|\frac{F_g'}{F_g}-\frac{F_t'}{F_t}\right|<1
\;\Longrightarrow\; N_D(F_g)=N_D(F_t).
$$
For `D = {|z|<R}` this reads `R · sup_{|z|=R}|Δ| < 1`.

### 1.3 Which is weaker

As abstract hypotheses on `∂D` alone the two are **incomparable**:

* (I) fails, (II) holds: `h ≡ 10^6` (constant ratio) — a huge multiplicative drift, zero derivative.
* (II) fails, (I) holds: `h = 1 + ε sin(Kz)` with `ε` tiny and `K` huge — values near 1, derivative
  unbounded.

There *is* a one-way implication once the anchor and the whole disk are used. If
`sup_{|z|≤R}|h'/h| ≤ M` and `h(0)=1` (both numerators are anchor-normalized, `P(0)≠0`), then
integrating along the radius gives `|log h(z)| ≤ MR`, so `MR < log 2` implies `|h−1| < 1`, i.e.

$$
\text{(II) on the full disk, with constant }\log 2 \;\Longrightarrow\;\text{(I) on }\partial D .
$$

The converse is false. **So the disk-version of (II) is the stronger hypothesis and (I) is the
weaker one.**

For *this project's data* the ranking inverts, and that is the operationally relevant statement:

* (I) is a statement about **values**. The corpus controls the ground-vs-target values only through
  `Δ_n` (node ratio defect, size `~10⁻²`, decaying polylogarithmically, `~1/log²m`). A `10⁻²`
  relative defect does not give `|h−1|<1` on a circle where `P` varies over many orders of magnitude.
* (II) is a statement about **divisors**: `P'/P = Σ_j 2z/(z²−ρ_j²)` is a pure function of the root
  multiset. The corpus controls exactly that, and to `10⁻²⁶` for the tracked roots
  (`docs/routeB_bus/phase5_codex/out/xi_row_zeros.md`, ADDENDUM 14; erratum of 2026-09-04:
  `F_ground(γ_j) = C_j λ₁`, so `ρ_j − γ_j ≈ F(γ_j)/F'(γ_j) ~ 10⁻²⁶` already at `m=13`).

**Verdict on (1): use the length form (II); it is the interface matched to the evidence we own.**

### 1.4 The exact log-derivative in root coordinates

Using `Complex.cot_series_rep` (Mathlib, `Trigonometric/Cotangent.lean`)
`π cot(πx) = 1/x + Σ_{n≥1} 2x/(x²−n²)`, rescaled to `w = zL/2`, the sine's log-derivative is
`(L/2)cot(zL/2) = 1/z + Σ_{k≥1} 2z/(z²−x_k²)`, and `Q'/Q = 1/z + Σ_{k=1}^{N} 2z/(z²−x_k²)`. Hence,
for an even real-rooted row,

$$
\boxed{\;\frac{F_v'}{F_v}(z)=\sum_{j=1}^{N}\frac{2z}{z^2-\rho_j^2}\;+\;\sum_{k>N}\frac{2z}{z^2-x_k^2}\;}
$$

— the log-derivative of the explicit product `∏_ρ(1−z²/ρ²)·∏_{k>N}(1−z²/x_k²)` that
`proposition59_explicit_product_identity` already encodes. For two rows on the same lattice the
second sum cancels and

$$
\Delta_{g,t}(z)=\sum_{j=1}^{N}\frac{2z\,(\rho_j^{2}-\sigma_j^{2})}{(z^{2}-\rho_j^{2})(z^{2}-\sigma_j^{2})},
$$

under any pairing `ρ_j ↔ σ_j` of the two root multisets. The interface (II) is therefore a
**matched-root** statement, and the bound needed is a per-pair discrepancy `|ρ_j² − σ_j²|` for
**all** `j = 1..N`, not only for the tracked low ones. That is the first honest cost of (II) on the
same-family pair: the corpus has nothing on `ρ_j − σ_j` for `j` comparable to `N`.

---

## 2. Item (2) — which pairs the lock applies to

### 2.1 Ground vs prolate trial (`k1`/`g04`, same `(m,N)`) — **the lock applies verbatim**

Same `L`, same `S`, same `Q`, same sine. §1.2 applies with no residue. This is the only pair for
which the judge's length form is structurally viable, because `Δ_{g,t}(z) → 0` as `|z| → ∞`
(both tails identical), so the budget `R·sup|Δ| < 1` is not defeated by the geometry.

Asymmetry to record: **real-rootedness is available on the ground side only.** CCM Theorem 5.10
applies to the simple-even bottom eigenvector, not to the prolate trial. The corpus contains
*no* zero data at all for the prolate trial numerator (`xi_row_zeros.md` covers `ground` and
`xi_row`, not `k1/g04`). So on the trial side the boundary lower bound cannot be obtained from
real-rootedness and must be certified numerically.

### 2.2 Ground vs Ξ-sample row (same `(m,N)`) — **the lock applies; the guard is a live risk**

Same lattice again, so the cancellation is exact. But the Ξ-row numerator has genuine nonreal
roots: `xi_row_zeros.md` reports `NONREAL = 16/26, 28/46, 50/86` at `m = 13, 23, 43`, and the
erratum confirms one by Newton at `z = −18.8595 + 24.6602i` (`|z| = 31.05`).

**Where the boundary guard fails.** For a real-rooted numerator the zeros meet a concentric circle
only at `|ρ_j| = R` — a codimension-1 coincidence one can precommit away from by choosing `R`
between consecutive real roots. For a numerator with nonreal roots, `Z(P) ∩ {|z|=R} ≠ ∅` is again
codimension 1 in `R`, but there is no a priori list of the moduli to avoid: the `16/28/50` nonreal
roots have unknown moduli, and the one that is known sits at `|z| = 31.05`, i.e. just outside
`R = 28` and inside `R = 32`. The guard therefore cannot be discharged by a precommitment rule; it
must be certified per cell, per `R`, by interval arithmetic, with an explicit `ABSTAIN` branch.

Useful consequence: the Ξ-row is a **free positive control** for the detector. Ground and Ξ-row have
different divisors, so the certified integer must be nonzero on some precommitted disk; a detector
that returns 0 on every disk for this pair is broken.

### 2.3 Ground vs Ξ itself (target crosswalk) — **nothing cancels; the length form is out of budget**

Ξ is not a P59 transform. There is no lattice factor, no `Q`, no common prefactor. The comparison
must be made between two entire functions directly:

$$
\frac{1}{2\pi i}\oint_{\partial D}\left(\frac{F_g'}{F_g}-\frac{\Xi'}{\Xi}\right)dz
= N_D(F_g)-N_D(\Xi),
$$

valid whenever both are zero-free on `∂D`. With the Hadamard genus-0 product for the even function
`Ξ` (its centered zeros `z_ρ` come in `±`, conjugate quartets; `Σ|z_ρ|^{-2} < ∞`),

$$
\frac{\Xi'}{\Xi}(z)=\sum_{\rho}\frac{2z}{z^{2}-z_\rho^{2}},
\qquad
\Delta_{g,\Xi}(z)
=\underbrace{\sum_{j\le J}\Bigl[\tfrac{2z}{z^2-\rho_j^2}-\tfrac{2z}{z^2-\gamma_j^2}\Bigr]}_{\text{tracked, }\sim10^{-26}}
+\underbrace{\sum_{\text{ground far}}\tfrac{2z}{z^2-w^2}-\sum_{\Xi\text{ far}}\tfrac{2z}{z^2-z_\rho^2}}_{\text{unmatched tails}} .
$$

**What the length form then needs.** With `T` = the tracking height (largest modulus up to which the
ground zeros are certified to sit on `Ξ`'s zeros), the only bound available without a *pairing* of
the far zeros is the triangle inequality:

$$
\sup_{|z|=R}|\Delta_{g,\Xi}|
\;\le\;
\varepsilon_{\text{tracked}}
+\frac{2R}{1-R^{2}/T^{2}}\bigl(M_g(T)+M_\Xi(T)\bigr),
\qquad
M_g(T)=\!\!\sum_{|w|>T,\,w\in Z(F_g)}\!\!\frac1{|w|^{2}},\quad
M_\Xi(T)=\!\!\sum_{|z_\rho|>T}\!\!\frac1{|z_\rho|^{2}} .
$$

so the interface reduces to, essentially,

$$
\boxed{\;M_g(T)+M_\Xi(T)\;<\;\frac{1}{2R^{2}}\;}
$$

`[PAPER_ESTIMATE — NOT A RUN]` At `R = 18` the budget is `1.54·10⁻³`. On the best cell in the
corpus (`m = 43`, tracking to `T ≈ 92.5`, `x_N = 71.8`), the Riemann–von Mangoldt density gives
`M_Ξ(92.5) ≈ (log(T/2π)+1)/(2πT) ≈ 6.3·10⁻³`, and the ground side carries at minimum its lattice
tail `Σ_{k>N} x_k^{-2} = (L/2π)²·Σ_{k>N}k^{-2} ≈ 8.3·10⁻³`. The sum overshoots the budget by an
order of magnitude. Meeting it needs `T ≳ 800` and `N ≳ 2·10³` — two to three orders of magnitude
beyond the whole certified schedule.

**The structural reason, independent of any cell.** `F_g` has exponential type `L/2` (from
`sin(zL/2)`), so `|F_g'/F_g| → L/2` off the real axis; `Ξ` has order 1 maximal type, and by
Stirling `|Ξ'/Ξ(iy)| ≈ ½log(y/2π) → ∞`. Hence `|Δ_{g,Ξ}| ≳ ½log(R/2π) − L/2` for large `R` at fixed
`m`, and the budget `R·sup|Δ| < 1` can only ever be met in the regime `R ≪ γ₁ = 14.13`, where the
test is vacuous (`N_D = 0` on both sides). Any content requires `R > γ₁`, and then the budget can
only be recovered by driving `m` up so that the tracked height `T` outruns `R` — that is, by
exactly the convergence the lock is supposed to certify.

**If the far tails could be paired**, the bound would improve to `2R²|κ_g − κ_Ξ| < 1`. With the
measured curvature defect (`Progress_Log`, probe 4: `κ_k − κ_Ξ = 0.0028, 0.0032, 0.0027, 0.0021,
0.0014` at `m = 13…163`) this gives `1.81, 2.07, 1.75, 1.36, 0.91` at `R = 18` — marginally
satisfiable at `m = 163` only, and only at `R = 18`. The missing theorem is precisely the judge's
own `GLOBAL_PRODUCT_IDENTIFICATION_ADDS` item: *a pairing of the far ground zeros with the far Ξ
zeros with summable reciprocal-square discrepancy*. Nothing in the corpus supplies it; the proved
curvature ledger gives the **signed** total `κ = Σ 1/ρ²`, and a signed total does not bound an
unsigned tail difference.

### 2.4 The first uncontrolled term — stated twice, because the two interfaces need different things

**(A) Length form (II), ground vs Ξ.** No lower bound on `|F_g|` is needed at all: the
log-derivative is a sum over roots and only needs distance to the roots. The first uncontrolled term
is the **unmatched far-zero reciprocal-square tail `M_g(T) + M_Ξ(T)`**, which the triangle
inequality forces to appear un-cancelled and which the corpus bounds only through the signed
curvature `κ`, never through a pairing.

**(B) Rouché form (I), ground vs anything.** Here a boundary lower bound on `|F_g|` *is* needed. It
is **strictly weaker than the node-value tracking `Δ_n`, and it is not implied by `Δ_n`.** Two steps:

1. Real-rootedness (`ZerosRealOn`, CCM Thm 5.10, already the standing hypothesis of
   `proposition59CauchyNumerator_normalized_product`) gives, for an even real-rooted normalized `P`,
   `|1 − (x+iy)²/ρ²| = |ρ−x−iy||ρ+x+iy|/ρ² ≥ |ρ−x||ρ+x|/ρ² = |1−x²/ρ²|`, hence
   `|P(x+iy)| ≥ |P(x)|` for every real `x`. On `|z| = R` the modulus can therefore only be small
   near the real axis.
2. What remains is `|P_g(±R)|` (equal by evenness) together with simplicity/slope at the interior
   roots. **So the first uncontrolled term is `|F_g(R)| at the single real point `z = R`.**

This is weaker than `Δ_n` (which controls `2N+1` node values) and is *not* a consequence of it,
because `R` is not a node: `Δ_n` says nothing between nodes or off the real axis.

**CLOSES (a design fix that opens nothing).** Choose the boundary radius **on the lattice**,
`R = x_n = 2πn/L` for a precommitted `n ≤ N`. Then, by
`proposition59PoleKernel_sum_at_lattice` and `proposition59CauchyNumerator_eval_at_lattice`,

$$
F_g(x_n)=\sqrt L\,(-1)^n v_n ,\qquad
P_g(x_n)=v_n\prod_{k\ne n}(x_n-x_k),
$$

both exact and source-certified nonzero **iff `v_n ≠ 0`** — a hypothesis the project already
formalizes (`proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff`). The uncontrolled term
disappears on the ground side. Node radii exist inside every relevant `γ`-gap:

| cell | in `(γ₁,γ₂)` | in `(γ₂,γ₃)` | in `(γ₃,γ₄)` |
|---|---|---|---|
| m=13 | `x₇ = 17.148` | `x₉ = 22.047` | `x₁₁ = 26.947` |
| m=23 | `x₉ = 18.035` | `x₁₁ = 22.043` | `x₁₃ = 26.051` |
| m=43 | `x₁₀ = 16.706` | `x₁₃ = 21.717` | `x₁₆ = 26.729` |

Cost: the radius is then cell-dependent, so the disks are not literally the same across cells.
Trade-off to be precommitted, not decided after seeing results.

---

## 3. Item (3) — what source input would bound `sup_{∂D}|Δ|` without an inverse or a floor

Ranked by what the corpus actually owns.

1. **Same-lattice pairs (`ground` vs `trial`, `ground` vs `Ξ-row`).** Needed input: a per-pair root
   discrepancy `|ρ_j − σ_j|` for **all** `j ≤ N` under some pairing, not only the tracked low `j`.
   Available: nothing. Status: `NEW_ANALYTIC`. This is the honest content of
   `P59_LOG_DERIVATIVE_SOURCE_BOUND_NOT_AVAILABLE`.
2. **Ground vs Ξ.** Needed input: the far-tail pairing of §2.3. Available: only the signed curvature
   `κ_g` (Lean-exact via `proposition59RawTransform_secondDerivative_zero`) and the classical
   `κ_Ξ`. Status: `NEW_ANALYTIC`, and quantitatively out of reach on the certified schedule.
3. **The one input the corpus does own** is not a boundary bound at all: it is the S9
   evaluation-range datum `F_g(γ_j) = C_j(m)·λ₁` with `C_1(m)·L → ≈205`
   (`Progress_Log`, 2026-09-04). Paired with a **local slope lower bound** `|F_g'|` on a small disk
   `B(γ_j,r)`, it gives a *localization* certificate `|ρ_j − γ_j| ≤ |F_g(γ_j)|/inf_B|F_g'|` — which
   is what the judge demanded twice (ZEROPIN Q2, LEAKAGE Q3 `SMALL_VALUE_AT_TARGET_ZERO`). It
   supplies **location**, not **completeness**.

**Division of labour, stated plainly.** The winding lock's added value over the S9 slope certificate
is *completeness* — "no ground zero in `D` other than the matched ones". Its own sufficient
interface, however, needs the matched-pair bound as **input**. So the two are complementary, not
alternative, and neither is self-contained:

```
S9 value + slope lower bound  ->  location of the matched zeros
winding lock (given location) ->  completeness on D
tail pairing / recip-square   ->  identification of the limit  (still missing)
second jet (kappa)            ->  gauge pin, only AFTER complete divisor equality
```

Forbidden by the task and not used anywhere above: complement floors, `‖(K−λ₁)⁻¹‖`, assumed
convergence.

---

## 4. Item (4) — the planted failure and three more plants

All plants act on the analytic pair, anchored at `z = 0` so that `F(0)` is unchanged.

**Plant 1 (the judge's; `P59_EXTRA_REAL_ROOT_PAIR_WINDING_PLANT`).**
`F_plant(z) = F_g(z)·(1 − z²/a²)`, `0 < a < R` real. `F_plant(0) = F_g(0)`; parity, reality,
real-rootedness and order are all preserved; the second jet moves by `−2/a²` (so a κ-only check
*would* see it, but a κ-only check is not the discriminator under test). Expected certified integer:
`+2`. A detector that reports `0` is not a divisor certificate. Also run `a` just outside
(`a = R·(1+10⁻⁶)`, expect `0`).

**Plant 2 (boundary-guard plant).** `a = R` exactly, or `a = R + 10⁻³⁰i`. Then `P_plant` vanishes on
(or within any achievable enclosure of) `∂D`; the integrand has a pole on the contour and the
integer is undefined. **Required behaviour: `ABSTAIN`.** A detector that outputs any integer here —
including `0` or `2` — is broken. This plant is the reason the pipeline must have three outcomes
(`PASS` / `FAIL` / `ABSTAIN`), not two.

**Plant 3 (same count, displaced zero) — and why it is not artificial.**
`P̃ = P_g · (1 − z²/(ρ₁+δ)²)/(1 − z²/ρ₁²)`, a genuine polynomial of the same degree with the same
count in `D`. The winding lock **passes** and identification **fails**. Extra control that detects
it: replace the single circle by the judge's own divisor requirement — a winding integral on each
small disk `B(γ_j,r)` plus the statement that `Σ_j N_{B(γ_j,r)} = N_D`; then the plant is caught
whenever `δ > r`. Catching every `δ` requires `r → 0` with a proved rate, i.e. exactly the
quantitative `ρ_j → γ_j` statement. Alternatively the S9 value+slope certificate of §3.3 bounds
`δ` directly.

**This is the sharpest honest point in the report.** A concentric disk `|z| < R` sees only the
*modulus* of a zero. An off-line zeta zero at `ρ = β + iγ₀` sits at centered coordinate
`z_ρ = γ₀ − i(β − ½)`, i.e. at modulus `√(γ₀² + (β−½)²)` — arbitrarily close to `γ₀`. A real-rooted
ground family can match the concentric count exactly while every off-line zero is missed. **Plant 3
*is* the not-RH configuration.** Concentric-disk winding is therefore, by construction, blind to the
very configuration whose exclusion is the goal. The compact must be a union of small disks around
each target zero plus a certificate that the rest of `D` is zero-free — the judge's Q3 items 1–2 —
and a single circle is a calibration instrument, not a divisor certificate.

**Plant 4 (degree drop / escape to infinity).** Take a row with `Σ_{k∈S} v_k = 0`. Then
`deg P_v < 2N`: two or more zeros have escaped to `∞`. On every fixed `D` the winding lock reports
`0` and sees nothing. Only a count at `R > ` all roots — i.e. a degree/`∞` ledger — detects it. This
plant instantiates the judge's `GLOBAL_PRODUCT_IDENTIFICATION_ADDS` item "escape of excess zeros
from every compact" and shows it is not reachable from any fixed compact.

**Positive control (not a plant).** Ground vs Ξ-row at the same `(m,N)`: different divisors
(`NONREAL = 16/28/50`), so the detector must report a nonzero integer on some precommitted disk.

**Already-dead plant, re-checked.** The Robin-cosine pair `cos(πz/h)` vs
`cos(πz/h) − a(πz/h)sin(πz/h)` (verdict QUASIEIGEN) has a different zero divisor, so the winding
lock **does** separate it — consistent with `ROBIN_COSINE_PLANT: excluded, reason
DIFFERENT_ZERO_DIVISOR`.

---

## 5. Item (5) — interval-test design for one production cell

`SCOPE: FINITE_CELL`. Diagnostic; `DIAGNOSTIC_NEVER_A_PROOF`. **Not executed here** (numerics
forbidden by the task); this is the precommitment.

**Cells.** `(m,N) ∈ {(13,13),(13,26),(23,23),(43,43),(43,86)}` and bonus `(13,120)` for pairs
involving the trial; ground-vs-Ξ additionally at `m = 83, 163` where only the ground vector is
needed. Excluded for trial pairs: `m = 83, 163` (`TRIAL_GENERATOR_NOT_PARAMETRIZABLE`).

**Boundaries (precommit before any evaluation).**
Primary: circles `|z| = R`, `R ∈ {18, 23, 28}` — each strictly between consecutive `γ_j`
(`γ = 14.134725, 21.022040, 25.010858, 30.424876`) and strictly below `x_N` for every cell, so the
lattice tail contributes no zeros. Target counts for `Ξ`: `N_D(Ξ) = 2, 4, 6`. These are certified
integers, not assumptions: all zeta zeros to height `3·10¹²` are verified simple and on the line,
so on `R ≤ 28` the target divisor is a finite certified fact. **This is precisely why these three
disks are calibration, not evidence: the lock cannot learn anything about RH on a disk where the
target divisor is already known.**
Secondary (the §2.4 CLOSES): node radii `R = x_n` from the table in §2.4, which make the ground-side
boundary lower bound exact.

**Evaluation form — never expand the polynomial.** The erratum of 2026-09-04 records that
`acb_poly.roots()` on the degree-`2N` numerator with coefficients of size `10²⁹` returned roots good
only to `10⁻⁸`. The same cancellation would poison a coefficient-space boundary evaluation. Instead
evaluate the ratio in its native Cauchy form, where the sine and `Q` cancel *in the arithmetic too*:

$$
h(z)\;=\;\frac{P_g(z)}{P_t(z)}\;=\;
\frac{\sum_{k\in S} g_k/(z-x_k)}{\sum_{k\in S} t_k/(z-x_k)} .
$$

`2N+1` well-conditioned terms, no growth, no expansion. Working precision `dps = 120` suffices for
`N ≤ 120`; keep the ledger's `240` for the ground eigenvector solve itself.

**Certification of the integer (argument tracking, no quadrature).**
1. Partition `∂D` into `M` arcs `A_i` with midpoints `z_i`.
2. For each arc, evaluate `h` on a **ball** covering `A_i` (`arb`/`flint` ball input gives the
   enclosure directly). Require `0 ∉ h(A_i)` — this certifies the boundary guard, arc by arc, with
   no separate Lipschitz argument.
3. Require each enclosure `h(A_i)` to have angular width `< π/2` as seen from `0`, and consecutive
   enclosures to overlap. Then the argument increment across each arc is determined, and the sum is
   the certified winding number `∈ ℤ`.
4. `M` is refined adaptively; start at `M = 512` and double until (2) and (3) hold or `M > 2¹⁶`, in
   which case the cell returns `ABSTAIN`.

**Precision rule.** If, contrary to the above, a coefficient-space evaluation is ever used, budget
`dps ≥ 60 + 2N·log₁₀(max(1, 2π/L)) + 2N·log₁₀ R`; for `(13,120)` this already exceeds `400`. The
Cauchy form removes the rule entirely, which is the point of using it.

**Ξ evaluation** (crosswalk pair only). Build `Ξ(z) = ξ(½+iz)` from certified `Γ` and `ζ`
enclosures; `N_D(Ξ)` on `R ≤ 28` is taken from the verified-zeros fact above, not from the
integral, and the integral is used only as a consistency check on the pipeline.

**Planted-failure controls, run in the same pipeline, results precommitted.**

| control | construction | required output |
|---|---|---|
| P1 | `h·(1 − z²/a²)`, `a = 20 < R = 23` | certified `+2` |
| P1' | `a = R(1+10⁻⁶)` | certified `0` |
| P2 | `a = R` exactly | `ABSTAIN` |
| P3 | `ρ₁ → ρ₁+δ`, `δ = 10⁻³` | certified `0` (documents the blind spot) |
| P4 | row rescaled so `Σ_k v_k = 0` | certified `0` on every `D` (documents the blind spot) |
| PC | ground vs Ξ-row | certified nonzero on some `R` |

A run in which P1 does not return `+2`, or P2 does not abstain, invalidates the cell — the detector,
not the mathematics, is then the object under test.

**What a green run would and would not license.** It would license: "on these precommitted disks,
at these cells, the ground and trial (resp. ground and Ξ) numerator divisors have equal total
count." It would not license any statement about locations, about zeros outside `D`, about the
second jet, or about any cell not precommitted. `ZERO_CONSISTENT_RESULT:
INCONCLUSIVE_WITHOUT_ANALYTIC_OR_INTERVAL_CERTIFICATE` remains the judge's correct label.

---

## 6. Item (6) — Mathlib inventory (`.lake/packages/mathlib` @ `2df2f015`, 2025-12-13)

**Exists, directly usable.**

| object | file | use here |
|---|---|---|
| `logDeriv`, `logDeriv_mul`, `logDeriv_div`, `logDeriv_const_mul`, `logDeriv_prod`, `logDeriv_comp` | `Analysis/Calculus/LogDeriv.lean` | §1.1 cancellation of the common P59 factor — pure algebra, no analysis |
| `MeromorphicOn.divisor`, `divisor_mul`, `divisor_inv`, `divisor_pow`, `divisor_smul`, `AnalyticOnNhd.divisor_nonneg` | `Analysis/Meromorphic/Divisor.lean` | divisor-level form of §1.1: `divisor(F_v) = divisor(sin/Q) + divisor(P_v)`, so the common factor cancels **without** the argument principle |
| `MeromorphicOn.extract_zeros_poles`, `..._log`, `meromorphicTrailingCoeffAt_...` | `Analysis/Meromorphic/FactorizedRational.lean` | `f = (factorized rational)·(nonvanishing g)`; the converse direction "equal divisors ⇒ equal up to a nonvanishing factor" |
| `MeromorphicOn.circleAverage_log_norm` (**Jensen's formula**) | `Analysis/Complex/JensenFormula.lean` | present, but see below |
| `logCounting`, proximity, characteristic, First Main Theorem | `Analysis/Complex/ValueDistribution/` | Nevanlinna counting function `N(r,f)` |
| `circleIntegral`, Cauchy integral formula on circles (`DifferentiableOn.circleIntegral_sub_inv_smul`, `two_pi_I_inv_smul_circleIntegral_...`) | `Analysis/Complex/CauchyIntegral.lean` | the integral itself exists; the *interpretation* as a zero count does not |
| `Complex.cot_series_rep` | `Analysis/SpecialFunctions/Trigonometric/Cotangent.lean` | the Mittag-Leffler expansion used in §1.4 |
| `Complex.log`, `Complex.arg`, `Circle`, `circleMap` | `Analysis/SpecialFunctions/Complex/{Log,Arg,Circle,CircleMap}.lean` | argument tracking, if the winding number is defined by hand |
| `Complex.Hadamard` | `Analysis/Complex/Hadamard.lean` | **three-lines theorem only** — *not* the Hadamard factorization theorem |

**Missing — every one of them.** `rg -in "winding" Mathlib/` returns **zero hits** in the whole
library; likewise `rouch` and `"argument principle"`.

* no `windingNumber` / index of a curve about a point;
* no argument principle in any form (no "number of zeros = contour integral");
* no Rouché theorem, in either the classical or the symmetric form;
* no Hurwitz theorem on zeros of locally uniform limits;
* no Hadamard factorization / Laguerre–Pólya API.

**One line:** Mathlib has `logDeriv` + the full `MeromorphicOn.divisor` algebra + Jensen's formula
+ Nevanlinna counting + circle Cauchy integrals; it has **no** winding number, **no** argument
principle, **no** Rouché, **no** Hurwitz.

**Consequence for Lean sequencing.** The judge's `FIRST_SOURCE_STEP` ("prove the common P59
sine/lattice factor cancels exactly in the anchored logarithmic-derivative difference") is
**LEAN_READY today** — `logDeriv_mul`/`logDeriv_div`, or at divisor level `divisor_mul` +
`divisor_inv`, with `differentiable_proposition59RawTransform` and
`proposition59CauchyDenominator_eval_ne_zero` supplying the side conditions. Nothing new is needed.

The step after it is **NEW_ANALYTIC in Mathlib terms**: the argument principle or Rouché must be
built. Cheapest honest route inside the existing API: define the winding number of a `C¹` loop as
`(2πi)⁻¹∮ dz/(z−w)`, prove `∮ f'/f` counts zeros for a *polynomial* (finite product, `logDeriv_prod`
+ the `1/(z−ρ)` integral) — which is all the winding lock actually needs, since after §1.1 both
sides are polynomials. **A polynomial-only argument principle is a strictly smaller Lean target than
the general one, and it suffices for `P59_FIXED_COMPACT_DIVISOR_COUNT_LOCKED`.**

Jensen's formula is present but is the wrong instrument here: it bounds `n(R)` from above by a
circle average of `log|F|`, and with the project's proved Gaussian envelope
`|F_k(z)/F_k(0)| ≤ e^{κ|z|²}` it gives `n(18) ≤ e²κR² ≈ 60` against a target of `2`
`[PAPER_ESTIMATE]`. `F_g` genuinely has that many zeros below `e·R`; the bound is not lossy, the
tool is simply not a divisor certificate.

---

## 7. Honest summary — what is settled, what is not

**Settled on paper.**
1. The common P59 factor cancels exactly, and more of it cancels than the judge stated (the
   Cauchy denominator `Q` as well as the sine). Same-`(m,N)` pairs reduce to two polynomials of
   degree `2N`. `P_COMMON_LATTICE_FACTOR_CANCELS_IN_LOG_DERIVATIVE`: CONFIRMED, finite algebra,
   Lean-ready.
2. Because the factor is common, `∂D` need not avoid the lattice; a node radius is legal, and a node
   radius makes the ground-side boundary value exact.
3. The judge's length form and Rouché are incomparable as boundary hypotheses; the disk version of
   the length form implies Rouché. For this project's evidence the length form is the right one,
   because our tight data are about divisors, not values.

**Not settled, and not manufactured.**
4. The length form is structurally restricted to same-lattice P59 pairs. For ground-vs-Ξ it is out
   of budget by an order of magnitude on the entire certified schedule, and the obstruction is a
   type mismatch (`F_g` has exponential type `L/2`, `Ξ` has maximal type), not a constant.
5. The first uncontrolled term is the unmatched far-zero reciprocal-square tail
   `M_g(T)+M_Ξ(T)` — a signed curvature ledger cannot bound an unsigned tail difference.
6. For the Rouché form the first uncontrolled term is the single real boundary value `|F_g(R)|`,
   weaker than `Δ_n` and not implied by it; closed by the node-radius choice.
7. A concentric-disk winding lock is blind to plant 3, and plant 3 is the not-RH configuration.
   The single circle is calibration; the divisor certificate needs small disks around each target
   zero plus a zero-free complement — the judge's Q3 items 1–2, unchanged.
8. `P_FIXED_COMPACT_SOURCE_BOUND_CLOSES_WITHOUT_FULL_TRACKING` (judge probability 0.35): this
   preflight moves it **down**. On the same-lattice pair the bound needs per-pair root discrepancies
   for all `j ≤ N`; on the crosswalk pair it needs a far-tail pairing. Neither is "without full
   tracking".

**CLOSES / OPENS of this report.**
`CLOSES`: the FIRST_SOURCE_STEP as a Lean target (no new API); the boundary-lower-bound gap on the
ground side (node radius, using an existing project theorem); the choice between interfaces (I) and
(II); the Mathlib question. `OPENS`: nothing — no new tool, script, file or "input" is proposed. The
interval design in §5 uses the existing `phase5_codex` evaluation stack and the existing ledger
cells; the only new artefact would be one script, and it is not proposed here because the numerics
are not authorized.

`SCOPE: FINITE_CELL` for §1, §4, §5; `COFINAL_FAMILY` for §2.3, §3; `ABSTRACT` for §1.2, §1.3, §6.
`VERIFIER: PAPER` throughout, except the `[PAPER_ESTIMATE]`-marked magnitudes, which are
back-of-envelope and are `DIAGNOSTIC_NEVER_A_PROOF`.
No Lean source was edited. No numerical run was performed. No route promotion. `PX_RH_CLAIM: NOT_MADE`.
