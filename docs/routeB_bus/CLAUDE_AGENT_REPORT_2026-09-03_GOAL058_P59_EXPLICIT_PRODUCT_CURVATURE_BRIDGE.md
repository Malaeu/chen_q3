# Claude-agent report — Goal 058: P59 explicit-product curvature bridge (Lean)

Date: 2026-09-03 (revision 2, after the coordinator authorized the finite route for steps 5–7)
Task: `docs/Codex/TASK_2026-09-03_goal058_p59_explicit_product_curvature_bridge_lean.md`
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.md` §2.1–2.7
Executor: Linux-Claude agent (not Codex); prefix `[Linux-Claude-agent][rh_clean][Goal058]`
Branch: `claude_agent/goal058-p59-bridge`, rebased on `origin/rh_clean` (which already carries steps 1–4a)
Pushed: NO (task forbids push)
File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean` (1483 lines)

```yaml
RESULT: SUBSTANTIALLY_COMPLETE
STEPS_KERNEL_GREEN: [1, 2, 3, 4a, 5, 6, 7]
STEPS_PARTIAL: [4b]          # green off the real axis; NOT claimed at a removable node
FAILURE_CODE: P59_EULER_TAIL_LIMIT_API_GAP   # scoped to 4b alone; blocks nothing else
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
```

## The judge's §2.1, bullet by bullet

| §2.1 bullet | declaration | status |
|---|---|---|
| `-(iteratedDeriv 2 F 0)/(2 * F 0) = (κ_F : ℂ)`, `κ_F` REAL | `proposition59_curvature_coercion` | GREEN |
| `0 ≤ κ_F` | `proposition59Curvature_nonneg` | GREEN |
| `κ_F = Σ_{ρ∈R⁺} ρ⁻² + (L²/4π²) Σ_{k>N} k⁻²` | `proposition59Curvature_eq_root_sum_add_tail` (`rfl`) | GREEN |
| `‖F z‖ ≤ ‖F 0‖ exp(κ_F ‖z‖²)` for every `z ∈ ℂ` | `proposition59_compact_envelope` | GREEN |
| `κ_F = (L²/2)[1/12 + (1/(2π² v₀)) Σ_{k≠0} v_k/k²]` | `proposition59_curvature_closed_form` | GREEN |
| §2.7 roof consequence on a ball | `proposition59_normalized_bound_on_ball` | GREEN |

## Commits (one step per commit, each kernel-green before the next)

| commit | step | content |
|---|---|---|
| `5293a75f` | 1 | finite Cauchy numerator identity |
| `8d9db9f8` | 2 | numerator root ⟹ transform root; plants A, B |
| `58f3c765` | 3 | even real-rooted quadratic product (abstract) |
| `9bea2990` | 3 | applied to `P_N`: evenness, `P_N(0) ≠ 0`, normalized product |
| `bace1212` | 4a | node-safe explicit product identity |
| `de108de0` | — | report (rev 1) + plant-D lemma |
| `0e1b6d1e` | 5 | exact second jet from the explicit product |
| `f92e3fdb` | 6 | real curvature scalar and the zero sum |
| `9eaaa835` | 7 | global Gaussian envelope |
| `f6cbea62` | 4b | Euler tail product off the real axis |

## Per-step status

### Step 1 — `P59_FINITE_CAUCHY_NUMERATOR_IDENTITY` — KERNEL GREEN

`proposition59CauchyDenominator`, `proposition59CauchyNumerator` (both in `Polynomial ℂ`; over `ℂ[X]`
`Polynomial.Splits` is free and "real root" is the honest statement `z.im = 0`);
`proposition59CauchyDenominator_eval`, `proposition59CauchyNumerator_eval`,
`proposition59CauchyDenominator_eval_ne_zero`;
`proposition59_finite_cauchy_numerator_identity` (off-lattice `∑ v_k/(z−x_k) = P_N(z)/D_N(z)`);
`proposition59CauchyNumerator_eval_at_lattice` (`P_N(x_j) = v_j ∏_{k≠j}(x_j−x_k)`);
`proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff` (`P_N(x_j) = 0 ↔ v_j = 0`).

`sourceLagrangePolynomial` (`RankOneCorrectionLagrangePolynomial.lean`) was checked first: it *is* the
same shape (`∑_k C (ξ k) * ∏_{j≠k} (C (λ j) − X)`), but it lives over `ℝ`, is indexed by an abstract
`Fintype`, and orients its factors as `(λ_j − s)`. Reusing it would have forced a `Fintype`-subtype
carrier plus an `ℝ → ℂ` transport through every later step, while the target object `F` is `ℂ → ℂ`.
Not reused — a recorded decision, not an oversight.

### Step 2 — `P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT` — KERNEL GREEN

`proposition59RawTransform_at_lattice` (exact removable sampling `F(x_j) = √L (−1)^j v_j`, built on
`proposition59PoleKernel_at_lattice_sign`); `proposition59_numerator_root_imp_transform_root` (both
branches — the included-lattice branch runs through `v_j = 0` and the removable value, never through a
global cancellation of the sine against the denominator);
`proposition59CauchyNumerator_roots_real` (`ZerosRealOn Set.univ F` ⟹ every complex root of `P_N` is
real). `ZerosRealOn` is consumed here and nowhere else; steps 3–7 inherit it only through this.

### Step 3 — `P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT` — KERNEL GREEN

`rootMultiplicity_neg_of_even` (private) — for `p.comp (−X) = p`, `rootMultiplicity (−a) p =
rootMultiplicity a p`, by transporting `(X − C a)^n ∣ p` through `comp (−X)`
(`Polynomial.le_rootMultiplicity_iff`). Mathlib has no root-multiplicity-under-composition lemma;
this is the local finite-polynomial glue the judge predicted, and it stays local.
`roots_map_neg_of_even`; `positiveRootMultiset` and `positiveRootMultiset_pos`;
`eval_div_eval_zero_eq_prod_positiveRootMultiset` — `p(z)/p(0) = ∏_{ρ∈R⁺}(1 − z²/ρ²)` via
`Polynomial.Splits.eval_eq_prod_roots` with `Splits` from `IsAlgClosed.splits`. No Hadamard
factorization, no entire-function order predicate, no Laguerre–Pólya.

Applied to `P_N`: `proposition59Pole_neg`, `card_Icc_symm`,
`proposition59CauchyNumerator_eval_neg` (evenness by explicit double reindexing with `Equiv.neg ℤ`
plus the parity of `|I_N \ {k}| = 2N`), `proposition59CauchyNumerator_eval_zero_ne_zero`,
`proposition59CauchyNumerator_normalized_product`.

### Step 4a — the removable-node-safe explicit product — KERNEL GREEN

`proposition59CauchyDenominator_eq_included_factors` —
`v_0 · D_N(z) = z · P_N(0) · ∏_{k∈I_N, k≠0}(1 − z/x_k)`, finite algebra, all `z`.
`proposition59_included_factor_product_identity` and `proposition59_explicit_product_identity` — for
**every** `z`,

```
F(z) · ∏_{k∈I_N, k≠0}(1 − z/x_k)
  = F(0) · ∏_{ρ∈R⁺}(1 − z²/ρ²) · (proposition59PoleKernel L 0 z / L),
```

where `proposition59PoleKernel L 0 z / L` is exactly the entire `sin(zL/2)/(zL/2)`. The included
lattice factors stay on the **left**, so no denominator is cancelled at a node. The three cases are
off-lattice (Cauchy quotient), `z = 0` (removable value `poleKernel L 0 0 = L`) and `z = x_j`, `j ≠ 0`
(both sides vanish *exactly* — the left by its `k = j` factor, the right by
`proposition59PoleKernel_at_lattice_sign`). The judge's "this extension must be explicit in Lean" is
discharged with no density or continuity hand-wave.

### Step 4b — GREEN OFF THE REAL AXIS, not claimed at a node

`proposition59_euler_tendsto` transports `Complex.tendsto_euler_sin_prod` into the `x_k = 2πk/L`
coordinate. `proposition59_normalized_euler_tail_product`: for `z.im ≠ 0`,

```
Tendsto (fun n => ∏_{ρ∈R⁺}(1 − z²/ρ²) · ∏_{j∈Ico N n}(1 − z²/x_{j+1}²)) atTop (𝓝 (F z / F 0)).
```

Off the real axis the included factor `A z` is nonzero and cancels honestly. At a removable node the
same statement would need the *identified* locally uniform Euler product and is deliberately not
claimed. See the failure section.

### Step 5 — `P59_CURVATURE_SECOND_JET_REAL` — KERNEL GREEN

The finite route: differentiate the node-safe step-4a identity `F · A = F(0) · Q · s` twice at the
origin, instead of differentiating an infinite product.

* `iteratedDeriv_two_mul_of_differentiable` — second-order Leibniz at a point for two entire functions.
* `quadProductPoly` with `quadProductPoly_coeff_zero/one/two` — `∏(1 − c_i X²)` has coefficients
  `1, 0, −∑ c_i` (multiset induction). All the "second jet of a finite product" content lives here.
* `prod_erase_zero_Icc_symm` — the symmetric-window pairing, so the included factor
  `∏_{k≠0}(1 − z/x_k)` *is* `∏_{k=1}^N(1 − z²/x_k²)`, an even polynomial.
* `proposition59IncludedFactors_eq_eval`, `proposition59RootFactors_eq_eval` — both factors are
  polynomial evaluations.
* `proposition59Sinc_at_zero`, `proposition59Sinc_secondDeriv` — `s(0) = 1`, `s''(0) = −L²/12`, read
  straight off the existing `proposition59PoleKernel_secondDerivative_zero`.
* `proposition59_secondDerivative_zero_from_product`:

```
iteratedDeriv 2 F 0 = F 0 · ( −2 Σ_{ρ∈R⁺} ρ⁻² − L²/12 + 2 Σ_{k=1}^N x_k⁻² ).
```

Every first derivative at the origin is multiplied by a partner that vanishes there (`A` and `Q` are
even), so the unknown `F'(0)` never survives. No Euler tail is used.

### Step 6 — `P59_CURVATURE_ZERO_SUM` — KERNEL GREEN

`proposition59HeadZetaTwo`; `proposition59TailZetaTwo` — a genuine `tsum`;
`proposition59TailZetaTwo_hasSum` — `∑_{k>N} k⁻² = π²/6 − ∑_{k=1}^N k⁻²` from `hasSum_zeta_two` via
`hasSum_nat_add_iff'`; `proposition59TailZetaTwo_nonneg`.
`proposition59Curvature : ℝ` — a **real** number, `Σ_{ρ∈R⁺} ρ⁻² + (L²/4π²)·tail`.
`proposition59Curvature_nonneg` — `0 ≤ κ_F`, immediate from that definition (positive roots,
nonnegative tsum); this is exactly why `κ_F` is *defined* by the root-plus-tail formula and not by
the analytic quotient. `proposition59_curvature_coercion` —
`-(iteratedDeriv 2 F 0)/(2 · F 0) = (κ_F : ℂ)`. `proposition59_curvature_closed_form` — the judge's
fourth boxed formula, obtained by feeding the coercion identity the *existing* exact
`proposition59RawTransform_secondDerivative_zero`.

### Step 7 — `P59_CURVATURE_COMPACT_ENVELOPE` — KERNEL GREEN

The Euler tail is **bounded, never identified**.

* `norm_quadProduct_le_exp` / `norm_prod_one_sub_le_exp` — `‖∏(1 − c_i z²)‖ ≤ exp(‖z‖² ∑‖c_i‖)` from
  `Real.add_one_le_exp`.
* `sum_Ico_norm_pole_sq_inv_le` — every finite tail block is dominated by `(L²/4π²)·tail`.
* `proposition59_compact_envelope_offAxis` — for `z.im ≠ 0`: `‖s z‖ ≤ ‖A z‖ exp(‖z‖²·κ_tail)` by
  `le_of_tendsto` on the Euler partial products, then the step-4a identity in normed form and an
  honest cancellation of `‖A z‖ > 0`.
* `dense_im_ne_zero` — `{z | z.im ≠ 0}` is dense in `ℂ`.
* `proposition59_compact_envelope` — the inequality is a **closed** condition and both sides are
  continuous, so it extends from that dense set to every `z ∈ ℂ`, lattice points included. This is the
  step where an *identity* would have needed the locally uniform product and an *inequality* does not.
* `proposition59_normalized_bound_on_ball` — §2.7: `κ_F ≤ C` and `‖z‖ ≤ R` give
  `‖F z‖/‖F 0‖ ≤ exp(C R²)`.

## Failure code — now scoped to step 4b alone

```
P59_EULER_TAIL_LIMIT_API_GAP
```

**What is not claimed.** Exactly one thing: the tail product *identity*
`F(z)/F(0) = ∏_{ρ∈R⁺}(1 − z²/ρ²) · lim_M ∏_{k=N+1}^{M}(1 − z²/x_k²)` **at a removable node**
`z = x_j`, `|j| ≤ N`. Off the real axis it is proved. Nothing else in the file depends on it: the
curvature identity, `κ_F ≥ 0`, the closed form and the global envelope are all established without it.

**Why it is blocked.** With `w = Lz/(2π)` a node has `w ∈ ℤ`, so `∏_{k≤M}(1 − w²/k²)` is identically
`0` for `M ≥ |w|` and the tail cannot be recovered by dividing the full product by the finite head.
Mathlib `2df2f015` offers `Complex.tendsto_euler_sin_prod` (pointwise), `Complex.multipliable_sineTerm`
(convergence at every `x`, value unidentified) and `Complex.HasProdLocallyUniformlyOn_euler_sin_prod`
— but the *identified* locally uniform statement is restricted to `ℂ_ℤ`, which excludes exactly the
nodes. The helper that would let one redo the compact bound for the shifted family,
`Complex.sineTerm_bound_aux`, is `private`.

**Missing declaration (named).** Either

* `Complex.HasProdLocallyUniformlyOn_euler_sin_prod` stated on `Set.univ` / on every compact rather
  than on `ℂ_ℤ`, or
* a tail form, e.g. `Continuous fun z : ℂ => ∏' n : ℕ, (1 - z ^ 2 / ((n + N + 1 : ℕ) : ℂ) ^ 2)`
  (a `MultipliableUniformlyOn` / `HasProdUniformlyOn` statement for
  `fun n z => 1 + Complex.sineTerm z (n + N)` on every compact of `ℂ`),

neither of which exists.

**Not a blocker elsewhere.** No `P59_PRODUCT_BRIDGE_REMOVABLE_NODE_MISMATCH`, no
`P59_EVEN_ROOT_MULTISET_PAIRING_API_GAP` (the pairing closed locally, as the judge predicted), no
`P59_CURVATURE_SECOND_JET_NORMAL_FORM_GAP`.

## Note for the judge — the finite route, executed

Revision 1 observed that the infinite product is not logically necessary for the curvature identity.
Revision 2 carried that out. Rather than the coefficient computation sketched there
(`P_N = v₀E + zEg`), the implemented route differentiates the step-4a identity twice at the origin,
which is cheaper: the whole "second jet of a finite product" content collapses into one reusable
statement, `quadProductPoly_coeff_two`. `hasSum_zeta_two` then converts `L²/12 − 2∑_{k≤N} x_k⁻²`
into `2·(L²/4π²)·∑_{k>N} k⁻²`.

The envelope did need the tail after all — near a node the included factors on the left of 4a are
small and cannot be divided out — but only as a **bound**, and a bound survives passage to the
closure of a dense set where an identity does not. That is the whole trick of step 7, and it is why
the Mathlib gap above no longer blocks §2.1.

## Mandatory plants

| plant | form | result |
|---|---|---|
| A | two compiling `example`s | PASS |
| B | one compiling `example` | PASS |
| C | hypothesis-consumption + arithmetic counterexample (below) | PASS |
| D | compiling lemma `proposition59RawTransform_at_zero_ne_zero_iff` | PASS |

**A** (`N = 1`, `v_0 = 1`, `v_{±1} = 0`). Two `example`s:
`(proposition59CauchyNumerator L {-1,0,1} (fun k => if k = 0 then 1 else 0)).eval z
 = (z − x_{−1})(z − x_1)`, and
`proposition59RawTransform L {-1,0,1} … (proposition59Pole L 1) = 0` derived *through*
`proposition59_numerator_root_imp_transform_root`. The two included factors are produced by `P_N`
itself, and the transform root at `±x_1` comes from the numerator, not from the sine.

**B** (`N = 1`, `v_{−1} = v_0 = v_1 = 1`). `example`: for every `j ∈ {−1,0,1}`,
`proposition59RawTransform L {-1,0,1} (fun _ => 1) (proposition59Pole L j) ≠ 0` — the included lattice
values are nonzero, so they do not survive as sine zeros.

**C** (non-even row). The paired-quadratic theorems are unavailable by construction: evenness is an
explicit hypothesis with no default instance —
`eval_div_eval_zero_eq_prod_positiveRootMultiset` requires `heven : ∀ z, p.eval (−z) = p.eval z`, and
`proposition59CauchyNumerator_normalized_product`, `proposition59_explicit_product_identity`,
`proposition59_secondDerivative_zero_from_product`, `proposition59_curvature_coercion`,
`proposition59_compact_envelope` all require `hv : ∀ k, v (−k) = v k`. There is no term of either
type for a non-even row. It is also *false* there, not merely unproved: for `N = 1`, `v_{−1} = 1`,
`v_0 = 1`, `v_1 = 0` one gets `P_1(z) = 2z² − x_1 z − x_1²` with real roots `x_1` and `−x_1/2`,
`P_1(0) = −x_1²`, so `P_1(z)/P_1(0) = 1 + z/x_1 − 2z²/x_1²`, which carries an odd term and cannot
equal any product of `(1 − z²/ρ²)`.

**D** (`F(0) = 0`). `proposition59RawTransform_at_zero_ne_zero_iff` proves `F 0 ≠ 0 ↔ v 0 ≠ 0`, so
the hypothesis `hv0 : v 0 ≠ 0` carried by every theorem from step 4a onwards *is* the judge's
`F 0 ≠ 0`. Without it `P_N(0) = 0`, the normalization `P_N(z)/P_N(0)` is division by zero, and
`eval_div_eval_zero_eq_prod_positiveRootMultiset` (which requires `p.eval 0 ≠ 0`) has no applicable
instance. The theorems are unavailable.

## κ is real

No complex number is ordered anywhere in this file. `positiveRootMultiset : ℂ[X] → Multiset ℝ`
returns **real** roots (`Complex.re` of roots already proved real), `positiveRootMultiset_pos` is an
inequality between reals, and `proposition59Curvature : ℝ → ℕ → (ℤ → ℝ) → ℝ` is a real-valued
definition. The only statement relating it to the complex second jet is the *equation*
`-(iteratedDeriv 2 F 0)/(2 · F 0) = (κ_F : ℂ)`; `0 ≤ κ_F` is proved entirely in `ℝ`, from the
definition, never by ordering the quotient.

## Validation

```
q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean   OK (no errors, no warnings)
                   lake build Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge           OK (7774 jobs)
repo root:         scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean   "q3_check ok"
```

`#print axioms` for every public theorem in the file — the step-1..4a set, plus
`quadProductPoly_coeff_zero/one/two`, `prod_erase_zero_Icc_symm`,
`proposition59IncludedFactors_eq_eval`, `proposition59RootFactors_eq_eval`,
`proposition59_secondDerivative_zero_from_product`, `proposition59TailZetaTwo_hasSum`,
`proposition59TailZetaTwo_eq`, `proposition59TailZetaTwo_nonneg`, `proposition59Curvature_nonneg`,
`proposition59_curvature_coercion`, `proposition59_curvature_closed_form`,
`proposition59Curvature_eq_root_sum_add_tail`, `proposition59Pole_ofReal`,
`proposition59_compact_envelope`, `proposition59_normalized_bound_on_ball`,
`proposition59_normalized_euler_tail_product`:

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no `exact?`, no new axiom, no `phase5_scripts`, no precommit, no queue edit,
no route promotion, no RH claim.

## Anything strange

1. **`Real.prod_one_add_le_exp_sum` was not used.** The judge named it for the exponential estimate,
   but it is a `Finset` statement while the positive-root product is a `Multiset` (roots carry
   multiplicity). A four-line induction on `Real.add_one_le_exp` covers both, so the local
   `norm_quadProduct_le_exp` is used instead. Flagged as a deviation from the named Mathlib fact
   list, not because anything is weaker.
2. **`sourceLagrangePolynomial` overlap.** Same algebraic object as `P_N` up to the `(λ_j − s)`
   orientation (harmless: the erased carrier has even cardinality `2N`), but over `ℝ` and over an
   abstract `Fintype`. Not reused — recorded as a decision.
3. **Build artefacts.** The worktree's `.lake` is a symlink into the owner's main checkout, so
   `lake build` added exactly one new olean
   (`Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.olean`) to the shared build
   directory. Nothing existing was rebuilt or overwritten.
4. **Nothing cofinal is claimed.** Everything above is finite-cell for one fixed `N`;
   `proposition59_normalized_bound_on_ball` takes `κ_F ≤ C` as a *hypothesis* and does not produce
   one. The source wall `sup_j κ_{F_j} < ∞` is untouched.
5. **`ZerosRealOn` is consumed exactly once**, in step 2; steps 3–7 inherit it only through
   `proposition59_explicit_product_identity`.
