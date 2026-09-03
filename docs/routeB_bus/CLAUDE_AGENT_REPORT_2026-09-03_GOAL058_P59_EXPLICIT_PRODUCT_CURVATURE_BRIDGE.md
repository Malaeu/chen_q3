# Claude-agent report — Goal 058: P59 explicit-product curvature bridge (Lean)

Date: 2026-09-03
Task: `docs/Codex/TASK_2026-09-03_goal058_p59_explicit_product_curvature_bridge_lean.md`
Judge source: `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CURVATURE_BRIDGE_PROOF_AND_HS_REPRESENTATION_2026-09-03.md` §2.1–2.7
Executor: Linux-Claude agent (not Codex); prefix `[Linux-Claude-agent][rh_clean][Goal058]`
Branch: `claude_agent/goal058-p59-bridge`, based on `origin/rh_clean` = `ed343593`
Pushed: NO (task forbids push)
File: `q3.lean.aristotle/Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean` (591 lines)

```yaml
RESULT: PARTIAL
STEPS_KERNEL_GREEN: [1, 2, 3, 4a]
STEPS_NOT_ATTEMPTED_OR_OPEN: [4b, 5, 6, 7]
FAILURE_CODE: P59_EULER_TAIL_LIMIT_API_GAP
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
```

## Commits (in order, each kernel-green before the next)

| commit | step | content |
|---|---|---|
| `adae8598` | 1 | finite Cauchy numerator identity |
| `21260a65` | 2 | numerator root ⟹ transform root; plants A, B |
| `7c4f4bdd` | 3 | even real-rooted quadratic product (abstract) |
| `49cfb52e` | 3 | applied to `P_N`: evenness, `P_N(0) ≠ 0`, normalized product |
| `acfaa244` | 4a | node-safe explicit product identity |
| (this report + plant-D lemma) | — | report commit |

## Per-step status

### Step 1 — `P59_FINITE_CAUCHY_NUMERATOR_IDENTITY` — KERNEL GREEN

* `proposition59CauchyDenominator`, `proposition59CauchyNumerator` (`Polynomial ℂ`; working over `ℂ[X]`
  makes `Polynomial.Splits` free and makes "real root" the honest statement `z.im = 0`);
* `proposition59CauchyDenominator_eval`, `proposition59CauchyNumerator_eval`,
  `proposition59CauchyDenominator_eval_ne_zero`;
* `proposition59_finite_cauchy_numerator_identity` — off-lattice `∑ v_k/(z−x_k) = P_N(z)/D_N(z)`;
* `proposition59CauchyNumerator_eval_at_lattice` — `P_N(x_j) = v_j ∏_{k≠j}(x_j−x_k)`;
* `proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff` — `P_N(x_j) = 0 ↔ v_j = 0`.

`sourceLagrangePolynomial` (`RankOneCorrectionLagrangePolynomial.lean`) was checked first: it *is*
the same shape (`∑_k C (ξ k) * ∏_{j≠k} (C (λ j) − X)`), but it lives over `ℝ`, is indexed by an
abstract `Fintype`, and orients its factors as `(λ_j − s)`. Reusing it would have forced a
`Fintype`-subtype carrier plus an `ℝ → ℂ` transport for every subsequent step, and the target
object `F` is `ℂ → ℂ`. It was therefore not reused; this is recorded as a deliberate choice, not an
oversight.

### Step 2 — `P59_NUMERATOR_ROOT_IMP_TRANSFORM_ROOT` — KERNEL GREEN

* `proposition59RawTransform_at_lattice` — the exact removable sampling value
  `F(x_j) = √L · (−1)^j · v_j`, built on `proposition59PoleKernel_at_lattice_sign`;
* `proposition59_numerator_root_imp_transform_root` — both branches. The included-lattice branch
  goes through `v_j = 0` and the removable value; the off-lattice branch through the Cauchy
  quotient. The sine numerator is never cancelled against the denominator globally.
* `proposition59CauchyNumerator_roots_real` — `ZerosRealOn Set.univ F ⟹ every complex root of `P_N`
  is real.

### Step 3 — `P59_EVEN_REAL_ROOTED_POLYNOMIAL_QUADRATIC_PRODUCT` — KERNEL GREEN

* `rootMultiplicity_neg_of_even` (private) — for `p.comp (−X) = p`, `rootMultiplicity (−a) p =
  rootMultiplicity a p`, proved by transporting `(X − C a)^n ∣ p` through `comp (−X)`
  (`Polynomial.le_rootMultiplicity_iff`). Mathlib has no root/multiplicity-under-composition lemma;
  this is the "local finite-polynomial glue" the judge predicted, and it is genuinely local.
* `roots_map_neg_of_even` (private) — `p.roots.map Neg.neg = p.roots`.
* `positiveRootMultiset` — `(p.roots.filter (0 < ·.re)).map Complex.re`; `positiveRootMultiset_pos`.
* `eval_div_eval_zero_eq_prod_positiveRootMultiset` — `p(z)/p(0) = ∏_{ρ∈R⁺}(1 − z²/ρ²)`, via
  `Polynomial.Splits.eval_eq_prod_roots` (`Splits` over `ℂ` from `IsAlgClosed.splits`).
  No Hadamard factorization, no order predicate, no Laguerre–Pólya.

Applied to `P_N`:

* `proposition59Pole_neg`, `card_Icc_symm`;
* `proposition59CauchyNumerator_eval_neg` — `P_N(−z) = P_N(z)` on the symmetric window with an even
  row, by explicit double reindexing with `Equiv.neg ℤ` and the parity of `|I_N \ {k}| = 2N`;
* `proposition59CauchyNumerator_eval_zero_ne_zero` — `P_N(0) ≠ 0` from `v 0 ≠ 0`;
* `proposition59CauchyNumerator_normalized_product` — the step-3 conclusion for `P_N` under
  `ZerosRealOn` and `v 0 ≠ 0`.

### Step 4 — `P59_NORMALIZED_EULER_TAIL_PRODUCT` — HALF GREEN (4a), tail OPEN (4b)

Kernel-green (4a), and this is the removable-node-safe half:

* `proposition59CauchyDenominator_eq_included_factors` —
  `v_0 · D_N(z) = z · P_N(0) · ∏_{k∈I_N, k≠0}(1 − z/x_k)` (finite algebra, all `z`);
* `proposition59_included_factor_product_identity` — for **every** `z`:

```
F(z) · ∏_{k∈I_N, k≠0} (1 − z/x_k)
  = F(0) · (P_N(z)/P_N(0)) · (proposition59PoleKernel L 0 z / L)
```

  where `proposition59PoleKernel L 0 z / L` is exactly the entire `sin(zL/2)/(zL/2)`.
  The included lattice factors are kept on the **left**, so no denominator is cancelled at a node.
  The three cases are: off-lattice (Cauchy quotient), `z = 0` (removable value `poleKernel L 0 0 = L`),
  and `z = x_j`, `j ≠ 0` (both sides vanish *exactly*: the left by the `k = j` factor, the right by
  `proposition59PoleKernel_at_lattice_sign`). This is the judge's "this extension must be explicit
  in Lean" requirement discharged without any density/continuity hand-wave.
* `proposition59_explicit_product_identity` — the same with `P_N(z)/P_N(0)` replaced by
  `∏_{ρ∈R⁺}(1 − z²/ρ²)`.

Open (4b): the statement

```
F(z)/F(0) = ∏_{ρ∈R⁺}(1 − z²/ρ²) · lim_{M} ∏_{k=N+1}^{M} (1 − z²/x_k²)
```

is **not** proved. See the failure section.

### Steps 5, 6, 7 — NOT REACHED

Not attempted; they consume step 4b. Nothing about them is claimed.

## Failure code

```
P59_EULER_TAIL_LIMIT_API_GAP
```

**What is needed and is not in Mathlib `2df2f015`.** The tail factor
`z ↦ ∏'_{k>N} (1 − z²/x_k²)` must be evaluated *at the removable nodes* `z = x_j`, `|j| ≤ N`. What
Mathlib provides:

* `Complex.tendsto_euler_sin_prod` — pointwise only, and it degenerates at the nodes: with
  `w = Lz/(2π)` a node has `w ∈ ℤ`, the partial product `∏_{k≤M}(1 − w²/k²)` is identically `0` for
  `M ≥ |w|`, so the tail cannot be recovered by dividing the full product by the finite head.
* `Complex.multipliable_sineTerm` (`Mathlib/Analysis/SpecialFunctions/Trigonometric/Cotangent.lean`)
  — gives that the product *converges* at every `x`, including integers, but says nothing about its
  value there.
* `Complex.multipliableUniformlyOn_euler_sin_prod_on_compact`,
  `Complex.HasProdUniformlyOn_sineTerm_prod_on_compact`,
  `Complex.HasProdLocallyUniformlyOn_euler_sin_prod` — the *identified* locally uniform statement is
  restricted to `ℂ_ℤ`, the complement of the integers, i.e. it excludes exactly the removable nodes
  we must reach. The helper that would let one redo the bound for the shifted family,
  `Complex.sineTerm_bound_aux`, is `private`.

**Missing declaration (named).** Either of

* `Complex.HasProdLocallyUniformlyOn_euler_sin_prod` stated on `Set.univ` / any compact rather than
  on `ℂ_ℤ`, or
* a tail form, e.g.
  `Continuous fun z : ℂ => ∏' n : ℕ, (1 - z ^ 2 / ((n + N + 1 : ℕ) : ℂ) ^ 2)`
  (a `MultipliableUniformlyOn`/`HasProdUniformlyOn` statement for the shifted family
  `fun n z => 1 + Complex.sineTerm z (n + N)` on every compact of `ℂ`),

neither of which exists. Closing 4b from the existing API means re-deriving the compact-set bound
(the `private` lemma), assembling `MultipliableUniformlyOn` for the shifted family, converting it to
continuity of the `tprod`, and only then running the density argument of §2.4. That is a
self-contained but multi-hour Mathlib-side piece and was outside this task's budget.

**Not a blocker anywhere else.** `Polynomial.Splits.eq_prod_roots_of_monic` /
`Polynomial.Splits.eval_eq_prod_roots_of_monic` were available and used (in the `Splits.eval_eq_prod_roots`
non-monic form, which is strictly more convenient over `ℂ`). `Real.prod_one_add_le_exp_sum` and
`hasSum_zeta_two` were not reached. No `P59_EVEN_ROOT_MULTISET_PAIRING_API_GAP` — the pairing was
closed locally, as the judge predicted.

## Note for the judge — a finite route to steps 5 and 6

The infinite product is *not* logically necessary for the curvature identity itself. Writing
`E(z) = ∏_{k∈I_N,k≠0}(z − x_k)` and `g(z) = ∑_{k≠0} v_k/(z − x_k)` one has `P_N = v_0 E + z E g`
with `g(0) = 0` by evenness and `g'(0) = −∑_{k≠0} v_k/x_k²`, hence

```
P_N,2 / P_N(0) = E_2/E_0 + g'(0)/v_0 = −∑_{k=1}^N x_k^{-2} − (1/v_0) ∑_{k≠0} v_k/x_k² ,
```

and with `∑_{k>N} x_k^{-2} = L²/24 − ∑_{k≤N} x_k^{-2}` (from `hasSum_zeta_two`) this reproduces the
verdict's boxed identity

```
(L²/2)[1/12 + (1/(2π² v_0)) ∑_{k≠0} v_k/k²] = ∑_{ρ∈R⁺} ρ^{-2} + (L²/4π²) ∑_{k>N} k^{-2}
```

against the *existing* exact `proposition59RawTransform_secondDerivative_zero`, with no Euler tail
limit at all. Only bullet 3 of §2.1 (the global envelope `‖F z‖ ≤ ‖F 0‖ exp(κ‖z‖²)`) genuinely
needs the tail, because near a node `z ≈ x_k` the included factors on the left of 4a are small and
cannot be divided out. If the judge wants κ before the Mathlib gap is closed, this is the cheaper
order: 5–6 first by the finite route, 4b/7 afterwards.

## Mandatory plants

| plant | form | result |
|---|---|---|
| A | two compiling `example`s | PASS |
| B | one compiling `example` | PASS |
| C | hypothesis-consumption + arithmetic counterexample (below) | PASS |
| D | compiling lemma `proposition59RawTransform_at_zero_ne_zero_iff` | PASS |

**A** (`N = 1`, `v_0 = 1`, `v_{±1} = 0`). Two `example`s:
`(proposition59CauchyNumerator L {-1,0,1} (fun k => if k = 0 then 1 else 0)).eval z
 = (z − x_{−1})(z − x_1)` and
`proposition59RawTransform L {-1,0,1} … (proposition59Pole L 1) = 0` derived *through*
`proposition59_numerator_root_imp_transform_root`. The two included factors are therefore produced
by `P_N` itself, and the transform root at `±x_1` is obtained from the numerator, not from the sine.

**B** (`N = 1`, `v_{−1} = v_0 = v_1 = 1`). `example`: for every `j ∈ {−1,0,1}`,
`proposition59RawTransform L {-1,0,1} (fun _ => 1) (proposition59Pole L j) ≠ 0` — the included
lattice values are nonzero, so they do not survive as sine zeros. Compiles.

**C** (non-even row). The paired-quadratic theorems are unavailable by construction: evenness is an
explicit hypothesis with no default instance —
`eval_div_eval_zero_eq_prod_positiveRootMultiset` requires `heven : ∀ z, p.eval (−z) = p.eval z`, and
`proposition59CauchyNumerator_normalized_product` requires `hv : ∀ k, v (−k) = v k`. There is no
term of either type for a non-even row, so the theorem cannot be applied. It is also *false* there,
not merely unproved: for `N = 1`, `v_{−1} = 1`, `v_0 = 1`, `v_1 = 0` one gets
`P_1(z) = 2z² − x_1 z − x_1²` with real roots `x_1` and `−x_1/2`, `P_1(0) = −x_1²`, so
`P_1(z)/P_1(0) = 1 + z/x_1 − 2z²/x_1²`, which carries an odd term and cannot equal any product of
`(1 − z²/ρ²)`.

**D** (`F(0) = 0`). `proposition59RawTransform_at_zero_ne_zero_iff` proves
`F 0 ≠ 0 ↔ v 0 ≠ 0`, so the hypothesis `hv0 : v 0 ≠ 0` carried by
`proposition59CauchyNumerator_eval_zero_ne_zero`,
`proposition59_included_factor_product_identity` and `proposition59_explicit_product_identity`
*is* the judge's `F 0 ≠ 0`. Without it `P_N(0) = 0`, the normalization `P_N(z)/P_N(0)` is division
by zero, and `eval_div_eval_zero_eq_prod_positiveRootMultiset` (which requires `p.eval 0 ≠ 0`) has
no applicable instance. The theorems are unavailable.

## κ is real

No complex number is ordered anywhere in this file. `positiveRootMultiset : ℂ[X] → Multiset ℝ`
returns **real** roots (`Complex.re` of roots already proved to be real), and
`positiveRootMultiset_pos` is an inequality between reals. The curvature scalar itself is not yet
defined, because its defining identity is step 5/6 and was not reached.

## Validation

```
q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean   OK (no errors, no warnings)
                   lake build Q3.Proofs.RouteB.Proposition59ExplicitProductCurvatureBridge           OK (7774 jobs)
repo root:         scripts/q3_check.sh Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.lean   "q3_check ok"
```

`#print axioms` for every public theorem in the file
(`proposition59_finite_cauchy_numerator_identity`, `proposition59CauchyNumerator_eval_at_lattice`,
`proposition59CauchyNumerator_eval_at_lattice_eq_zero_iff`, `proposition59RawTransform_at_lattice`,
`proposition59_numerator_root_imp_transform_root`, `proposition59CauchyNumerator_roots_real`,
`positiveRootMultiset_pos`, `eval_div_eval_zero_eq_prod_positiveRootMultiset`,
`proposition59CauchyNumerator_eval_neg`, `proposition59CauchyNumerator_eval_zero_ne_zero`,
`proposition59CauchyNumerator_normalized_product`,
`proposition59CauchyDenominator_eq_included_factors`,
`proposition59_included_factor_product_identity`, `proposition59_explicit_product_identity`,
`proposition59RawTransform_at_zero_ne_zero_iff`):

```
[propext, Classical.choice, Quot.sound]
```

No `sorry`, no `admit`, no `exact?`, no new axiom, no `phase5_scripts`, no precommit, no queue edit,
no route promotion, no RH claim.

## Anything strange

1. **`sourceLagrangePolynomial` overlap.** It is the same algebraic object as `P_N` up to the sign
   convention `(λ_j − s)` vs `(z − x_j)` (harmless here: the erased carrier has even cardinality
   `2N`), but over `ℝ` and over an abstract `Fintype`. Reusing it would have cost more than it
   saved. Flagged so the duplication is a recorded decision, not drift.
2. **Build artefacts.** The worktree's `.lake` is a symlink into the owner's main checkout, so
   `lake build` added exactly one new olean
   (`Q3/Proofs/RouteB/Proposition59ExplicitProductCurvatureBridge.olean`) to the shared build
   directory. Nothing existing was rebuilt or overwritten: the worktree is at `ed343593` and the
   only Lean source difference against the main checkout is one *extra* file there
   (`Goal058CurvatureBorderedSecular.lean`), which this module does not import.
3. **`ZerosRealOn` is used exactly once**, to turn "root of `P_N`" into "real root of `P_N`", via
   step 2. It is not used again, and in particular no step assumes anything about roots of `F` that
   is not routed through `P_N`.
4. **Nothing cofinal is claimed.** Everything above is finite-cell for one fixed `N`; the source
   wall `sup_j κ_{F_j} < ∞` is untouched.
