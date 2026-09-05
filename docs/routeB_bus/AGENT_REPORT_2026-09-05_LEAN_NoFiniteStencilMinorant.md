# NoFiniteStencilMinorant.lean — report

File written (only file created or touched):
`/mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle/Q3/Proofs/RouteB/NoFiniteStencilMinorant.lean`
621 lines, namespace `Q3.RouteB.NoFiniteStencilMinorant`.
`git status --porcelain` shows exactly one entry: `?? q3.lean.aristotle/Q3/Proofs/RouteB/NoFiniteStencilMinorant.lean`. Nothing committed.

## Compile

```
cd /mnt/hdd01/Soft/GitHub/chen_q3_rh_clean/q3.lean.aristotle && \
  lake env lean Q3/Proofs/RouteB/NoFiniteStencilMinorant.lean
```
Exit code **0**, no errors, no warnings. Only output is the `#print axioms` block below.
No project checker was found: `../orchestrator/q3_check.py` does not exist (searched the
whole `orchestrator/` tree), so that step was skipped.

No `sorry`, no `admit`, no `axiom`, no `native_decide` in the file (the string "sorry"
occurs once, inside a docstring sentence).

## What is proved

Everything is proved. Nothing was left out as a `sorry`; the one item deliberately not
attempted is the analytic budget lemma (paper Lemma 5.1), which enters only as
hypothesis `H1` — documented as future work in the module docstring.

### Stage 1 — independence of translates (fully proved)

```lean
theorem independence_of_translates
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f)
    (hf_mass : (∫ x : ℝ, f x) ≠ 0)
    {k : ℕ} {p : Fin k → ℝ} (hp : Function.Injective p) {d : Fin k → ℂ}
    (h : ∀ q : ℚ, ∑ l, d l * (f (p l - (q : ℝ)) : ℂ) = 0) :
    d = 0
```
plus the pointwise restatement
```lean
theorem independence_of_translates_apply (… same hypotheses …) : ∀ l, d l = 0
```

Proof route (route (a) of the spec, with one deviation, see below):

1. `t ↦ ∑ l, d l * f (p l - t)` is continuous and vanishes on `ℚ`, hence everywhere
   (`Rat.denseRange_cast`, `Continuous.ext_on`).
2. Integrating against `e^{i ξ t}` and translating each summand
   (`MeasureTheory.integral_sub_left_eq_self`) gives, for every real `ξ`,
   `(∑ l, d l · e^{i ξ p l}) · fourierPhase f ξ = 0`, where
   `fourierPhase f ξ = ∫ u, f u · e^{-i ξ u}` is defined in the file (Mathlib's
   `Real.fourierIntegral` API is **not** used — the transform is spelled out, which
   avoids the `Circle`-smul plumbing).
   Integrability of each summand: `Integrable.ofReal`, `Integrable.comp_sub_left`,
   `Integrable.bdd_mul` with bound `1`.
3. `fourierPhase f` is continuous (`MeasureTheory.continuous_of_dominated`, bound `|f|`)
   and `fourierPhase f 0 = ↑(∫ f) ≠ 0`, so it is nonzero on `|ξ| < ε`; there the
   exponential sum `E ξ = ∑ l, d l e^{i ξ p l}` vanishes.
4. **Deviation from the spec's plan**: instead of differentiating `E` at `0` and using
   the moment Vandermonde `∑ d_l p_l^j = 0`, the file *samples* `E` at the `k` points
   `ξ = n·ξ₀`, `n < k`, with `ξ₀ = min (ε/(k+1)) (1/(2B+1))`, `B = ∑ l |p l|`. Then
   `k·ξ₀ < ε` (all samples lie in the vanishing interval) and `ξ₀|p l − p m| < 1 < 2π`,
   which makes `z l = e^{i ξ₀ p l}` injective via
   `Complex.exp_eq_exp_iff_exists_int`. So `∑ l, d l (z l)^n = 0` for all `n < k` and
   `Matrix.det_vandermonde_ne_zero_iff` + `Matrix.eq_zero_of_mulVec_eq_zero` give `d = 0`.
   Sampling replaces differentiation, so no iterated derivative of an exponential
   polynomial is ever needed. This is strictly easier to formalise and proves the same
   statement.

### Stage 3 item — the Fatou/stencil lemma, stated separately (fully proved)

```lean
def stencil (f : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (q R x : ℝ) : ℂ :=
  ((χ R x * (f (x - q) / f x) : ℝ) : ℂ)

lemma stencil_energy_limit_eq_zero
    (f : ℝ → ℝ) (hf_cont : Continuous f)
    (Q : (ℝ → ℂ) → ℝ) (χ : ℝ → ℝ → ℝ)
    (hχ_meas : ∀ R : ℝ, Measurable (χ R))
    (hχ_one : ∀ R x : ℝ, |x| ≤ R → χ R x = 1)
    {k : ℕ} (τ : Fin k → ℝ) (c : Fin k → ℝ)
    (W : ℝ → ℝ≥0∞) (hW : Measurable W) (q : ℚ)
    (H1 : Tendsto (fun R : ℝ => Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x))
      atTop (𝓝 0))
    (H2 : ∀ R : ℝ, 1 ≤ R →
      (∫⁻ x : ℝ, W x * ‖∑ l, (c l : ℂ) * stencil f χ (q : ℝ) R (x + τ l)‖ₑ ^ 2)
        ≤ ENNReal.ofReal (Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x))) :
    (∫⁻ x : ℝ, W x
        * ‖∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2) = 0
```
For a fixed `x` the integrand is eventually constant in `n : ℕ` (`χ n (x + τ l) = 1`
once `n ≥ |x| + ∑ l |τ l|`), so `liminf` of the discretised family is the cutoff-free
integrand; `MeasureTheory.lintegral_liminf_le` (Fatou) plus
`Filter.liminf_le_liminf` and `Tendsto.liminf_eq` on the `ENNReal.ofReal`-image of the
budget give `0`. Neither `f > 0`, nor integrability of `f`, nor injectivity of `τ`,
nor `c ≠ 0` is used in this lemma.

### Stage 2 — no positive finite-stencil minorant (fully proved)

```lean
theorem no_positive_finite_stencil_minorant
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f) (hf_pos : ∀ x, 0 < f x)
    (Q : (ℝ → ℂ) → ℝ) (χ : ℝ → ℝ → ℝ)
    (hχ_meas : ∀ R, Measurable (χ R))
    (hχ_one : ∀ R x : ℝ, |x| ≤ R → χ R x = 1)
    {k : ℕ} {τ : Fin k → ℝ} (hτ : Function.Injective τ)
    {c : Fin k → ℝ} (hc : c ≠ 0)
    (W : ℝ → ℝ≥0∞) (hW : Measurable W)
    (H1 : ∀ q : ℚ, Tendsto
      (fun R : ℝ => Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x)) atTop (𝓝 0))
    (H2 : ∀ (q : ℚ) (R : ℝ), 1 ≤ R →
      (∫⁻ x : ℝ, W x * ‖∑ l, (c l : ℂ) * stencil f χ (q : ℝ) R (x + τ l)‖ₑ ^ 2)
        ≤ ENNReal.ofReal (Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x))) :
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), W x = 0
```
`k = 0` is discharged by `Subsingleton.elim c 0` contradicting `hc`. For `k > 0`:
`stencil_energy_limit_eq_zero` for each `q : ℚ`, then `lintegral_eq_zero_iff` gives
a.e. `W x = 0 ∨ ∑ l c l · f(x+τ l−q)/f(x+τ l) = 0`; `MeasureTheory.ae_all_iff` (ℚ is
countable) intersects over `q`; off the null set, `W x ≠ 0` feeds Stage 1 with
`p l = x + τ l` (injective from `hτ` by `add_left_cancel`) and
`d l = c l / f(x + τ l)`, forcing `c = 0`, contradiction.

### Non-vacuity (added, not requested)

```lean
theorem no_positive_finite_stencil_minorant_hypotheses_satisfiable :
    ∃ f Q χ τ c W, (all ten hypotheses of the Stage 2 theorem)
```
Witness: `f x = exp (−1·x²)` (`integrable_exp_neg_mul_sq one_pos`), `Q ≡ 0`, `χ ≡ 1`,
`τ = ![0]`, `c = ![1]`, `W ≡ 0`. This is a guard against the Stage 2 hypothesis set
being contradictory, which would make the theorem true but worthless.

## Hypotheses relative to the spec

Added (all explicit in the statements, none hidden):

* `hf_cont : Continuous f` in Stage 1 — needed for the ℚ→ℝ density step; the spec
  already listed it.
* `hχ_meas : ∀ R, Measurable (χ R)` — needed for `lintegral_liminf_le`; the spec said
  "measurability/continuity as needed".
* `hW : Measurable W` — the spec offered it.
* `H2` is required only for `R ≥ 1` (as in the spec).

Dropped relative to the spec (i.e. the theorems are **stronger** than asked):

* `0 ≤ χ R x ≤ 1` is **not** assumed anywhere. Only `χ R x = 1` on `|x| ≤ R` is used.
* No Hermitian / positivity / sesquilinear structure on `Q`: it is an arbitrary
  `(ℝ → ℂ) → ℝ`.
* Stage 1 uses `∫ f ≠ 0` (the weaker of the two spec variants), not `0 < ∫ f`. In
  Stage 2 `∫ f ≠ 0` is derived from `f > 0` + integrability via
  `integral_pos_iff_support_of_nonneg` (helper `integral_ne_zero_of_pos`).

## Axioms printed (exact output of the final compile)

```
'Q3.RouteB.NoFiniteStencilMinorant.independence_of_translates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.NoFiniteStencilMinorant.independence_of_translates_apply' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.NoFiniteStencilMinorant.stencil_energy_limit_eq_zero' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.NoFiniteStencilMinorant.no_positive_finite_stencil_minorant' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'Q3.RouteB.NoFiniteStencilMinorant.no_positive_finite_stencil_minorant_hypotheses_satisfiable' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
```
The three names are Lean's standard axioms; there is no project axiom and no
`sorryAx` anywhere.

## Left out

* The analytic budget lemma (paper Lemma 5.1) — assumed as `H1`, explicitly named as
  future work in the module docstring, not approached.
* Nothing about the Weil form, zeta, or which concrete `Q` satisfies `H1`/`H2`.
* The spec's alternative Stage 1 proof by differentiation at `0` (replaced by sampling,
  see above).

## Auxiliary declarations in the file

`cexpI`, `cexpI_zero`, `cexpI_add`, `norm_cexpI`, `continuous_cexpI`, `cexpI_natMul`,
`fourierPhase`, `fourierPhase_zero`, `continuous_fourierPhase`,
`integral_translate_phase`, `stencil`, `measurable_stencil_shift`,
`measurable_ratio_shift`, `integral_ne_zero_of_pos`.
