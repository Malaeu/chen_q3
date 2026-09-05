import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.Topology.Algebra.Order.Archimedean

set_option linter.mathlibStandardSet false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

/-!
# No positive finite-stencil minorant

Source boundary (read this before citing anything from this file).

This file is **abstract**.  There is no zeta function, no Weil form, no
arithmetic anywhere in it.  The only objects are: a strictly positive
continuous integrable weight `f : ℝ → ℝ`, an arbitrary "form value"
`Q : (ℝ → ℂ) → ℝ` (no Hermitian structure, no positivity, nothing), an
arbitrary cutoff family `χ`, a finite stencil `(τ, c)` and a measurable
weight `W`.

Everything is proved from hypotheses, with no placeholder proofs, no unfinished steps and no new
`axiom`; every result depends only on `propext`, `Classical.choice`, `Quot.sound`
(see the `#print axioms` block at the end of the file).

Contents:

* `independence_of_translates` (+ `independence_of_translates_apply`) — Stage 1.
* `stencil_energy_limit_eq_zero` — the Fatou/stencil step, stated separately.
* `no_positive_finite_stencil_minorant` — Stage 2.
* `no_positive_finite_stencil_minorant_hypotheses_satisfiable` — a witness showing
  the Stage 2 hypothesis set is consistent, so the theorem is not vacuous.

## Stage 1 — independence of translates

`independence_of_translates` : if `f : ℝ → ℝ` is continuous, integrable and
has nonzero total mass `∫ f ≠ 0`, if `p : Fin k → ℝ` is injective and
`d : Fin k → ℂ` satisfies `∑ l, d l * f (p l - q) = 0` for every **rational**
`q`, then `d = 0`.

The proof runs through the Fourier integral but never uses Mathlib's
`Real.fourierIntegral` API; the transform is spelled out directly as
`fourierPhase f ξ = ∫ u, f u * exp (-(ξ u) i)`, which keeps the whole
argument inside elementary integral calculus:

1. `F q = ∑ l d l f (p l - q)` is continuous and vanishes on `ℚ`, hence
   vanishes on `ℝ` (`Rat.denseRange_cast`, `Continuous.ext_on`).
2. Integrating `F(t) e^{i ξ t}` and translating each summand
   (`integral_sub_left_eq_self`) gives, for every real `ξ`,
   `(∑ l, d l e^{i ξ p l}) * fourierPhase f ξ = 0`.
3. `fourierPhase f` is continuous (`continuous_of_dominated`, bound `|f|`)
   and `fourierPhase f 0 = ∫ f ≠ 0`, so it is nonzero on `|ξ| < ε`, and
   there the exponential sum `E ξ = ∑ l, d l e^{i ξ p l}` vanishes.
4. Instead of differentiating `E` at `0`, we sample it at the `k` points
   `ξ = n ξ₀`, `n < k`, with `ξ₀ > 0` chosen so small that (i) `k ξ₀ < ε`
   and (ii) `ξ₀ |p l - p m| < 2π` for all `l, m`, which makes
   `z l = e^{i ξ₀ p l}` injective (`Complex.exp_eq_exp_iff_exists_int`).
   Then `∑ l, d l (z l)^n = 0` for `n < k` and the Vandermonde determinant
   (`Matrix.det_vandermonde_ne_zero_iff`,
   `Matrix.eq_zero_of_mulVec_eq_zero`) forces `d = 0`.

Sampling replaces differentiation: no iterated derivative of an exponential
polynomial is ever needed.

## Stage 2 — no positive finite-stencil minorant

`no_positive_finite_stencil_minorant` : with `f` in addition strictly
positive, with the ratio profile

`stencil f χ q R x = χ R x * (f (x - q) / f x)`  (as a complex number),

if

* (H1, "budget") for each rational `q` the form values
  `Q (fun x => f x * stencil f χ q R x)` tend to `0` as `R → ∞`, and
* (H2, "minorant") there are a finite injective stencil `τ : Fin k → ℝ`, a
  nonzero coefficient vector `c : Fin k → ℝ` and a measurable weight
  `W : ℝ → ℝ≥0∞` with
  `∫⁻ x, W x * ‖∑ l, c l * stencil f χ q R (x + τ l)‖ₑ ^ 2 ≤ ENNReal.ofReal (Q …)`
  for every rational `q` and every `R ≥ 1`,

then `W = 0` almost everywhere.

The analytic core is isolated as `stencil_energy_limit_eq_zero`, which for a single
rational `q` turns H1 + H2 into the vanishing of the cutoff-free weighted energy.

The proof is Fatou (`MeasureTheory.lintegral_liminf_le`) along `R = n : ℕ`:
for fixed `x` the integrand is *eventually constant* in `n`, because
`χ n (x + τ l) = 1` as soon as `n ≥ |x| + ∑ l |τ l|`.  So the limit
integrand has vanishing integral, hence vanishes a.e.; intersecting over the
countably many rational `q` (`MeasureTheory.ae_all_iff`) and invoking Stage 1
at every point where `W x ≠ 0` contradicts `c ≠ 0`.

## Hypotheses deliberately **not** assumed

* No `0 ≤ χ R x ≤ 1`.  Only `χ R x = 1` on `|x| ≤ R` is used, plus
  measurability of `χ R`.  Boundedness of the cutoff is irrelevant to the
  obstruction.
* No Hermitian/positivity/sesquilinearity structure on `Q`.  It is an
  arbitrary function `(ℝ → ℂ) → ℝ`; only H1 and H2 are used.
* The minorant hypothesis H2 is assumed **only** on the one-parameter family
  `s q R`, not on all compact smooth test profiles.  This makes the theorem
  stronger, since the conclusion is drawn from less.

## Not attempted here (future work)

The analytic budget statement itself — the paper's Lemma 5.1, i.e. a proof
that `Q (f · s q R) → 0` for an actual Weil-type form `Q` — is **not** in
this file and is not approached.  It enters only as the hypothesis `H1`.
Likewise nothing is claimed about which forms `Q` do or do not satisfy H2.
-/

noncomputable section

namespace Q3.RouteB.NoFiniteStencilMinorant

open MeasureTheory Filter Complex Topology
open scoped ENNReal NNReal

/-! ### The unimodular phase `r ↦ e^{i r}` -/

/-- `cexpI r = exp (i r)`. -/
def cexpI (r : ℝ) : ℂ := Complex.exp ((r : ℂ) * Complex.I)

@[simp] lemma cexpI_zero : cexpI 0 = 1 := by simp [cexpI]

lemma cexpI_add (a b : ℝ) : cexpI (a + b) = cexpI a * cexpI b := by
  simp [cexpI, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma norm_cexpI (r : ℝ) : ‖cexpI r‖ = 1 := Complex.norm_exp_ofReal_mul_I r

lemma continuous_cexpI : Continuous cexpI := by
  unfold cexpI
  exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

lemma cexpI_natMul (n : ℕ) (r : ℝ) : cexpI ((n : ℝ) * r) = cexpI r ^ n := by
  unfold cexpI
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-! ### The Fourier phase integral -/

/-- The (unnormalised, `2π`-free) Fourier integral of a real function,
`fourierPhase f ξ = ∫ u, f u * e^{-i ξ u}`. -/
def fourierPhase (f : ℝ → ℝ) (ξ : ℝ) : ℂ := ∫ u : ℝ, (f u : ℂ) * cexpI (-(ξ * u))

lemma fourierPhase_zero (f : ℝ → ℝ) : fourierPhase f 0 = ((∫ u : ℝ, f u : ℝ) : ℂ) := by
  simp only [fourierPhase, zero_mul, neg_zero, cexpI_zero, mul_one]
  exact _root_.integral_ofReal

lemma continuous_fourierPhase (f : ℝ → ℝ) (hf : Integrable f) :
    Continuous (fourierPhase f) := by
  have hmulmeas : ∀ ξ : ℝ,
      AEStronglyMeasurable (fun u : ℝ => (f u : ℂ) * cexpI (-(ξ * u))) volume := by
    intro ξ
    refine AEStronglyMeasurable.mul ?_ ?_
    · exact Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1
    · exact (continuous_cexpI.comp
        (continuous_const.mul continuous_id).neg).aestronglyMeasurable
  refine continuous_of_dominated (bound := fun u => |f u|) hmulmeas ?_ hf.abs ?_
  · intro ξ
    filter_upwards with u
    rw [norm_mul, norm_cexpI, mul_one, Complex.norm_real, Real.norm_eq_abs]
  · filter_upwards with u
    exact continuous_const.mul
      (continuous_cexpI.comp ((continuous_id.mul continuous_const).neg))

/-- Translation rule: `∫ f (a - t) e^{i ξ t} dt = e^{i ξ a} · fourierPhase f ξ`. -/
lemma integral_translate_phase (f : ℝ → ℝ) (a ξ : ℝ) :
    (∫ t : ℝ, (f (a - t) : ℂ) * cexpI (ξ * t)) = cexpI (ξ * a) * fourierPhase f ξ := by
  have h1 : (∫ t : ℝ, (f (a - t) : ℂ) * cexpI (ξ * t))
      = ∫ t : ℝ, (fun u : ℝ => (f u : ℂ) * cexpI (ξ * (a - u))) (a - t) := by
    simp only [sub_sub_cancel]
  rw [h1, integral_sub_left_eq_self (fun u : ℝ => (f u : ℂ) * cexpI (ξ * (a - u))) volume a]
  have h2 : ∀ u : ℝ, (f u : ℂ) * cexpI (ξ * (a - u))
      = cexpI (ξ * a) * ((f u : ℂ) * cexpI (-(ξ * u))) := by
    intro u
    have he : ξ * (a - u) = ξ * a + -(ξ * u) := by ring
    rw [he, cexpI_add]
    ring
  simp only [h2]
  rw [integral_const_mul]
  rfl

/-! ### Stage 1: independence of translates -/

/-- **Independence of translates.**  Let `f : ℝ → ℝ` be continuous, integrable and of
nonzero total mass.  Let `p : Fin k → ℝ` be injective and `d : Fin k → ℂ`.  If the
finite combination of translates `∑ l, d l * f (p l - q)` vanishes for every
**rational** `q`, then `d = 0`.

Rational `q` suffices: the combination is continuous, so it vanishes everywhere. -/
theorem independence_of_translates
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f)
    (hf_mass : (∫ x : ℝ, f x) ≠ 0)
    {k : ℕ} {p : Fin k → ℝ} (hp : Function.Injective p) {d : Fin k → ℂ}
    (h : ∀ q : ℚ, ∑ l, d l * (f (p l - (q : ℝ)) : ℂ) = 0) :
    d = 0 := by
  -- Step A : the combination vanishes at every real point.
  have hFcont : Continuous (fun t : ℝ => ∑ l, d l * (f (p l - t) : ℂ)) := by
    refine continuous_finset_sum _ fun l _ => ?_
    exact continuous_const.mul
      (Complex.continuous_ofReal.comp (hf_cont.comp (continuous_const.sub continuous_id)))
  have hFzero : ∀ t : ℝ, ∑ l, d l * (f (p l - t) : ℂ) = 0 := by
    have hEq : (fun t : ℝ => ∑ l, d l * (f (p l - t) : ℂ)) = (fun _ : ℝ => (0 : ℂ)) := by
      refine Continuous.ext_on Rat.denseRange_cast hFcont continuous_const ?_
      rintro _ ⟨q, rfl⟩
      exact h q
    intro t
    exact congrFun hEq t
  -- Step B : the exponential sum times the Fourier phase vanishes, for every `ξ`.
  have hEΦ : ∀ ξ : ℝ, (∑ l, d l * cexpI (ξ * p l)) * fourierPhase f ξ = 0 := by
    intro ξ
    have hbase : ∀ l : Fin k,
        Integrable (fun t : ℝ => (f (p l - t) : ℂ) * cexpI (ξ * t)) := by
      intro l
      have h1 : Integrable (fun t : ℝ => (f (p l - t) : ℂ)) :=
        (hf_int.ofReal (𝕜 := ℂ)).comp_sub_left (p l)
      have h2 : Integrable (fun t : ℝ => cexpI (ξ * t) * (f (p l - t) : ℂ)) := by
        refine h1.bdd_mul (c := 1) ?_ ?_
        · exact (continuous_cexpI.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
        · filter_upwards with t
          exact le_of_eq (norm_cexpI _)
      have h3 : (fun t : ℝ => (f (p l - t) : ℂ) * cexpI (ξ * t))
          = fun t : ℝ => cexpI (ξ * t) * (f (p l - t) : ℂ) := by
        funext t; ring
      rw [h3]; exact h2
    have hint : ∀ l : Fin k,
        Integrable (fun t : ℝ => d l * ((f (p l - t) : ℂ) * cexpI (ξ * t))) :=
      fun l => (hbase l).const_mul (d l)
    have hzero : (∫ t : ℝ, ∑ l, d l * ((f (p l - t) : ℂ) * cexpI (ξ * t))) = 0 := by
      have : ∀ t : ℝ, ∑ l, d l * ((f (p l - t) : ℂ) * cexpI (ξ * t)) = 0 := by
        intro t
        have hs : ∑ l, d l * ((f (p l - t) : ℂ) * cexpI (ξ * t))
            = (∑ l, d l * (f (p l - t) : ℂ)) * cexpI (ξ * t) := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun l _ => by ring
        rw [hs, hFzero t, zero_mul]
      simp only [this, integral_zero]
    rw [integral_finset_sum _ (fun l _ => hint l)] at hzero
    have hstep : ∀ l : Fin k,
        (∫ t : ℝ, d l * ((f (p l - t) : ℂ) * cexpI (ξ * t)))
          = d l * (cexpI (ξ * p l) * fourierPhase f ξ) := by
      intro l
      rw [integral_const_mul, integral_translate_phase]
    simp only [hstep] at hzero
    rw [Finset.sum_mul]
    rw [← hzero]
    exact Finset.sum_congr rfl fun l _ => by ring
  -- Step C : the Fourier phase does not vanish near `0`.
  have hΦ0 : fourierPhase f 0 ≠ 0 := by
    rw [fourierPhase_zero]
    exact_mod_cast Complex.ofReal_ne_zero.mpr hf_mass
  obtain ⟨ε, hε, hεΦ⟩ : ∃ ε > 0, ∀ ξ : ℝ, |ξ| < ε → fourierPhase f ξ ≠ 0 := by
    have hev := ((continuous_fourierPhase f hf_int).continuousAt
      (x := (0 : ℝ))).eventually_ne hΦ0
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨ε, hε, hmem⟩ := hev
    refine ⟨ε, hε, fun ξ hξ => hmem ?_⟩
    simpa [Real.dist_eq] using hξ
  -- Step D : the exponential sum vanishes on `|ξ| < ε`.
  have hE : ∀ ξ : ℝ, |ξ| < ε → ∑ l, d l * cexpI (ξ * p l) = 0 := by
    intro ξ hξ
    rcases mul_eq_zero.mp (hEΦ ξ) with h' | h'
    · exact h'
    · exact absurd h' (hεΦ ξ hξ)
  -- Step E : choose a sampling step.
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · funext l; exact l.elim0
  set B : ℝ := ∑ l, |p l| with hBdef
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun l _ => abs_nonneg _
  have hpB : ∀ l, |p l| ≤ B :=
    fun l => Finset.single_le_sum (f := fun l => |p l|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ l)
  set ξ₀ : ℝ := min (ε / (k + 1)) (1 / (2 * B + 1)) with hξ₀def
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have h2B : (0 : ℝ) < 2 * B + 1 := by linarith
  have hξ₀pos : 0 < ξ₀ := lt_min (div_pos hε hkpos) (by positivity)
  have hξ₀le1 : ξ₀ ≤ ε / (k + 1) := min_le_left _ _
  have hξ₀le2 : ξ₀ ≤ 1 / (2 * B + 1) := min_le_right _ _
  -- (i) the sampling points stay inside the interval where `E` vanishes.
  have hsample : ∀ n : Fin k, |(n : ℝ) * ξ₀| < ε := by
    intro n
    have hn : (n : ℝ) ≤ (k : ℝ) := by exact_mod_cast n.isLt.le
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
    have habs : |(n : ℝ) * ξ₀| = (n : ℝ) * ξ₀ :=
      abs_of_nonneg (mul_nonneg hnn hξ₀pos.le)
    rw [habs]
    have hle : (n : ℝ) * ξ₀ ≤ (k : ℝ) * (ε / ((k : ℝ) + 1)) :=
      mul_le_mul hn hξ₀le1 hξ₀pos.le (Nat.cast_nonneg _)
    have hlt : (k : ℝ) * (ε / ((k : ℝ) + 1)) < ε := by
      rw [mul_div_assoc', div_lt_iff₀ hkpos]
      nlinarith
    linarith
  -- (ii) the sampled phases are pairwise distinct.
  have hzinj : Function.Injective (fun l : Fin k => cexpI (ξ₀ * p l)) := by
    intro l m hlm
    by_contra hne
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hlm
    have hcast : ((ξ₀ * p l : ℝ) : ℂ) * Complex.I
        = ((ξ₀ * p m + (n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I := by
      rw [hn]
      push_cast
      ring
    have hreal : ξ₀ * p l = ξ₀ * p m + (n : ℝ) * (2 * Real.pi) := by
      exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero hcast
    have hdiff : ξ₀ * (p l - p m) = (n : ℝ) * (2 * Real.pi) := by
      rw [mul_sub]; linarith
    have htri : |p l - p m| ≤ 2 * B := by
      have h1 : |p l - p m| ≤ |p l| + |p m| := by
        simpa [sub_eq_add_neg, abs_neg] using abs_add_le (p l) (-(p m))
      have := hpB l
      have := hpB m
      linarith
    have hlt1 : ξ₀ * (2 * B) < 1 := by
      have h1 : ξ₀ * (2 * B) ≤ (1 / (2 * B + 1)) * (2 * B) :=
        mul_le_mul_of_nonneg_right hξ₀le2 (by linarith)
      have h2 : (1 / (2 * B + 1)) * (2 * B) < 1 := by
        rw [div_mul_eq_mul_div, one_mul, div_lt_one h2B]
        linarith
      linarith
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    have hbound : |ξ₀ * (p l - p m)| < 2 * Real.pi := by
      rw [abs_mul, abs_of_pos hξ₀pos]
      have : ξ₀ * |p l - p m| ≤ ξ₀ * (2 * B) :=
        mul_le_mul_of_nonneg_left htri hξ₀pos.le
      have hp3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      linarith
    have hn0 : n = 0 := by
      by_contra hnz
      have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hnz
        calc (1 : ℝ) ≤ ((|n| : ℤ) : ℝ) := by exact_mod_cast this
          _ = |(n : ℝ)| := by push_cast [Int.cast_abs]; ring_nf
      rw [hdiff, abs_mul, abs_of_pos hpi] at hbound
      nlinarith
    rw [hn0] at hdiff
    simp only [Int.cast_zero, zero_mul] at hdiff
    have : p l = p m := by
      have := mul_eq_zero.mp hdiff
      rcases this with h' | h'
      · exact absurd h' (ne_of_gt hξ₀pos)
      · linarith [sub_eq_zero.mp h']
    exact hne (hp this)
  -- Step F : Vandermonde.
  have hsum : ∀ n : Fin k, ∑ l, d l * (cexpI (ξ₀ * p l)) ^ (n : ℕ) = 0 := by
    intro n
    rw [← hE ((n : ℝ) * ξ₀) (hsample n)]
    refine Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [← cexpI_natMul]
    congr 1
    ring
  have hdet : (Matrix.vandermonde (fun l : Fin k => cexpI (ξ₀ * p l))).transpose.det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hzinj
  have hmv : Matrix.mulVec
      (Matrix.vandermonde (fun l : Fin k => cexpI (ξ₀ * p l))).transpose d = 0 := by
    funext n
    have hexp : Matrix.mulVec
        (Matrix.vandermonde (fun l : Fin k => cexpI (ξ₀ * p l))).transpose d n
        = ∑ l, d l * (cexpI (ξ₀ * p l)) ^ (n : ℕ) := by
      simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.vandermonde_apply, dotProduct]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [hexp, Pi.zero_apply]
    exact hsum n
  exact Matrix.eq_zero_of_mulVec_eq_zero hdet hmv

/-- Pointwise form of `independence_of_translates`. -/
theorem independence_of_translates_apply
    (f : ℝ → ℝ) (hf_cont : Continuous f) (hf_int : Integrable f)
    (hf_mass : (∫ x : ℝ, f x) ≠ 0)
    {k : ℕ} {p : Fin k → ℝ} (hp : Function.Injective p) {d : Fin k → ℂ}
    (h : ∀ q : ℚ, ∑ l, d l * (f (p l - (q : ℝ)) : ℂ) = 0) :
    ∀ l, d l = 0 := fun l =>
  congrFun (independence_of_translates f hf_cont hf_int hf_mass hp h) l


/-! ### Stage 2: no positive finite-stencil minorant -/

/-- The complex-valued stencil profile `s q R x = χ R x · (f (x - q) / f x)`. -/
def stencil (f : ℝ → ℝ) (χ : ℝ → ℝ → ℝ) (q R x : ℝ) : ℂ :=
  ((χ R x * (f (x - q) / f x) : ℝ) : ℂ)

lemma measurable_stencil_shift {f : ℝ → ℝ} (hf : Continuous f) {χ : ℝ → ℝ → ℝ}
    {R : ℝ} (hχ : Measurable (χ R)) (q a : ℝ) :
    Measurable (fun x : ℝ => stencil f χ q R (x + a)) := by
  simp only [stencil]
  have h1 : Measurable (fun x : ℝ => χ R (x + a)) := hχ.comp (measurable_id.add_const a)
  have h2 : Measurable (fun x : ℝ => f (x + a - q)) :=
    hf.measurable.comp ((measurable_id.add_const a).sub_const q)
  have h3 : Measurable (fun x : ℝ => f (x + a)) := hf.measurable.comp (measurable_id.add_const a)
  exact Complex.continuous_ofReal.measurable.comp (h1.mul (h2.div h3))

lemma measurable_ratio_shift {f : ℝ → ℝ} (hf : Continuous f) (q a : ℝ) :
    Measurable (fun x : ℝ => ((f (x + a - q) / f (x + a) : ℝ) : ℂ)) := by
  have h2 : Measurable (fun x : ℝ => f (x + a - q)) :=
    hf.measurable.comp ((measurable_id.add_const a).sub_const q)
  have h3 : Measurable (fun x : ℝ => f (x + a)) := hf.measurable.comp (measurable_id.add_const a)
  exact Complex.continuous_ofReal.measurable.comp (h2.div h3)

/-- A strictly positive integrable function has nonzero total mass. -/
lemma integral_ne_zero_of_pos {f : ℝ → ℝ} (hf_int : Integrable f) (hf_pos : ∀ x, 0 < f x) :
    (∫ x : ℝ, f x) ≠ 0 := by
  have hsupp : Function.support f = Set.univ := by
    ext x
    simp [Function.mem_support, (hf_pos x).ne']
  have hpos : 0 < ∫ x : ℝ, f x := by
    rw [integral_pos_iff_support_of_nonneg (fun x => (hf_pos x).le) hf_int, hsupp]
    simp
  exact hpos.ne'

/-- **Fatou / stencil lemma** (the analytic core of Stage 2, stated separately).

For a *fixed* rational shift `q`, if the form values along the cutoff family tend to
`0` (H1) and dominate the weighted finite-stencil energy for every `R ≥ 1` (H2), then
the *cutoff-free* weighted energy already vanishes:

`∫⁻ x, W x * ‖∑ l, c l * (f (x + τ l - q) / f (x + τ l))‖ₑ ^ 2 = 0`.

The mechanism is that for each fixed `x` the cutoff `χ n (x + τ l)` equals `1` once
`n ≥ |x| + ∑ l |τ l|`, so the integrand is eventually constant in `n`; Fatou
(`MeasureTheory.lintegral_liminf_le`) then transfers the vanishing budget to the
limit.  Neither `f > 0` nor integrability of `f` nor `τ` injective nor `c ≠ 0` is
used here. -/
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
        * ‖∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2) = 0 := by
  set B : ℝ := ∑ l, |τ l| with hBdef
  have hτB : ∀ l, |τ l| ≤ B :=
    fun l => Finset.single_le_sum (f := fun l => |τ l|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ l)
  set g : ℕ → ℝ → ℝ≥0∞ := fun n x =>
    W x * ‖∑ l, (c l : ℂ) * stencil f χ (q : ℝ) (n : ℝ) (x + τ l)‖ₑ ^ 2 with hgdef
  have hgmeas : ∀ n, Measurable (g n) := by
    intro n
    refine hW.mul ((Measurable.enorm ?_).pow_const 2)
    exact Finset.measurable_sum _ fun l _ =>
      measurable_const.mul
        (measurable_stencil_shift hf_cont (hχ_meas (n : ℝ)) (q : ℝ) (τ l))
  have hlim : ∀ x : ℝ, liminf (fun n => g n x) atTop
      = W x * ‖∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2 := by
    intro x
    refine Tendsto.liminf_eq (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
    filter_upwards [eventually_ge_atTop ⌈|x| + B⌉₊] with n hn
    have hnge : |x| + B ≤ (n : ℝ) := le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hst : ∀ l : Fin k, stencil f χ (q : ℝ) (n : ℝ) (x + τ l)
        = ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ) := by
      intro l
      have hle : |x + τ l| ≤ (n : ℝ) := by
        have h1 := abs_add_le x (τ l)
        have h2 := hτB l
        linarith
      simp [stencil, hχ_one (n : ℝ) (x + τ l) hle]
    simp only [hgdef, hst]
  have hfatou : (∫⁻ x : ℝ, W x
        * ‖∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2)
      ≤ liminf (fun n : ℕ => ∫⁻ x : ℝ, g n x) atTop := by
    refine le_trans (le_of_eq ?_) (lintegral_liminf_le hgmeas)
    exact lintegral_congr fun x => (hlim x).symm
  have hQ : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) (n : ℝ) x))) atTop (𝓝 0) := by
    have h1 := H1.comp tendsto_natCast_atTop_atTop
    have h2 := (ENNReal.continuous_ofReal.tendsto (0 : ℝ)).comp h1
    simpa using h2
  have hle : liminf (fun n : ℕ => ∫⁻ x : ℝ, g n x) atTop
      ≤ liminf (fun n : ℕ => ENNReal.ofReal
          (Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) (n : ℝ) x))) atTop := by
    refine liminf_le_liminf ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact H2 (n : ℝ) (by exact_mod_cast hn)
  rw [hQ.liminf_eq] at hle
  exact le_antisymm (le_trans hfatou hle) (zero_le _)

/-- **No positive finite-stencil minorant.**

Abstract data: a strictly positive continuous integrable weight `f`, an arbitrary
"form value" `Q : (ℝ → ℂ) → ℝ`, an arbitrary cutoff family `χ` which is `1` on
`|x| ≤ R` and measurable in `x`, a finite injective stencil `τ : Fin k → ℝ` with a
nonzero real coefficient vector `c`, and a measurable weight `W : ℝ → ℝ≥0∞`.

If the "budget" hypothesis `H1` holds (the form values along the ratio family tend
to `0` as the cutoff opens) and the "minorant" hypothesis `H2` holds (the weighted
finite-stencil energy of the ratio family is dominated by the form value), then the
weight `W` vanishes almost everywhere. -/
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
    ∀ᵐ x : ℝ ∂(volume : Measure ℝ), W x = 0 := by
  by_cases hk : k = 0
  · subst hk
    exact absurd (Subsingleton.elim c 0) hc
  have hf_mass : (∫ x : ℝ, f x) ≠ 0 := integral_ne_zero_of_pos hf_int hf_pos
  -- The limiting (cutoff-free) integrand.
  set G : ℚ → ℝ → ℝ≥0∞ := fun q x =>
    W x * ‖∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2 with hGdef
  have hGmeas : ∀ q : ℚ, Measurable (G q) := by
    intro q
    refine hW.mul ((Measurable.enorm ?_).pow_const 2)
    exact Finset.measurable_sum _ fun l _ =>
      measurable_const.mul (measurable_ratio_shift hf_cont (q : ℝ) (τ l))
  -- Fatou along `R = n : ℕ` kills the limiting integrand.
  have hGzero : ∀ q : ℚ, (∫⁻ x : ℝ, G q x) = 0 := by
    intro q
    simp only [hGdef]
    exact stencil_energy_limit_eq_zero f hf_cont Q χ hχ_meas hχ_one τ c W hW q (H1 q)
      (fun R hR => H2 q R hR)
  -- Pointwise dichotomy for each rational shift.
  have hae : ∀ q : ℚ, ∀ᵐ x : ℝ ∂(volume : Measure ℝ),
      W x = 0 ∨ ∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ) = 0 := by
    intro q
    have h0 := (lintegral_eq_zero_iff (hGmeas q)).mp (hGzero q)
    filter_upwards [h0] with x hx
    have hx0 : W x * ‖∑ l, (c l : ℂ)
        * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ)‖ₑ ^ 2 = 0 := hx
    rcases mul_eq_zero.mp hx0 with h' | h'
    · exact Or.inl h'
    · exact Or.inr (enorm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h'))
  have haeall : ∀ᵐ x : ℝ ∂(volume : Measure ℝ), ∀ q : ℚ,
      W x = 0 ∨ ∑ l, (c l : ℂ) * ((f (x + τ l - (q : ℝ)) / f (x + τ l) : ℝ) : ℂ) = 0 :=
    ae_all_iff.mpr hae
  filter_upwards [haeall] with x hx
  by_contra hWx
  have hzero : ∀ q : ℚ,
      ∑ l, ((c l : ℂ) / (f (x + τ l) : ℂ)) * (f ((x + τ l) - (q : ℝ)) : ℂ) = 0 := by
    intro q
    rcases hx q with h' | h'
    · exact absurd h' hWx
    · rw [← h']
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Complex.ofReal_div]
      ring
  have hpinj : Function.Injective (fun l : Fin k => x + τ l) := by
    intro l m hlm
    exact hτ (add_left_cancel hlm)
  have hd := independence_of_translates (p := fun l : Fin k => x + τ l)
    (d := fun l : Fin k => (c l : ℂ) / (f (x + τ l) : ℂ))
    f hf_cont hf_int hf_mass hpinj hzero
  apply hc
  funext l
  have hdl := congrFun hd l
  simp only [Pi.zero_apply] at hdl ⊢
  have hfne : ((f (x + τ l) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hf_pos _).ne'
  rcases div_eq_zero_iff.mp hdl with h' | h'
  · exact_mod_cast h'
  · exact absurd h' hfne



/-! ### Non-vacuity -/

/-- The hypothesis set of `no_positive_finite_stencil_minorant` is consistent: a
Gaussian weight, the constant cutoff `1`, the zero form, a one-point stencil with
coefficient `1` and the zero weight satisfy every hypothesis simultaneously.  This
rules out the theorem being vacuously true. -/
theorem no_positive_finite_stencil_minorant_hypotheses_satisfiable :
    ∃ (f : ℝ → ℝ) (Q : (ℝ → ℂ) → ℝ) (χ : ℝ → ℝ → ℝ) (τ : Fin 1 → ℝ) (c : Fin 1 → ℝ)
      (W : ℝ → ℝ≥0∞),
      Continuous f ∧ Integrable f ∧ (∀ x, 0 < f x) ∧
      (∀ R : ℝ, Measurable (χ R)) ∧ (∀ R x : ℝ, |x| ≤ R → χ R x = 1) ∧
      Function.Injective τ ∧ c ≠ 0 ∧ Measurable W ∧
      (∀ q : ℚ, Tendsto (fun R : ℝ => Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x))
        atTop (𝓝 0)) ∧
      (∀ (q : ℚ) (R : ℝ), 1 ≤ R →
        (∫⁻ x : ℝ, W x * ‖∑ l, (c l : ℂ) * stencil f χ (q : ℝ) R (x + τ l)‖ₑ ^ 2)
          ≤ ENNReal.ofReal (Q (fun x => (f x : ℂ) * stencil f χ (q : ℝ) R x))) := by
  refine ⟨fun x => Real.exp (-1 * x ^ 2), fun _ => 0, fun _ _ => 1, ![0], ![1],
    fun _ => 0, ?_, integrable_exp_neg_mul_sq one_pos, fun x => Real.exp_pos _,
    fun R => measurable_const, fun R x _ => rfl,
    fun a b _ => Subsingleton.elim a b, ?_, measurable_const,
    fun q => tendsto_const_nhds, ?_⟩
  · exact Real.continuous_exp.comp (by fun_prop)
  · intro h
    have := congrFun h 0
    simp at this
  · intro q R _
    simp

/-! ### Axiom audit -/

#print axioms independence_of_translates
#print axioms independence_of_translates_apply
#print axioms stencil_energy_limit_eq_zero
#print axioms no_positive_finite_stencil_minorant
#print axioms no_positive_finite_stencil_minorant_hypotheses_satisfiable

end Q3.RouteB.NoFiniteStencilMinorant

end
