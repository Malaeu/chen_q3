/-
A_Star_Properties.lean
======================

Proofs of a_star classical axioms (Tier-1) using Mathlib Gamma function properties.

Axioms closed in this file:
- a_star_even (T1.3d): a*(-ξ) = a*(ξ)

Axioms partially addressed:
- a_star_continuous (T1.3b): requires digamma continuity
- a_star_bdd_on_compact (T1.3c): follows from continuity
- a_star_pos (T1.3): requires digamma positivity bounds

Key insight: The argument z = 1/4 + iπξ always has Re(z) = 1/4 > 0,
so it avoids all poles of Gamma (at 0, -1, -2, ...).

References:
- Mathlib: Complex.Gamma_conj, Complex.differentiableAt_Gamma
- DLMF 5.5: ψ(z̄) = ψ(z)̄ (digamma conjugation symmetry)
-/

import Mathlib
import Q3.Basic.Defs

open scoped BigOperators Real Nat Classical Pointwise ComplexConjugate
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3

/-! ## Helper lemmas -/

/-- conj of 1/4 is 1/4 -/
lemma conj_one_fourth : conj (1/4 : ℂ) = 1/4 := by
  simp only [map_div₀, map_one, RCLike.conj_ofNat]

/-! ## The argument z = 1/4 + iπξ -/

/-- The argument used in a_star: z(ξ) = 1/4 + iπξ -/
def a_star_arg (ξ : ℝ) : ℂ := (1/4 : ℂ) + I * π * ξ

/-- Conjugate of a_star_arg(ξ) equals a_star_arg(-ξ) -/
lemma conj_a_star_arg (ξ : ℝ) : conj (a_star_arg ξ) = a_star_arg (-ξ) := by
  simp only [a_star_arg]
  rw [map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  rw [conj_one_fourth]
  simp only [ofReal_neg]
  ring

/-- a_star_arg(ξ) has positive real part (= 1/4) -/
lemma a_star_arg_re_pos (ξ : ℝ) : 0 < (a_star_arg ξ).re := by
  simp only [a_star_arg, add_re, one_div, mul_re, I_re, ofReal_im, mul_zero,
             I_im, ofReal_re, sub_zero]
  norm_num

/-- a_star_arg(ξ) is not a non-positive integer -/
lemma a_star_arg_ne_neg_nat (ξ : ℝ) (m : ℕ) : a_star_arg ξ ≠ -↑m := by
  intro h
  have hre := a_star_arg_re_pos ξ
  rw [h] at hre
  simp only [neg_re, natCast_re] at hre
  linarith

/-- Gamma is differentiable at a_star_arg(ξ) -/
lemma gamma_differentiable_at_a_star_arg (ξ : ℝ) :
    DifferentiableAt ℂ Complex.Gamma (a_star_arg ξ) :=
  Complex.differentiableAt_Gamma _ (a_star_arg_ne_neg_nat ξ)

/-- Gamma is nonzero at a_star_arg(ξ) -/
lemma gamma_ne_zero_at_a_star_arg (ξ : ℝ) :
    Complex.Gamma (a_star_arg ξ) ≠ 0 :=
  Complex.Gamma_ne_zero (a_star_arg_ne_neg_nat ξ)

/-! ## Digamma conjugation symmetry -/

/-- star ∘ Gamma ∘ star = Gamma (since Gamma(z̄) = Gamma(z)̄) -/
lemma Gamma_star_star_eq : star ∘ Complex.Gamma ∘ star = Complex.Gamma := by
  ext w
  simp only [Function.comp_apply, star_def]
  -- Need: conj (Gamma (conj w)) = Gamma w
  rw [Complex.Gamma_conj]
  -- Now: conj (conj (Gamma w)) = Gamma w
  exact Complex.conj_conj _

/-- deriv Gamma has conjugation symmetry: Γ'(z̄) = Γ'(z)̄

    Proof uses HasDerivAt.conj_conj from Mathlib:
    If f has derivative f' at z, then (star ∘ f ∘ star) has derivative (star f') at (star z).
    Since Gamma satisfies Gamma(star w) = star(Gamma w), we have star ∘ Gamma ∘ star = Gamma,
    so deriv Gamma (star z) = star (deriv Gamma z).
-/
lemma deriv_Gamma_conj (z : ℂ) (hz : ∀ m : ℕ, z ≠ -↑m) :
    deriv Complex.Gamma (conj z) = conj (deriv Complex.Gamma z) := by
  have hconj_ne : ∀ m : ℕ, conj z ≠ -↑m := by
    intro m h
    have hconj_re : (conj z).re = z.re := Complex.conj_re z
    have : (conj z).re = (-m : ℂ).re := by rw [h]
    simp at this
    have hz' := hz m
    by_contra
    have hzre : z.re = -(m : ℝ) := by linarith [hconj_re, this]
    have him : z.im = 0 → z = -↑m := by
      intro hz_im
      apply Complex.ext
      · simp [hzre]
      · simp [hz_im]
    have hconj_im : (conj z).im = 0 := by rw [h]; simp
    have hz_im : z.im = 0 := by
      have : (conj z).im = -z.im := Complex.conj_im z
      linarith
    exact hz m (him hz_im)
  have hDiff : DifferentiableAt ℂ Complex.Gamma z := Complex.differentiableAt_Gamma z hz
  -- Use HasDerivAt.conj_conj: HasDerivAt (star ∘ f ∘ star) (star f') (star x)
  have h1 := hDiff.hasDerivAt.conj_conj
  -- h1 : HasDerivAt (star ∘ Gamma ∘ star) (star (deriv Gamma z)) (star z)
  have h2 : deriv (star ∘ Complex.Gamma ∘ star) (star z) =
            star (deriv Complex.Gamma z) := h1.deriv
  rw [Gamma_star_star_eq] at h2
  -- star z = conj z for ℂ
  simp only [star_def] at h2
  exact h2

/-- Digamma has conjugation symmetry: ψ(z̄) = ψ(z)̄

    This follows from Γ(z̄) = Γ(z)̄ and Γ'(z̄) = Γ'(z)̄:
    ψ(z̄) = Γ'(z̄)/Γ(z̄) = Γ'(z)̄/Γ(z)̄ = (Γ'/Γ)(z)̄ = ψ(z)̄
-/
lemma digamma_conj (z : ℂ) (hz : 0 < z.re) :
    Q3.digamma (conj z) = conj (Q3.digamma z) := by
  have hz_ne : ∀ m : ℕ, z ≠ -↑m := by
    intro m h
    have : z.re = (-m : ℂ).re := by rw [h]
    simp at this
    linarith
  have hconj_ne : ∀ m : ℕ, conj z ≠ -↑m := by
    intro m h
    have hconj_re : (conj z).re = z.re := Complex.conj_re z
    have : (conj z).re = (-m : ℂ).re := by rw [h]
    simp at this
    linarith [hconj_re, this]
  unfold Q3.digamma
  have h1 : Complex.Gamma (conj z) = conj (Complex.Gamma z) := Complex.Gamma_conj z
  have h2 : deriv Complex.Gamma (conj z) = conj (deriv Complex.Gamma z) :=
    deriv_Gamma_conj z hz_ne
  have hGamma_ne : Complex.Gamma z ≠ 0 := Complex.Gamma_ne_zero hz_ne
  rw [h1, h2]
  rw [map_div₀]

/-! ## Main theorem: a_star is even -/

/-- **Theorem (T1.3d):** a_star is an even function: a*(-ξ) = a*(ξ)

    **Proof:**
    - The argument z(ξ) = 1/4 + iπξ satisfies z(-ξ) = conj(z(ξ))
    - By digamma_conj: ψ(z(-ξ)) = ψ(conj(z(ξ))) = conj(ψ(z(ξ)))
    - Taking real parts: Re(ψ(z(-ξ))) = Re(conj(ψ(z(ξ)))) = Re(ψ(z(ξ)))
    - Therefore a*(-ξ) = 2π(log π - Re(ψ(z(-ξ)))) = 2π(log π - Re(ψ(z(ξ)))) = a*(ξ)

    **Citation:** DLMF 5.5, Abramowitz & Stegun 6.3
-/
theorem a_star_even_thm : ∀ ξ : ℝ, a_star (-ξ) = a_star ξ := by
  intro ξ
  unfold a_star a
  have h_cast : ((-ξ : ℝ) : ℂ) = -(ξ : ℂ) := ofReal_neg ξ
  have h1 : (1/4 : ℂ) + I * π * ((-ξ : ℝ) : ℂ) = conj ((1/4 : ℂ) + I * π * ξ) := by
    rw [h_cast]
    rw [map_add, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
    rw [conj_one_fourth]
    ring
  have hpos : 0 < ((1/4 : ℂ) + I * π * ξ).re := by
    simp only [add_re, one_div, mul_re, I_re, ofReal_im, mul_zero, I_im, ofReal_re, sub_zero]
    norm_num
  have h2 : Q3.digamma ((1/4 : ℂ) + I * π * ((-ξ : ℝ) : ℂ)) =
            conj (Q3.digamma ((1/4 : ℂ) + I * π * ξ)) := by
    rw [h1]
    exact digamma_conj _ hpos
  have h3 : (conj (Q3.digamma ((1/4 : ℂ) + I * π * ξ))).re =
            (Q3.digamma ((1/4 : ℂ) + I * π * ξ)).re := Complex.conj_re _
  simp only [ofReal_neg] at h2 ⊢
  rw [h2, h3]

end Q3

end
