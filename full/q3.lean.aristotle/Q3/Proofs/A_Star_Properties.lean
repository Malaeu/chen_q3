/-
A_Star_Properties.lean
======================

Proofs of a_star classical axioms (Tier-1) using Mathlib Gamma function properties.

Axioms closed in this file:
- a_star_even (T1.3d): a*(-ξ) = a*(ξ)
- a_star_continuous (T1.3b): a* is continuous

Axioms partially addressed:
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
import Q3.DigammaSeries  -- For Gamma_continuousAt_of_re_pos, Gamma_differentiableOn_right_half_plane

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

/-! ## Continuity of digamma and a_star -/

/-- deriv Gamma is continuous on right half-plane -/
lemma deriv_Gamma_continuousOn_right_half_plane :
    ContinuousOn (deriv Complex.Gamma) {z | 0 < z.re} := by
  have hS_open : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.continuousOn
    (DifferentiableOn.deriv Gamma_differentiableOn_right_half_plane hS_open)

/-- Gamma is continuous on right half-plane -/
lemma Gamma_continuousOn_right_half_plane :
    ContinuousOn Complex.Gamma {z | 0 < z.re} := by
  intro z hz
  exact (Gamma_continuousAt_of_re_pos hz).continuousWithinAt

/-- digamma = deriv Gamma / Gamma is continuous on right half-plane -/
lemma digamma_continuousOn_right_half_plane :
    ContinuousOn Q3.digamma {z | 0 < z.re} := by
  unfold Q3.digamma
  apply ContinuousOn.div
  · exact deriv_Gamma_continuousOn_right_half_plane
  · exact Gamma_continuousOn_right_half_plane
  · intro z hz
    exact Complex.Gamma_ne_zero_of_re_pos hz

/-- digamma is continuous at z when Re(z) > 0 -/
lemma digamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Q3.digamma z := by
  have hS_open : IsOpen {z : ℂ | 0 < z.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact digamma_continuousOn_right_half_plane.continuousAt (hS_open.mem_nhds hz)

/-- The argument map matching the definition in Defs.lean: ξ ↦ 1/4 + iπξ -/
def arg_map' (ξ : ℝ) : ℂ := (1/4 : ℂ) + Complex.I * Real.pi * ξ

lemma arg_map'_continuous : Continuous arg_map' := by
  unfold arg_map'
  fun_prop

lemma arg_map'_re_pos (ξ : ℝ) : 0 < (arg_map' ξ).re := by
  simp only [arg_map', add_re, one_div, mul_re, I_re, ofReal_im, mul_zero,
             I_im, ofReal_re, sub_zero]
  norm_num

/-- digamma ∘ arg_map' is continuous -/
lemma digamma_arg'_continuous : Continuous (fun ξ => Q3.digamma (arg_map' ξ)) := by
  rw [continuous_iff_continuousAt]
  intro ξ
  have h1 : ContinuousAt Q3.digamma (arg_map' ξ) := digamma_continuousAt_of_re_pos (arg_map'_re_pos ξ)
  have h2 : ContinuousAt arg_map' ξ := arg_map'_continuous.continuousAt
  exact h1.comp h2

/-- Re ∘ digamma ∘ arg_map' is continuous -/
lemma re_digamma_arg'_continuous : Continuous (fun ξ => (Q3.digamma (arg_map' ξ)).re) := by
  exact continuous_re.comp digamma_arg'_continuous

/-- a is continuous -/
lemma a_continuous : Continuous Q3.a := by
  have h : Q3.a = (fun ξ => Real.log Real.pi - (Q3.digamma (arg_map' ξ)).re) := by
    funext ξ
    rfl
  rw [h]
  apply Continuous.sub
  · exact continuous_const
  · exact re_digamma_arg'_continuous

/-- **Theorem (T1.3b):** a_star is continuous

    **Proof:**
    - digamma is continuous on {Re > 0} (quotient of continuous functions, denominator ≠ 0)
    - The map ξ ↦ 1/4 + iπξ is continuous and maps into {Re > 0}
    - Therefore digamma ∘ arg_map is continuous
    - Taking Re and multiplying by constants preserves continuity

    **Citation:** Titchmarsh (1986) Ch. IX, DLMF 5.2
-/
theorem a_star_continuous_thm : Continuous Q3.a_star := by
  have h : Q3.a_star = (fun ξ => 2 * Real.pi * Q3.a ξ) := by
    funext ξ
    rfl
  rw [h]
  apply Continuous.mul
  · exact continuous_const
  · exact a_continuous

/-! ## Boundedness on compact sets -/

/-- **Theorem (T1.3c):** a_star is bounded on any compact interval.

    **Proof:**
    By extreme value theorem: continuous real-valued function on compact set
    attains its supremum. Since [-K, K] is compact, a_star attains a maximum M.
    Then a_star ξ ≤ M for all ξ ∈ [-K, K].

    **Citation:** Rudin (1976) Theorem 4.16
-/
theorem a_star_bdd_on_compact_thm : ∀ (K : ℝ) (hK : K > 0),
    ∃ M > 0, ∀ ξ ∈ Set.Icc (-K) K, a_star ξ ≤ M := by
  intro K hK
  -- The interval [-K, K] is compact
  have hCompact : IsCompact (Set.Icc (-K) K) := isCompact_Icc
  -- a_star restricted to [-K, K] is continuous
  have hCont : ContinuousOn a_star (Set.Icc (-K) K) :=
    a_star_continuous_thm.continuousOn
  -- Non-empty interval
  have hNe : (Set.Icc (-K) K).Nonempty := by
    use 0
    constructor <;> linarith
  -- By extreme value theorem, a_star attains its supremum on [-K, K]
  obtain ⟨ξ_max, hξ_max_mem, hξ_max_sup⟩ := hCompact.exists_isMaxOn hNe hCont
  -- The supremum value
  let M_raw := a_star ξ_max
  -- We need M > 0. Use max with 1 to ensure positivity.
  use max M_raw 1
  constructor
  · -- max M_raw 1 > 0
    apply lt_max_of_lt_right
    linarith
  · -- For all ξ in the interval, a_star ξ ≤ max M_raw 1
    intro ξ hξ
    have h1 : a_star ξ ≤ M_raw := hξ_max_sup hξ
    exact le_trans h1 (le_max_left _ _)

end Q3

end
