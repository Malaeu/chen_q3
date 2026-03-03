import Mathlib
import Q3.Basic.Defs
import Q3.DigammaSeries

noncomputable section

namespace Q3.Proofs.PrimeCert

open scoped ComplexOrder

private lemma add_natCast_ne_zero_of_re_pos
    (x y : ℝ) (hx : 0 < x) (n : ℕ) :
    ((x : ℂ) + Complex.I * y + n) ≠ 0 := by
  intro h
  have hre : (((x : ℂ) + Complex.I * y + n).re) = x + n := by
    simp [add_assoc, add_comm, add_left_comm]
  have hzero : x + n = 0 := by
    simpa [hre] using congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := by
    exact_mod_cast Nat.cast_nonneg n
  linarith

private lemma add_natCast_real_ne_zero_of_re_pos
    (x : ℝ) (hx : 0 < x) (n : ℕ) :
    ((x : ℂ) + n) ≠ 0 := by
  intro h
  have hre : (((x : ℂ) + n).re) = x + n := by simp
  have hzero : x + n = 0 := by
    simpa [hre] using congrArg Complex.re h
  have hn : (0 : ℝ) ≤ n := by
    exact_mod_cast Nat.cast_nonneg n
  linarith

private lemma re_inv_add_natCast_real
    (x : ℝ) (hx : 0 < x) (n : ℕ) :
    (((((x : ℂ) + n)⁻¹)).re) = 1 / (x + n) := by
  have hneC : ((x : ℂ) + n) ≠ 0 := add_natCast_real_ne_zero_of_re_pos x hx n
  have hnx_pos : 0 < x + n := by
    have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.cast_nonneg n
    linarith
  have hnx_ne : x + n ≠ 0 := ne_of_gt hnx_pos
  calc
    ((((x : ℂ) + n)⁻¹)).re
        = (((x : ℂ) + n).re) / Complex.normSq ((x : ℂ) + n) := by
            simpa using Complex.inv_re ((x : ℂ) + n)
    _ = (x + n) / ((x + n) ^ 2) := by
          simp [Complex.normSq_apply, pow_two, add_assoc, add_comm, add_left_comm]
    _ = 1 / (x + n) := by
          field_simp [hnx_ne]

private lemma re_inv_add_natCast_imag
    (x y : ℝ) (hx : 0 < x) (n : ℕ) :
    ((((x : ℂ) + Complex.I * y + n)⁻¹).re) =
      (x + n) / ((x + n) ^ 2 + y ^ 2) := by
  have hne : ((x : ℂ) + Complex.I * y + n) ≠ 0 := add_natCast_ne_zero_of_re_pos x y hx n
  calc
    ((((x : ℂ) + Complex.I * y + n)⁻¹).re)
        = (((x : ℂ) + Complex.I * y + n).re) /
            Complex.normSq ((x : ℂ) + Complex.I * y + n) := by
              simpa using Complex.inv_re ((x : ℂ) + Complex.I * y + n)
    _ = (x + n) / ((x + n) ^ 2 + y ^ 2) := by
          simp [Complex.normSq_apply, pow_two, add_assoc, add_comm, add_left_comm]

/-- Exact real-part digamma shift identity used by the prime-heat arch route. -/
lemma re_digamma_add_imag_sq
    (x y : ℝ) (hx : 0 < x) :
    (Q3.digamma ((x : ℂ) + Complex.I * y)).re - (Q3.digamma (x : ℂ)).re =
      y ^ 2 * ∑' n : ℕ, 1 / (((n : ℝ) + x) * (((n : ℝ) + x) ^ 2 + y ^ 2)) := by
  let z1 : ℂ := (x : ℂ) + Complex.I * y
  let z0 : ℂ := (x : ℂ)
  have hz1_re : 0 < z1.re := by simpa [z1] using hx
  have hz0_re : 0 < z0.re := by simpa [z0] using hx
  have hz1 : ∀ n : ℕ, z1 + n ≠ 0 := by
    intro n
    simpa [z1, add_assoc, add_left_comm, add_comm] using add_natCast_ne_zero_of_re_pos x y hx n
  have hz0 : ∀ n : ℕ, z0 + n ≠ 0 := by
    intro n
    simpa [z0, add_assoc, add_left_comm, add_comm] using add_natCast_real_ne_zero_of_re_pos x hx n
  have ht1 :
      Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z1 n) Filter.atTop (nhds (Q3.digamma z1)) := by
    exact Q3.digammaSeq_tendsto_Q3_digamma z1 hz1_re
  have ht0 :
      Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z0 n) Filter.atTop (nhds (Q3.digamma z0)) := by
    exact Q3.digammaSeq_tendsto_Q3_digamma z0 hz0_re
  have hre1 := Q3.re_digamma_eq_sum_of_tendsto z1 hz1 ht1
  have hre0 := Q3.re_digamma_eq_sum_of_tendsto z0 hz0 ht0
  have hsum1 :
      Summable (fun n : ℕ => (1 / (n + 1 : ℂ) - 1 / (z1 + n)).re) := by
    simpa using (Complex.reCLM.summable (Q3.digamma_series_summable z1 hz1))
  have hsum0 :
      Summable (fun n : ℕ => (1 / (n + 1 : ℂ) - 1 / (z0 + n)).re) := by
    simpa using (Complex.reCLM.summable (Q3.digamma_series_summable z0 hz0))
  calc
    (Q3.digamma ((x : ℂ) + Complex.I * y)).re - (Q3.digamma (x : ℂ)).re
        = (∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (z1 + n)).re) -
            (∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (z0 + n)).re) := by
              linarith [hre1, hre0]
    _ = ∑' n : ℕ,
          ((1 / (n + 1 : ℂ) - 1 / (z1 + n)).re -
            (1 / (n + 1 : ℂ) - 1 / (z0 + n)).re) := by
              simpa using (hsum1.tsum_sub hsum0).symm
    _ = ∑' n : ℕ,
          ((((z0 + n)⁻¹).re) - (((z1 + n)⁻¹).re)) := by
            refine tsum_congr ?_
            intro n
            ring_nf
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    _ = ∑' n : ℕ,
          (y ^ 2 / (((n : ℝ) + x) * (((n : ℝ) + x) ^ 2 + y ^ 2))) := by
            refine tsum_congr ?_
            intro n
            have h_re0 : (((z0 + n)⁻¹).re) = 1 / ((n : ℝ) + x) := by
              simpa [z0, add_assoc, add_left_comm, add_comm] using re_inv_add_natCast_real x hx n
            have h_re1 :
                (((z1 + n)⁻¹).re) = ((n : ℝ) + x) / (((n : ℝ) + x) ^ 2 + y ^ 2) := by
              simpa [z1, add_assoc, add_left_comm, add_comm] using re_inv_add_natCast_imag x y hx n
            have hnx_pos : 0 < (n : ℝ) + x := by
              have hn : (0 : ℝ) ≤ n := by exact_mod_cast Nat.cast_nonneg n
              linarith
            have hnx_ne : ((n : ℝ) + x) ≠ 0 := ne_of_gt hnx_pos
            have hden_pos : 0 < ((n : ℝ) + x) ^ 2 + y ^ 2 := by
              have hsq : 0 < ((n : ℝ) + x) ^ 2 := by nlinarith [hnx_pos]
              nlinarith
            have hden_ne : (((n : ℝ) + x) ^ 2 + y ^ 2) ≠ 0 := ne_of_gt hden_pos
            calc
              (((z0 + n)⁻¹).re) - (((z1 + n)⁻¹).re)
                  = (1 / ((n : ℝ) + x)) - (((n : ℝ) + x) / (((n : ℝ) + x) ^ 2 + y ^ 2)) := by
                      simp [h_re0, h_re1]
              _ = y ^ 2 / (((n : ℝ) + x) * (((n : ℝ) + x) ^ 2 + y ^ 2)) := by
                      field_simp [hnx_ne, hden_ne]
                      ring
    _ = y ^ 2 *
          ∑' n : ℕ, (((n : ℝ) + x)⁻¹ * ((((n : ℝ) + x) ^ 2 + y ^ 2)⁻¹)) := by
          simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
            (tsum_mul_left (a := y ^ 2)
              (f := fun n : ℕ => (((n : ℝ) + x)⁻¹ * ((((n : ℝ) + x) ^ 2 + y ^ 2)⁻¹))))
    _ = y ^ 2 * ∑' n : ℕ, 1 / (((n : ℝ) + x) * (((n : ℝ) + x) ^ 2 + y ^ 2)) := by
          simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Specialization of `re_digamma_add_imag_sq` to the Q3 arch argument
`1/4 + i * π * ξ`. -/
lemma re_digamma_quarter_shift (ξ : ℝ) :
    (Q3.digamma ((1 / 4 : ℂ) + Complex.I * Real.pi * ξ)).re -
      (Q3.digamma (1 / 4 : ℂ)).re =
      (Real.pi * ξ) ^ 2 *
        ∑' n : ℕ,
          1 /
            (((n : ℝ) + (1 / 4 : ℝ)) *
              ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    (re_digamma_add_imag_sq (x := (1 / 4 : ℝ)) (y := Real.pi * ξ) (by norm_num))

/-- Exact shift formula for the archimedean density `a(ξ)` around `ξ=0`. -/
lemma a_eq_a0_sub_shift_series (ξ : ℝ) :
    Q3.a ξ =
      Q3.a 0 -
        (Real.pi * ξ) ^ 2 *
          ∑' n : ℕ,
            1 /
              (((n : ℝ) + (1 / 4 : ℝ)) *
                ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
  unfold Q3.a
  have hshift := re_digamma_quarter_shift ξ
  have h0 :
      (Q3.digamma ((1 / 4 : ℂ) + Complex.I * Real.pi * (0 : ℝ))).re =
        (Q3.digamma (1 / 4 : ℂ)).re := by
    simp
  have hbase :
      (Q3.digamma ((1 / 4 : ℂ) + Complex.I * Real.pi * ξ)).re =
        (Q3.digamma ((1 / 4 : ℂ) + Complex.I * Real.pi * (0 : ℝ))).re +
          (Real.pi * ξ) ^ 2 *
            ∑' n : ℕ,
              1 /
                (((n : ℝ) + (1 / 4 : ℝ)) *
                  ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
    linarith [hshift, h0]
  linarith

/-- Exact shift formula for the scaled archimedean density `a_star(ξ)`. -/
lemma a_star_eq_a_star0_sub_shift_series (ξ : ℝ) :
    Q3.a_star ξ =
      Q3.a_star 0 -
        (2 * Real.pi) * ((Real.pi * ξ) ^ 2) *
          ∑' n : ℕ,
            1 /
              (((n : ℝ) + (1 / 4 : ℝ)) *
                ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
  have ha := a_eq_a0_sub_shift_series ξ
  calc
    Q3.a_star ξ = 2 * Real.pi * Q3.a ξ := by
      rfl
    _ = 2 * Real.pi *
          (Q3.a 0 -
            (Real.pi * ξ) ^ 2 *
                ∑' n : ℕ,
                  1 /
                    (((n : ℝ) + (1 / 4 : ℝ)) *
                    ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2)))) := by
          simpa [ha]
    _ = 2 * Real.pi * Q3.a 0 -
          (2 * Real.pi) * ((Real.pi * ξ) ^ 2) *
            ∑' n : ℕ,
              1 /
                (((n : ℝ) + (1 / 4 : ℝ)) *
                  ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
          ring
    _ = Q3.a_star 0 -
          (2 * Real.pi) * ((Real.pi * ξ) ^ 2) *
            ∑' n : ℕ,
              1 /
                (((n : ℝ) + (1 / 4 : ℝ)) *
                  ((((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))) := by
          simpa [Q3.a_star]

/-- Immediate corollary of the shift-series formula:
`a_star` is pointwise bounded above by its value at `0`. -/
lemma a_star_le_a_star_zero (ξ : ℝ) :
    Q3.a_star ξ ≤ Q3.a_star 0 := by
  let s : ℕ → ℝ := fun n =>
    1 / (((n : ℝ) + (1 / 4 : ℝ)) * (((n : ℝ) + (1 / 4 : ℝ)) ^ 2 + (Real.pi * ξ) ^ 2))
  have h_series_nonneg :
      0 ≤ ∑' n : ℕ, s n := by
    refine tsum_nonneg ?_
    intro n
    dsimp [s]
    positivity
  have h_coef_nonneg : 0 ≤ (2 * Real.pi) * ((Real.pi * ξ) ^ 2) := by
    positivity
  have h_drop_nonneg :
      0 ≤ (2 * Real.pi) * ((Real.pi * ξ) ^ 2) * ∑' n : ℕ, s n := by
    exact mul_nonneg h_coef_nonneg h_series_nonneg
  have h_eq := a_star_eq_a_star0_sub_shift_series ξ
  have h_eq' :
      Q3.a_star ξ =
        Q3.a_star 0 - (2 * Real.pi) * ((Real.pi * ξ) ^ 2) * ∑' n : ℕ, s n := by
    simpa [s] using h_eq
  linarith [h_eq', h_drop_nonneg]

end Q3.Proofs.PrimeCert
