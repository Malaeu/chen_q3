import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreGram
import Q3.Proofs.RouteB.D0Mode4LegendreHermitianCoordinateScale

/-!
# Exact finite even-Legendre quadratic form

This file realizes the finite Hermitian coordinate vector `b` as the exact
ordinary-Legendre polynomial

`sum q, (-1)^q D_q b_q P_(2q)`

and proves the corresponding `L²` and differential quadratic-form identities.
The phase supplies the negative neighboring entries of the literal forward
Hermitian matrix, while `D_q² = 4q+1` cancels the Legendre Gram weight.

Knowledge preflight before the write:

`./orchestrator/kb.py ask "mode4 finite even Legendre polynomial exact quadratic form L2 energy Gram Hermitian matrix"`

returned no hits. Retrieval is only a discovery receipt, not proof evidence.

This finite form does not prove `P₀` zero-freeness, form-core density, a global
minimizer, regular-solution identification, a nodal count, Goal 058 G3, Route B
promotion, or RH.
-/

open MeasureTheory Polynomial Matrix
open scoped BigOperators

namespace Q3.RouteB

/-- The finite even ordinary-Legendre synthesis in the literal forward
Hermitian coordinates. -/
noncomputable def mode4FiniteEvenLegendrePolynomial
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) : ℝ[X] :=
  ∑ q : Fin d,
    C (((-1 : ℝ) ^ q.val) *
        mode4DLMFEvenSimilarityScale G q.val * b q) *
      mode4OrdinaryLegendrePolynomial (2 * q.val)

private theorem mode4FiniteEvenLegendrePolynomial_eval
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) (x : ℝ) :
    (mode4FiniteEvenLegendrePolynomial G b).eval x =
      ∑ q : Fin d,
        ((-1 : ℝ) ^ q.val) *
          mode4DLMFEvenSimilarityScale G q.val * b q *
            mode4OrdinaryLegendre (2 * q.val) x := by
  classical
  unfold mode4FiniteEvenLegendrePolynomial
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp [mode4OrdinaryLegendre]

/-- The finite synthesis is an exact `L²(-1,1)` isometry up to the source
factor `2`. -/
theorem mode4FiniteEvenLegendrePolynomial_l2
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (mode4FiniteEvenLegendrePolynomial G b).eval x ^ 2) =
      2 * (b ⬝ᵥ b) := by
  classical
  simp_rw [mode4FiniteEvenLegendrePolynomial_eval, sq]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [intervalIntegral.integral_finset_sum]
  · have hinner (q : Fin d) :
        (∫ x in (-1 : ℝ)..1,
          ∑ r : Fin d,
            ((-1 : ℝ) ^ q.val) *
                mode4DLMFEvenSimilarityScale G q.val * b q *
                  mode4OrdinaryLegendre (2 * q.val) x *
              (((-1 : ℝ) ^ r.val) *
                mode4DLMFEvenSimilarityScale G r.val * b r *
                  mode4OrdinaryLegendre (2 * r.val) x)) =
          ∑ r : Fin d,
            ∫ x in (-1 : ℝ)..1,
              ((-1 : ℝ) ^ q.val) *
                  mode4DLMFEvenSimilarityScale G q.val * b q *
                    mode4OrdinaryLegendre (2 * q.val) x *
                (((-1 : ℝ) ^ r.val) *
                  mode4DLMFEvenSimilarityScale G r.val * b r *
                    mode4OrdinaryLegendre (2 * r.val) x) := by
      rw [intervalIntegral.integral_finset_sum]
      intro r hr
      apply Continuous.intervalIntegrable
      simp only [mode4OrdinaryLegendre]
      fun_prop
    simp_rw [hinner]
    have hreassoc (q r : Fin d) (x : ℝ) :
        ((-1 : ℝ) ^ q.val) *
              mode4DLMFEvenSimilarityScale G q.val * b q *
                mode4OrdinaryLegendre (2 * q.val) x *
            (((-1 : ℝ) ^ r.val) *
              mode4DLMFEvenSimilarityScale G r.val * b r *
                mode4OrdinaryLegendre (2 * r.val) x) =
          (((-1 : ℝ) ^ q.val) *
              mode4DLMFEvenSimilarityScale G q.val * b q *
            (((-1 : ℝ) ^ r.val) *
              mode4DLMFEvenSimilarityScale G r.val * b r)) *
            (mode4OrdinaryLegendre (2 * q.val) x *
              mode4OrdinaryLegendre (2 * r.val) x) := by ring
    simp_rw [hreassoc, intervalIntegral.integral_const_mul,
      mode4OrdinaryLegendre_even_gram]
    simp_rw [← Fin.ext_iff]
    simp only [mul_ite, mul_zero, Fintype.sum_ite_eq]
    simp only [dotProduct]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    have hscale :=
      mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight G q.val hG
    have hsign :
        ((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ q.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hsign2 : ((-1 : ℝ) ^ q.val) ^ 2 = 1 := by
      simpa [pow_two] using hsign
    have hden : (4 * (q.val : ℝ) + 1) ≠ 0 := by positivity
    push_cast at hscale ⊢
    field_simp [hden]
    rw [hsign2, hscale]
    ring
  · intro q hq
    apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

private theorem mode4FiniteEvenLegendre_Xsq_zero (G x : ℝ) :
    G * x ^ 2 * mode4OrdinaryLegendre 0 x =
      -mode4PSWFLegendreSubdiagonal G 1 *
          mode4OrdinaryLegendre 2 x +
        (mode4PSWFLegendreDiagonal G 0 -
          ((0 : ℝ) * (0 + 1))) *
          mode4OrdinaryLegendre 0 x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_three_term_succ 0)
  simp only [eval_mul, eval_C, eval_X, eval_sub] at h
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at h ⊢
  unfold mode4PSWFLegendreSubdiagonal mode4PSWFLegendreDiagonal
  norm_num [mode4JacobiIndex]
  change G * x ^ 2 =
    -(-(G * 2) / 3 *
      (mode4OrdinaryLegendrePolynomial 2).eval x) + G / 3
  have hx : x ^ 2 =
      (2 * (mode4OrdinaryLegendrePolynomial 2).eval x + 1) / 3 := by
    linarith
  rw [hx]
  ring

private theorem mode4FiniteEvenLegendre_Xsq_succ
    (G x : ℝ) (q : ℕ) :
    G * x ^ 2 * mode4OrdinaryLegendre (2 * (q + 1)) x =
      -mode4PSWFLegendreSubdiagonal G (q + 2) *
          mode4OrdinaryLegendre (2 * (q + 2)) x +
        (mode4PSWFLegendreDiagonal G (q + 1) -
          (((2 * (q + 1) : ℕ) : ℝ) *
            (((2 * (q + 1) : ℕ) : ℝ) + 1))) *
          mode4OrdinaryLegendre (2 * (q + 1)) x -
        mode4PSWFLegendreSuperdiagonal G q *
          mode4OrdinaryLegendre (2 * q) x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_X_sq_mul (2 * q))
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at h
  have hupper :
      G * ((((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
        (((2 * q + 4 : ℕ) : ℝ) / ((4 * q + 7 : ℕ) : ℝ))) =
        -mode4PSWFLegendreSubdiagonal G (q + 2) := by
    have hN : mode4JacobiIndex (q + 2) = 2 * (q : ℝ) + 4 := by
      unfold mode4JacobiIndex
      push_cast
      ring
    have hsub :
        -mode4PSWFLegendreSubdiagonal G (q + 2) =
          G * (mode4JacobiIndex (q + 2) - 1) *
              mode4JacobiIndex (q + 2) /
            ((2 * mode4JacobiIndex (q + 2) - 3) *
              (2 * mode4JacobiIndex (q + 2) - 1)) := by
      unfold mode4PSWFLegendreSubdiagonal
      dsimp
      ring
    rw [hsub, hN]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [div_mul_div_comm]
    ring
  have hdiag :
      G * (((((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
          (((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 7 : ℕ) : ℝ))) +
        ((((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
          (((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 3 : ℕ) : ℝ)))) =
        mode4PSWFLegendreDiagonal G (q + 1) -
          (((2 * (q + 1) : ℕ) : ℝ) *
            (((2 * (q + 1) : ℕ) : ℝ) + 1)) := by
    have hN : mode4JacobiIndex (q + 1) = 2 * (q : ℝ) + 2 := by
      unfold mode4JacobiIndex
      push_cast
      ring
    have hD :
        mode4PSWFLegendreDiagonal G (q + 1) -
            mode4JacobiIndex (q + 1) *
              (mode4JacobiIndex (q + 1) + 1) =
          G * (2 * mode4JacobiIndex (q + 1) *
              (mode4JacobiIndex (q + 1) + 1) - 1) /
            ((2 * mode4JacobiIndex (q + 1) - 1) *
              (2 * mode4JacobiIndex (q + 1) + 3)) := by
      unfold mode4PSWFLegendreDiagonal
      dsimp
      ring
    rw [show (((2 * (q + 1) : ℕ) : ℝ) *
          (((2 * (q + 1) : ℕ) : ℝ) + 1)) =
        mode4JacobiIndex (q + 1) *
          (mode4JacobiIndex (q + 1) + 1) by
      rw [hN]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring,
      hD, hN]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hden : (4 * (q : ℝ) + 3) ≠ 0 := by positivity
    have hden' : (3 + (q : ℝ) * 4) ≠ 0 := by positivity
    field_simp [hden]
    have hcancel := inv_mul_cancel₀ hden'
    ring_nf at hcancel ⊢
    linear_combination
      -(G * (385 + 1228 * (q : ℝ) + 1416 * (q : ℝ) ^ 2 +
        704 * (q : ℝ) ^ 3 + 128 * (q : ℝ) ^ 4)) * hcancel
  have hlower :
      G * ((((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
        (((2 * q + 1 : ℕ) : ℝ) / ((4 * q + 3 : ℕ) : ℝ))) =
        -mode4PSWFLegendreSuperdiagonal G q := by
    unfold mode4PSWFLegendreSuperdiagonal mode4JacobiIndex
    push_cast
    field_simp
    all_goals ring
  change G * x ^ 2 *
      (mode4OrdinaryLegendrePolynomial (2 * (q + 1))).eval x = _
  simp only [mode4OrdinaryLegendre]
  norm_num [Nat.mul_add, Nat.mul_assoc] at h ⊢
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hupper hdiag hlower ⊢
  calc
    _ = G *
        (((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 5) *
            ((2 * (q : ℝ) + 4) / (4 * (q : ℝ) + 7))) *
            (mode4OrdinaryLegendrePolynomial (2 * q + 4)).eval x +
          (((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 5) *
              ((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 7)) +
            (2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 5) *
              ((2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 3))) *
            (mode4OrdinaryLegendrePolynomial (2 * q + 2)).eval x +
          ((2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 5) *
            ((2 * (q : ℝ) + 1) / (4 * (q : ℝ) + 3))) *
            (mode4OrdinaryLegendrePolynomial (2 * q)).eval x)) := by
        have hG := congrArg (fun y : ℝ => G * y) h
        ring_nf at hG ⊢
        exact hG
    _ = _ := by
      rw [mul_add, mul_add, ← mul_assoc, hupper,
        ← mul_assoc, hdiag, ← mul_assoc, hlower]
      ring

private theorem mode4FiniteEvenLegendre_potential_pair_zero
    (G : ℝ) (r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      G * x ^ 2 * mode4OrdinaryLegendre 0 x *
        mode4OrdinaryLegendre (2 * r) x) =
      (-mode4PSWFLegendreSubdiagonal G 1) *
          (if 1 = r then 2 / 5 else 0) +
        mode4PSWFLegendreDiagonal G 0 *
          (if 0 = r then 2 else 0) := by
  have hpoint (x : ℝ) :
      G * x ^ 2 * mode4OrdinaryLegendre 0 x *
          mode4OrdinaryLegendre (2 * r) x =
        (-mode4PSWFLegendreSubdiagonal G 1) *
            (mode4OrdinaryLegendre 2 x *
              mode4OrdinaryLegendre (2 * r) x) +
          mode4PSWFLegendreDiagonal G 0 *
            (mode4OrdinaryLegendre 0 x *
              mode4OrdinaryLegendre (2 * r) x) := by
    rw [mode4FiniteEvenLegendre_Xsq_zero]
    ring
  rw [intervalIntegral.integral_congr (fun x hx => hpoint x)]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      mode4OrdinaryLegendre_even_gram 1 r,
      mode4OrdinaryLegendre_even_gram 0 r]
    norm_num
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

private theorem mode4FiniteEvenLegendre_potential_pair_succ
    (G : ℝ) (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      G * x ^ 2 * mode4OrdinaryLegendre (2 * (q + 1)) x *
        mode4OrdinaryLegendre (2 * r) x) =
      (-mode4PSWFLegendreSubdiagonal G (q + 2)) *
          (if q + 2 = r then
            2 / (((4 * (q + 2) + 1 : ℕ) : ℝ)) else 0) +
        (mode4PSWFLegendreDiagonal G (q + 1) -
          (((2 * (q + 1) : ℕ) : ℝ) *
            (((2 * (q + 1) : ℕ) : ℝ) + 1))) *
          (if q + 1 = r then
            2 / (((4 * (q + 1) + 1 : ℕ) : ℝ)) else 0) +
        (-mode4PSWFLegendreSuperdiagonal G q) *
          (if q = r then
            2 / (((4 * q + 1 : ℕ) : ℝ)) else 0) := by
  have hpoint (x : ℝ) :
      G * x ^ 2 * mode4OrdinaryLegendre (2 * (q + 1)) x *
          mode4OrdinaryLegendre (2 * r) x =
        (-mode4PSWFLegendreSubdiagonal G (q + 2)) *
            (mode4OrdinaryLegendre (2 * (q + 2)) x *
              mode4OrdinaryLegendre (2 * r) x) +
          (mode4PSWFLegendreDiagonal G (q + 1) -
            (((2 * (q + 1) : ℕ) : ℝ) *
              (((2 * (q + 1) : ℕ) : ℝ) + 1))) *
            (mode4OrdinaryLegendre (2 * (q + 1)) x *
              mode4OrdinaryLegendre (2 * r) x) +
          (-mode4PSWFLegendreSuperdiagonal G q) *
            (mode4OrdinaryLegendre (2 * q) x *
              mode4OrdinaryLegendre (2 * r) x) := by
    rw [mode4FiniteEvenLegendre_Xsq_succ]
    ring
  rw [intervalIntegral.integral_congr (fun x hx => hpoint x)]
  rw [intervalIntegral.integral_add]
  · rw [intervalIntegral.integral_add]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul,
        mode4OrdinaryLegendre_even_gram (q + 2) r,
        mode4OrdinaryLegendre_even_gram (q + 1) r,
        mode4OrdinaryLegendre_even_gram q r]
    · apply Continuous.intervalIntegrable
      simp only [mode4OrdinaryLegendre]
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [mode4OrdinaryLegendre]
      fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

private noncomputable def mode4FiniteEvenLegendreEnergyPair
    (G Λ : ℝ) (q r : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    (1 - x ^ 2) *
        (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x *
        (mode4OrdinaryLegendrePolynomial (2 * r)).derivative.eval x +
      G * x ^ 2 * mode4OrdinaryLegendre (2 * q) x *
        mode4OrdinaryLegendre (2 * r) x -
      (Λ + G) *
        (mode4OrdinaryLegendre (2 * q) x *
          mode4OrdinaryLegendre (2 * r) x)

private theorem mode4FiniteEvenLegendreEnergyPair_zero
    (G Λ : ℝ) (r : ℕ) :
    mode4FiniteEvenLegendreEnergyPair G Λ 0 r =
      (-mode4PSWFLegendreSubdiagonal G 1) *
          (if 1 = r then 2 / 5 else 0) +
        (mode4PSWFLegendreDiagonal G 0 - (Λ + G)) *
          (if 0 = r then 2 else 0) := by
  unfold mode4FiniteEvenLegendreEnergyPair
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_add]
    · rw [mode4OrdinaryLegendre_even_derivative_gram 0 r,
        mode4FiniteEvenLegendre_potential_pair_zero G r,
        intervalIntegral.integral_const_mul,
        mode4OrdinaryLegendre_even_gram 0 r]
      norm_num
      split_ifs <;> ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [mode4OrdinaryLegendre]
      fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

private theorem mode4FiniteEvenLegendreEnergyPair_succ
    (G Λ : ℝ) (q r : ℕ) :
    mode4FiniteEvenLegendreEnergyPair G Λ (q + 1) r =
      (-mode4PSWFLegendreSubdiagonal G (q + 2)) *
          (if q + 2 = r then
            2 / (((4 * (q + 2) + 1 : ℕ) : ℝ)) else 0) +
        (mode4PSWFLegendreDiagonal G (q + 1) - (Λ + G)) *
          (if q + 1 = r then
            2 / (((4 * (q + 1) + 1 : ℕ) : ℝ)) else 0) +
        (-mode4PSWFLegendreSuperdiagonal G q) *
          (if q = r then
            2 / (((4 * q + 1 : ℕ) : ℝ)) else 0) := by
  unfold mode4FiniteEvenLegendreEnergyPair
  rw [intervalIntegral.integral_sub]
  · rw [intervalIntegral.integral_add]
    · rw [mode4OrdinaryLegendre_even_derivative_gram (q + 1) r,
        mode4FiniteEvenLegendre_potential_pair_succ G q r,
        intervalIntegral.integral_const_mul,
        mode4OrdinaryLegendre_even_gram (q + 1) r]
      push_cast
      split_ifs <;> ring
    · apply Continuous.intervalIntegrable
      fun_prop
    · apply Continuous.intervalIntegrable
      simp only [mode4OrdinaryLegendre]
      fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop
  · apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

private theorem mode4FiniteEvenLegendreEnergyPair_diag
    (G Λ : ℝ) (q : ℕ) :
    mode4FiniteEvenLegendreEnergyPair G Λ q q =
      mode4JacobiCenter G Λ q *
        (2 / (((4 * q + 1 : ℕ) : ℝ))) := by
  cases q with
  | zero =>
      rw [mode4FiniteEvenLegendreEnergyPair_zero]
      norm_num
      rw [mode4JacobiCenter_eq_pswfLegendreDiagonal_shift]
  | succ q =>
      rw [mode4FiniteEvenLegendreEnergyPair_succ]
      have hneUpper : q + 2 ≠ q + 1 := by omega
      have hneLower : q ≠ q + 1 := by omega
      rw [if_neg hneUpper, if_pos rfl, if_neg hneLower]
      simp only [mul_zero, zero_add, add_zero]
      rw [mode4JacobiCenter_eq_pswfLegendreDiagonal_shift]

private theorem mode4FiniteEvenLegendreEnergyPair_upper
    (G Λ : ℝ) (q : ℕ) :
    mode4FiniteEvenLegendreEnergyPair G Λ q (q + 1) =
      mode4JacobiLower G (q + 1) *
        (2 / (((4 * (q + 1) + 1 : ℕ) : ℝ))) := by
  cases q with
  | zero =>
      rw [mode4FiniteEvenLegendreEnergyPair_zero]
      norm_num
      rw [mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal]
      ring
  | succ q =>
      rw [mode4FiniteEvenLegendreEnergyPair_succ]
      have hneDiag : q + 1 ≠ q + 2 := by omega
      have hneLower : q ≠ q + 2 := by omega
      rw [if_pos rfl, if_neg hneDiag, if_neg hneLower]
      simp only [mul_zero, add_zero]
      rw [mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal]

private theorem mode4FiniteEvenLegendreEnergyPair_symm
    (G Λ : ℝ) (q r : ℕ) :
    mode4FiniteEvenLegendreEnergyPair G Λ q r =
      mode4FiniteEvenLegendreEnergyPair G Λ r q := by
  unfold mode4FiniteEvenLegendreEnergyPair
  apply intervalIntegral.integral_congr
  intro x hx
  ring

private theorem mode4FiniteEvenLegendreEnergyPair_eq_zero_of_far
    (G Λ : ℝ) (q r : ℕ)
    (hdiag : q ≠ r) (hupper : r ≠ q + 1) (hlower : q ≠ r + 1) :
    mode4FiniteEvenLegendreEnergyPair G Λ q r = 0 := by
  cases q with
  | zero =>
      rw [mode4FiniteEvenLegendreEnergyPair_zero]
      have h0 : ¬0 = r := hdiag
      have h1 : ¬1 = r := by omega
      rw [if_neg h1, if_neg h0]
      ring
  | succ q =>
      rw [mode4FiniteEvenLegendreEnergyPair_succ]
      have h1 : ¬q + 2 = r := by omega
      have h2 : ¬q + 1 = r := by omega
      have h3 : ¬q = r := by omega
      rw [if_neg h1, if_neg h2, if_neg h3]
      ring

private theorem mode4FiniteEvenLegendre_scale_lower_balance_of_fin_succ
    (G Λ : ℝ) {d : ℕ} (hG : 0 < G) (q r : Fin d)
    (hsucc : r.val = q.val + 1) :
    mode4JacobiLower G r.val *
        mode4DLMFEvenSimilarityScale G q.val =
      mode4DLMFEvenSimilarityScale G r.val *
        mode4JacobiSymmetricOff G q.val := by
  have hne : r ≠ q := by
    intro h
    subst r
    omega
  have hfar : q.val ≠ q.val + 1 + 1 := by omega
  have hsim :=
    mode4DLMFEvenFiniteMatrix_mul_scale_eq_scale_mul_forwardHermitian
      G Λ d hG r q
  simp [mode4DLMFEvenFiniteMatrix,
    mode4ForwardHermitianFiniteMatrix, hne, hsucc, hfar,
    mode4DLMFEvenLower_eq_neg_jacobiLower] at hsim
  rw [hsucc]
  exact hsim

private theorem mode4FiniteEvenLegendre_scaledEnergyPair_eq_matrix
    (G Λ : ℝ) {d : ℕ} (hG : 0 < G) (q r : Fin d) :
    (((-1 : ℝ) ^ q.val) *
        mode4DLMFEvenSimilarityScale G q.val) *
      (((-1 : ℝ) ^ r.val) *
        mode4DLMFEvenSimilarityScale G r.val) *
      mode4FiniteEvenLegendreEnergyPair G Λ q.val r.val =
        2 * mode4ForwardHermitianFiniteMatrix G Λ d q r := by
  unfold mode4ForwardHermitianFiniteMatrix
  by_cases hdiag : q = r
  · subst r
    rw [if_pos rfl,
      mode4FiniteEvenLegendreEnergyPair_diag]
    have hscale :=
      mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight G q.val hG
    have hsign :
        ((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ q.val) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hcoeff :
        (((-1 : ℝ) ^ q.val) *
            mode4DLMFEvenSimilarityScale G q.val) *
          (((-1 : ℝ) ^ q.val) *
            mode4DLMFEvenSimilarityScale G q.val) =
          mode4DLMFEvenSimilarityScale G q.val ^ 2 := by
      calc
        _ = (((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ q.val)) *
              mode4DLMFEvenSimilarityScale G q.val ^ 2 := by ring
        _ = _ := by rw [hsign]; ring
    rw [hcoeff, hscale]
    have hden : (0 : ℝ) < 4 * (q.val : ℝ) + 1 := by positivity
    push_cast
    field_simp [hden.ne']
  · rw [if_neg hdiag]
    by_cases hupper : r.val = q.val + 1
    · rw [if_pos hupper]
      have hpair :
          mode4FiniteEvenLegendreEnergyPair G Λ q.val r.val =
            mode4JacobiLower G r.val *
              (2 / (((4 * r.val + 1 : ℕ) : ℝ))) := by
        rw [hupper]
        exact mode4FiniteEvenLegendreEnergyPair_upper G Λ q.val
      rw [hpair]
      have hsign :
          ((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ r.val) = -1 := by
        rw [hupper, pow_succ]
        have hs :
            ((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ q.val) = 1 := by
          rw [← pow_add, ← two_mul, pow_mul]
          norm_num
        nlinarith
      have hscale :=
        mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight G r.val hG
      have hbalance :=
        mode4FiniteEvenLegendre_scale_lower_balance_of_fin_succ
          G Λ hG q r hupper
      have hDpos := mode4DLMFEvenSimilarityScale_pos G r.val hG
      calc
        (((-1 : ℝ) ^ q.val) *
              mode4DLMFEvenSimilarityScale G q.val) *
            (((-1 : ℝ) ^ r.val) *
              mode4DLMFEvenSimilarityScale G r.val) *
            (mode4JacobiLower G r.val *
              (2 / (((4 * r.val + 1 : ℕ) : ℝ)))) =
          (((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ r.val)) * 2 *
              (mode4JacobiLower G r.val *
                mode4DLMFEvenSimilarityScale G q.val) /
              mode4DLMFEvenSimilarityScale G r.val := by
            push_cast
            rw [← hscale]
            field_simp [hDpos.ne']
        _ = -2 *
              (mode4JacobiLower G r.val *
                mode4DLMFEvenSimilarityScale G q.val) /
              mode4DLMFEvenSimilarityScale G r.val := by
            rw [hsign]
            ring
        _ = -2 *
              (mode4DLMFEvenSimilarityScale G r.val *
                mode4JacobiSymmetricOff G q.val) /
              mode4DLMFEvenSimilarityScale G r.val := by
            rw [hbalance]
        _ = 2 * -mode4JacobiSymmetricOff G q.val := by
            field_simp [hDpos.ne']
    · rw [if_neg hupper]
      by_cases hlower : q.val = r.val + 1
      · rw [if_pos hlower,
          mode4FiniteEvenLegendreEnergyPair_symm]
        have hpair :
            mode4FiniteEvenLegendreEnergyPair G Λ r.val q.val =
              mode4JacobiLower G q.val *
                (2 / (((4 * q.val + 1 : ℕ) : ℝ))) := by
          rw [hlower]
          exact mode4FiniteEvenLegendreEnergyPair_upper G Λ r.val
        rw [hpair]
        have hsign :
            ((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ r.val) = -1 := by
          rw [hlower, pow_succ]
          have hs :
              ((-1 : ℝ) ^ r.val) * ((-1 : ℝ) ^ r.val) = 1 := by
            rw [← pow_add, ← two_mul, pow_mul]
            norm_num
          nlinarith
        have hscale :=
          mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight G q.val hG
        have hbalance :=
          mode4FiniteEvenLegendre_scale_lower_balance_of_fin_succ
            G Λ hG r q hlower
        have hDpos := mode4DLMFEvenSimilarityScale_pos G q.val hG
        calc
          (((-1 : ℝ) ^ q.val) *
                mode4DLMFEvenSimilarityScale G q.val) *
              (((-1 : ℝ) ^ r.val) *
                mode4DLMFEvenSimilarityScale G r.val) *
              (mode4JacobiLower G q.val *
                (2 / (((4 * q.val + 1 : ℕ) : ℝ)))) =
            (((-1 : ℝ) ^ q.val) * ((-1 : ℝ) ^ r.val)) * 2 *
                (mode4JacobiLower G q.val *
                  mode4DLMFEvenSimilarityScale G r.val) /
                mode4DLMFEvenSimilarityScale G q.val := by
              push_cast
              rw [← hscale]
              field_simp [hDpos.ne']
          _ = -2 *
                (mode4JacobiLower G q.val *
                  mode4DLMFEvenSimilarityScale G r.val) /
                mode4DLMFEvenSimilarityScale G q.val := by
              rw [hsign]
              ring
          _ = -2 *
                (mode4DLMFEvenSimilarityScale G q.val *
                  mode4JacobiSymmetricOff G r.val) /
                mode4DLMFEvenSimilarityScale G q.val := by
              rw [hbalance]
          _ = 2 * -mode4JacobiSymmetricOff G r.val := by
              field_simp [hDpos.ne']
      · rw [if_neg hlower]
        have hdiagVal : q.val ≠ r.val := by
          intro h
          exact hdiag (Fin.ext h)
        rw [mode4FiniteEvenLegendreEnergyPair_eq_zero_of_far
          G Λ q.val r.val hdiagVal hupper hlower]
        ring

private theorem mode4FiniteEvenLegendrePolynomial_derivative_eval
    (G : ℝ) {d : ℕ} (b : Fin d → ℝ) (x : ℝ) :
    (mode4FiniteEvenLegendrePolynomial G b).derivative.eval x =
      ∑ q : Fin d,
        ((-1 : ℝ) ^ q.val) *
          mode4DLMFEvenSimilarityScale G q.val * b q *
            (mode4OrdinaryLegendrePolynomial
              (2 * q.val)).derivative.eval x := by
  classical
  unfold mode4FiniteEvenLegendrePolynomial
  rw [derivative_sum, eval_finset_sum]
  apply Finset.sum_congr rfl
  intro q hq
  simp only [derivative_mul, derivative_C, zero_mul, zero_add,
    eval_mul, eval_C]

private theorem mode4FiniteEvenLegendre_energy_pointwise
    (G Λ : ℝ) {d : ℕ} (b : Fin d → ℝ) (x : ℝ) :
    (1 - x ^ 2) *
          ((mode4FiniteEvenLegendrePolynomial G b).derivative.eval x) ^ 2 +
        G * x ^ 2 *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2 -
        (Λ + G) *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2 =
      ∑ q : Fin d, ∑ r : Fin d,
        (((( -1 : ℝ) ^ q.val) *
            mode4DLMFEvenSimilarityScale G q.val * b q) *
          (((-1 : ℝ) ^ r.val) *
            mode4DLMFEvenSimilarityScale G r.val * b r)) *
          ((1 - x ^ 2) *
              (mode4OrdinaryLegendrePolynomial
                (2 * q.val)).derivative.eval x *
              (mode4OrdinaryLegendrePolynomial
                (2 * r.val)).derivative.eval x +
            G * x ^ 2 * mode4OrdinaryLegendre (2 * q.val) x *
              mode4OrdinaryLegendre (2 * r.val) x -
            (Λ + G) *
              (mode4OrdinaryLegendre (2 * q.val) x *
                mode4OrdinaryLegendre (2 * r.val) x)) := by
  classical
  rw [mode4FiniteEvenLegendrePolynomial_derivative_eval,
    mode4FiniteEvenLegendrePolynomial_eval]
  simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- The exact differential quadratic form of the finite synthesis is twice
the literal forward-Hermitian matrix quadratic form. -/
theorem mode4FiniteEvenLegendrePolynomial_energy
    (G Λ : ℝ) {d : ℕ} (b : Fin d → ℝ) (hG : 0 < G) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
          ((mode4FiniteEvenLegendrePolynomial G b).derivative.eval x) ^ 2 +
        G * x ^ 2 *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2 -
        (Λ + G) *
          ((mode4FiniteEvenLegendrePolynomial G b).eval x) ^ 2) =
      2 *
        (b ⬝ᵥ
          ((mode4ForwardHermitianFiniteMatrix G Λ d) *ᵥ b)) := by
  classical
  rw [intervalIntegral.integral_congr
    (fun x hx => mode4FiniteEvenLegendre_energy_pointwise G Λ b x)]
  rw [intervalIntegral.integral_finset_sum]
  · have hinner (q : Fin d) :
        (∫ x in (-1 : ℝ)..1,
          ∑ r : Fin d,
            (((( -1 : ℝ) ^ q.val) *
                mode4DLMFEvenSimilarityScale G q.val * b q) *
              (((-1 : ℝ) ^ r.val) *
                mode4DLMFEvenSimilarityScale G r.val * b r)) *
              ((1 - x ^ 2) *
                  (mode4OrdinaryLegendrePolynomial
                    (2 * q.val)).derivative.eval x *
                  (mode4OrdinaryLegendrePolynomial
                    (2 * r.val)).derivative.eval x +
                G * x ^ 2 * mode4OrdinaryLegendre (2 * q.val) x *
                  mode4OrdinaryLegendre (2 * r.val) x -
                (Λ + G) *
                  (mode4OrdinaryLegendre (2 * q.val) x *
                    mode4OrdinaryLegendre (2 * r.val) x))) =
          ∑ r : Fin d,
            (((( -1 : ℝ) ^ q.val) *
                mode4DLMFEvenSimilarityScale G q.val * b q) *
              (((-1 : ℝ) ^ r.val) *
                mode4DLMFEvenSimilarityScale G r.val * b r)) *
              mode4FiniteEvenLegendreEnergyPair G Λ q.val r.val := by
      rw [intervalIntegral.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro r hr
        rw [intervalIntegral.integral_const_mul]
        rfl
      · intro r hr
        apply Continuous.intervalIntegrable
        simp only [mode4OrdinaryLegendre]
        fun_prop
    simp_rw [hinner]
    have hreassoc (q r : Fin d) :
        (((( -1 : ℝ) ^ q.val) *
              mode4DLMFEvenSimilarityScale G q.val * b q) *
            (((-1 : ℝ) ^ r.val) *
              mode4DLMFEvenSimilarityScale G r.val * b r)) *
            mode4FiniteEvenLegendreEnergyPair G Λ q.val r.val =
          (b q * b r) *
            ((((-1 : ℝ) ^ q.val) *
                mode4DLMFEvenSimilarityScale G q.val) *
              (((-1 : ℝ) ^ r.val) *
                mode4DLMFEvenSimilarityScale G r.val) *
              mode4FiniteEvenLegendreEnergyPair G Λ q.val r.val) := by
      ring
    simp_rw [hreassoc,
      mode4FiniteEvenLegendre_scaledEnergyPair_eq_matrix G Λ hG]
    simp only [dotProduct, Matrix.mulVec]
    change
      (∑ q ∈ Finset.univ, ∑ r ∈ Finset.univ,
        b q * b r *
          (2 * mode4ForwardHermitianFiniteMatrix G Λ d q r)) =
        2 * ∑ q ∈ Finset.univ,
          b q * ∑ r ∈ Finset.univ,
            mode4ForwardHermitianFiniteMatrix G Λ d q r * b r
    rw [Finset.mul_sum]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    apply Finset.sum_congr rfl
    intro r hr
    ring
  · intro q hq
    apply Continuous.intervalIntegrable
    simp only [mode4OrdinaryLegendre]
    fun_prop

#print axioms mode4FiniteEvenLegendrePolynomial_l2
#print axioms mode4FiniteEvenLegendrePolynomial_energy

end Q3.RouteB
