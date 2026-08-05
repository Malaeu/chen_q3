import Mathlib.RingTheory.Polynomial.ShiftedLegendre
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Real.Basic

/-!
# Ordinary Legendre affine kernel for the mode-four Ferrers gate

This file fixes only the affine orientation that converts Mathlib's shifted
Legendre convention into the standard ordinary convention.  It proves the
base cases, degree, parity, and endpoint values, together with two private
orientation mutants.

It does not prove a three-term recurrence, a differential equation, an
`x ^ 2` action, an analytic bound, orthogonality, a Ferrers series, or any
PSWF provenance statement.
-/

open Polynomial

noncomputable section

/-- The affine coordinate converting Mathlib's convention
`shiftedLegendre 1 = 1 - 2X` into the ordinary convention `P₁(X) = X`. -/
noncomputable def mode4OrdinaryLegendreAffine : ℝ[X] :=
  C (1 / 2 : ℝ) * (1 - X)

/-- The standard ordinary real Legendre polynomial, obtained by the exact
affine substitution `(1 - X) / 2`. -/
noncomputable def mode4OrdinaryLegendrePolynomial (n : ℕ) : ℝ[X] :=
  ((shiftedLegendre n).map (Int.castRingHom ℝ)).comp
    mode4OrdinaryLegendreAffine

/-- Function evaluation of the standard ordinary Legendre polynomial. -/
noncomputable def mode4OrdinaryLegendre (n : ℕ) (x : ℝ) : ℝ :=
  (mode4OrdinaryLegendrePolynomial n).eval x

@[simp]
theorem mode4OrdinaryLegendreAffine_eval (x : ℝ) :
    mode4OrdinaryLegendreAffine.eval x = (1 - x) / 2 := by
  simp [mode4OrdinaryLegendreAffine]
  ring

/-- Exact evaluation crosswalk to Mathlib's shifted polynomial. -/
theorem mode4OrdinaryLegendre_eval_eq_shiftedLegendre
    (n : ℕ) (x : ℝ) :
    mode4OrdinaryLegendre n x =
      Polynomial.eval₂
        (Int.castRingHom ℝ)
        ((1 - x) / 2)
        (shiftedLegendre n) := by
  rw [mode4OrdinaryLegendre, mode4OrdinaryLegendrePolynomial,
    Polynomial.eval_comp, Polynomial.eval_map,
    mode4OrdinaryLegendreAffine_eval]

@[simp]
theorem mode4OrdinaryLegendrePolynomial_zero :
    mode4OrdinaryLegendrePolynomial 0 = 1 := by
  norm_num [mode4OrdinaryLegendrePolynomial, Polynomial.shiftedLegendre,
    Finset.sum_range_succ]

@[simp]
theorem mode4OrdinaryLegendrePolynomial_one :
    mode4OrdinaryLegendrePolynomial 1 = X := by
  have hpoly : Polynomial.shiftedLegendre 1 = 1 - 2 * X := by
    norm_num [Polynomial.shiftedLegendre, Finset.sum_range_succ,
      sub_eq_add_neg]
  rw [mode4OrdinaryLegendrePolynomial, hpoly]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_X, Polynomial.sub_comp,
    Polynomial.one_comp, Polynomial.mul_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp]
  rw [mode4OrdinaryLegendreAffine]
  rw [← Polynomial.C_eq_natCast 2]
  rw [← mul_assoc, ← Polynomial.C_mul]
  norm_num

@[simp]
theorem mode4OrdinaryLegendre_zero (x : ℝ) :
    mode4OrdinaryLegendre 0 x = 1 := by
  simp [mode4OrdinaryLegendre]

@[simp]
theorem mode4OrdinaryLegendre_one (x : ℝ) :
    mode4OrdinaryLegendre 1 x = x := by
  simp [mode4OrdinaryLegendre]

@[simp]
theorem natDegree_mode4OrdinaryLegendrePolynomial (n : ℕ) :
    (mode4OrdinaryLegendrePolynomial n).natDegree = n := by
  rw [mode4OrdinaryLegendrePolynomial, Polynomial.natDegree_comp]
  rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
  have hdeg : mode4OrdinaryLegendreAffine.natDegree = 1 := by
    rw [mode4OrdinaryLegendreAffine,
      Polynomial.natDegree_C_mul (by norm_num)]
    rw [show (1 - X : ℝ[X]) = C (-1) * (X - C 1) by
      simp [sub_eq_add_neg]]
    rw [Polynomial.natDegree_C_mul (by norm_num),
      Polynomial.natDegree_X_sub_C]
  rw [Polynomial.natDegree_shiftedLegendre, hdeg]
  simp

/-- Exact parity in the ordinary convention. -/
theorem mode4OrdinaryLegendre_neg (n : ℕ) (x : ℝ) :
    mode4OrdinaryLegendre n (-x) =
      (-1 : ℝ) ^ n * mode4OrdinaryLegendre n x := by
  rw [mode4OrdinaryLegendre_eval_eq_shiftedLegendre,
    mode4OrdinaryLegendre_eval_eq_shiftedLegendre]
  have h := Polynomial.shiftedLegendre_eval_symm n ((1 + x) / 2 : ℝ)
  have harg : 1 - (1 + x) / 2 = (1 - x) / 2 := by ring
  simpa [harg] using h

@[simp]
theorem mode4OrdinaryLegendre_even (q : ℕ) (x : ℝ) :
    mode4OrdinaryLegendre (2 * q) (-x) =
      mode4OrdinaryLegendre (2 * q) x := by
  rw [mode4OrdinaryLegendre_neg]
  simp [pow_mul]

@[simp]
theorem mode4OrdinaryLegendre_odd (q : ℕ) (x : ℝ) :
    mode4OrdinaryLegendre (2 * q + 1) (-x) =
      -mode4OrdinaryLegendre (2 * q + 1) x := by
  rw [mode4OrdinaryLegendre_neg]
  simp [pow_add, pow_mul]

@[simp]
theorem mode4OrdinaryLegendre_at_one (n : ℕ) :
    mode4OrdinaryLegendre n 1 = 1 := by
  rw [mode4OrdinaryLegendre_eval_eq_shiftedLegendre]
  rw [show ((1 - (1 : ℝ)) / 2) = 0 by norm_num]
  rw [Polynomial.eval₂_at_zero]
  simp [Polynomial.coeff_shiftedLegendre]

@[simp]
theorem mode4OrdinaryLegendre_at_neg_one (n : ℕ) :
    mode4OrdinaryLegendre n (-1) = (-1 : ℝ) ^ n := by
  rw [mode4OrdinaryLegendre_neg, mode4OrdinaryLegendre_at_one]
  ring

/-! ## Planted orientation mutants -/

private noncomputable def mode4WrongOrdinaryLegendreAffine : ℝ[X] :=
  C (1 / 2 : ℝ) * (1 + X)

private theorem mode4WrongAffine_shiftedLegendre_one_eq_neg_X :
    ((shiftedLegendre 1).map (Int.castRingHom ℝ)).comp
        mode4WrongOrdinaryLegendreAffine =
      -X := by
  have hpoly : Polynomial.shiftedLegendre 1 = 1 - 2 * X := by
    norm_num [Polynomial.shiftedLegendre, Finset.sum_range_succ,
      sub_eq_add_neg]
  rw [hpoly]
  simp only [Polynomial.map_sub, Polynomial.map_one, Polynomial.map_mul,
    Polynomial.map_ofNat, Polynomial.map_X, Polynomial.sub_comp,
    Polynomial.one_comp, Polynomial.mul_comp, Polynomial.X_comp,
    Polynomial.ofNat_comp]
  rw [mode4WrongOrdinaryLegendreAffine]
  rw [← Polynomial.C_eq_natCast 2]
  rw [← mul_assoc, ← Polynomial.C_mul]
  norm_num

private theorem mode4WrongAffine_shiftedLegendre_one_ne_X :
    ((shiftedLegendre 1).map (Int.castRingHom ℝ)).comp
        mode4WrongOrdinaryLegendreAffine ≠
      X := by
  rw [mode4WrongAffine_shiftedLegendre_one_eq_neg_X]
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  norm_num at heval

private theorem mode4OddIndex_changes_sign_at_endpoints :
    mode4OrdinaryLegendre 1 (-1) ≠
      mode4OrdinaryLegendre 1 1 := by
  norm_num

#print axioms mode4OrdinaryLegendrePolynomial_one
#print axioms natDegree_mode4OrdinaryLegendrePolynomial
#print axioms mode4OrdinaryLegendre_neg
