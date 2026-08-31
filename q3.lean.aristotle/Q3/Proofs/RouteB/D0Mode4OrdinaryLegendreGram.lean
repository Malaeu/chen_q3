import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreXSquaredAction
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreIntervalBound
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Exact even ordinary-Legendre Gram identities

This file supplies the reusable integral Gram layer needed before any finite
prolate quadratic-form theorem.  It depends only on the exact ordinary
Legendre polynomial, its ODE and recurrence actions, and interval calculus.

It does not consume a selected PSWF, a root, a zero count, a minimizer, a
Ferrers solution structure, or a Goal 058 conclusion.
-/

open MeasureTheory Polynomial Set

namespace Q3.RouteB

private theorem mode4OrdinaryLegendre_gram_offdiag
    (n m : ℕ) (hnm : n ≠ m) :
    (∫ x in (-1 : ℝ)..1,
      mode4OrdinaryLegendre n x * mode4OrdinaryLegendre m x) = 0 := by
  let p : ℝ[X] := mode4OrdinaryLegendrePolynomial n
  let s : ℝ[X] := mode4OrdinaryLegendrePolynomial m
  let fluxPoly : ℝ[X] :=
    (1 - X ^ 2) * (p.derivative * s - p * s.derivative)
  have hpODE :
      (1 - X ^ 2) * p.derivative.derivative -
          2 * X * p.derivative + C ((n : ℝ) * (n + 1)) * p = 0 := by
    simpa [p] using mode4OrdinaryLegendrePolynomial_differentialEquation n
  have hsODE :
      (1 - X ^ 2) * s.derivative.derivative -
          2 * X * s.derivative + C ((m : ℝ) * (m + 1)) * s = 0 := by
    simpa [s] using mode4OrdinaryLegendrePolynomial_differentialEquation m
  have hfluxDerivative :
      fluxPoly.derivative =
        C ((m : ℝ) * (m + 1) - (n : ℝ) * (n + 1)) * (p * s) := by
    dsimp [fluxPoly]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_one, Polynomial.derivative_pow]
    rw [map_sub]
    norm_num
    have hCtwo : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_ofNat 2
    rw [hCtwo]
    norm_num at hpODE hsODE
    linear_combination hpODE * s - hsODE * p
  have hderiv :
      deriv (fun x : ℝ => fluxPoly.eval x) =
        fun x : ℝ =>
          ((m : ℝ) * (m + 1) - (n : ℝ) * (n + 1)) *
            (mode4OrdinaryLegendre n x * mode4OrdinaryLegendre m x) := by
    funext x
    have h := fluxPoly.hasDerivAt x
    rw [hfluxDerivative] at h
    simpa [p, s, mode4OrdinaryLegendre] using h.deriv
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => fluxPoly.eval x)
    hderiv
    (fun x _ => fluxPoly.differentiableAt)
    (by
      exact
        ((continuous_const.mul
          ((mode4OrdinaryLegendrePolynomial n).continuous.mul
            (mode4OrdinaryLegendrePolynomial m).continuous))).continuousOn)
  have hzero :
      (∫ x in (-1 : ℝ)..1,
        ((m : ℝ) * (m + 1) - (n : ℝ) * (n + 1)) *
          (mode4OrdinaryLegendre n x * mode4OrdinaryLegendre m x)) = 0 := by
    simpa [fluxPoly, p, s] using hftc
  rw [intervalIntegral.integral_const_mul] at hzero
  have hcoef :
      (m : ℝ) * (m + 1) - (n : ℝ) * (n + 1) ≠ 0 := by
    intro h
    have hm0 : 0 ≤ (m : ℝ) := by positivity
    have hn0 : 0 ≤ (n : ℝ) := by positivity
    have hmn : m = n := by
      exact_mod_cast (by nlinarith : (m : ℝ) = n)
    exact hnm hmn.symm
  exact (mul_eq_zero.mp hzero).resolve_left hcoef

private theorem mode4OrdinaryLegendrePolynomial_X_mul_all (n : ℕ) :
    X * mode4OrdinaryLegendrePolynomial n =
      C ((((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial (n + 1) +
        C (((n : ℝ) / ((2 * n + 1 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial (n - 1) := by
  cases n with
  | zero =>
      norm_num [mode4OrdinaryLegendrePolynomial_zero,
        mode4OrdinaryLegendrePolynomial_one]
  | succ n =>
      convert mode4OrdinaryLegendrePolynomial_X_mul n using 1

private noncomputable def mode4OrdinaryLegendreGram
    (n m : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1,
    mode4OrdinaryLegendre n x * mode4OrdinaryLegendre m x

private theorem mode4OrdinaryLegendre_X_mul_eval (n : ℕ) (x : ℝ) :
    x * mode4OrdinaryLegendre n x =
      (((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
          mode4OrdinaryLegendre (n + 1) x +
        ((n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
          mode4OrdinaryLegendre (n - 1) x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_X_mul_all n)
  simpa [mode4OrdinaryLegendre] using h

private theorem mode4OrdinaryLegendreGram_X_left (n m : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (x * mode4OrdinaryLegendre n x) *
        mode4OrdinaryLegendre m x) =
      (((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
          mode4OrdinaryLegendreGram (n + 1) m +
        ((n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
          mode4OrdinaryLegendreGram (n - 1) m := by
  let cup : ℝ := ((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)
  let cdown : ℝ := (n : ℝ) / ((2 * n + 1 : ℕ) : ℝ)
  calc
    (∫ x in (-1 : ℝ)..1,
      (x * mode4OrdinaryLegendre n x) *
        mode4OrdinaryLegendre m x) =
        ∫ x in (-1 : ℝ)..1,
          cup * (mode4OrdinaryLegendre (n + 1) x *
              mode4OrdinaryLegendre m x) +
            cdown * (mode4OrdinaryLegendre (n - 1) x *
              mode4OrdinaryLegendre m x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      change
        (x * mode4OrdinaryLegendre n x) * mode4OrdinaryLegendre m x =
          cup * (mode4OrdinaryLegendre (n + 1) x *
              mode4OrdinaryLegendre m x) +
            cdown * (mode4OrdinaryLegendre (n - 1) x *
              mode4OrdinaryLegendre m x)
      rw [mode4OrdinaryLegendre_X_mul_eval]
      dsimp [cup, cdown]
      ring
    _ = cup * mode4OrdinaryLegendreGram (n + 1) m +
          cdown * mode4OrdinaryLegendreGram (n - 1) m := by
      rw [intervalIntegral.integral_add]
      · rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]
        rfl
      · exact
          (continuous_const.mul
            ((mode4OrdinaryLegendrePolynomial (n + 1)).continuous.mul
              (mode4OrdinaryLegendrePolynomial m).continuous)).intervalIntegrable
              (-1) 1
      · exact
          (continuous_const.mul
            ((mode4OrdinaryLegendrePolynomial (n - 1)).continuous.mul
              (mode4OrdinaryLegendrePolynomial m).continuous)).intervalIntegrable
              (-1) 1
    _ = _ := by rfl

private theorem mode4OrdinaryLegendreGram_norm_succ_relation (n : ℕ) :
    (((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
        mode4OrdinaryLegendreGram (n + 1) (n + 1) =
      (((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) *
        mode4OrdinaryLegendreGram n n := by
  have hupperZero : mode4OrdinaryLegendreGram (n + 2) n = 0 := by
    unfold mode4OrdinaryLegendreGram
    exact mode4OrdinaryLegendre_gram_offdiag (n + 2) n (by omega)
  have hlowerZero : mode4OrdinaryLegendreGram (n - 1) (n + 1) = 0 := by
    unfold mode4OrdinaryLegendreGram
    exact mode4OrdinaryLegendre_gram_offdiag (n - 1) (n + 1) (by omega)
  have hleft := mode4OrdinaryLegendreGram_X_left (n + 1) n
  have hright := mode4OrdinaryLegendreGram_X_left n (n + 1)
  rw [hupperZero, mul_zero, zero_add] at hleft
  rw [hlowerZero, mul_zero, add_zero] at hright
  have hcommon :
      (∫ x in (-1 : ℝ)..1,
        (x * mode4OrdinaryLegendre n x) *
          mode4OrdinaryLegendre (n + 1) x) =
        ∫ x in (-1 : ℝ)..1,
          (x * mode4OrdinaryLegendre (n + 1) x) *
            mode4OrdinaryLegendre n x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  calc
    (((n + 1 : ℕ) : ℝ) / ((2 * n + 1 : ℕ) : ℝ)) *
          mode4OrdinaryLegendreGram (n + 1) (n + 1) =
        (∫ x in (-1 : ℝ)..1,
          (x * mode4OrdinaryLegendre n x) *
            mode4OrdinaryLegendre (n + 1) x) := by
      rw [hright]
    _ = (∫ x in (-1 : ℝ)..1,
          (x * mode4OrdinaryLegendre (n + 1) x) *
            mode4OrdinaryLegendre n x) := hcommon
    _ = (((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) *
          mode4OrdinaryLegendreGram n n := by
      rw [hleft]
      push_cast
      ring

private theorem mode4OrdinaryLegendreGram_norm (n : ℕ) :
    mode4OrdinaryLegendreGram n n =
      2 / (((2 * n + 1 : ℕ) : ℝ)) := by
  induction n with
  | zero =>
      norm_num [mode4OrdinaryLegendreGram,
        mode4OrdinaryLegendre_zero]
  | succ n ih =>
      have hrel := mode4OrdinaryLegendreGram_norm_succ_relation n
      rw [ih] at hrel
      have h1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
      have h2 : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := by positivity
      have h3 : (0 : ℝ) < ((2 * n + 3 : ℕ) : ℝ) := by positivity
      push_cast at hrel ⊢
      field_simp [h1.ne', h2.ne', h3.ne'] at hrel ⊢
      nlinarith

/-- Exact Gram matrix of the even ordinary-Legendre basis on `[-1,1]`. -/
theorem mode4OrdinaryLegendre_even_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      mode4OrdinaryLegendre (2 * q) x *
        mode4OrdinaryLegendre (2 * r) x) =
      if q = r then
        2 / (((4 * q + 1 : ℕ) : ℝ))
      else 0 := by
  split_ifs with hqr
  · subst r
    have h := mode4OrdinaryLegendreGram_norm (2 * q)
    unfold mode4OrdinaryLegendreGram at h
    convert h using 1 <;> (push_cast; ring)
  · exact mode4OrdinaryLegendre_gram_offdiag
      (2 * q) (2 * r) (by omega)

private theorem mode4OrdinaryLegendre_derivative_gram_eq_eigen_mul_gram
    (n m : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
        (mode4OrdinaryLegendrePolynomial n).derivative.eval x *
        (mode4OrdinaryLegendrePolynomial m).derivative.eval x) =
      ((n : ℝ) * (n + 1)) * mode4OrdinaryLegendreGram n m := by
  let p : ℝ[X] := mode4OrdinaryLegendrePolynomial n
  let s : ℝ[X] := mode4OrdinaryLegendrePolynomial m
  let fluxPoly : ℝ[X] := (1 - X ^ 2) * p.derivative * s
  have hpODE :
      (1 - X ^ 2) * p.derivative.derivative -
          2 * X * p.derivative + C ((n : ℝ) * (n + 1)) * p = 0 := by
    simpa [p] using mode4OrdinaryLegendrePolynomial_differentialEquation n
  have hfluxDerivative :
      fluxPoly.derivative =
        (1 - X ^ 2) * p.derivative * s.derivative -
          C ((n : ℝ) * (n + 1)) * (p * s) := by
    dsimp [fluxPoly]
    simp only [Polynomial.derivative_mul, Polynomial.derivative_sub,
      Polynomial.derivative_one, Polynomial.derivative_pow]
    norm_num
    have hCtwo : (C (2 : ℝ) : ℝ[X]) = 2 := Polynomial.C_ofNat 2
    rw [hCtwo]
    norm_num at hpODE
    linear_combination hpODE * s
  have hderiv :
      deriv (fun x : ℝ => fluxPoly.eval x) =
        fun x : ℝ =>
          (1 - x ^ 2) * p.derivative.eval x * s.derivative.eval x -
            ((n : ℝ) * (n + 1)) * (p.eval x * s.eval x) := by
    funext x
    have h := fluxPoly.hasDerivAt x
    rw [hfluxDerivative] at h
    simpa using h.deriv
  have hftc := intervalIntegral.integral_deriv_eq_sub'
    (a := (-1 : ℝ)) (b := 1)
    (fun x : ℝ => fluxPoly.eval x)
    hderiv
    (fun x _ => fluxPoly.differentiableAt)
    (by
      exact
        ((((continuous_const.sub (continuous_id.pow 2)).mul
          p.derivative.continuous).mul s.derivative.continuous).sub
            (continuous_const.mul (p.continuous.mul s.continuous))).continuousOn)
  have hzero :
      (∫ x in (-1 : ℝ)..1,
        (1 - x ^ 2) * p.derivative.eval x * s.derivative.eval x -
          ((n : ℝ) * (n + 1)) * (p.eval x * s.eval x)) = 0 := by
    simpa [fluxPoly, p, s] using hftc
  rw [intervalIntegral.integral_sub,
      intervalIntegral.integral_const_mul] at hzero
  · simpa [mode4OrdinaryLegendreGram, p, s,
      mode4OrdinaryLegendre] using eq_of_sub_eq_zero hzero
  · exact
      (((continuous_const.sub (continuous_id.pow 2)).mul
        p.derivative.continuous).mul s.derivative.continuous).intervalIntegrable
          (-1) 1
  · exact
      (continuous_const.mul
        (p.continuous.mul s.continuous)).intervalIntegrable (-1) 1

/-- Exact weighted derivative Gram matrix of the even ordinary-Legendre
basis. -/
theorem mode4OrdinaryLegendre_even_derivative_gram
    (q r : ℕ) :
    (∫ x in (-1 : ℝ)..1,
      (1 - x ^ 2) *
        (mode4OrdinaryLegendrePolynomial
          (2 * q)).derivative.eval x *
        (mode4OrdinaryLegendrePolynomial
          (2 * r)).derivative.eval x) =
      if q = r then
        (((2 * q : ℕ) : ℝ) *
          (((2 * q + 1 : ℕ) : ℝ))) *
          (2 / (((4 * q + 1 : ℕ) : ℝ)))
      else 0 := by
  have h := mode4OrdinaryLegendre_derivative_gram_eq_eigen_mul_gram
    (2 * q) (2 * r)
  have hgram :
      mode4OrdinaryLegendreGram (2 * q) (2 * r) =
        if q = r then 2 / (((4 * q + 1 : ℕ) : ℝ)) else 0 := by
    unfold mode4OrdinaryLegendreGram
    exact mode4OrdinaryLegendre_even_gram q r
  rw [hgram] at h
  split_ifs with hqr
  · rw [if_pos hqr] at h
    convert h using 1 <;> (push_cast; ring)
  · rw [if_neg hqr] at h
    simpa using h

#print axioms mode4OrdinaryLegendre_even_gram
#print axioms mode4OrdinaryLegendre_even_derivative_gram

end Q3.RouteB
