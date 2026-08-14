import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreAffineKernel
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Topology.Algebra.Polynomial

/-!
# Ordinary Legendre differential equation and the sharp interval bound

Mathlib supplies the shifted Legendre polynomial and its Rodrigues identity,
but no analytic bound on the unit interval.  This file proves the shifted
differential equation coefficientwise, transports it through the committed
ordinary affine convention, and uses the classical polynomial-energy
monotonicity argument to prove `|Pₙ(x)| ≤ 1` on `[-1, 1]`.  The same
energy identity gives first- and second-derivative majorants on every strict
compact subinterval.

This is an ordinary-Legendre theorem only.  It does not construct a PSWF,
identify an ordered prolate mode, or prove a Fourier eigenrelation.
-/

open Polynomial
open Nat

private theorem shifted_coeff_ode (n k : ℕ) :
    ((k + 1 : ℕ) : ℤ) ^ 2 * (shiftedLegendre n).coeff (k + 1) +
      (((n : ℤ) * (n + 1) - (k : ℤ) * (k + 1)) *
        (shiftedLegendre n).coeff k) = 0 := by
  rw [coeff_shiftedLegendre, coeff_shiftedLegendre]
  by_cases hk : k ≤ n
  · have hchoose1 :
        (k + 1) * n.choose (k + 1) = (n - k) * n.choose k := by
      simpa [mul_comm] using Nat.choose_succ_right_eq n k
    have hchoose2 :
        (k + 1) * (n + k + 1).choose n =
          (n + k + 1) * (n + k).choose n := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using
        (Nat.choose_mul_succ_eq (n + k) n).symm
    have hcastScalar :
        (n : ℤ) * (n + 1) - (k : ℤ) * (k + 1) =
          ((n - k : ℕ) : ℤ) * (n + k + 1) := by
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
      simp only [Nat.add_sub_cancel_left]
      push_cast
      ring
    rw [hcastScalar]
    have hchoose1z :
        ((k + 1 : ℕ) : ℤ) * n.choose (k + 1) =
          (n - k : ℕ) * n.choose k := by
      exact_mod_cast hchoose1
    have hchoose2z :
        ((k + 1 : ℕ) : ℤ) * (n + k + 1).choose n =
          (n + k + 1 : ℕ) * (n + k).choose n := by
      exact_mod_cast hchoose2
    have hprodz :
        ((k + 1 : ℕ) : ℤ) ^ 2 * n.choose (k + 1) *
            (n + k + 1).choose n =
          ((n - k : ℕ) : ℤ) * (n + k + 1) *
            n.choose k * (n + k).choose n := by
      calc
        _ = (((k + 1 : ℕ) : ℤ) * n.choose (k + 1)) *
            (((k + 1 : ℕ) : ℤ) *
              (n + k + 1).choose n) := by ring
        _ = (((n - k : ℕ) : ℤ) * n.choose k) *
            (((n + k + 1 : ℕ) : ℤ) *
              (n + k).choose n) := by rw [hchoose1z, hchoose2z]
        _ = _ := by push_cast; ring
    rw [show n + (k + 1) = n + k + 1 by omega]
    rw [show (-1 : ℤ) ^ (k + 1) = -((-1 : ℤ) ^ k) by
      rw [pow_succ]
      ring]
    calc
      _ = ((-1 : ℤ) ^ k) *
          (-(((k + 1 : ℕ) : ℤ) ^ 2 * n.choose (k + 1) *
              (n + k + 1).choose n) +
            (((n - k : ℕ) : ℤ) * (n + k + 1) *
              n.choose k * (n + k).choose n)) := by ring
      _ = 0 := by rw [hprodz]; ring
  · have hnk : n < k := Nat.lt_of_not_ge hk
    have hnk1 : n < k + 1 := lt_trans hnk (Nat.lt_succ_self k)
    rw [Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt hnk1]
    simp

private theorem shifted_polynomial_ode (n : ℕ) :
    X * (1 - X) * (shiftedLegendre n).derivative.derivative +
        (1 - 2 * X) * (shiftedLegendre n).derivative +
        C ((n : ℤ) * (n + 1)) * shiftedLegendre n = 0 := by
  rw [show
      X * (1 - X) * (shiftedLegendre n).derivative.derivative +
          (1 - 2 * X) * (shiftedLegendre n).derivative +
          C ((n : ℤ) * (n + 1)) * shiftedLegendre n =
        derivative
            ((X - X ^ 2) * (shiftedLegendre n).derivative) +
          C ((n : ℤ) * (n + 1)) * shiftedLegendre n by
      simp [derivative_mul]
      ring]
  ext k
  rw [coeff_add, coeff_derivative, coeff_C_mul]
  rw [show (X - X ^ 2) * (shiftedLegendre n).derivative =
      X * (shiftedLegendre n).derivative -
        X ^ 2 * (shiftedLegendre n).derivative by ring]
  cases k with
  | zero =>
      have h := shifted_coeff_ode n 0
      simp [coeff_derivative, coeff_X_mul, coeff_X_pow_mul',
        coeff_shiftedLegendre] at h ⊢
  | succ k =>
      have h := shifted_coeff_ode n (k + 1)
      simp [coeff_derivative, coeff_X_mul, coeff_X_pow_mul',
        Nat.add_comm, Nat.add_left_comm] at h ⊢
      ring_nf at h ⊢
      exact h

private theorem shifted_polynomial_real_ode (n : ℕ) :
    let p := (shiftedLegendre n).map (Int.castRingHom ℝ)
    X * (1 - X) * p.derivative.derivative +
        (1 - 2 * X) * p.derivative +
        C ((n : ℝ) * (n + 1)) * p = 0 := by
  dsimp
  have h := congrArg
    (fun p : ℤ[X] => p.map (Int.castRingHom ℝ))
    (shifted_polynomial_ode n)
  simpa using h

/-- The exact ordinary Legendre differential equation in polynomial form. -/
theorem mode4OrdinaryLegendrePolynomial_differentialEquation (n : ℕ) :
    (1 - X ^ 2) *
          (mode4OrdinaryLegendrePolynomial n).derivative.derivative -
        2 * X * (mode4OrdinaryLegendrePolynomial n).derivative +
        C ((n : ℝ) * (n + 1)) *
          mode4OrdinaryLegendrePolynomial n = 0 := by
  let L : ℝ[X] := (shiftedLegendre n).map (Int.castRingHom ℝ)
  let A : ℝ[X] := mode4OrdinaryLegendreAffine
  have hshift :
      X * (1 - X) * L.derivative.derivative +
          (1 - 2 * X) * L.derivative +
          C ((n : ℝ) * (n + 1)) * L = 0 := by
    simpa [L] using shifted_polynomial_real_ode n
  have hcomp := congrArg (fun p : ℝ[X] => p.comp A) hshift
  simp only [Polynomial.add_comp, Polynomial.sub_comp,
    Polynomial.mul_comp, Polynomial.one_comp, Polynomial.X_comp,
    Polynomial.C_comp, Polynomial.ofNat_comp,
    Polynomial.zero_comp] at hcomp
  norm_num at hcomp
  have hAderiv : A.derivative = C (-1 / 2 : ℝ) := by
    norm_num [A, mode4OrdinaryLegendreAffine]
  have hAone : 1 - 2 * A = X := by
    ext x
    simp [A, mode4OrdinaryLegendreAffine]
  have hAprod : A * (1 - A) = C (1 / 4 : ℝ) * (1 - X ^ 2) := by
    have h2A : 2 * A = 1 - X := by
      calc
        2 * A = 1 - (1 - 2 * A) := by ring
        _ = 1 - X := by rw [hAone]
    have h2oneA : 2 * (1 - A) = 1 + X := by
      calc
        2 * (1 - A) = 2 - 2 * A := by ring
        _ = 2 - (1 - X) := by rw [h2A]
        _ = 1 + X := by ring
    have h4quarter : (4 : ℝ[X]) * C (1 / 4 : ℝ) = 1 := by
      change C (4 : ℝ) * C (1 / 4 : ℝ) = C 1
      rw [← Polynomial.C_mul]
      norm_num
    apply mul_left_cancel₀ (a := (4 : ℝ[X])) (by norm_num)
    calc
      4 * (A * (1 - A)) = (2 * A) * (2 * (1 - A)) := by ring
      _ = (1 - X) * (1 + X) := by rw [h2A, h2oneA]
      _ = 1 - X ^ 2 := by ring
      _ = 4 * (C (1 / 4 : ℝ) * (1 - X ^ 2)) := by
        rw [← mul_assoc, h4quarter, one_mul]
  rw [hAone, hAprod] at hcomp
  rw [mode4OrdinaryLegendrePolynomial]
  change
    (1 - X ^ 2) * (L.comp A).derivative.derivative -
        2 * X * (L.comp A).derivative +
        C ((n : ℝ) * (n + 1)) * (L.comp A) = 0
  rw [derivative_comp]
  rw [derivative_mul, derivative_comp]
  rw [hAderiv]
  simp only [derivative_C, zero_mul, zero_add, Polynomial.C_mul]
  have hhalfSq : C (1 / 2 : ℝ) ^ 2 = C (1 / 4 : ℝ) := by
    rw [pow_two, ← Polynomial.C_mul]
    norm_num
  have hnegHalfSq : C (-1 / 2 : ℝ) ^ 2 = C (1 / 4 : ℝ) := by
    rw [pow_two, ← Polynomial.C_mul]
    norm_num
  have hscalarC :
      C (n : ℝ) * C ((n : ℝ) + 1) =
        C ((n : ℝ) * (n + 1)) := by
    rw [← Polynomial.C_mul]
  have hscalarNorm :
      C (n : ℝ) * C (1 + (n : ℝ)) =
        C ((n : ℝ) + (n : ℝ) ^ 2) := by
    rw [← Polynomial.C_mul]
    congr 1
    ring
  calc
    _ = C (1 / 4 : ℝ) * (1 - X ^ 2) *
            (L.derivative.derivative.comp A) +
          X * (L.derivative.comp A) +
          C ((n : ℝ) * (n + 1)) * (L.comp A) := by
      ring_nf
      rw [hnegHalfSq, hscalarNorm]
      have hnegHalf : C (-1 / 2 : ℝ) = -C (1 / 2 : ℝ) := by
        rw [← Polynomial.C_neg]
        congr 1
        ring
      rw [hnegHalf]
      ring_nf
      have hhalfTwo : C (1 / 2 : ℝ) * (2 : ℝ[X]) = 1 := by
        change C (1 / 2 : ℝ) * C (2 : ℝ) = C 1
        rw [← Polynomial.C_mul]
        norm_num
      have hterm :
          X * C (1 / 2 : ℝ) * (L.derivative.comp A) * 2 =
            X * (L.derivative.comp A) := by
        calc
          _ = X * (C (1 / 2 : ℝ) * 2) *
              (L.derivative.comp A) := by ring
          _ = X * (L.derivative.comp A) := by rw [hhalfTwo]; ring
      rw [hterm]
    _ = 0 := by
      simpa [← Polynomial.C_mul] using hcomp

/-- Pointwise form of the ordinary Legendre differential equation. -/
theorem mode4OrdinaryLegendre_differentialEquation
    (n : ℕ) (x : ℝ) :
    (1 - x ^ 2) *
          (mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x -
        2 * x *
          (mode4OrdinaryLegendrePolynomial n).derivative.eval x +
        ((n : ℝ) * (n + 1)) * mode4OrdinaryLegendre n x = 0 := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_differentialEquation n)
  simpa [mode4OrdinaryLegendre] using h

/-- The energy whose derivative is `2x(Pₙ'(x))²`. -/
noncomputable def mode4OrdinaryLegendreEnergyPolynomial (n : ℕ) : ℝ[X] :=
  let p := mode4OrdinaryLegendrePolynomial n
  (1 - X ^ 2) * p.derivative ^ 2 +
    C ((n : ℝ) * (n + 1)) * p ^ 2

theorem mode4OrdinaryLegendreEnergyPolynomial_derivative (n : ℕ) :
    (mode4OrdinaryLegendreEnergyPolynomial n).derivative =
      2 * X * (mode4OrdinaryLegendrePolynomial n).derivative ^ 2 := by
  let p := mode4OrdinaryLegendrePolynomial n
  have hode :
      (1 - X ^ 2) * p.derivative.derivative -
          2 * X * p.derivative +
          C ((n : ℝ) * (n + 1)) * p = 0 := by
    simpa [p] using mode4OrdinaryLegendrePolynomial_differentialEquation n
  unfold mode4OrdinaryLegendreEnergyPolynomial
  dsimp only
  calc
    derivative
          ((1 - X ^ 2) * p.derivative ^ 2 +
            C ((n : ℝ) * (n + 1)) * p ^ 2) =
        2 * p.derivative *
          ((1 - X ^ 2) * p.derivative.derivative -
            X * p.derivative +
            C ((n : ℝ) * (n + 1)) * p) := by
      have hCtwo : C (2 : ℝ) = (2 : ℝ[X]) := by
        exact Polynomial.C_eq_natCast 2
      simp [derivative_add, derivative_mul, derivative_pow]
      rw [hCtwo]
      ring
    _ = 2 * p.derivative *
          (X * p.derivative +
            ((1 - X ^ 2) * p.derivative.derivative -
              2 * X * p.derivative +
              C ((n : ℝ) * (n + 1)) * p)) := by ring
    _ = 2 * X * p.derivative ^ 2 := by rw [hode]; ring

theorem mode4OrdinaryLegendreEnergyPolynomial_at_one (n : ℕ) :
    (mode4OrdinaryLegendreEnergyPolynomial n).eval 1 =
      (n : ℝ) * (n + 1) := by
  have hp1 : (mode4OrdinaryLegendrePolynomial n).eval 1 = 1 := by
    simpa [mode4OrdinaryLegendre] using mode4OrdinaryLegendre_at_one n
  simp [mode4OrdinaryLegendreEnergyPolynomial, hp1]

theorem mode4OrdinaryLegendreEnergyPolynomial_monotoneOn_Icc (n : ℕ) :
    MonotoneOn
      (fun x : ℝ => (mode4OrdinaryLegendreEnergyPolynomial n).eval x)
      (Set.Icc 0 1) := by
  let E := mode4OrdinaryLegendreEnergyPolynomial n
  refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
    E.continuous.continuousOn E.differentiable.differentiableOn ?_
  intro x hx
  have hx0 : 0 ≤ x := by
    rw [interior_Icc] at hx
    exact hx.1.le
  rw [E.deriv]
  rw [show E.derivative =
      2 * X * (mode4OrdinaryLegendrePolynomial n).derivative ^ 2 by
    simpa [E] using mode4OrdinaryLegendreEnergyPolynomial_derivative n]
  simp only [eval_mul, eval_ofNat, eval_X, eval_pow]
  positivity

theorem mode4OrdinaryLegendre_abs_le_one_of_nonneg
    (n : ℕ) (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |mode4OrdinaryLegendre n x| ≤ 1 := by
  cases n with
  | zero => simp
  | succ n =>
      let p := mode4OrdinaryLegendrePolynomial (n + 1)
      let N : ℝ := (n + 1 : ℕ) * (n + 2 : ℕ)
      have hNpos : 0 < N := by
        dsimp [N]
        positivity
      have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx1⟩
      have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
      have hmono := mode4OrdinaryLegendreEnergyPolynomial_monotoneOn_Icc (n + 1)
        hxmem hone hx1
      have hEone := mode4OrdinaryLegendreEnergyPolynomial_at_one (n + 1)
      have hfirst :
          0 ≤ (1 - x ^ 2) * (p.derivative.eval x) ^ 2 := by
        have hxSq : x ^ 2 ≤ 1 := by nlinarith
        exact mul_nonneg (sub_nonneg.mpr hxSq) (sq_nonneg _)
      have hEexpand :
          (mode4OrdinaryLegendreEnergyPolynomial (n + 1)).eval x =
            (1 - x ^ 2) * (p.derivative.eval x) ^ 2 +
              N * (p.eval x) ^ 2 := by
        simp only [mode4OrdinaryLegendreEnergyPolynomial, eval_add, eval_mul, eval_sub,
          eval_one, eval_pow, eval_X, eval_C]
        dsimp [p, N]
        push_cast
        ring
      have hNpSq :
          N * (p.eval x) ^ 2 ≤
            (mode4OrdinaryLegendreEnergyPolynomial (n + 1)).eval x := by
        rw [hEexpand]
        nlinarith
      have hEoneN :
          (mode4OrdinaryLegendreEnergyPolynomial (n + 1)).eval 1 = N := by
        rw [hEone]
        dsimp [N]
        push_cast
        ring
      have hpSq : (p.eval x) ^ 2 ≤ 1 := by
        change
          (mode4OrdinaryLegendreEnergyPolynomial (n + 1)).eval x ≤
            (mode4OrdinaryLegendreEnergyPolynomial (n + 1)).eval 1 at hmono
        rw [hEoneN] at hmono
        nlinarith
      change |p.eval x| ≤ 1
      nlinarith [sq_abs (p.eval x), abs_nonneg (p.eval x)]

/-- The sharp ordinary Legendre bound on the closed unit interval. -/
theorem mode4OrdinaryLegendre_abs_le_one
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |mode4OrdinaryLegendre n x| ≤ 1 := by
  by_cases hx0 : 0 ≤ x
  · exact mode4OrdinaryLegendre_abs_le_one_of_nonneg n x hx0 hx.2
  · have hneg0 : 0 ≤ -x := by linarith
    have hneg1 : -x ≤ 1 := by linarith [hx.1]
    have hbound := mode4OrdinaryLegendre_abs_le_one_of_nonneg n (-x) hneg0 hneg1
    have hpar := mode4OrdinaryLegendre_neg n (-x)
    simp only [neg_neg] at hpar
    calc
      |mode4OrdinaryLegendre n x| =
          |(-1 : ℝ) ^ n * mode4OrdinaryLegendre n (-x)| := by rw [hpar]
      _ = |mode4OrdinaryLegendre n (-x)| := by
        rw [abs_mul, abs_pow]
        norm_num
      _ ≤ 1 := hbound

/-- The first derivative has the opposite parity to the Legendre polynomial. -/
theorem mode4OrdinaryLegendrePolynomial_derivative_eval_neg
    (n : ℕ) (x : ℝ) :
    (mode4OrdinaryLegendrePolynomial n).derivative.eval (-x) =
      (-1 : ℝ) ^ (n + 1) *
        (mode4OrdinaryLegendrePolynomial n).derivative.eval x := by
  let p := mode4OrdinaryLegendrePolynomial n
  have hfun :
      (fun y : ℝ => p.eval (-y)) =
        fun y : ℝ => (-1 : ℝ) ^ n * p.eval y := by
    funext y
    exact mode4OrdinaryLegendre_neg n y
  have hleft : HasDerivAt
      (fun y : ℝ => p.eval (-y))
      (p.derivative.eval (-x) * (-1)) x :=
    (p.hasDerivAt (-x)).comp x (hasDerivAt_neg x)
  have hright : HasDerivAt
      (fun y : ℝ => (-1 : ℝ) ^ n * p.eval y)
      ((-1 : ℝ) ^ n * p.derivative.eval x) x :=
    (p.hasDerivAt x).const_mul ((-1 : ℝ) ^ n)
  rw [hfun] at hleft
  have heval := hleft.unique hright
  calc
    p.derivative.eval (-x) =
        -((-1 : ℝ) ^ n * p.derivative.eval x) := by linarith
    _ = (-1 : ℝ) ^ (n + 1) * p.derivative.eval x := by
      rw [pow_succ]
      ring

/-- The Legendre energy is even. -/
theorem mode4OrdinaryLegendreEnergyPolynomial_eval_neg
    (n : ℕ) (x : ℝ) :
    (mode4OrdinaryLegendreEnergyPolynomial n).eval (-x) =
      (mode4OrdinaryLegendreEnergyPolynomial n).eval x := by
  have hp := mode4OrdinaryLegendre_neg n x
  have hdp := mode4OrdinaryLegendrePolynomial_derivative_eval_neg n x
  simp only [mode4OrdinaryLegendreEnergyPolynomial, eval_add, eval_mul,
    eval_sub, eval_one, eval_pow, eval_X, eval_C]
  change
    (1 - (-x) ^ 2) *
          (mode4OrdinaryLegendrePolynomial n).derivative.eval (-x) ^ 2 +
        ((n : ℝ) * (n + 1)) * mode4OrdinaryLegendre n (-x) ^ 2 =
      (1 - x ^ 2) *
          (mode4OrdinaryLegendrePolynomial n).derivative.eval x ^ 2 +
        ((n : ℝ) * (n + 1)) * mode4OrdinaryLegendre n x ^ 2
  rw [hp, hdp]
  have hphase : ((-1 : ℝ) ^ n) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  have hphaseSucc : ((-1 : ℝ) ^ (n + 1)) ^ 2 = 1 := by
    rw [← pow_mul]
    simp
  rw [mul_pow, mul_pow, hphase, hphaseSucc]
  ring

/-- The energy is bounded by its endpoint value throughout the unit interval. -/
theorem mode4OrdinaryLegendreEnergyPolynomial_eval_le_endpoint
    (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    (mode4OrdinaryLegendreEnergyPolynomial n).eval x ≤
      (n : ℝ) * (n + 1) := by
  have hone : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  by_cases hx0 : 0 ≤ x
  · have hxmem : x ∈ Set.Icc (0 : ℝ) 1 := ⟨hx0, hx.2⟩
    have hmono := mode4OrdinaryLegendreEnergyPolynomial_monotoneOn_Icc n
      hxmem hone hx.2
    change
      (mode4OrdinaryLegendreEnergyPolynomial n).eval x ≤
        (mode4OrdinaryLegendreEnergyPolynomial n).eval 1 at hmono
    rw [mode4OrdinaryLegendreEnergyPolynomial_at_one n] at hmono
    exact hmono
  · have hnegmem : -x ∈ Set.Icc (0 : ℝ) 1 := by
      constructor <;> linarith [hx.1]
    have hnegLe : -x ≤ (1 : ℝ) := hnegmem.2
    have hmono := mode4OrdinaryLegendreEnergyPolynomial_monotoneOn_Icc n
      hnegmem hone hnegLe
    change
      (mode4OrdinaryLegendreEnergyPolynomial n).eval (-x) ≤
        (mode4OrdinaryLegendreEnergyPolynomial n).eval 1 at hmono
    rw [mode4OrdinaryLegendreEnergyPolynomial_at_one n] at hmono
    rw [mode4OrdinaryLegendreEnergyPolynomial_eval_neg n x] at hmono
    exact hmono

/-- On every strict compact subinterval, the first derivative has a uniform
quadratic-in-degree bound.  This is the local majorant used for termwise
differentiation of the Ferrers series. -/
theorem mode4OrdinaryLegendrePolynomial_derivative_abs_le
    (n : ℕ) (r x : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : x ∈ Set.Icc (-r) r) :
    |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| ≤
      ((n : ℝ) * (n + 1)) / (1 - r ^ 2) + 1 := by
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hxUnit : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have henergy := mode4OrdinaryLegendreEnergyPolynomial_eval_le_endpoint
    n x hxUnit
  have hNsq : 0 ≤ ((n : ℝ) * (n + 1)) *
      (mode4OrdinaryLegendre n x) ^ 2 := by positivity
  have hderivEnergy :
      (1 - x ^ 2) *
          ((mode4OrdinaryLegendrePolynomial n).derivative.eval x) ^ 2 ≤
        (mode4OrdinaryLegendreEnergyPolynomial n).eval x := by
    simp only [mode4OrdinaryLegendreEnergyPolynomial, eval_add, eval_mul,
      eval_sub, eval_one, eval_pow, eval_X, eval_C]
    change
      (1 - x ^ 2) *
            ((mode4OrdinaryLegendrePolynomial n).derivative.eval x) ^ 2 ≤
        (1 - x ^ 2) *
            ((mode4OrdinaryLegendrePolynomial n).derivative.eval x) ^ 2 +
          ((n : ℝ) * (n + 1)) * (mode4OrdinaryLegendre n x) ^ 2
    linarith
  have hxSq : x ^ 2 ≤ r ^ 2 := by
    have hsum : 0 ≤ r + x := by linarith [hx.1]
    have hdiff : 0 ≤ r - x := by linarith [hx.2]
    nlinarith [mul_nonneg hsum hdiff]
  have hsquare :
      (1 - r ^ 2) *
          ((mode4OrdinaryLegendrePolynomial n).derivative.eval x) ^ 2 ≤
        (n : ℝ) * (n + 1) := by
    have hnonneg := sq_nonneg
      ((mode4OrdinaryLegendrePolynomial n).derivative.eval x)
    nlinarith
  have hquotNonneg :
      0 ≤ ((n : ℝ) * (n + 1)) / (1 - r ^ 2) :=
    div_nonneg (by positivity) hd.le
  have hsquareQuot :
      ((mode4OrdinaryLegendrePolynomial n).derivative.eval x) ^ 2 ≤
        ((n : ℝ) * (n + 1)) / (1 - r ^ 2) := by
    apply (le_div_iff₀ hd).2
    simpa only [mul_comm] using hsquare
  calc
    |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| ≤
        Real.sqrt (((n : ℝ) * (n + 1)) / (1 - r ^ 2)) :=
      Real.abs_le_sqrt hsquareQuot
    _ ≤ ((n : ℝ) * (n + 1)) / (1 - r ^ 2) + 1 := by
      rw [Real.sqrt_le_iff]
      constructor
      · linarith
      · nlinarith [sq_nonneg
          (((n : ℝ) * (n + 1)) / (1 - r ^ 2))]

/-- On every strict compact subinterval, the second derivative has a uniform
quadratic-in-degree bound. -/
theorem mode4OrdinaryLegendrePolynomial_secondDerivative_abs_le
    (n : ℕ) (r x : ℝ)
    (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hx : x ∈ Set.Icc (-r) r) :
    |(mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x| ≤
      (2 * r *
          (((n : ℝ) * (n + 1)) / (1 - r ^ 2) + 1) +
        (n : ℝ) * (n + 1)) / (1 - r ^ 2) := by
  let N : ℝ := (n : ℝ) * (n + 1)
  let B : ℝ := N / (1 - r ^ 2) + 1
  have hd : 0 < 1 - r ^ 2 := by nlinarith
  have hxUnit : x ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor <;> linarith [hx.1, hx.2]
  have hxAbs : |x| ≤ r := (abs_le).2 hx
  have hP := mode4OrdinaryLegendre_abs_le_one n x hxUnit
  have hP' := mode4OrdinaryLegendrePolynomial_derivative_abs_le
    n r x hr0 hr1 hx
  change
    |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| ≤ B at hP'
  have hN0 : 0 ≤ N := by
    dsimp [N]
    positivity
  have hfactor : 0 < 1 - x ^ 2 := by
    have hxSq : x ^ 2 ≤ r ^ 2 := by
      have hsum : 0 ≤ r + x := by linarith [hx.1]
      have hdiff : 0 ≤ r - x := by linarith [hx.2]
      nlinarith [mul_nonneg hsum hdiff]
    linarith
  have hode := mode4OrdinaryLegendre_differentialEquation n x
  have heq :
      (1 - x ^ 2) *
          (mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x =
        2 * x * (mode4OrdinaryLegendrePolynomial n).derivative.eval x -
          N * mode4OrdinaryLegendre n x := by
    dsimp [N]
    linarith
  have habsEq := congrArg abs heq
  rw [abs_mul, abs_of_pos hfactor] at habsEq
  have hrhs :
      |2 * x * (mode4OrdinaryLegendrePolynomial n).derivative.eval x -
          N * mode4OrdinaryLegendre n x| ≤
        2 * r * B + N := by
    calc
      _ ≤
          |2 * x * (mode4OrdinaryLegendrePolynomial n).derivative.eval x| +
            |N * mode4OrdinaryLegendre n x| := abs_sub _ _
      _ = 2 * |x| *
            |(mode4OrdinaryLegendrePolynomial n).derivative.eval x| +
          N * |mode4OrdinaryLegendre n x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hN0]
        norm_num
      _ ≤ 2 * r * B + N * 1 := by
        gcongr
      _ = 2 * r * B + N := by ring
  have hscaled :
      (1 - r ^ 2) *
          |(mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x| ≤
        2 * r * B + N := by
    have hfactorOrder : 1 - r ^ 2 ≤ 1 - x ^ 2 := by
      have hsum : 0 ≤ r + x := by linarith [hx.1]
      have hdiff : 0 ≤ r - x := by linarith [hx.2]
      nlinarith [mul_nonneg hsum hdiff]
    calc
      _ ≤ (1 - x ^ 2) *
          |(mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x| :=
        mul_le_mul_of_nonneg_right hfactorOrder (abs_nonneg _)
      _ = |2 * x *
            (mode4OrdinaryLegendrePolynomial n).derivative.eval x -
          N * mode4OrdinaryLegendre n x| := habsEq
      _ ≤ 2 * r * B + N := hrhs
  change
    |(mode4OrdinaryLegendrePolynomial n).derivative.derivative.eval x| ≤
      (2 * r * B + N) / (1 - r ^ 2)
  apply (le_div_iff₀ hd).2
  simpa only [mul_comm] using hscaled
