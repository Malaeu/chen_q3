import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreXAction

/-!
# Multiplication by X squared in the mode-four ordinary Legendre basis

This file applies the committed `X` action twice and collects the exact three
resulting bands.  It introduces no new representation or public definition.

It does not prove a differential equation, analytic bounds, a Ferrers series,
or any PSWF provenance statement.
-/

open Polynomial

noncomputable section

/-- The exact three-band action of multiplication by `X ^ 2` on `P_(n+2)`. -/
theorem mode4OrdinaryLegendrePolynomial_X_sq_mul (n : ℕ) :
    X ^ 2 * mode4OrdinaryLegendrePolynomial (n + 2) =
      C (((n + 3 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ) *
          (((n + 4 : ℕ) : ℝ) / ((2 * n + 7 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial (n + 4) +
        C (((n + 3 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ) *
              (((n + 3 : ℕ) : ℝ) / ((2 * n + 7 : ℕ) : ℝ)) +
            ((n + 2 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ) *
              (((n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial (n + 2) +
        C (((n + 2 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ) *
          (((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial n := by
  calc
    X ^ 2 * mode4OrdinaryLegendrePolynomial (n + 2) =
        X * (X * mode4OrdinaryLegendrePolynomial (n + 2)) := by ring
    _ = X *
        (C (((n + 3 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ)) *
            mode4OrdinaryLegendrePolynomial (n + 3) +
          C (((n + 2 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ)) *
            mode4OrdinaryLegendrePolynomial (n + 1)) := by
      congr 1
      convert mode4OrdinaryLegendrePolynomial_X_mul (n + 1) using 1
    _ = C (((n + 3 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ)) *
          (X * mode4OrdinaryLegendrePolynomial (n + 3)) +
        C (((n + 2 : ℕ) : ℝ) / ((2 * n + 5 : ℕ) : ℝ)) *
          (X * mode4OrdinaryLegendrePolynomial (n + 1)) := by ring
    _ = _ := by
      rw [mode4OrdinaryLegendrePolynomial_X_mul (n + 2),
        mode4OrdinaryLegendrePolynomial_X_mul n]
      simp only [mul_add, ← mul_assoc, ← C_mul]
      rw [C_add]
      ring

/-! ## Planted three-band mutants -/

-- M-F0D-1: delete the upper band at `n = 0`.
private theorem mutant_X_sq_action_missing_upper_band_rejected :
    X ^ 2 * mode4OrdinaryLegendrePolynomial 2 ≠
      C (11 / 21 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
        C (2 / 15 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at heval
  change 1 ^ 2 * mode4OrdinaryLegendre 2 1 =
    (11 / 21 : ℝ) * mode4OrdinaryLegendre 2 1 +
      (2 / 15 : ℝ) * mode4OrdinaryLegendre 0 1 at heval
  norm_num at heval

-- M-F0D-2: delete the lower band at `n = 0`.
private theorem mutant_X_sq_action_missing_lower_band_rejected :
    X ^ 2 * mode4OrdinaryLegendrePolynomial 2 ≠
      C (12 / 35 : ℝ) * mode4OrdinaryLegendrePolynomial 4 +
        C (11 / 21 : ℝ) * mode4OrdinaryLegendrePolynomial 2 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at heval
  change 1 ^ 2 * mode4OrdinaryLegendre 2 1 =
    (12 / 35 : ℝ) * mode4OrdinaryLegendre 4 1 +
      (11 / 21 : ℝ) * mode4OrdinaryLegendre 2 1 at heval
  norm_num at heval

-- M-F0D-3: flip the sign of the diagonal band at `n = 0`.
private theorem mutant_X_sq_action_wrong_diagonal_sign_rejected :
    X ^ 2 * mode4OrdinaryLegendrePolynomial 2 ≠
      C (12 / 35 : ℝ) * mode4OrdinaryLegendrePolynomial 4 -
        C (11 / 21 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
          C (2 / 15 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add, eval_sub] at heval
  change 1 ^ 2 * mode4OrdinaryLegendre 2 1 =
    (12 / 35 : ℝ) * mode4OrdinaryLegendre 4 1 -
      (11 / 21 : ℝ) * mode4OrdinaryLegendre 2 1 +
        (2 / 15 : ℝ) * mode4OrdinaryLegendre 0 1 at heval
  norm_num at heval

-- M-F0D-4: shift the input polynomial from `P₂` to `P₁` at `n = 0`.
private theorem mutant_X_sq_action_wrong_input_index_rejected :
    X ^ 2 * mode4OrdinaryLegendrePolynomial 1 ≠
      C (12 / 35 : ℝ) * mode4OrdinaryLegendrePolynomial 4 +
        C (11 / 21 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
          C (2 / 15 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval (-1)) h
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at heval
  change (-1) ^ 2 * mode4OrdinaryLegendre 1 (-1) =
    (12 / 35 : ℝ) * mode4OrdinaryLegendre 4 (-1) +
      (11 / 21 : ℝ) * mode4OrdinaryLegendre 2 (-1) +
        (2 / 15 : ℝ) * mode4OrdinaryLegendre 0 (-1) at heval
  norm_num at heval

-- M-F0D-5: change the upper numerator `4` to `3` at `n = 0`.
private theorem mutant_X_sq_action_wrong_upper_coefficient_rejected :
    X ^ 2 * mode4OrdinaryLegendrePolynomial 2 ≠
      C (9 / 35 : ℝ) * mode4OrdinaryLegendrePolynomial 4 +
        C (11 / 21 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
          C (2 / 15 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at heval
  change 1 ^ 2 * mode4OrdinaryLegendre 2 1 =
    (9 / 35 : ℝ) * mode4OrdinaryLegendre 4 1 +
      (11 / 21 : ℝ) * mode4OrdinaryLegendre 2 1 +
        (2 / 15 : ℝ) * mode4OrdinaryLegendre 0 1 at heval
  norm_num at heval

#print axioms mode4OrdinaryLegendrePolynomial_X_sq_mul
