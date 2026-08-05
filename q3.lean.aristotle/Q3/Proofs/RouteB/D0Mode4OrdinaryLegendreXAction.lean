import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreRecurrence

/-!
# Multiplication by X in the mode-four ordinary Legendre basis

This file derives only the exact two-band `X`-multiplication action from the
committed three-term recurrence.  It introduces no new representation and no
public definition.

It does not prove an `X ^ 2` action, a differential equation, analytic bounds,
a Ferrers series, or any PSWF provenance statement.
-/

open Polynomial

noncomputable section

/-- Multiplication by `X` in the ordinary Legendre basis, indexed so that the
input is `P_(n+1)` and no predecessor side condition is required. -/
theorem mode4OrdinaryLegendrePolynomial_X_mul (n : ℕ) :
    X * mode4OrdinaryLegendrePolynomial (n + 1) =
      C ((((n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial (n + 2) +
        C ((((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ))) *
          mode4OrdinaryLegendrePolynomial n := by
  have h := mode4OrdinaryLegendrePolynomial_three_term_succ n
  have hn : (((2 * n + 3 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hcoef1 :
      ((2 * n + 3 : ℕ) : ℝ) *
          (((n + 2 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) =
        ((n + 2 : ℕ) : ℝ) := by
    exact mul_div_cancel₀ _ hn
  have hcoef2 :
      ((2 * n + 3 : ℕ) : ℝ) *
          (((n + 1 : ℕ) : ℝ) / ((2 * n + 3 : ℕ) : ℝ)) =
        ((n + 1 : ℕ) : ℝ) := by
    exact mul_div_cancel₀ _ hn
  have hscaled :
      C ((2 * n + 3 : ℕ) : ℝ) * X *
          mode4OrdinaryLegendrePolynomial (n + 1) =
        C ((n + 2 : ℕ) : ℝ) *
            mode4OrdinaryLegendrePolynomial (n + 2) +
          C ((n + 1 : ℕ) : ℝ) *
            mode4OrdinaryLegendrePolynomial n := by
    rw [h]
    ring
  apply mul_left_cancel₀ (a := C ((2 * n + 3 : ℕ) : ℝ))
  · exact C_ne_zero.mpr hn
  rw [mul_add]
  simp only [← mul_assoc, ← C_mul]
  rw [hcoef1, hcoef2]
  exact hscaled

/-! ## Planted finite-action mutants -/

private theorem mode4OrdinaryLegendre_two_eval_zero :
    mode4OrdinaryLegendre 2 0 = -(1 / 2 : ℝ) := by
  have h := congrArg (fun p : ℝ[X] => p.eval 0)
    (mode4OrdinaryLegendrePolynomial_three_term_succ 0)
  simp only [eval_mul, eval_C, eval_X, eval_sub] at h
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at h
  change 2 * mode4OrdinaryLegendre 2 0 = -1 at h
  linarith

-- M-F0C-1: replace the denominator `3` by `1` at `n = 0`.
private theorem mutant_X_action_wrong_denominator_rejected :
    X * mode4OrdinaryLegendrePolynomial 1 ≠
      C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
        C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_add] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change mode4OrdinaryLegendre 2 1 = 0 at heval
  norm_num at heval

-- M-F0C-2: delete the lower-band term at `n = 0`.
private theorem mutant_X_action_missing_lower_term_rejected :
    X * mode4OrdinaryLegendrePolynomial 1 ≠
      C (2 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 2 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_one] at heval
  change 1 = (2 / 3 : ℝ) * mode4OrdinaryLegendre 2 1 at heval
  norm_num at heval

-- M-F0C-3: subtract rather than add the lower-band term at `n = 0`.
private theorem mutant_X_action_wrong_lower_sign_rejected :
    X * mode4OrdinaryLegendrePolynomial 1 ≠
      C (2 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 2 -
        C (1 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_sub] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change 1 = (2 / 3 : ℝ) * mode4OrdinaryLegendre 2 1 - 1 / 3 at heval
  norm_num at heval

-- M-F0C-4: shift the input polynomial from `P₁` to `P₀` at `n = 0`.
private theorem mutant_X_action_wrong_input_index_rejected :
    X * mode4OrdinaryLegendrePolynomial 0 ≠
      C (2 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
        C (1 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval (-1)) h
  simp only [eval_mul, eval_C, eval_X, eval_add] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero] at heval
  change -1 =
    (2 / 3 : ℝ) * mode4OrdinaryLegendre 2 (-1) + 1 / 3 at heval
  norm_num at heval

-- M-F0C-5: swap the upper- and lower-band coefficients at `n = 0`.
private theorem mutant_X_action_swapped_coefficients_rejected :
    X * mode4OrdinaryLegendrePolynomial 1 ≠
      C (1 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 2 +
        C (2 / 3 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 0) h
  simp only [eval_mul, eval_C, eval_X, eval_add] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change 0 = (1 / 3 : ℝ) * mode4OrdinaryLegendre 2 0 + 2 / 3 at heval
  rw [mode4OrdinaryLegendre_two_eval_zero] at heval
  norm_num at heval

#print axioms mode4OrdinaryLegendrePolynomial_X_mul
