import Q3.Proofs.RouteB.D0Mode4DLMFEvenFiniteMatrix

/-!
# Even Legendre to Hermitian coordinate scale

The literal DLMF even recurrence is diagonally similar to the forward
Hermitian Jacobi matrix.  This file identifies the square of that positive
recursive similarity scale with the exact even-Legendre norm weight.

Knowledge preflight before the write:

`./orchestrator/kb.py ask "mode4DLMFEvenSimilarityScale square legendre weight 4 q plus 1 Hermitian coordinate scale"`

returned no hits.  Retrieval output is only a discovery receipt, not proof
evidence.

This coordinate identity does not prove a differential quadratic-form
identity, form closure, ground-state minimization, a zero count, Goal 058 G3,
Route B promotion, or RH.
-/

noncomputable section

/-- The DLMF-to-Hermitian similarity scale has exactly the square of the
standard even-Legendre normalization weight. -/
theorem mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    mode4DLMFEvenSimilarityScale G q ^ 2 =
      4 * (q : ℝ) + 1 := by
  induction q with
  | zero =>
      simp [mode4DLMFEvenSimilarityScale]
  | succ q ih =>
      rw [mode4DLMFEvenSimilarityScale, div_pow, mul_pow,
        mode4JacobiSymmetricOff_sq G q hG, ih]
      have hd1 : (0 : ℝ) < 4 * (q : ℝ) + 1 := by positivity
      have hd3 : (0 : ℝ) < 4 * (q : ℝ) + 3 := by positivity
      have hd5 : (0 : ℝ) < 4 * (q : ℝ) + 5 := by positivity
      have hlower :
          mode4JacobiLower G (q + 1) =
            G * (2 * (q : ℝ) + 1) * (2 * (q : ℝ) + 2) /
              ((4 * (q : ℝ) + 1) * (4 * (q : ℝ) + 3)) := by
        norm_num [mode4JacobiLower, mode4JacobiIndex]
        ring
      have hupper :
          mode4JacobiUpper G q =
            G * (2 * (q : ℝ) + 1) * (2 * (q : ℝ) + 2) /
              ((4 * (q : ℝ) + 3) * (4 * (q : ℝ) + 5)) := by
        norm_num [mode4JacobiUpper, mode4JacobiIndex]
        ring
      have hratio :
          (4 * (q : ℝ) + 1) * mode4JacobiLower G (q + 1) =
            (4 * ((q + 1 : ℕ) : ℝ) + 1) * mode4JacobiUpper G q := by
        rw [hlower, hupper]
        push_cast
        field_simp [ne_of_gt hd1, ne_of_gt hd3, ne_of_gt hd5]
        ring
      field_simp [(mode4JacobiUpper_pos G q hG).ne']
      nlinarith

#print axioms mode4DLMFEvenSimilarityScale_sq_eq_legendreWeight
