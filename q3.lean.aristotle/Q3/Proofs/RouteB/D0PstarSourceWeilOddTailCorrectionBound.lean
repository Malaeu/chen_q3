import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailGraphOperator

set_option linter.mathlibStandardSet false

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Source-Weil odd-tail inverse-weighted correction bound

This file proves the bounded C1 leaf selected by the joint Goal 058 G1/G3
source-wall review.  It combines the literal source-Weil graph coercivity with
the actual inverse equation for the outer block and Cauchy--Schwarz.  No finite
section, scalar inverse surrogate, corrected-head sign, even-sector floor, or
cofinal-family promotion enters the proof.

Knowledge preflight before the write:

`./orchestrator/kb.py ask "sourceWeilOddTailInverseWeightedCorrection quadratic form residual norm correction bound min mu one"`

returned no hits.  Retrieval output is only a discovery receipt, not proof
evidence.
-/

set_option maxHeartbeats 800000 in
/-- The actual inverse-weighted odd-tail correction is controlled by twice the
residual norm squared, with the literal graph coercivity factor `min mu 1`.

This is only a correction budget.  It does not prove positivity of the
corrected finite head, control the even part of the full complex complement,
or construct a cofinal source complement floor. -/
theorem sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le
    {Head : Type*}
    [NormedAddCommGroup Head]
    [InnerProductSpace ℂ Head]
    [CompleteSpace Head]
    (i : PairIndex)
    (R : ℕ)
    (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (residual : Head →L[ℂ] SourceWeilGraphOddTailCarrier i R)
    (x : Head) :
    min mu 1 *
        (inner ℂ
          (oddTailInverseWeightedCorrection
            (sourceWeilOddTailInverseWeightedData
              i R mu hcoercive residual) x)
          x).re ≤
      2 * ‖residual x‖ ^ 2 := by
  let D := sourceWeilOddTailInverseWeightedData
    i R mu hcoercive residual
  let y := D.outerBlock.inverse (D.residual x)
  have hy : D.outerBlock y = D.residual x :=
    outerBlock_apply_inverse_residual D x
  have hy_source :
      sourceWeilShiftedOddTailOperator i R y = residual x := by
    simpa [D] using hy
  have hcorr :
      (inner ℂ (oddTailInverseWeightedCorrection D x) x).re =
        (inner ℂ y (D.residual x)).re := by
    exact congrArg Complex.re (inner_oddTailInverseWeightedCorrection D x x)
  have hcorr_target :
      (inner ℂ
        (oddTailInverseWeightedCorrection
          (sourceWeilOddTailInverseWeightedData
            i R mu hcoercive residual) x)
        x).re =
        (inner ℂ y (residual x)).re := by
    simpa only [D] using hcorr
  have hgraph :=
    sourceWeilShiftedOddTailOperator_graph_lower i R mu hcoercive y
  have hgraph' :
      (min mu 1 / 2) * ‖y‖ ^ 2 ≤
        (inner ℂ y (D.residual x)).re := by
    rw [hy_source] at hgraph
    calc
      (min mu 1 / 2) * ‖y‖ ^ 2 ≤
          (inner ℂ (residual x) y).re := hgraph
      _ = (inner ℂ y (residual x)).re :=
        inner_re_symm (𝕜 := ℂ)
          (E := SourceWeilGraphOddTailCarrier i R) _ _
      _ = (inner ℂ y (D.residual x)).re := by rfl
  have hupper :
      (inner ℂ y (D.residual x)).re ≤ ‖y‖ * ‖D.residual x‖ := by
    exact re_inner_le_norm (𝕜 := ℂ) y (D.residual x)
  have hmu : 0 < min mu 1 := lt_min hcoercive.1 (by norm_num)
  by_cases hyzero : y = 0
  · rw [hcorr_target]
    simp only [hyzero, inner_zero_left, zero_re, mul_zero]
    positivity
  · have hynorm : 0 < ‖y‖ := norm_pos_iff.mpr hyzero
    have hresnorm : 0 ≤ ‖D.residual x‖ := norm_nonneg _
    have hybound : min mu 1 * ‖y‖ ≤ 2 * ‖D.residual x‖ := by
      nlinarith
    have hupper_source :
        (inner ℂ y (residual x)).re ≤ ‖y‖ * ‖residual x‖ := by
      simpa only [D] using hupper
    have hybound_source : min mu 1 * ‖y‖ ≤ 2 * ‖residual x‖ := by
      simpa only [D] using hybound
    rw [hcorr_target]
    nlinarith

#print axioms sourceWeilOddTailInverseWeightedCorrection_quadraticForm_le

end Q3.RouteB.D0Pstar
