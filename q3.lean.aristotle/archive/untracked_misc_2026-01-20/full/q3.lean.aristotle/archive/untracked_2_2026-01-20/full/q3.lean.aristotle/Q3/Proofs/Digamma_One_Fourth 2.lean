/-
Q3 Formalization: Digamma at 1/4 is Negative
=============================================

This file proves that Re(ψ(1/4)) < 0, which is used to show a*(0) > 0.

The proof uses the exact value:
  ψ(1/4) = -γ - π/2 - 3·ln(2) ≈ -4.227

where γ is the Euler-Mascheroni constant.

**Citation:** DLMF 5.4.14

**Proof source:** Aristotle (file 2e3b3bf8_aristotle.lean, namespace Digamma14)
-/

import aristotle_output.«2e3b3bf8_aristotle»
import Q3.Basic.Defs

set_option linter.mathlibStandardSet false

open scoped Real
open Real

namespace Q3

/-- The digamma functions from Digamma14 and Q3 are definitionally equal -/
lemma digamma_eq : @Digamma14.digamma = @Q3.digamma := rfl

/-- **Key Result:** The value of ψ(1/4) is -γ - π/2 - 3·ln(2)

This is the exact formula from DLMF 5.4.14.
Proven in aristotle_output/2e3b3bf8_aristotle.lean (namespace Digamma14)
-/
theorem digamma_one_fourth_eq : Q3.digamma (1/4 : ℂ) =
    -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
  rw [← digamma_eq]
  exact Digamma14.digamma_one_fourth

/-- **Main Theorem:** Re(ψ(1/4)) < 0

This follows from the exact value and bounds on the constants:
- γ > 1/2 (Mathlib: one_half_lt_eulerMascheroniConstant)
- π > 3 (Mathlib: pi_gt_three)
- ln(2) > 0 (Mathlib: log_pos)

Therefore: -γ - π/2 - 3·ln(2) < -1/2 - 3/2 - 0 = -2 < 0
-/
theorem digamma_one_fourth_neg_thm : (Q3.digamma (1/4 : ℂ)).re < 0 := by
  rw [digamma_one_fourth_eq]
  -- Simplify the real part of the complex expression
  have h : (-Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 : ℂ).re =
      -Real.eulerMascheroniConstant - Real.pi / 2 - 3 * Real.log 2 := by
    simp only [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, Complex.div_ofNat_re,
      Complex.ofReal_im, Complex.mul_re, mul_zero, sub_zero]
    norm_num
  rw [h]
  -- Now prove the inequality using bounds on constants
  have hgamma : (1 : ℝ) / 2 < Real.eulerMascheroniConstant := Real.one_half_lt_eulerMascheroniConstant
  have hpi : Real.pi / 2 > 3 / 2 := by have := Real.pi_gt_three; linarith
  have hlog : Real.log 2 > 0 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

end Q3
