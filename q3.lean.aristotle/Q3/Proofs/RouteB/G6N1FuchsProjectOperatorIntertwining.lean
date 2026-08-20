import Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# F72.3A — exact intertwining of the paper and project finite Fourier operators

Floor F72.3A of the L73.2 wall, named by the judge as the next local lock in
the REQ-2026-08-20-H scope lock
(`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_20_H_FUCHS_F72_3_SCOPE_LOCK_2026-08-20.md`).

The two operators live in different coordinates.  Fuchs integrates
`exp (I * s * t)` over `(-a, a)`; the project integrates `exp (I * 2 * pi * x * y)`
over `[-lambda, lambda]`.  The kill of REQ-2026-08-20-E showed what happens
when such a mismatch is left implicit, so the conversion is proved here rather
than assumed anywhere downstream.

The whole content is one linear change of variables `s = sqrt (2 * pi) * y`,
made to work because `2 * pi / sqrt (2 * pi) = sqrt (2 * pi)`.

This file proves the operator identity only.  It does NOT define `ps_n`, does
not state the eigenvalue map `Lambda_n = chi_n ^ 2`, does not assume Satz 9 or
Fuchs Theorem 1, and does not touch `CCMLemma73PreAnchorPort`.

LEDGER:
  CLOSES: [F72_3A_FUCHS_PROJECT_OPERATOR_INTERTWINING]
  OPENS:  []
-/

/-- The paper window radius attached to a project window: `a = sqrt (2 pi) * lambda`. -/
noncomputable def paperWindowRadius (lambda : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi) * lambda

/-- The unitary rescaling carrying project coordinates to paper coordinates. -/
noncomputable def paperRescale (h : ℝ → ℂ) (s : ℝ) : ℂ :=
  (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
    h (s / Real.sqrt (2 * Real.pi))

/-- The paper finite Fourier action: kernel `exp (I * s * t)` on `[-a, a]`,
with no `2 * pi` in the exponent. -/
noncomputable def paperFiniteFourierAction (a : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ s in Icc (-a) a, Complex.exp (Complex.I * ((s * t : ℝ) : ℂ)) * f s

private theorem sqrtTwoPi_pos : 0 < Real.sqrt (2 * Real.pi) :=
  Real.sqrt_pos.2 (by positivity)

private theorem sqrtTwoPi_sq :
    Real.sqrt (2 * Real.pi) * Real.sqrt (2 * Real.pi) = 2 * Real.pi :=
  Real.mul_self_sqrt (by positivity)

/-- A symmetric `Icc` integral rescales by a positive factor.  This is the only
analytic step of the floor. -/
private theorem integral_Icc_symm_comp_mul
    (r lambda : ℝ) (hr : 0 < r) (hlambda : 0 ≤ lambda) (F : ℝ → ℂ) :
    (∫ s in Icc (-(r * lambda)) (r * lambda), F s) =
      r • ∫ y in Icc (-lambda) lambda, F (r * y) := by
  have hrl : 0 ≤ r * lambda := mul_nonneg hr.le hlambda
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -(r * lambda) ≤ r * lambda),
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -lambda ≤ lambda)]
  rw [intervalIntegral.integral_comp_mul_left (c := r) F (ne_of_gt hr)]
  rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul, mul_neg]

/-- Exact intertwining, the statement named by the judge:

`F_a (U h) = sqrt (2 pi) * U (T_lambda h)`

where `F_a` is `paperFiniteFourierAction (paperWindowRadius lambda)`, `U` is
`paperRescale`, and `T_lambda` is the production `finiteFourierAction`. -/
theorem paperFiniteFourierAction_paperRescale_eq_smul_paperRescale_finiteFourierAction
    (lambda : ℝ) (hlambda : 0 ≤ lambda) (h : ℝ → ℂ) (t : ℝ) :
    paperFiniteFourierAction (paperWindowRadius lambda) (paperRescale h) t =
      ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) *
        paperRescale (finiteFourierAction lambda h) t := by
  have hr := sqrtTwoPi_pos
  set r : ℝ := Real.sqrt (2 * Real.pi) with hrdef
  have hrne : r ≠ 0 := ne_of_gt hr
  have hrsq : r * r = 2 * Real.pi := sqrtTwoPi_sq
  -- left side: change variables `s = r * y`
  have hleft :
      paperFiniteFourierAction (paperWindowRadius lambda) (paperRescale h) t =
        r • ∫ y in Icc (-lambda) lambda,
          Complex.exp (Complex.I * (((r * y) * t : ℝ) : ℂ)) *
            paperRescale h (r * y) := by
    unfold paperFiniteFourierAction paperWindowRadius
    exact integral_Icc_symm_comp_mul r lambda hr hlambda _
  -- right side: unfold the production operator at the rescaled frequency
  have hright :
      ((r : ℝ) : ℂ) * paperRescale (finiteFourierAction lambda h) t =
        ((r : ℝ) : ℂ) * ((((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
          ∫ y in Icc (-lambda) lambda,
            Complex.exp (Complex.I * ((2 * Real.pi * (t / r) * y : ℝ) : ℂ)) * h y) := by
    unfold paperRescale finiteFourierAction finiteFourierKernel
    rfl
  rw [hleft, hright]
  -- the two integrands agree pointwise
  have hpt : ∀ y : ℝ,
      Complex.exp (Complex.I * (((r * y) * t : ℝ) : ℂ)) * paperRescale h (r * y) =
        (((2 * Real.pi) ^ (-(1 : ℝ) / 4) : ℝ) : ℂ) *
          (Complex.exp (Complex.I * ((2 * Real.pi * (t / r) * y : ℝ) : ℂ)) * h y) := by
    intro y
    have hrsq2 : r ^ 2 = 2 * Real.pi := by
      rw [pow_two]; exact hrsq
    have harg : (r * y) * t = 2 * Real.pi * (t / r) * y := by
      field_simp
      linear_combination (y * t) * hrsq2
    have hdiv : (r * y) / r = y :=
      mul_div_cancel_left₀ y hrne
    unfold paperRescale
    rw [← hrdef, hdiv, harg]
    ring
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [MeasureTheory.integral_const_mul]
  rw [real_smul]

#print axioms paperWindowRadius
#print axioms paperRescale
#print axioms paperFiniteFourierAction
#print axioms integral_Icc_symm_comp_mul
#print axioms paperFiniteFourierAction_paperRescale_eq_smul_paperRescale_finiteFourierAction

end Q3.RouteB.D0Pstar
