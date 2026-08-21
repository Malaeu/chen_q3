import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open MeasureTheory Set

namespace Q3.RouteB.D0Pstar

/-!
# At a fixed window the subcritical weight is bounded

The judge's primary G5 route (verdict `2794daa0`) turns on one sentence:

> For fixed `m`, the exponential weight is bounded on the finite window, so
> ordinary `L²` projection convergence implies weighted `L¹` convergence.

This file proves the first clause and only the first clause. On the window
`[-L/2, L/2]` the weight `exp (σ |t|)` never exceeds its endpoint value
`exp (σ L / 2)`, so a weighted integral is dominated by the unweighted one times
an explicit constant depending on the window and the weight but on nothing else.

That constant is exactly what may **not** be carried across the cofinal path:
`L` is the log of the window parameter, so `exp (σ L / 2)` grows. The bound is
useful precisely because the route uses it at fixed `m` and then chooses a
diagonal, never because it is uniform. Reading it as uniform is the second
largest defect class in the kill ledger.

⚠️ **The second clause is not here.** Passing from an `L²` bound to an `L¹`
bound on a finite window is Cauchy–Schwarz and is a separate step; this file
assumes whatever unweighted control it is given.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- On the centred window the subcritical weight is bounded by its endpoint
value. -/
theorem exp_weight_le_endpoint
    {L σ t : ℝ} (hσ : 0 ≤ σ) (ht : t ∈ Icc (-(L / 2)) (L / 2)) :
    Real.exp (σ * |t|) ≤ Real.exp (σ * (L / 2)) := by
  have habs : |t| ≤ L / 2 := abs_le.mpr ⟨ht.1, ht.2⟩
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hσ)

/-- **The fixed-window weight bound.**  A weighted integral of a nonnegative
function over the centred window is at most the endpoint weight times the
unweighted integral.

The constant depends on the window and on the weight, and on nothing else. It is
not uniform in the window. -/
theorem weighted_window_integral_le
    {L σ : ℝ} (hσ : 0 ≤ σ) (f : ℝ → ℝ)
    (hf : ∀ t, 0 ≤ f t)
    (hint : IntegrableOn f (Icc (-(L / 2)) (L / 2)))
    (hintw :
      IntegrableOn (fun t => f t * Real.exp (σ * |t|)) (Icc (-(L / 2)) (L / 2))) :
    (∫ t in Icc (-(L / 2)) (L / 2), f t * Real.exp (σ * |t|))
      ≤ Real.exp (σ * (L / 2)) * ∫ t in Icc (-(L / 2)) (L / 2), f t := by
  rw [← integral_const_mul]
  refine setIntegral_mono_on hintw (hint.const_mul _) measurableSet_Icc ?_
  intro t ht
  have hw : Real.exp (σ * |t|) ≤ Real.exp (σ * (L / 2)) :=
    exp_weight_le_endpoint hσ ht
  calc
    f t * Real.exp (σ * |t|) ≤ f t * Real.exp (σ * (L / 2)) :=
      mul_le_mul_of_nonneg_left hw (hf t)
    _ = Real.exp (σ * (L / 2)) * f t := by ring

/-- The convergence form the route consumes at fixed window: an unweighted
sequence of integrals tending to zero drags the weighted ones with it.

Stated with the unweighted control as a hypothesis, because supplying that
control is the separate Cauchy–Schwarz step and is not proved here. -/
theorem weighted_window_integral_le_of_unweighted_le
    {L σ : ℝ} (hσ : 0 ≤ σ) (f : ℝ → ℝ) (ε : ℝ)
    (hf : ∀ t, 0 ≤ f t)
    (hint : IntegrableOn f (Icc (-(L / 2)) (L / 2)))
    (hintw :
      IntegrableOn (fun t => f t * Real.exp (σ * |t|)) (Icc (-(L / 2)) (L / 2)))
    (hsmall : (∫ t in Icc (-(L / 2)) (L / 2), f t) ≤ ε) :
    (∫ t in Icc (-(L / 2)) (L / 2), f t * Real.exp (σ * |t|))
      ≤ Real.exp (σ * (L / 2)) * ε := by
  refine le_trans (weighted_window_integral_le hσ f hf hint hintw) ?_
  exact mul_le_mul_of_nonneg_left hsmall (Real.exp_nonneg _)

#print axioms exp_weight_le_endpoint
#print axioms weighted_window_integral_le
#print axioms weighted_window_integral_le_of_unweighted_le

end Q3.RouteB.D0Pstar
