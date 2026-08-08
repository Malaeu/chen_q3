import Q3.Proofs.RouteB.D0LogWindowMeasureTransport
import Mathlib.Analysis.Fourier.FourierTransform

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

def logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) : ℝ → ℂ :=
  Set.indicator (Set.Icc 0 (L_m i))
    (fun x =>
      ((Real.sqrt (L_m i))⁻¹ : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * n *
            (x / L_m i)))

private theorem fourier_logWindowZeroExtendedMode_integral
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    𝓕 (logWindowZeroExtendedMode i n) t =
      (∫ x : ℝ in Set.Icc 0 (L_m i),
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((n : ℝ) / L_m i - t) * x))) := by
  rw [Real.fourier_eq']
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ Set.Icc 0 (L_m i)
  · simp only [logWindowZeroExtendedMode, Set.indicator_of_mem hx,
      smul_eq_mul]
    calc
      Complex.exp (↑(-2 * Real.pi * ⟪x, t⟫) * Complex.I) *
          (((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n * (x / L_m i))) =
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            (Complex.exp (↑(-2 * Real.pi * ⟪x, t⟫) * Complex.I) *
              Complex.exp
                (2 * Real.pi * Complex.I * n * (x / L_m i))) := by ring
      _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (↑(-2 * Real.pi * ⟪x, t⟫) * Complex.I +
                2 * Real.pi * Complex.I * n * (x / L_m i)) := by
          rw [Complex.exp_add]
      _ = ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I *
                (((n : ℝ) / L_m i - t) * x)) := by
          congr 2
          simp [RCLike.inner_apply]
          field_simp [(logLength_pos i).ne']
          ring
  · simp [logWindowZeroExtendedMode, Set.indicator_of_notMem hx]

theorem fourier_logWindowZeroExtendedMode
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    𝓕 (logWindowZeroExtendedMode i n) t =
      if t = (n : ℝ) / L_m i then
        (Real.sqrt (L_m i) : ℂ)
      else
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          (Complex.exp
              (2 * Real.pi * Complex.I *
                (((n : ℝ) / L_m i - t) * L_m i))
            - 1) /
          (2 * Real.pi * Complex.I *
            ((n : ℝ) / L_m i - t)) := by
  rw [fourier_logWindowZeroExtendedMode_integral]
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (logLength_pos i).le]
  by_cases ht : t = (n : ℝ) / L_m i
  · rw [if_pos ht]
    subst t
    simp
    have hsqrt_ne : Real.sqrt (L_m i) ≠ 0 :=
      (Real.sqrt_pos.mpr (logLength_pos i)).ne'
    field_simp [hsqrt_ne]
    norm_cast
    exact (Real.sq_sqrt (logLength_pos i).le).symm
  · rw [if_neg ht]
    rw [intervalIntegral.integral_const_mul]
    have hfreq : (n : ℝ) / L_m i - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
    have hc :
        (2 * Real.pi * Complex.I *
          (((n : ℝ) / L_m i - t : ℝ) : ℂ)) ≠ 0 := by
      apply mul_ne_zero
      · exact mul_ne_zero
          (mul_ne_zero (by norm_num)
            (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
          Complex.I_ne_zero
      · exact Complex.ofReal_ne_zero.mpr hfreq
    have hphase :
        (fun x : ℝ =>
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((n : ℝ) / L_m i - t) * x))) =
        (fun x : ℝ =>
          Complex.exp
            ((2 * Real.pi * Complex.I *
              (((n : ℝ) / L_m i - t : ℝ) : ℂ)) * x)) := by
      funext x
      congr 1
      push_cast
      ring
    have hcoeff :
        2 * Real.pi * Complex.I *
            (((n : ℝ) / L_m i - t : ℝ) : ℂ) =
          2 * Real.pi * Complex.I *
            ((n : ℂ) / (L_m i : ℂ) - (t : ℂ)) := by
      push_cast
      rfl
    have hupper :
        Complex.exp
            ((2 * Real.pi * Complex.I *
              ((n : ℂ) / (L_m i : ℂ) - (t : ℂ))) *
              (L_m i : ℂ)) =
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((n : ℝ) / L_m i - t) * L_m i)) := by
      congr 1
      push_cast
      ring
    have hlower :
        Complex.exp
            ((2 * Real.pi * Complex.I *
              ((n : ℂ) / (L_m i : ℂ) - (t : ℂ))) *
              ((0 : ℝ) : ℂ)) = 1 := by
      norm_num
    have hintCast : ((n : ℝ) : ℂ) = (n : ℂ) := by
      norm_num
    rw [hphase, integral_exp_mul_complex hc]
    rw [hcoeff]
    rw [hupper]
    rw [hintCast]
    rw [hlower]
    ring

#print axioms fourier_logWindowZeroExtendedMode

end Q3.RouteB.D0Pstar
