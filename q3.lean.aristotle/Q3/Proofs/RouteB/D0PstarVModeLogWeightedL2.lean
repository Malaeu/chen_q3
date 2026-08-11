import Q3.Proofs.RouteB.D0PstarVModeFourierFormula
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.MeasureTheory.Function.L2Space

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

/--
An explicit logarithmic-growth envelope used to separate elementary
mode decay from the still-open exact Riemann--Siegel/digamma symbol bound.

This is not the source archimedean symbol.
-/
def vModeLogGrowthEnvelope (t : ℝ) : ℝ :=
  1 + Real.log (2 + |t|)

private theorem logWindowZeroExtendedMode_integrable
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem norm_fourier_logWindowZeroExtendedMode_le_sqrt
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤ Real.sqrt (L_m i) := by
  rw [Real.fourier_eq]
  calc
    ‖∫ v : ℝ,
        Real.fourierChar (-(inner ℝ v t)) •
          logWindowZeroExtendedMode i n v‖ ≤
        ∫ v : ℝ, ‖logWindowZeroExtendedMode i n v‖ := by
      refine (norm_integral_le_integral_norm _).trans_eq ?_
      apply integral_congr_ae
      filter_upwards [] with v
      simp
    _ = Real.sqrt (L_m i) := by
      have hsqrt : 0 < Real.sqrt (L_m i) :=
        Real.sqrt_pos.mpr (logLength_pos i)
      have hfun :
          (fun v : ℝ => ‖logWindowZeroExtendedMode i n v‖) =
            Set.indicator (Set.Icc 0 (L_m i))
              (fun _ : ℝ => (Real.sqrt (L_m i))⁻¹) := by
        funext v
        by_cases hv : v ∈ Set.Icc 0 (L_m i)
        · simp [logWindowZeroExtendedMode, hv, Complex.norm_exp]
        · simp [logWindowZeroExtendedMode, hv]
      rw [hfun, MeasureTheory.integral_indicator measurableSet_Icc]
      rw [MeasureTheory.setIntegral_const,
        Real.volume_real_Icc_of_le (logLength_pos i).le]
      simp only [sub_zero, smul_eq_mul]
      field_simp [hsqrt.ne']
      exact (Real.sq_sqrt (logLength_pos i).le).symm

theorem norm_fourier_logWindowZeroExtendedMode_le_far
    (i : PairIndex) (n : ℤ) (t : ℝ)
    (hfar : 1 < |t - (n : ℝ) / L_m i|) :
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
      1 / (Real.pi * Real.sqrt (L_m i) *
        |t - (n : ℝ) / L_m i|) := by
  have ht : t ≠ (n : ℝ) / L_m i := by
    intro h
    subst t
    norm_num at hfar
  rw [fourier_logWindowZeroExtendedMode, if_neg ht]
  have hsqrt : 0 < Real.sqrt (L_m i) :=
    Real.sqrt_pos.mpr (logLength_pos i)
  have hdist : 0 < |t - (n : ℝ) / L_m i| := lt_trans zero_lt_one hfar
  have hnum :
      ‖Complex.exp
          (2 * Real.pi * Complex.I *
            (((n : ℝ) / L_m i - t) * L_m i)) - 1‖ ≤ 2 := by
    calc
      ‖Complex.exp
          (2 * Real.pi * Complex.I *
            (((n : ℝ) / L_m i - t) * L_m i)) - 1‖ ≤
          ‖Complex.exp
            (2 * Real.pi * Complex.I *
              (((n : ℝ) / L_m i - t) * L_m i))‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        rw [Complex.norm_exp]
        norm_num
  rw [norm_div, norm_mul]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hsqrt, norm_mul, Complex.norm_I, mul_one,
    norm_ofNat, abs_of_pos Real.pi_pos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hcast :
      (((n : ℝ) : ℂ) / (L_m i : ℂ)) - (t : ℂ) =
        (((n : ℝ) / L_m i - t : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hphase :
      ((((n : ℝ) / L_m i - t) * L_m i : ℝ) : ℂ) =
        ((((n : ℝ) / L_m i - t : ℝ) : ℂ) * (L_m i : ℂ)) := by
    push_cast
    rfl
  rw [← hphase]
  rw [hcast, ← hphase] at hnum
  have hdenpos :
      0 < 2 * Real.pi * |t - (n : ℝ) / L_m i| := by positivity
  rw [div_eq_mul_inv]
  calc
    (Real.sqrt (L_m i))⁻¹ *
          ‖Complex.exp
              (2 * ↑Real.pi * Complex.I *
                ↑(((n : ℝ) / L_m i - t) * L_m i)) - 1‖ *
        (2 * Real.pi * |t - (n : ℝ) / L_m i|)⁻¹ ≤
        (Real.sqrt (L_m i))⁻¹ * 2 *
          (2 * Real.pi * |t - (n : ℝ) / L_m i|)⁻¹ := by
      gcongr
    _ = 1 /
        (Real.pi * Real.sqrt (L_m i) *
          |t - (n : ℝ) / L_m i|) := by
      field_simp [hsqrt.ne', Real.pi_ne_zero, ne_of_gt hdist]

theorem norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
      ((2 * Real.sqrt (L_m i) +
          2 / (Real.pi * Real.sqrt (L_m i))) *
        (1 + |(n : ℝ) / L_m i|)) /
      (1 + |t|) := by
  let a : ℝ := (n : ℝ) / L_m i
  let s : ℝ := Real.sqrt (L_m i)
  have hs : 0 < s := by
    exact Real.sqrt_pos.mpr (logLength_pos i)
  have hpi : 0 < Real.pi := Real.pi_pos
  have hshift : 1 + |t| ≤ (1 + |a|) * (1 + |t - a|) := by
    dsimp [a]
    have habs : |t| ≤ |(n : ℝ) / L_m i| + |t - (n : ℝ) / L_m i| := by
      calc
        |t| = |(n : ℝ) / L_m i + (t - (n : ℝ) / L_m i)| := by ring_nf
        _ ≤ |(n : ℝ) / L_m i| + |t - (n : ℝ) / L_m i| := abs_add_le _ _
    nlinarith [abs_nonneg ((n : ℝ) / L_m i),
      abs_nonneg (t - (n : ℝ) / L_m i)]
  by_cases hnear : |t - a| ≤ 1
  · have hfourier := norm_fourier_logWindowZeroExtendedMode_le_sqrt i n t
    have hden : 0 < 1 + |t| := by positivity
    have hshiftpos : 0 < 1 + |t - a| := by positivity
    have hcoeff :
        s ≤ (2 * s + 2 / (Real.pi * s)) / (1 + |t - a|) := by
      rw [le_div_iff₀ hshiftpos]
      have hnonneg : 0 ≤ 2 / (Real.pi * s) := by positivity
      nlinarith
    calc
      ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤ s := hfourier
      _ ≤ (2 * s + 2 / (Real.pi * s)) / (1 + |t - a|) := hcoeff
      _ ≤ ((2 * s + 2 / (Real.pi * s)) * (1 + |a|)) /
          (1 + |t|) := by
        rw [div_le_div_iff₀ hshiftpos hden]
        have hC : 0 ≤ 2 * s + 2 / (Real.pi * s) := by positivity
        nlinarith
      _ = ((2 * Real.sqrt (L_m i) +
              2 / (Real.pi * Real.sqrt (L_m i))) *
            (1 + |(n : ℝ) / L_m i|)) /
          (1 + |t|) := by rfl
  · have hfar : 1 < |t - a| := lt_of_not_ge hnear
    have hfourier := norm_fourier_logWindowZeroExtendedMode_le_far i n t (by simpa [a] using hfar)
    have hden : 0 < 1 + |t| := by positivity
    have hshiftpos : 0 < 1 + |t - a| := by positivity
    have hdistpos : 0 < |t - a| := lt_trans zero_lt_one hfar
    have hcoeff :
        1 / (Real.pi * s * |t - a|) ≤
          (2 * s + 2 / (Real.pi * s)) / (1 + |t - a|) := by
      rw [div_le_div_iff₀ (by positivity : 0 < Real.pi * s * |t - a|) hshiftpos]
      have hs2 : 0 ≤ 2 * s := by positivity
      have hmain :
          1 + |t - a| ≤ 2 * |t - a| := by linarith
      have haux :
          2 / (Real.pi * s) * (Real.pi * s * |t - a|) =
            2 * |t - a| := by
        field_simp [Real.pi_ne_zero, hs.ne']
      calc
        1 * (1 + |t - a|) ≤ 2 * |t - a| := by linarith
        _ = 2 / (Real.pi * s) *
            (Real.pi * s * |t - a|) := haux.symm
        _ ≤ (2 * s + 2 / (Real.pi * s)) *
            (Real.pi * s * |t - a|) := by
          exact mul_le_mul_of_nonneg_right (by linarith [hs2]) (by positivity)
    calc
      ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤
          1 / (Real.pi * s * |t - a|) := by simpa [a, s] using hfourier
      _ ≤ (2 * s + 2 / (Real.pi * s)) / (1 + |t - a|) := hcoeff
      _ ≤ ((2 * s + 2 / (Real.pi * s)) * (1 + |a|)) /
          (1 + |t|) := by
        rw [div_le_div_iff₀ hshiftpos hden]
        have hC : 0 ≤ 2 * s + 2 / (Real.pi * s) := by positivity
        nlinarith
      _ = ((2 * Real.sqrt (L_m i) +
              2 / (Real.pi * Real.sqrt (L_m i))) *
            (1 + |(n : ℝ) / L_m i|)) /
          (1 + |t|) := by rfl

private theorem vModeLogGrowthEnvelope_continuous :
    Continuous vModeLogGrowthEnvelope := by
  unfold vModeLogGrowthEnvelope
  apply continuous_const.add
  exact (continuous_const.add continuous_abs).log (fun t => by positivity)

private theorem vModeLogGrowthEnvelope_le_rpow_quarter (t : ℝ) :
    vModeLogGrowthEnvelope t ≤
      9 * (1 + |t|) ^ (1 / 4 : ℝ) := by
  have hx : 0 ≤ 2 + |t| := by positivity
  have hlog := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 4)
  have hbase : 1 ≤ (1 + |t|) ^ (1 / 4 : ℝ) := by
    calc
      1 = 1 ^ (1 / 4 : ℝ) := (Real.one_rpow _).symm
      _ ≤ (1 + |t|) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (x := 1) (y := 1 + |t|) (z := 1 / 4)
          (by norm_num) (by linarith [abs_nonneg t]) (by norm_num)
  have hpow :
      (2 + |t|) ^ (1 / 4 : ℝ) ≤
        2 * (1 + |t|) ^ (1 / 4 : ℝ) := by
    calc
      (2 + |t|) ^ (1 / 4 : ℝ) ≤
          (2 * (1 + |t|)) ^ (1 / 4 : ℝ) := by
        apply Real.rpow_le_rpow
        · positivity
        · nlinarith [abs_nonneg t]
        · norm_num
      _ = 2 ^ (1 / 4 : ℝ) * (1 + |t|) ^ (1 / 4 : ℝ) := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity)]
      _ ≤ 2 * (1 + |t|) ^ (1 / 4 : ℝ) := by
        gcongr
        simpa using (Real.rpow_le_rpow_of_exponent_le (x := 2)
          (y := 1 / 4) (z := 1) (by norm_num) (by norm_num))
  unfold vModeLogGrowthEnvelope
  norm_num at hlog
  nlinarith

private theorem integrable_vModeLogGrowthEnvelope_sq_div_one_add_abs_sq :
    Integrable
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2) := by
  have hdom : Integrable (fun t : ℝ => 81 * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) := by
    exact (integrable_one_add_norm (E := ℝ) (by norm_num)).const_mul 81
  refine hdom.mono' ?_ ?_
  · exact ((vModeLogGrowthEnvelope_continuous.pow 2).div
      ((continuous_const.add continuous_abs).pow 2)
      (fun t => by positivity)).aestronglyMeasurable
  · filter_upwards [] with t
    rw [Real.norm_eq_abs]
    have henv_nonneg : 0 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      positivity
    have hbound := vModeLogGrowthEnvelope_le_rpow_quarter t
    have hbase : 0 < 1 + |t| := by positivity
    have hpow_nonneg : 0 ≤ (1 + |t|) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hbase.le _
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hsq :
        (vModeLogGrowthEnvelope t) ^ 2 ≤
          81 * ((1 + |t|) ^ (1 / 4 : ℝ)) ^ 2 := by nlinarith
    have hpow_id :
        ((1 + |t|) ^ (1 / 4 : ℝ)) ^ 2 /
            (1 + |t|) ^ 2 =
          (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hbase.le]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_sub hbase]
      norm_num
    calc
      (vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2 ≤
          (81 * ((1 + |t|) ^ (1 / 4 : ℝ)) ^ 2) /
            (1 + |t|) ^ 2 := by gcongr
      _ = 81 * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by
        rw [mul_div_assoc, hpow_id]

theorem
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp
    (i : PairIndex) (n : ℤ) :
    MemLp
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t)
      2 volume := by
  have hfi : Integrable (logWindowZeroExtendedMode i n) :=
    logWindowZeroExtendedMode_integrable i n
  have hfourier_cont : Continuous (fun t : ℝ =>
      𝓕 (logWindowZeroExtendedMode i n) t) := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hfi
  have hmeas : AEStronglyMeasurable
      (fun t : ℝ =>
        (vModeLogGrowthEnvelope t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t) volume := by
    exact ((Complex.continuous_ofReal.comp
      vModeLogGrowthEnvelope_continuous).mul hfourier_cont).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  let C : ℝ :=
    (2 * Real.sqrt (L_m i) +
      2 / (Real.pi * Real.sqrt (L_m i))) *
      (1 + |(n : ℝ) / L_m i|)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdom :=
    (integrable_vModeLogGrowthEnvelope_sq_div_one_add_abs_sq.const_mul (C ^ 2))
  refine hdom.mono' ?_ ?_
  · fun_prop
  · filter_upwards [] with t
    have hdecay := norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe i n t
    have hden : 0 < 1 + |t| := by positivity
    have henv_nonneg : 0 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      positivity
    have hfourier_nonneg :
        0 ≤ ‖𝓕 (logWindowZeroExtendedMode i n) t‖ := norm_nonneg _
    change |‖(vModeLogGrowthEnvelope t : ℂ) *
        𝓕 (logWindowZeroExtendedMode i n) t‖ ^ 2| ≤
      C ^ 2 *
        ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2)
    rw [abs_of_nonneg (sq_nonneg _)]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg henv_nonneg]
    have hdecay' :
        ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤ C / (1 + |t|) := by
      simpa [C] using hdecay
    have hsq :
        ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ^ 2 ≤
          (C / (1 + |t|)) ^ 2 := by nlinarith
    calc
      (vModeLogGrowthEnvelope t *
          ‖𝓕 (logWindowZeroExtendedMode i n) t‖) ^ 2 ≤
          (vModeLogGrowthEnvelope t * (C / (1 + |t|))) ^ 2 := by
        gcongr
      _ = C ^ 2 *
          ((vModeLogGrowthEnvelope t) ^ 2 / (1 + |t|) ^ 2) := by
        field_simp [ne_of_gt hden]

#print axioms norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe
#print axioms norm_fourier_logWindowZeroExtendedMode_le_far
#print axioms vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp

end Q3.RouteB.D0Pstar
