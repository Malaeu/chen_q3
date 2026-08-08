import Q3.Proofs.RouteB.D0PstarSourceArchHyperbolicKernel
import Q3.Proofs.RouteB.D0PstarVModeLogWeightedL2
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

private theorem abs_one_sub_cos_le_two_mul_sqrt_abs (y : ℝ) :
    |1 - Real.cos y| ≤ 2 * Real.sqrt |y| := by
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.cos_le_one y))]
  by_cases hy : |y| ≤ 1
  · have hquad : 1 - Real.cos y ≤ y ^ 2 / 2 := by
      linarith [Real.one_sub_sq_div_two_le_cos (x := y)]
    have habs_sq : y ^ 2 = |y| ^ 2 := by rw [sq_abs]
    have hsqrt_sq : (Real.sqrt |y|) ^ 2 = |y| :=
      Real.sq_sqrt (abs_nonneg y)
    have hsqrt_nonneg : 0 ≤ Real.sqrt |y| := Real.sqrt_nonneg _
    have hsqrt_le_one : Real.sqrt |y| ≤ 1 := by nlinarith
    have habs_le_sqrt : |y| ≤ Real.sqrt |y| := by nlinarith
    rw [habs_sq] at hquad
    nlinarith [sq_nonneg |y|]
  · have hcrude : 1 - Real.cos y ≤ 2 := by
      linarith [Real.neg_one_le_cos y]
    have habs_gt : 1 < |y| := lt_of_not_ge hy
    have hsqrt_sq : (Real.sqrt |y|) ^ 2 = |y| :=
      Real.sq_sqrt (abs_nonneg y)
    have hsqrt_nonneg : 0 ≤ Real.sqrt |y| := Real.sqrt_nonneg _
    have hsqrt_ge_one : 1 ≤ Real.sqrt |y| := by nlinarith
    nlinarith

private theorem two_mul_exp_neg_two_mul_le_one_sub_exp_neg_two
    (x : ℝ) :
    2 * x * Real.exp (-2 * x) ≤ 1 - Real.exp (-2 * x) := by
  have hbase := Real.add_one_le_exp (2 * x)
  have hmul := mul_le_mul_of_nonneg_right hbase (Real.exp_nonneg (-2 * x))
  rw [← Real.exp_add] at hmul
  norm_num at hmul ⊢
  nlinarith

private def pairedNumerator (t x : ℝ) : ℝ :=
  Real.exp (-2 * x) -
    Real.exp (-x / 2) * Real.cos (2 * Real.pi * t * x)

private def pairedDenominator (x : ℝ) : ℝ :=
  1 - Real.exp (-2 * x)

private theorem pairedDenominator_pos {x : ℝ} (hx : 0 < x) :
    0 < pairedDenominator x := by
  unfold pairedDenominator
  rw [sub_pos, Real.exp_lt_one_iff]
  linarith

private theorem sourceArchimedeanRegularizedKernel_eq_paired
    (t : ℝ) {x : ℝ} (hx : x ≠ 0) :
    sourceArchimedeanRegularizedKernel t x =
      -(pairedNumerator t x / pairedDenominator x) := by
  have hsourceDen : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have harg : x = -x := Real.exp_injective (sub_eq_zero.mp h)
    exact hx (by linarith)
  have hpairDen : pairedDenominator x ≠ 0 := by
    unfold pairedDenominator
    intro h
    have hexp : Real.exp (-2 * x) = Real.exp 0 := by
      simpa using (sub_eq_zero.mp h).symm
    have : -2 * x = 0 := Real.exp_injective hexp
    exact hx (by linarith)
  have hneg2 : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [show -2 * x = -x + -x by ring, Real.exp_add]
  have hneg2' : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
    rw [show -(2 * x) = -x + -x by ring, Real.exp_add]
  have hAB : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  have hAJ : Real.exp x * Real.exp (-x / 2) = Real.exp (x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hHB : Real.exp (x / 2) * Real.exp (-x) = Real.exp (-x / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hpairDenSq : 1 - Real.exp (-x) ^ 2 ≠ 0 := by
    simpa [pairedDenominator, hneg2, hneg2', pow_two] using hpairDen
  unfold sourceArchimedeanRegularizedKernel pairedNumerator pairedDenominator
  rw [hneg2]
  field_simp [hpairDenSq, hsourceDen]
  ring_nf
  have hhalfNormPos : Real.exp (x * (1 / 2)) = Real.exp (x / 2) := by
    congr 1
    ring
  have hhalfNormNeg : Real.exp (x * (-1 / 2)) = Real.exp (-x / 2) := by
    congr 1
    ring
  have hcosNorm : Real.cos (x * Real.pi * t * 2) =
      Real.cos (2 * Real.pi * t * x) := by
    congr 1
    ring
  rw [hhalfNormPos, hhalfNormNeg, hcosNorm]
  have hCBA :
      Real.cos (2 * Real.pi * t * x) * Real.exp (-x) * Real.exp x =
        Real.cos (2 * Real.pi * t * x) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) *
          (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [hAB, mul_one]
  have hBBA : Real.exp (-x) ^ 2 * Real.exp x = Real.exp (-x) := by
    calc
      _ = Real.exp (-x) * (Real.exp x * Real.exp (-x)) := by ring
      _ = _ := by rw [hAB, mul_one]
  have hCAJ :
      Real.cos (2 * Real.pi * t * x) * Real.exp x * Real.exp (-x / 2) =
        Real.cos (2 * Real.pi * t * x) * Real.exp (x / 2) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) *
          (Real.exp x * Real.exp (-x / 2)) := by ring
      _ = _ := by rw [hAJ]
  have hHCB :
      Real.exp (x / 2) * Real.cos (2 * Real.pi * t * x) *
          Real.exp (-x) ^ 2 =
        Real.cos (2 * Real.pi * t * x) * Real.exp (-x) *
          Real.exp (-x / 2) := by
    calc
      _ = Real.cos (2 * Real.pi * t * x) * Real.exp (-x) *
          (Real.exp (x / 2) * Real.exp (-x)) := by ring
      _ = _ := by rw [hHB]
  rw [hHCB, hCAJ, hBBA]
  ring

private theorem abs_pairedNumerator_le_den_add_oscillation
    (t : ℝ) {x : ℝ} (hx : 0 < x) :
    |pairedNumerator t x| ≤
      pairedDenominator x +
        Real.exp (-x / 2) * |1 - Real.cos (2 * Real.pi * t * x)| := by
  have hexp_order : Real.exp (-2 * x) ≤ Real.exp (-x / 2) := by
    rw [Real.exp_le_exp]
    linarith
  have hexp_half_le_one : Real.exp (-x / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hsplit :
      pairedNumerator t x =
        (Real.exp (-2 * x) - Real.exp (-x / 2)) +
          Real.exp (-x / 2) *
            (1 - Real.cos (2 * Real.pi * t * x)) := by
    unfold pairedNumerator
    ring
  rw [hsplit]
  calc
    |(Real.exp (-2 * x) - Real.exp (-x / 2)) +
        Real.exp (-x / 2) *
          (1 - Real.cos (2 * Real.pi * t * x))| ≤
        |Real.exp (-2 * x) - Real.exp (-x / 2)| +
          |Real.exp (-x / 2) *
            (1 - Real.cos (2 * Real.pi * t * x))| := abs_add_le _ _
    _ = (Real.exp (-x / 2) - Real.exp (-2 * x)) +
          Real.exp (-x / 2) *
            |1 - Real.cos (2 * Real.pi * t * x)| := by
      rw [abs_of_nonpos (sub_nonpos.mpr hexp_order), abs_mul,
        abs_of_pos (Real.exp_pos _)]
      ring
    _ ≤ (1 - Real.exp (-2 * x)) +
          Real.exp (-x / 2) *
            |1 - Real.cos (2 * Real.pi * t * x)| := by
      gcongr
    _ = pairedDenominator x +
          Real.exp (-x / 2) *
            |1 - Real.cos (2 * Real.pi * t * x)| := by
      rfl

private theorem sourceArchimedeanRegularizedKernel_norm_le_near
    (t : ℝ) {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖sourceArchimedeanRegularizedKernel t x‖ ≤
      1 + Real.exp (3 / 2 : ℝ) *
        (Real.sqrt |2 * Real.pi * t| / Real.sqrt x) := by
  have hden_pos : 0 < pairedDenominator x := pairedDenominator_pos hx
  have hden_ne : pairedDenominator x ≠ 0 := hden_pos.ne'
  have hlower_pos : 0 < 2 * x * Real.exp (-2 * x) := by positivity
  have hlower :
      2 * x * Real.exp (-2 * x) ≤ pairedDenominator x := by
    simpa [pairedDenominator] using
      two_mul_exp_neg_two_mul_le_one_sub_exp_neg_two x
  have hnum := abs_pairedNumerator_le_den_add_oscillation t hx
  let y : ℝ := 2 * Real.pi * t * x
  have hcos : |1 - Real.cos y| ≤ 2 * Real.sqrt |y| :=
    abs_one_sub_cos_le_two_mul_sqrt_abs y
  have hosc_nonneg :
      0 ≤ Real.exp (-x / 2) * |1 - Real.cos y| := by positivity
  have hosc_le :
      Real.exp (-x / 2) * |1 - Real.cos y| ≤
        Real.exp (-x / 2) * (2 * Real.sqrt |y|) := by
    gcongr
  have hfrac :
      Real.exp (-x / 2) * |1 - Real.cos y| / pairedDenominator x ≤
        Real.exp (-x / 2) * (2 * Real.sqrt |y|) /
          (2 * x * Real.exp (-2 * x)) := by
    calc
      Real.exp (-x / 2) * |1 - Real.cos y| / pairedDenominator x ≤
          Real.exp (-x / 2) * (2 * Real.sqrt |y|) /
            pairedDenominator x := by
        exact div_le_div_of_nonneg_right hosc_le hden_pos.le
      _ ≤ Real.exp (-x / 2) * (2 * Real.sqrt |y|) /
            (2 * x * Real.exp (-2 * x)) := by
        exact div_le_div_of_nonneg_left (by positivity) hlower_pos hlower
  have habs_y : |y| = |2 * Real.pi * t| * x := by
    dsimp [y]
    rw [abs_mul, abs_of_pos hx]
  have hsqrt_y :
      Real.sqrt |y| = Real.sqrt |2 * Real.pi * t| * Real.sqrt x := by
    rw [habs_y, Real.sqrt_mul (abs_nonneg (2 * Real.pi * t))]
  have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hsqrt_ratio :
      Real.sqrt |y| / x =
        Real.sqrt |2 * Real.pi * t| / Real.sqrt x := by
    rw [hsqrt_y]
    field_simp [hsqrt_pos.ne', hx.ne']
    rw [Real.sq_sqrt hx.le]
  have hexp_ratio :
      Real.exp (-x / 2) / Real.exp (-2 * x) =
        Real.exp (3 * x / 2) := by
    rw [← Real.exp_sub]
    congr 1
    ring
  have hfrac_eq :
      Real.exp (-x / 2) * (2 * Real.sqrt |y|) /
          (2 * x * Real.exp (-2 * x)) =
        Real.exp (3 * x / 2) *
          (Real.sqrt |2 * Real.pi * t| / Real.sqrt x) := by
    calc
      _ = (Real.exp (-x / 2) / Real.exp (-2 * x)) *
            (Real.sqrt |y| / x) := by
        field_simp [Real.exp_ne_zero, hx.ne']
      _ = _ := by rw [hexp_ratio, hsqrt_ratio]
  have hexp_le : Real.exp (3 * x / 2) ≤ Real.exp (3 / 2 : ℝ) := by
    rw [Real.exp_le_exp]
    nlinarith
  rw [sourceArchimedeanRegularizedKernel_eq_paired t hx.ne',
    norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
  calc
    |pairedNumerator t x| / pairedDenominator x ≤
        (pairedDenominator x +
          Real.exp (-x / 2) *
            |1 - Real.cos (2 * Real.pi * t * x)|) /
          pairedDenominator x :=
      div_le_div_of_nonneg_right hnum hden_pos.le
    _ = 1 + Real.exp (-x / 2) * |1 - Real.cos y| /
          pairedDenominator x := by
      dsimp [y]
      field_simp [hden_ne]
    _ ≤ 1 + Real.exp (-x / 2) * (2 * Real.sqrt |y|) /
          (2 * x * Real.exp (-2 * x)) := by
      linarith
    _ = 1 + Real.exp (3 * x / 2) *
          (Real.sqrt |2 * Real.pi * t| / Real.sqrt x) := by
      rw [hfrac_eq]
    _ ≤ 1 + Real.exp (3 / 2 : ℝ) *
          (Real.sqrt |2 * Real.pi * t| / Real.sqrt x) := by
      gcongr

private theorem sourceArchimedeanRegularizedKernel_norm_le_tail
    (t : ℝ) {x : ℝ} (hx : 1 < x) :
    ‖sourceArchimedeanRegularizedKernel t x‖ ≤
      (1 - Real.exp (-2))⁻¹ *
        (Real.exp (-2 * x) + Real.exp (-x / 2)) := by
  have hconst_pos : 0 < 1 - Real.exp (-2) := by
    rw [sub_pos, Real.exp_lt_one_iff]
    norm_num
  have hexp_le : Real.exp (-2 * x) ≤ Real.exp (-2) := by
    rw [Real.exp_le_exp]
    linarith
  have hden_pos : 0 < pairedDenominator x := pairedDenominator_pos (by linarith)
  have hden_lower : 1 - Real.exp (-2) ≤ pairedDenominator x := by
    unfold pairedDenominator
    linarith
  have hnum :
      |pairedNumerator t x| ≤
        Real.exp (-2 * x) + Real.exp (-x / 2) := by
    unfold pairedNumerator
    calc
      |Real.exp (-2 * x) -
          Real.exp (-x / 2) * Real.cos (2 * Real.pi * t * x)| ≤
          |Real.exp (-2 * x)| +
            |Real.exp (-x / 2) * Real.cos (2 * Real.pi * t * x)| :=
        abs_sub _ _
      _ = Real.exp (-2 * x) +
          Real.exp (-x / 2) * |Real.cos (2 * Real.pi * t * x)| := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _),
          abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp (-2 * x) + Real.exp (-x / 2) * 1 := by
        gcongr
        exact Real.abs_cos_le_one _
      _ = _ := by ring
  rw [sourceArchimedeanRegularizedKernel_eq_paired t (by linarith),
    norm_neg, Real.norm_eq_abs, abs_div, abs_of_pos hden_pos]
  calc
    |pairedNumerator t x| / pairedDenominator x ≤
        (Real.exp (-2 * x) + Real.exp (-x / 2)) /
          pairedDenominator x :=
      div_le_div_of_nonneg_right hnum hden_pos.le
    _ ≤ (Real.exp (-2 * x) + Real.exp (-x / 2)) /
          (1 - Real.exp (-2)) := by
      exact div_le_div_of_nonneg_left (by positivity) hconst_pos hden_lower
    _ = (1 - Real.exp (-2))⁻¹ *
          (Real.exp (-2 * x) + Real.exp (-x / 2)) := by
      field_simp

private theorem integrableOn_one_Ioc_zero_one :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioc 0 1) := by
  exact integrableOn_const measure_Ioc_lt_top.ne

private theorem integrableOn_inv_sqrt_Ioc_zero_one :
    IntegrableOn (fun x : ℝ => 1 / Real.sqrt x) (Ioc 0 1) := by
  have hrpow :
      IntegrableOn (fun x : ℝ => x ^ (-1 / 2 : ℝ)) (Ioc 0 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      (show (0 : ℝ) ≤ 1 by norm_num)]
    exact intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  refine hrpow.congr_fun ?_ measurableSet_Ioc
  intro x hx
  symm
  calc
    1 / Real.sqrt x = (x ^ (1 / 2 : ℝ))⁻¹ := by
      rw [Real.sqrt_eq_rpow, one_div]
    _ = x ^ (-(1 / 2 : ℝ)) :=
      (Real.rpow_neg hx.1.le (1 / 2 : ℝ)).symm
    _ = x ^ (-1 / 2 : ℝ) := by ring_nf

private theorem integrableOn_tailMajorant_Ioi_one :
    IntegrableOn
      (fun x : ℝ =>
        (1 - Real.exp (-2))⁻¹ *
          (Real.exp (-2 * x) + Real.exp (-x / 2)))
      (Ioi 1) := by
  have htwo : IntegrableOn (fun x : ℝ => Real.exp (-2 * x)) (Ioi 1) :=
    integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 1
  have hhalf : IntegrableOn (fun x : ℝ => Real.exp ((-1 / 2 : ℝ) * x))
      (Ioi 1) :=
    integrableOn_exp_mul_Ioi (a := (-1 / 2 : ℝ)) (by norm_num) 1
  have hhalf' : IntegrableOn (fun x : ℝ => Real.exp (-x / 2))
      (Ioi 1) := by
    refine hhalf.congr_fun ?_ measurableSet_Ioi
    intro x _
    ring_nf
  have hsum : IntegrableOn
      (fun x : ℝ => Real.exp (-2 * x) + Real.exp (-x / 2))
      (Ioi 1) := htwo.add hhalf'
  exact hsum.const_mul ((1 - Real.exp (-2))⁻¹)

private def fixedModeNormProduct
    (i : PairIndex) (n r : ℤ) (t : ℝ) : ℝ :=
  ‖𝓕 (logWindowZeroExtendedMode i n) t‖ *
    ‖𝓕 (logWindowZeroExtendedMode i r) t‖

private theorem logWindowZeroExtendedMode_integrable_local
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem fourier_logWindowZeroExtendedMode_memLp_two_local
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · have hfi := logWindowZeroExtendedMode_integrable_local i n
    exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop) hfi).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private theorem fixedModeNormProduct_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (fixedModeNormProduct i n r) := by
  have hn := fourier_logWindowZeroExtendedMode_memLp_two_local i n
  have hr := fourier_logWindowZeroExtendedMode_memLp_two_local i r
  have hproduct : Integrable
      (fun t : ℝ =>
        𝓕 (logWindowZeroExtendedMode i n) t *
          𝓕 (logWindowZeroExtendedMode i r) t) := by
    simpa only [Pi.mul_apply] using hn.integrable_mul hr
  simpa [fixedModeNormProduct, norm_mul] using hproduct.norm

private def fixedModeDecayConstant (i : PairIndex) (n : ℤ) : ℝ :=
  (2 * Real.sqrt (L_m i) +
      2 / (Real.pi * Real.sqrt (L_m i))) *
    (1 + |(n : ℝ) / L_m i|)

private theorem fixedModeDecayConstant_nonneg
    (i : PairIndex) (n : ℤ) :
    0 ≤ fixedModeDecayConstant i n := by
  unfold fixedModeDecayConstant
  positivity

private theorem fixedModeNormProduct_mul_sqrt_frequency_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable
      (fun t : ℝ =>
        fixedModeNormProduct i n r t *
          Real.sqrt |2 * Real.pi * t|) := by
  let Cn := fixedModeDecayConstant i n
  let Cr := fixedModeDecayConstant i r
  let C := Cn * Cr * Real.sqrt (2 * Real.pi)
  have hCn : 0 ≤ Cn := fixedModeDecayConstant_nonneg i n
  have hCr : 0 ≤ Cr := fixedModeDecayConstant_nonneg i r
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hdom : Integrable
      (fun t : ℝ => C * (1 + ‖t‖) ^ (-(3 / 2 : ℝ))) := by
    exact (integrable_one_add_norm (E := ℝ) (by norm_num)).const_mul C
  refine hdom.mono' ?_ ?_
  · exact (fixedModeNormProduct_integrable i n r).1.mul (by fun_prop)
  · filter_upwards [] with t
    let a : ℝ := 1 + |t|
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hn := norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe i n t
    have hr := norm_fourier_logWindowZeroExtendedMode_le_resonanceSafe i r t
    have hn' :
        ‖𝓕 (logWindowZeroExtendedMode i n) t‖ ≤ Cn / a := by
      simpa [Cn, a, fixedModeDecayConstant] using hn
    have hr' :
        ‖𝓕 (logWindowZeroExtendedMode i r) t‖ ≤ Cr / a := by
      simpa [Cr, a, fixedModeDecayConstant] using hr
    have hprod :
        fixedModeNormProduct i n r t ≤ Cn * Cr / a ^ 2 := by
      unfold fixedModeNormProduct
      calc
        ‖𝓕 (logWindowZeroExtendedMode i n) t‖ *
            ‖𝓕 (logWindowZeroExtendedMode i r) t‖ ≤
            (Cn / a) * (Cr / a) := by
          exact mul_le_mul hn' hr' (norm_nonneg _) (div_nonneg hCn ha.le)
        _ = Cn * Cr / a ^ 2 := by
          field_simp [ha.ne']
    have habs_frequency :
        |2 * Real.pi * t| = (2 * Real.pi) * |t| := by
      rw [abs_mul, abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
    have hsqrt_frequency :
        Real.sqrt |2 * Real.pi * t| ≤
          Real.sqrt (2 * Real.pi) * Real.sqrt a := by
      rw [habs_frequency,
        Real.sqrt_mul (show 0 ≤ 2 * Real.pi by positivity)]
      gcongr
      dsimp [a]
      linarith
    have hpow :
        Real.sqrt a / a ^ 2 = a ^ (-(3 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_sub ha]
      norm_num
    have htarget_nonneg :
        0 ≤ fixedModeNormProduct i n r t *
          Real.sqrt |2 * Real.pi * t| := by
      unfold fixedModeNormProduct
      positivity
    have hdom_nonneg : 0 ≤ C * (1 + ‖t‖) ^ (-(3 / 2 : ℝ)) := by
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg htarget_nonneg]
    calc
      fixedModeNormProduct i n r t * Real.sqrt |2 * Real.pi * t| ≤
          (Cn * Cr / a ^ 2) *
            (Real.sqrt (2 * Real.pi) * Real.sqrt a) := by
        exact mul_le_mul hprod hsqrt_frequency (Real.sqrt_nonneg _)
          (by positivity)
      _ = C * a ^ (-(3 / 2 : ℝ)) := by
        dsimp [C]
        rw [← hpow]
        field_simp [ha.ne']
      _ = C * (1 + |t|) ^ (-(3 / 2 : ℝ)) := by rfl

def sourceArchimedeanKernelModeIntegrand
    (i : PairIndex) (n r : ℤ) (p : ℝ × ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) p.1) *
    (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ) *
    𝓕 (logWindowZeroExtendedMode i r) p.1

private theorem sourceArchimedeanKernelModeIntegrand_aestronglyMeasurable
    (i : PairIndex) (n r : ℤ) (μ : Measure (ℝ × ℝ)) :
    AEStronglyMeasurable
      (sourceArchimedeanKernelModeIntegrand i n r) μ := by
  have hncont : Continuous
      (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (logWindowZeroExtendedMode_integrable_local i n)
  have hrcont : Continuous
      (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i r) t) :=
    VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (logWindowZeroExtendedMode_integrable_local i r)
  have hnmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => conj (𝓕 (logWindowZeroExtendedMode i n) p.1)) μ :=
    (Complex.continuous_conj.comp (hncont.comp continuous_fst)).aestronglyMeasurable
  have hrmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => 𝓕 (logWindowZeroExtendedMode i r) p.1) μ :=
    (hrcont.comp continuous_fst).aestronglyMeasurable
  have hkmeasReal : Measurable
      (fun p : ℝ × ℝ =>
        sourceArchimedeanRegularizedKernel p.1 p.2) := by
    unfold sourceArchimedeanRegularizedKernel
    fun_prop
  have hkmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ =>
        (sourceArchimedeanRegularizedKernel p.1 p.2 : ℂ)) μ :=
    (Complex.measurable_ofReal.comp hkmeasReal).aestronglyMeasurable
  simpa [sourceArchimedeanKernelModeIntegrand] using
    (hnmeas.mul hkmeas).mul hrmeas

private theorem sourceArchimedeanKernelModeIntegrand_integrable_near
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Ioc 0 1))) := by
  let E : ℝ := Real.exp (3 / 2 : ℝ)
  have hmode := fixedModeNormProduct_integrable i n r
  have hmodeSqrt :=
    fixedModeNormProduct_mul_sqrt_frequency_integrable i n r
  have hone : Integrable (fun _ : ℝ => (1 : ℝ))
      (volume.restrict (Ioc 0 1)) := integrableOn_one_Ioc_zero_one
  have hinvSqrt : Integrable (fun x : ℝ => 1 / Real.sqrt x)
      (volume.restrict (Ioc 0 1)) := integrableOn_inv_sqrt_Ioc_zero_one
  have hmajor0 : Integrable
      (fun p : ℝ × ℝ => fixedModeNormProduct i n r p.1 * 1)
      (volume.prod (volume.restrict (Ioc 0 1))) :=
    hmode.mul_prod hone
  have hmajor1 : Integrable
      (fun p : ℝ × ℝ =>
        (E * (fixedModeNormProduct i n r p.1 *
          Real.sqrt |2 * Real.pi * p.1|)) *
            (1 / Real.sqrt p.2))
      (volume.prod (volume.restrict (Ioc 0 1))) := by
    exact (hmodeSqrt.const_mul E).mul_prod hinvSqrt
  have hmajor := hmajor0.add hmajor1
  have hmeas :=
    sourceArchimedeanKernelModeIntegrand_aestronglyMeasurable i n r
      (volume.prod (volume.restrict (Ioc 0 1)))
  rw [← integrable_norm_iff hmeas]
  refine hmajor.mono' hmeas.norm ?_
  have hx_ae : ∀ᵐ x ∂volume.restrict (Ioc (0 : ℝ) 1), x ∈ Ioc 0 1 :=
    ae_restrict_mem measurableSet_Ioc
  have hp_ae : ∀ᵐ (p : ℝ × ℝ) ∂volume.prod (volume.restrict (Ioc (0 : ℝ) 1)),
      p.2 ∈ Ioc 0 1 := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (measurable_snd measurableSet_Ioc)]
    exact ae_of_all volume (fun _ => hx_ae)
  filter_upwards [hp_ae] with p hp
  have hk := sourceArchimedeanRegularizedKernel_norm_le_near
    p.1 hp.1 hp.2
  have hmode_nonneg : 0 ≤ fixedModeNormProduct i n r p.1 := by
    unfold fixedModeNormProduct
    positivity
  have hsqrt_nonneg : 0 ≤ Real.sqrt |2 * Real.pi * p.1| :=
    Real.sqrt_nonneg _
  have hinv_nonneg : 0 ≤ 1 / Real.sqrt p.2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [sourceArchimedeanKernelModeIntegrand, norm_mul,
    norm_conj, Complex.norm_real, Pi.add_apply]
  dsimp [E]
  calc
    ‖𝓕 (logWindowZeroExtendedMode i n) p.1‖ *
          |sourceArchimedeanRegularizedKernel p.1 p.2| *
          ‖𝓕 (logWindowZeroExtendedMode i r) p.1‖ =
        fixedModeNormProduct i n r p.1 *
          ‖sourceArchimedeanRegularizedKernel p.1 p.2‖ := by
      rw [Real.norm_eq_abs]
      unfold fixedModeNormProduct
      ring
    _ ≤ fixedModeNormProduct i n r p.1 *
          (1 + Real.exp (3 / 2 : ℝ) *
            (Real.sqrt |2 * Real.pi * p.1| / Real.sqrt p.2)) := by
      gcongr
    _ = fixedModeNormProduct i n r p.1 * 1 +
          (Real.exp (3 / 2 : ℝ) *
            (fixedModeNormProduct i n r p.1 *
              Real.sqrt |2 * Real.pi * p.1|)) *
            (1 / Real.sqrt p.2) := by
      ring

private theorem sourceArchimedeanKernelModeIntegrand_integrable_tail
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Ioi 1))) := by
  have hmode := fixedModeNormProduct_integrable i n r
  have htail : Integrable
      (fun x : ℝ =>
        (1 - Real.exp (-2))⁻¹ *
          (Real.exp (-2 * x) + Real.exp (-x / 2)))
      (volume.restrict (Ioi 1)) := integrableOn_tailMajorant_Ioi_one
  have hmajor : Integrable
      (fun p : ℝ × ℝ =>
        fixedModeNormProduct i n r p.1 *
          ((1 - Real.exp (-2))⁻¹ *
            (Real.exp (-2 * p.2) + Real.exp (-p.2 / 2))))
      (volume.prod (volume.restrict (Ioi 1))) :=
    hmode.mul_prod htail
  have hmeas :=
    sourceArchimedeanKernelModeIntegrand_aestronglyMeasurable i n r
      (volume.prod (volume.restrict (Ioi 1)))
  rw [← integrable_norm_iff hmeas]
  refine hmajor.mono' hmeas.norm ?_
  have hx_ae : ∀ᵐ x ∂volume.restrict (Ioi (1 : ℝ)), x ∈ Ioi 1 :=
    ae_restrict_mem measurableSet_Ioi
  have hp_ae : ∀ᵐ (p : ℝ × ℝ) ∂volume.prod (volume.restrict (Ioi (1 : ℝ))),
      p.2 ∈ Ioi 1 := by
    rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
      (measurable_snd measurableSet_Ioi)]
    exact ae_of_all volume (fun _ => hx_ae)
  filter_upwards [hp_ae] with p hp
  have hk := sourceArchimedeanRegularizedKernel_norm_le_tail p.1 hp
  have hmode_nonneg : 0 ≤ fixedModeNormProduct i n r p.1 := by
    unfold fixedModeNormProduct
    positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  simp only [sourceArchimedeanKernelModeIntegrand, norm_mul,
    norm_conj, Complex.norm_real]
  calc
    ‖𝓕 (logWindowZeroExtendedMode i n) p.1‖ *
          |sourceArchimedeanRegularizedKernel p.1 p.2| *
          ‖𝓕 (logWindowZeroExtendedMode i r) p.1‖ =
        fixedModeNormProduct i n r p.1 *
          ‖sourceArchimedeanRegularizedKernel p.1 p.2‖ := by
      rw [Real.norm_eq_abs]
      unfold fixedModeNormProduct
      ring
    _ ≤ fixedModeNormProduct i n r p.1 *
          ((1 - Real.exp (-2))⁻¹ *
            (Real.exp (-2 * p.2) + Real.exp (-p.2 / 2))) := by
      gcongr

/--
For every fixed source mode pair, the regularized hyperbolic kernel times the
conjugate-first Fourier-mode product is jointly absolutely integrable in
frequency and the positive hyperbolic variable.
-/
theorem sourceArchimedeanKernelModeIntegrand_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceArchimedeanKernelModeIntegrand i n r)
      (volume.prod (volume.restrict (Ioi 0))) := by
  have hnear := sourceArchimedeanKernelModeIntegrand_integrable_near i n r
  have htail := sourceArchimedeanKernelModeIntegrand_integrable_tail i n r
  have hnearOn : IntegrableOn
      (sourceArchimedeanKernelModeIntegrand i n r)
      ((univ : Set ℝ) ×ˢ Ioc 0 1) (volume.prod volume) := by
    rw [IntegrableOn]
    have hmeasure :
        (volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioc (0 : ℝ) 1) =
          volume.prod (volume.restrict (Ioc 0 1)) := by
      rw [← MeasureTheory.Measure.prod_restrict]
      simp
    rw [hmeasure]
    exact hnear
  have htailOn : IntegrableOn
      (sourceArchimedeanKernelModeIntegrand i n r)
      ((univ : Set ℝ) ×ˢ Ioi 1) (volume.prod volume) := by
    rw [IntegrableOn]
    have hmeasure :
        (volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioi (1 : ℝ)) =
          volume.prod (volume.restrict (Ioi 1)) := by
      rw [← MeasureTheory.Measure.prod_restrict]
      simp
    rw [hmeasure]
    exact htail
  have htotalOn : IntegrableOn
      (sourceArchimedeanKernelModeIntegrand i n r)
      ((univ : Set ℝ) ×ˢ Ioi 0) (volume.prod volume) := by
    rw [← Set.Ioc_union_Ioi_eq_Ioi
      (show (0 : ℝ) ≤ 1 by norm_num), Set.prod_union]
    exact hnearOn.union htailOn
  have hmeasure :
      volume.prod (volume.restrict (Ioi (0 : ℝ))) =
        (volume.prod volume).restrict ((univ : Set ℝ) ×ˢ Ioi 0) := by
    rw [← MeasureTheory.Measure.prod_restrict]
    simp
  rw [hmeasure]
  exact htotalOn


end Q3.RouteB.D0Pstar
