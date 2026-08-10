import Q3.Proofs.RouteB.D0PstarSourceArchModePairingKernel
import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.D0PstarSourceModeCosineCCMQKernel
import Mathlib.MeasureTheory.Integral.Prod

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

private theorem logWindowZeroExtendedMode_integrable_for_e4a
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem fourier_logWindowZeroExtendedMode_memLp_two_for_e4a
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (logWindowZeroExtendedMode_integrable_for_e4a i n)).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private theorem conj_fourier_logWindowZeroExtendedMode_memLp_two_for_e4a
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => conj (𝓕 (logWindowZeroExtendedMode i n) t))
      2 volume := by
  have hleft := fourier_logWindowZeroExtendedMode_memLp_two_for_e4a i n
  refine hleft.congr_norm ?_ ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable hleft.1
  · filter_upwards [] with t
    exact (norm_conj _).symm

private def bareModeProduct
    (i : PairIndex) (n r : ℤ) (t : ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) t) *
    𝓕 (logWindowZeroExtendedMode i r) t

private theorem bareModeProduct_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (bareModeProduct i n r) := by
  have hn := conj_fourier_logWindowZeroExtendedMode_memLp_two_for_e4a i n
  have hr := fourier_logWindowZeroExtendedMode_memLp_two_for_e4a i r
  simpa only [bareModeProduct, Pi.mul_apply] using hn.integrable_mul hr

private def cosineModeProduct
    (i : PairIndex) (n r : ℤ) (x t : ℝ) : ℂ :=
  (Real.cos (2 * Real.pi * t * x) : ℂ) *
    bareModeProduct i n r t

private theorem cosineModeProduct_integrable
    (i : PairIndex) (n r : ℤ) (x : ℝ) :
    Integrable (cosineModeProduct i n r x) := by
  have hbare := bareModeProduct_integrable i n r
  have hcos : Integrable (fun t : ℝ =>
      (Real.cos (2 * Real.pi * t * x) : ℂ) *
        bareModeProduct i n r t) := by
    refine hbare.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (Real.cos (2 * Real.pi * t * x) : ℂ))).aestronglyMeasurable
    · filter_upwards [] with t
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  exact hcos

private theorem ccmQKernel_zero_of_ne
    (L : ℝ) {n r : ℤ} (hnr : n ≠ r) :
    Q3.RouteB.ccmQKernel L n r 0 = 0 := by
  simp [Q3.RouteB.ccmQKernel, hnr]

private theorem bareModeProduct_integral_zero_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    ∫ t : ℝ, bareModeProduct i n r t = 0 := by
  have hzero := sourceModeCosineCorrelation_control_offdiag_zero i hnr
  have htwo : (2 : ℂ) * ∫ t : ℝ, bareModeProduct i n r t = 0 := by
    simpa [cosineModeProduct, bareModeProduct] using hzero
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

private theorem sourceKernelModeFiber_eq_cosine_sub_bare
    (i : PairIndex) (n r : ℤ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    sourceArchimedeanKernelModeIntegrand i n r (t, x) =
      (((Real.exp (x / 2) /
          (Real.exp x - Real.exp (-x)) : ℝ) : ℂ) *
        cosineModeProduct i n r x t) -
      (((Real.exp (-x) /
          (Real.exp x - Real.exp (-x)) : ℝ) : ℂ) *
        bareModeProduct i n r t) := by
  have hden : Real.exp x - Real.exp (-x) ≠ 0 := by
    intro h
    have heq : Real.exp x = Real.exp (-x) := sub_eq_zero.mp h
    have hxneg : x = -x := Real.exp_injective heq
    linarith
  unfold sourceArchimedeanKernelModeIntegrand
  unfold sourceArchimedeanRegularizedKernel cosineModeProduct bareModeProduct
  push_cast
  field_simp [hden]

private theorem two_mul_sourceKernelModeFiber_integral_eq_ccmWRIntegrand_or_zero
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ} (hx : 0 < x) :
    2 * ∫ t : ℝ,
        sourceArchimedeanKernelModeIntegrand i n r (t, x) =
      if x ≤ L_m i then
        (Q3.RouteB.ccmWRIntegrand (L_m i) n r x : ℂ)
      else
        0 := by
  let a : ℂ :=
    ((Real.exp (x / 2) /
      (Real.exp x - Real.exp (-x)) : ℝ) : ℂ)
  let b : ℂ :=
    ((Real.exp (-x) /
      (Real.exp x - Real.exp (-x)) : ℝ) : ℂ)
  have hcos := cosineModeProduct_integrable i n r x
  have hbare := bareModeProduct_integrable i n r
  have hfiber :
      (∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n r (t, x)) =
        a * (∫ t : ℝ, cosineModeProduct i n r x t) -
          b * (∫ t : ℝ, bareModeProduct i n r t) := by
    rw [show (fun t : ℝ =>
        sourceArchimedeanKernelModeIntegrand i n r (t, x)) =
      (fun t : ℝ =>
        a * cosineModeProduct i n r x t -
          b * bareModeProduct i n r t) by
        funext t
        exact sourceKernelModeFiber_eq_cosine_sub_bare i n r hx t]
    rw [integral_sub (hcos.const_mul a) (hbare.const_mul b),
      integral_const_mul, integral_const_mul]
  have hbareZero := bareModeProduct_integral_zero_of_ne i hnr
  have hqZero := ccmQKernel_zero_of_ne (L_m i) hnr
  have hcorr :=
    two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
      i n r x hx.le
  have hcorr' :
      2 * ∫ t : ℝ, cosineModeProduct i n r x t =
        if x ≤ L_m i then
          (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ)
        else
          0 := by
    simpa [cosineModeProduct, bareModeProduct, mul_comm, mul_left_comm,
      mul_assoc] using hcorr
  rw [hfiber, hbareZero, mul_zero, sub_zero]
  by_cases hxL : x ≤ L_m i
  · rw [if_pos hxL] at hcorr' ⊢
    unfold Q3.RouteB.ccmWRIntegrand
    rw [hqZero]
    simp only [sub_zero]
    dsimp [a]
    push_cast
    rw [← hcorr']
    ring
  · rw [if_neg hxL] at hcorr' ⊢
    have hcosZero : (∫ t : ℝ, cosineModeProduct i n r x t) = 0 :=
      (mul_eq_zero.mp hcorr').resolve_left (by norm_num)
    rw [hcosZero, mul_zero, mul_zero]

private theorem integral_Ioi_ccmWRIntegrand_or_zero_eq_integral_Ioc
    (i : PairIndex) (n r : ℤ) :
    (∫ x in Ioi 0,
        if x ≤ L_m i then
          (Q3.RouteB.ccmWRIntegrand (L_m i) n r x : ℂ)
        else
          0) =
      ∫ x in Ioc 0 (L_m i),
        (Q3.RouteB.ccmWRIntegrand (L_m i) n r x : ℂ) := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx0 : 0 < x <;> by_cases hxL : x ≤ L_m i <;>
    simp [Set.indicator, hx0, hxL]

private theorem sourceArchimedeanModePairing_eq_neg_two_integral_fibers
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -2 * ∫ x in Ioi 0, ∫ t : ℝ,
        sourceArchimedeanKernelModeIntegrand i n r (t, x) := by
  let c : ℂ :=
    ((-Real.log Real.pi - Real.eulerMascheroniConstant : ℝ) : ℂ)
  have hbare := bareModeProduct_integrable i n r
  have hbareZero := bareModeProduct_integral_zero_of_ne i hnr
  have hjoint := sourceArchimedeanKernelModeIntegrand_integrable i n r
  have hinner : Integrable (fun t : ℝ => ∫ x in Ioi 0,
      sourceArchimedeanKernelModeIntegrand i n r (t, x)) :=
    hjoint.integral_prod_left
  have hswap :
      (∫ t : ℝ, ∫ x in Ioi 0,
          sourceArchimedeanKernelModeIntegrand i n r (t, x)) =
        ∫ x in Ioi 0, ∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n r (t, x) := by
    have hjoint' : Integrable
        (Function.uncurry (fun t x =>
          sourceArchimedeanKernelModeIntegrand i n r (t, x)))
        (volume.prod (volume.restrict (Ioi 0))) := by
      simpa [Function.uncurry] using hjoint
    simpa using (MeasureTheory.integral_integral_swap hjoint')
  have hpoint :
      (fun t : ℝ =>
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t) =
      (fun t : ℝ =>
        c * bareModeProduct i n r t -
          2 * (∫ x in Ioi 0,
            sourceArchimedeanKernelModeIntegrand i n r (t, x))) := by
    funext t
    have hpull :
        (∫ x in Ioi 0,
          sourceArchimedeanKernelModeIntegrand i n r (t, x)) =
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (∫ x in Ioi 0,
              (sourceArchimedeanRegularizedKernel t x : ℂ)) *
            𝓕 (logWindowZeroExtendedMode i r) t := by
      unfold sourceArchimedeanKernelModeIntegrand
      calc
        (∫ x in Ioi 0,
            conj (𝓕 (logWindowZeroExtendedMode i n) t) *
                (sourceArchimedeanRegularizedKernel t x : ℂ) *
              𝓕 (logWindowZeroExtendedMode i r) t) =
            ∫ x in Ioi 0,
              conj (𝓕 (logWindowZeroExtendedMode i n) t) *
                ((sourceArchimedeanRegularizedKernel t x : ℂ) *
                  𝓕 (logWindowZeroExtendedMode i r) t) := by
              apply setIntegral_congr_fun measurableSet_Ioi
              intro x _
              ring
        _ = conj (𝓕 (logWindowZeroExtendedMode i n) t) *
              (∫ x in Ioi 0,
                (sourceArchimedeanRegularizedKernel t x : ℂ) *
                  𝓕 (logWindowZeroExtendedMode i r) t) := by
              rw [integral_const_mul]
        _ = conj (𝓕 (logWindowZeroExtendedMode i n) t) *
              ((∫ x in Ioi 0,
                (sourceArchimedeanRegularizedKernel t x : ℂ)) *
                  𝓕 (logWindowZeroExtendedMode i r) t) := by
              rw [integral_mul_const]
        _ = _ := by ring
    rw [integral_complex_ofReal] at hpull
    rw [sourceArchimedeanMultiplier_eq_regularizedHyperbolicIntegral,
      hpull]
    dsimp [c]
    push_cast
    unfold bareModeProduct
    ring
  unfold sourceArchimedeanModePairing
  rw [hpoint]
  rw [integral_sub (hbare.const_mul c) (hinner.const_mul 2),
    integral_const_mul, integral_const_mul, hbareZero, mul_zero, zero_sub,
    hswap]
  ring

theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
  rw [sourceArchimedeanModePairing_eq_neg_two_integral_fibers i hnr]
  calc
    -2 * (∫ x in Ioi 0, ∫ t : ℝ,
        sourceArchimedeanKernelModeIntegrand i n r (t, x)) =
        -(∫ x in Ioi 0, 2 * ∫ t : ℝ,
          sourceArchimedeanKernelModeIntegrand i n r (t, x)) := by
      rw [integral_const_mul]
      ring
    _ = -(∫ x in Ioi 0,
        if x ≤ L_m i then
          (Q3.RouteB.ccmWRIntegrand (L_m i) n r x : ℂ)
        else
          0) := by
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact two_mul_sourceKernelModeFiber_integral_eq_ccmWRIntegrand_or_zero
        i hnr hx
    _ = -(∫ x in Ioc 0 (L_m i),
        (Q3.RouteB.ccmWRIntegrand (L_m i) n r x : ℂ)) := by
      rw [integral_Ioi_ccmWRIntegrand_or_zero_eq_integral_Ioc]
    _ = -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
      unfold Q3.RouteB.ccmWREntry
      rw [ccmQKernel_zero_of_ne (L_m i) hnr]
      simp only [zero_div, zero_mul, zero_add]
      rw [integral_complex_ofReal]

example (i : PairIndex) :
    sourceArchimedeanModePairing i 0 1 =
      -(Q3.RouteB.ccmWREntry (L_m i) 0 1 : ℂ) := by
  exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i (by norm_num)

example (i : PairIndex) :
    sourceArchimedeanModePairing i 1 0 =
      -(Q3.RouteB.ccmWREntry (L_m i) 1 0 : ℂ) := by
  exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i (by norm_num)

#print axioms sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne

end Q3.RouteB.D0Pstar
