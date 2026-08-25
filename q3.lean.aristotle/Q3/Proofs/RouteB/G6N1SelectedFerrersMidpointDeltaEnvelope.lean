import Q3.Proofs.RouteB.G6N1SelectedFerrersFirstOrderCoefficientEnvelope

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Complex Filter MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Midpoint-delta envelope: from the W3 Abel-limit vector to the pure E_star vector

The consumer vector is `toLp (E_star packet)`, while the committed W4 decay
lives on `selectedFerrersAbelLimitHm`, which carries the extra midpoint term
`(1/2) * packet 0 * sqrt u`.  This node computes the delta coefficient
exactly (a closed-form exponential integral) and produces the first-order
envelope for the pure `E_star` vector with the explicit combined constant
`Budget_k + ‖packet 0‖ * sqrt(lambda_k) / (4π)`.  No claim is made that the
combined constant is eventually bounded; that assembly joins the W5
conditional chain separately.
-/

private theorem w5m_one_lt_lambda (i : PairIndex) : 1 < lambda_m i := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  simpa [lambda_m] using
    (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
      Real.sqrt 1 < Real.sqrt i.m)

private theorem w5m_exp_half_L (i : PairIndex) :
    Real.exp (L_m i / 2) = lambda_m i := by
  have hlam0 : 0 < lambda_m i := lt_trans one_pos (w5m_one_lt_lambda i)
  have hm0 : (0 : ℝ) ≤ (i.m : ℝ) := by positivity
  have hsq : lambda_m i ^ 2 = (i.m : ℝ) := by
    rw [lambda_m]
    exact Real.sq_sqrt hm0
  have hlog : L_m i = 2 * Real.log (lambda_m i) := by
    show logLength i = 2 * Real.log (lambda_m i)
    rw [logLength, ← hsq, Real.log_pow]
    push_cast
    ring
  rw [hlog,
    show (2 : ℝ) * Real.log (lambda_m i) / 2 = Real.log (lambda_m i) by ring]
  exact Real.exp_log hlam0

private theorem w5m_finiteWindow (i : PairIndex) :
    IsFiniteMeasure (dStar.restrict (I_m i)) := by
  have hlambda : 1 < lambda_m i := w5m_one_lt_lambda i
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    apply ne_of_gt
    exact (inv_pos.mpr (zero_lt_one.trans hlambda)).trans_le hu.1
  exact
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩

private theorem w5m_sqrtU_memLp (i : PairIndex) :
    MemLp (fun u : ℝ => (Real.sqrt u : ℂ)) 2 (dStar.restrict (I_m i)) := by
  letI := w5m_finiteWindow i
  apply MemLp.of_bound
    (Continuous.aestronglyMeasurable (by fun_prop))
    (Real.sqrt (lambda_m i))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
  have h1 : ‖((Real.sqrt u : ℝ) : ℂ)‖ = Real.sqrt u := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg u)]
  rw [h1]
  exact Real.sqrt_le_sqrt hu.2

/-- The multiplicative square-root vector in the literal carrier. -/
noncomputable def selectedFerrersSqrtUHm (k : ℕ) :
    H_m (selectedFerrersPreAnchorIndex k) :=
  (w5m_sqrtU_memLp (selectedFerrersPreAnchorIndex k)).toLp _

private theorem w5m_eStar_eq_fun (k : ℕ) :
    E_star (selectedFerrersLemma73SourcePacket k) =
      fun u : ℝ =>
        selectedFerrersAbelLimit k u -
          ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0) *
            (Real.sqrt u : ℂ) := by
  funext u
  rw [selectedFerrersAbelLimit]
  ring

theorem w5m_eStar_memLp (k : ℕ) :
    MemLp (E_star (selectedFerrersLemma73SourcePacket k)) 2
      (dStar.restrict (I_m (selectedFerrersPreAnchorIndex k))) := by
  rw [w5m_eStar_eq_fun k]
  exact (selectedFerrersAbelLimit_memLp k).sub
    ((w5m_sqrtU_memLp (selectedFerrersPreAnchorIndex k)).const_mul _)

/-- The pure `E_star` production vector of the selected Ferrers packet. -/
noncomputable def selectedFerrersEStarHm (k : ℕ) :
    H_m (selectedFerrersPreAnchorIndex k) :=
  (w5m_eStar_memLp k).toLp _

private theorem w5m_eStarHm_eq (k : ℕ) :
    selectedFerrersEStarHm k =
      selectedFerrersAbelLimitHm k -
        ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0) •
          selectedFerrersSqrtUHm k := by
  set i := selectedFerrersPreAnchorIndex k with hi
  set c : ℂ := (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 with hc
  apply MeasureTheory.Lp.ext
  have h1 : (selectedFerrersEStarHm k : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      E_star (selectedFerrersLemma73SourcePacket k) :=
    MemLp.coeFn_toLp (w5m_eStar_memLp k)
  have h2 : (selectedFerrersAbelLimitHm k : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      selectedFerrersAbelLimit k :=
    MemLp.coeFn_toLp (selectedFerrersAbelLimit_memLp k)
  have h3 : (selectedFerrersSqrtUHm k : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ => (Real.sqrt u : ℂ)) :=
    MemLp.coeFn_toLp (w5m_sqrtU_memLp i)
  have hsub := MeasureTheory.Lp.coeFn_sub
    (selectedFerrersAbelLimitHm k) (c • selectedFerrersSqrtUHm k)
  have hsmul := MeasureTheory.Lp.coeFn_smul c (selectedFerrersSqrtUHm k)
  filter_upwards [h1, h2, h3, hsub, hsmul] with u hu1 hu2 hu3 hu4 hu5
  change (selectedFerrersEStarHm k : ℝ → ℂ) u = _
  rw [hu4]
  simp only [Pi.sub_apply]
  rw [hu5]
  simp only [Pi.smul_apply, smul_eq_mul]
  change (selectedFerrersEStarHm k : ℝ → ℂ) u =
    (selectedFerrersAbelLimitHm k : ℝ → ℂ) u -
      c * (selectedFerrersSqrtUHm k : ℝ → ℂ) u
  rw [hu1, hu2, hu3]
  rw [congrFun (w5m_eStar_eq_fun k) u]

/-- Additive-log zero extension of the square-root vector. -/
private theorem w5m_sqrtU_zeroExtension_ae (k : ℕ) :
    sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
        (selectedFerrersSqrtUHm k) =ᵐ[volume]
      Set.indicator
        (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))
        (fun z : ℝ =>
          (Real.sqrt (Real.exp z / lambda_m (selectedFerrersPreAnchorIndex k)) :
            ℂ)) := by
  let i := selectedFerrersPreAnchorIndex k
  let x : H_m i := selectedFerrersSqrtUHm k
  let y := (logWindowL2Equiv i).symm x
  have hxy : logWindowL2Equiv i y = x := by
    exact (logWindowL2Equiv i).apply_symm_apply x
  have hy := coeFn_logWindowL2Equiv i y
  rw [hxy] at hy
  have hycomp := hy.comp_tendsto
    (sourceExpWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  have hylog :
      ∀ᵐ z : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))),
        (x : ℝ → ℂ) (Real.exp z / lambda_m i) = (y : ℝ → ℂ) z := by
    filter_upwards [hycomp] with z hz
    have hlam : lambda_m i ≠ 0 :=
      (lt_trans one_pos (w5m_one_lt_lambda i)).ne'
    have harg : lambda_m i * (Real.exp z / lambda_m i) = Real.exp z := by
      field_simp
    simp only [Function.comp_apply] at hz
    rw [harg, Real.log_exp] at hz
    exact hz
  have hxrep := MemLp.coeFn_toLp (w5m_sqrtU_memLp i)
  change (x : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
    (fun u : ℝ => (Real.sqrt u : ℂ)) at hxrep
  have hxcomp := hxrep.comp_tendsto
    (sourceExpWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  have hinside :
      ∀ᵐ z : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))),
        (y : ℝ → ℂ) z =
          (Real.sqrt (Real.exp z / lambda_m i) : ℂ) := by
    filter_upwards [hylog, hxcomp] with z hyz hxz
    rw [← hyz]
    simpa [Function.comp_apply] using hxz
  have hinside' :
      ∀ᵐ z : ℝ ∂volume,
        z ∈ Set.Icc (0 : ℝ) (L_m i) →
          (y : ℝ → ℂ) z =
            (Real.sqrt (Real.exp z / lambda_m i) : ℂ) := by
    rw [← ae_restrict_iff' measurableSet_Icc]
    exact hinside
  filter_upwards [hinside'] with z hz
  unfold sourceLogWindowZeroExtension
  change Set.indicator (Set.Icc (0 : ℝ) (L_m i)) (y : ℝ → ℂ) z = _
  by_cases hmem : z ∈ Set.Icc (0 : ℝ) (L_m i)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hz hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

private theorem w5m_fourier_congr_ae
    {f g : ℝ → ℂ} (hfg : f =ᵐ[volume] g) (t : ℝ) :
    𝓕 f t = 𝓕 g t := by
  rw [Real.fourier_eq', Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  rw [hx]

/-- Closed-form norm bound for the square-root Fourier value. -/
private theorem w5m_sqrtU_fourier_norm_le (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖𝓕 (sourceLogWindowZeroExtension (selectedFerrersPreAnchorIndex k)
          (selectedFerrersSqrtUHm k))
        ((n : ℝ) / L_m (selectedFerrersPreAnchorIndex k))‖ ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) *
        L_m (selectedFerrersPreAnchorIndex k) /
          (2 * Real.pi * |(n : ℝ)|) := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hL : 0 < L_m i := logLength_pos i
  have hlam1 : 1 < lambda_m i := w5m_one_lt_lambda i
  have hlam0 : 0 < lambda_m i := lt_trans one_pos hlam1
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hn
  set t : ℝ := (n : ℝ) / L_m i with ht
  set c : ℂ := (1 / 2 : ℂ) - 2 * Real.pi * Complex.I * t with hcdef
  have hc_re : c.re = 1 / 2 := by
    simp [hcdef, Complex.sub_re, Complex.mul_re, Complex.mul_im]
  have hc_ne : c ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    rw [hc_re] at this
    norm_num at this
  have hc_im : c.im = -(2 * Real.pi * t) := by
    simp [hcdef, Complex.sub_im, Complex.mul_im, Complex.mul_re]
  have hpoint : ∀ z : ℝ,
      ((Real.sqrt (Real.exp z / lambda_m i) : ℝ) : ℂ) =
        ((Real.sqrt (lambda_m i))⁻¹ : ℂ) * Complex.exp ((z : ℂ) / 2) := by
    intro z
    have hsq : Real.exp (z / 2) ^ 2 = Real.exp z := by
      rw [sq, ← Real.exp_add]
      norm_num
    have hsq2 : (Real.exp (z / 2) / Real.sqrt (lambda_m i)) ^ 2 =
        Real.exp z / lambda_m i := by
      rw [div_pow, hsq, Real.sq_sqrt hlam0.le]
    have hdiv : Real.sqrt (Real.exp z / lambda_m i) =
        Real.exp (z / 2) / Real.sqrt (lambda_m i) := by
      rw [← hsq2, Real.sqrt_sq (by positivity)]
    rw [hdiv]
    push_cast
    ring
  have hfour :
      𝓕 (sourceLogWindowZeroExtension i (selectedFerrersSqrtUHm k)) t =
        𝓕 (Set.indicator (Set.Icc (0 : ℝ) (L_m i))
          (fun z : ℝ => (Real.sqrt (Real.exp z / lambda_m i) : ℂ))) t :=
    w5m_fourier_congr_ae (w5m_sqrtU_zeroExtension_ae k) t
  have hcL : c * ((L_m i : ℝ) : ℂ) =
      ((L_m i / 2 : ℝ) : ℂ) + ((-n : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    rw [hcdef, ht]
    have hLne : ((L_m i : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hL.ne'
    push_cast
    field_simp
    ring
  have hexpcL : Complex.exp (c * ((L_m i : ℝ) : ℂ)) = ((lambda_m i : ℝ) : ℂ) := by
    rw [hcL, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
      ← Complex.ofReal_exp, w5m_exp_half_L i]
  have hintegral :
      𝓕 (Set.indicator (Set.Icc (0 : ℝ) (L_m i))
          (fun z : ℝ => (Real.sqrt (Real.exp z / lambda_m i) : ℂ))) t =
        ((Real.sqrt (lambda_m i))⁻¹ : ℂ) *
          (((( lambda_m i : ℝ) : ℂ) - 1) / c) := by
    rw [Real.fourier_eq']
    have hstep1 :
        (∫ v : ℝ,
          Complex.exp (((-2 * Real.pi * (inner ℝ v t : ℝ) : ℝ) : ℂ) *
              Complex.I) •
            Set.indicator (Set.Icc (0 : ℝ) (L_m i))
              (fun z : ℝ => (Real.sqrt (Real.exp z / lambda_m i) : ℂ)) v) =
        ∫ v : ℝ,
          Set.indicator (Set.Icc (0 : ℝ) (L_m i))
            (fun z : ℝ =>
              ((Real.sqrt (lambda_m i))⁻¹ : ℂ) *
                Complex.exp (c * (z : ℂ))) v := by
      apply integral_congr_ae
      filter_upwards [] with v
      by_cases hmem : v ∈ Set.Icc (0 : ℝ) (L_m i)
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
          smul_eq_mul, hpoint v]
        rw [show
          Complex.exp (((-2 * Real.pi * (inner ℝ v t : ℝ) : ℝ) : ℂ) *
              Complex.I) *
            (((Real.sqrt (lambda_m i))⁻¹ : ℂ) * Complex.exp ((v : ℂ) / 2)) =
          ((Real.sqrt (lambda_m i))⁻¹ : ℂ) *
            (Complex.exp (((-2 * Real.pi * (inner ℝ v t : ℝ) : ℝ) : ℂ) *
                Complex.I) *
              Complex.exp ((v : ℂ) / 2)) from by ring]
        rw [← Complex.exp_add]
        congr 2
        have hip : (inner ℝ v t : ℝ) = t * v := by
          simp [RCLike.inner_apply]
        rw [hip, hcdef]
        push_cast
        ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
          smul_zero]
    rw [hstep1, integral_indicator measurableSet_Icc,
      MeasureTheory.integral_const_mul]
    congr 1
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hL.le,
      integral_exp_mul_complex hc_ne]
    rw [show c * ((0 : ℝ) : ℂ) = 0 by push_cast; ring, Complex.exp_zero, hexpcL]
  rw [hfour, hintegral]
  have h1 : ‖((Real.sqrt (lambda_m i))⁻¹ : ℂ)‖ = (Real.sqrt (lambda_m i))⁻¹ := by
    have hcast : ((Real.sqrt (lambda_m i))⁻¹ : ℂ) =
        (((Real.sqrt (lambda_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have h2 : ‖(((lambda_m i : ℝ) : ℂ) - 1)‖ = lambda_m i - 1 := by
    rw [show (((lambda_m i : ℝ) : ℂ) - 1) = (((lambda_m i - 1 : ℝ)) : ℂ) by
      push_cast; ring]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hc_ne
  have him2 : 2 * Real.pi * |(n : ℝ)| / L_m i ≤ ‖c‖ := by
    have h := Complex.abs_im_le_norm c
    rw [hc_im, ht] at h
    have habs : |(-(2 * Real.pi * ((n : ℝ) / L_m i)))| =
        2 * Real.pi * |(n : ℝ)| / L_m i := by
      rw [abs_neg, abs_mul, abs_div, abs_of_pos hL,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      ring
    rw [habs] at h
    exact h
  rw [norm_mul, norm_div, h1, h2]
  have hstep : (lambda_m i - 1) / ‖c‖ ≤
      (lambda_m i - 1) * (L_m i / (2 * Real.pi * |(n : ℝ)|)) := by
    rw [div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0 : ℝ) ≤ lambda_m i - 1)
    have hpos : (0 : ℝ) < 2 * Real.pi * |(n : ℝ)| / L_m i := by positivity
    have := inv_anti₀ hpos him2
    rwa [inv_div] at this
  calc
    (Real.sqrt (lambda_m i))⁻¹ * ((lambda_m i - 1) / ‖c‖)
        ≤ (Real.sqrt (lambda_m i))⁻¹ *
            ((lambda_m i - 1) * (L_m i / (2 * Real.pi * |(n : ℝ)|))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
    _ = ((Real.sqrt (lambda_m i))⁻¹ * (lambda_m i - 1)) *
          (L_m i / (2 * Real.pi * |(n : ℝ)|)) := by ring
    _ ≤ Real.sqrt (lambda_m i) * (L_m i / (2 * Real.pi * |(n : ℝ)|)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          calc
            (Real.sqrt (lambda_m i))⁻¹ * (lambda_m i - 1)
                ≤ (Real.sqrt (lambda_m i))⁻¹ * lambda_m i :=
                  mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            _ = lambda_m i / Real.sqrt (lambda_m i) := by ring
            _ = Real.sqrt (lambda_m i) := Real.div_sqrt
    _ = Real.sqrt (lambda_m i) * L_m i / (2 * Real.pi * |(n : ℝ)|) := by ring

/-- First-order coefficient bound for the square-root vector. -/
private theorem w5m_sqrtU_coefficient_le (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
        (selectedFerrersSqrtUHm k) n‖ ≤
      Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) *
        Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) /
          (2 * Real.pi * |(n : ℝ)|) := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hL : 0 < L_m i := logLength_pos i
  rw [physicalFourierCoefficient_eq_fourier_sourceLogWindowZeroExtension,
    norm_mul]
  have h1 : ‖((Real.sqrt (L_m i))⁻¹ : ℂ)‖ = (Real.sqrt (L_m i))⁻¹ := by
    have hcast : ((Real.sqrt (L_m i))⁻¹ : ℂ) =
        (((Real.sqrt (L_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  rw [h1]
  have hbound := w5m_sqrtU_fourier_norm_le k n hn
  calc
    (Real.sqrt (L_m i))⁻¹ *
        ‖𝓕 (sourceLogWindowZeroExtension i (selectedFerrersSqrtUHm k))
          ((n : ℝ) / L_m i)‖
        ≤ (Real.sqrt (L_m i))⁻¹ *
            (Real.sqrt (lambda_m i) * L_m i / (2 * Real.pi * |(n : ℝ)|)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = Real.sqrt (lambda_m i) * ((Real.sqrt (L_m i))⁻¹ * L_m i) /
          (2 * Real.pi * |(n : ℝ)|) := by ring
    _ = Real.sqrt (lambda_m i) * Real.sqrt (L_m i) /
          (2 * Real.pi * |(n : ℝ)|) := by
          rw [show (Real.sqrt (L_m i))⁻¹ * L_m i =
              L_m i / Real.sqrt (L_m i) by ring, Real.div_sqrt]

/--
**First-order envelope for the pure `E_star` vector**, with the explicit
combined constant.  Nothing here asserts that the constant is eventually
bounded in `k`.
-/
theorem selectedFerrersEStarHm_physicalCoefficient_le
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) n‖ ≤
      (selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
            (4 * Real.pi)) *
        Real.sqrt (L_m (selectedFerrersPreAnchorIndex k)) / |(n : ℝ)| := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hL : 0 < L_m i := logLength_pos i
  have hnabs : (0 : ℝ) < |(n : ℝ)| := by
    rw [abs_pos]; exact_mod_cast hn
  have hsplit :
      physicalFourierCoefficient i (selectedFerrersEStarHm k) n =
        physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n -
          ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0) *
            physicalFourierCoefficient i (selectedFerrersSqrtUHm k) n := by
    rw [w5m_eStarHm_eq k]
    simp only [physicalFourierCoefficient]
    rw [inner_sub_right, inner_smul_right]
  have habel := selectedFerrersAbelLimitHm_physicalCoefficient_le k n hn
  have hsqrt := w5m_sqrtU_coefficient_le k n hn
  have hhalf :
      ‖(1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0‖ =
        (1 / 2 : ℝ) * ‖selectedFerrersLemma73SourcePacket k 0‖ := by
    rw [norm_mul]
    norm_num
  calc
    ‖physicalFourierCoefficient i (selectedFerrersEStarHm k) n‖
        = ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n -
            ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0) *
              physicalFourierCoefficient i (selectedFerrersSqrtUHm k) n‖ := by
          rw [hsplit]
    _ ≤ ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n‖ +
          ‖((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0) *
            physicalFourierCoefficient i (selectedFerrersSqrtUHm k) n‖ :=
          norm_sub_le _ _
    _ = ‖physicalFourierCoefficient i (selectedFerrersAbelLimitHm k) n‖ +
          (1 / 2 : ℝ) * ‖selectedFerrersLemma73SourcePacket k 0‖ *
            ‖physicalFourierCoefficient i (selectedFerrersSqrtUHm k) n‖ := by
          rw [norm_mul, hhalf]
    _ ≤ selectedFerrersAbelFourierDecayBudget k * Real.sqrt (L_m i) / |(n : ℝ)| +
          (1 / 2 : ℝ) * ‖selectedFerrersLemma73SourcePacket k 0‖ *
            (Real.sqrt (lambda_m i) * Real.sqrt (L_m i) /
              (2 * Real.pi * |(n : ℝ)|)) := by
          apply add_le_add habel
          apply mul_le_mul_of_nonneg_left hsqrt
          positivity
    _ = (selectedFerrersAbelFourierDecayBudget k +
          ‖selectedFerrersLemma73SourcePacket k 0‖ *
            Real.sqrt (lambda_m i) / (4 * Real.pi)) *
          Real.sqrt (L_m i) / |(n : ℝ)| := by
          field_simp
          ring

/-- Squared form, in the exact receiver shape. -/
theorem selectedFerrersEStarHm_physicalCoefficient_sq_le
    (k : ℕ) (n : ℤ) (hn : n ≠ 0) :
    ‖physicalFourierCoefficient (selectedFerrersPreAnchorIndex k)
        (selectedFerrersEStarHm k) n‖ ^ 2 ≤
      (selectedFerrersAbelFourierDecayBudget k +
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
          Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) /
            (4 * Real.pi)) ^ 2 *
        L_m (selectedFerrersPreAnchorIndex k) / (n : ℝ) ^ 2 := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hL : 0 < L_m i := logLength_pos i
  have hfinal := selectedFerrersEStarHm_physicalCoefficient_le k n hn
  set C := selectedFerrersAbelFourierDecayBudget k +
    ‖selectedFerrersLemma73SourcePacket k 0‖ *
      Real.sqrt (lambda_m i) / (4 * Real.pi) with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have := selectedFerrersAbelFourierDecayBudget_nonneg k
    positivity
  have hnn : (0 : ℝ) ≤ ‖physicalFourierCoefficient i
      (selectedFerrersEStarHm k) n‖ := norm_nonneg _
  calc
    ‖physicalFourierCoefficient i (selectedFerrersEStarHm k) n‖ ^ 2
        ≤ (C * Real.sqrt (L_m i) / |(n : ℝ)|) ^ 2 := by
          apply sq_le_sq' _ hfinal
          have : (0 : ℝ) ≤ C * Real.sqrt (L_m i) / |(n : ℝ)| := by positivity
          linarith
    _ = C ^ 2 * L_m i / (n : ℝ) ^ 2 := by
          rw [div_pow, mul_pow, Real.sq_sqrt hL.le, sq_abs]

#print axioms selectedFerrersEStarHm_physicalCoefficient_le
#print axioms selectedFerrersEStarHm_physicalCoefficient_sq_le

end Q3.RouteB.D0Pstar
