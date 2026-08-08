import Q3.Proofs.RouteB.D0PstarSourceArchKernelModeProductL1
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrixN1
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Convolution

noncomputable section

set_option maxHeartbeats 800000

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate Convolution

namespace Q3.RouteB.D0Pstar

private def complexConvolution (f g : ℝ → ℂ) : ℝ → ℂ :=
  MeasureTheory.convolution f g (ContinuousLinearMap.mul ℂ ℂ) volume

private def reflectedConjMode
    (i : PairIndex) (n : ℤ) (x : ℝ) : ℂ :=
  conj (logWindowZeroExtendedMode i n (-x))

private def sourceModeCorrelation
    (i : PairIndex) (n r : ℤ) : ℝ → ℂ :=
  complexConvolution
    (reflectedConjMode i n)
    (logWindowZeroExtendedMode i r)

private theorem logWindowZeroExtendedMode_integrable_for_correlation
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

private theorem reflectedConjMode_integrable
    (i : PairIndex) (n : ℤ) :
    Integrable (reflectedConjMode i n) := by
  have hneg :=
    (logWindowZeroExtendedMode_integrable_for_correlation i n).comp_neg
  simpa [reflectedConjMode] using
    (RCLike.conjLIE.toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp hneg)

private theorem sourceModeCorrelation_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (sourceModeCorrelation i n r) := by
  exact (reflectedConjMode_integrable i n).integrable_convolution
    (ContinuousLinearMap.mul ℂ ℂ)
    (logWindowZeroExtendedMode_integrable_for_correlation i r)

private theorem fourier_convolution_mul
    {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (w : ℝ) :
    𝓕 (complexConvolution f g) w =
      𝓕 f w * 𝓕 g w := by
  let F : ℝ → ℂ := fun x => (Real.fourierChar (-(x * w)) : ℂ) * f x
  let G : ℝ → ℂ := fun x => (Real.fourierChar (-(x * w)) : ℂ) * g x
  have hF : Integrable F := by
    refine hf.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous
        (fun x : ℝ => (Real.fourierChar (-(x * w)) : ℂ))).aestronglyMeasurable
    · filter_upwards [] with x
      simp
  have hG : Integrable G := by
    refine hg.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous
        (fun x : ℝ => (Real.fourierChar (-(x * w)) : ℂ))).aestronglyMeasurable
    · filter_upwards [] with x
      simp
  have hconv :
      (fun x : ℝ =>
          (Real.fourierChar (-(x * w)) : ℂ) *
            complexConvolution f g x) =
        complexConvolution F G := by
    funext x
    rw [complexConvolution, complexConvolution,
      MeasureTheory.convolution_def, MeasureTheory.convolution_def]
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with u
    dsimp [F, G]
    have hchar :
        (Real.fourierChar (-(u * w)) : ℂ) *
            (Real.fourierChar (-((x - u) * w)) : ℂ) =
          (Real.fourierChar (-(x * w)) : ℂ) := by
      rw [← Circle.coe_mul]
      apply congrArg (fun z : Circle => (z : ℂ))
      rw [← Real.fourierChar.map_add_eq_mul]
      congr 1
      ring
    rw [← hchar]
    ring
  rw [Real.fourier_real_eq]
  change (∫ x : ℝ,
      (Real.fourierChar (-(x * w)) : ℂ) *
        complexConvolution f g x) = _
  rw [hconv]
  rw [complexConvolution]
  rw [MeasureTheory.integral_convolution
    (ContinuousLinearMap.mul ℂ ℂ) hF hG]
  change (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * f x) *
      (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g x) = _
  have hfFourier :
      (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * f x) = 𝓕 f w := by
    rw [Real.fourier_real_eq]
    rfl
  have hgFourier :
      (∫ x : ℝ, (Real.fourierChar (-(x * w)) : ℂ) * g x) = 𝓕 g w := by
    rw [Real.fourier_real_eq]
    rfl
  rw [hfFourier, hgFourier]

private theorem fourier_reflectedConjMode
    (i : PairIndex) (n : ℤ) (t : ℝ) :
    𝓕 (reflectedConjMode i n) t =
      conj (𝓕 (logWindowZeroExtendedMode i n) t) := by
  rw [Real.fourier_real_eq, Real.fourier_real_eq]
  change (∫ v : ℝ,
      (Real.fourierChar (-(v * t)) : ℂ) * reflectedConjMode i n v) =
    conj (∫ v : ℝ,
      (Real.fourierChar (-(v * t)) : ℂ) *
        logWindowZeroExtendedMode i n v)
  rw [← MeasureTheory.integral_neg_eq_self
    (fun x : ℝ =>
      (Real.fourierChar (-(x * t)) : ℂ) * reflectedConjMode i n x)
    volume]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [reflectedConjMode, neg_neg, map_mul]
  have harg : -(-x * t) = x * t := by ring
  rw [harg]
  rw [show (Real.fourierChar (x * t) : ℂ) =
      conj (Real.fourierChar (-(x * t)) : ℂ) by
    rw [Real.fourierChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
    simp]

private theorem fourier_sourceModeCorrelation
    (i : PairIndex) (n r : ℤ) (t : ℝ) :
    𝓕 (sourceModeCorrelation i n r) t =
      conj (𝓕 (logWindowZeroExtendedMode i n) t) *
        𝓕 (logWindowZeroExtendedMode i r) t := by
  rw [sourceModeCorrelation, fourier_convolution_mul
    (reflectedConjMode_integrable i n)
    (logWindowZeroExtendedMode_integrable_for_correlation i r)]
  rw [fourier_reflectedConjMode]

private theorem logWindowZeroExtendedMode_measurable
    (i : PairIndex) (n : ℤ) :
    Measurable (logWindowZeroExtendedMode i n) := by
  apply Measurable.indicator
  · fun_prop
  · exact measurableSet_Icc

private theorem norm_logWindowZeroExtendedMode_le
    (i : PairIndex) (n : ℤ) (x : ℝ) :
    ‖logWindowZeroExtendedMode i n x‖ ≤
      (Real.sqrt (L_m i))⁻¹ := by
  by_cases hx : x ∈ Icc (0 : ℝ) (L_m i)
  · simp [logWindowZeroExtendedMode, hx, Complex.norm_exp,
      Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  · simp [logWindowZeroExtendedMode, hx]

private theorem logWindowZeroExtendedMode_continuousAt_off_endpoints
    (i : PairIndex) (n : ℤ) {y : ℝ}
    (hy0 : y ≠ 0) (hyL : y ≠ L_m i) :
    ContinuousAt (logWindowZeroExtendedMode i n) y := by
  let base : ℝ → ℂ := fun x =>
    ((Real.sqrt (L_m i))⁻¹ : ℂ) *
      Complex.exp
        (2 * Real.pi * Complex.I * n * (x / L_m i))
  have hbase : Continuous base := by
    dsimp [base]
    fun_prop
  change ContinuousAt ((Icc (0 : ℝ) (L_m i)).indicator base) y
  by_cases hy : y ∈ Icc (0 : ℝ) (L_m i)
  · have hyPos : 0 < y := lt_of_le_of_ne hy.1 (Ne.symm hy0)
    have hyLt : y < L_m i := lt_of_le_of_ne hy.2 hyL
    refine hbase.continuousAt.congr_of_eventuallyEq ?_
    filter_upwards [Ioo_mem_nhds hyPos hyLt] with z hz
    simp [hz.1.le, hz.2.le]
  · by_cases hyNeg : y < 0
    · have hzero : ContinuousAt (fun _ : ℝ => (0 : ℂ)) y := continuousAt_const
      refine hzero.congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds hyNeg] with z hz
      rw [Set.indicator_of_notMem]
      exact fun hmem => (not_le_of_gt hz) hmem.1
    · have hyNonneg : 0 ≤ y := le_of_not_gt hyNeg
      have hyGt : L_m i < y := by
        have : ¬ y ≤ L_m i := fun hle => hy ⟨hyNonneg, hle⟩
        exact lt_of_not_ge this
      have hzero : ContinuousAt (fun _ : ℝ => (0 : ℂ)) y := continuousAt_const
      refine hzero.congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds hyGt] with z hz
      rw [Set.indicator_of_notMem]
      exact fun hmem => (not_le_of_gt hz) hmem.2

private theorem sourceModeCorrelation_continuous
    (i : PairIndex) (n r : ℤ) :
    Continuous (sourceModeCorrelation i n r) := by
  rw [continuous_iff_continuousAt]
  intro s
  let c : ℝ := (Real.sqrt (L_m i))⁻¹
  let bound : ℝ → ℝ := fun u => c * ‖reflectedConjMode i n u‖
  have hc : 0 ≤ c := by
    dsimp [c]
    positivity
  have hsection : ∀ z : ℝ, Integrable
      (fun u : ℝ => reflectedConjMode i n u *
        logWindowZeroExtendedMode i r (z - u)) := by
    intro z
    refine (reflectedConjMode_integrable i n).mul_bdd (c := c) ?_ ?_
    · exact ((logWindowZeroExtendedMode_measurable i r).comp
        (measurable_const.sub measurable_id)).aestronglyMeasurable
    · filter_upwards [] with u
      exact norm_logWindowZeroExtendedMode_le i r (z - u)
  have hbound : Integrable bound := by
    exact (reflectedConjMode_integrable i n).norm.const_mul c
  have hu0 : ∀ᵐ u : ℝ, u ≠ s := by
    rw [ae_iff]
    simpa using (measure_singleton s : volume ({s} : Set ℝ) = 0)
  have huL : ∀ᵐ u : ℝ, u ≠ s - L_m i := by
    rw [ae_iff]
    simpa using
      (measure_singleton (s - L_m i) :
        volume ({s - L_m i} : Set ℝ) = 0)
  have hcontinuousAE : ∀ᵐ u : ℝ,
      ContinuousAt
        (fun z : ℝ => reflectedConjMode i n u *
          logWindowZeroExtendedMode i r (z - u)) s := by
    filter_upwards [hu0, huL] with u hu0 huL
    have hmode : ContinuousAt (logWindowZeroExtendedMode i r) (s - u) :=
      logWindowZeroExtendedMode_continuousAt_off_endpoints i r
        (sub_ne_zero.mpr (Ne.symm hu0))
        (fun h => huL (by linarith))
    have hsub : ContinuousAt (fun z : ℝ => z - u) s :=
      continuousAt_id.sub continuousAt_const
    have hcomp := ContinuousAt.comp
      (f := fun z : ℝ => z - u) (x := s) hmode hsub
    exact continuousAt_const.mul (by simpa only [Function.comp_apply] using hcomp)
  have hcont := MeasureTheory.continuousAt_of_dominated
    (F := fun z u : ℝ => reflectedConjMode i n u *
      logWindowZeroExtendedMode i r (z - u))
    (bound := bound)
    (Filter.Eventually.of_forall fun z => (hsection z).1)
    (Filter.Eventually.of_forall fun z =>
      Filter.Eventually.of_forall fun u => by
        rw [norm_mul]
        calc
          ‖reflectedConjMode i n u‖ *
              ‖logWindowZeroExtendedMode i r (z - u)‖ ≤
            ‖reflectedConjMode i n u‖ * c := by
              gcongr
              exact norm_logWindowZeroExtendedMode_le i r (z - u)
          _ = bound u := by simp [bound, mul_comm])
    hbound hcontinuousAE
  simpa [sourceModeCorrelation, complexConvolution,
    MeasureTheory.convolution_def] using hcont

private theorem fourier_logWindowZeroExtendedMode_memLp_two_for_correlation
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) 2 volume := by
  have hweighted :=
    vModeLogGrowthEnvelope_mul_fourier_logWindowZeroExtendedMode_memLp i n
  refine hweighted.of_le ?_ ?_
  · exact (VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar (by fun_prop)
      (logWindowZeroExtendedMode_integrable_for_correlation i n)).aestronglyMeasurable
  · filter_upwards [] with t
    have henv : 1 ≤ vModeLogGrowthEnvelope t := by
      unfold vModeLogGrowthEnvelope
      have hlog : 0 ≤ Real.log (2 + |t|) :=
        Real.log_nonneg (by linarith [abs_nonneg t])
      linarith
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) henv)]
    nlinarith [norm_nonneg (𝓕 (logWindowZeroExtendedMode i n) t)]

private theorem conj_fourier_logWindowZeroExtendedMode_memLp_two_for_correlation
    (i : PairIndex) (n : ℤ) :
    MemLp (fun t : ℝ => conj (𝓕 (logWindowZeroExtendedMode i n) t))
      2 volume := by
  have hleft :=
    fourier_logWindowZeroExtendedMode_memLp_two_for_correlation i n
  refine hleft.congr_norm ?_ ?_
  · exact Complex.continuous_conj.comp_aestronglyMeasurable hleft.1
  · filter_upwards [] with t
    exact (norm_conj _).symm

private def modeFourierProduct
    (i : PairIndex) (n r : ℤ) (t : ℝ) : ℂ :=
  conj (𝓕 (logWindowZeroExtendedMode i n) t) *
    𝓕 (logWindowZeroExtendedMode i r) t

private theorem modeFourierProduct_integrable
    (i : PairIndex) (n r : ℤ) :
    Integrable (modeFourierProduct i n r) := by
  have hn :=
    conj_fourier_logWindowZeroExtendedMode_memLp_two_for_correlation i n
  have hr :=
    fourier_logWindowZeroExtendedMode_memLp_two_for_correlation i r
  simpa only [modeFourierProduct, Pi.mul_apply] using hn.integrable_mul hr

private theorem fourierInv_modeFourierProduct_eq_sourceModeCorrelation
    (i : PairIndex) (n r : ℤ) (x : ℝ) :
    𝓕⁻ (modeFourierProduct i n r) x = sourceModeCorrelation i n r x := by
  have hfun : 𝓕 (sourceModeCorrelation i n r) = modeFourierProduct i n r := by
    funext t
    exact fourier_sourceModeCorrelation i n r t
  rw [← hfun]
  exact (sourceModeCorrelation_integrable i n r).fourierInv_fourier_eq
    (by simpa [hfun] using modeFourierProduct_integrable i n r)
    (sourceModeCorrelation_continuous i n r).continuousAt

private theorem two_mul_modeFourierProduct_cosine_integral_eq_correlations
    (i : PairIndex) (n r : ℤ) (x : ℝ) :
    2 * ∫ t : ℝ,
        modeFourierProduct i n r t *
          (Real.cos (2 * Real.pi * t * x) : ℂ) =
      sourceModeCorrelation i n r x + sourceModeCorrelation i n r (-x) := by
  have hprod := modeFourierProduct_integrable i n r
  have hplus : Integrable (fun t : ℝ =>
      (Real.fourierChar (t * x) : ℂ) * modeFourierProduct i n r t) := by
    refine hprod.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (Real.fourierChar (t * x) : ℂ))).aestronglyMeasurable
    · filter_upwards [] with t
      simp
  have hminus : Integrable (fun t : ℝ =>
      (Real.fourierChar (-(t * x)) : ℂ) * modeFourierProduct i n r t) := by
    refine hprod.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop : Continuous
        (fun t : ℝ => (Real.fourierChar (-(t * x)) : ℂ))).aestronglyMeasurable
    · filter_upwards [] with t
      simp
  have hcos : ∀ t : ℝ,
      2 * (Real.cos (2 * Real.pi * (t * x)) : ℂ) =
        (Real.fourierChar (t * x) : ℂ) +
          (Real.fourierChar (-(t * x)) : ℂ) := by
    intro t
    rw [Complex.ofReal_cos]
    unfold Complex.cos
    rw [Real.fourierChar_apply, Real.fourierChar_apply]
    push_cast
    congr 1 <;> congr 1 <;> ring
  calc
    2 * ∫ t : ℝ,
          modeFourierProduct i n r t *
            (Real.cos (2 * Real.pi * t * x) : ℂ) =
        ∫ t : ℝ,
          ((Real.fourierChar (t * x) : ℂ) * modeFourierProduct i n r t +
            (Real.fourierChar (-(t * x)) : ℂ) * modeFourierProduct i n r t) := by
      rw [← MeasureTheory.integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      calc
        2 * (modeFourierProduct i n r t *
            (Real.cos (2 * Real.pi * t * x) : ℂ)) =
          2 * (modeFourierProduct i n r t *
            (Real.cos (2 * Real.pi * (t * x)) : ℂ)) := by
              congr 3
              ring
        _ = modeFourierProduct i n r t *
            (2 * (Real.cos (2 * Real.pi * (t * x)) : ℂ)) := by ring
        _ = modeFourierProduct i n r t *
            ((Real.fourierChar (t * x) : ℂ) +
              (Real.fourierChar (-(t * x)) : ℂ)) := by rw [hcos]
        _ = (Real.fourierChar (t * x) : ℂ) * modeFourierProduct i n r t +
            (Real.fourierChar (-(t * x)) : ℂ) * modeFourierProduct i n r t := by
          ring
    _ = (∫ t : ℝ,
          (Real.fourierChar (t * x) : ℂ) * modeFourierProduct i n r t) +
        ∫ t : ℝ,
          (Real.fourierChar (-(t * x)) : ℂ) * modeFourierProduct i n r t := by
      rw [MeasureTheory.integral_add hplus hminus]
    _ = 𝓕⁻ (modeFourierProduct i n r) x +
        𝓕⁻ (modeFourierProduct i n r) (-x) := by
      rw [Real.fourierInv_eq, Real.fourierInv_eq]
      congr 1 <;> apply integral_congr_ae <;>
        filter_upwards [] with t <;>
        simp [RCLike.inner_apply, Circle.smul_def, smul_eq_mul, mul_comm]
    _ = sourceModeCorrelation i n r x +
        sourceModeCorrelation i n r (-x) := by
      rw [fourierInv_modeFourierProduct_eq_sourceModeCorrelation,
        fourierInv_modeFourierProduct_eq_sourceModeCorrelation]

private theorem sourceModeCorrelation_eq_overlap_integral
    (i : PairIndex) (n r : ℤ) (x : ℝ) :
    sourceModeCorrelation i n r x =
      ∫ u : ℝ,
        conj (logWindowZeroExtendedMode i n u) *
          logWindowZeroExtendedMode i r (x + u) := by
  rw [sourceModeCorrelation, complexConvolution,
    MeasureTheory.convolution_def]
  change (∫ u : ℝ,
      reflectedConjMode i n u *
        logWindowZeroExtendedMode i r (x - u)) = _
  rw [← MeasureTheory.integral_neg_eq_self
    (fun u : ℝ =>
      reflectedConjMode i n u *
        logWindowZeroExtendedMode i r (x - u)) volume]
  apply integral_congr_ae
  filter_upwards [] with u
  simp only [reflectedConjMode, neg_neg]
  congr 2
  ring

private theorem zeroExtendedMode_product_inside
    (i : PairIndex) (n r : ℤ) {u v : ℝ}
    (hu : u ∈ Icc (0 : ℝ) (L_m i))
    (hv : v ∈ Icc (0 : ℝ) (L_m i)) :
    conj (logWindowZeroExtendedMode i n u) *
        logWindowZeroExtendedMode i r v =
      ((L_m i : ℂ)⁻¹) *
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((r : ℝ) * v - (n : ℝ) * u) / L_m i)) := by
  have hsqrtPos : 0 < Real.sqrt (L_m i) :=
    Real.sqrt_pos.mpr (logLength_pos i)
  have hsqrtSq : (Real.sqrt (L_m i)) ^ 2 = L_m i :=
    Real.sq_sqrt (logLength_pos i).le
  have hcoeff :
      conj (((Real.sqrt (L_m i))⁻¹ : ℂ)) *
          (((Real.sqrt (L_m i))⁻¹ : ℂ)) =
        ((L_m i : ℂ)⁻¹) := by
    rw [map_inv₀, Complex.conj_ofReal]
    push_cast
    field_simp [hsqrtPos.ne', (logLength_pos i).ne']
    norm_cast
    nlinarith [hsqrtSq]
  rw [logWindowZeroExtendedMode, Set.indicator_of_mem hu,
    logWindowZeroExtendedMode, Set.indicator_of_mem hv]
  rw [map_mul, ← Complex.exp_conj]
  calc
    conj (((Real.sqrt (L_m i))⁻¹ : ℂ)) *
          Complex.exp
            (conj (2 * Real.pi * Complex.I * n * (u / L_m i))) *
        ((((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * r * (v / L_m i)))) =
      (conj (((Real.sqrt (L_m i))⁻¹ : ℂ)) *
          (((Real.sqrt (L_m i))⁻¹ : ℂ))) *
        (Complex.exp
            (conj (2 * Real.pi * Complex.I * n * (u / L_m i))) *
          Complex.exp
            (2 * Real.pi * Complex.I * r * (v / L_m i))) := by ring
    _ = ((L_m i : ℂ)⁻¹) *
        Complex.exp
          (conj (2 * Real.pi * Complex.I * n * (u / L_m i)) +
            2 * Real.pi * Complex.I * r * (v / L_m i)) := by
      rw [hcoeff, ← Complex.exp_add]
    _ = ((L_m i : ℂ)⁻¹) *
        Complex.exp
          (2 * Real.pi * Complex.I *
            (((r : ℝ) * v - (n : ℝ) * u) / L_m i)) := by
      congr 2
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_I,
        map_intCast, map_div₀, map_ofNat]
      push_cast
      field_simp [(logLength_pos i).ne']
      ring

private def positiveOverlapIntegrand
    (i : PairIndex) (n r : ℤ) (x u : ℝ) : ℂ :=
  ((L_m i : ℂ)⁻¹) *
    Complex.exp
      (2 * Real.pi * Complex.I *
        (((r : ℝ) * (x + u) - (n : ℝ) * u) / L_m i))

private def negativeOverlapIntegrand
    (i : PairIndex) (n r : ℤ) (x u : ℝ) : ℂ :=
  ((L_m i : ℂ)⁻¹) *
    Complex.exp
      (2 * Real.pi * Complex.I *
        (((r : ℝ) * (-x + u) - (n : ℝ) * u) / L_m i))

private theorem sourceModeCorrelation_pos_eq_integral_Icc
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    sourceModeCorrelation i n r x =
      ∫ u : ℝ in Icc 0 (L_m i - x),
        positiveOverlapIntegrand i n r x u := by
  rw [sourceModeCorrelation_eq_overlap_integral]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Icc (0 : ℝ) (L_m i - x)
  · rw [Set.indicator_of_mem hu]
    have hun : u ∈ Icc (0 : ℝ) (L_m i) := by
      exact ⟨hu.1, le_trans hu.2 (sub_le_self _ hx)⟩
    have hur : x + u ∈ Icc (0 : ℝ) (L_m i) := by
      constructor
      · exact add_nonneg hx hu.1
      · linarith [hu.2]
    simpa [positiveOverlapIntegrand] using
      (zeroExtendedMode_product_inside i n r hun hur)
  · rw [Set.indicator_of_notMem hu]
    by_cases hun : u ∈ Icc (0 : ℝ) (L_m i)
    · have huGt : L_m i < x + u := by
        have hnotUpper : ¬ u ≤ L_m i - x := fun hle => hu ⟨hun.1, hle⟩
        linarith
      have hur : x + u ∉ Icc (0 : ℝ) (L_m i) :=
        fun hmem => (not_le_of_gt huGt) hmem.2
      simp [logWindowZeroExtendedMode, hun, hur]
    · simp [logWindowZeroExtendedMode, hun]

private theorem sourceModeCorrelation_neg_eq_integral_Icc
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    sourceModeCorrelation i n r (-x) =
      ∫ u : ℝ in Icc x (L_m i),
        negativeOverlapIntegrand i n r x u := by
  rw [sourceModeCorrelation_eq_overlap_integral]
  rw [← MeasureTheory.integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [] with u
  by_cases hu : u ∈ Icc x (L_m i)
  · rw [Set.indicator_of_mem hu]
    have hun : u ∈ Icc (0 : ℝ) (L_m i) :=
      ⟨le_trans hx hu.1, hu.2⟩
    have hur : -x + u ∈ Icc (0 : ℝ) (L_m i) := by
      constructor
      · linarith [hu.1]
      · linarith [hu.2]
    simpa [negativeOverlapIntegrand, add_comm, add_left_comm, add_assoc] using
      (zeroExtendedMode_product_inside i n r hun hur)
  · rw [Set.indicator_of_notMem hu]
    by_cases hun : u ∈ Icc (0 : ℝ) (L_m i)
    · have huLt : -x + u < 0 := by
        have hnotLower : ¬ x ≤ u := fun hle => hu ⟨hle, hun.2⟩
        linarith
      have hur : -x + u ∉ Icc (0 : ℝ) (L_m i) :=
        fun hmem => (not_le_of_gt huLt) hmem.1
      simp [logWindowZeroExtendedMode, hun, hur]
    · simp [logWindowZeroExtendedMode, hun]

private theorem sourceModeCorrelation_add_neg_eq_zero_of_window_lt
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hxL : L_m i < x) :
    sourceModeCorrelation i n r x +
      sourceModeCorrelation i n r (-x) = 0 := by
  have hpos : sourceModeCorrelation i n r x = 0 := by
    rw [sourceModeCorrelation_eq_overlap_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hun : u ∈ Icc (0 : ℝ) (L_m i)
    · have hur : x + u ∉ Icc (0 : ℝ) (L_m i) := by
        intro hmem
        linarith [hun.1, hmem.2]
      simp [logWindowZeroExtendedMode, hun, hur]
    · simp [logWindowZeroExtendedMode, hun]
  have hneg : sourceModeCorrelation i n r (-x) = 0 := by
    rw [sourceModeCorrelation_eq_overlap_integral]
    apply integral_eq_zero_of_ae
    filter_upwards [] with u
    by_cases hun : u ∈ Icc (0 : ℝ) (L_m i)
    · have hur : -x + u ∉ Icc (0 : ℝ) (L_m i) := by
        intro hmem
        linarith [hun.2, hmem.1]
      simp [logWindowZeroExtendedMode, hun, hur]
    · simp [logWindowZeroExtendedMode, hun]
  rw [hpos, hneg, add_zero]

private theorem positiveOverlapIntegral_diag
    (i : PairIndex) (n : ℤ) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc 0 (L_m i - x),
        positiveOverlapIntegrand i n n x u) =
      (((L_m i - x) / L_m i : ℝ) : ℂ) *
        Complex.exp
          (2 * Real.pi * Complex.I * n * (x / L_m i)) := by
  have hinterval : 0 ≤ L_m i - x := sub_nonneg.mpr hxL
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hinterval]
  have hfun : positiveOverlapIntegrand i n n x =
      fun _ : ℝ =>
        ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (2 * Real.pi * Complex.I * n * (x / L_m i)) := by
    funext u
    unfold positiveOverlapIntegrand
    congr 2
    push_cast
    field_simp [(logLength_pos i).ne']
    ring
  rw [hfun, intervalIntegral.integral_const]
  rw [Complex.real_smul]
  push_cast
  field_simp [(logLength_pos i).ne']
  ring

private theorem negativeOverlapIntegral_diag
    (i : PairIndex) (n : ℤ) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc x (L_m i),
        negativeOverlapIntegrand i n n x u) =
      (((L_m i - x) / L_m i : ℝ) : ℂ) *
        Complex.exp
          (-(2 * Real.pi * Complex.I * n * (x / L_m i))) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hxL]
  have hfun : negativeOverlapIntegrand i n n x =
      fun _ : ℝ =>
        ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (-(2 * Real.pi * Complex.I * n * (x / L_m i))) := by
    funext u
    unfold negativeOverlapIntegrand
    congr 2
    push_cast
    field_simp [(logLength_pos i).ne']
    ring
  rw [hfun, intervalIntegral.integral_const]
  rw [Complex.real_smul]
  push_cast
  field_simp [(logLength_pos i).ne']

private theorem sourceModeCorrelation_add_neg_diag_eq_ccmQKernel
    (i : PairIndex) (n : ℤ) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    sourceModeCorrelation i n n x +
        sourceModeCorrelation i n n (-x) =
      (Q3.RouteB.ccmQKernel (L_m i) n n x : ℂ) := by
  rw [sourceModeCorrelation_pos_eq_integral_Icc i n n hx hxL,
    sourceModeCorrelation_neg_eq_integral_Icc i n n hx hxL,
    positiveOverlapIntegral_diag i n hxL,
    negativeOverlapIntegral_diag i n hxL]
  rw [Q3.RouteB.ccmQKernel, if_pos rfl]
  push_cast
  unfold Complex.cos
  have hphase :
      (2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) / (L_m i : ℂ)) * Complex.I =
        2 * Real.pi * Complex.I * n * (x / L_m i) := by
    field_simp [(logLength_pos i).ne']
  have hphaseNeg :
      (-(2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) / (L_m i : ℂ))) * Complex.I =
        -(2 * Real.pi * Complex.I * n * (x / L_m i)) := by
    field_simp [(logLength_pos i).ne']
  rw [hphase, hphaseNeg]
  ring

private theorem integral_Icc_const_mul_exp_mul
    {a b : ℝ} {C A : ℂ} (hab : a ≤ b) (hA : A ≠ 0) :
    (∫ u : ℝ in Icc a b, C * Complex.exp (A * u)) =
      C * ((Complex.exp (A * b) - Complex.exp (A * a)) / A) := by
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le hab]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_exp_mul_complex hA]

private def overlapFrequency
    (i : PairIndex) (n r : ℤ) : ℂ :=
  2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ)

private def positiveOverlapCoefficient
    (i : PairIndex) (r : ℤ) (x : ℝ) : ℂ :=
  ((L_m i : ℂ)⁻¹) *
    Complex.exp
      (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) / (L_m i : ℂ))

private def negativeOverlapCoefficient
    (i : PairIndex) (r : ℤ) (x : ℝ) : ℂ :=
  ((L_m i : ℂ)⁻¹) *
    Complex.exp
      (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) / (L_m i : ℂ)))

private theorem overlapFrequency_ne_zero
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    overlapFrequency i n r ≠ 0 := by
  unfold overlapFrequency
  have hdiff : (r : ℂ) - (n : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnr))
  exact div_ne_zero
    (mul_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
        Complex.I_ne_zero)
      hdiff)
    (Complex.ofReal_ne_zero.mpr (logLength_pos i).ne')

private theorem positiveOverlapIntegral_offdiag_raw
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc 0 (L_m i - x),
        positiveOverlapIntegrand i n r x u) =
      positiveOverlapCoefficient i r x *
        ((Complex.exp
            (overlapFrequency i n r * (L_m i - x)) -
          Complex.exp (overlapFrequency i n r * 0)) /
        overlapFrequency i n r) := by
  have hfun : positiveOverlapIntegrand i n r x =
      fun u : ℝ => positiveOverlapCoefficient i r x *
        Complex.exp (overlapFrequency i n r * u) := by
    funext u
    unfold positiveOverlapIntegrand positiveOverlapCoefficient overlapFrequency
    calc
      ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((r : ℝ) * (x + u) - (n : ℝ) * u) / L_m i)) =
        ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) / (L_m i : ℂ) +
              (2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ)) /
                (L_m i : ℂ)) * (u : ℂ)) := by
          congr 2
          push_cast
          field_simp [(logLength_pos i).ne']
          ring
      _ = (((L_m i : ℂ)⁻¹) *
            Complex.exp
              (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) / (L_m i : ℂ))) *
          Complex.exp
            ((2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ)) /
              (L_m i : ℂ)) * (u : ℂ)) := by
        rw [Complex.exp_add]
        ring
  rw [hfun]
  simpa only [Complex.ofReal_sub, Complex.ofReal_zero] using
    (integral_Icc_const_mul_exp_mul
      (C := positiveOverlapCoefficient i r x)
      (A := overlapFrequency i n r)
      (sub_nonneg.mpr hxL) (overlapFrequency_ne_zero i hnr))

private theorem negativeOverlapIntegral_offdiag_raw
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc x (L_m i),
        negativeOverlapIntegrand i n r x u) =
      negativeOverlapCoefficient i r x *
        ((Complex.exp
            (overlapFrequency i n r * L_m i) -
          Complex.exp (overlapFrequency i n r * x)) /
        overlapFrequency i n r) := by
  have hfun : negativeOverlapIntegrand i n r x =
      fun u : ℝ => negativeOverlapCoefficient i r x *
        Complex.exp (overlapFrequency i n r * u) := by
    funext u
    unfold negativeOverlapIntegrand negativeOverlapCoefficient overlapFrequency
    calc
      ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (2 * Real.pi * Complex.I *
              (((r : ℝ) * (-x + u) - (n : ℝ) * u) / L_m i)) =
        ((L_m i : ℂ)⁻¹) *
          Complex.exp
            (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) / (L_m i : ℂ)) +
              (2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ)) /
                (L_m i : ℂ)) * (u : ℂ)) := by
          congr 2
          push_cast
          field_simp [(logLength_pos i).ne']
          ring
      _ = (((L_m i : ℂ)⁻¹) *
            Complex.exp
              (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
                (L_m i : ℂ)))) *
          Complex.exp
            ((2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ)) /
              (L_m i : ℂ)) * (u : ℂ)) := by
        rw [Complex.exp_add]
        ring
  rw [hfun]
  simpa only using
    (integral_Icc_const_mul_exp_mul
      (C := negativeOverlapCoefficient i r x)
      (A := overlapFrequency i n r)
      hxL (overlapFrequency_ne_zero i hnr))

private theorem exp_overlapFrequency_mul_logLength_eq_one
    (i : PairIndex) (n r : ℤ) :
    Complex.exp (overlapFrequency i n r * L_m i) = 1 := by
  have hphase :
      overlapFrequency i n r * (L_m i : ℂ) =
        ((r - n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold overlapFrequency
    push_cast
    field_simp [(logLength_pos i).ne']
  rw [hphase]
  exact Complex.exp_int_mul_two_pi_mul_I (r - n)

private theorem positiveOverlapIntegral_offdiag
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc 0 (L_m i - x),
        positiveOverlapIntegrand i n r x u) =
      (Complex.exp
          (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) -
        Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) /
        (2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ))) := by
  rw [positiveOverlapIntegral_offdiag_raw i hnr hxL]
  have hshift :
      Complex.exp (overlapFrequency i n r * (L_m i - x)) =
        Complex.exp (-(overlapFrequency i n r * x)) := by
    change
      Complex.exp
          (overlapFrequency i n r * ((L_m i : ℂ) - (x : ℂ))) =
        Complex.exp (-(overlapFrequency i n r * (x : ℂ)))
    have harg :
        overlapFrequency i n r * ((L_m i : ℂ) - (x : ℂ)) =
          overlapFrequency i n r * (L_m i : ℂ) +
            (-(overlapFrequency i n r * (x : ℂ))) := by
      ring
    rw [harg, Complex.exp_add,
      exp_overlapFrequency_mul_logLength_eq_one, one_mul]
  rw [hshift]
  simp only [mul_zero, Complex.exp_zero, sub_zero]
  have hcombine :
      Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) *
        Complex.exp (-(overlapFrequency i n r * (x : ℂ))) =
      Complex.exp
          (2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    unfold overlapFrequency
    field_simp [(logLength_pos i).ne']
    ring
  unfold positiveOverlapCoefficient overlapFrequency
  have hdiff : (r : ℂ) - (n : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnr))
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero,
    (logLength_pos i).ne', hdiff]
  have hcombine_norm :
      Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) *
        Complex.exp
          (-(2 * Real.pi * Complex.I * (x : ℂ) *
            ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ))) =
      Complex.exp
          (2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) /
            (L_m i : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp [(logLength_pos i).ne']
    ring
  calc
    Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) *
        (Complex.exp
            (-(2 * Real.pi * Complex.I * (x : ℂ) *
              ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ))) - 1) =
      Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) *
          Complex.exp
            (-(2 * Real.pi * Complex.I * (x : ℂ) *
              ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ))) -
        Complex.exp
          (2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ)) := by ring
    _ = _ := by rw [hcombine_norm]

private theorem negativeOverlapIntegral_offdiag
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hxL : x ≤ L_m i) :
    (∫ u : ℝ in Icc x (L_m i),
        negativeOverlapIntegrand i n r x u) =
      (Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) -
        Complex.exp
          (-(2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
            (L_m i : ℂ)))) /
        (2 * Real.pi * Complex.I * ((r : ℂ) - (n : ℂ))) := by
  rw [negativeOverlapIntegral_offdiag_raw i hnr hxL]
  rw [exp_overlapFrequency_mul_logLength_eq_one]
  have hcombine :
      Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) *
        Complex.exp (overlapFrequency i n r * (x : ℂ)) =
      Complex.exp
          (-(2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    unfold overlapFrequency
    field_simp [(logLength_pos i).ne']
    ring
  unfold negativeOverlapCoefficient overlapFrequency
  have hdiff : (r : ℂ) - (n : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnr))
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero,
    (logLength_pos i).ne', hdiff]
  have hcombine_norm :
      Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) *
        Complex.exp
          (2 * Real.pi * Complex.I * (x : ℂ) *
            ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ)) =
      Complex.exp
          (-(2 * Real.pi * Complex.I * (x : ℂ) * (n : ℂ) /
            (L_m i : ℂ))) := by
    rw [← Complex.exp_add]
    congr 1
    field_simp [(logLength_pos i).ne']
    ring
  calc
    Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) *
        (1 - Complex.exp
          (2 * Real.pi * Complex.I * (x : ℂ) *
            ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ))) =
      Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) -
        Complex.exp
          (-(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
            (L_m i : ℂ))) *
          Complex.exp
            (2 * Real.pi * Complex.I * (x : ℂ) *
              ((r : ℂ) - (n : ℂ)) / (L_m i : ℂ)) := by ring
    _ = _ := by rw [hcombine_norm]

private theorem sourceModeCorrelation_add_neg_offdiag_eq_ccmQKernel
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    sourceModeCorrelation i n r x +
        sourceModeCorrelation i n r (-x) =
      (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) := by
  rw [sourceModeCorrelation_pos_eq_integral_Icc i n r hx hxL,
    sourceModeCorrelation_neg_eq_integral_Icc i n r hx hxL,
    positiveOverlapIntegral_offdiag i hnr hxL,
    negativeOverlapIntegral_offdiag i hnr hxL]
  rw [Q3.RouteB.ccmQKernel, if_neg hnr]
  push_cast
  unfold Complex.sin
  have hnPos :
      (2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) /
          (L_m i : ℂ)) * Complex.I =
        2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
          (L_m i : ℂ) := by
    field_simp [(logLength_pos i).ne']
  have hrPos :
      (2 * (Real.pi : ℂ) * (r : ℂ) * (x : ℂ) /
          (L_m i : ℂ)) * Complex.I =
        2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
          (L_m i : ℂ) := by
    field_simp [(logLength_pos i).ne']
  have hnNeg :
      (-(2 * (Real.pi : ℂ) * (n : ℂ) * (x : ℂ) /
          (L_m i : ℂ))) * Complex.I =
        -(2 * Real.pi * Complex.I * (n : ℂ) * (x : ℂ) /
          (L_m i : ℂ)) := by
    field_simp [(logLength_pos i).ne']
  have hrNeg :
      (-(2 * (Real.pi : ℂ) * (r : ℂ) * (x : ℂ) /
          (L_m i : ℂ))) * Complex.I =
        -(2 * Real.pi * Complex.I * (r : ℂ) * (x : ℂ) /
          (L_m i : ℂ)) := by
    field_simp [(logLength_pos i).ne']
  rw [hnPos, hrPos, hnNeg, hrNeg]
  have hnrC : (n : ℂ) - (r : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hnr)
  have hrnC : (r : ℂ) - (n : ℂ) ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hnr))
  field_simp [Complex.I_ne_zero, Real.pi_ne_zero, hnrC, hrnC]
  rw [Complex.I_sq]
  ring

private theorem sourceModeCorrelation_add_neg_eq_ccmQKernel
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    sourceModeCorrelation i n r x +
        sourceModeCorrelation i n r (-x) =
      (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ) := by
  by_cases hnr : n = r
  · subst r
    exact sourceModeCorrelation_add_neg_diag_eq_ccmQKernel i n hx hxL
  · exact sourceModeCorrelation_add_neg_offdiag_eq_ccmQKernel i hnr hx hxL

theorem two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    (i : PairIndex) (n r : ℤ) (x : ℝ) (hx : 0 ≤ x) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t
      =
        if x ≤ L_m i then
          (Q3.RouteB.ccmQKernel (L_m i) n r x : ℂ)
        else
          0 := by
  have hintegral :
      (∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (Real.cos (2 * Real.pi * t * x) : ℂ) *
            𝓕 (logWindowZeroExtendedMode i r) t) =
        ∫ t : ℝ,
          modeFourierProduct i n r t *
            (Real.cos (2 * Real.pi * t * x) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [] with t
    unfold modeFourierProduct
    ring
  rw [hintegral,
    two_mul_modeFourierProduct_cosine_integral_eq_correlations]
  by_cases hxL : x ≤ L_m i
  · rw [if_pos hxL]
    exact sourceModeCorrelation_add_neg_eq_ccmQKernel i n r hx hxL
  · rw [if_neg hxL]
    exact sourceModeCorrelation_add_neg_eq_zero_of_window_lt i n r
      (lt_of_not_ge hxL)

theorem sourceModeCosineCorrelation_control_diag_zero
    (i : PairIndex) (n : ℤ) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * 0) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i n) t = 2 := by
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n n 0 le_rfl]
  simp [Q3.RouteB.ccmQKernel, (logLength_pos i).ne',
    le_of_lt (logLength_pos i)]

theorem sourceModeCosineCorrelation_control_offdiag_zero
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * 0) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0 := by
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n r 0 le_rfl]
  simp [Q3.RouteB.ccmQKernel, hnr, (logLength_pos i).ne']

theorem sourceModeCosineCorrelation_control_offdiag_inside
    (i : PairIndex) {n r : ℤ} (hnr : n ≠ r) {x : ℝ}
    (hx : 0 ≤ x) (hxL : x ≤ L_m i) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t =
      (((Real.sin (2 * Real.pi * (r : ℝ) * x / L_m i) -
          Real.sin (2 * Real.pi * (n : ℝ) * x / L_m i)) /
        (Real.pi * ((n : ℝ) - (r : ℝ))) : ℝ) : ℂ) := by
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n r x hx, if_pos hxL, Q3.RouteB.ccmQKernel, if_neg hnr]

theorem sourceModeCosineCorrelation_control_right_boundary
    (i : PairIndex) (n r : ℤ) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * L_m i) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0 := by
  have hintegral :
      (∫ t : ℝ,
          conj (𝓕 (logWindowZeroExtendedMode i n) t) *
            (Real.cos (2 * Real.pi * t * L_m i) : ℂ) *
            𝓕 (logWindowZeroExtendedMode i r) t) =
        ∫ t : ℝ,
          modeFourierProduct i n r t *
            (Real.cos (2 * Real.pi * t * L_m i) : ℂ) := by
    apply integral_congr_ae
    filter_upwards [] with t
    unfold modeFourierProduct
    ring
  rw [hintegral,
    two_mul_modeFourierProduct_cosine_integral_eq_correlations,
    sourceModeCorrelation_pos_eq_integral_Icc i n r
      (le_of_lt (logLength_pos i)) le_rfl,
    sourceModeCorrelation_neg_eq_integral_Icc i n r
      (le_of_lt (logLength_pos i)) le_rfl]
  simp

theorem sourceModeCosineCorrelation_control_outside_zero
    (i : PairIndex) (n r : ℤ) {x : ℝ}
    (hxL : L_m i < x) :
    2 * ∫ t : ℝ,
        conj (𝓕 (logWindowZeroExtendedMode i n) t) *
          (Real.cos (2 * Real.pi * t * x) : ℂ) *
          𝓕 (logWindowZeroExtendedMode i r) t = 0 := by
  rw [two_mul_sourceModeCosineCorrelation_eq_ccmQKernel_or_zero
    i n r x (le_trans (le_of_lt (logLength_pos i)) (le_of_lt hxL))]
  simp [not_le_of_gt hxL]


end Q3.RouteB.D0Pstar
