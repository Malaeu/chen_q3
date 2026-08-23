import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry
import Q3.Proofs.RouteB.D0LogWindowVNMCompletenessBridge

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Complex Filter MeasureTheory Set
open scoped BigOperators Topology FourierTransform RealInnerProductSpace ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# H2a.4.1b.3c.1.10 — the source log-window Fourier integral crosswalk

Task `H2A_4_1B_3C_1_10_SOURCE_LOG_WINDOW_FOURIER_ACTUAL_INTEGRAL_LEAN` of
verdict `4fa4a981`.

The synthesized `sourceLogWindowFourierL2Isometry` is identified almost
everywhere with the ordinary Fourier integral of the additive log-window
zero extension of any `H_m` vector.  The proof uses only completeness of
the literal `V_n_m` basis, the finite measure of the additive window
`[0, L_m]` (`L²→L¹` with the exact constant `√(L_m)`), the `L¹→C⁰` bound
of the pinned Fourier integral, and an almost-everywhere subsequence
extracted from `L²` convergence.  No Plancherel-type import is used.

The C04 coordinate firewall is kept: the Fourier integral acts on the
ADDITIVE log-window object `(logWindowL2Equiv i).symm x`, zero-extended by
the indicator of `Icc 0 (L_m i)` — never on the multiplicative `I_m`
representative.

The mandatory plant records that one-mode agreement without the complete
basis does not identify two maps.

LEDGER:
  CLOSES: [SOURCE_LOG_WINDOW_FOURIER_L2_ISOMETRY_ACTUAL_FOURIER_CROSSWALK]
  OPENS:  []
-/

/-! ## The mandatory plant -/

/-- **Plant.**  Agreement on one basis vector does not identify two linear
maps: two maps on `Fin 2 → ℂ` agree on the first coordinate vector and
differ on the second.  The dense-limit argument in the main theorem is
load-bearing; a modewise computation alone would not suffice. -/
private theorem one_mode_agreement_without_complete_basis_does_not_identify_maps_plant :
    ∃ f g : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ),
      f (fun j => if j = 0 then 1 else 0) =
          g (fun j => if j = 0 then 1 else 0) ∧
        f ≠ g := by
  refine ⟨LinearMap.id, ?_, ?_, ?_⟩
  · exact
      { toFun := fun v j => if j = 0 then v 0 else 0
        map_add' := by
          intro v w
          funext j
          by_cases hj : j = 0 <;> simp [hj]
        map_smul' := by
          intro c v
          funext j
          by_cases hj : j = 0 <;> simp [hj] }
  · funext j
    by_cases hj : j = 0 <;> simp [hj, LinearMap.id_apply]
  · intro hcontra
    have h1 :
        (LinearMap.id (R := ℂ) (M := Fin 2 → ℂ))
            (fun j => if j = 1 then 1 else 0) =
          (fun j : Fin 2 => if j = 1 then (1 : ℂ) else 0) := rfl
    have h2 := congrArg
      (fun F : (Fin 2 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) =>
        F (fun j => if j = 1 then (1 : ℂ) else 0) 1) hcontra
    simp at h2

/-! ## The additive zero extension -/

/-- **The additive log-window zero extension** of an `H_m` vector: the
chosen representative of `(logWindowL2Equiv i).symm x`, extended by zero
outside the additive window `[0, L_m i]`. -/
noncomputable def sourceLogWindowZeroExtension
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  Set.indicator (Set.Icc (0 : ℝ) (L_m i))
    (((logWindowL2Equiv i).symm x :
        MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)

/-! ## Finite measure of the additive window -/

private theorem additiveWindow_isFiniteMeasure (i : PairIndex) :
    IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  constructor
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.ofReal_lt_top

private theorem additiveWindow_measure_univ (i : PairIndex) :
    (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) Set.univ =
      ENNReal.ofReal (L_m i) := by
  rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]

/-! ## Integrability -/

private theorem restrictL2_integrable
    (i : PairIndex)
    (f : MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) :
    Integrable (f : ℝ → ℂ)
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  letI := additiveWindow_isFiniteMeasure i
  exact (MeasureTheory.Lp.memLp f).integrable (by norm_num)

theorem sourceLogWindowZeroExtension_integrable
    (i : PairIndex) (x : H_m i) :
    Integrable (sourceLogWindowZeroExtension i x) volume := by
  unfold sourceLogWindowZeroExtension
  exact IntegrableOn.integrable_indicator
    (restrictL2_integrable i ((logWindowL2Equiv i).symm x))
    measurableSet_Icc

/-! ## The `L²→L¹` estimate with the exact constant `√(L_m)` -/

private theorem restrictL2_l1_le
    (i : PairIndex)
    (f : MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) :
    ∫ t : ℝ, ‖(f : ℝ → ℂ) t‖
        ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))) ≤
      Real.sqrt (L_m i) * ‖f‖ := by
  letI := additiveWindow_isFiniteMeasure i
  have hmeas : AEStronglyMeasurable (f : ℝ → ℂ)
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
    (MeasureTheory.Lp.memLp f).aestronglyMeasurable
  have h1 : ∫ t : ℝ, ‖(f : ℝ → ℂ) t‖
        ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))) =
      (eLpNorm (f : ℝ → ℂ) 1
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))).toReal := by
    rw [integral_norm_eq_lintegral_enorm hmeas,
      eLpNorm_one_eq_lintegral_enorm]
  have hle : eLpNorm (f : ℝ → ℂ) 1
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) ≤
      eLpNorm (f : ℝ → ℂ) 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) *
        ((volume.restrict (Set.Icc (0 : ℝ) (L_m i))) Set.univ) ^
          ((1 : ℝ) / 1 - 1 / 2) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) hmeas
  have hfin2 : eLpNorm (f : ℝ → ℂ) 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) < ⊤ :=
    (MeasureTheory.Lp.memLp f).2
  have hμfin :
      (((volume.restrict (Set.Icc (0 : ℝ) (L_m i))) Set.univ) ^
        ((1 : ℝ) / 1 - 1 / 2)) < ⊤ := by
    rw [additiveWindow_measure_univ]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hrhs_fin :
      eLpNorm (f : ℝ → ℂ) 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) *
        ((volume.restrict (Set.Icc (0 : ℝ) (L_m i))) Set.univ) ^
          ((1 : ℝ) / 1 - 1 / 2) < ⊤ :=
    ENNReal.mul_lt_top hfin2 hμfin
  rw [h1]
  refine le_trans (ENNReal.toReal_mono hrhs_fin.ne hle) ?_
  rw [ENNReal.toReal_mul]
  have hnorm : (eLpNorm (f : ℝ → ℂ) 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))).toReal = ‖f‖ := by
    rw [MeasureTheory.Lp.norm_def]
  have hmeasval :
      ((((volume.restrict (Set.Icc (0 : ℝ) (L_m i))) Set.univ) ^
        ((1 : ℝ) / 1 - 1 / 2)).toReal) =
        Real.sqrt (L_m i) := by
    rw [additiveWindow_measure_univ, ← ENNReal.toReal_rpow,
      ENNReal.toReal_ofReal (logLength_pos i).le]
    rw [show (1 : ℝ) / 1 - 1 / 2 = 1 / (2 : ℝ) by norm_num]
    exact (Real.sqrt_eq_rpow (L_m i)).symm
  rw [hnorm, hmeasval, mul_comm]

/-- Almost-everywhere representative of a finite `Lp` sum (no ready-made
`Lp.coeFn_sum` exists at the pinned Mathlib; finite induction suffices). -/
private theorem lp_coeFn_finsetSum
    {μ : MeasureTheory.Measure ℝ} (F : Finset ℤ)
    (f : ℤ → MeasureTheory.Lp ℂ 2 μ) :
    ((∑ n ∈ F, f n : MeasureTheory.Lp ℂ 2 μ) : ℝ → ℂ)
      =ᵐ[μ] (fun x => ∑ n ∈ F, (f n : ℝ → ℂ) x) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      exact MeasureTheory.Lp.coeFn_zero ℂ 2 μ
  | insert n s hns ih =>
      rw [Finset.sum_insert hns]
      have hadd := MeasureTheory.Lp.coeFn_add (f n) (∑ m ∈ s, f m)
      filter_upwards [hadd, ih] with x hx1 hx2
      rw [Finset.sum_insert hns, hx1]
      simp only [Pi.add_apply]
      rw [hx2]

/-! ## Elementary Fourier-integral facts (self-contained) -/

private theorem fourier_kernel_smul_integrable
    {h : ℝ → ℂ} (hh : Integrable h volume) (t : ℝ) :
    Integrable
      (fun x : ℝ =>
        Complex.exp (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
          h x) volume := by
  refine Integrable.mono' hh.norm ?_ ?_
  · exact ((Complex.continuous_exp.comp (by fun_prop)).aestronglyMeasurable.mul
      hh.aestronglyMeasurable)
  · filter_upwards [] with x
    rw [norm_mul]
    have hexp : ‖Complex.exp
        (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I)‖ = 1 := by
      rw [Complex.norm_exp]
      simp
    rw [hexp, one_mul]

private theorem fourier_apply_eq
    (h : ℝ → ℂ) (t : ℝ) :
    𝓕 h t =
      ∫ x : ℝ,
        Complex.exp (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
          h x := by
  rw [Real.fourier_eq']
  apply integral_congr_ae
  filter_upwards [] with x
  rw [smul_eq_mul]
  congr 2
  push_cast
  simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial]
  push_cast
  ring

/-- The Fourier integral does not see almost-everywhere modifications. -/
private theorem fourier_congr_ae
    {h g : ℝ → ℂ} (hg : h =ᵐ[volume] g) (t : ℝ) :
    𝓕 h t = 𝓕 g t := by
  rw [fourier_apply_eq h t, fourier_apply_eq g t]
  apply integral_congr_ae
  filter_upwards [hg] with x hx
  rw [hx]

/-- Fourier difference bound: `‖𝓕h t − 𝓕g t‖ ≤ ∫‖h−g‖`. -/
private theorem fourier_sub_norm_le
    {h g : ℝ → ℂ} (hh : Integrable h volume) (hg : Integrable g volume)
    (t : ℝ) :
    ‖𝓕 h t - 𝓕 g t‖ ≤ ∫ x : ℝ, ‖h x - g x‖ ∂volume := by
  rw [fourier_apply_eq h t, fourier_apply_eq g t]
  rw [← integral_sub (fourier_kernel_smul_integrable hh t)
    (fourier_kernel_smul_integrable hg t)]
  refine le_trans (norm_integral_le_integral_norm _) (le_of_eq ?_)
  apply integral_congr_ae
  filter_upwards [] with x
  have hker :
      Complex.exp (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) * h x -
        Complex.exp
          (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) * g x =
        Complex.exp
          (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
          (h x - g x) := by
    ring
  rw [hker, norm_mul]
  have hexp : ‖Complex.exp
      (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hexp, one_mul]

/-- Fourier linearity over a finite combination of integrable functions. -/
private theorem fourier_finsetSum
    (F : Finset ℤ) (c : ℤ → ℂ) (φ : ℤ → ℝ → ℂ)
    (hφ : ∀ n ∈ F, Integrable (φ n) volume) (t : ℝ) :
    𝓕 (fun x => ∑ n ∈ F, c n • φ n x) t =
      ∑ n ∈ F, c n • 𝓕 (φ n) t := by
  rw [fourier_apply_eq _ t]
  have hswap :
      ∀ x : ℝ,
        Complex.exp (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
            (∑ n ∈ F, c n • φ n x) =
          ∑ n ∈ F,
            c n •
              (Complex.exp
                  (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
                φ n x) := by
    intro x
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [smul_eq_mul, smul_eq_mul]
    ring
  calc
    ∫ x : ℝ,
        Complex.exp (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
          (∑ n ∈ F, c n • φ n x) =
        ∫ x : ℝ,
          ∑ n ∈ F,
            c n •
              (Complex.exp
                  (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
                φ n x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact hswap x
    _ = ∑ n ∈ F,
          ∫ x : ℝ,
            c n •
              (Complex.exp
                  (((-2 : ℝ) * Real.pi * (x * t) : ℝ) * Complex.I) *
                φ n x) := by
      apply integral_finset_sum
      intro n hn
      exact (fourier_kernel_smul_integrable (hφ n hn) t).smul (c n)
    _ = ∑ n ∈ F, c n • 𝓕 (φ n) t := by
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [integral_smul, fourier_apply_eq (φ n) t]

/-- Integrability of the literal zero-extended mode (local copy of the
standard argument; the upstream instance is private). -/
private theorem logWindowMode_integrable
    (i : PairIndex) (n : ℤ) :
    Integrable (logWindowZeroExtendedMode i n) volume := by
  apply IntegrableOn.integrable_indicator
  · apply Continuous.integrableOn_Icc
    fun_prop
  · exact measurableSet_Icc

/-! ## The additive mode class and its crosswalks -/

private theorem additiveMode_memLp (i : PairIndex) (n : ℤ) :
    MemLp
      (fun x : ℝ =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i)))
      2 (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  letI := additiveWindow_isFiniteMeasure i
  apply MemLp.of_bound
    ((Continuous.aestronglyMeasurable (by fun_prop)))
    ((Real.sqrt (L_m i))⁻¹)
  filter_upwards [] with x
  rw [norm_mul]
  have h1 : ‖((Real.sqrt (L_m i))⁻¹ : ℂ)‖ = (Real.sqrt (L_m i))⁻¹ := by
    have hcast : ((Real.sqrt (L_m i))⁻¹ : ℂ) =
        (((Real.sqrt (L_m i))⁻¹ : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg]
    positivity
  have h2 : ‖Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i))‖ = 1 := by
    rw [Complex.norm_exp]
    have hre : (2 * Real.pi * Complex.I * n * (x / L_m i)).re = 0 := by
      have hcast :
          (2 * Real.pi * Complex.I * n * (x / L_m i) : ℂ) =
            Complex.I * ((2 * Real.pi * n * (x / L_m i) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [hcast]
      simp [Complex.mul_re]
    rw [hre]
    exact Real.exp_zero
  rw [h1, h2, mul_one]

/-- The additive-window mode class. -/
private noncomputable def additiveModeLp (i : PairIndex) (n : ℤ) :
    MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
  (additiveMode_memLp i n).toLp _

/-- Local copy of the private upstream change-of-variables fact
(`logWindow_measurePreserving` in the completeness bridge): the
logarithmic map carries the multiplicative window measure to the
additive window measure. -/
private theorem local_logWindow_measurePreserving
    (i : PairIndex) :
    MeasurePreserving
      (fun u : ℝ => Real.log (lambda_m i * u))
      (dStar.restrict (I_m i))
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
  have hm_real : (0 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2 hm_real
  have hlam_sq : lambda_m i * lambda_m i = (i.m : ℝ) := by
    rw [lambda_m, Real.mul_self_sqrt]
    exact hm_real.le
  have himage :
      (fun u : ℝ => Real.log (lambda_m i * u)) '' I_m i =
        Set.Icc 0 (L_m i) := by
    have hlam_one : 1 < lambda_m i := by
      have hm_one : (1 : ℝ) < i.m := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
      simpa [lambda_m] using
        (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_one :
          Real.sqrt 1 < Real.sqrt i.m)
    have hab : (lambda_m i)⁻¹ ≤ lambda_m i := by
      calc
        (lambda_m i)⁻¹ ≤ 1 := (inv_le_one₀ hlam).2 hlam_one.le
        _ ≤ lambda_m i := hlam_one.le
    have hcont :
        ContinuousOn
          (fun u : ℝ => Real.log (lambda_m i * u))
          (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) := by
      apply (continuousOn_const.mul continuousOn_id).log
      intro u hu
      exact ne_of_gt (mul_pos hlam ((inv_pos.mpr hlam).trans_le hu.1))
    have hmono :
        MonotoneOn
          (fun u : ℝ => Real.log (lambda_m i * u))
          (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) := by
      intro a ha b hb hab'
      exact Real.strictMonoOn_log.monotoneOn
        (mul_pos hlam ((inv_pos.mpr hlam).trans_le ha.1))
        (mul_pos hlam ((inv_pos.mpr hlam).trans_le hb.1))
        (mul_le_mul_of_nonneg_left hab' hlam.le)
    rw [I_m]
    rw [hcont.image_Icc_of_monotoneOn hab hmono]
    rw [mul_inv_cancel₀ hlam.ne', Real.log_one, hlam_sq]
    rfl
  have hderiv :
      ∀ u ∈ I_m i,
        HasDerivWithinAt
          (fun v : ℝ => Real.log (lambda_m i * v))
          u⁻¹ (I_m i) u := by
    intro u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam).trans_le hu.1
    have hmul :
        HasDerivAt (fun v : ℝ => lambda_m i * v) (lambda_m i) u := by
      simpa only [id_eq, mul_one] using
        (HasDerivAt.const_mul (lambda_m i) (hasDerivAt_id u))
    have hlog :=
      (Real.hasDerivAt_log (mul_ne_zero hlam.ne' hu_pos.ne')).comp u hmul
    convert hlog.hasDerivWithinAt using 1
    field_simp
  have hinj :
      Set.InjOn (fun u : ℝ => Real.log (lambda_m i * u)) (I_m i) := by
    intro a ha b hb hab
    have hmul := congrArg Real.exp hab
    rw [Real.exp_log (mul_pos hlam ((inv_pos.mpr hlam).trans_le ha.1)),
      Real.exp_log (mul_pos hlam ((inv_pos.mpr hlam).trans_le hb.1))] at hmul
    exact mul_left_cancel₀ hlam.ne' hmul
  have hjac :=
    MeasureTheory.map_withDensity_abs_det_fderiv_eq_addHaar
      (μ := volume) (s := I_m i)
      measurableSet_Icc.nullMeasurableSet
      (fun u hu => (hderiv u hu).hasFDerivWithinAt)
      hinj
  simp only [ContinuousLinearMap.det_one_smulRight, abs_inv] at hjac
  rw [himage] at hjac
  refine ⟨by fun_prop, ?_⟩
  rw [dStar, MeasureTheory.restrict_withDensity
    (s := I_m i) (measurableSet_Icc : MeasurableSet (I_m i))]
  calc
    Measure.map (fun u : ℝ => Real.log (lambda_m i * u))
        ((volume.restrict (I_m i)).withDensity fun u => ENNReal.ofReal u⁻¹) =
        Measure.map (fun u : ℝ => Real.log (lambda_m i * u))
          ((volume.restrict (I_m i)).withDensity fun u => ENNReal.ofReal |u|⁻¹) := by
      congr 1
      apply MeasureTheory.withDensity_congr_ae
      filter_upwards [ae_restrict_mem
        (measurableSet_Icc : MeasurableSet (I_m i))] with u hu
      rw [abs_of_pos ((inv_pos.mpr hlam).trans_le hu.1)]
    _ = volume.restrict (Set.Icc (0 : ℝ) (L_m i)) := hjac


/-- The additive window unitary sends the additive mode class to the
literal production mode `V_n_m`. -/
private theorem logWindowL2Equiv_additiveModeLp
    (i : PairIndex) (n : ℤ) :
    logWindowL2Equiv i (additiveModeLp i n) = V_n_m i n := by
  apply MeasureTheory.Lp.ext
  have hcoe := coeFn_logWindowL2Equiv i (additiveModeLp i n)
  have hmode := MemLp.coeFn_toLp (additiveMode_memLp i n)
  have hVcoe :
      ((V_n_m i n : H_m i) : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ =>
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp
              (2 * Real.pi * Complex.I * n *
                (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    exact MemLp.coeFn_toLp _
  have hcomp := hmode.comp_tendsto
    (local_logWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hcoe, hVcoe, hcomp] with u hu hV hcm
  rw [hu, hV]
  simpa using hcm

private theorem symm_V_n_m_eq_additiveModeLp
    (i : PairIndex) (n : ℤ) :
    (logWindowL2Equiv i).symm (V_n_m i n) = additiveModeLp i n := by
  rw [← logWindowL2Equiv_additiveModeLp i n]
  exact (logWindowL2Equiv i).symm_apply_apply _

/-- The zero extension of the additive mode class is a.e. equal to the
literal `logWindowZeroExtendedMode`. -/
private theorem indicator_additiveModeLp_ae
    (i : PairIndex) (n : ℤ) :
    Set.indicator (Set.Icc (0 : ℝ) (L_m i))
        ((additiveModeLp i n : ℝ → ℂ)) =ᵐ[volume]
      logWindowZeroExtendedMode i n := by
  have hmode := MemLp.coeFn_toLp (additiveMode_memLp i n)
  have hae :
      ∀ᵐ x ∂volume, x ∈ Set.Icc (0 : ℝ) (L_m i) →
        (additiveModeLp i n : ℝ → ℂ) x =
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            Complex.exp (2 * Real.pi * Complex.I * n * (x / L_m i)) := by
    rw [← ae_restrict_iff' measurableSet_Icc]
    exact hmode
  filter_upwards [hae] with x hx
  unfold logWindowZeroExtendedMode
  by_cases hmem : x ∈ Set.Icc (0 : ℝ) (L_m i)
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, hx hmem]
  · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]

/-! ## The extension of a finite combination -/

private theorem sourceLogWindowZeroExtension_finsetSum_ae
    (i : PairIndex) (F : Finset ℤ) (c : ℤ → ℂ) :
    sourceLogWindowZeroExtension i (∑ n ∈ F, c n • V_n_m i n)
      =ᵐ[volume]
      (fun x : ℝ =>
        ∑ n ∈ F, c n • logWindowZeroExtendedMode i n x) := by
  have hsymm :
      (logWindowL2Equiv i).symm (∑ n ∈ F, c n • V_n_m i n) =
        ∑ n ∈ F, c n • additiveModeLp i n := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearIsometryEquiv.map_smul, symm_V_n_m_eq_additiveModeLp]
  unfold sourceLogWindowZeroExtension
  rw [hsymm]
  have hsum :
      (((∑ n ∈ F, c n • additiveModeLp i n :
          MeasureTheory.Lp ℂ 2
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i))))) : ℝ → ℂ)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
        (fun x => ∑ n ∈ F, c n • (additiveModeLp i n : ℝ → ℂ) x) := by
    have h1 := lp_coeFn_finsetSum F
      (fun n : ℤ => c n • additiveModeLp i n)
    refine h1.trans ?_
    have h2 :
        ∀ n ∈ F,
          ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))),
            ((c n • additiveModeLp i n :
                MeasureTheory.Lp ℂ 2
                  (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) x =
              c n • (additiveModeLp i n : ℝ → ℂ) x := by
      intro n _
      exact MeasureTheory.Lp.coeFn_smul (c n) (additiveModeLp i n)
    have h3 := Filter.eventually_all_finset F |>.mpr h2
    filter_upwards [h3] with x hx
    exact Finset.sum_congr rfl fun n hn => hx n hn
  have haesum :
      ∀ᵐ x ∂volume, x ∈ Set.Icc (0 : ℝ) (L_m i) →
        (((∑ n ∈ F, c n • additiveModeLp i n :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i))))) : ℝ → ℂ) x =
          ∑ n ∈ F, c n • (additiveModeLp i n : ℝ → ℂ) x := by
    rw [← ae_restrict_iff' measurableSet_Icc]
    exact hsum
  have hmodes :
      ∀ᵐ x ∂volume,
        ∀ n ∈ F,
          Set.indicator (Set.Icc (0 : ℝ) (L_m i))
              ((additiveModeLp i n : ℝ → ℂ)) x =
            logWindowZeroExtendedMode i n x := by
    rw [Filter.eventually_all_finset F]
    intro n _
    exact indicator_additiveModeLp_ae i n
  filter_upwards [haesum, hmodes] with x hx hmx
  by_cases hmem : x ∈ Set.Icc (0 : ℝ) (L_m i)
  · rw [Set.indicator_of_mem hmem, hx hmem]
    refine Finset.sum_congr rfl fun n hn => ?_
    have hone := hmx n hn
    rw [Set.indicator_of_mem hmem] at hone
    rw [hone]
  · rw [Set.indicator_of_notMem hmem]
    symm
    apply Finset.sum_eq_zero
    intro n hn
    have hone := hmx n hn
    rw [Set.indicator_of_notMem hmem] at hone
    rw [← hone]
    simp

/-! ## The finite-combination identity -/

/-- On a finite combination of modes the synthesized isometry agrees a.e.
with the ordinary Fourier integral of its additive zero extension. -/
private theorem crosswalk_on_finsetSum
    (i : PairIndex) (F : Finset ℤ) (c : ℤ → ℂ) :
    ((sourceLogWindowFourierL2Isometry i
        (∑ n ∈ F, c n • V_n_m i n) :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
      (fun t : ℝ =>
        𝓕 (sourceLogWindowZeroExtension i (∑ n ∈ F, c n • V_n_m i n)) t) := by
  have hmap :
      sourceLogWindowFourierL2Isometry i (∑ n ∈ F, c n • V_n_m i n) =
        ∑ n ∈ F, c n • sourceLogWindowFourierL2Isometry i (V_n_m i n) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearIsometry.map_smul]
  rw [hmap]
  have h1 := lp_coeFn_finsetSum F
    (fun n : ℤ => c n • sourceLogWindowFourierL2Isometry i (V_n_m i n))
  refine h1.trans ?_
  have h2 :
      ∀ n ∈ F,
        ∀ᵐ t ∂(volume : Measure ℝ),
          ((c n • sourceLogWindowFourierL2Isometry i (V_n_m i n) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t =
            c n • 𝓕 (logWindowZeroExtendedMode i n) t := by
    intro n _
    have hs := MeasureTheory.Lp.coeFn_smul (c n)
      (sourceLogWindowFourierL2Isometry i (V_n_m i n))
    have hm := coeFn_sourceLogWindowFourierL2Isometry_apply_mode i n
    filter_upwards [hs, hm] with t hts htm
    rw [hts]
    simp only [Pi.smul_apply]
    rw [htm]
  have h3 := Filter.eventually_all_finset F |>.mpr h2
  have hext := sourceLogWindowZeroExtension_finsetSum_ae i F c
  filter_upwards [h3, hext.fun_comp id] with t ht _
  have hsum_eq :
      ∑ n ∈ F,
          ((c n • sourceLogWindowFourierL2Isometry i (V_n_m i n) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t =
        ∑ n ∈ F, c n • 𝓕 (logWindowZeroExtendedMode i n) t :=
    Finset.sum_congr rfl fun n hn => ht n hn
  rw [hsum_eq]
  have hlin := fourier_finsetSum F c
    (fun n => logWindowZeroExtendedMode i n)
    (fun n _ => logWindowMode_integrable i n) t
  rw [← hlin]
  exact (fourier_congr_ae
    (sourceLogWindowZeroExtension_finsetSum_ae i F c) t).symm

/-! ## The main crosswalk -/

/-- **The source log-window Fourier crosswalk.**  The synthesized
whole-line `L²` isometry agrees almost everywhere with the ordinary
Fourier integral of the additive log-window zero extension. -/
theorem coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
    (i : PairIndex) (x : H_m i) :
    ((sourceLogWindowFourierL2Isometry i x :
        MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t : ℝ => 𝓕 (sourceLogWindowZeroExtension i x) t) := by
  classical
  -- Step 1: finite-combination approximants with error `< 1/(k+1)`.
  have happrox :
      ∀ k : ℕ, ∃ y : H_m i,
        (∃ F : Finset ℤ, ∃ c : ℤ → ℂ, y = ∑ n ∈ F, c n • V_n_m i n) ∧
          ‖x - y‖ < 1 / (k + 1) := by
    intro k
    have hδ : (0 : ℝ) < 1 / (k + 1) := by positivity
    have hclosure : x ∈ closure ((Submodule.span ℂ
        (Set.range ⇑(V_n_m_hilbertBasis i))) : Set (H_m i)) := by
      have hds := (V_n_m_hilbertBasis i).dense_span
      rw [← Submodule.topologicalClosure_coe, hds]
      trivial
    rw [Metric.mem_closure_iff] at hclosure
    obtain ⟨y, hy_mem, hy_dist⟩ := hclosure _ hδ
    obtain ⟨cf, hcf⟩ :=
      (Finsupp.mem_span_range_iff_exists_finsupp).mp (by simpa using hy_mem)
    refine ⟨y, ⟨cf.support, fun n => cf n, ?_⟩, ?_⟩
    · rw [← hcf, Finsupp.sum]
      refine (Finset.sum_congr rfl fun n _ => ?_).symm
      rw [V_n_m_hilbertBasis_apply]
    · rw [dist_eq_norm] at hy_dist
      exact hy_dist
  choose y hy_span hy_close using happrox
  -- Step 2: `L²` convergence of the approximants.
  have hL2 : Tendsto (fun k => y k) atTop (𝓝 x) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun k => norm_nonneg _)
      (fun k => (norm_sub_rev (y k) x ▸ (hy_close k).le)) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- Step 3: `L¹` control of the zero-extension differences.
  have hL1bound :
      ∀ k : ℕ,
        ∫ t : ℝ,
            ‖sourceLogWindowZeroExtension i (y k) t -
              sourceLogWindowZeroExtension i x t‖ ∂volume ≤
          Real.sqrt (L_m i) * ‖y k - x‖ := by
    intro k
    set D := (logWindowL2Equiv i).symm (y k) - (logWindowL2Equiv i).symm x
      with hD
    have hDnorm : ‖D‖ = ‖y k - x‖ := by
      rw [hD, ← map_sub]
      exact LinearIsometryEquiv.norm_map _ _
    have hDcoe :
        ((D :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)
          =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))]
          (fun s =>
            (((logWindowL2Equiv i).symm (y k) :
                MeasureTheory.Lp ℂ 2
                  (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) s -
              (((logWindowL2Equiv i).symm x :
                MeasureTheory.Lp ℂ 2
                  (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) s) := by
      rw [hD]
      exact MeasureTheory.Lp.coeFn_sub _ _
    have hpoint :
        ∀ᵐ s ∂volume,
          ‖sourceLogWindowZeroExtension i (y k) s -
              sourceLogWindowZeroExtension i x s‖ =
            Set.indicator (Set.Icc (0 : ℝ) (L_m i))
              (fun r => ‖(D : ℝ → ℂ) r‖) s := by
      have hae :
          ∀ᵐ s ∂volume, s ∈ Set.Icc (0 : ℝ) (L_m i) →
            (D : ℝ → ℂ) s =
              (((logWindowL2Equiv i).symm (y k) :
                  MeasureTheory.Lp ℂ 2
                    (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) s -
                (((logWindowL2Equiv i).symm x :
                  MeasureTheory.Lp ℂ 2
                    (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) s := by
        rw [← ae_restrict_iff' measurableSet_Icc]
        exact hDcoe
      filter_upwards [hae] with s hs
      unfold sourceLogWindowZeroExtension
      by_cases hmem : s ∈ Set.Icc (0 : ℝ) (L_m i)
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem,
          Set.indicator_of_mem hmem, hs hmem]
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem,
          Set.indicator_of_notMem hmem]
        simp
    calc
      ∫ t : ℝ,
          ‖sourceLogWindowZeroExtension i (y k) t -
            sourceLogWindowZeroExtension i x t‖ ∂volume =
          ∫ t : ℝ,
            Set.indicator (Set.Icc (0 : ℝ) (L_m i))
              (fun r => ‖(D : ℝ → ℂ) r‖) t ∂volume :=
        integral_congr_ae hpoint
      _ = ∫ t : ℝ, ‖(D : ℝ → ℂ) t‖
            ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
        rw [MeasureTheory.integral_indicator measurableSet_Icc]
      _ ≤ Real.sqrt (L_m i) * ‖D‖ := restrictL2_l1_le i D
      _ = Real.sqrt (L_m i) * ‖y k - x‖ := by rw [hDnorm]
  -- Step 4: pointwise Fourier convergence at every frequency.
  have hFour :
      ∀ t : ℝ,
        Tendsto
          (fun k => 𝓕 (sourceLogWindowZeroExtension i (y k)) t)
          atTop (𝓝 (𝓕 (sourceLogWindowZeroExtension i x) t)) := by
    intro t
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hb :
        ∀ k : ℕ,
          ‖𝓕 (sourceLogWindowZeroExtension i (y k)) t -
              𝓕 (sourceLogWindowZeroExtension i x) t‖ ≤
            Real.sqrt (L_m i) * ‖y k - x‖ := by
      intro k
      refine le_trans
        (fourier_sub_norm_le
          (sourceLogWindowZeroExtension_integrable i (y k))
          (sourceLogWindowZeroExtension_integrable i x) t)
        (hL1bound k)
    refine squeeze_zero (fun k => norm_nonneg _) hb ?_
    have hzero :
        Tendsto (fun k => ‖y k - x‖) atTop (𝓝 0) := by
      have := (tendsto_iff_norm_sub_tendsto_zero).mp hL2
      exact this
    have := hzero.const_mul (Real.sqrt (L_m i))
    simpa using this
  -- Step 5: `L²` convergence of the isometry images, hence an a.e.
  -- convergent subsequence.
  have hIsoL2 :
      Tendsto
        (fun k => sourceLogWindowFourierL2Isometry i (y k))
        atTop (𝓝 (sourceLogWindowFourierL2Isometry i x)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hnorm_eq :
        ∀ k : ℕ,
          ‖sourceLogWindowFourierL2Isometry i (y k) -
              sourceLogWindowFourierL2Isometry i x‖ = ‖y k - x‖ := by
      intro k
      rw [← LinearIsometry.map_sub]
      exact LinearIsometry.norm_map _ _
    have := (tendsto_iff_norm_sub_tendsto_zero).mp hL2
    refine Tendsto.congr (fun k => (hnorm_eq k).symm) this
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hMeas :=
    MeasureTheory.tendstoInMeasure_of_tendsto_Lp
      (f := fun k => sourceLogWindowFourierL2Isometry i (y k))
      (g := sourceLogWindowFourierL2Isometry i x) hIsoL2
  obtain ⟨ns, hns_mono, hns_ae⟩ := hMeas.exists_seq_tendsto_ae
  -- Step 6: identify the two limits along the subsequence.
  have hcross :
      ∀ᵐ t ∂(volume : Measure ℝ),
        ∀ k : ℕ,
          ((sourceLogWindowFourierL2Isometry i (y k) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t =
            𝓕 (sourceLogWindowZeroExtension i (y k)) t := by
    rw [MeasureTheory.ae_all_iff]
    intro k
    obtain ⟨F, c, hy⟩ := hy_span k
    rw [hy]
    exact crosswalk_on_finsetSum i F c
  filter_upwards [hns_ae, hcross] with t htns htcross
  have hleft :
      Tendsto
        (fun j =>
          ((sourceLogWindowFourierL2Isometry i (y (ns j)) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
        atTop
        (𝓝 (((sourceLogWindowFourierL2Isometry i x :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)) := htns
  have hright :
      Tendsto
        (fun j =>
          ((sourceLogWindowFourierL2Isometry i (y (ns j)) :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
        atTop
        (𝓝 (𝓕 (sourceLogWindowZeroExtension i x) t)) := by
    have hsub := (hFour t).comp hns_mono.tendsto_atTop
    refine Tendsto.congr (fun j => ?_) hsub
    exact (htcross (ns j)).symm
  exact tendsto_nhds_unique hleft hright

#print axioms sourceLogWindowZeroExtension
#print axioms sourceLogWindowZeroExtension_integrable
#print axioms coeFn_sourceLogWindowFourierL2Isometry_eq_fourier_sourceLogWindowZeroExtension
#print axioms one_mode_agreement_without_complete_basis_does_not_identify_maps_plant

end Q3.RouteB.D0Pstar
