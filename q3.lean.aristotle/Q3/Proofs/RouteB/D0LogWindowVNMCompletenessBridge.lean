import Q3.Proofs.RouteB.D0FiniteProjectionReconstruction
import Q3.Proofs.RouteB.D0HilbertBasisWeightedTail
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Function.Jacobian

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

private theorem logWindow_measurePreserving
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

private theorem expWindow_measurePreserving
    (i : PairIndex) :
    MeasurePreserving
      (fun x : ℝ => Real.exp x / lambda_m i)
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
      (dStar.restrict (I_m i)) := by
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2 (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm))
  have hforward := logWindow_measurePreserving i
  refine ⟨by fun_prop, ?_⟩
  calc
    Measure.map (fun x : ℝ => Real.exp x / lambda_m i)
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) =
        Measure.map (fun x : ℝ => Real.exp x / lambda_m i)
          (Measure.map (fun u : ℝ => Real.log (lambda_m i * u))
            (dStar.restrict (I_m i))) := by rw [hforward.map_eq]
    _ = Measure.map
          ((fun x : ℝ => Real.exp x / lambda_m i) ∘
            (fun u : ℝ => Real.log (lambda_m i * u)))
          (dStar.restrict (I_m i)) := by
      rw [Measure.map_map]
      · fun_prop
      · exact hforward.measurable
    _ = Measure.map id (dStar.restrict (I_m i)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (I_m i))]
        with u hu
      have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
      simp only [Function.comp_apply, id_eq, Real.exp_log (mul_pos hlam hu_pos)]
      field_simp
    _ = dStar.restrict (I_m i) := Measure.map_id

/-- The exact D0.1 unitary from the additive logarithmic window to `H_m`. -/
noncomputable def logWindowL2Equiv (i : PairIndex) :
    MeasureTheory.Lp ℂ 2
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
      ≃ₗᵢ[ℂ]
    H_m i := by
  let phi : ℝ → ℝ := fun u => Real.log (lambda_m i * u)
  let psi : ℝ → ℝ := fun x => Real.exp x / lambda_m i
  have hphi := logWindow_measurePreserving i
  have hpsi := expWindow_measurePreserving i
  have hlam : 0 < lambda_m i := by
    rw [lambda_m]
    exact Real.sqrt_pos.2 (by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm))
  have hpsiphi : psi ∘ phi =ᵐ[dStar.restrict (I_m i)] id := by
    filter_upwards [ae_restrict_mem (measurableSet_Icc : MeasurableSet (I_m i))]
      with u hu
    have hu_pos : 0 < u := (inv_pos.mpr hlam).trans_le hu.1
    simp only [psi, phi, Function.comp_apply, id_eq,
      Real.exp_log (mul_pos hlam hu_pos)]
    field_simp
  have hphipsi :
      phi ∘ psi =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))] id := by
    filter_upwards [] with x
    simp only [phi, psi, Function.comp_apply, id_eq]
    rw [show lambda_m i * (Real.exp x / lambda_m i) = Real.exp x by field_simp]
    exact Real.log_exp x
  let forward :
      MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) →ₗᵢ[ℂ]
        H_m i :=
    MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ phi hphi
  let backward :
      H_m i →ₗ[ℂ]
        MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
    MeasureTheory.Lp.compMeasurePreservingₗ ℂ psi hpsi
  apply LinearIsometryEquiv.ofLinearIsometry forward backward
  · ext f
    have hout := MeasureTheory.Lp.coeFn_compMeasurePreserving
      (MeasureTheory.Lp.compMeasurePreserving psi hpsi f) hphi
    have hin := MeasureTheory.Lp.coeFn_compMeasurePreserving f hpsi
    have hin_phi := hin.comp_tendsto hphi.quasiMeasurePreserving.tendsto_ae
    filter_upwards [hout, hin_phi, hpsiphi] with u huout huin huinv
    change
      ((MeasureTheory.Lp.compMeasurePreserving phi hphi
        (MeasureTheory.Lp.compMeasurePreserving psi hpsi f) : H_m i) : ℝ → ℂ) u =
        (f : ℝ → ℂ) u
    rw [huout, huin]
    simpa [Function.comp_apply] using congrArg (fun z => (f : ℝ → ℂ) z) huinv
  · ext f
    have hout := MeasureTheory.Lp.coeFn_compMeasurePreserving
      (MeasureTheory.Lp.compMeasurePreserving phi hphi f) hpsi
    have hin := MeasureTheory.Lp.coeFn_compMeasurePreserving f hphi
    have hin_psi := hin.comp_tendsto hpsi.quasiMeasurePreserving.tendsto_ae
    filter_upwards [hout, hin_psi, hphipsi] with x hxout hxin hxinv
    change
      ((MeasureTheory.Lp.compMeasurePreserving psi hpsi
        (MeasureTheory.Lp.compMeasurePreserving phi hphi f) :
          MeasureTheory.Lp ℂ 2
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) x =
        (f : ℝ → ℂ) x
    rw [hxout, hxin]
    simpa [Function.comp_apply] using congrArg (fun z => (f : ℝ → ℂ) z) hxinv

/-- The exact almost-everywhere representative of the D0.1 unitary. -/
theorem coeFn_logWindowL2Equiv
    (i : PairIndex)
    (f : MeasureTheory.Lp ℂ 2
      (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) :
    ((logWindowL2Equiv i f : H_m i) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
        (fun u : ℝ => f (Real.log (lambda_m i * u))) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (logWindow_measurePreserving i)

private theorem V_n_m_span_orthogonal_eq_bot
    (i : PairIndex) :
    (Submodule.span ℂ (Set.range (V_n_m i)))ᗮ = ⊥ := by
  have hL : 0 < L_m i := logLength_pos i
  letI : Fact (0 < L_m i) := ⟨hL⟩
  let circleMk : ℝ → AddCircle (L_m i) := fun x => (x : AddCircle (L_m i))
  let circleRep : AddCircle (L_m i) → ℝ := fun z =>
    ((AddCircle.equivIoc (L_m i) 0 z : Set.Ioc 0 (0 + L_m i)) : ℝ)
  have hmk :
      MeasurePreserving circleMk
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))
        (volume : Measure (AddCircle (L_m i))) := by
    have h := AddCircle.measurePreserving_mk (L_m i) 0
    rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at h
    simpa [circleMk] using h
  have hrep_meas : Measurable circleRep := by
    have hx : Measurable (fun z : AddCircle (L_m i) =>
        (((AddCircle.equivIoc (L_m i) 0) z : Set.Ioc 0 (0 + L_m i)) : ℝ)) :=
      measurable_subtype_coe.comp
        (AddCircle.measurableEquivIoc (L_m i) 0).measurable
    simpa [circleRep] using hx
  have hrepmk :
      circleRep ∘ circleMk =ᵐ[volume.restrict (Set.Icc (0 : ℝ) (L_m i))] id := by
    have hsingle :
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) ({0} : Set ℝ) = 0 := by
      simp
    have hne :
        ∀ᵐ x : ℝ ∂(volume.restrict (Set.Icc (0 : ℝ) (L_m i))), x ≠ 0 := by
      simpa only [ae_iff, Classical.not_not] using hsingle
    filter_upwards [ae_restrict_mem measurableSet_Icc, hne] with x hx hxne
    have hxIoc : x ∈ Set.Ioc (0 : ℝ) (0 + L_m i) := by
      exact ⟨lt_of_le_of_ne hx.1 (Ne.symm hxne), by simpa using hx.2⟩
    change
      (((AddCircle.equivIoc (L_m i) 0) (x : AddCircle (L_m i)) :
        Set.Ioc 0 (0 + L_m i)) : ℝ) = x
    rw [AddCircle.equivIoc_coe_eq hxIoc]
  have hmkrep : circleMk ∘ circleRep = id := by
    funext z
    change
      ((((AddCircle.equivIoc (L_m i) 0) z :
        Set.Ioc 0 (0 + L_m i)) : ℝ) : AddCircle (L_m i)) = z
    exact (AddCircle.equivIoc (L_m i) 0).symm_apply_apply z
  have hrep :
      MeasurePreserving circleRep
        (volume : Measure (AddCircle (L_m i)))
        (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
    refine ⟨hrep_meas, ?_⟩
    calc
      Measure.map circleRep (volume : Measure (AddCircle (L_m i))) =
          Measure.map circleRep
            (Measure.map circleMk
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) := by rw [hmk.map_eq]
      _ = Measure.map (circleRep ∘ circleMk)
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
        rw [Measure.map_map hrep_meas hmk.measurable]
      _ = Measure.map id
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
        Measure.map_congr hrepmk
      _ = volume.restrict (Set.Icc (0 : ℝ) (L_m i)) := Measure.map_id
  let circleIntervalEquiv :
      MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) ≃ₗᵢ[ℂ]
        MeasureTheory.Lp ℂ 2
          (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) := by
    let forward :
        MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) →ₗᵢ[ℂ]
          MeasureTheory.Lp ℂ 2
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) :=
      MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ circleMk hmk
    let backward :
        MeasureTheory.Lp ℂ 2
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i))) →ₗ[ℂ]
          MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) :=
      MeasureTheory.Lp.compMeasurePreservingₗ ℂ circleRep hrep
    apply LinearIsometryEquiv.ofLinearIsometry forward backward
    · ext f
      have hout := MeasureTheory.Lp.coeFn_compMeasurePreserving
        (MeasureTheory.Lp.compMeasurePreserving circleRep hrep f) hmk
      have hin := MeasureTheory.Lp.coeFn_compMeasurePreserving f hrep
      have hin_mk := hin.comp_tendsto hmk.quasiMeasurePreserving.tendsto_ae
      filter_upwards [hout, hin_mk, hrepmk] with x hxout hxin hxinv
      change
        ((MeasureTheory.Lp.compMeasurePreserving circleMk hmk
          (MeasureTheory.Lp.compMeasurePreserving circleRep hrep f) :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ) x =
          (f : ℝ → ℂ) x
      rw [hxout, hxin]
      simpa [Function.comp_apply] using
        congrArg (fun y => (f : ℝ → ℂ) y) hxinv
    · ext f
      have hout := MeasureTheory.Lp.coeFn_compMeasurePreserving
        (MeasureTheory.Lp.compMeasurePreserving circleMk hmk f) hrep
      have hin := MeasureTheory.Lp.coeFn_compMeasurePreserving f hmk
      have hin_rep := hin.comp_tendsto hrep.quasiMeasurePreserving.tendsto_ae
      filter_upwards [hout, hin_rep] with z hzout hzin
      change
        ((MeasureTheory.Lp.compMeasurePreserving circleRep hrep
          (MeasureTheory.Lp.compMeasurePreserving circleMk hmk f) :
            MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i)))) :
              AddCircle (L_m i) → ℂ) z =
          (f : AddCircle (L_m i) → ℂ) z
      rw [hzout, hzin]
      simpa [Function.comp_apply] using
        congrArg (fun w => (f : AddCircle (L_m i) → ℂ) w) (congrFun hmkrep z)
  let circleToH :
      MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) ≃ₗᵢ[ℂ]
        H_m i :=
    circleIntervalEquiv.trans (logWindowL2Equiv i)
  let fourierVolumeLp (n : ℤ) :
      MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) :=
    ContinuousMap.toLp 2 volume ℂ (fourier n)
  let normalizedFourierVolume (n : ℤ) :
      MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))) :=
    ((Real.sqrt (L_m i))⁻¹ : ℂ) • fourierVolumeLp n
  have hspan_fourier :
      (Submodule.span ℂ (Set.range fourierVolumeLp)).topologicalClosure = ⊤ := by
    convert
      (ContinuousMap.toLp_denseRange (p := (2 : ℝ≥0∞)) ℂ
        (volume : Measure (AddCircle (L_m i))) ℂ (by norm_num)).topologicalClosure_map_submodule
        (@span_fourier_closure_eq_top (L_m i) inferInstance) using 1
    rw [Submodule.map_span]
    unfold fourierVolumeLp
    rw [Set.range_comp']
    simp only [ContinuousLinearMap.coe_coe]
  have hinner_fourier (n r : ℤ) :
      inner ℂ (fourierVolumeLp n) (fourierVolumeLp r) =
        ((L_m i : ℝ) : ℂ) * (if n = r then 1 else 0) := by
    rw [ContinuousMap.inner_toLp]
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    rw [MeasureTheory.integral_smul_measure]
    have hhaar :=
      (orthonormal_iff_ite.mp
        (@orthonormal_fourier (L_m i) inferInstance)) n r
    rw [ContinuousMap.inner_toLp] at hhaar
    rw [hhaar]
    rw [ENNReal.toReal_ofReal hL.le]
    simp [Complex.real_smul]
  have hnormalized : Orthonormal ℂ normalizedFourierVolume := by
    rw [orthonormal_iff_ite]
    intro n r
    dsimp only [normalizedFourierVolume]
    rw [inner_smul_left, inner_smul_right]
    rw [hinner_fourier]
    have hsqrt : Real.sqrt (L_m i) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    by_cases hnr : n = r
    · rw [if_pos hnr]
      simp only [map_inv₀, Complex.conj_ofReal, mul_one]
      norm_cast
      field_simp [hsqrt]
      nlinarith [Real.sq_sqrt hL.le]
    · rw [if_neg hnr]
      simp
  have hdense_normalized :
      ⊤ ≤ (Submodule.span ℂ (Set.range normalizedFourierVolume)).topologicalClosure := by
    rw [← hspan_fourier]
    apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.2
    intro f hf
    obtain ⟨n, rfl⟩ := hf
    have hmem : normalizedFourierVolume n ∈
        Submodule.span ℂ (Set.range normalizedFourierVolume) :=
      Submodule.subset_span (Set.mem_range_self n)
    have hsqrt : Real.sqrt (L_m i) ≠ 0 := (Real.sqrt_pos.2 hL).ne'
    convert
      (Submodule.smul_mem _ ((Real.sqrt (L_m i) : ℂ)) hmem) using 1
    simp [normalizedFourierVolume, hsqrt]
  let bCircle :
      HilbertBasis ℤ ℂ
        (MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i)))) :=
    HilbertBasis.mk hnormalized hdense_normalized
  have hbCircle (n : ℤ) : bCircle n = normalizedFourierVolume n := by
    exact congrFun (HilbertBasis.coe_mk hnormalized hdense_normalized) n
  let bH : HilbertBasis ℤ ℂ (H_m i) :=
    HilbertBasis.ofRepr (circleToH.symm.trans bCircle.repr)
  have hbH (n : ℤ) : bH n = circleToH (bCircle n) := by
    rw [← bH.repr_symm_single n]
    change (circleToH.symm.trans bCircle.repr).symm
        (lp.single 2 n (1 : ℂ)) = circleToH (bCircle n)
    rw [LinearIsometryEquiv.symm_trans]
    rw [LinearIsometryEquiv.trans_apply]
    rw [bCircle.repr_symm_single]
    rfl
  have hmode (n : ℤ) : bH n = V_n_m i n := by
    rw [hbH, hbCircle]
    apply MeasureTheory.Lp.ext
    have houter := coeFn_logWindowL2Equiv i
      (circleIntervalEquiv (normalizedFourierVolume n))
    have hmiddle := MeasureTheory.Lp.coeFn_compMeasurePreserving
      (normalizedFourierVolume n) hmk
    have hmiddle_log :=
      hmiddle.comp_tendsto
        (logWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
    have hfourier := ContinuousMap.coeFn_toLp
      (p := (2 : ENNReal)) (𝕜 := ℂ)
      (volume : Measure (AddCircle (L_m i))) (fourier n)
    have hnormalized_ae :
        (normalizedFourierVolume n : AddCircle (L_m i) → ℂ) =ᵐ[volume]
          (fun z => ((Real.sqrt (L_m i))⁻¹ : ℂ) * fourier n z) := by
      dsimp only [normalizedFourierVolume, fourierVolumeLp]
      have hsmul := MeasureTheory.Lp.coeFn_smul
        ((Real.sqrt (L_m i))⁻¹ : ℂ)
        (ContinuousMap.toLp 2 volume ℂ (fourier n) :
          MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i))))
      filter_upwards [hsmul, hfourier] with z hsz hz
      rw [hsz]
      change
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            ((ContinuousMap.toLp 2 volume ℂ (fourier n) :
              MeasureTheory.Lp ℂ 2 (volume : Measure (AddCircle (L_m i)))) :
                AddCircle (L_m i) → ℂ) z =
          ((Real.sqrt (L_m i))⁻¹ : ℂ) * fourier n z
      rw [hz]
    have hnormalized_log :=
      (hnormalized_ae.comp_tendsto hmk.quasiMeasurePreserving.tendsto_ae).comp_tendsto
        (logWindow_measurePreserving i).quasiMeasurePreserving.tendsto_ae
    have hv :
        (V_n_m i n : ℝ → ℂ) =ᵐ[dStar.restrict (I_m i)]
          (fun u : ℝ =>
            ((Real.sqrt (L_m i))⁻¹ : ℂ) *
              Complex.exp
                (2 * Real.pi * Complex.I * n *
                  (Real.log (lambda_m i * u) / L_m i))) := by
      unfold V_n_m
      apply MemLp.coeFn_toLp
    filter_upwards [houter, hmiddle_log, hnormalized_log, hv]
      with u huouter humiddle hunormalized huv
    change
      ((logWindowL2Equiv i
        (circleIntervalEquiv (normalizedFourierVolume n)) : H_m i) : ℝ → ℂ) u =
        (V_n_m i n : ℝ → ℂ) u
    rw [huouter]
    change
      ((MeasureTheory.Lp.compMeasurePreserving circleMk hmk
        (normalizedFourierVolume n) :
          MeasureTheory.Lp ℂ 2
            (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)
          (Real.log (lambda_m i * u)) =
        (V_n_m i n : ℝ → ℂ) u
    have humiddle' :
        ((MeasureTheory.Lp.compMeasurePreserving circleMk hmk
          (normalizedFourierVolume n) :
            MeasureTheory.Lp ℂ 2
              (volume.restrict (Set.Icc (0 : ℝ) (L_m i)))) : ℝ → ℂ)
            (Real.log (lambda_m i * u)) =
          (normalizedFourierVolume n : AddCircle (L_m i) → ℂ)
            (circleMk (Real.log (lambda_m i * u))) := by
      simpa [Function.comp_apply] using humiddle
    have hunormalized' :
        (normalizedFourierVolume n : AddCircle (L_m i) → ℂ)
            (circleMk (Real.log (lambda_m i * u))) =
          ((Real.sqrt (L_m i))⁻¹ : ℂ) *
            fourier n (circleMk (Real.log (lambda_m i * u))) := by
      simpa [Function.comp_apply] using hunormalized
    rw [humiddle', hunormalized', huv]
    simp only [circleMk]
    rw [fourier_coe_apply]
    congr 2
    ring
  have hfamily : (bH : ℤ → H_m i) = V_n_m i := funext hmode
  rw [← hfamily]
  rw [← Submodule.orthogonal_closure]
  rw [bH.dense_span]
  simp

/-- The literal production modes form a complete Hilbert basis of `H_m`. -/
noncomputable def V_n_m_hilbertBasis (i : PairIndex) :
    HilbertBasis ℤ ℂ (H_m i) :=
  HilbertBasis.mkOfOrthogonalEqBot
    (V_n_m_orthonormal i)
    (V_n_m_span_orthogonal_eq_bot i)

/-- The basis values are exactly the existing source-locked `V_n_m` modes. -/
@[simp]
theorem V_n_m_hilbertBasis_apply
    (i : PairIndex) (n : ℤ) :
    V_n_m_hilbertBasis i n = V_n_m i n := by
  simp [V_n_m_hilbertBasis]

/-- Exact unweighted Parseval identity for the complement of `modeSet`. -/
theorem norm_sub_coe_P_m_N_sq_eq_tsum_complement
    (i : PairIndex) (f : H_m i) :
    ‖f - (P_m_N i f : H_m i)‖ ^ 2 =
      ∑' n : ℤ,
        if n ∈ modeSet i then 0
        else ‖inner ℂ (V_n_m i n) f‖ ^ 2 := by
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul]
  simpa [V_n_m_hilbertBasis_apply] using
    norm_sub_basisPartialSum_sq_eq_tsum
      (V_n_m_hilbertBasis i)
      (modeSet i)
      f

#print axioms coeFn_logWindowL2Equiv
#print axioms V_n_m_hilbertBasis_apply
#print axioms norm_sub_coe_P_m_N_sq_eq_tsum_complement

end Q3.RouteB.D0Pstar
