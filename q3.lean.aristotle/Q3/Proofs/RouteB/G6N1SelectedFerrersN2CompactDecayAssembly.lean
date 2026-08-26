import Q3.Proofs.RouteB.G6N1PreAnchorLimitZeroModeAndSelectedShell
import Q3.Proofs.RouteB.G6N1SelectedFerrersN2SourceScaledTailRate
import Q3.Proofs.RouteB.G6N1SelectedFerrersCCMLemma73PreAnchorPort
import Q3.Proofs.RouteB.D0PstarProjectedMellinCoordinate
import Q3.Proofs.RouteB.CompactEvaluationRateTransfer

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 4000000

open Complex Filter Finset MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Goal 058 — N2/N3/N4 selected-shell compact closure

Verdict `REQ-2026-08-26-K`.  The ratified pre-anchor source-scaled tail rate
is transported to the theorem-generated selected shell through the public
cofinal reindex receipt, the exact center-normalizer cancellation is proved
before any inequality, the moving-window Mellin kernel is bounded on every
compact by the closed-substrip envelope, and the centered selected family
converges locally uniformly to `centeredXi`.  SlotS2 follows with `c = 1`
and gauge `1`.

No compact-rate premise; no `S + hFamily`; no trial-normalizer premise; no
new subsequence; `σ = 1/2` is never claimed.
-/

/-! ## Step 1: the pre-anchor projected Mellin coordinate equals the raw
transform -/

/-- The multiplicative Mellin coordinate of the literal normalized projected
trial on the source-locked `dStar` window, in source-parametric form. -/
noncomputable def preAnchorProjectedMellinCoordinate
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (z : ℂ) : ℂ :=
  ∫ u : ℝ,
      (kTrial_m_N i h hLp hNonzero : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

/-- An `H_m` representative times the selected Mellin kernel is integrable on
the exact multiplicative window (parametric clone of the Phase-4G lemma). -/
private theorem n2c_integrable_repr_mul_kernel
    (i : PairIndex) (f : H_m i) (z : ℂ) :
    Integrable
      (fun u : ℝ => f u * (u : ℂ) ^ (-Complex.I * z))
      (dStar.restrict (I_m i)) := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    apply ne_of_gt
    exact (inv_pos.mpr hlam_pos).trans_le hu.1
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hf :
      Integrable (fun u : ℝ => f u) (dStar.restrict (I_m i)) :=
    (Lp.memLp f).integrable fact_one_le_two_ennreal.elim
  have hkernel_cont :
      ContinuousOn
        (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        (I_m i) := by
    intro u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam_pos).trans_le hu.1
    exact
      (Complex.continuousAt_ofReal_cpow_const
        u (-Complex.I * z) (Or.inr hu_pos.ne')).continuousWithinAt
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.bddAbove_image hkernel_cont.norm
  have hkernel_meas :
      AEStronglyMeasurable
        (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        (dStar.restrict (I_m i)) :=
    hkernel_cont.aestronglyMeasurable_of_isCompact
      isCompact_Icc measurableSet_Icc
  have hkernel_bound :
      ∀ᵐ u : ℝ ∂(dStar.restrict (I_m i)),
        ‖(u : ℂ) ^ (-Complex.I * z)‖ ≤ C := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hC (mem_image_of_mem _ hu)
  exact hf.mul_bdd hkernel_meas hkernel_bound

set_option maxHeartbeats 8000000 in
/-- **The pre-anchor Phase-4E engine.**  The Mellin coordinate of the literal
normalized projection is the phase-centered finite raw integral of its exact
coefficient row, in source-parametric form. -/
private theorem n2c_projected_eq_finiteRaw
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (z : ℂ) :
    preAnchorProjectedMellinCoordinate i h hLp hNonzero z =
      finiteRawCenteredIntegral (L_m i) (modeSet i)
        (c_n i h hLp hNonzero) z := by
  let c : ℤ → ℂ := c_n i h hLp hNonzero
  let phase : ℂ :=
    Complex.exp (Complex.I * z * (L_m i : ℂ) / 2)
  have hlam_pos : 0 < lambda_m i := by
    unfold lambda_m
    apply Real.sqrt_pos.mpr
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) i.hm)
  have hlog_lambda : Real.log (lambda_m i) = L_m i / 2 := by
    rw [lambda_m, Real.log_sqrt]
    · rfl
    · positivity
  have hmem :
      ∀ᵐ u : ℝ ∂(dStar.restrict (I_m i)), u ∈ I_m i :=
    ae_restrict_mem measurableSet_Icc
  have hkernel :
      (fun u : ℝ => (u : ℂ) ^ (-Complex.I * z))
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        phase *
          Complex.exp
            (-Complex.I * z *
              (Real.log (lambda_m i * u) : ℂ))) := by
    filter_upwards [hmem] with u hu
    have hu_pos : 0 < u :=
      (inv_pos.mpr hlam_pos).trans_le hu.1
    have hlog_u :
        Real.log u =
          Real.log (lambda_m i * u) - L_m i / 2 := by
      rw [Real.log_mul hlam_pos.ne' hu_pos.ne', hlog_lambda]
      ring
    rw [Complex.cpow_def_of_ne_zero
      (Complex.ofReal_ne_zero.mpr hu_pos.ne')]
    rw [← Complex.ofReal_log hu_pos.le]
    rw [hlog_u]
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hrep :=
    kTrial_m_N_coeFn_ae_eq_finiteLogFourierTrial_logWindow
      i h hLp hNonzero
  have hintegrand :
      (fun u : ℝ =>
        (kTrial_m_N i h hLp hNonzero : H_m i) u *
          (u : ℂ) ^ (-Complex.I * z))
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        phase *
          (finiteLogFourierTrial
              (L_m i) (modeSet i) c
              (Real.log (lambda_m i * u)) *
            Complex.exp
              (-Complex.I * z *
                (Real.log (lambda_m i * u) : ℂ)))) := by
    filter_upwards [hrep, hkernel] with u hrep_u hkernel_u
    rw [hrep_u, hkernel_u]
    ring
  have htransport :
      (∫ u : ℝ,
          finiteLogFourierTrial
              (L_m i) (modeSet i) c
              (Real.log (lambda_m i * u)) *
            Complex.exp
              (-Complex.I * z *
                (Real.log (lambda_m i * u) : ℂ))
        ∂(dStar.restrict (I_m i))) =
      ∫ x : ℝ in Set.Icc 0 (L_m i),
        finiteLogFourierTrial (L_m i) (modeSet i) c x *
          Complex.exp (-Complex.I * z * (x : ℂ)) := by
    simpa using
      (integral_comp_logWindow_dStar i
        (fun x : ℝ =>
          finiteLogFourierTrial (L_m i) (modeSet i) c x *
            Complex.exp (-Complex.I * z * (x : ℂ))))
  have hcoordinate :
      (∫ u : ℝ,
          (kTrial_m_N i h hLp hNonzero : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
        ∂(dStar.restrict (I_m i))) =
      finiteRawCenteredIntegral (L_m i) (modeSet i) c z := by
    calc
      _ = ∫ u : ℝ,
            phase *
              (finiteLogFourierTrial
                  (L_m i) (modeSet i) c
                  (Real.log (lambda_m i * u)) *
                Complex.exp
                  (-Complex.I * z *
                    (Real.log (lambda_m i * u) : ℂ)))
          ∂(dStar.restrict (I_m i)) := integral_congr_ae hintegrand
      _ = phase *
          ∫ u : ℝ,
            finiteLogFourierTrial
                (L_m i) (modeSet i) c
                (Real.log (lambda_m i * u)) *
              Complex.exp
                (-Complex.I * z *
                  (Real.log (lambda_m i * u) : ℂ))
            ∂(dStar.restrict (I_m i)) := by
              rw [integral_const_mul]
      _ = phase *
          ∫ x : ℝ in Set.Icc 0 (L_m i),
            finiteLogFourierTrial (L_m i) (modeSet i) c x *
              Complex.exp (-Complex.I * z * (x : ℂ)) := by
              rw [htransport]
      _ = phase *
          ∫ x : ℝ in 0..L_m i,
            finiteLogFourierTrial (L_m i) (modeSet i) c x *
              Complex.exp (-Complex.I * z * (x : ℂ)) := by
              rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
              rw [← intervalIntegral.integral_of_le (logLength_pos i).le]
      _ = finiteRawCenteredIntegral (L_m i) (modeSet i) c z := by
              rfl
  exact hcoordinate

/-- **The pre-anchor Phase-4E identity, Fplus orientation.**  The raw
transform is the Mellin coordinate of the normalized projection at the
reflected spectral point. -/
theorem preAnchorProjectedMellinCoordinate_neg_eq_rawTransformCoordinate
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (z : ℂ) :
    preAnchorProjectedMellinCoordinate i h hLp hNonzero (-z) =
      preAnchorRawTransformCoordinate i h hLp hNonzero z := by
  rw [n2c_projected_eq_finiteRaw i h hLp hNonzero (-z),
    finiteRawCenteredIntegral_eq_proposition59RawTransform
      (logLength_pos i).ne']
  rfl

/-- The raw transform is the finite normalizer times the Mellin coordinate of
the unnormalized projection, at the reflected spectral point. -/
theorem preAnchorRawTransformCoordinate_eq_normalizer_mul_projected
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (z : ℂ) :
    preAnchorRawTransformCoordinate i h hLp hNonzero z =
      ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) *
        ∫ u : ℝ,
          ((gTrial_m_N i h hLp : E_m_N i) : H_m i) u *
            (u : ℂ) ^ (-Complex.I * (-z))
          ∂(dStar.restrict (I_m i)) := by
  rw [← preAnchorProjectedMellinCoordinate_neg_eq_rawTransformCoordinate]
  unfold preAnchorProjectedMellinCoordinate
  have hsmul :
      (fun u : ℝ => (kTrial_m_N i h hLp hNonzero : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) *
          ((gTrial_m_N i h hLp : E_m_N i) : H_m i) u) := by
    have h1 := MeasureTheory.Lp.coeFn_smul
      (((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ))
      (((gTrial_m_N i h hLp : E_m_N i) : H_m i))
    have h2 : (kTrial_m_N i h hLp hNonzero : H_m i) =
        ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) •
          ((gTrial_m_N i h hLp : E_m_N i) : H_m i) := by
      unfold kTrial_m_N
      rw [Submodule.coe_smul]
    rw [h2]
    filter_upwards [h1] with u hu
    rw [hu]
    simp [smul_eq_mul]
  calc
    (∫ u : ℝ,
        (kTrial_m_N i h hLp hNonzero : H_m i) u *
          (u : ℂ) ^ (-Complex.I * (-z))
      ∂(dStar.restrict (I_m i))) =
        ∫ u : ℝ,
          ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) *
            (((gTrial_m_N i h hLp : E_m_N i) : H_m i) u *
              (u : ℂ) ^ (-Complex.I * (-z)))
          ∂(dStar.restrict (I_m i)) := by
        apply integral_congr_ae
        filter_upwards [hsmul] with u hu
        rw [hu]
        ring
    _ = ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) *
        ∫ u : ℝ,
          ((gTrial_m_N i h hLp : E_m_N i) : H_m i) u *
            (u : ℂ) ^ (-Complex.I * (-z))
          ∂(dStar.restrict (I_m i)) := by
        rw [integral_const_mul]

/-! ## Step 2: the moving-window Mellin kernel envelope -/

/-- The `dStar` mass of the full window is exactly `L_m`. -/
private theorem n2c_dStar_window_mass (i : PairIndex) :
    dStar (I_m i) = ENNReal.ofReal (L_m i) := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hinv_pos : 0 < (lambda_m i)⁻¹ := by positivity
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹)
        (Set.Icc (lambda_m i)⁻¹ (lambda_m i)) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    exact ne_of_gt (hinv_pos.trans_le hu.1)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (lambda_m i)⁻¹ (lambda_m i))]
      (fun u : ℝ => u⁻¹) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hu0 : 0 < u := hinv_pos.trans_le hu.1
    positivity
  rw [dStar, I_m, withDensity_apply _ measurableSet_Icc]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hinv hnn]
  congr 1
  have hle : (lambda_m i)⁻¹ ≤ lambda_m i := by
    have h1 : (lambda_m i)⁻¹ ≤ 1 := by
      rw [inv_eq_one_div, div_le_one hlam_pos]
      linarith
    linarith
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hle]
  rw [integral_inv_of_pos hinv_pos hlam_pos]
  have hdiv : lambda_m i / (lambda_m i)⁻¹ = lambda_m i * lambda_m i := by
    field_simp
  rw [hdiv, show lambda_m i * lambda_m i = (i.m : ℝ) from
    Real.mul_self_sqrt (by positivity)]
  rfl

/-- Pointwise kernel bound on the window: `‖u^(-iw)‖ ≤ λ^σ` for
`|Im w| ≤ σ`. -/
private theorem n2c_kernel_norm_le
    (i : PairIndex) {σ : ℝ} {w : ℂ} (hw : |w.im| ≤ σ)
    {u : ℝ} (hu : u ∈ I_m i) :
    ‖(u : ℂ) ^ (-Complex.I * w)‖ ≤ (lambda_m i) ^ σ := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hu_pos : 0 < u := (by positivity :
    (0:ℝ) < (lambda_m i)⁻¹).trans_le hu.1
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hu_pos]
  rw [show (-Complex.I * w).re = w.im by simp [Complex.mul_re]]
  rcases le_or_lt 0 w.im with hy | hy
  · calc u ^ w.im ≤ (lambda_m i) ^ w.im :=
        Real.rpow_le_rpow hu_pos.le hu.2 hy
      _ ≤ (lambda_m i) ^ σ := by
        apply Real.rpow_le_rpow_of_exponent_le hlam_one.le
        rwa [abs_of_nonneg hy] at hw
  · have h1 : u ^ w.im = (u⁻¹) ^ (-w.im) := by
      rw [Real.inv_rpow hu_pos.le, Real.rpow_neg hu_pos.le, inv_inv]
    have hinv_le : u⁻¹ ≤ lambda_m i := by
      have h2 := one_div_le_one_div_of_le (by positivity :
        (0:ℝ) < (lambda_m i)⁻¹) hu.1
      simpa [one_div, inv_inv] using h2
    calc u ^ w.im = (u⁻¹) ^ (-w.im) := h1
      _ ≤ (lambda_m i) ^ (-w.im) :=
        Real.rpow_le_rpow (by positivity) hinv_le (by linarith)
      _ ≤ (lambda_m i) ^ σ := by
        apply Real.rpow_le_rpow_of_exponent_le hlam_one.le
        rw [abs_of_neg hy] at hw
        linarith

set_option maxHeartbeats 8000000 in
/-- **The Cauchy–Schwarz coordinate envelope.**  For every `H_m` element `f`
and every `w` in the closed substrip `|Im w| ≤ σ`, the Mellin coordinate is
bounded by `λ^σ √L` times the `H_m` norm. -/
private theorem n2c_coordinate_envelope
    (i : PairIndex) (f : H_m i) {σ : ℝ} (hσ0 : 0 ≤ σ)
    {w : ℂ} (hw : |w.im| ≤ σ) :
    ‖∫ u : ℝ,
        f u * (u : ℂ) ^ (-Complex.I * w)
      ∂(dStar.restrict (I_m i))‖ ≤
      (lambda_m i) ^ σ * Real.sqrt (L_m i) * ‖f‖ := by
  have hL : 0 < L_m i := logLength_pos i
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hlamσ : (0:ℝ) ≤ (lambda_m i) ^ σ :=
    Real.rpow_nonneg hlam_pos.le σ
  have hinv :
      IntegrableOn (fun u : ℝ => u⁻¹) (I_m i) volume := by
    apply ContinuousOn.integrableOn_Icc
    apply continuousOn_id.inv₀
    intro u hu
    exact ne_of_gt ((by positivity :
      (0:ℝ) < (lambda_m i)⁻¹).trans_le hu.1)
  letI : IsFiniteMeasure (dStar.restrict (I_m i)) :=
    ⟨by
      rw [Measure.restrict_apply_univ, dStar, I_m,
        withDensity_apply _ measurableSet_Icc]
      simpa [I_m] using hinv.setLIntegral_lt_top⟩
  have hkernel_cont :
      ContinuousOn
        (fun u : ℝ => (u : ℂ) ^ (-Complex.I * w))
        (I_m i) := by
    intro u hu
    have hu_pos : 0 < u := (by positivity :
      (0:ℝ) < (lambda_m i)⁻¹).trans_le hu.1
    exact
      (Complex.continuousAt_ofReal_cpow_const
        u (-Complex.I * w) (Or.inr hu_pos.ne')).continuousWithinAt
  have hmeas :
      AEStronglyMeasurable
        (fun u : ℝ => starRingEnd ℂ ((u : ℂ) ^ (-Complex.I * w)))
        (dStar.restrict (I_m i)) :=
    Complex.continuous_conj.comp_aestronglyMeasurable
      (hkernel_cont.aestronglyMeasurable_of_isCompact
        isCompact_Icc measurableSet_Icc)
  have hbound_ae :
      ∀ᵐ u : ℝ ∂(dStar.restrict (I_m i)),
        ‖starRingEnd ℂ ((u : ℂ) ^ (-Complex.I * w))‖ ≤
          (lambda_m i) ^ σ := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [RCLike.norm_conj]
    exact n2c_kernel_norm_le i hw hu
  have hkmem :
      MemLp (fun u : ℝ =>
        starRingEnd ℂ ((u : ℂ) ^ (-Complex.I * w))) 2
        (dStar.restrict (I_m i)) :=
    MemLp.of_bound hmeas _ hbound_ae
  have hKcoe : (hkmem.toLp _ : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ => starRingEnd ℂ ((u : ℂ) ^ (-Complex.I * w))) :=
    MemLp.coeFn_toLp _
  have hinner : inner ℂ (hkmem.toLp _ : H_m i) f =
      ∫ u : ℝ,
        f u * (u : ℂ) ^ (-Complex.I * w)
      ∂(dStar.restrict (I_m i)) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hKcoe] with u hu
    rw [RCLike.inner_apply, hu, Complex.conj_conj]
  have hCS : ‖(inner ℂ (hkmem.toLp _ : H_m i) f : ℂ)‖ ≤
      ‖(hkmem.toLp _ : H_m i)‖ * ‖f‖ :=
    norm_inner_le_norm _ _
  rw [hinner] at hCS
  have hKnorm : ‖(hkmem.toLp _ : H_m i)‖ ≤
      (lambda_m i) ^ σ * Real.sqrt (L_m i) := by
    rw [MeasureTheory.Lp.norm_toLp]
    have h1 := eLpNorm_le_of_ae_bound (p := (2 : ENNReal))
      (μ := dStar.restrict (I_m i)) hbound_ae
    have hμ : (dStar.restrict (I_m i)) Set.univ =
        ENNReal.ofReal (L_m i) := by
      rw [Measure.restrict_apply_univ, n2c_dStar_window_mass]
    rw [hμ] at h1
    have htoReal2 : ((2 : ENNReal).toReal)⁻¹ = (1/2 : ℝ) := by norm_num
    rw [htoReal2] at h1
    have hval : ENNReal.ofReal (L_m i) ^ (1/2 : ℝ) *
        ENNReal.ofReal ((lambda_m i) ^ σ) =
        ENNReal.ofReal (Real.sqrt (L_m i) * (lambda_m i) ^ σ) := by
      rw [ENNReal.ofReal_rpow_of_pos hL]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [← Real.sqrt_eq_rpow]
    rw [hval] at h1
    have h2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top h1
    rw [ENNReal.toReal_ofReal (by positivity)] at h2
    calc (eLpNorm (fun u : ℝ =>
          starRingEnd ℂ ((u : ℂ) ^ (-Complex.I * w))) 2
          (dStar.restrict (I_m i))).toReal ≤
        Real.sqrt (L_m i) * (lambda_m i) ^ σ := h2
      _ = (lambda_m i) ^ σ * Real.sqrt (L_m i) := by ring
  calc ‖∫ u : ℝ,
        f u * (u : ℂ) ^ (-Complex.I * w)
      ∂(dStar.restrict (I_m i))‖ ≤
      ‖(hkmem.toLp _ : H_m i)‖ * ‖f‖ := hCS
    _ ≤ (lambda_m i) ^ σ * Real.sqrt (L_m i) * ‖f‖ :=
      mul_le_mul_of_nonneg_right hKnorm (norm_nonneg f)

/-! ## Step 3: exact identities on the selected shell -/

/-- The centered `Xi` is even: the functional equation
`completedRiemannZeta₀ (1 - s) = completedRiemannZeta₀ s` centred at `1/2`. -/
theorem centeredXi_neg (z : ℂ) : centeredXi (-z) = centeredXi z := by
  unfold centeredXi riemannXi
  have h := completedRiemannZeta₀_one_sub ((1 / 2 : ℂ) + Complex.I * z)
  have harg : (1 : ℂ) - ((1 / 2 : ℂ) + Complex.I * z) =
      (1 / 2 : ℂ) + Complex.I * (-z) := by ring
  rw [harg] at h
  rw [h]
  ring

/-- The positive finite normalizer is a nonzero complex scalar. -/
private theorem n2c_sTrial_ne
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp) :
    ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) ≠ 0 := by
  have hpos : 0 < sTrial_m_N i h hLp hNonzero := by
    unfold sTrial_m_N
    exact inv_pos.mpr hNonzero
  exact_mod_cast ne_of_gt hpos

/-- Central `Gwin` nonvanishing extracted from the shell's raw-zero field. -/
private theorem n2c_gwin_zero_ne
    (D : SelectedProlateCofinalSourceData) (k : ℕ) :
    preAnchorGwinTransformCoordinate
      (D.index k) (prolateCombination (D.pair k)) 0 ≠ 0 := by
  intro hzero
  apply D.rawZeroNonzero k
  rw [preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero,
    hzero, mul_zero]

/-- **The exact center-normalizer cancellation.**  On the selected shell the
centered finite family minus the `Gwin`-anchored main term is the anchored
ratio times the Mellin coordinate of the literal unnormalized projection
residual, at the reflected spectral point.  The finite trial normalizer
cancels exactly before any inequality. -/
private theorem n2c_centered_identity
    (D : SelectedProlateCofinalSourceData) (k : ℕ) (z : ℂ) :
    D.centeredPstar k z -
      centeredXi 0 /
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0 *
        preAnchorGwinTransformCoordinate
          (D.index k) (prolateCombination (D.pair k)) (-z) =
      centeredXi 0 /
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0 *
        ∫ u : ℝ,
          (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : E_m_N (D.index k)) :
              H_m (D.index k)) u -
            (gTrial_m (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : H_m (D.index k)) u) *
            (u : ℂ) ^ (-Complex.I * (-z))
          ∂(dStar.restrict (I_m (D.index k))) := by
  have hgwin0 := n2c_gwin_zero_ne D k
  have hsT := n2c_sTrial_ne (D.index k) (prolateCombination (D.pair k))
    (D.eStar_memLp k) (D.trialNonzero k)
  have hraw0 := preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
    (D.index k) (prolateCombination (D.pair k))
    (D.eStar_memLp k) (D.trialNonzero k)
  have hrawz := preAnchorRawTransformCoordinate_eq_normalizer_mul_projected
    (D.index k) (prolateCombination (D.pair k))
    (D.eStar_memLp k) (D.trialNonzero k) z
  have hfull := preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
    (D.index k) (prolateCombination (D.pair k)) (D.eStar_memLp k) (-z)
  have hsub :
      (∫ u : ℝ,
        (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : E_m_N (D.index k)) :
            H_m (D.index k)) u -
          (gTrial_m (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : H_m (D.index k)) u) *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k)))) =
      (∫ u : ℝ,
        ((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : E_m_N (D.index k)) :
            H_m (D.index k)) u *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k)))) -
      ∫ u : ℝ,
        (gTrial_m (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : H_m (D.index k)) u *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k))) := by
    rw [← integral_sub
      (n2c_integrable_repr_mul_kernel (D.index k) _ (-z))
      (n2c_integrable_repr_mul_kernel (D.index k) _ (-z))]
    apply integral_congr_ae
    filter_upwards [] with u
    ring
  rw [hsub]
  have hproj :
      (∫ u : ℝ,
        ((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : E_m_N (D.index k)) :
            H_m (D.index k)) u *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k)))) =
      preAnchorRawTransformCoordinate
        (D.index k) (prolateCombination (D.pair k))
        (D.eStar_memLp k) (D.trialNonzero k) z /
        ((sTrial_m_N (D.index k) (prolateCombination (D.pair k))
          (D.eStar_memLp k) (D.trialNonzero k) : ℝ) : ℂ) := by
    rw [hrawz]
    field_simp
  have hfullm :
      (∫ u : ℝ,
        (gTrial_m (D.index k) (prolateCombination (D.pair k))
            (D.eStar_memLp k) : H_m (D.index k)) u *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k)))) =
      preAnchorGwinTransformCoordinate
        (D.index k) (prolateCombination (D.pair k)) (-z) := by
    rw [← hfull]
    rfl
  rw [hproj, hfullm]
  show centeredXi 0 /
      preAnchorRawTransformCoordinate
        (D.index k) (prolateCombination (D.pair k))
        (D.eStar_memLp k) (D.trialNonzero k) 0 *
      preAnchorRawTransformCoordinate
        (D.index k) (prolateCombination (D.pair k))
        (D.eStar_memLp k) (D.trialNonzero k) z - _ = _
  rw [hraw0, hrawz]
  field_simp

/-! ## Step 4: the selected Ferrers cofinal shell and the transported rate -/

/-- The theorem-generated selected Ferrers cofinal shell: the literal
pre-anchor data through the L73.8 port. -/
noncomputable def selectedFerrersCofinalShell
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    SelectedProlateCofinalSourceData :=
  selectedProlateCofinalSourceDataOfPreAnchorPort
    selectedFerrersPreAnchorData
    (selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ)

/-- Transport of the weighted scaled-residual term across exact index, pair
and scale equalities. -/
private theorem n2c_rate_term_transport
    {i i' : PairIndex} (hii : i = i')
    {P P' : ProlatePair} (hPP : P = P')
    {a a' : ℂ} (haa : a = a')
    (w : MemLp (E_star (prolateCombination P)) 2 (dStar.restrict (I_m i)))
    (w' : MemLp (E_star (prolateCombination P')) 2 (dStar.restrict (I_m i')))
    {σ : ℝ} :
    Real.sqrt (L_m i) * lambda_m i ^ σ *
      ‖a • (((gTrial_m_N i (prolateCombination P) w : E_m_N i) : H_m i) -
        gTrial_m i (prolateCombination P) w)‖ =
    Real.sqrt (L_m i') * lambda_m i' ^ σ *
      ‖a' • (((gTrial_m_N i' (prolateCombination P') w' : E_m_N i') :
          H_m i') -
        gTrial_m i' (prolateCombination P') w')‖ := by
  subst hii
  subst hPP
  subst haa
  rfl

set_option maxHeartbeats 8000000 in
/-- **The transported N2 rate.**  The ratified pre-anchor source-scaled tail
rate holds along the selected shell path, through the cofinal reindex
receipt. -/
private theorem n2c_shell_rate
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ)
    (σ : ℝ) (hσ0 : 0 ≤ σ) (hσ : σ < 1 / 2) :
    Filter.Tendsto
      (fun k : ℕ =>
        Real.sqrt (L_m ((selectedFerrersCofinalShell
            C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) *
          lambda_m ((selectedFerrersCofinalShell
            C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k) ^ σ *
          ‖(selectedFerrersCofinalShell
              C0 C4 Cχ hC0 hC4 hCχ hmode hχ).sourceScale k •
            (((gTrial_m_N
                ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
                (prolateCombination ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
                ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k) :
                E_m_N ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) :
                H_m ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) -
              gTrial_m
                ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
                (prolateCombination ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
                ((selectedFerrersCofinalShell
                  C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k))‖)
      Filter.atTop (nhds 0) := by
  obtain ⟨φ, hφ, hle, hidx, hpair, hscale⟩ :=
    selectedProlateCofinalSourceDataOfPreAnchorPort_exists_cofinal_reindex
      selectedFerrersPreAnchorData
      (selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates
        C0 C4 Cχ hC0 hC4 hCχ hmode hχ)
  have hbase :=
    selectedFerrersPreAnchorSourceScaledMellinProjectionTailRate
      C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ σ hσ0 hσ
  have hcomp := hbase.comp hφ
  apply hcomp.congr
  intro k
  simp only [Function.comp]
  exact n2c_rate_term_transport
    (by unfold selectedFerrersCofinalShell; rw [hidx k]; rfl)
    (by unfold selectedFerrersCofinalShell; rw [hpair k]; rfl)
    (by unfold selectedFerrersCofinalShell; rw [hscale k]; rfl)
    (selectedFerrersPreAnchorPair_eStar_memLp (φ k))
    ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k)

/-- The anchored central ratio tends to one on any selected shell. -/
private theorem n2c_ratio_tendsto_one
    (D : SelectedProlateCofinalSourceData) :
    Filter.Tendsto
      (fun k : ℕ =>
        centeredXi 0 /
          (D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0))
      Filter.atTop (nhds 1) := by
  have hzero_mem : (0 : ℂ) ∈ centeredCriticalStrip := by
    show |(0 : ℂ).im| < 1 / 2
    norm_num
  have hpoint :
      Filter.Tendsto
        (fun k =>
          D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0)
        Filter.atTop (nhds (centeredXi 0)) :=
    D.muntzLimit.tendsto_at hzero_mem
  have hdiv := Filter.Tendsto.div
    (tendsto_const_nhds (x := centeredXi 0)) hpoint
    centeredXi_zero_ne_zero
  rw [div_self centeredXi_zero_ne_zero] at hdiv
  exact hdiv

set_option maxHeartbeats 8000000 in
/-- **The per-index compact error budget.**  On the closed substrip the
centered error is the anchored ratio times the source-scaled residual
envelope. -/
private theorem n2c_error_bound
    (D : SelectedProlateCofinalSourceData) (k : ℕ) {σ : ℝ} (hσ0 : 0 ≤ σ)
    {z : ℂ} (hz : |z.im| ≤ σ) :
    ‖D.centeredPstar k z -
      centeredXi 0 /
          (D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0) *
        (D.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) (-z))‖ ≤
      ‖centeredXi 0 /
        (D.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0)‖ *
        (lambda_m (D.index k) ^ σ * Real.sqrt (L_m (D.index k)) *
          ‖D.sourceScale k •
            (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
                (D.eStar_memLp k) : E_m_N (D.index k)) :
                H_m (D.index k)) -
              gTrial_m (D.index k) (prolateCombination (D.pair k))
                (D.eStar_memLp k))‖) := by
  have hgwin0 := n2c_gwin_zero_ne D k
  have hscale0 := D.sourceScale_ne k
  -- rewrite the anchored term to the Gwin-anchored form of the identity
  have hA :
      centeredXi 0 /
          (D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0) *
        (D.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) (-z)) =
      centeredXi 0 /
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0 *
        preAnchorGwinTransformCoordinate
          (D.index k) (prolateCombination (D.pair k)) (-z) := by
    field_simp
  rw [hA, n2c_centered_identity D k z]
  -- pull the scale inside the residual integral
  have hsmul_int :
      D.sourceScale k *
        ∫ u : ℝ,
          (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : E_m_N (D.index k)) :
              H_m (D.index k)) u -
            (gTrial_m (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : H_m (D.index k)) u) *
            (u : ℂ) ^ (-Complex.I * (-z))
          ∂(dStar.restrict (I_m (D.index k))) =
      ∫ u : ℝ,
        (D.sourceScale k •
          (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : E_m_N (D.index k)) :
              H_m (D.index k)) -
            gTrial_m (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k)) : H_m (D.index k)) u *
          (u : ℂ) ^ (-Complex.I * (-z))
        ∂(dStar.restrict (I_m (D.index k))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    have hcoe := MeasureTheory.Lp.coeFn_smul (D.sourceScale k)
      (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
          (D.eStar_memLp k) : E_m_N (D.index k)) : H_m (D.index k)) -
        gTrial_m (D.index k) (prolateCombination (D.pair k))
          (D.eStar_memLp k))
    have hcoesub := MeasureTheory.Lp.coeFn_sub
      (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
          (D.eStar_memLp k) : E_m_N (D.index k)) : H_m (D.index k)))
      (gTrial_m (D.index k) (prolateCombination (D.pair k))
        (D.eStar_memLp k))
    filter_upwards [hcoe, hcoesub] with u hu1 hu2
    rw [hu1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hu2]
    simp only [Pi.sub_apply]
    ring
  -- the split: ratio times scale times residual coordinate
  have hsplit :
      centeredXi 0 /
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0 *
        ∫ u : ℝ,
          (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : E_m_N (D.index k)) :
              H_m (D.index k)) u -
            (gTrial_m (D.index k) (prolateCombination (D.pair k))
              (D.eStar_memLp k) : H_m (D.index k)) u) *
            (u : ℂ) ^ (-Complex.I * (-z))
          ∂(dStar.restrict (I_m (D.index k))) =
      (centeredXi 0 /
          (D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0)) *
        (D.sourceScale k *
          ∫ u : ℝ,
            (((gTrial_m_N (D.index k) (prolateCombination (D.pair k))
                (D.eStar_memLp k) : E_m_N (D.index k)) :
                H_m (D.index k)) u -
              (gTrial_m (D.index k) (prolateCombination (D.pair k))
                (D.eStar_memLp k) : H_m (D.index k)) u) *
              (u : ℂ) ^ (-Complex.I * (-z))
            ∂(dStar.restrict (I_m (D.index k)))) := by
    field_simp
  rw [hsplit, hsmul_int, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hzneg : |(-z).im| ≤ σ := by
    rw [Complex.neg_im, abs_neg]
    exact hz
  exact n2c_coordinate_envelope (D.index k) _ hσ0 hzneg

/-! ## Step 5: locally uniform compact decay, the centered limit and SlotS2 -/

set_option maxHeartbeats 8000000 in
/-- **N2 compact decay** (verdict `REQ-2026-08-26-K`, theorem 2).  On the
selected Ferrers cofinal shell the centered finite family minus the
`Müntz`-anchored main term tends to zero locally uniformly on the centered
critical strip.  The anchored term is evaluated at the reflected spectral
point: the shell's raw transform carries the paper `Fplus(z) = T(k)(-z)`
orientation, so the exact cancellation pairs `centeredPstar` at `z` with the
Müntz family at `-z`. -/
theorem selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    TendstoLocallyUniformlyOn
      (fun k z =>
        (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar k z -
          centeredXi 0 /
              (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k 0 *
            (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k (-z))
      (fun _ => 0) Filter.atTop centeredCriticalStrip := by
  apply Q3.RouteB.tendstoLocallyUniformlyOn_zero_of_compact_envelopes _ _
    CanonicalRHRoute.isOpen_centeredCriticalStrip
  intro K hKU hK
  obtain ⟨σ, hσ0, hσ, hKσ⟩ :=
    compact_subset_centeredCriticalStrip_contained_in_closed_substrip hK hKU
  refine ⟨fun k =>
    ‖centeredXi 0 /
      ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).sourceScale k *
        preAnchorGwinTransformCoordinate
          ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
          (prolateCombination ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k)) 0)‖ *
      (lambda_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k) ^ σ *
        Real.sqrt (L_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) *
        ‖(selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).sourceScale k •
          (((gTrial_m_N ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
              (prolateCombination ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
              ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k) :
              E_m_N ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) :
              H_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) -
            gTrial_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
              (prolateCombination ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
              ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k))‖), ?_, ?_⟩
  · have h1 := (n2c_ratio_tendsto_one (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ)).norm
    rw [norm_one] at h1
    have h2 := n2c_shell_rate C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ σ hσ0 hσ
    have h2' : Filter.Tendsto
        (fun k =>
          lambda_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k) ^ σ *
            Real.sqrt (L_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) *
            ‖(selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).sourceScale k •
              (((gTrial_m_N ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
                  (prolateCombination ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
                  ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k) :
                  E_m_N ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) :
                  H_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)) -
                gTrial_m ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).index k)
                  (prolateCombination ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).pair k))
                  ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).eStar_memLp k))‖)
        Filter.atTop (nhds 0) := by
      apply h2.congr
      intro k
      ring
    have hmul := h1.mul h2'
    rw [one_mul] at hmul
    exact hmul
  · filter_upwards [] with k
    intro z hz
    have hb := n2c_error_bound (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ) k hσ0 (hKσ z hz)
    simpa only [SelectedProlateCofinalSourceData.muntzApproximation] using hb

set_option maxHeartbeats 8000000 in
/-- The Müntz-anchored family tends to `centeredXi` locally uniformly, on any
selected shell: the anchored ratio tends to one, the Müntz family carries the
Lemma-7.3 limit, and `centeredXi` is even. -/
private theorem n2c_anchored_tendsto_xi
    (D : SelectedProlateCofinalSourceData) :
    TendstoLocallyUniformlyOn
      (fun k z =>
        centeredXi 0 / D.muntzApproximation k 0 *
          D.muntzApproximation k (-z))
      centeredXi Filter.atTop centeredCriticalStrip := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    CanonicalRHRoute.isOpen_centeredCriticalStrip]
  intro K hKU hK
  have hnegK : IsCompact (Neg.neg '' K) := hK.image continuous_neg
  have hnegSub : (Neg.neg '' K) ⊆ centeredCriticalStrip := by
    rintro w ⟨z, hz, rfl⟩
    have hzs := hKU hz
    show |(-z).im| < 1 / 2
    rw [Complex.neg_im, abs_neg]
    exact hzs
  have hmuntzK := (tendstoLocallyUniformlyOn_iff_forall_isCompact
    CanonicalRHRoute.isOpen_centeredCriticalStrip).mp
    D.muntzLimit (Neg.neg '' K) hnegSub hnegK
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    (differentiable_centeredXi.continuous.continuousOn)
  have hM'pos : (0 : ℝ) < max M 0 + 1 := by
    have := le_max_right M 0
    linarith
  have hM' : ∀ z ∈ K, ‖centeredXi z‖ ≤ max M 0 + 1 := by
    intro z hz
    have := hM z hz
    have h2 := le_max_left M 0
    linarith
  have hratio := n2c_ratio_tendsto_one D
  rw [Metric.tendstoUniformlyOn_iff] at hmuntzK ⊢
  intro ε hε
  have hc2 : ∀ᶠ k in Filter.atTop,
      ‖centeredXi 0 /
        (D.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0)‖ < 2 := by
    have hn := hratio.norm
    rw [norm_one] at hn
    exact hn.eventually_lt_const (by norm_num)
  have hc1 : ∀ᶠ k in Filter.atTop,
      ‖centeredXi 0 /
        (D.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0) - 1‖ <
        ε / (2 * (max M 0 + 1)) := by
    have hd := Metric.tendsto_nhds.mp hratio
      (ε / (2 * (max M 0 + 1))) (by positivity)
    apply hd.mono
    intro k hk
    rwa [dist_eq_norm] at hk
  filter_upwards [hc2, hc1, hmuntzK (ε / 4) (by positivity)] with
    k h2 h1 hmuk
  intro z hz
  have hmz := hmuk (-z) (Set.mem_image_of_mem _ hz)
  rw [dist_eq_norm] at hmz ⊢
  have hXin := centeredXi_neg z
  have hkey :
      centeredXi z -
        centeredXi 0 / D.muntzApproximation k 0 *
          D.muntzApproximation k (-z) =
      -((centeredXi 0 / D.muntzApproximation k 0) *
          (D.muntzApproximation k (-z) - centeredXi (-z))) -
        ((centeredXi 0 / D.muntzApproximation k 0 - 1) *
          centeredXi (-z)) := by
    rw [hXin]
    ring
  have hratio_eq :
      centeredXi 0 / D.muntzApproximation k 0 =
        centeredXi 0 /
          (D.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0) := rfl
  rw [hkey]
  have hb1 : ‖(centeredXi 0 / D.muntzApproximation k 0) *
      (D.muntzApproximation k (-z) - centeredXi (-z))‖ < 2 * (ε / 4) := by
    rw [norm_mul]
    have hfac : ‖D.muntzApproximation k (-z) - centeredXi (-z)‖ =
        ‖centeredXi (-z) - D.muntzApproximation k (-z)‖ := norm_sub_rev _ _
    rw [hfac, hratio_eq]
    rcases eq_or_ne ‖centeredXi (-z) - D.muntzApproximation k (-z)‖ 0 with
      hzero | hne
    · rw [hzero, mul_zero]
      positivity
    · apply mul_lt_mul' h2.le hmz (norm_nonneg _)
      norm_num
  have hb2 : ‖(centeredXi 0 / D.muntzApproximation k 0 - 1) *
      centeredXi (-z)‖ ≤ ε / (2 * (max M 0 + 1)) * (max M 0 + 1) := by
    rw [norm_mul]
    apply mul_le_mul
    · exact h1.le
    · rw [hXin]
      exact hM' z hz
    · exact norm_nonneg _
    · positivity
  have hb2' : ε / (2 * (max M 0 + 1)) * (max M 0 + 1) = ε / 2 := by
    field_simp
  calc ‖-((centeredXi 0 / D.muntzApproximation k 0) *
        (D.muntzApproximation k (-z) - centeredXi (-z))) -
        ((centeredXi 0 / D.muntzApproximation k 0 - 1) *
          centeredXi (-z))‖ ≤
      ‖(centeredXi 0 / D.muntzApproximation k 0) *
        (D.muntzApproximation k (-z) - centeredXi (-z))‖ +
      ‖(centeredXi 0 / D.muntzApproximation k 0 - 1) *
        centeredXi (-z)‖ := by
        calc ‖_ - _‖ ≤ ‖-((centeredXi 0 / D.muntzApproximation k 0) *
              (D.muntzApproximation k (-z) - centeredXi (-z)))‖ +
            ‖(centeredXi 0 / D.muntzApproximation k 0 - 1) *
              centeredXi (-z)‖ := norm_sub_le _ _
          _ = _ := by rw [norm_neg]
    _ < 2 * (ε / 4) + ε / 2 := by
        have := hb2'.symm ▸ hb2
        apply add_lt_add_of_lt_of_le hb1
        rw [← hb2']
        exact hb2
    _ = ε := by ring

set_option maxHeartbeats 8000000 in
/-- **N2/N3: the centered selected family converges to `centeredXi`**
(verdict `REQ-2026-08-26-K`, theorem 3), locally uniformly on the centered
critical strip. -/
theorem selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    TendstoLocallyUniformlyOn
      ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar)
      centeredXi Filter.atTop centeredCriticalStrip := by
  have h1 :=
    selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
      C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ
  have h2 := n2c_anchored_tendsto_xi (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
    CanonicalRHRoute.isOpen_centeredCriticalStrip] at h1 h2 ⊢
  intro K hKU hK
  have hu1 := h1 K hKU hK
  have hu2 := h2 K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at hu1 hu2 ⊢
  intro ε hε
  filter_upwards [hu1 (ε / 2) (by positivity),
    hu2 (ε / 2) (by positivity)] with k g1 g2
  intro z hz
  have e1 := g1 z hz
  have e2 := g2 z hz
  rw [dist_eq_norm] at e1 e2 ⊢
  have hdecomp :
      centeredXi z - (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar k z =
      (centeredXi z -
        centeredXi 0 / (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k 0 *
          (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k (-z)) -
      ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar k z -
        centeredXi 0 / (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k 0 *
          (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k (-z)) := by
    ring
  rw [hdecomp]
  calc ‖_ - _‖ ≤
      ‖centeredXi z -
        centeredXi 0 / (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k 0 *
          (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k (-z)‖ +
      ‖(selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar k z -
        centeredXi 0 / (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k 0 *
          (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).muntzApproximation k (-z)‖ := norm_sub_le _ _
    _ < ε / 2 + ε / 2 := by
        apply add_lt_add e2
        have e1' := e1
        rw [zero_sub] at e1'
        rwa [norm_neg] at e1'
    _ = ε := by ring

/-- **N4: SlotS2 on the selected shell** (verdict `REQ-2026-08-26-K`,
theorem 4), with `c = 1` and gauge `1`: every cluster limit of the selected
family is `centeredXi` itself. -/
theorem selectedFerrersCofinalSlotS2_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    CanonicalRHRoute.SlotS2
      ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).canonicalApproximation) := by
  intro DC
  refine ⟨1, fun _ => 1, one_ne_zero, fun z _ => one_ne_zero, ?_⟩
  intro z hz
  have hfam : CanonicalRHRoute.selectedFamily
      ((selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).canonicalApproximation) =
      (selectedFerrersCofinalShell C0 C4 Cχ hC0 hC4 hCχ hmode hχ).centeredPstar := rfl
  have hlim1 := DC.convergence.tendsto_at hz
  rw [hfam] at hlim1
  have hlim2 :=
    (selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
      C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ).tendsto_at hz
  have heq := tendsto_nhds_unique hlim1 hlim2
  rw [heq]
  ring

#print axioms selectedFerrersCofinalCenteredFinite_sub_anchoredMuntz_tendsto_zero_of_modeChiThetaRates
#print axioms selectedFerrersCofinalCenteredPstar_tendsto_centeredXi_of_modeChiThetaRates
#print axioms selectedFerrersCofinalSlotS2_of_modeChiThetaRates

end Q3.RouteB.D0Pstar
