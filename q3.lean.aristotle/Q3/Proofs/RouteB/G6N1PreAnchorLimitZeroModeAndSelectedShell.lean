import Q3.Proofs.RouteB.D0AnchorFloor
import Q3.Proofs.RouteB.D0CenteredCriticalMoment
import Q3.Proofs.RouteB.CenteredXiZeroNonzero
import Q3.Proofs.RouteB.MuntzV3.Core
import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex Filter Topology MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# G6/N1 pre-anchor limit, exact zero mode, and additive selected shell

This module stays strictly before `ProlateCanonicalSourceData`.  The paper
supplier is recorded by `CCMLemma73PreAnchorPort`; it normalizes the literal
unprojected `Gwin` family and never divides by `rawFplus ... 0`.

The Lean layer proves the exact zero-mode identity, derives finite projected
nonvanishing, removes one finite prefix, and constructs a new terminal
`CanonicalApproximation ℕ`.  The existing all-index D0Pstar source layer is
not modified or duplicated.
-/

/-- The unnormalized pre-anchor Müntz coordinate in the production centered
variable.  The paper transform coordinate is `s = -I*z`. -/
noncomputable def preAnchorGwinTransformCoordinate
    (i : PairIndex) (h : ℝ → ℂ) (z : ℂ) : ℂ :=
  EStarMuntzZeroMassContinuation.Gwin h (lambda_m i) (-Complex.I * z)

/-- The literal full multiplicative Mellin coordinate of the unprojected
source packet. -/
noncomputable def preAnchorFullMellinCoordinate
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (z : ℂ) : ℂ :=
  ∫ u : ℝ,
      (gTrial_m i h hLp : H_m i) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

/-- Exact pre-anchor full-Mellin/Gwin crosswalk.  This is the source-parametric
form of the already-green selected crosswalk and uses neither `TrialNonzero`
nor `CentralIndex`. -/
theorem preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (z : ℂ) :
    preAnchorFullMellinCoordinate i h hLp z =
      preAnchorGwinTransformCoordinate i h z := by
  have hm_real : (1 : ℝ) < i.m := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) i.hm)
  have hlam_one : 1 < lambda_m i := by
    simpa [lambda_m] using
      (Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 1) hm_real :
        Real.sqrt 1 < Real.sqrt i.m)
  have hlam_pos : 0 < lambda_m i := zero_lt_one.trans hlam_one
  have hrep :
      (fun u : ℝ => (gTrial_m i h hLp : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      E_star h := by
    unfold gTrial_m
    apply MemLp.coeFn_toLp
  have hdensity_meas :
      Measurable (fun u : ℝ => ENNReal.ofReal u⁻¹) :=
    measurable_inv.ennreal_ofReal
  have hdensity_top :
      ∀ᵐ u : ℝ ∂(volume.restrict (I_m i)),
        ENNReal.ofReal u⁻¹ < ⊤ := by
    filter_upwards [] with u
    exact ENNReal.ofReal_lt_top
  calc
    preAnchorFullMellinCoordinate i h hLp z =
        ∫ u : ℝ,
          (gTrial_m i h hLp : H_m i) u *
            (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            rfl
    _ = ∫ u : ℝ,
          E_star h u * (u : ℂ) ^ (-Complex.I * z)
          ∂(dStar.restrict (I_m i)) := by
            apply integral_congr_ae
            filter_upwards [hrep] with u hu
            rw [hu]
    _ = ∫ u : ℝ in I_m i,
          u⁻¹ • (E_star h u * (u : ℂ) ^ (-Complex.I * z)) := by
            rw [dStar]
            rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
              hdensity_meas hdensity_top _ measurableSet_Icc]
            apply setIntegral_congr_fun measurableSet_Icc
            intro u hu
            have hu_pos : 0 < u :=
              (inv_pos.mpr hlam_pos).trans_le hu.1
            change (ENNReal.ofReal u⁻¹).toReal •
                (E_star h u * (u : ℂ) ^ (-Complex.I * z)) =
              u⁻¹ • (E_star h u * (u : ℂ) ^ (-Complex.I * z))
            rw [ENNReal.toReal_ofReal (inv_nonneg.mpr hu_pos.le)]
    _ = ∫ u : ℝ in I_m i,
          EStarMuntzZeroMassContinuation.Estar h u *
            (u : ℂ) ^ ((-Complex.I * z) - 1) := by
            apply setIntegral_congr_fun measurableSet_Icc
            intro u hu
            have hu_pos : 0 < u :=
              (inv_pos.mpr hlam_pos).trans_le hu.1
            have hu_ne : (u : ℂ) ≠ 0 :=
              Complex.ofReal_ne_zero.mpr hu_pos.ne'
            change u⁻¹ •
                (E_star h u * (u : ℂ) ^ (-Complex.I * z)) =
              EStarMuntzZeroMassContinuation.Estar h u *
                (u : ℂ) ^ ((-Complex.I * z) - 1)
            rw [Complex.cpow_sub _ _ hu_ne, Complex.cpow_one]
            simp only [E_star,
              EStarMuntzZeroMassContinuation.Estar]
            rw [Complex.real_smul]
            push_cast
            rw [div_eq_mul_inv]
            ring
    _ = ∫ u : ℝ in Set.Ioo (lambda_m i)⁻¹ (lambda_m i),
          EStarMuntzZeroMassContinuation.Estar h u *
            (u : ℂ) ^ ((-Complex.I * z) - 1) := by
            rw [I_m, MeasureTheory.integral_Icc_eq_integral_Ioo]
    _ = preAnchorGwinTransformCoordinate i h z := by
            rfl

/-- At the central transform point the full Mellin coordinate is exactly the
zero logarithmic Fourier overlap. -/
theorem preAnchorFullMellinCoordinate_zero_eq_sqrtL_mul_innerV0
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i))) :
    preAnchorFullMellinCoordinate i h hLp 0 =
      (Real.sqrt (L_m i) : ℂ) *
        inner ℂ (V_n_m i 0) (gTrial_m i h hLp) := by
  have hsqrt : Real.sqrt (L_m i) ≠ 0 :=
    (Real.sqrt_pos.mpr (logLength_pos i)).ne'
  have hrep :
      (fun u : ℝ => (gTrial_m i h hLp : H_m i) u)
        =ᵐ[dStar.restrict (I_m i)]
      E_star h := by
    unfold gTrial_m
    apply MemLp.coeFn_toLp
  have hmode :
      (fun u : ℝ => (V_n_m i 0) u)
        =ᵐ[dStar.restrict (I_m i)]
      (fun u : ℝ =>
        ((Real.sqrt (L_m i))⁻¹ : ℂ) *
          Complex.exp
            (2 * Real.pi * Complex.I * (0 : ℤ) *
              (Real.log (lambda_m i * u) / L_m i))) := by
    unfold V_n_m
    apply MemLp.coeFn_toLp
  unfold preAnchorFullMellinCoordinate
  rw [MeasureTheory.L2.inner_def, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [hrep, hmode] with u hrep_u hmode_u
  rw [hrep_u, hmode_u]
  have hsqrtC : (Real.sqrt (L_m i) : ℂ) ≠ 0 := by
    exact_mod_cast hsqrt
  have hscale :
      E_star h u =
        (Real.sqrt (L_m i) : ℂ) *
          (E_star h u * (Real.sqrt (L_m i) : ℂ)⁻¹) := by
    field_simp [hsqrtC]
  simpa using hscale

/-- The exact source identity requested by the transaction:
`Gwin(0) = sqrt(L_m) * <V0,gTrial_m>`. -/
theorem preAnchorGwin_zero_eq_sqrtL_mul_innerV0
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i))) :
    preAnchorGwinTransformCoordinate i h 0 =
      (Real.sqrt (L_m i) : ℂ) *
        inner ℂ (V_n_m i 0) (gTrial_m i h hLp) := by
  rw [← preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate]
  exact preAnchorFullMellinCoordinate_zero_eq_sqrtL_mul_innerV0 i h hLp

/-- Exact preservation of the zero mode by Galerkin projection turns a nonzero
pre-anchor central value into the legal `TrialNonzero` witness. -/
theorem trialNonzero_of_preAnchorGwin_zero_ne
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hzero : preAnchorGwinTransformCoordinate i h 0 ≠ 0) :
    TrialNonzero i h hLp := by
  have hinner : inner ℂ (V_n_m i 0) (gTrial_m i h hLp) ≠ 0 := by
    intro hinner_zero
    apply hzero
    rw [preAnchorGwin_zero_eq_sqrtL_mul_innerV0 i h hLp, hinner_zero, mul_zero]
  have hprojected : gTrial_m_N i h hLp ≠ 0 := by
    intro hprojected_zero
    apply hinner
    rw [← inner_V0_gTrial_m_N_eq i h hLp, hprojected_zero]
    simp
  exact norm_pos_iff.mpr hprojected

/-- Literal path-local Proposition-59 raw transform of the normalized finite
projection. -/
noncomputable def preAnchorRawTransformCoordinate
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (z : ℂ) : ℂ :=
  proposition59RawTransform (logLength i) (modeSet i)
    (c_n i h hLp hNonzero) (-z)

/-- The central raw value is the constant normalized Fourier coefficient. -/
theorem preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp) :
    preAnchorRawTransformCoordinate i h hLp hNonzero 0 =
      (Real.sqrt (L_m i) : ℂ) * c_n i h hLp hNonzero 0 := by
  let D : CoefficientFamily :=
    ⟨fun _ n => c_n i h hLp hNonzero n⟩
  have hzero := rawFplus_zero_eq_sqrt_mul_c0 D i
  simpa [preAnchorRawTransformCoordinate, rawFplus, D] using hzero

/-- The normalized finite raw central value is the positive inverse projected
norm times the pre-anchor `Gwin` value. -/
theorem preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp) :
    preAnchorRawTransformCoordinate i h hLp hNonzero 0 =
      ((sTrial_m_N i h hLp hNonzero : ℝ) : ℂ) *
        preAnchorGwinTransformCoordinate i h 0 := by
  rw [preAnchorRawTransformCoordinate_zero_eq_sqrt_mul_c0 i h hLp hNonzero]
  unfold c_n kTrial_m_N
  rw [Submodule.coe_smul, inner_smul_right]
  rw [inner_V0_gTrial_m_N_eq i h hLp]
  rw [preAnchorGwin_zero_eq_sqrtL_mul_innerV0 i h hLp]
  ring

/-- Hence the exact normalized path-local raw value at zero is nonzero. -/
theorem preAnchorRawTransformCoordinate_zero_ne
    (i : PairIndex)
    (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNonzero : TrialNonzero i h hLp)
    (hGwin : preAnchorGwinTransformCoordinate i h 0 ≠ 0) :
    preAnchorRawTransformCoordinate i h hLp hNonzero 0 ≠ 0 := by
  rw [preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero]
  apply mul_ne_zero
  · exact_mod_cast (inv_ne_zero (ne_of_gt hNonzero))
  · exact hGwin

/-- The selected source objects needed before any anchor denominator exists. -/
structure SelectedProlatePreAnchorData where
  index : ℕ → PairIndex
  pair : ℕ → ProlatePair
  mCofinal : Tendsto (fun k => (index k).m) atTop atTop
  nCofinal : Tendsto (fun k => (index k).N) atTop atTop
  lambda_eq : ∀ k, (pair k).pw.lambda = lambda_m (index k)
  eStar_memLp : ∀ k,
    MemLp (E_star (prolateCombination (pair k))) 2
      (dStar.restrict (I_m (index k)))

/-- Exact project port of the already-ratified CCM Lemma 7.3 paper supplier.
The normalizer is source-defined and the statement contains no finite raw
anchor or `CentralIndex`. -/
structure CCMLemma73PreAnchorPort
    (D : SelectedProlatePreAnchorData) where
  sourceScale : ℕ → ℂ
  sourceScale_ne : ∀ k, sourceScale k ≠ 0
  convergence :
    TendstoLocallyUniformlyOn
      (fun k z =>
        sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) z)
      centeredXi atTop centeredCriticalStrip

/-- Lemma 7.3 at the nonzero central target gives eventual pre-anchor central
nonvanishing without any finite normalization. -/
theorem eventually_preAnchorGwin_zero_ne
    (D : SelectedProlatePreAnchorData)
    (P : CCMLemma73PreAnchorPort D) :
    ∀ᶠ k in atTop,
      preAnchorGwinTransformCoordinate
        (D.index k) (prolateCombination (D.pair k)) 0 ≠ 0 := by
  have hzero_mem : (0 : ℂ) ∈ centeredCriticalStrip := by
    show |(0 : ℂ).im| < 1 / 2
    norm_num
  have hpoint :
      Tendsto
        (fun k =>
          P.sourceScale k *
            preAnchorGwinTransformCoordinate
              (D.index k) (prolateCombination (D.pair k)) 0)
        atTop (𝓝 (centeredXi 0)) :=
    P.convergence.tendsto_at hzero_mem
  have hproduct_ne :
      ∀ᶠ k in atTop,
        P.sourceScale k *
          preAnchorGwinTransformCoordinate
            (D.index k) (prolateCombination (D.pair k)) 0 ≠ 0 :=
    hpoint.eventually (eventually_ne_nhds centeredXi_zero_ne_zero)
  filter_upwards [hproduct_ne] with k hk
  intro hGwin
  apply hk
  rw [hGwin, mul_zero]

/-- The final selected tail.  Every nonvanishing field is a theorem-generated
consequence of the pre-anchor port, not an assumption. -/
structure SelectedProlateCofinalSourceData where
  index : ℕ → PairIndex
  pair : ℕ → ProlatePair
  mCofinal : Tendsto (fun k => (index k).m) atTop atTop
  nCofinal : Tendsto (fun k => (index k).N) atTop atTop
  lambda_eq : ∀ k, (pair k).pw.lambda = lambda_m (index k)
  eStar_memLp : ∀ k,
    MemLp (E_star (prolateCombination (pair k))) 2
      (dStar.restrict (I_m (index k)))
  trialNonzero : ∀ k,
    TrialNonzero (index k) (prolateCombination (pair k)) (eStar_memLp k)
  rawZeroNonzero : ∀ k,
    preAnchorRawTransformCoordinate
      (index k) (prolateCombination (pair k)) (eStar_memLp k)
      (trialNonzero k) 0 ≠ 0
  sourceScale : ℕ → ℂ
  sourceScale_ne : ∀ k, sourceScale k ≠ 0
  muntzLimit :
    TendstoLocallyUniformlyOn
      (fun k z =>
        sourceScale k *
          preAnchorGwinTransformCoordinate
            (index k) (prolateCombination (pair k)) z)
      centeredXi atTop centeredCriticalStrip

/-- Tail shift tends to infinity. -/
private theorem tendsto_nat_add_atTop (start : ℕ) :
    Tendsto (fun k : ℕ => start + k) atTop atTop := by
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop b] with k hk
  omega

/-- Discarding the finite prefix selected by eventual central nonvanishing
constructs the full source-locked selected shell. -/
noncomputable def selectedProlateCofinalSourceDataOfPreAnchorPort
    (D : SelectedProlatePreAnchorData)
    (P : CCMLemma73PreAnchorPort D) :
    SelectedProlateCofinalSourceData := by
  let hEventually :
      ∃ start : ℕ, ∀ k ≥ start,
        preAnchorGwinTransformCoordinate
          (D.index k) (prolateCombination (D.pair k)) 0 ≠ 0 :=
    eventually_atTop.1 (eventually_preAnchorGwin_zero_ne D P)
  let start : ℕ := Classical.choose hEventually
  have hstart : ∀ k ≥ start,
      preAnchorGwinTransformCoordinate
        (D.index k) (prolateCombination (D.pair k)) 0 ≠ 0 := by
    simpa [start] using Classical.choose_spec hEventually
  let shift : ℕ → ℕ := fun k => start + k
  have hshift : Tendsto shift atTop atTop := by
    simpa [shift] using tendsto_nat_add_atTop start
  have htrial : ∀ k,
      TrialNonzero (D.index (shift k))
        (prolateCombination (D.pair (shift k)))
        (D.eStar_memLp (shift k)) := fun k =>
    trialNonzero_of_preAnchorGwin_zero_ne
      (D.index (shift k))
      (prolateCombination (D.pair (shift k)))
      (D.eStar_memLp (shift k))
      (hstart (shift k) (by omega))
  have hraw : ∀ k,
      preAnchorRawTransformCoordinate
        (D.index (shift k)) (prolateCombination (D.pair (shift k)))
        (D.eStar_memLp (shift k)) (htrial k) 0 ≠ 0 := fun k =>
    preAnchorRawTransformCoordinate_zero_ne
      (D.index (shift k))
      (prolateCombination (D.pair (shift k)))
      (D.eStar_memLp (shift k))
      (htrial k)
      (hstart (shift k) (by omega))
  have hlimit :
      TendstoLocallyUniformlyOn
        (fun k z =>
          P.sourceScale (shift k) *
            preAnchorGwinTransformCoordinate
              (D.index (shift k)) (prolateCombination (D.pair (shift k))) z)
        centeredXi atTop centeredCriticalStrip := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact
      isOpen_centeredCriticalStrip]
    intro K hKU hK
    have hbase :=
      (tendstoLocallyUniformlyOn_iff_forall_isCompact
        isOpen_centeredCriticalStrip).mp P.convergence K hKU hK
    intro u hu
    exact hshift (hbase u hu)
  exact {
    index := fun k => D.index (shift k)
    pair := fun k => D.pair (shift k)
    mCofinal := D.mCofinal.comp hshift
    nCofinal := D.nCofinal.comp hshift
    lambda_eq := fun k => D.lambda_eq (shift k)
    eStar_memLp := fun k => D.eStar_memLp (shift k)
    trialNonzero := htrial
    rawZeroNonzero := hraw
    sourceScale := fun k => P.sourceScale (shift k)
    sourceScale_ne := fun k => P.sourceScale_ne (shift k)
    muntzLimit := hlimit }

namespace SelectedProlateCofinalSourceData

/-- Literal selected finite raw family. -/
noncomputable def rawFplus
    (D : SelectedProlateCofinalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  preAnchorRawTransformCoordinate
    (D.index k) (prolateCombination (D.pair k))
    (D.eStar_memLp k) (D.trialNonzero k) z

/-- Literal selected Müntz main family from the paper port. -/
noncomputable def muntzApproximation
    (D : SelectedProlateCofinalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  D.sourceScale k *
    preAnchorGwinTransformCoordinate
      (D.index k) (prolateCombination (D.pair k)) z

/-- The centered finite selected family with a theorem-proved denominator. -/
noncomputable def centeredPstar
    (D : SelectedProlateCofinalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  centeredXi 0 / D.rawFplus k 0 * D.rawFplus k z

@[simp] theorem centeredPstar_zero
    (D : SelectedProlateCofinalSourceData) (k : ℕ) :
    D.centeredPstar k 0 = centeredXi 0 := by
  unfold centeredPstar
  field_simp [D.rawZeroNonzero k]

/-- The new terminal selected view.  The generic cofinal proposition records
both literal source coordinates and `parent = extract = id`. -/
noncomputable def canonicalApproximation
    (D : SelectedProlateCofinalSourceData) :
    CanonicalApproximation ℕ where
  Pstar := ⟨D.centeredPstar⟩
  parent := fun k => k
  parentCofinal :=
    Tendsto (fun k => (D.index k).m) atTop atTop ∧
      Tendsto (fun k => (D.index k).N) atTop atTop
  parentCofinalProof := ⟨D.mCofinal, D.nCofinal⟩
  extract := fun k => k
  extractStrictMono := fun _ _ h => h

/-- The selected Müntz approximation carries the exact Lemma 7.3 limit. -/
theorem muntzApproximation_tendsto_centeredXi
    (D : SelectedProlateCofinalSourceData) :
    TendstoLocallyUniformlyOn D.muntzApproximation centeredXi atTop
      centeredCriticalStrip :=
  D.muntzLimit

/-- The additive selected shell has the production anchor. -/
theorem canonicalApproximation_slotAnchor
    (D : SelectedProlateCofinalSourceData) :
    SlotAnchor D.canonicalApproximation 0 := by
  intro k
  exact D.centeredPstar_zero k

end SelectedProlateCofinalSourceData

/-- Plant: a zero target cannot force eventual central nonvanishing.  The
proved fact `centeredXi 0 ≠ 0` is therefore load-bearing. -/
theorem goalG6N1ZeroTarget_nonvanishing_not_free :
    ¬ (∀ᶠ _k : ℕ in atTop, (0 : ℂ) ≠ 0) := by
  intro h
  obtain ⟨k, hk⟩ := eventually_atTop.1 h
  exact (hk k le_rfl) rfl

#print axioms preAnchorFullMellinCoordinate_eq_preAnchorGwinTransformCoordinate
#print axioms preAnchorGwin_zero_eq_sqrtL_mul_innerV0
#print axioms trialNonzero_of_preAnchorGwin_zero_ne
#print axioms preAnchorRawTransformCoordinate_zero_eq_normalizer_mul_gwin_zero
#print axioms eventually_preAnchorGwin_zero_ne
#print axioms selectedProlateCofinalSourceDataOfPreAnchorPort
#print axioms SelectedProlateCofinalSourceData.muntzApproximation_tendsto_centeredXi
#print axioms SelectedProlateCofinalSourceData.canonicalApproximation_slotAnchor
#print axioms goalG6N1ZeroTarget_nonvanishing_not_free

end Q3.RouteB.D0Pstar
