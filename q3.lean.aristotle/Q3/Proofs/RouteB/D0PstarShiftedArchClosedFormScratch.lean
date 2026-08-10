import Q3.Proofs.RouteB.D0PstarW02AmbientAndSourceWeilFormScratch
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section

open Complex Filter MeasureTheory Topology
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

/-- The maximal square-root-weight multiplication operator underlying the
shifted positive archimedean form.  Its domain is exactly the already locked
shifted form domain; this is not the full-multiplier associated operator. -/
noncomputable def sourceArchimedeanShiftedWeightedLpPMap
    (i : PairIndex) :
    H_m i →ₗ.[ℂ] MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) where
  domain := sourceArchimedeanShiftedFormDomain i
  toFun := sourceArchimedeanShiftedWeightedLpLinearMap i

@[simp]
theorem sourceArchimedeanShiftedWeightedLpPMap_apply
    (i : PairIndex) (x : (sourceArchimedeanShiftedWeightedLpPMap i).domain) :
    sourceArchimedeanShiftedWeightedLpPMap i x =
      sourceArchimedeanShiftedWeightedLpLinearMap i x := by
  rfl

/-- The maximal square-root-weight multiplication operator is closed.  The
proof uses only L² convergence, extraction of a common a.e.-convergent
subsequence, and pointwise continuity of multiplication by the fixed weight. -/
theorem sourceArchimedeanShiftedWeightedLpPMap_isClosed
    (i : PairIndex) :
    (sourceArchimedeanShiftedWeightedLpPMap i).IsClosed := by
  rw [LinearPMap.IsClosed]
  refine IsSeqClosed.isClosed ?_
  rintro z ⟨x, y⟩ hzGraph hz
  have hx :
      Tendsto (fun n ↦ (z n).1) atTop (𝓝 x) :=
    (continuous_fst.tendsto (x, y)).comp hz
  have hy :
      Tendsto (fun n ↦ (z n).2) atTop (𝓝 y) :=
    (continuous_snd.tendsto (x, y)).comp hz
  have hUx :
      Tendsto
        (fun n ↦ sourceLogWindowFourierL2Isometry i (z n).1)
        atTop
        (𝓝 (sourceLogWindowFourierL2Isometry i x)) :=
    (sourceLogWindowFourierL2Isometry i).continuous.tendsto x |>.comp hx
  obtain ⟨φ, hφmono, hφae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hUx).exists_seq_tendsto_ae
  have hyφ :
      Tendsto (fun n ↦ (z (φ n)).2) atTop (𝓝 y) :=
    hy.comp hφmono.tendsto_atTop
  obtain ⟨ψ, hψmono, hψae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hyφ).exists_seq_tendsto_ae
  have hφψae :
      ∀ᵐ t : ℝ ∂volume,
        Tendsto
          (fun n ↦
            ((sourceLogWindowFourierL2Isometry i (z (φ (ψ n))).1 :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)
          atTop
          (𝓝
            (((sourceLogWindowFourierL2Isometry i x :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)) := by
    filter_upwards [hφae] with t ht
    exact ht.comp hψmono.tendsto_atTop
  have hGraphAe :
      ∀ᵐ t : ℝ ∂volume, ∀ n : ℕ,
        (((z (φ (ψ n))).2 :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t =
          (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
            (((sourceLogWindowFourierL2Isometry i (z (φ (ψ n))).1 :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t) := by
    rw [ae_all_iff]
    intro n
    have hzn := hzGraph (φ (ψ n))
    obtain ⟨xn, hxn, hout⟩ :=
      (LinearPMap.mem_graph_iff
        (sourceArchimedeanShiftedWeightedLpPMap i)).mp hzn
    have hn := coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i xn
    rw [← hout]
    simpa only [sourceArchimedeanShiftedWeightedLpPMap_apply, hxn] using hn
  have hyEq :
      ((y : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
      (fun t : ℝ ↦
        (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
          (((sourceLogWindowFourierL2Isometry i x :
              MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)) := by
    filter_upwards [hψae, hφψae, hGraphAe] with t hyt hxt hgraph
    apply tendsto_nhds_unique hyt
    convert
      (tendsto_const_nhds.mul hxt) using 1
    ext n
    exact hgraph n
  have hmemLp :
      MemLp
        (fun t : ℝ ↦
          (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
            (((sourceLogWindowFourierL2Isometry i x :
                MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t))
        2 volume :=
    (MeasureTheory.Lp.memLp y).ae_eq hyEq
  have hxDomain : x ∈ sourceArchimedeanShiftedFormDomain i :=
    (mem_sourceArchimedeanShiftedFormDomain_iff i x).mpr hmemLp
  let xm : (sourceArchimedeanShiftedWeightedLpPMap i).domain := ⟨x, hxDomain⟩
  have hout : sourceArchimedeanShiftedWeightedLpPMap i xm = y := by
    apply MeasureTheory.Lp.ext
    exact
      (coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i xm).trans
        hyEq.symm
  simpa only [hout] using
    (LinearPMap.mem_graph (sourceArchimedeanShiftedWeightedLpPMap i) xm)

private noncomputable def shiftedWeightedImageOnH
    (i : PairIndex) (x : H_m i) : ℝ → ℂ :=
  fun t : ℝ ↦
    (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
      (((sourceLogWindowFourierL2Isometry i x :
          MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ) t)

private theorem shiftedWeightedImageOnH_aestronglyMeasurable
    (i : PairIndex) (x : H_m i) :
    AEStronglyMeasurable (shiftedWeightedImageOnH i x) volume := by
  exact
    sourceArchimedeanShiftedSqrtWeight_measurable.complex_ofReal.aestronglyMeasurable.mul
      (MeasureTheory.Lp.aestronglyMeasurable
        (sourceLogWindowFourierL2Isometry i x))

/-- The extended nonnegative square-root energy of the exact shifted
archimedean form.  It is finite exactly on the locked form domain. -/
noncomputable def sourceArchimedeanShiftedFormRootEnergy
    (i : PairIndex) (x : H_m i) : ℝ≥0∞ :=
  eLpNorm (shiftedWeightedImageOnH i x) 2 volume

theorem mem_sourceArchimedeanShiftedFormDomain_iff_rootEnergy_lt_top
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      sourceArchimedeanShiftedFormRootEnergy i x < ∞ := by
  rw [mem_sourceArchimedeanShiftedFormDomain_iff]
  change
    MemLp (shiftedWeightedImageOnH i x) 2 volume ↔
      eLpNorm (shiftedWeightedImageOnH i x) 2 volume < ∞
  constructor
  · exact fun hx ↦ hx.eLpNorm_lt_top
  · exact fun hx ↦
      ⟨shiftedWeightedImageOnH_aestronglyMeasurable i x, hx⟩

/-- The exact shifted square-root energy is lower semicontinuous on the whole
ambient Hilbert space.  The proof is the source-faithful Fatou/subsequence
argument rather than a finite-dimensional surrogate. -/
theorem sourceArchimedeanShiftedFormRootEnergy_lowerSemicontinuous
    (i : PairIndex) :
    LowerSemicontinuous (sourceArchimedeanShiftedFormRootEnergy i) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro C
  refine IsSeqClosed.isClosed ?_
  intro xs x hxs hx
  have hUx :
      Tendsto
        (fun n ↦ sourceLogWindowFourierL2Isometry i (xs n))
        atTop
        (𝓝 (sourceLogWindowFourierL2Isometry i x)) :=
    (sourceLogWindowFourierL2Isometry i).continuous.tendsto x |>.comp hx
  obtain ⟨φ, hφmono, hφae⟩ :=
    (tendstoInMeasure_of_tendsto_Lp hUx).exists_seq_tendsto_ae
  have hweightedAe :
      ∀ᵐ t : ℝ ∂volume,
        Tendsto
          (fun n ↦ shiftedWeightedImageOnH i (xs (φ n)) t)
          atTop
          (𝓝 (shiftedWeightedImageOnH i x t)) := by
    filter_upwards [hφae] with t ht
    exact tendsto_const_nhds.mul ht
  have hbound :
      ∀ᶠ n in atTop,
        eLpNorm (shiftedWeightedImageOnH i (xs (φ n))) 2 volume ≤ C :=
    Filter.Eventually.of_forall fun n ↦ hxs (φ n)
  change eLpNorm (shiftedWeightedImageOnH i x) 2 volume ≤ C
  exact
    MeasureTheory.Lp.eLpNorm_le_of_ae_tendsto hbound
      (fun n ↦ shiftedWeightedImageOnH_aestronglyMeasurable i (xs (φ n)))
      hweightedAe

/-- The extended nonnegative quadratic form obtained by squaring the exact
shifted root energy. -/
noncomputable def sourceArchimedeanShiftedExtendedQuadraticForm
    (i : PairIndex) (x : H_m i) : ℝ≥0∞ :=
  sourceArchimedeanShiftedFormRootEnergy i x ^ 2

theorem sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous
    (i : PairIndex) :
    LowerSemicontinuous
      (sourceArchimedeanShiftedExtendedQuadraticForm i) := by
  change LowerSemicontinuous
    ((fun a : ℝ≥0∞ ↦ a ^ 2) ∘ sourceArchimedeanShiftedFormRootEnergy i)
  exact
    (ENNReal.continuous_pow 2).comp_lowerSemicontinuous
      (sourceArchimedeanShiftedFormRootEnergy_lowerSemicontinuous i)
      (fun _ _ h ↦ pow_le_pow_left' h 2)

theorem sourceArchimedeanShiftedFormRootEnergy_eq_enorm
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    sourceArchimedeanShiftedFormRootEnergy i x.1 =
      ‖sourceArchimedeanShiftedWeightedLpLinearMap i x‖ₑ := by
  unfold sourceArchimedeanShiftedFormRootEnergy shiftedWeightedImageOnH
  exact
    (eLpNorm_congr_ae
      (coeFn_sourceArchimedeanShiftedWeightedLpLinearMap i x).symm).trans
      (MeasureTheory.Lp.enorm_def
        (sourceArchimedeanShiftedWeightedLpLinearMap i x)).symm

/-- On the finite form domain, the extended quadratic form agrees exactly
with the real diagonal of the shifted sesquilinear form. -/
theorem sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceArchimedeanShiftedExtendedQuadraticForm i x.1).toReal =
      (sourceArchimedeanShiftedSesquilinearForm i x x).re := by
  rw [sourceArchimedeanShiftedExtendedQuadraticForm,
    sourceArchimedeanShiftedFormRootEnergy_eq_enorm,
    ENNReal.toReal_pow, toReal_enorm,
    sourceArchimedeanShiftedSesquilinearForm_apply]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ)
    (sourceArchimedeanShiftedWeightedLpLinearMap i x)).symm

theorem mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      sourceArchimedeanShiftedExtendedQuadraticForm i x < ∞ := by
  rw [mem_sourceArchimedeanShiftedFormDomain_iff_rootEnergy_lt_top]
  simp only [sourceArchimedeanShiftedExtendedQuadraticForm,
    ENNReal.pow_lt_top_iff, OfNat.ofNat, Nat.reduceEqDiff, or_false]

/-- The whole-domain continuous diagonal perturbation which turns the shifted
positive Arch form into `W02 + Arch - Prime`. -/
noncomputable def sourceWeilBoundedDiagonalPerturbation
    (i : PairIndex) (x : H_m i) : ℝ :=
  (sourceW02AmbientContinuousSesquilinearForm i x x).re -
    (sourcePrimeContinuousSesquilinearForm i x x).re -
      (|Real.log Real.pi| + Real.log 4 + 6) * ‖x‖ ^ 2

theorem sourceWeilBoundedDiagonalPerturbation_continuous
    (i : PairIndex) :
    Continuous (sourceWeilBoundedDiagonalPerturbation i) := by
  unfold sourceWeilBoundedDiagonalPerturbation
  fun_prop

/-- The complete exact source-Weil quadratic form as an extended-real
function.  Outside the shifted form domain the shifted energy is `+∞`; the
bounded ambient perturbation does not change that domain. -/
noncomputable def sourceWeilExtendedQuadraticForm
    (i : PairIndex) (x : H_m i) : EReal :=
  (sourceArchimedeanShiftedExtendedQuadraticForm i x : EReal) +
    (sourceWeilBoundedDiagonalPerturbation i x : EReal)

/-- The complete exact source-Weil extended quadratic form is lower
semicontinuous. -/
theorem sourceWeilExtendedQuadraticForm_lowerSemicontinuous
    (i : PairIndex) :
    LowerSemicontinuous (sourceWeilExtendedQuadraticForm i) := by
  have hq : LowerSemicontinuous
      (fun x : H_m i ↦
        (sourceArchimedeanShiftedExtendedQuadraticForm i x : EReal)) :=
    continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
      (sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous i)
      (fun _ _ h ↦ by exact_mod_cast h)
  have hb : LowerSemicontinuous
      (fun x : H_m i ↦
        (sourceWeilBoundedDiagonalPerturbation i x : EReal)) :=
    (continuous_coe_real_ereal.comp
      (sourceWeilBoundedDiagonalPerturbation_continuous i)).lowerSemicontinuous
  exact hq.add' hb fun x ↦
    EReal.continuousAt_add (by right; simp) (by left; simp)

theorem sourceWeil_shiftedDiagonal_add_boundedPerturbation
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceArchimedeanShiftedExtendedQuadraticForm i x.1).toReal +
        sourceWeilBoundedDiagonalPerturbation i x.1 =
      (sourceWeilSesquilinearForm i x x).re := by
  rw [sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re]
  unfold sourceWeilBoundedDiagonalPerturbation
  rw [sourceWeilSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply,
    sourcePrimeContinuousSesquilinearForm_apply]
  have hinner : (inner ℂ x x).re = ‖(x : H_m i)‖ ^ 2 := by
    simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) x)
  simp only [add_re, sub_re, mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [hinner]
  ring

/-- On its exact finite domain, the extended-real source-Weil form agrees
with the real diagonal of the assembled Hermitian sesquilinear form. -/
theorem sourceWeilExtendedQuadraticForm_eq_re
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    sourceWeilExtendedQuadraticForm i x.1 =
      ((sourceWeilSesquilinearForm i x x).re : EReal) := by
  have hfinite :
      sourceArchimedeanShiftedExtendedQuadraticForm i x.1 ≠ ∞ :=
    (mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
      i x.1).mp x.2 |>.ne
  unfold sourceWeilExtendedQuadraticForm
  rw [← EReal.coe_ennreal_toReal hfinite, ← EReal.coe_add]
  exact_mod_cast sourceWeil_shiftedDiagonal_add_boundedPerturbation i x

theorem mem_sourceArchimedeanShiftedFormDomain_iff_sourceWeilExtended_lt_top
    (i : PairIndex) (x : H_m i) :
    x ∈ sourceArchimedeanShiftedFormDomain i ↔
      sourceWeilExtendedQuadraticForm i x < ⊤ := by
  constructor
  · intro hx
    let xm : sourceArchimedeanShiftedFormDomain i := ⟨x, hx⟩
    rw [show x = xm.1 by rfl, sourceWeilExtendedQuadraticForm_eq_re]
    exact EReal.coe_lt_top _
  · intro hfinite
    by_contra hx
    have hqtop :
        sourceArchimedeanShiftedExtendedQuadraticForm i x = ∞ := by
      apply top_unique
      rw [← not_lt]
      exact fun h ↦ hx
        ((mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
          i x).mpr h)
    unfold sourceWeilExtendedQuadraticForm at hfinite
    rw [hqtop] at hfinite
    simp at hfinite

/-- The complete extended-real source-Weil form has the explicit global
lower bound already proved on its finite domain; outside that domain it is
`+∞`.  This is lower boundedness, not positivity. -/
theorem sourceWeilExtendedQuadraticForm_lowerBound
    (i : PairIndex) (x : H_m i) :
    ((-(sourceWeilLowerBoundConstant i * ‖x‖ ^ 2) : ℝ) : EReal) ≤
      sourceWeilExtendedQuadraticForm i x := by
  by_cases hx : x ∈ sourceArchimedeanShiftedFormDomain i
  · let xm : sourceArchimedeanShiftedFormDomain i := ⟨x, hx⟩
    rw [show x = xm.1 by rfl, sourceWeilExtendedQuadraticForm_eq_re]
    exact_mod_cast sourceWeilSesquilinearForm_re_self_lowerBound i xm
  · have hqtop :
        sourceArchimedeanShiftedExtendedQuadraticForm i x = ∞ := by
      apply top_unique
      rw [← not_lt]
      exact fun h ↦ hx
        ((mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
          i x).mpr h)
    unfold sourceWeilExtendedQuadraticForm
    rw [hqtop]
    simp

#print axioms sourceArchimedeanShiftedWeightedLpPMap
#print axioms sourceArchimedeanShiftedWeightedLpPMap_isClosed
#print axioms sourceArchimedeanShiftedFormRootEnergy
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_rootEnergy_lt_top
#print axioms sourceArchimedeanShiftedFormRootEnergy_lowerSemicontinuous
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous
#print axioms sourceArchimedeanShiftedFormRootEnergy_eq_enorm
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
#print axioms sourceWeilBoundedDiagonalPerturbation
#print axioms sourceWeilBoundedDiagonalPerturbation_continuous
#print axioms sourceWeilExtendedQuadraticForm
#print axioms sourceWeilExtendedQuadraticForm_lowerSemicontinuous
#print axioms sourceWeil_shiftedDiagonal_add_boundedPerturbation
#print axioms sourceWeilExtendedQuadraticForm_eq_re
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_sourceWeilExtended_lt_top
#print axioms sourceWeilExtendedQuadraticForm_lowerBound

end Q3.RouteB.D0Pstar
