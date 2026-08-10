import Q3.Proofs.RouteB.D0PstarShiftedArchSesquilinearForm
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Topology.Semicontinuous
import Mathlib.Topology.Instances.EReal.Lemmas

noncomputable section

open Complex Filter MeasureTheory Topology
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

/-- The maximal square-root-weight multiplication operator underlying the
shifted positive archimedean form. Its domain is exactly the already locked
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

/-- The maximal square-root-weight multiplication operator is closed. The
proof uses only L2 convergence, extraction of a common almost-everywhere
convergent subsequence, and pointwise multiplication by the fixed weight. -/
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
archimedean form. It is finite exactly on the locked form domain. -/
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
ambient Hilbert space. The proof is the source-faithful Fatou/subsequence
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

#print axioms sourceArchimedeanShiftedWeightedLpPMap
#print axioms sourceArchimedeanShiftedWeightedLpPMap_apply
#print axioms sourceArchimedeanShiftedWeightedLpPMap_isClosed
#print axioms sourceArchimedeanShiftedFormRootEnergy
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_rootEnergy_lt_top
#print axioms sourceArchimedeanShiftedFormRootEnergy_lowerSemicontinuous
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm_lowerSemicontinuous
#print axioms sourceArchimedeanShiftedFormRootEnergy_eq_enorm
#print axioms sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re
#print axioms mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top

end Q3.RouteB.D0Pstar
