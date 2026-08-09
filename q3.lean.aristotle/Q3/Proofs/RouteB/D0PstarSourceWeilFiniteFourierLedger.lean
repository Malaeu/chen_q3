import Q3.Proofs.RouteB.D0PstarSourceLogWindowFourierL2Isometry
import Q3.Proofs.RouteB.D0PstarSourceWeilFiniteFormCCMWeilCrosswalk
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual

set_option linter.mathlibStandardSet false

open Complex MeasureTheory
open scoped BigOperators FourierTransform ComplexConjugate

noncomputable section

namespace Q3.RouteB.D0Pstar

private theorem
    coeFn_sourceLogWindowFourierL2Isometry_ccmFiniteSynthesis
    (i : PairIndex)
    (c : CCMModeFinite i.N → ℂ) :
    ((sourceLogWindowFourierL2Isometry i
        (ccmFiniteSynthesis i c) :
          MeasureTheory.Lp ℂ 2
            (volume : Measure ℝ)) : ℝ → ℂ)
      =ᵐ[volume]
        (fun t =>
          ∑ j,
            c j *
              𝓕
                (logWindowZeroExtendedMode i
                  (ccmModeFinite i.N j)) t) := by
  classical
  simp only [ccmFiniteSynthesis, LinearMap.coe_mk, AddHom.coe_mk,
    map_sum, map_smul]
  have hcoe :
      (((∑ j, c j • sourceLogWindowFourierL2Isometry i
          (V_n_m i (ccmModeFinite i.N j))) :
            MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)) : ℝ → ℂ)
        =ᵐ[volume]
          (fun t =>
            ∑ j,
              c j *
                (((sourceLogWindowFourierL2Isometry i
                    (V_n_m i (ccmModeFinite i.N j)) :
                      MeasureTheory.Lp ℂ 2
                        (volume : Measure ℝ)) : ℝ → ℂ) t)) := by
    induction (Finset.univ : Finset (CCMModeFinite i.N)) using
        Finset.induction_on with
    | empty =>
        simpa using
          (MeasureTheory.Lp.coeFn_zero ℂ 2 (volume : Measure ℝ))
    | @insert j s hjs ih =>
        rw [Finset.sum_insert hjs]
        refine (MeasureTheory.Lp.coeFn_add _ _).trans ?_
        simpa only [Finset.sum_insert hjs, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul] using
          (MeasureTheory.Lp.coeFn_smul (c j)
            (sourceLogWindowFourierL2Isometry i
              (V_n_m i (ccmModeFinite i.N j)))).add ih
  refine hcoe.trans ?_
  induction (Finset.univ : Finset (CCMModeFinite i.N)) using
      Finset.induction_on with
  | empty => simp
  | @insert j s hjs ih =>
      simp only [Finset.sum_insert hjs]
      filter_upwards
        [coeFn_sourceLogWindowFourierL2Isometry_apply_mode
          i (ccmModeFinite i.N j), ih] with t hjt hist
      rw [hjt, hist]

private theorem sourceArchimedeanFiniteSynthesisPairing_eq_modeSum
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∫ t : ℝ,
        conj
            (((sourceLogWindowFourierL2Isometry i
                (ccmFiniteSynthesis i c) :
                  MeasureTheory.Lp ℂ 2
                    (volume : Measure ℝ)) : ℝ → ℂ) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
            (((sourceLogWindowFourierL2Isometry i
                (ccmFiniteSynthesis i d) :
                  MeasureTheory.Lp ℂ 2
                    (volume : Measure ℝ)) : ℝ → ℂ) t)) =
      ∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k := by
  classical
  have hc :=
    coeFn_sourceLogWindowFourierL2Isometry_ccmFiniteSynthesis i c
  have hd :=
    coeFn_sourceLogWindowFourierL2Isometry_ccmFiniteSynthesis i d
  calc
    _ = ∫ t : ℝ,
          ∑ j, ∑ k,
            star (c j) *
              (conj
                  (𝓕
                    (logWindowZeroExtendedMode i
                      (ccmModeFinite i.N j)) t) *
                (sourceArchimedeanMultiplier t : ℂ) *
                𝓕
                  (logWindowZeroExtendedMode i
                    (ccmModeFinite i.N k)) t) *
              d k := by
      apply integral_congr_ae
      filter_upwards [hc, hd] with t hct hdt
      rw [hct, hdt]
      simp only [map_sum, map_mul]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      simp only [starRingEnd_apply]
      ring
    _ = ∑ j, ∑ k,
          ∫ t : ℝ,
            star (c j) *
              (conj
                  (𝓕
                    (logWindowZeroExtendedMode i
                      (ccmModeFinite i.N j)) t) *
                (sourceArchimedeanMultiplier t : ℂ) *
                𝓕
                  (logWindowZeroExtendedMode i
                    (ccmModeFinite i.N k)) t) *
              d k := by
      rw [integral_finset_sum]
      · congr with j
        rw [integral_finset_sum]
        intro k _
        exact ((sourceArchimedeanModePairing_integrable i
          (ccmModeFinite i.N j) (ccmModeFinite i.N k)).const_mul _).mul_const _
      · intro j _
        exact integrable_finset_sum Finset.univ fun k _ =>
          ((sourceArchimedeanModePairing_integrable i
            (ccmModeFinite i.N j) (ccmModeFinite i.N k)).const_mul _).mul_const _
    _ = ∑ j, ∑ k,
          star (c j) *
            sourceArchimedeanModePairing i
              (ccmModeFinite i.N j)
              (ccmModeFinite i.N k) *
            d k := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [sourceArchimedeanModePairing]
      rw [integral_mul_const, integral_const_mul]

/-- The exact finite source Weil ledger, expressed through the whole-line
Fourier carrier, equals the literal finite CCM Weil matrix form. -/
theorem sourceWeilFiniteFourierLedger_eq_ccmWeilMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    ((∑ j, ∑ k,
        star (c j) *
          sourceW02ModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k) +
      (∫ t : ℝ,
        conj
            (((sourceLogWindowFourierL2Isometry i
                (ccmFiniteSynthesis i c) :
                  MeasureTheory.Lp ℂ 2
                    (volume : Measure ℝ)) : ℝ → ℂ) t) *
          (sourceArchimedeanMultiplier t : ℂ) *
            (((sourceLogWindowFourierL2Isometry i
                (ccmFiniteSynthesis i d) :
                  MeasureTheory.Lp ℂ 2
                    (volume : Measure ℝ)) : ℝ → ℂ) t)) -
      (∑ j, ∑ k,
        star (c j) *
          sourcePrimeModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k)) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWeilMatFinite i.m i.N j k : ℂ) *
          d k := by
  rw [sourceArchimedeanFiniteSynthesisPairing_eq_modeSum]
  exact sourceWeilFiniteForm_eq_ccmWeilMatrixForm i c d

#print axioms sourceWeilFiniteFourierLedger_eq_ccmWeilMatrixForm

end Q3.RouteB.D0Pstar
