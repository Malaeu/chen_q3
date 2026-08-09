import Q3.Proofs.RouteB.D0PstarShiftedArchFormDomain
import Q3.Proofs.RouteB.D0PstarExactArchSymbolWeightedModeL2

noncomputable section

open Complex MeasureTheory
open scoped ENNReal FourierTransform

namespace Q3.RouteB.D0Pstar

/-- Every literal production mode belongs to the exact shifted archimedean
form-domain carrier.  This is fixed-mode membership only; it is not a claim
about every vector of `H_m i`, finite-span inclusion, density, D0.2, or an
associated operator domain. -/
theorem V_n_m_mem_sourceArchimedeanShiftedFormDomain
    (i : PairIndex) (n : ℤ) :
    V_n_m i n ∈ sourceArchimedeanShiftedFormDomain i := by
  rw [mem_sourceArchimedeanShiftedFormDomain_iff]
  let phiLp : MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
    sourceLogWindowFourierL2Isometry i (V_n_m i n)
  change MemLp
    (fun t : ℝ =>
      (sourceArchimedeanShiftedSqrtWeight t : ℂ) *
        (phiLp : ℝ → ℂ) t)
    2 volume
  have hPhi : MemLp (phiLp : ℝ → ℂ) 2 volume :=
    MeasureTheory.Lp.memLp phiLp
  have hPhiEq :
      (phiLp : ℝ → ℂ) =ᵐ[volume]
        (fun t : ℝ => 𝓕 (logWindowZeroExtendedMode i n) t) := by
    simpa [phiLp] using
      coeFn_sourceLogWindowFourierL2Isometry_apply_mode i n
  have hArchLiteral :=
    sourceArchimedeanMultiplier_mul_fourier_logWindowZeroExtendedMode_memLp i n
  have hArchPhi :
      MemLp
        (fun t : ℝ =>
          (sourceArchimedeanMultiplier t : ℂ) *
            (phiLp : ℝ → ℂ) t)
        2 volume := by
    have hEq :
        (fun t : ℝ =>
          (sourceArchimedeanMultiplier t : ℂ) *
            𝓕 (logWindowZeroExtendedMode i n) t)
          =ᵐ[volume]
        (fun t : ℝ =>
          (sourceArchimedeanMultiplier t : ℂ) *
            (phiLp : ℝ → ℂ) t) := by
      filter_upwards [hPhiEq] with t ht
      rw [ht]
    exact MemLp.ae_eq hEq hArchLiteral
  let C : ℝ := |Real.log Real.pi| + Real.log 4 + 7
  have hMajor :
      MemLp
        (fun t : ℝ =>
          ‖(sourceArchimedeanMultiplier t : ℂ) *
              (phiLp : ℝ → ℂ) t‖ +
            C * ‖(phiLp : ℝ → ℂ) t‖)
        2 volume := by
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      hArchPhi.norm.add (hPhi.norm.const_smul C)
  refine hMajor.mono' ?_ ?_
  · have hWeight :
        AEStronglyMeasurable
          (fun t : ℝ =>
            (sourceArchimedeanShiftedSqrtWeight t : ℂ)) volume :=
      (Complex.continuous_ofReal.comp
        sourceArchimedeanShiftedSqrtWeight_continuous).aestronglyMeasurable
    exact hWeight.mul hPhi.1
  · filter_upwards [] with t
    have hWeightNonneg :=
      sourceArchimedeanShiftedSqrtWeight_nonneg t
    have hWeightSq :=
      sourceArchimedeanShiftedSqrtWeight_sq t
    have hMultiplierLeAbs :
        sourceArchimedeanMultiplier t ≤
          |sourceArchimedeanMultiplier t| :=
      le_abs_self _
    have hSquareNonneg :
        0 ≤ (sourceArchimedeanShiftedSqrtWeight t - 1) ^ 2 :=
      sq_nonneg _
    have hWeightLe :
        sourceArchimedeanShiftedSqrtWeight t ≤
          |sourceArchimedeanMultiplier t| + C := by
      dsimp [C]
      nlinarith
    have hPhiNormNonneg :
        0 ≤ ‖(phiLp : ℝ → ℂ) t‖ :=
      norm_nonneg _
    have hMul :=
      mul_le_mul_of_nonneg_right hWeightLe hPhiNormNonneg
    calc
      ‖(sourceArchimedeanShiftedSqrtWeight t : ℂ) *
          (phiLp : ℝ → ℂ) t‖ =
          sourceArchimedeanShiftedSqrtWeight t *
            ‖(phiLp : ℝ → ℂ) t‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg hWeightNonneg]
      _ ≤ (|sourceArchimedeanMultiplier t| + C) *
            ‖(phiLp : ℝ → ℂ) t‖ := hMul
      _ = ‖(sourceArchimedeanMultiplier t : ℂ) *
              (phiLp : ℝ → ℂ) t‖ +
            C * ‖(phiLp : ℝ → ℂ) t‖ := by
              rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
              ring

#print axioms V_n_m_mem_sourceArchimedeanShiftedFormDomain

end Q3.RouteB.D0Pstar
