import Q3.Proofs.RouteB.D0Mode4FerrersPhysicalNormalizedZeroExtension
import Q3.Proofs.RouteB.D0ModeZeroFourSelectedFerrersPhysicalProlate

/-!
# Goal 058 G3: selected Ferrers modes in the production ProlatePair

This leaf composes the selected zero-based even carrier indices `0` and `2`
with the canonical whole-line zero extension and `L2` normalization.  The
result inhabits the unchanged production `D0Pstar.ProlatePair`, with positive
integrals, nonzero real Fourier scalars, and the two exact restricted
finite-Fourier eigenrelations.

`ProlatePair` is deliberately weaker than the source predicate
`IsActualProlateModePair`.  This theorem therefore does not claim that the
remaining source fields follow from record inhabitation.  In particular it
does not prove scalar positivity/order, orthogonality, the exact interior zero
counts `0/4`, CCM Lemma 7.2, Goal 058 G3, Route B promotion, or RH.
-/

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB

/-- The selected regular Ferrers witnesses now construct the unchanged
production prolate-pair record.  The conclusion keeps the exact witness
identity visible so the record cannot be mistaken for a parallel source
family. -/
theorem exists_modeZero_modeFour_selectedFerrersProductionProlatePair
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    ∃ (S0 : Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0))
      (S4 : Mode4FerrersRegularEvenProlateSolution mProject K
          (mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2))
      (P : D0Pstar.ProlatePair),
      P.pw.lambda = Real.sqrt mProject ∧
      P.h0 = S0.normalizedPhysicalMode ∧
      P.h4 = S4.normalizedPhysicalMode ∧
      0 < P.I0 ∧ 0 < P.I4 ∧
      P.chi0 ≠ 0 ∧ P.chi2 ≠ 0 ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction P.pw.lambda P.h0 x =
          (P.chi0 : ℂ) * P.h0 x) ∧
      (∀ x ∈ Icc (-P.pw.lambda) P.pw.lambda,
        D0Pstar.finiteFourierAction P.pw.lambda P.h4 x =
          (P.chi2 : ℂ) * P.h4 x) ∧
      mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 0 <
        mode4ClassicalEvenEigenvalue (mode4JacobiG mProject) 2 := by
  obtain ⟨hS0, hS4, hLambdaOrder, _hLambdaFourLt⟩ :=
    exists_modeZero_modeFour_selectedFerrersRegularEvenProlateSolutions
      mProject K hm hK hsep
  obtain ⟨S0⟩ := hS0
  obtain ⟨S4⟩ := hS4
  obtain ⟨chi0, hchi0, hFourier0⟩ :=
    S0.exists_normalizedPhysicalMode_finiteFourier_eq_real_nonzero_scalar_mul hm
  obtain ⟨chi2, hchi2, hFourier4⟩ :=
    S4.exists_normalizedPhysicalMode_finiteFourier_eq_real_nonzero_scalar_mul hm
  obtain ⟨I0, hI0, hIntegral0⟩ :=
    S0.integral_normalizedPhysicalMode_pos hm
  obtain ⟨I4, hI4, hIntegral4⟩ :=
    S4.integral_normalizedPhysicalMode_pos hm
  have hzeroMem : (0 : ℝ) ∈
      Icc (-Real.sqrt mProject) (Real.sqrt mProject) := by
    have hs := Real.sqrt_nonneg (mProject : ℝ)
    constructor <;> linarith
  let P : D0Pstar.ProlatePair := {
    pw := {
      lambda := Real.sqrt mProject
      action := D0Pstar.prolateWaveExpression (Real.sqrt mProject)
      action_eq := rfl }
    h0 := S0.normalizedPhysicalMode
    h4 := S4.normalizedPhysicalMode
    chi0 := chi0
    chi2 := chi2
    I0 := I0
    I4 := I4
    h0_even := S0.normalizedPhysicalMode_even
    h4_even := S4.normalizedPhysicalMode_even
    h0_support := S0.normalizedPhysicalMode_support
    h4_support := S4.normalizedPhysicalMode_support
    h0_integrable := S0.normalizedPhysicalMode_integrable hm
    h4_integrable := S4.normalizedPhysicalMode_integrable hm
    h0_sqNorm_integrable := S0.normalizedPhysicalMode_sqNorm_integrable hm
    h4_sqNorm_integrable := S4.normalizedPhysicalMode_sqNorm_integrable hm
    h0_normalized := S0.normalizedPhysicalMode_normalized hm
    h4_normalized := S4.normalizedPhysicalMode_normalized hm
    I0_eq_integral := hIntegral0
    I4_eq_integral := hIntegral4
    h0_fourier_center := hIntegral0.trans
      (D0Pstar.integral_eq_chi_mul_zero_of_finiteFourier_eigenrelation
        (Real.sqrt mProject) S0.normalizedPhysicalMode (chi0 : ℂ)
        S0.normalizedPhysicalMode_support (hFourier0 0 hzeroMem))
    h4_fourier_center := hIntegral4.trans
      (D0Pstar.integral_eq_chi_mul_zero_of_finiteFourier_eigenrelation
        (Real.sqrt mProject) S4.normalizedPhysicalMode (chi2 : ℂ)
        S4.normalizedPhysicalMode_support (hFourier4 0 hzeroMem)) }
  refine ⟨S0, S4, P, rfl, rfl, rfl, hI0, hI4, hchi0, hchi2, ?_, ?_,
    hLambdaOrder⟩
  · intro x hx
    exact hFourier0 x hx
  · intro x hx
    exact hFourier4 x hx

#print axioms exists_modeZero_modeFour_selectedFerrersProductionProlatePair

end Q3.RouteB
