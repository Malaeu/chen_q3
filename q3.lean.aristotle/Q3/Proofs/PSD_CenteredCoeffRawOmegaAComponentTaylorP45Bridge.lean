import Q3.Proofs.PSD_CenteredCoeffRawOmegaAComponentTaylorRawBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
P45 assembly bridge for the nonfinal Step33A.1-A component Taylor source.

This file connects the checked nominal component product to the named degree-45
assembled raw-derivative polynomial and then to the residual Taylor convention.
The resulting enclosure uses the coarse tight product budget; it is a proof
object, not a final small-budget closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

theorem rawOmegaATaylorPolynomial_add_coeff
    (degree : Nat) (center : Rat)
    (lhs rhs : Fin (degree + 1) -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial degree center (fun i => lhs i + rhs i) eta =
      rawOmegaATaylorPolynomial degree center lhs eta +
        rawOmegaATaylorPolynomial degree center rhs eta := by
  unfold rawOmegaATaylorPolynomial
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  norm_num
  ring

theorem rawOmegaATaylorPolynomial_scale_coeff
    (degree : Nat) (center : Rat) (scale : Rat)
    (coeff : Fin (degree + 1) -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial degree center (fun i => scale * coeff i) eta =
      (scale : Real) * rawOmegaATaylorPolynomial degree center coeff eta := by
  unfold rawOmegaATaylorPolynomial
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  norm_num
  ring

theorem primaryFiniteRow0Parent0Split100Sub0_productCoeffPadded_poly_eq
    (coeff : Fin 32 -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded coeff) eta =
      rawOmegaATaylorPolynomial 31 ((1 : Rat) / 20) coeff eta := by
  let term : Nat -> Real := fun k =>
    ((if h : k < 32 then coeff ⟨k, h⟩ else 0 : Rat) : Real) *
      (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ k
  have h45 :
      rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          (primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded coeff) eta =
        ∑ k ∈ Finset.range 46, term k := by
    unfold rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded
    change (∑ i : Fin 46, term i.1) = ∑ k ∈ Finset.range 46, term k
    exact Fin.sum_univ_eq_sum_range term 46
  have h31 :
      rawOmegaATaylorPolynomial 31 ((1 : Rat) / 20) coeff eta =
        ∑ k ∈ Finset.range 32, term k := by
    unfold rawOmegaATaylorPolynomial
    change
      (∑ i : Fin 32,
        ((coeff i : Rat) : Real) *
          (eta - (((1 : Rat) / 20 : Rat) : Real)) ^ i.1) =
        ∑ k ∈ Finset.range 32, term k
    rw [← Fin.sum_univ_eq_sum_range term 32]
    refine Finset.sum_congr rfl ?_
    intro i _hi
    unfold term
    simp [i.2]
  have hsubset : Finset.range 32 ⊆ Finset.range 46 := by
    intro k hk
    simp only [Finset.mem_range] at hk ⊢
    omega
  have htail :
      ∀ k ∈ Finset.range 46, k ∉ Finset.range 32 -> term k = 0 := by
    intro k _hk46 hknot32
    have hkge : ¬ k < 32 := by
      simpa only [Finset.mem_range] using hknot32
    unfold term
    simp [hkge]
  calc
    rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ProductCoeffPadded coeff) eta
        = ∑ k ∈ Finset.range 46, term k := h45
    _ = ∑ k ∈ Finset.range 32, term k := (Finset.sum_subset hsubset htail).symm
    _ = rawOmegaATaylorPolynomial 31 ((1 : Rat) / 20) coeff eta := h31.symm

theorem primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct
    (eta : Real) :
    rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta =
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff eta *
            rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff eta +
          rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff eta *
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff eta) := by
  unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
  rw [rawOmegaATaylorPolynomial_scale_coeff]
  rw [rawOmegaATaylorPolynomial_add_coeff]
  rw [primaryFiniteRow0Parent0Split100Sub0_productCoeffPadded_poly_eq]
  rw [primaryFiniteRow0Parent0Split100Sub0_productCoeffPadded_poly_eq]
  rw [← primaryFiniteRow0Parent0Split100Sub0_omegaPrime_shapeSq_product_crosswalk]
  rw [← primaryFiniteRow0Parent0Split100Sub0_omega_shapeSqDeriv_product_crosswalk]

theorem primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta| <=
      primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
  have h :=
    primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightProductSource
      hEta
  rw [primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct]
  exact h

theorem primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖(primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
        rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta‖ <=
      primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget := by
  have hSource :=
    primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource
      hEta
  have hCross :=
    primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
      eta
  have hEq :
      (primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta) -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeff eta =
        primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta -
          rawOmegaATaylorPolynomial
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
            ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta := by
    rw [← hCross]
    ring
  rw [hEq, Real.norm_eq_abs]
  exact hSource

end Step33
end PSDpd
end Q3
