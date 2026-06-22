import Q3.Proofs.PSD_CenteredCoeffRawOmegaAHRawLanding

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Step33A.1-A component Taylor coefficient assembly support.

This file only closes the exact algebraic subtraction layer in the active
`RawTaylorCoeffCert` residual convention.  It does not claim that a
proof-grade component product polynomial has been assembled from
`omega`, `omegaPrime`, `shapeSq`, and `shapeSqDeriv`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeDeltaLiveRationalPayloadImport
namespace RawOmegaAChunkIntegral
namespace RawOmegaATaylorModelCertificate

def primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree : Nat := 45

/-- Degree-45 zero extension of the active degree-15 derivative model. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  if h : i.1 < 16 then
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff ⟨i.1, h⟩
  else
    0

/-- Residual coefficients obtained by subtracting the active degree-15
derivative model from a rational degree-45 raw-derivative model. -/
def primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
    (assembledRawDerivCoeff :
      Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1) ->
        Rat)
    (i : Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1)) :
    Rat :=
  assembledRawDerivCoeff i -
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded i

theorem rawOmegaATaylorPolynomial_sub_coeff
    (degree : Nat) (center : Rat)
    (lhs rhs : Fin (degree + 1) -> Rat) (eta : Real) :
    rawOmegaATaylorPolynomial
        degree center (fun i => lhs i - rhs i) eta =
      rawOmegaATaylorPolynomial degree center lhs eta -
        rawOmegaATaylorPolynomial degree center rhs eta := by
  unfold rawOmegaATaylorPolynomial
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  norm_num
  ring

/-- Algebraic coefficient-subtraction crosswalk for the active degree-45
component residual model.

This theorem is conditional in the intended sense: it works for any rational
degree-45 `assembledRawDerivCoeff`.  A separate upstream proof must still build
that coefficient vector from proof-grade component Taylor data.

This is intentionally a same-degree bridge.  The bridge from the active
degree-15 derivative model to `ResidualDerivmodelCoeffPadded` is a separate
zero-extension gate, not hidden inside this theorem. -/
theorem primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_sameDegree_crosswalk_of_assembled
    (assembledRawDerivCoeff :
      Fin (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree + 1) ->
        Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20) assembledRawDerivCoeff eta -
        rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta =
      rawOmegaATaylorPolynomial
        primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
        ((1 : Rat) / 20)
        (primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffOf
          assembledRawDerivCoeff) eta := by
  rw [← rawOmegaATaylorPolynomial_sub_coeff
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    ((1 : Rat) / 20) assembledRawDerivCoeff
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeffPadded eta]
  rfl

end RawOmegaATaylorModelCertificate
end RawOmegaAChunkIntegral
end CenteredCoeffPrimeDeltaLiveRationalPayloadImport
end PSDpd
end Q3
