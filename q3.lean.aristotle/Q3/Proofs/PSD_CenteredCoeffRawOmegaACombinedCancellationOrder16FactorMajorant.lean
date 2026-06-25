import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Order-16 structural reduction for the Step33A.1-A sub0 combined-cancellation
source.

This file does not provide a numerical or rational order-16 bound.  It only
collapses the assembled component-source algebra to the actual component product
whose factor derivatives must be bounded by the next certificate layer.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private def primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyOrder16
    (degree : Nat) (center : Rat)
    (coeff : Fin (degree + 1) -> Rat) : Polynomial Real :=
  ∑ i : Fin (degree + 1),
    Polynomial.C (coeff i : Real) *
      (Polynomial.X - Polynomial.C (center : Real)) ^ i.1

private theorem primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolyOrder16_eval
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial degree center coeff eta =
      (primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyOrder16
        degree center coeff).eval eta := by
  unfold rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyOrder16
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

private theorem primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval_order16
    (p : Polynomial Real) (n : Nat) :
    iteratedDeriv n (fun eta : Real => p.eval eta) =
      fun eta : Real => (Polynomial.derivative^[n] p).eval eta := by
  induction n generalizing p with
  | zero =>
      ext eta
      simp [iteratedDeriv]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      ext eta
      rw [ih p]
      rw [Polynomial.deriv]
      rw [Function.iterate_succ_apply']

/-- The degree-15 residual derivative model contributes no order-16 source. -/
private theorem
    primaryFiniteRow0Parent0Split100Sub0_residualDerivmodel_order16_eq_zero
    (eta : Real) :
    iteratedDeriv 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
        eta = 0 := by
  let p :=
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyOrder16
      15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff
  have hEval :
      rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff =
        fun eta : Real => p.eval eta := by
    funext eta
    exact
      primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPolyOrder16_eval
        15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta
  have hDeriv :
      iteratedDeriv 16
          (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
            primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
          eta =
        (Polynomial.derivative^[16] p).eval eta := by
    rw [hEval]
    simpa using congrFun
      (primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval_order16
        p 16) eta
  have hPolyDeriv :
      (Polynomial.derivative^[16] p).eval eta = 0 := by
    unfold p primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPolyOrder16
    rw [Polynomial.iterate_derivative_sum
      (R := Real) (k := 16) (s := Finset.univ)
      (f := fun i : Fin 16 =>
        Polynomial.C
            (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff i :
              Real) *
          (Polynomial.X - Polynomial.C ((((1 : Rat) / 20 : Rat) : Real))) ^
            i.1)]
    rw [Polynomial.eval_finset_sum]
    apply Finset.sum_eq_zero
    intro i _hi
    have hdesc : i.1.descFactorial 16 = 0 :=
      Nat.descFactorial_eq_zero_iff_lt.mpr i.2
    rw [Polynomial.iterate_derivative_C_mul]
    rw [Polynomial.iterate_derivative_X_sub_pow i.1 16
      ((((1 : Rat) / 20 : Rat) : Real))]
    rw [hdesc]
    simp
  rw [hDeriv, hPolyDeriv]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff16 :
    ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual := by
  have hOmegaPrime :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16
  have hOmega :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16
  have hShapeSq :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
  exact (hOmegaPrime.mul hShapeSq).add (hOmega.mul hShapeSqDeriv)

private theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16 :
    ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal := by
  have hOmegaPrimePoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff
  have hOmegaPoly :
      ContDiff Real 16 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff
  have hShapeSqPoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff
  have hShapeSqDerivPoly :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real 16
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
  exact
    (hOmegaPrimePoly.mul hShapeSqPoly).add
      (hOmegaPoly.mul hShapeSqDerivPoly)

private theorem
    primaryFiniteRow0Parent0Split100Sub0_residualTaylor_order16_eq_nominalProduct
    (eta : Real) :
    iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly eta =
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  have hResidualFun :
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly =
        (rawOmegaATaylorPolynomial
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
              ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff -
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff) := by
    funext eta
    exact
      (primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
        eta).symm
  have hAssembledFun :
      (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) =
        fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    funext eta
    rw [primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct]
    rw [primaryFiniteRow0Parent0Split100Sub0_nominalProduct_eq_componentProductNominal]
  have hAssembledPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
  have hModelPoly :
      ContDiff Real 16
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff) :=
    rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff
  have hNominal :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16
  calc
    iteratedDeriv 16 primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly eta
        = iteratedDeriv 16
            (rawOmegaATaylorPolynomial
                  primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
                  ((1 : Rat) / 20)
                  primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff -
                rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
                  primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
            eta := by
          rw [hResidualFun]
    _ = iteratedDeriv 16
            (rawOmegaATaylorPolynomial
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
              ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff)
            eta -
          iteratedDeriv 16
            (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
            eta := by
          rw [iteratedDeriv_sub hAssembledPoly.contDiffAt hModelPoly.contDiffAt]
    _ = iteratedDeriv 16
            (fun eta : Real =>
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta)
            eta := by
          rw [
            primaryFiniteRow0Parent0Split100Sub0_residualDerivmodel_order16_eq_zero,
            hAssembledFun]
          ring
    _ = (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
          rw [iteratedDeriv_const_mul hNominal.contDiffAt]

private theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq
    (eta : Real) :
    iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        eta =
      iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
  have hResidualFun :
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual =
        (primaryFiniteRow0Parent0Split100Sub0ComponentProductActual -
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal) := by
    funext eta
    exact
      (primaryFiniteRow0Parent0Split100Sub0_componentProductError_eq_cancellationResidual
        eta).symm
  have hActual :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductActual :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff16
  have hNominal :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16
  calc
    iteratedDeriv 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
        eta =
      iteratedDeriv 16
        (primaryFiniteRow0Parent0Split100Sub0ComponentProductActual -
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal)
        eta := by
          rw [hResidualFun]
    _ = iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
          rw [iteratedDeriv_sub hActual.contDiffAt hNominal.contDiffAt]

/--
The assembled order-16 component-source algebra is just the active-scale
multiple of the actual component product's order-16 derivative.

This is a structural bridge only: the remaining proof-grade obligation is a
uniform factor-majorant bound for the right-hand side on `eta ∈ [0, 1/10]`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellationOrder16Source_eq_activeActual
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
        iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
  rw [
    primaryFiniteRow0Parent0Split100Sub0_residualTaylor_order16_eq_nominalProduct,
    primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq]
  ring

end Step33
end PSDpd
end Q3
