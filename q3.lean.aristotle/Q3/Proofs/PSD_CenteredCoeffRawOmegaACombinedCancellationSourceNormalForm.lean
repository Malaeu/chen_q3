import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Cancellation-preserving normal-form support for the Step33A.1-A
combined-cancellation source rows.

This file does not emit source intervals and does not instantiate
`Step33Sub0CombinedCancellationSourceIntervalCert.Valid`.  It records the
Lean-checked algebra that is available before the remaining coefficient
alignment bridge:

* the cancellation-residual Cauchy source equals actual minus nominal in the
  repository's factorial-normalized center-jet convention;
* once the residual Taylor center jet is aligned with the same convention, the
  combined source reduces to active actual product minus the residual model row.

The missing nonconditional bridge is the coefficient extraction theorem from
`rawOmegaATaylorPolynomial` coefficients to normalized center jets.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Polynomial realization of `rawOmegaATaylorPolynomial` in the same centered
coefficient convention. -/
private def primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPoly
    (degree : Nat) (center : Rat)
    (coeff : Fin (degree + 1) -> Rat) : Polynomial Real :=
  ∑ i : Fin (degree + 1),
    Polynomial.C (coeff i : Real) *
      (Polynomial.X - Polynomial.C (center : Real)) ^ i.1

/-- The repository's raw Taylor evaluator is evaluation of the corresponding
formal polynomial. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_eval
    (degree : Nat) (center : Rat) (coeff : Fin (degree + 1) -> Rat)
    (eta : Real) :
    rawOmegaATaylorPolynomial degree center coeff eta =
      (primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPoly
        degree center coeff).eval eta := by
  unfold rawOmegaATaylorPolynomial
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPoly
  simp [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

/-- Iterated analytic derivatives of a real polynomial evaluator are evaluations
of formal iterated derivatives. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval
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

/-- Coefficient extraction for the centered raw Taylor polynomial in the
factorial-normalized center-jet convention. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_centerJet_eq_coeff
    (degree : Nat) (coeff : Fin (degree + 1) -> Rat)
    (n : Nat) (hn : n <= degree) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (rawOmegaATaylorPolynomial degree ((1 : Rat) / 20) coeff) n =
      (coeff ⟨n, by omega⟩ : Real) := by
  let p :=
    primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPoly degree ((1 : Rat) / 20) coeff
  have hEval :
      rawOmegaATaylorPolynomial degree ((1 : Rat) / 20) coeff =
        fun eta : Real => p.eval eta := by
    funext eta
    exact primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_eval
      degree ((1 : Rat) / 20) coeff eta
  have hDeriv :
      iteratedDeriv n (rawOmegaATaylorPolynomial degree ((1 : Rat) / 20) coeff)
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter =
        (Polynomial.derivative^[n] p).eval
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter := by
    rw [hEval]
    simpa using congrFun
      (primaryFiniteRow0Parent0Split100Sub0_polynomial_iteratedDeriv_eval p n)
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
  have hCenterSub :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter -
          (((1 : Rat) / 20 : Rat) : Real) = 0 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]
  have hCenterSubInv :
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter -
          (20 : Real)⁻¹ = 0 := by
    norm_num [primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter]
  have hPolyDeriv :
      (Polynomial.derivative^[n] p).eval
          primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter =
        (Nat.factorial n : Real) * (coeff ⟨n, by omega⟩ : Real) := by
    unfold p primaryFiniteRow0Parent0Split100Sub0RawOmegaTaylorPoly
    rw [Polynomial.iterate_derivative_sum
      (R := Real) (k := n) (s := Finset.univ)
      (f := fun i : Fin (degree + 1) =>
        Polynomial.C (coeff i : Real) *
          (Polynomial.X - Polynomial.C ((((1 : Rat) / 20 : Rat) : Real))) ^ i.1)]
    rw [Polynomial.eval_finset_sum]
    let centerR : Real :=
      primaryFiniteRow0Parent0Split100Sub0CombinedCancellationCenter
    let term : Fin (degree + 1) -> Real := fun i =>
      ((Polynomial.derivative^[n])
        (Polynomial.C (coeff i : Real) *
          (Polynomial.X - Polynomial.C ((((1 : Rat) / 20 : Rat) : Real))) ^ i.1)).eval
        centerR
    change (∑ i : Fin (degree + 1), term i) =
      (Nat.factorial n : Real) * (coeff ⟨n, by omega⟩ : Real)
    calc
      (∑ i : Fin (degree + 1), term i) =
          term (⟨n, by omega⟩ : Fin (degree + 1)) := by
        refine Finset.sum_eq_single (⟨n, by omega⟩ : Fin (degree + 1)) ?_ ?_
        · intro i _hi hi_ne
          dsimp [term, centerR]
          rw [Polynomial.iterate_derivative_C_mul]
          rw [Polynomial.iterate_derivative_X_sub_pow]
          by_cases hlt : i.1 < n
          · have hdesc : i.1.descFactorial n = 0 :=
              Nat.descFactorial_eq_zero_iff_lt.mpr hlt
            simp [hdesc]
          · have hneq_val : i.1 ≠ n := by
              intro h
              apply hi_ne
              ext
              exact h
            have hnlt : n < i.1 := lt_of_le_of_ne (le_of_not_gt hlt) hneq_val.symm
            have hpos : 0 < i.1 - n := Nat.sub_pos_of_lt hnlt
            simp [hCenterSubInv, hpos.ne']
        · intro hnot
          exact False.elim (hnot (Finset.mem_univ _))
      _ = (Nat.factorial n : Real) * (coeff ⟨n, by omega⟩ : Real) := by
        dsimp [term, centerR]
        rw [Polynomial.iterate_derivative_C_mul]
        rw [Polynomial.iterate_derivative_X_sub_pow]
        simp [Nat.descFactorial_self]
        ring
  unfold primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
  rw [hDeriv, hPolyDeriv]
  field_simp [Nat.cast_ne_zero]

/-- The actual component product is smooth to every row currently consumed by
the 16-row source interval target. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff_low
    (j : Fin 16) :
    ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ComponentProductActual := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrime :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaPrimeActual] using
      step22OmegaArchWeightDerivClosedForm_contDiff16.of_le hj16
  have hOmega :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0OmegaActual] using
      step22OmegaArchWeight_contDiff16.of_le hj16
  have hShapeSq :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual := by
    unfold primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
    fun_prop
  have hShapeSqDeriv :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivActual,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDeriv] using
      (shapeSqDeriv_contDiff16 11 ((3 : Real) / 10)).of_le hj16
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
  exact (hOmegaPrime.mul hShapeSq).add (hOmega.mul hShapeSqDeriv)

/-- The nominal Taylor-polynomial component product is smooth to every row
currently consumed by the 16-row source interval target. -/
private theorem primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff_low
    (j : Fin 16) :
    ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hOmegaPrimePoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorCoeff).of_le hj16
  have hOmegaPoly :
      ContDiff Real j.1 primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0OmegaTaylorCoeff).of_le hj16
  have hShapeSqPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 16 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorCoeff).of_le hj16
  have hShapeSqDerivPoly :
      ContDiff Real j.1
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly := by
    change ContDiff Real j.1
      (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff)
    exact
      (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorCoeff).of_le hj16
  unfold primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
  exact
    (hOmegaPrimePoly.mul hShapeSqPoly).add
      (hOmegaPoly.mul hShapeSqDerivPoly)

/-- Cancellation-residual Cauchy rows are actual product rows minus nominal
product rows in the same normalized center-jet convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidualCauchyCenterJet
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
          j.1 -
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
          j.1 := by
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_centerJet_eq_cauchy j]
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductActual_centerJet_eq_cauchy j]
  rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet_eq_cauchy j]
  have hFun :
      primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual =
        fun eta : Real =>
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    funext eta
    rw [← primaryFiniteRow0Parent0Split100Sub0_componentProductError_eq_cancellationResidual eta]
  rw [hFun]
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_sub
    j.1
    primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
    (primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff_low j)
    (primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff_low j)]

/-- The assembled rational raw-derivative polynomial exposes exactly the
nominal component-product Cauchy row in the normalized center-jet convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_nominalProductCauchyCenterJet_eq_assembledCoeff_low
    (j : Fin 16) :
    (primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
        ⟨j.1, by
          unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          omega⟩ : Real) =
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
          j.1 := by
  have hjDegree :
      j.1 <= primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree := by
    unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    exact Nat.le_trans (Nat.le_of_lt j.2) (by norm_num)
  have hFun :
      rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff =
        fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    funext eta
    simpa [primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal,
      primaryFiniteRow0Parent0Split100Sub0OmegaPrimeTaylorPoly,
      primaryFiniteRow0Parent0Split100Sub0OmegaTaylorPoly,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqTaylorPoly,
      primaryFiniteRow0Parent0Split100Sub0ShapeSqDerivTaylorPoly] using
      primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_poly_eq_nominalProduct
        eta
  have hJet :=
    congrArg
      (fun f : Real -> Real =>
        primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet f j.1)
      hFun
  change
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff)
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        (fun eta : Real =>
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta)
        j.1 at hJet
  rw [primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_centerJet_eq_coeff
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
    j.1 hjDegree] at hJet
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_const_mul
    j.1
    (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real)
    primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
    (primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff_low j)]
    at hJet
  rw [primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_centerJet_eq_cauchy j]
    at hJet
  exact hJet

/-- Low residual Taylor rows equal nominal product rows minus the active
degree-15 residual derivative model rows, all in the same normalized
center-jet convention. -/
theorem primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
        primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly j.1 =
      (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
          j.1 -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j : Real) := by
  have hj16 : (j.1 : WithTop ENat) ≤ (16 : WithTop ENat) := by
    exact_mod_cast (Nat.le_of_lt j.2)
  have hj15 : j.1 <= 15 := by
    omega
  have hjDegree :
      j.1 <= primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree := by
    unfold primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    omega
  have hResidualFun :
      primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly =
        fun eta : Real =>
          rawOmegaATaylorPolynomial
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
              ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta -
            rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
              primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff eta := by
    funext eta
    unfold primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly
    exact
      (primaryFiniteRow0Parent0Split100Sub0_componentTaylor_residualCoeff_crosswalk
        eta).symm
  rw [hResidualFun]
  have hAssembledPoly :
      ContDiff Real j.1
        (rawOmegaATaylorPolynomial
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
          ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff) :=
    (rawOmegaATaylorPolynomial_contDiff16
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff).of_le hj16
  have hModelPoly :
      ContDiff Real j.1
        (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
          primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff) :=
    (rawOmegaATaylorPolynomial_contDiff16 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff).of_le hj16
  rw [primaryFiniteRow0Parent0Split100Sub0_normalizedCenterJet_sub
    j.1
    (rawOmegaATaylorPolynomial
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff)
    (rawOmegaATaylorPolynomial 15 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff)
    hAssembledPoly hModelPoly]
  rw [primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_centerJet_eq_coeff
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivDegree
    primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff
    j.1 hjDegree]
  rw [primaryFiniteRow0Parent0Split100Sub0_rawOmegaTaylorPoly_centerJet_eq_coeff
    15
    primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff
    j.1 hj15]
  rw [primaryFiniteRow0Parent0Split100Sub0_nominalProductCauchyCenterJet_eq_assembledCoeff_low
    j]

/--
Conditional center-jet normal form for the combined source.

The hypothesis is exactly the remaining coefficient-alignment bridge:
`ResidualTaylorPoly` must expose the low rows as
`nominalScale * nominalProductCauchy - residualModelCoeff` in the same
factorial-normalized center-jet convention.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet
    (j : Fin 16)
    (hResidualJet :
      primaryFiniteRow0Parent0Split100Sub0NormalizedCenterJet
          primaryFiniteRow0Parent0Split100Sub0ResidualTaylorPoly j.1 =
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductNominalCauchyCenterJet
            j.1 -
          (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
            Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
          Real) := by
  unfold primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
  rw [hResidualJet]
  rw [primaryFiniteRow0Parent0Split100Sub0_cancellationResidualCauchy_eq_actual_sub_nominal j]
  ring

/-- Center-jet normal form for the combined source after the local residual
coefficient-alignment bridge has been discharged. -/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model
    (j : Fin 16) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationComponentSourceCenterJet
        j.1 =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActualCauchyCenterJet
            j.1 -
        (primaryFiniteRow0Parent0Split100Sub0ResidualDerivmodelCoeff j :
          Real) :=
  primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_centerJet_eq_activeActual_sub_model_of_residualJet
    j
    (primaryFiniteRow0Parent0Split100Sub0_residualTaylor_centerJet_low_eq_nominalProduct_sub_model
      j)

end Step33
end PSDpd
end Q3
