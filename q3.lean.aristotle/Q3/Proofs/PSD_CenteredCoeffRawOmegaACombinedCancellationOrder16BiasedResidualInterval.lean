import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NonzeroModel

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Signed interval adapter for the Step33A.1-A sub0 biased nonzero-model residual.

This file is interface-only.  It does not generate or prove the signed full-cell
interval rows.  It records the exact way such rows must be assembled into the
`ResidualSourceProp` consumed by the biased nonzero-model bridge.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff16_biasedResidual :
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
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16_biasedResidual :
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

/--
Order-16 cancellation residual is the order-16 actual product row minus the
order-16 nominal product row.

This public bridge is the small algebraic adapter needed by the biased residual
route; it replaces a private equality in the older factor-majorant file without
spending any of that older absolute-majorant budget.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq_biasedResidual
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
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_contDiff16_biasedResidual
  have hNominal :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductNominal_contDiff16_biasedResidual
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

theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_cancel_interval_of_scaled_actual_nominal_intervals
    {actualLower actualUpper activeNominalLower activeNominalUpper
      cancelLower cancelUpper : Real}
    (hActual :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        actualLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
                eta <= actualUpper)
    (hActiveNominal :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        activeNominalLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
                eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
                eta <= activeNominalUpper)
    (hCancelLower : cancelLower <= actualLower - activeNominalUpper)
    (hCancelUpper : actualUpper - activeNominalLower <= cancelUpper) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      cancelLower <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta <= cancelUpper := by
  intro eta hEta
  have ha := hActual eta hEta
  have hn := hActiveNominal eta hEta
  have hEq :
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq_biasedResidual]
    ring
  constructor
  · calc
      cancelLower <= actualLower - activeNominalUpper := hCancelLower
      _ <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta :=
          sub_le_sub ha.1 hn.2
      _ =
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta := by rw [hEq]
  · calc
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
            eta =
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta := hEq
      _ <= actualUpper - activeNominalLower :=
          sub_le_sub ha.2 hn.1
      _ <= cancelUpper := hCancelUpper

/--
Collapsed biased-residual normal form.

This keeps cancellation until the last algebraic step: the residual against the
biased nonzero model is an active-scaled actual row minus a nominal-scaled
nominal row, then the fixed bias is subtracted.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_eq_activeActual_sub_nominalNominal
    (eta : Real) :
    primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
          eta -
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
          eta =
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta -
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly,
    primaryFiniteRow0Parent0Split100Sub0_componentProductCancellationResidual_order16_eq_biasedResidual]
  ring

/--
Direct signed-interval receiver for the collapsed biased residual.

The remaining payload obligation is only the two full-cell signed intervals
shown in the hypotheses.  Center jets alone are not sufficient for this theorem.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_abs_le_of_activeActual_nominal_signed_intervals
    {actualLower actualUpper nominalLower nominalUpper remainderAbs : Real}
    (hActual :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        actualLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
            actualUpper)
    (hNominal :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        nominalLower <=
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta ∧
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta <=
            nominalUpper)
    (hLower :
      -remainderAbs <=
        actualLower - nominalUpper -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real))
    (hUpper :
      actualUpper - nominalLower -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) <=
        remainderAbs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
            eta‖ <=
        remainderAbs := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_eq_activeActual_sub_nominalNominal,
    Real.norm_eq_abs,
    abs_le]
  have ha := hActual eta hEta
  have hn := hNominal eta hEta
  constructor <;> linarith

/--
Rat-facing wrapper for the collapsed signed-interval receiver.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_activeActual_nominal_signed_intervals
    {actualLower actualUpper nominalLower nominalUpper : Real}
    {residualAbs : Rat}
    (hActual :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        actualLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
            actualUpper)
    (hNominal :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        nominalLower <=
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta ∧
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta <=
            nominalUpper)
    (hLower :
      -(residualAbs : Real) <=
        actualLower - nominalUpper -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real))
    (hUpper :
      actualUpper - nominalLower -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) <=
        (residualAbs : Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      residualAbs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_abs_le_of_activeActual_nominal_signed_intervals
      hActual hNominal hLower hUpper

/--
Assemble signed full-cell intervals for the two surviving biased residual
summands into a symmetric bound for `source - biasedNonzeroModel`.

The hypotheses are intentionally signed intervals for the already-scaled terms;
using separate absolute product majorants here would return to the killed coarse
triangle route.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_abs_le_of_scaled_signed_intervals
    {cancelLower cancelUpper nominalLower nominalUpper remainderAbs : Real}
    (hCancel :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        cancelLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
                eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
                eta <= cancelUpper)
    (hNominal :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        nominalLower <=
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
                (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
                  Real)) *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
                eta ∧
          (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
                Real)) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
              eta <= nominalUpper)
    (hLower :
      -remainderAbs <=
        cancelLower + nominalLower -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real))
    (hUpper :
      cancelUpper + nominalUpper -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) <=
        remainderAbs) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedCancellationOrder16ComponentSource
            eta -
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelPoly
            eta‖ <=
        remainderAbs := by
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16Source_sub_biasedNonzeroModelPoly]
  have hc := hCancel eta hEta
  have hn := hNominal eta hEta
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith

/--
Rat-facing wrapper for the live residual source proposition consumed by
`primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound`.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_scaled_signed_intervals
    {cancelLower cancelUpper nominalLower nominalUpper : Real}
    {residualAbs : Rat}
    (hCancel :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        cancelLower <=
            primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
                eta ∧
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
                eta <= cancelUpper)
    (hNominal :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        nominalLower <=
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
                (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
                  Real)) *
              iteratedDeriv 16
                primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
                eta ∧
          (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
                Real)) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
              eta <= nominalUpper)
    (hLower :
      -(residualAbs : Real) <=
        cancelLower + nominalLower -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real))
    (hUpper :
      cancelUpper + nominalUpper -
          (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
            Real) <=
        (residualAbs : Real)) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      residualAbs := by
  exact
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_abs_le_of_scaled_signed_intervals
      hCancel hNominal hLower hUpper

/--
Generator-facing data for the biased residual signed-row route.

The fields are rational row data only.  The proof object is `Valid`: it must
prove signed full-cell intervals for the two already-scaled split terms and the
exact budget arithmetic that spends them against the biased model slack.
-/
structure Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert where
  cancelLower : Rat
  cancelUpper : Rat
  nominalLower : Rat
  nominalUpper : Rat
  residualAbs : Rat

namespace Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert

/--
Proof-bearing validity predicate for a biased residual signed-row certificate.

This is the exact next payload target: once a generated certificate proves
`Valid`, the already checked biased nonzero-model route receives the order-16
direct interval certificate.
-/
structure Valid
    (cert : Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert) :
    Prop where
  cancelInterval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.cancelLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductCancellationResidual
              eta <= (cert.cancelUpper : Real)
  nominalInterval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.nominalLower : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
              (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
                Real)) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
              eta ∧
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff -
            (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff :
              Real)) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal
            eta <= (cert.nominalUpper : Real)
  lowerBudget :
    -(cert.residualAbs : Real) <=
      (cert.cancelLower : Real) + (cert.nominalLower : Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real)
  upperBudget :
    (cert.cancelUpper : Real) + (cert.nominalUpper : Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) <=
      (cert.residualAbs : Real)
  slackBudget :
    (cert.residualAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real)

namespace Valid

theorem to_residualSourceProp
    {cert : Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      cert.residualAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_scaled_signed_intervals
    h.cancelInterval h.nominalInterval h.lowerBudget h.upperBudget

theorem to_order16DirectIntervalValid
    {cert : Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    h.slackBudget h.to_residualSourceProp

end Valid
end Step33Sub0CombinedOrder16BiasedResidualSignedIntervalCert

/--
Generator-facing data for the collapsed active-actual/nominal biased residual
route.

This is the preferred next payload surface: prove signed full-cell intervals for
the active-scaled actual order-16 row and the nominal-scaled nominal order-16
row, then spend their signed difference against the fixed bias.
-/
structure Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert where
  actualLower : Rat
  actualUpper : Rat
  nominalLower : Rat
  nominalUpper : Rat
  residualAbs : Rat

namespace Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert

/--
Proof-bearing validity predicate for the collapsed route.

If only center-jet rows are available, this predicate is intentionally
uninhabited: it needs uniform full-cell signed intervals for the order-16 rows.
-/
structure Valid
    (cert :
      Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert) :
    Prop where
  actualInterval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.actualLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual eta <=
          (cert.actualUpper : Real)
  nominalInterval :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      (cert.nominalLower : Real) <=
          (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
            iteratedDeriv 16
              primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta ∧
        (primaryFiniteRow0Parent0Split100Sub0NominalScaleCoeff : Real) *
          iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0ComponentProductNominal eta <=
          (cert.nominalUpper : Real)
  lowerBudget :
    -(cert.residualAbs : Real) <=
      (cert.actualLower : Real) - (cert.nominalUpper : Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real)
  upperBudget :
    (cert.actualUpper : Real) - (cert.nominalLower : Real) -
        (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16NonzeroModelBiasRat :
          Real) <=
      (cert.residualAbs : Real)
  slackBudget :
    (cert.residualAbs : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSlackRat :
        Real)

namespace Valid

theorem to_residualSourceProp
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelResidualSourceProp
      cert.residualAbs :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedResidual_sourceProp_of_activeActual_nominal_signed_intervals
    h.actualInterval h.nominalInterval h.lowerBudget h.upperBudget

theorem to_order16DirectIntervalValid
    {cert :
      Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert}
    (h : cert.Valid) :
    primaryFiniteRow0Parent0Split100Sub0CombinedOrder16BiasedNonzeroModelOrder16IntervalData.Valid :=
  primaryFiniteRow0Parent0Split100Sub0_combinedOrder16BiasedNonzeroModel_order16_direct_interval_valid_of_residual_bound
    h.slackBudget h.to_residualSourceProp

end Valid
end Step33Sub0CombinedOrder16BiasedResidualActiveActualNominalSignedIntervalCert

end Step33
end PSDpd
end Q3
