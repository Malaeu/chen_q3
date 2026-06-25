import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerCert
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectSourceBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Collapsed-expression bridge for the direct Horner receiver.

The direct Horner receiver consumes a remainder row for
`ComponentSource - NonzeroModelPoly`.  The checked source bridge identifies that
target with the collapsed expression

`ActiveScaleCoeff * D^16(ComponentProductActual)
 - NominalScaleCoeff * D^16(ComponentProductNominal)`.

This file transports future proof-grade collapsed-expression Horner rows into
the existing receiver.  It does not provide coefficients, interval rows, budget
rows, or Step33A.1-A closure.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert
namespace Valid

/--
Constructor for the direct Horner segment receiver from a remainder estimate
against the checked collapsed expression.

This closes only the normalization bridge for the hard `directRemainder` field:
a generator still has to prove the collapsed-expression remainder estimate,
Horner range rows, and final budget rows.
-/
theorem of_collapsed_horner_range
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert}
    {range : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert data}
    (hCell :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hPolyErrorNonneg : 0 <= (data.polyErrorAbs : Real))
    (hCollapsedRemainder :
      ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
        ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
              eta -
            data.poly eta‖ <=
          (data.polyErrorAbs : Real))
    (hRange : range.Valid)
    (hIntervalLower :
      (data.lower : Real) <=
        (data.polyLower : Real) - (data.polyErrorAbs : Real))
    (hIntervalUpper :
      (data.polyUpper : Real) + (data.polyErrorAbs : Real) <=
        (data.upper : Real))
    (hResidualNonneg : 0 <= (data.residualAbs : Real))
    (hLowerBudget : -(data.residualAbs : Real) <= (data.lower : Real))
    (hUpperBudget : (data.upper : Real) <= (data.residualAbs : Real)) :
    data.Valid := by
  refine
    of_horner_range
      hCell
      hPolyErrorNonneg
      ?_
      hRange
      hIntervalLower
      hIntervalUpper
      hResidualNonneg
      hLowerBudget
      hUpperBudget
  intro eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression]
  exact hCollapsedRemainder eta hEta

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert

/--
Family-level constructor from collapsed-expression remainder rows.

The output is the same `Valid` predicate consumed by the existing direct
payload.  This theorem only changes the row-source normalization; it does not
generate or trust any row data.
-/
theorem valid_of_collapsed_horner_rows
    {cert : Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert}
    (hCell :
      ∀ i : Fin cert.n,
        ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
          eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hPolyErrorNonneg :
      ∀ i : Fin cert.n, 0 <= ((cert.seg i).polyErrorAbs : Real))
    (hCollapsedRemainder :
      ∀ i : Fin cert.n,
        ∀ eta ∈ Set.Icc ((cert.seg i).cellL : Real) ((cert.seg i).cellU : Real),
          ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
                eta -
              (cert.seg i).poly eta‖ <=
            ((cert.seg i).polyErrorAbs : Real))
    (hRange : ∀ i : Fin cert.n, (cert.range i).Valid)
    (hIntervalLower :
      ∀ i : Fin cert.n,
        ((cert.seg i).lower : Real) <=
          ((cert.seg i).polyLower : Real) -
            ((cert.seg i).polyErrorAbs : Real))
    (hIntervalUpper :
      ∀ i : Fin cert.n,
        ((cert.seg i).polyUpper : Real) +
            ((cert.seg i).polyErrorAbs : Real) <=
          ((cert.seg i).upper : Real))
    (hSegmentResidualNonneg :
      ∀ i : Fin cert.n, 0 <= ((cert.seg i).residualAbs : Real))
    (hSegmentLowerBudget :
      ∀ i : Fin cert.n,
        -(((cert.seg i).residualAbs : Rat) : Real) <=
          ((cert.seg i).lower : Real))
    (hSegmentUpperBudget :
      ∀ i : Fin cert.n,
        ((cert.seg i).upper : Real) <=
          (((cert.seg i).residualAbs : Rat) : Real))
    (hSegmentBudget :
      ∀ i : Fin cert.n,
        (((cert.seg i).residualAbs : Rat) : Real) <= (cert.residualAbs : Real))
    (hCover :
      Step33Sub0CombinedOrder16ScaledRemainderDirectHornerSegmentCover
        cert.n cert.seg) :
    cert.Valid := by
  refine
    { cellSubset := hCell
      polyErrorNonneg := hPolyErrorNonneg
      directRemainder := ?_
      rangeValid := hRange
      intervalLowerBudget := hIntervalLower
      intervalUpperBudget := hIntervalUpper
      segmentResidualNonneg := hSegmentResidualNonneg
      segmentLowerBudget := hSegmentLowerBudget
      segmentUpperBudget := hSegmentUpperBudget
      segmentBudget := hSegmentBudget
      cover := hCover }
  intro i eta hEta
  rw [
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_eq_collapsedExpression]
  exact hCollapsedRemainder i eta hEta

end Step33Sub0CombinedOrder16ScaledRemainderDirectHornerFamilyCert

end Step33
end PSDpd
end Q3
