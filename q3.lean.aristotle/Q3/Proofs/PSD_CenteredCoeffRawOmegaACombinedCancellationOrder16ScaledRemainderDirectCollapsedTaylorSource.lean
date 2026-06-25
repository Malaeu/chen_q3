import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16ScaledRemainderDirectHornerSourceBridge
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationHighOrderTaylorSource

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Taylor receiver for the direct Step33A.1-A sub0 collapsed-expression route.

The active direct route must approximate the whole signed collapsed expression

`ActiveScaleCoeff * D^16(ComponentProductActual)
 - NominalScaleCoeff * D^16(ComponentProductNominal)`

before taking norms or spending the final residual budget.  This file provides
only the proof surface that turns segment-wise center-jet/order-16 Taylor data
for that single expression into the existing direct Horner receiver.  It emits
no generated coefficients, no Horner rows, and no Step33A.1-A closure claim.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/--
Segment-wise degree-15 Taylor remainder receiver for the direct collapsed
scaled-remainder expression.

The generator must supply rational center-jet enclosures for `0..15`, a
proof-grade uniform order-16 derivative bound on the same segment, and the
same-segment radius budget.  The output is exactly in the
`rawOmegaATaylorPolynomial` normalization consumed by the direct Horner bridge.
-/
theorem primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_centerJet15_order16
    (cellL cellU center radius : Rat)
    (coeff coeffErrorAbs : Fin 16 -> Rat)
    (order16Abs remainderAbs : Rat)
    (hCenterMem :
      (center : Real) ∈ Set.Icc (cellL : Real) (cellU : Real))
    (hSmooth :
      ContDiff Real 16
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression)
    (hCoeffErrorNonneg :
      ∀ j : Fin 16, 0 <= (coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            (center : Real) /
            (Nat.factorial j.1 : Real) -
          (coeff j : Real)‖ <=
          (coeffErrorAbs j : Real))
    (hOrder16 :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        ‖iteratedDeriv 16
            primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta‖ <=
          (order16Abs : Real))
    (hRadius :
      ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
        ‖eta - (center : Real)‖ <= (radius : Real))
    (hBudget :
      (∑ j : Fin 16,
          (coeffErrorAbs j : Real) * (radius : Real) ^ j.1) +
          (order16Abs : Real) * (radius : Real) ^ 16 /
            (Nat.factorial 16 : Real) <=
        (remainderAbs : Real)) :
    ∀ eta ∈ Set.Icc (cellL : Real) (cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          rawOmegaATaylorPolynomial 15 center coeff eta‖ <=
        (remainderAbs : Real) := by
  exact
    centerJetTaylor_error_bound_of_order16
      (f :=
        primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression)
      (a := (cellL : Real)) (b := (cellU : Real))
      (radius := (radius : Real)) (order16Abs := (order16Abs : Real))
      (remainderAbs := (remainderAbs : Real)) (center := center)
      coeff coeffErrorAbs hCenterMem hSmooth hCoeffErrorNonneg hCenterJet
      hOrder16 hRadius hBudget

/--
Rational proof-data shape for one direct collapsed-expression Taylor segment.

`Valid` below is the proof object.  The data alone is only a normalized row
container for a future generator.
-/
structure Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert where
  cellL : Rat
  cellU : Rat
  center : Rat
  radius : Rat
  coeff : Fin 16 -> Rat
  coeffErrorAbs : Fin 16 -> Rat
  order16Abs : Rat
  remainderAbs : Rat

namespace Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert

def poly
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert)
    (eta : Real) : Real :=
  rawOmegaATaylorPolynomial 15 data.center data.coeff eta

def toDirectHornerSegment
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert)
    (polyLower polyUpper lower upper residualAbs : Rat) :
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert where
  cellL := data.cellL
  cellU := data.cellU
  center := data.center
  degree := 15
  coeff := data.coeff
  polyErrorAbs := data.remainderAbs
  polyLower := polyLower
  polyUpper := polyUpper
  lower := lower
  upper := upper
  residualAbs := residualAbs

structure Valid
    (data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert) :
    Prop where
  cellSubset :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)
  centerMem :
    (data.center : Real) ∈ Set.Icc (data.cellL : Real) (data.cellU : Real)
  smooth :
    ContDiff Real 16
      primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
  coeffErrorNonneg :
    ∀ j : Fin 16, 0 <= (data.coeffErrorAbs j : Real)
  remainderNonneg :
    0 <= (data.remainderAbs : Real)
  centerJet :
    ∀ j : Fin 16,
      ‖iteratedDeriv j.1
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          (data.center : Real) /
          (Nat.factorial j.1 : Real) -
        (data.coeff j : Real)‖ <=
        (data.coeffErrorAbs j : Real)
  order16 :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖iteratedDeriv 16
          primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
          eta‖ <=
        (data.order16Abs : Real)
  radiusBound :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖eta - (data.center : Real)‖ <= (data.radius : Real)
  remainderBudget :
    (∑ j : Fin 16,
        (data.coeffErrorAbs j : Real) * (data.radius : Real) ^ j.1) +
        (data.order16Abs : Real) * (data.radius : Real) ^ 16 /
          (Nat.factorial 16 : Real) <=
      (data.remainderAbs : Real)

namespace Valid

theorem remainder_bound
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (data.cellL : Real) (data.cellU : Real),
      ‖primaryFiniteRow0Parent0Split100Sub0CombinedOrder16ScaledRemainderCollapsedExpression
            eta -
          data.poly eta‖ <=
        (data.remainderAbs : Real) := by
  simpa [Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.poly] using
    primaryFiniteRow0Parent0Split100Sub0_combinedOrder16ScaledRemainder_collapsed_segment_remainder_of_centerJet15_order16
      data.cellL data.cellU data.center data.radius data.coeff data.coeffErrorAbs
      data.order16Abs data.remainderAbs h.centerMem h.smooth h.coeffErrorNonneg
      h.centerJet h.order16 h.radiusBound h.remainderBudget

theorem to_directHorner_valid
    {data : Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert}
    (h : data.Valid)
    {polyLower polyUpper lower upper residualAbs : Rat}
    {range :
      Step33Sub0CombinedOrder16ScaledRemainderDirectHornerRangeCert
        (data.toDirectHornerSegment polyLower polyUpper lower upper residualAbs)}
    (hRange : range.Valid)
    (hIntervalLower :
      (lower : Real) <= (polyLower : Real) - (data.remainderAbs : Real))
    (hIntervalUpper :
      (polyUpper : Real) + (data.remainderAbs : Real) <= (upper : Real))
    (hResidualNonneg : 0 <= (residualAbs : Real))
    (hLowerBudget : -(residualAbs : Real) <= (lower : Real))
    (hUpperBudget : (upper : Real) <= (residualAbs : Real)) :
    (data.toDirectHornerSegment polyLower polyUpper lower upper residualAbs).Valid := by
  refine
    Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.Valid.of_collapsed_horner_range
      ?_ ?_ ?_ hRange ?_ ?_ ?_ ?_ ?_
  · intro eta hEta
    exact h.cellSubset eta hEta
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using h.remainderNonneg
  · intro eta hEta
    simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment,
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.poly,
      Step33Sub0CombinedOrder16ScaledRemainderDirectHornerCert.poly]
      using h.remainder_bound eta hEta
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using hIntervalLower
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using hIntervalUpper
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using hResidualNonneg
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using hLowerBudget
  · simpa [
      Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert.toDirectHornerSegment]
      using hUpperBudget

end Valid
end Step33Sub0CombinedOrder16ScaledRemainderDirectCollapsedTaylorCert

end Step33
end PSDpd
end Q3
