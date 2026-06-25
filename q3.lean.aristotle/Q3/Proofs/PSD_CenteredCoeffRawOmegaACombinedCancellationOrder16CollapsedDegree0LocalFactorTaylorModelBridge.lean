import Q3.Proofs.PSD_CenteredCoeffRawOmegaACenteredTaylorDerivativeModel18
import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0RawD17SignedFactorRows

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Local-factor Taylor-model bridge for the direct collapsed degree-0 signed
source route.

This file is the first route-C bridge selected by the Browser/Computer Use
review.  It does not emit numerical rows and does not close Step33A.1-A.  It
only proves that segment0 local Taylor models for the two product factors,
together with exact term-corner/raw/poly arithmetic rows, feed the already
checked signed-source segment receiver for

`ActiveScaleCoeff * D17(ComponentProductActual) - deriv(NominalOrder16Poly)`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
    Rat := 0

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
    Rat := (1 : Rat) / 20

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
    Rat := (1 : Rat) / 40

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
    Rat := (1 : Rat) / 40

private theorem primaryFiniteRow0Parent0Split100Sub0_segment0_cellSubset
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
          Real)) :
    eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
  constructor
  · simpa [
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL] using
      hEta.1
  · norm_num [
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU] at hEta ⊢
    linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_segment0_radiusCell
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
          Real)) :
    eta ∈ Set.Icc
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) -
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real))
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) +
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real)) := by
  constructor <;>
    norm_num [
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center,
      primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius] at hEta ⊢ <;>
    linarith

private theorem primaryFiniteRow0Parent0Split100Sub0_interval_of_model_error
    {x poly err lower upper : Real}
    (hModel : ‖x - poly‖ <= err)
    (hLower : lower <= poly - err)
    (hUpper : poly + err <= upper) :
    lower <= x ∧ x <= upper := by
  rw [Real.norm_eq_abs] at hModel
  have hAbs := abs_le.mp hModel
  constructor <;> linarith

/--
Segment0 local Taylor-model data for the raw-D17 factor pair.

The rows are still proof data, not trusted numerics.  `Valid` below is the
actual proof object.
-/
structure Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert where
  omegaCoeff : Fin 18 -> Rat
  omegaCoeffErrorAbs : Fin 18 -> Rat
  omegaOrder18Abs : Rat
  shapeSqCoeff : Fin 18 -> Rat
  shapeSqCoeffErrorAbs : Fin 18 -> Rat
  shapeSqOrder18Abs : Rat
  omegaLower : Nat -> Rat
  omegaUpper : Nat -> Rat
  shapeSqLower : Nat -> Rat
  shapeSqUpper : Nat -> Rat
  termLower : Nat -> Rat
  termUpper : Nat -> Rat
  rawLower : Rat
  rawUpper : Rat
  polyLower : Rat
  polyUpper : Rat
  lower : Rat
  upper : Rat

namespace Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert

def omegaCoeffReal
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Fin 18 -> Real :=
  fun j => (cert.omegaCoeff j : Real)

def omegaCoeffErrorReal
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Fin 18 -> Real :=
  fun j => (cert.omegaCoeffErrorAbs j : Real)

def shapeSqCoeffReal
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Fin 18 -> Real :=
  fun j => (cert.shapeSqCoeff j : Real)

def shapeSqCoeffErrorReal
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Fin 18 -> Real :=
  fun j => (cert.shapeSqCoeffErrorAbs j : Real)

def omegaPoly
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert)
    (k : Fin 18) (eta : Real) : Real :=
  centeredTaylorDerivPolynomial18 cert.omegaCoeffReal k
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
      Real)
    eta

def omegaError
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert)
    (k : Fin 18) : Real :=
  centeredTaylorDerivError18 cert.omegaCoeffErrorReal
    (cert.omegaOrder18Abs : Real)
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
      Real)
    k

def shapeSqPoly
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert)
    (k : Fin 18) (eta : Real) : Real :=
  centeredTaylorDerivPolynomial18 cert.shapeSqCoeffReal k
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
      Real)
    eta

def shapeSqError
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert)
    (k : Fin 18) : Real :=
  centeredTaylorDerivError18 cert.shapeSqCoeffErrorReal
    (cert.shapeSqOrder18Abs : Real)
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
      Real)
    k

def toRawD17SignedFactorSegmentCert
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Step33Sub0CollapsedDegree0RawD17SignedFactorSegmentCert where
  cellL := primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL
  cellU := primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU
  omegaLower := cert.omegaLower
  omegaUpper := cert.omegaUpper
  shapeSqLower := cert.shapeSqLower
  shapeSqUpper := cert.shapeSqUpper
  termLower := cert.termLower
  termUpper := cert.termUpper
  rawLower := cert.rawLower
  rawUpper := cert.rawUpper

def toRawPolySegmentCert
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Step33Sub0CollapsedDegree0RawPolySegmentCert :=
  cert.toRawD17SignedFactorSegmentCert.toRawPolySegmentCert
    cert.polyLower cert.polyUpper cert.lower cert.upper

def toSignedSegmentCert
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Step33Sub0CollapsedDegree0SignedSourceSegmentCert :=
  cert.toRawPolySegmentCert.toSignedSegmentCert

/--
Proof-bearing validity predicate for a segment0 local-factor Taylor bridge.

The generator-facing hard fields are the center-jet rows, local order-18 rows,
polynomial range rows, term-corner rows, and exact raw/poly subtraction
bookkeeping.  No final budget is spent here.
-/
structure Valid
    (cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert) :
    Prop where
  omegaSmooth :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual
  shapeSqSmooth :
    ContDiff Real 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
  omegaCoeffErrorNonneg :
    ∀ j : Fin 18, 0 <= (cert.omegaCoeffErrorAbs j : Real)
  shapeSqCoeffErrorNonneg :
    ∀ j : Fin 18, 0 <= (cert.shapeSqCoeffErrorAbs j : Real)
  omegaCenterJet :
    ∀ j : Fin 18,
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
            Real) /
          (Nat.factorial j.1 : Real) -
        (cert.omegaCoeff j : Real)‖ <=
        (cert.omegaCoeffErrorAbs j : Real)
  shapeSqCenterJet :
    ∀ j : Fin 18,
      ‖iteratedDeriv j.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual
          (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
            Real) /
          (Nat.factorial j.1 : Real) -
        (cert.shapeSqCoeff j : Real)‖ <=
        (cert.shapeSqCoeffErrorAbs j : Real)
  omegaOrder18 :
    ∀ eta ∈ Set.Icc
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) -
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real))
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) +
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real)),
      ‖iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0OmegaActual eta‖ <=
        (cert.omegaOrder18Abs : Real)
  shapeSqOrder18 :
    ∀ eta ∈ Set.Icc
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) -
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real))
      ((primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
          Real) +
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
          Real)),
      ‖iteratedDeriv 18 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta‖ <=
        (cert.shapeSqOrder18Abs : Real)
  omegaPolyRows :
    ∀ eta ∈ Set.Icc
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
        Real)
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
        Real),
      ∀ k : Fin 18,
        (cert.omegaLower k.1 : Real) <=
            cert.omegaPoly k eta - cert.omegaError k ∧
          cert.omegaPoly k eta + cert.omegaError k <=
            (cert.omegaUpper k.1 : Real)
  shapeSqPolyRows :
    ∀ eta ∈ Set.Icc
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
        Real)
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
        Real),
      ∀ k : Fin 18,
        (cert.shapeSqLower k.1 : Real) <=
            cert.shapeSqPoly k eta - cert.shapeSqError k ∧
          cert.shapeSqPoly k eta + cert.shapeSqError k <=
            (cert.shapeSqUpper k.1 : Real)
  omegaOrder18Rows :
    (cert.omegaLower 18 : Real) <= -(cert.omegaOrder18Abs : Real) ∧
      (cert.omegaOrder18Abs : Real) <= (cert.omegaUpper 18 : Real)
  shapeSqOrder18Rows :
    (cert.shapeSqLower 18 : Real) <= -(cert.shapeSqOrder18Abs : Real) ∧
      (cert.shapeSqOrder18Abs : Real) <= (cert.shapeSqUpper 18 : Real)
  termCorners :
    cert.toRawD17SignedFactorSegmentCert.termCornerRows
  rawAssembly :
    (cert.rawLower : Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termLower k : Real)) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          (∑ k ∈ Finset.range (18 + 1), (cert.termUpper k : Real)) <=
        (cert.rawUpper : Real)
  polyInterval :
    ∀ eta ∈ Set.Icc
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
        Real)
      (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
        Real),
      (cert.polyLower : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
          (cert.polyUpper : Real)
  lowerFromRawPoly :
    (cert.lower : Real) <= (cert.rawLower : Real) - (cert.polyUpper : Real)
  upperFromRawPoly :
    (cert.rawUpper : Real) - (cert.polyLower : Real) <= (cert.upper : Real)

namespace Valid

private theorem omega_interval
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid)
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
          Real))
    {k : Nat}
    (hk : k ∈ Finset.range (18 + 1)) :
    (cert.omegaLower k : Real) <=
        iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual eta ∧
      iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0OmegaActual eta <=
        (cert.omegaUpper k : Real) := by
  by_cases hk18lt : k < 18
  · let kk : Fin 18 := ⟨k, hk18lt⟩
    have hModel :
        ‖iteratedDeriv kk.1 primaryFiniteRow0Parent0Split100Sub0OmegaActual eta -
            cert.omegaPoly kk eta‖ <=
          cert.omegaError kk := by
      simpa [
        kk,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaPoly,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaError,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaCoeffReal,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaCoeffErrorReal] using
        iteratedDeriv_sub_centeredTaylorDerivPolynomial18_norm_le
          (f := primaryFiniteRow0Parent0Split100Sub0OmegaActual)
          (center :=
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
              Real))
          (radius :=
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real))
          (order18Abs := (cert.omegaOrder18Abs : Real))
          (eta := eta)
          (coeff := cert.omegaCoeffReal)
          (coeffErrorAbs := cert.omegaCoeffErrorReal)
          kk
          (by
            norm_num [
              primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius])
          h.omegaSmooth
          (by
            intro j
            exact h.omegaCoeffErrorNonneg j)
          (by
            intro j
            simpa [
              Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaCoeffReal,
              Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.omegaCoeffErrorReal]
              using h.omegaCenterJet j)
          h.omegaOrder18
          (primaryFiniteRow0Parent0Split100Sub0_segment0_radiusCell hEta)
    have hRows := h.omegaPolyRows eta hEta kk
    simpa [kk] using
      primaryFiniteRow0Parent0Split100Sub0_interval_of_model_error
        hModel hRows.1 hRows.2
  · have hk18 : k = 18 := by
      have hklt19 : k < 18 + 1 := Finset.mem_range.mp hk
      omega
    subst hk18
    have hModel := h.omegaOrder18 eta
      (primaryFiniteRow0Parent0Split100Sub0_segment0_radiusCell hEta)
    rw [Real.norm_eq_abs] at hModel
    have hAbs := abs_le.mp hModel
    constructor <;> linarith [h.omegaOrder18Rows.1, h.omegaOrder18Rows.2]

private theorem shapeSq_interval
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid)
    {eta : Real}
    (hEta :
      eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellL :
          Real)
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0CellU :
          Real))
    {k : Nat}
    (hk : k ∈ Finset.range (18 + 1)) :
    (cert.shapeSqLower k : Real) <=
        iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta ∧
      iteratedDeriv k primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta <=
        (cert.shapeSqUpper k : Real) := by
  by_cases hk18lt : k < 18
  · let kk : Fin 18 := ⟨k, hk18lt⟩
    have hModel :
        ‖iteratedDeriv kk.1 primaryFiniteRow0Parent0Split100Sub0ShapeSqActual eta -
            cert.shapeSqPoly kk eta‖ <=
          cert.shapeSqError kk := by
      simpa [
        kk,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqPoly,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqError,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqCoeffReal,
        Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqCoeffErrorReal] using
        iteratedDeriv_sub_centeredTaylorDerivPolynomial18_norm_le
          (f := primaryFiniteRow0Parent0Split100Sub0ShapeSqActual)
          (center :=
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Center :
              Real))
          (radius :=
            (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius :
              Real))
          (order18Abs := (cert.shapeSqOrder18Abs : Real))
          (eta := eta)
          (coeff := cert.shapeSqCoeffReal)
          (coeffErrorAbs := cert.shapeSqCoeffErrorReal)
          kk
          (by
            norm_num [
              primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0Segment0Radius])
          h.shapeSqSmooth
          (by
            intro j
            exact h.shapeSqCoeffErrorNonneg j)
          (by
            intro j
            simpa [
              Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqCoeffReal,
              Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.shapeSqCoeffErrorReal]
              using h.shapeSqCenterJet j)
          h.shapeSqOrder18
          (primaryFiniteRow0Parent0Split100Sub0_segment0_radiusCell hEta)
    have hRows := h.shapeSqPolyRows eta hEta kk
    simpa [kk] using
      primaryFiniteRow0Parent0Split100Sub0_interval_of_model_error
        hModel hRows.1 hRows.2
  · have hk18 : k = 18 := by
      have hklt19 : k < 18 + 1 := Finset.mem_range.mp hk
      omega
    subst hk18
    have hModel := h.shapeSqOrder18 eta
      (primaryFiniteRow0Parent0Split100Sub0_segment0_radiusCell hEta)
    rw [Real.norm_eq_abs] at hModel
    have hAbs := abs_le.mp hModel
    constructor <;> linarith [h.shapeSqOrder18Rows.1, h.shapeSqOrder18Rows.2]

theorem to_rawD17SignedFactorSegmentValid
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid) :
    cert.toRawD17SignedFactorSegmentCert.Valid where
  cellSubset := by
    intro eta hEta
    exact primaryFiniteRow0Parent0Split100Sub0_segment0_cellSubset hEta
  factorRows := by
    intro eta hEta k hk
    exact ⟨(h.omega_interval hEta hk).1, (h.omega_interval hEta hk).2,
      (h.shapeSq_interval hEta hk).1, (h.shapeSq_interval hEta hk).2⟩
  termCorners := h.termCorners
  rawAssembly := h.rawAssembly

theorem to_rawPolySegmentValid
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid) :
    cert.toRawPolySegmentCert.Valid := by
  simpa [
    Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert.toRawPolySegmentCert]
    using
      h.to_rawD17SignedFactorSegmentValid.to_rawPolySegmentValid
        h.polyInterval h.lowerFromRawPoly h.upperFromRawPoly

theorem to_signedSegmentValid
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid) :
    cert.toSignedSegmentCert.Valid :=
  h.to_rawPolySegmentValid.to_signedSegmentValid

end Valid
end Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert

/--
Route-C bridge theorem: a valid segment0 local-factor Taylor model produces the
already-subtracted signed-source segment row required by the direct collapsed
degree-0 route.
-/
theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_signedSource_segment0_remainder_of_localFactorTaylor18
    {cert : Step33Sub0CollapsedDegree0LocalFactorTaylor18Segment0Cert}
    (h : cert.Valid) :
    cert.toSignedSegmentCert.Valid :=
  h.to_signedSegmentValid

end Step33
end PSDpd
end Q3
