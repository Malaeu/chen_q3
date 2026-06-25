import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16NominalPolynomialBridge

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof-grade nominal-polynomial derivative rows for the Step33A.1-A collapsed
degree-0 signed-source route.

This file only proves the polynomial half of the same-segment raw/poly
subtraction receiver:

`deriv NominalOrder16Poly` is the degree-28 rational Taylor polynomial with
coefficients `NominalOrder16PolyDerivCoeff`, and that polynomial has a
proof-grade full-cell interval row obtained from the existing radius/sum-abs
Taylor bound.

It supplies no raw D17 rows, no signed-source interval rows, and no
Step33A.1-A closure claim.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Derivative coefficients for `deriv NominalOrder16Poly` in the same
centered Taylor coordinate. -/
def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff
    (j : Fin 29) : Rat :=
  ((j.1 + 1 : Nat) : Rat) *
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff
      ⟨j.1 + 1, by omega⟩

/-- The independent absolute-value majorant for
`deriv NominalOrder16Poly` on the cell of radius `1/20`. -/
def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
    Rat :=
  ∑ j : Fin 29,
    |primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff j| *
      ((1 : Rat) / 20) ^ j.1

/-- The nominal order-16 coefficient vector is the integrated form of its
formal derivative coefficient vector. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Coeff_eq_integrated_polyDerivCoeff :
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff =
      integratedTaylorCoeff 28
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff
        (primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff 0) := by
  funext j
  rcases j with ⟨j, hj⟩
  cases j with
  | zero =>
      rfl
  | succ k =>
    have hk : k < 29 := by omega
    simp [
      integratedTaylorCoeff,
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff,
      hk]
    have hden : ((k : Rat) + 1) ≠ 0 := by
      positivity
    field_simp [hden]

/-- Differentiating the nominal order-16 polynomial gives the named rational
degree-28 derivative polynomial. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly
    (eta : Real) :
    deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta =
      rawOmegaATaylorPolynomial 28 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff eta := by
  unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
  rw [
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Coeff_eq_integrated_polyDerivCoeff]
  exact
    integratedTaylorPolynomial_deriv_eq_base 28 ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff
      (primaryFiniteRow0Parent0Split100Sub0NominalOrder16Coeff 0) eta

/-- Proof-grade full-cell absolute bound for the nominal derivative polynomial. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le
    {eta : Real}
    (hEta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta‖ <=
      (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
        Real) := by
  have hRadius :=
    primaryFiniteRow0Parent0Split100Sub0_cell_radius_one_twentieth hEta
  have hPoly :
      |rawOmegaATaylorPolynomial 28 ((1 : Rat) / 20)
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff
        eta| <=
        (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat :
          Real) :=
    (abs_rawOmegaATaylorPolynomial_le_sum_abs_coeff_mul_radius
      28
      ((1 : Rat) / 20)
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff
      hRadius).trans
      (by
        dsimp [
          primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat]
        norm_num [Rat.cast_abs])
  rw [
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly]
  simpa [Real.norm_eq_abs] using hPoly

/-- One proof-grade nominal derivative segment row covers the active cell. -/
def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount :
    Nat := 1

def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL
    (_ :
      Fin
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount) :
    Rat := 0

def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU
    (_ :
      Fin
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount) :
    Rat := (1 : Rat) / 10

def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentLower
    (_ :
      Fin
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount) :
    Rat :=
  -primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentUpper
    (_ :
      Fin
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount) :
    Rat :=
  primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivAbsRat

/-- The one nominal-polynomial derivative row covers the full active cell. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_cover :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ∃ i :
        Fin
          primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount,
        eta ∈ Set.Icc
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL
            i : Real)
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU
            i : Real) := by
  intro eta hEta
  refine ⟨⟨0, by
    unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount
    norm_num⟩, ?_⟩
  simpa [
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL,
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU]
    using hEta

/-- Generated-row interface for the nominal-polynomial derivative component.

This is intentionally only the polynomial component row.  It must be paired
with proof-grade raw D17 local rows before the raw/poly same-segment family
receiver can produce a signed-source certificate. -/
theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_segment_interval_generated
    (i :
      Fin
        primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCount) :
    ∀ eta ∈ Set.Icc
        (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL
          i : Real)
        (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU
          i : Real),
      (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentLower
        i : Real) <=
          deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta ∧
        deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly eta <=
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentUpper
            i : Real) := by
  intro eta hEta
  have hFull :
      eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
    simpa [
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellL,
      primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentCellU]
      using hEta
  have hAbs :=
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_abs_le hFull
  simpa [
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentLower,
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivSegmentUpper,
    Real.norm_eq_abs,
    abs_le]
    using hAbs

end Step33
end PSDpd
end Q3
