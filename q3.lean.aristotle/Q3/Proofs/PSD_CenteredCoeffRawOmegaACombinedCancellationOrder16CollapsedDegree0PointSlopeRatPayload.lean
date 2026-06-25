import Q3.Proofs.PSD_CenteredCoeffRawOmegaACombinedCancellationOrder16CollapsedDegree0PointSlopeRows

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Rational point-row payload for the Step33A.1-A collapsed degree-0 point-slope
route.

This file keeps the route local:

* reuse the checked sharp signed-factor segment rows to get a rational point
  interval for `D17(ComponentProductActual)`;
* multiply that signed raw interval by the checked tight active-scale interval
  using all four corners;
* evaluate the nominal derivative polynomial exactly at the local point; and
* package the already-subtracted point interval as `PointRowCert.Valid`.

It does not claim the point-slope budget is killed.  The rows below are a
proof-grade Rat payload, but their tightness still has to be audited against
the budget/sign requirements.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral
open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

private theorem primaryFiniteRow0Parent0Split100Sub0_sum_interval_rat
    {ι : Type} [DecidableEq ι] (s : Finset ι)
    {x : ι -> Real} {lower upper : ι -> Rat}
    (hTerm :
      ∀ i ∈ s, (lower i : Real) <= x i ∧ x i <= (upper i : Real)) :
    ((∑ i ∈ s, lower i : Rat) : Real) <= (∑ i ∈ s, x i) ∧
      (∑ i ∈ s, x i) <= ((∑ i ∈ s, upper i : Rat) : Real) := by
  constructor
  · rw [Rat.cast_sum]
    exact Finset.sum_le_sum fun i hi => (hTerm i hi).1
  · rw [Rat.cast_sum]
    exact Finset.sum_le_sum fun i hi => (hTerm i hi).2

def primaryFiniteRow0Parent0Split100Sub0_min4Rat
    (a b c d : Rat) : Rat :=
  min (min a b) (min c d)

def primaryFiniteRow0Parent0Split100Sub0_max4Rat
    (a b c d : Rat) : Rat :=
  max (max a b) (max c d)

private theorem primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_1
    (a b c d : Rat) :
    (primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d : Real) <=
      (a : Real) := by
  have h : primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d <= a := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_min4Rat]
    exact le_trans (min_le_left _ _) (min_le_left _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_2
    (a b c d : Rat) :
    (primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d : Real) <=
      (b : Real) := by
  have h : primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d <= b := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_min4Rat]
    exact le_trans (min_le_left _ _) (min_le_right _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_3
    (a b c d : Rat) :
    (primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d : Real) <=
      (c : Real) := by
  have h : primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d <= c := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_min4Rat]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_4
    (a b c d : Rat) :
    (primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d : Real) <=
      (d : Real) := by
  have h : primaryFiniteRow0Parent0Split100Sub0_min4Rat a b c d <= d := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_min4Rat]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_1
    (a b c d : Rat) :
    (a : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d : Real) := by
  have h : a <= primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_max4Rat]
    exact le_trans (le_max_left _ _) (le_max_left _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_2
    (a b c d : Rat) :
    (b : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d : Real) := by
  have h : b <= primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_max4Rat]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_3
    (a b c d : Rat) :
    (c : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d : Real) := by
  have h : c <= primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_max4Rat]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  exact_mod_cast h

private theorem primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_4
    (a b c d : Rat) :
    (d : Real) <=
      (primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d : Real) := by
  have h : d <= primaryFiniteRow0Parent0Split100Sub0_max4Rat a b c d := by
    dsimp [primaryFiniteRow0Parent0Split100Sub0_max4Rat]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  exact_mod_cast h

/-- Rational lower endpoint for the raw `D17(ComponentProductActual)` row at
the point-slope local center. -/
def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat
    (i : Fin 2) : Rat :=
  ∑ k ∈ Finset.range (18 + 1),
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
      i).termLower k

/-- Rational upper endpoint for the raw `D17(ComponentProductActual)` row at
the point-slope local center. -/
def primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat
    (i : Fin 2) : Rat :=
  ∑ k ∈ Finset.range (18 + 1),
    (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
      i).termUpper k

theorem
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat i :
        Real) <=
        iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) ∧
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) <=
        (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat i :
          Real) := by
  have hValid :
      (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
        i).Valid :=
    primaryFiniteRow0Parent0Split100Sub0_rawD17_signedFactor_twoSegment_sharp_valid
      i
  have hTermRows :=
    primaryFiniteRow0Parent0Split100Sub0_sum_interval_rat
      (Finset.range (18 + 1))
      (x := fun k =>
        primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real))
      (lower := fun k =>
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
          i).termLower k)
      (upper := fun k =>
        (primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp
          i).termUpper k)
      (fun k hk =>
        hValid.to_termRows
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i : Real)
          (by
            simpa [
              primaryFiniteRow0Parent0Split100Sub0RawD17SignedFactorTwoSegmentSharp]
              using
                primaryFiniteRow0Parent0Split100Sub0_rawD17LocalCenter_mem_segment
                  i)
          k hk)
  have hEq :
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) =
        ∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) := by
    rw [
      primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_eq_rawProduct18,
      primaryFiniteRow0Parent0Split100Sub0_rawProductActual_order18_eq_signedLeibniz]
  constructor
  · calc
      (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat i :
          Real) <=
          (∑ k ∈ Finset.range (18 + 1),
            primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
              (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
                Real)) := by
            simpa [
              primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat]
              using hTermRows.1
      _ =
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) := hEq.symm
  · calc
      iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real) =
        (∑ k ∈ Finset.range (18 + 1),
          primaryFiniteRow0Parent0Split100Sub0RawProduct18SignedTerm k
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real)) := hEq
      _ <=
          (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat i :
            Real) := by
            simpa [
              primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat]
              using hTermRows.2

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleLower *
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat i

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleLower *
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat i

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleUpper *
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat i

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0TightScaleUpper *
    primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat i

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0_min4Rat
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU i)

def primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0_max4Rat
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL i)
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU i)

theorem
    primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat i :
        Real) <=
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) ∧
      primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff *
          iteratedDeriv 17
            primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) <=
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat i :
          Real) := by
  have hScale :=
    primaryFiniteRow0Parent0Split100Sub0_activeScale_mem_tightInterval
  have hScale' :
      (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real) <=
          primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff ∧
        primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff <=
          (primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Real) := by
    simpa [primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff] using hScale
  have hRaw :=
    primaryFiniteRow0Parent0Split100Sub0_componentProductActual_order17_point_interval_rat_generated
      i
  have hMul :=
    mul_interval_bounds_of_four_corners
      (a := (primaryFiniteRow0Parent0Split100Sub0TightScaleLower : Real))
      (b := (primaryFiniteRow0Parent0Split100Sub0TightScaleUpper : Real))
      (c :=
        (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointLowerRat i :
          Real))
      (d :=
        (primaryFiniteRow0Parent0Split100Sub0RawProduct18PointUpperRat i :
          Real))
      (x := primaryFiniteRow0Parent0Split100Sub0ActiveScaleCoeff)
      (y :=
        iteratedDeriv 17
          primaryFiniteRow0Parent0Split100Sub0ComponentProductActual
          (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
            Real))
      (lower :=
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat i :
          Real))
      (upper :=
        (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat i :
          Real))
      hScale'.1 hScale'.2 hRaw.1 hRaw.2
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_1
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_2
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_3
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_min4Rat_le_4
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_1
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_2
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_3
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
      (by
        simpa [
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat,
          primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU,
          Rat.cast_mul] using
          primaryFiniteRow0Parent0Split100Sub0_le_max4Rat_4
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerLU
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUL
              i)
            (primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointCornerUU
              i))
  simpa [mul_comm, mul_left_comm, mul_assoc] using hMul

def primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat
    (i : Fin 2) : Rat :=
  ∑ j : Fin 29,
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivCoeff j *
      (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i -
        ((1 : Rat) / 20)) ^ j.1

theorem
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat
    (i : Fin 2) :
    deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
        (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointSlopeLocalCenter
          i : Real) =
      (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat i :
        Real) := by
  rw [
    primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter,
    primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_eq_poly]
  unfold rawOmegaATaylorPolynomial
  unfold primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat
  rw [Rat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [Rat.cast_mul, Rat.cast_pow]
  congr 1
  rw [Rat.cast_sub]

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointLowerRat
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointLowerRat i -
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat i

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointUpperRat
    (i : Fin 2) : Rat :=
  primaryFiniteRow0Parent0Split100Sub0ActiveScaledRawPointUpperRat i -
    primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat i

def primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointRowRat
    (i : Fin 2) :
    Step33Sub0CollapsedDegree0PointRowCert where
  i := i
  lower := primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointLowerRat i
  upper := primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointUpperRat i

theorem
    primaryFiniteRow0Parent0Split100Sub0_collapsedDegree0_pointRow_generated
    (i : Fin 2) :
    (primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointRowRat
      i).Valid where
  pointInterval := by
    have hRaw :=
      primaryFiniteRow0Parent0Split100Sub0_activeScaled_componentProductActual_order17_point_interval_rat_generated
        i
    have hNom :=
      primaryFiniteRow0Parent0Split100Sub0_nominalOrder16Poly_deriv_localCenter_eq_rat
        i
    have hNomRaw :
        deriv primaryFiniteRow0Parent0Split100Sub0NominalOrder16Poly
            (primaryFiniteRow0Parent0Split100Sub0RawD17LocalCenter i :
              Real) =
          (primaryFiniteRow0Parent0Split100Sub0NominalOrder16PolyDerivPointRat
            i : Real) := by
      simpa [
        primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter]
        using hNom
    dsimp [primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointRowRat]
    rw [
      primaryFiniteRow0Parent0Split100Sub0_pointSlopeLocalCenter_eq_rawD17LocalCenter]
    constructor
    · dsimp [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointLowerRat,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr]
      rw [hNomRaw]
      rw [Rat.cast_sub]
      linarith [hRaw.1]
    · dsimp [
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0PointUpperRat,
        primaryFiniteRow0Parent0Split100Sub0CollapsedDegree0SignedSourceExpr]
      rw [hNomRaw]
      rw [Rat.cast_sub]
      linarith [hRaw.2]

end Step33
end PSDpd
end Q3
