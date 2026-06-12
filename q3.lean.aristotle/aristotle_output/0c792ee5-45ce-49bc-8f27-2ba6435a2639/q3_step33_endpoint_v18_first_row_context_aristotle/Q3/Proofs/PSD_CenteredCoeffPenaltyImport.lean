import Q3.Proofs.PSD_CenteredCoeffPayloadImport
import Q3.Proofs.PSD_PenaltyCertificate

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPenaltyImport

open CenteredCoeffPayloadImport

/-!
Checked Step 18 penalty lower-bound parameters for the active Step 32F
coefficient blocks.

This generated file imports only exact parameter data and receiver adapters.
It does not prove the lower bounds.  The next proof-generating checker must
close the named `DLowerBound` and `RLowerBound` propositions below.
-/

/-- Step 18 penalty parameters for `psdpd_L3_k11_ell030_delta025_theta1e4`. -/
def primaryK11TauDRat : Rat := ((25059361681363677 : Rat) / 50000000000000)
def primaryK11TauRRat : Rat := ((7924465962305587 : Rat) / 500000000000)
def primaryK11DFloorRat : Rat := ((12228594783222341 : Rat) / 100000000000000000000)
def primaryK11RFloorRat : Rat := ((6784610389093003 : Rat) / 50000000000000000)

def primaryK11TauD : Real := (primaryK11TauDRat : Real)
def primaryK11TauR : Real := (primaryK11TauRRat : Real)
def primaryK11DFloor : Real := (primaryK11DFloorRat : Real)
def primaryK11RFloor : Real := (primaryK11RFloorRat : Real)

theorem primaryK11DFloorRat_pos : 0 < primaryK11DFloorRat := by
  native_decide

theorem primaryK11RFloorRat_pos : 0 < primaryK11RFloorRat := by
  native_decide

theorem primaryK11DFloor_pos : 0 < primaryK11DFloor := by
  change 0 < (primaryK11DFloorRat : Real)
  exact_mod_cast primaryK11DFloorRat_pos

theorem primaryK11RFloor_pos : 0 < primaryK11RFloor := by
  change 0 < (primaryK11RFloorRat : Real)
  exact_mod_cast primaryK11RFloorRat_pos

/-- Remaining checked lower-bound target for `psdpd_L3_k11_ell030_delta025_theta1e4` / D. -/
def primaryK11DLowerBound : Prop :=
  ∀ v : CoeffIndex23 -> Real,
    primaryK11DFloor * Q3.Proofs.euclideanEnergy v <=
      Q3.Proofs.penaltyForm primaryK11D primaryK11Q primaryK11TauD v

/-- Remaining checked lower-bound target for `psdpd_L3_k11_ell030_delta025_theta1e4` / R. -/
def primaryK11RLowerBound : Prop :=
  ∀ v : CoeffIndex23 -> Real,
    primaryK11RFloor * Q3.Proofs.euclideanEnergy v <=
      Q3.Proofs.penaltyForm primaryK11R primaryK11Q primaryK11TauR v

/-- Convert an exact weighted-square identity into `primaryK11DLowerBound`.

The proof-generating SOS/LDL checker only needs to supply nonnegative
weights and the exact identity; the reusable algebraic receiver proves
the Euclidean lower bound. -/
def primaryK11DLowerBound_of_weightedSquareSum
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.penaltyForm primaryK11D primaryK11Q primaryK11TauD v =
        primaryK11DFloor * Q3.Proofs.euclideanEnergy v +
          Q3.Proofs.weightedSquareSum w L v) :
    primaryK11DLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity
    primaryK11D primaryK11Q primaryK11TauD primaryK11DFloor w L hw hidentity

/-- Convert an exact weighted-Gram matrix identity into `primaryK11DLowerBound`.

This is the preferred landing surface for generated 23-by-23 LDL/SOS
certificates, because it checks matrix entries instead of expanding one
large coefficient polynomial. -/
def primaryK11DLowerBound_of_weightedSquareMatrix
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ i j : CoeffIndex23,
      primaryK11D i j + primaryK11TauD * (∑ r : BoundaryIndex2, primaryK11Q r i * primaryK11Q r j) =
        primaryK11DFloor * (if i = j then (1 : Real) else 0) +
          Q3.Proofs.weightedSquareMatrix w L i j) :
    primaryK11DLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity
    primaryK11D primaryK11Q primaryK11TauD primaryK11DFloor w L hw hidentity

/-- Convert an exact weighted-square identity into `primaryK11RLowerBound`.

The proof-generating SOS/LDL checker only needs to supply nonnegative
weights and the exact identity; the reusable algebraic receiver proves
the Euclidean lower bound. -/
def primaryK11RLowerBound_of_weightedSquareSum
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.penaltyForm primaryK11R primaryK11Q primaryK11TauR v =
        primaryK11RFloor * Q3.Proofs.euclideanEnergy v +
          Q3.Proofs.weightedSquareSum w L v) :
    primaryK11RLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity
    primaryK11R primaryK11Q primaryK11TauR primaryK11RFloor w L hw hidentity

/-- Convert an exact weighted-Gram matrix identity into `primaryK11RLowerBound`.

This is the preferred landing surface for generated 23-by-23 LDL/SOS
certificates, because it checks matrix entries instead of expanding one
large coefficient polynomial. -/
def primaryK11RLowerBound_of_weightedSquareMatrix
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ i j : CoeffIndex23,
      primaryK11R i j + primaryK11TauR * (∑ r : BoundaryIndex2, primaryK11Q r i * primaryK11Q r j) =
        primaryK11RFloor * (if i = j then (1 : Real) else 0) +
          Q3.Proofs.weightedSquareMatrix w L i j) :
    primaryK11RLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity
    primaryK11R primaryK11Q primaryK11TauR primaryK11RFloor w L hw hidentity

/-- Package the two checked lower bounds for `psdpd_L3_k11_ell030_delta025_theta1e4`. -/
def primaryK11PenaltyLowerBoundCert_of_bounds
    (hD : primaryK11DLowerBound)
    (hR : primaryK11RLowerBound) :
    Q3.Proofs.FinitePenaltyLowerBoundCert primaryK11D primaryK11R primaryK11Q where
  tauD := primaryK11TauD
  tauR := primaryK11TauR
  dFloor := primaryK11DFloor
  rFloor := primaryK11RFloor
  dFloor_pos := primaryK11DFloor_pos
  rFloor_pos := primaryK11RFloor_pos
  D_penalty_lower := hD
  R_penalty_lower := hR

/-- Convert the checked lower bounds for `psdpd_L3_k11_ell030_delta025_theta1e4` into the
existing finite penalty certificate receiver. -/
def primaryK11FinitePenaltyCert_of_bounds
    (hD : primaryK11DLowerBound)
    (hR : primaryK11RLowerBound) :
    Q3.Proofs.FinitePenaltyCert primaryK11D primaryK11R primaryK11Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert
    (primaryK11PenaltyLowerBoundCert_of_bounds hD hR)

/-- Step 18 penalty parameters for `psdpd_L3_k9_ell030_delta025_theta1e5`. -/
def controlK9TauDRat : Rat := ((15773933612004857 : Rat) / 250000000000000)
def controlK9TauRRat : Rat := ((100000 : Rat))
def controlK9DFloorRat : Rat := ((157961535273327 : Rat) / 12500000000000000000)
def controlK9RFloorRat : Rat := ((3918128125049953 : Rat) / 2000000000000000000)

def controlK9TauD : Real := (controlK9TauDRat : Real)
def controlK9TauR : Real := (controlK9TauRRat : Real)
def controlK9DFloor : Real := (controlK9DFloorRat : Real)
def controlK9RFloor : Real := (controlK9RFloorRat : Real)

theorem controlK9DFloorRat_pos : 0 < controlK9DFloorRat := by
  native_decide

theorem controlK9RFloorRat_pos : 0 < controlK9RFloorRat := by
  native_decide

theorem controlK9DFloor_pos : 0 < controlK9DFloor := by
  change 0 < (controlK9DFloorRat : Real)
  exact_mod_cast controlK9DFloorRat_pos

theorem controlK9RFloor_pos : 0 < controlK9RFloor := by
  change 0 < (controlK9RFloorRat : Real)
  exact_mod_cast controlK9RFloorRat_pos

/-- Remaining checked lower-bound target for `psdpd_L3_k9_ell030_delta025_theta1e5` / D. -/
def controlK9DLowerBound : Prop :=
  ∀ v : CoeffIndex23 -> Real,
    controlK9DFloor * Q3.Proofs.euclideanEnergy v <=
      Q3.Proofs.penaltyForm controlK9D controlK9Q controlK9TauD v

/-- Remaining checked lower-bound target for `psdpd_L3_k9_ell030_delta025_theta1e5` / R. -/
def controlK9RLowerBound : Prop :=
  ∀ v : CoeffIndex23 -> Real,
    controlK9RFloor * Q3.Proofs.euclideanEnergy v <=
      Q3.Proofs.penaltyForm controlK9R controlK9Q controlK9TauR v

/-- Convert an exact weighted-square identity into `controlK9DLowerBound`.

The proof-generating SOS/LDL checker only needs to supply nonnegative
weights and the exact identity; the reusable algebraic receiver proves
the Euclidean lower bound. -/
def controlK9DLowerBound_of_weightedSquareSum
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.penaltyForm controlK9D controlK9Q controlK9TauD v =
        controlK9DFloor * Q3.Proofs.euclideanEnergy v +
          Q3.Proofs.weightedSquareSum w L v) :
    controlK9DLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity
    controlK9D controlK9Q controlK9TauD controlK9DFloor w L hw hidentity

/-- Convert an exact weighted-Gram matrix identity into `controlK9DLowerBound`.

This is the preferred landing surface for generated 23-by-23 LDL/SOS
certificates, because it checks matrix entries instead of expanding one
large coefficient polynomial. -/
def controlK9DLowerBound_of_weightedSquareMatrix
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ i j : CoeffIndex23,
      controlK9D i j + controlK9TauD * (∑ r : BoundaryIndex2, controlK9Q r i * controlK9Q r j) =
        controlK9DFloor * (if i = j then (1 : Real) else 0) +
          Q3.Proofs.weightedSquareMatrix w L i j) :
    controlK9DLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity
    controlK9D controlK9Q controlK9TauD controlK9DFloor w L hw hidentity

/-- Convert an exact weighted-square identity into `controlK9RLowerBound`.

The proof-generating SOS/LDL checker only needs to supply nonnegative
weights and the exact identity; the reusable algebraic receiver proves
the Euclidean lower bound. -/
def controlK9RLowerBound_of_weightedSquareSum
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.penaltyForm controlK9R controlK9Q controlK9TauR v =
        controlK9RFloor * Q3.Proofs.euclideanEnergy v +
          Q3.Proofs.weightedSquareSum w L v) :
    controlK9RLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareSum_identity
    controlK9R controlK9Q controlK9TauR controlK9RFloor w L hw hidentity

/-- Convert an exact weighted-Gram matrix identity into `controlK9RLowerBound`.

This is the preferred landing surface for generated 23-by-23 LDL/SOS
certificates, because it checks matrix entries instead of expanding one
large coefficient polynomial. -/
def controlK9RLowerBound_of_weightedSquareMatrix
    {σ : Type} [Fintype σ]
    (w : σ -> Real) (L : σ -> CoeffIndex23 -> Real)
    (hw : ∀ s, 0 <= w s)
    (hidentity : ∀ i j : CoeffIndex23,
      controlK9R i j + controlK9TauR * (∑ r : BoundaryIndex2, controlK9Q r i * controlK9Q r j) =
        controlK9RFloor * (if i = j then (1 : Real) else 0) +
          Q3.Proofs.weightedSquareMatrix w L i j) :
    controlK9RLowerBound :=
  Q3.Proofs.penalty_lower_bound_of_weightedSquareMatrix_identity
    controlK9R controlK9Q controlK9TauR controlK9RFloor w L hw hidentity

/-- Package the two checked lower bounds for `psdpd_L3_k9_ell030_delta025_theta1e5`. -/
def controlK9PenaltyLowerBoundCert_of_bounds
    (hD : controlK9DLowerBound)
    (hR : controlK9RLowerBound) :
    Q3.Proofs.FinitePenaltyLowerBoundCert controlK9D controlK9R controlK9Q where
  tauD := controlK9TauD
  tauR := controlK9TauR
  dFloor := controlK9DFloor
  rFloor := controlK9RFloor
  dFloor_pos := controlK9DFloor_pos
  rFloor_pos := controlK9RFloor_pos
  D_penalty_lower := hD
  R_penalty_lower := hR

/-- Convert the checked lower bounds for `psdpd_L3_k9_ell030_delta025_theta1e5` into the
existing finite penalty certificate receiver. -/
def controlK9FinitePenaltyCert_of_bounds
    (hD : controlK9DLowerBound)
    (hR : controlK9RLowerBound) :
    Q3.Proofs.FinitePenaltyCert controlK9D controlK9R controlK9Q :=
  Q3.Proofs.FinitePenaltyLowerBoundCert.toFinitePenaltyCert
    (controlK9PenaltyLowerBoundCert_of_bounds hD hR)

end CenteredCoeffPenaltyImport
end PSDpd
end Q3
