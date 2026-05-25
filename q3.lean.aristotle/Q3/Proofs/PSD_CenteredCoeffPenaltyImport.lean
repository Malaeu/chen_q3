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
def primaryK11TauD : Real := ((25059361681363677 : Real) / 50000000000000)
def primaryK11TauR : Real := ((7924465962305587 : Real) / 500000000000)
def primaryK11DFloor : Real := ((1528574356267451 : Real) / 12500000000000000000)
def primaryK11RFloor : Real := ((13569220780301769 : Real) / 100000000000000000)

theorem primaryK11DFloor_pos : 0 < primaryK11DFloor := by
  norm_num [primaryK11DFloor]

theorem primaryK11RFloor_pos : 0 < primaryK11RFloor := by
  norm_num [primaryK11RFloor]

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
def controlK9TauD : Real := ((100 : Real))
def controlK9TauR : Real := ((100000 : Real))
def controlK9DFloor : Real := ((6318461466108783 : Real) / 500000000000000000000)
def controlK9RFloor : Real := ((19590641960201293 : Real) / 10000000000000000000)

theorem controlK9DFloor_pos : 0 < controlK9DFloor := by
  norm_num [controlK9DFloor]

theorem controlK9RFloor_pos : 0 < controlK9RFloor := by
  norm_num [controlK9RFloor]

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
