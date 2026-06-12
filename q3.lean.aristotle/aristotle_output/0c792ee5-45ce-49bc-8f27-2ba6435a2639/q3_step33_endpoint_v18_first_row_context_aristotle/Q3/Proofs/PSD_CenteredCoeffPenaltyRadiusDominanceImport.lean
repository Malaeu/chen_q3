import Q3.Proofs.PSD_CenteredCoeffGramRadiusImport
import Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPenaltyRadiusDominanceImport

open CenteredCoeffPayloadImport
open CenteredCoeffPenaltyImport
open CenteredCoeffRadiusFloorImport
open CenteredCoeffGramRadiusImport

/-!
Step32I penalty-radius dominance import.

The Step32F radius-floor generator defines the imported D/R penalty radii as
base A/P/P0 radius contributions plus the Q-boundary Gram radius contribution.
This file exposes those base D/R radii and proves the finite rational dominance
facts needed by the certified-block wrappers.
-/

def primaryK11BoundaryGramRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    Finset.univ.sum
      (fun r : BoundaryIndex2 =>
        primaryK11QRadiusRat r i * (|primaryK11QRat r j| + primaryK11QRadiusRat r j) +
          |primaryK11QRat r i| * primaryK11QRadiusRat r j)

theorem primaryK11BoundaryGramRadius_eq_rat :
    ∀ i j,
      primaryK11BoundaryGramRadius i j =
        (primaryK11BoundaryGramRadiusRat i j : Real) := by
  intro i j
  simp [primaryK11BoundaryGramRadius, primaryK11BoundaryGramRadiusRat,
    primaryK11Q, primaryK11QRadius, Rat.cast_abs]

def primaryK11DBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    (1 - primaryK11ThetaRat) * primaryK11ARadiusRat i j +
      primaryK11PRadiusRat i j +
        primaryK11ThetaRat * |primaryK11KappaRat| * primaryK11P0RadiusRat i j

def primaryK11DBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11DBaseRadiusRat i j : Real)

def primaryK11RBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    primaryK11ARadiusRat i j +
      |primaryK11KappaRat| * primaryK11P0RadiusRat i j

def primaryK11RBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (primaryK11RBaseRadiusRat i j : Real)

theorem primaryK11DBaseRadius_penaltyRadius_dominance_rat :
    ∀ i j,
      primaryK11DBaseRadiusRat i j +
          |primaryK11TauDRat| * primaryK11BoundaryGramRadiusRat i j ≤
        primaryK11DPenaltyRadiusRat i j := by
  native_decide

theorem primaryK11RBaseRadius_penaltyRadius_dominance_rat :
    ∀ i j,
      primaryK11RBaseRadiusRat i j +
          |primaryK11TauRRat| * primaryK11BoundaryGramRadiusRat i j ≤
        primaryK11RPenaltyRadiusRat i j := by
  native_decide

theorem primaryK11DBaseRadius_penaltyRadius_dominance :
    ∀ i j,
      primaryK11DBaseRadius i j +
          |primaryK11TauD| * primaryK11BoundaryGramRadius i j ≤
        primaryK11DPenaltyRadius i j := by
  intro i j
  rw [primaryK11BoundaryGramRadius_eq_rat i j]
  change
    (primaryK11DBaseRadiusRat i j : Real) +
        |primaryK11TauD| * (primaryK11BoundaryGramRadiusRat i j : Real) ≤
      (primaryK11DPenaltyRadiusRat i j : Real)
  have htau :
      |primaryK11TauD| = ((|primaryK11TauDRat| : Rat) : Real) := by
    norm_num [primaryK11TauD, primaryK11TauDRat]
  rw [htau]
  exact_mod_cast primaryK11DBaseRadius_penaltyRadius_dominance_rat i j

theorem primaryK11RBaseRadius_penaltyRadius_dominance :
    ∀ i j,
      primaryK11RBaseRadius i j +
          |primaryK11TauR| * primaryK11BoundaryGramRadius i j ≤
        primaryK11RPenaltyRadius i j := by
  intro i j
  rw [primaryK11BoundaryGramRadius_eq_rat i j]
  change
    (primaryK11RBaseRadiusRat i j : Real) +
        |primaryK11TauR| * (primaryK11BoundaryGramRadiusRat i j : Real) ≤
      (primaryK11RPenaltyRadiusRat i j : Real)
  have htau :
      |primaryK11TauR| = ((|primaryK11TauRRat| : Rat) : Real) := by
    norm_num [primaryK11TauR, primaryK11TauRRat]
  rw [htau]
  exact_mod_cast primaryK11RBaseRadius_penaltyRadius_dominance_rat i j

def controlK9BoundaryGramRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    Finset.univ.sum
      (fun r : BoundaryIndex2 =>
        controlK9QRadiusRat r i * (|controlK9QRat r j| + controlK9QRadiusRat r j) +
          |controlK9QRat r i| * controlK9QRadiusRat r j)

theorem controlK9BoundaryGramRadius_eq_rat :
    ∀ i j,
      controlK9BoundaryGramRadius i j =
        (controlK9BoundaryGramRadiusRat i j : Real) := by
  intro i j
  simp [controlK9BoundaryGramRadius, controlK9BoundaryGramRadiusRat,
    controlK9Q, controlK9QRadius, Rat.cast_abs]

def controlK9DBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    (1 - controlK9ThetaRat) * controlK9ARadiusRat i j +
      controlK9PRadiusRat i j +
        controlK9ThetaRat * |controlK9KappaRat| * controlK9P0RadiusRat i j

def controlK9DBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9DBaseRadiusRat i j : Real)

def controlK9RBaseRadiusRat : Matrix CoeffIndex23 CoeffIndex23 Rat :=
  fun i j =>
    controlK9ARadiusRat i j +
      |controlK9KappaRat| * controlK9P0RadiusRat i j

def controlK9RBaseRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j => (controlK9RBaseRadiusRat i j : Real)

theorem controlK9DBaseRadius_penaltyRadius_dominance_rat :
    ∀ i j,
      controlK9DBaseRadiusRat i j +
          |controlK9TauDRat| * controlK9BoundaryGramRadiusRat i j ≤
        controlK9DPenaltyRadiusRat i j := by
  native_decide

theorem controlK9RBaseRadius_penaltyRadius_dominance_rat :
    ∀ i j,
      controlK9RBaseRadiusRat i j +
          |controlK9TauRRat| * controlK9BoundaryGramRadiusRat i j ≤
        controlK9RPenaltyRadiusRat i j := by
  native_decide

theorem controlK9DBaseRadius_penaltyRadius_dominance :
    ∀ i j,
      controlK9DBaseRadius i j +
          |controlK9TauD| * controlK9BoundaryGramRadius i j ≤
        controlK9DPenaltyRadius i j := by
  intro i j
  rw [controlK9BoundaryGramRadius_eq_rat i j]
  change
    (controlK9DBaseRadiusRat i j : Real) +
        |controlK9TauD| * (controlK9BoundaryGramRadiusRat i j : Real) ≤
      (controlK9DPenaltyRadiusRat i j : Real)
  have htau :
      |controlK9TauD| = ((|controlK9TauDRat| : Rat) : Real) := by
    norm_num [controlK9TauD, controlK9TauDRat]
  rw [htau]
  exact_mod_cast controlK9DBaseRadius_penaltyRadius_dominance_rat i j

theorem controlK9RBaseRadius_penaltyRadius_dominance :
    ∀ i j,
      controlK9RBaseRadius i j +
          |controlK9TauR| * controlK9BoundaryGramRadius i j ≤
        controlK9RPenaltyRadius i j := by
  intro i j
  rw [controlK9BoundaryGramRadius_eq_rat i j]
  change
    (controlK9RBaseRadiusRat i j : Real) +
        |controlK9TauR| * (controlK9BoundaryGramRadiusRat i j : Real) ≤
      (controlK9RPenaltyRadiusRat i j : Real)
  have htau :
      |controlK9TauR| = ((|controlK9TauRRat| : Rat) : Real) := by
    norm_num [controlK9TauR, controlK9TauRRat]
  rw [htau]
  exact_mod_cast controlK9RBaseRadius_penaltyRadius_dominance_rat i j

end CenteredCoeffPenaltyRadiusDominanceImport
end PSDpd
end Q3
