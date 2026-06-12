import Q3.Proofs.PSD_CenteredCoeffQRowImport
import Q3.Proofs.PSD_PenaltyCertificate

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffGramRadiusImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffQRowImport

/-!
Step32H boundary-Gram radius import.

The Step32G Q-row hboxes imply boundary-Gram hboxes with a canonical radius:
the exact finite product-error sum over the imported Q midpoint/radius payload.
This file exposes that radius so downstream certified-block wrappers no longer
carry a separate generated `hGRad` premise.
-/

def primaryK11BoundaryGramRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j =>
    Finset.univ.sum
      (fun r : BoundaryIndex2 =>
        primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
          |primaryK11Q r i| * primaryK11QRadius r j)

theorem primaryK11BoundaryGramRadius_dominance :
    ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        primaryK11BoundaryGramRadius i j := by
  intro i j
  unfold primaryK11BoundaryGramRadius
  exact le_rfl

/-- Imported primary `k=11` Q-row radii enclose the induced boundary Gram. -/
theorem primaryK11BoundaryGramRadius_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix primaryK11Q)
      primaryK11BoundaryGramRadius := by
  intro i j
  have h :=
    (Q3.Proofs.boundaryGramMatrix_entrywiseAbsLe_of_matrix
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius primaryK11QRadius_hbox) i j
  simpa [primaryK11BoundaryGramRadius] using h

def controlK9BoundaryGramRadius : Matrix CoeffIndex23 CoeffIndex23 Real :=
  fun i j =>
    Finset.univ.sum
      (fun r : BoundaryIndex2 =>
        controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
          |controlK9Q r i| * controlK9QRadius r j)

theorem controlK9BoundaryGramRadius_dominance :
    ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        controlK9BoundaryGramRadius i j := by
  intro i j
  unfold controlK9BoundaryGramRadius
  exact le_rfl

/-- Imported control `k=9` Q-row radii enclose the induced boundary Gram. -/
theorem controlK9BoundaryGramRadius_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix controlK9Q)
      controlK9BoundaryGramRadius := by
  intro i j
  have h :=
    (Q3.Proofs.boundaryGramMatrix_entrywiseAbsLe_of_matrix
      controlK9AnalyticQ controlK9Q controlK9QRadius controlK9QRadius_hbox) i j
  simpa [controlK9BoundaryGramRadius] using h

end CenteredCoeffGramRadiusImport
end PSDpd
end Q3
