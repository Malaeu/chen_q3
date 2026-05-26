import Q3.Proofs.PSD_CenteredCoeffDictionaryImport
import Q3.Proofs.PSD_CenteredCoeffQRowImport
import Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffCertifiedBlockImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffQRowImport
open CenteredCoeffRadiusFloorImport

/-!
Certified coefficient-block import adapters for the active Step 32F rows.

The radius-floor import now exposes finite-penalty certificates from future
analytic penalty-box hypotheses.  This file connects those certificate wrappers
to the existing `CertifiedCenteredBSplineCoeffBlock` receiver for the concrete
primary/control coefficient dictionaries.

It deliberately does not assert the analytic hbox hypotheses.  Those are the
remaining enclosure obligations.
-/

/-- Analytic primary D matrix induced by a chosen analytic R matrix and the
imported primary penalty parameter. -/
def primaryK11AnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub primaryK11AnalyticC R primaryK11Theta

/-- The primary analytic split follows structurally from the definition of
`primaryK11AnalyticDFromR`. -/
theorem primaryK11AnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm primaryK11AnalyticC v =
        Q3.Proofs.quadForm (primaryK11AnalyticDFromR R) v +
          primaryK11Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold primaryK11AnalyticDFromR
  exact quadForm_scaled_sub_split primaryK11AnalyticC R primaryK11Theta v

/-- Primary `k=11` D penalty hbox from a base D hbox and a boundary-Gram
hbox.  The final radius relaxation is kept explicit because the imported
penalty radius is generated data. -/
theorem primaryK11DPenaltyBox_of_matrix_and_boundaryGram
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDFromR R) primaryK11D MR)
    (hG : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix primaryK11Q)
      GR)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j ≤
        primaryK11DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (primaryK11AnalyticDFromR R) primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauD)
      primaryK11DPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix
      (primaryK11AnalyticDFromR R) primaryK11AnalyticQ
      CenteredCoeffPenaltyImport.primaryK11TauD)
    (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q
      CenteredCoeffPenaltyImport.primaryK11TauD)
    (fun i j =>
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j)
    primaryK11DPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      (primaryK11AnalyticDFromR R) primaryK11D MR
      primaryK11AnalyticQ primaryK11Q GR
      CenteredCoeffPenaltyImport.primaryK11TauD hM hG)
    hRad

/-- Primary `k=11` R penalty hbox from a base R hbox and a boundary-Gram
hbox. -/
theorem primaryK11RPenaltyBox_of_matrix_and_boundaryGram
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R primaryK11R MR)
    (hG : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix primaryK11Q)
      GR)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j ≤
        primaryK11RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauR)
      (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauR)
      primaryK11RPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ
      CenteredCoeffPenaltyImport.primaryK11TauR)
    (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q
      CenteredCoeffPenaltyImport.primaryK11TauR)
    (fun i j =>
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j)
    primaryK11RPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      R primaryK11R MR primaryK11AnalyticQ primaryK11Q GR
      CenteredCoeffPenaltyImport.primaryK11TauR hM hG)
    hRad

/-
Q3 obstruction wall:
- wall: Matrix-identification / Step32F boundary-row hbox handoff
- role: tactical adapter from active boundary-row boxes to boundary Gram boxes
- input: future boundary-row hboxes and generated Gram-radius dominance lemmas
- output: primary boundary-Gram hbox consumed by active D/R penalty adapters
- reviewer question answered: does the boundary-row interval payload feed the
  actual `Q^T Q` Gram term rather than stopping at rowwise midpoint/radius data?
-/
/-- Primary `k=11` boundary-Gram hbox from a boundary-row hbox and a generated
Gram-radius dominance lemma. -/
theorem primaryK11BoundaryGramBox_of_boundaryRows
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q QR)
    (hRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|primaryK11Q r j| + QR r j) +
              |primaryK11Q r i| * QR r j) ≤
        GR i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix primaryK11Q)
      GR := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
    (Q3.Proofs.boundaryGramMatrix primaryK11Q)
    (fun i j =>
      Finset.univ.sum
        (fun r : BoundaryIndex2 =>
          QR r i * (|primaryK11Q r j| + QR r j) +
            |primaryK11Q r i| * QR r j))
    GR
    (Q3.Proofs.boundaryGramMatrix_entrywiseAbsLe_of_matrix
      primaryK11AnalyticQ primaryK11Q QR hQ)
    hRad

/-- Primary `k=11` D penalty hbox directly from a base D hbox, a boundary-row
hbox, and the two generated radius-dominance lemmas. -/
theorem primaryK11DPenaltyBox_of_matrix_and_boundaryRows
    (R MR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDFromR R) primaryK11D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q QR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|primaryK11Q r j| + QR r j) +
              |primaryK11Q r i| * QR r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j ≤
        primaryK11DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (primaryK11AnalyticDFromR R) primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauD)
      primaryK11DPenaltyRadius := by
  exact primaryK11DPenaltyBox_of_matrix_and_boundaryGram
    R MR GR hM
    (primaryK11BoundaryGramBox_of_boundaryRows QR GR hQ hGRad)
    hRad

/-- Primary `k=11` R penalty hbox directly from a base R hbox, a boundary-row
hbox, and the two generated radius-dominance lemmas. -/
theorem primaryK11RPenaltyBox_of_matrix_and_boundaryRows
    (R MR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R primaryK11R MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q QR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|primaryK11Q r j| + QR r j) +
              |primaryK11Q r i| * QR r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j ≤
        primaryK11RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauR)
      (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauR)
      primaryK11RPenaltyRadius := by
  exact primaryK11RPenaltyBox_of_matrix_and_boundaryGram
    R MR GR hM
    (primaryK11BoundaryGramBox_of_boundaryRows QR GR hQ hGRad)
    hRad

/-- Primary `k=11` boundary-Gram hbox specialized to the imported
`primaryK11QRadius` row-radius payload. -/
theorem primaryK11BoundaryGramBox_of_importedQRadius
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius)
    (hRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix primaryK11AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix primaryK11Q)
      GR := by
  exact primaryK11BoundaryGramBox_of_boundaryRows
    primaryK11QRadius GR hQ hRad

/-- Primary `k=11` D penalty hbox specialized to the imported
`primaryK11QRadius` row-radius payload. -/
theorem primaryK11DPenaltyBox_of_matrix_and_importedQRadius
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDFromR R) primaryK11D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j ≤
        primaryK11DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (primaryK11AnalyticDFromR R) primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauD)
      primaryK11DPenaltyRadius := by
  exact primaryK11DPenaltyBox_of_matrix_and_boundaryRows
    R MR primaryK11QRadius GR hM hQ hGRad hRad

/-- Primary `k=11` R penalty hbox specialized to the imported
`primaryK11QRadius` row-radius payload. -/
theorem primaryK11RPenaltyBox_of_matrix_and_importedQRadius
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R primaryK11R MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j ≤
        primaryK11RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauR)
      (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauR)
      primaryK11RPenaltyRadius := by
  exact primaryK11RPenaltyBox_of_matrix_and_boundaryRows
    R MR primaryK11QRadius GR hM hQ hGRad hRad

/- 
Q3 obstruction wall:
- wall: Matrix-identification / Step32F coefficient certified-block handoff
- role: tactical adapter from penalty-box certificates to certified coefficient blocks
- input: concrete coefficient dictionary, analytic split, future D/R penalty hboxes
- output: primary CertifiedCenteredBSplineCoeffBlock once analytic hboxes are supplied
- reviewer question answered: does the interval-backed certificate receiver feed the
  existing analytic coefficient block, rather than stopping at a penalty wrapper?
-/
/-- Primary active coefficient block from the future analytic penalty-box
hypotheses. -/
noncomputable def primaryK11CertifiedCoeffBlock_of_penalty_boxes
    (R : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hDbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (primaryK11AnalyticDFromR R) primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauD)
      (Q3.Proofs.penaltyMatrix primaryK11D primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauD)
      primaryK11DPenaltyRadius)
    (hRbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R primaryK11AnalyticQ
        CenteredCoeffPenaltyImport.primaryK11TauR)
      (Q3.Proofs.penaltyMatrix primaryK11R primaryK11Q
        CenteredCoeffPenaltyImport.primaryK11TauR)
      primaryK11RPenaltyRadius) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell where
  D := primaryK11AnalyticDFromR R
  R := R
  theta := primaryK11Theta
  theta_nonneg := primaryK11Theta_nonneg
  cert :=
    primaryK11FinitePenaltyCert_of_penalty_boxes
      (primaryK11AnalyticDFromR R) R primaryK11AnalyticQ hDbox hRbox
  split := primaryK11AnalyticSplitFromR R

/-- Primary active coefficient block directly from base D/R hboxes plus the
imported Q-row radius payload.  The analytic enclosure facts remain explicit
inputs; this definition only closes the receiver plumbing. -/
noncomputable def primaryK11CertifiedCoeffBlock_of_importedQRadius
    (R MRD MRR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hD : Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDFromR R) primaryK11D MRD)
    (hR : Q3.Proofs.matrixEntrywiseAbsLe R primaryK11R MRR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticQ primaryK11Q primaryK11QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hDRad : ∀ i j,
      MRD i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j ≤
        primaryK11DPenaltyRadius i j)
    (hRRad : ∀ i j,
      MRR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j ≤
        primaryK11RPenaltyRadius i j) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell :=
  primaryK11CertifiedCoeffBlock_of_penalty_boxes R
    (primaryK11DPenaltyBox_of_matrix_and_importedQRadius
      R MRD GR hD hQ hGRad hDRad)
    (primaryK11RPenaltyBox_of_matrix_and_importedQRadius
      R MRR GR hR hQ hGRad hRRad)

/-- Primary active coefficient block directly from base D/R hboxes plus the
Lean-checked imported Q-row hbox.  Gram-radius and D/R dominance remain
explicit generated obligations. -/
noncomputable def primaryK11CertifiedCoeffBlock_of_importedQRadius_hbox
    (R MRD MRR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hD : Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDFromR R) primaryK11D MRD)
    (hR : Q3.Proofs.matrixEntrywiseAbsLe R primaryK11R MRR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            primaryK11QRadius r i * (|primaryK11Q r j| + primaryK11QRadius r j) +
              |primaryK11Q r i| * primaryK11QRadius r j) ≤
        GR i j)
    (hDRad : ∀ i j,
      MRD i j + |CenteredCoeffPenaltyImport.primaryK11TauD| * GR i j ≤
        primaryK11DPenaltyRadius i j)
    (hRRad : ∀ i j,
      MRR i j + |CenteredCoeffPenaltyImport.primaryK11TauR| * GR i j ≤
        primaryK11RPenaltyRadius i j) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell :=
  primaryK11CertifiedCoeffBlock_of_importedQRadius
    R MRD MRR GR hD hR primaryK11QRadius_hbox hGRad hDRad hRRad

/-- Analytic control D matrix induced by a chosen analytic R matrix and the
imported control penalty parameter. -/
def controlK9AnalyticDFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixScaledSub controlK9AnalyticC R controlK9Theta

/-- The control analytic split follows structurally from the definition of
`controlK9AnalyticDFromR`. -/
theorem controlK9AnalyticSplitFromR
    (R : Matrix CoeffIndex23 CoeffIndex23 Real) :
    ∀ v : CoeffIndex23 -> Real,
      Q3.Proofs.quadForm controlK9AnalyticC v =
        Q3.Proofs.quadForm (controlK9AnalyticDFromR R) v +
          controlK9Theta * Q3.Proofs.quadForm R v := by
  intro v
  unfold controlK9AnalyticDFromR
  exact quadForm_scaled_sub_split controlK9AnalyticC R controlK9Theta v

/-- Control `k=9` D penalty hbox from a base D hbox and a boundary-Gram hbox. -/
theorem controlK9DPenaltyBox_of_matrix_and_boundaryGram
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDFromR R) controlK9D MR)
    (hG : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix controlK9Q)
      GR)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j ≤
        controlK9DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (controlK9AnalyticDFromR R) controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauD)
      controlK9DPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix
      (controlK9AnalyticDFromR R) controlK9AnalyticQ
      CenteredCoeffPenaltyImport.controlK9TauD)
    (Q3.Proofs.penaltyMatrix controlK9D controlK9Q
      CenteredCoeffPenaltyImport.controlK9TauD)
    (fun i j =>
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j)
    controlK9DPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      (controlK9AnalyticDFromR R) controlK9D MR
      controlK9AnalyticQ controlK9Q GR
      CenteredCoeffPenaltyImport.controlK9TauD hM hG)
    hRad

/-- Control `k=9` R penalty hbox from a base R hbox and a boundary-Gram hbox. -/
theorem controlK9RPenaltyBox_of_matrix_and_boundaryGram
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R controlK9R MR)
    (hG : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix controlK9Q)
      GR)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j ≤
        controlK9RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauR)
      (Q3.Proofs.penaltyMatrix controlK9R controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauR)
      controlK9RPenaltyRadius := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ
      CenteredCoeffPenaltyImport.controlK9TauR)
    (Q3.Proofs.penaltyMatrix controlK9R controlK9Q
      CenteredCoeffPenaltyImport.controlK9TauR)
    (fun i j =>
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j)
    controlK9RPenaltyRadius
    (Q3.Proofs.penaltyMatrix_entrywiseAbsLe_of_matrix_and_boundaryGram
      R controlK9R MR controlK9AnalyticQ controlK9Q GR
      CenteredCoeffPenaltyImport.controlK9TauR hM hG)
    hRad

/-
Q3 obstruction wall:
- wall: Matrix-identification / Step32F boundary-row hbox handoff
- role: tactical adapter from active boundary-row boxes to boundary Gram boxes
- input: future boundary-row hboxes and generated Gram-radius dominance lemmas
- output: control boundary-Gram hbox consumed by active D/R penalty adapters
- reviewer question answered: does the boundary-row interval payload feed the
  actual `Q^T Q` Gram term rather than stopping at rowwise midpoint/radius data?
-/
/-- Control `k=9` boundary-Gram hbox from a boundary-row hbox and a generated
Gram-radius dominance lemma. -/
theorem controlK9BoundaryGramBox_of_boundaryRows
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q QR)
    (hRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|controlK9Q r j| + QR r j) +
              |controlK9Q r i| * QR r j) ≤
        GR i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix controlK9Q)
      GR := by
  exact Q3.Proofs.matrixEntrywiseAbsLe_mono
    (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
    (Q3.Proofs.boundaryGramMatrix controlK9Q)
    (fun i j =>
      Finset.univ.sum
        (fun r : BoundaryIndex2 =>
          QR r i * (|controlK9Q r j| + QR r j) +
            |controlK9Q r i| * QR r j))
    GR
    (Q3.Proofs.boundaryGramMatrix_entrywiseAbsLe_of_matrix
      controlK9AnalyticQ controlK9Q QR hQ)
    hRad

/-- Control `k=9` D penalty hbox directly from a base D hbox, a boundary-row
hbox, and the two generated radius-dominance lemmas. -/
theorem controlK9DPenaltyBox_of_matrix_and_boundaryRows
    (R MR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDFromR R) controlK9D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q QR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|controlK9Q r j| + QR r j) +
              |controlK9Q r i| * QR r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j ≤
        controlK9DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (controlK9AnalyticDFromR R) controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauD)
      controlK9DPenaltyRadius := by
  exact controlK9DPenaltyBox_of_matrix_and_boundaryGram
    R MR GR hM
    (controlK9BoundaryGramBox_of_boundaryRows QR GR hQ hGRad)
    hRad

/-- Control `k=9` R penalty hbox directly from a base R hbox, a boundary-row
hbox, and the two generated radius-dominance lemmas. -/
theorem controlK9RPenaltyBox_of_matrix_and_boundaryRows
    (R MR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (QR : Matrix BoundaryIndex2 CoeffIndex23 Real)
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R controlK9R MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q QR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            QR r i * (|controlK9Q r j| + QR r j) +
              |controlK9Q r i| * QR r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j ≤
        controlK9RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauR)
      (Q3.Proofs.penaltyMatrix controlK9R controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauR)
      controlK9RPenaltyRadius := by
  exact controlK9RPenaltyBox_of_matrix_and_boundaryGram
    R MR GR hM
    (controlK9BoundaryGramBox_of_boundaryRows QR GR hQ hGRad)
    hRad

/-- Control `k=9` boundary-Gram hbox specialized to the imported
`controlK9QRadius` row-radius payload. -/
theorem controlK9BoundaryGramBox_of_importedQRadius
    (GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius)
    (hRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.boundaryGramMatrix controlK9AnalyticQ)
      (Q3.Proofs.boundaryGramMatrix controlK9Q)
      GR := by
  exact controlK9BoundaryGramBox_of_boundaryRows
    controlK9QRadius GR hQ hRad

/-- Control `k=9` D penalty hbox specialized to the imported
`controlK9QRadius` row-radius payload. -/
theorem controlK9DPenaltyBox_of_matrix_and_importedQRadius
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDFromR R) controlK9D MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j ≤
        controlK9DPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (controlK9AnalyticDFromR R) controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauD)
      controlK9DPenaltyRadius := by
  exact controlK9DPenaltyBox_of_matrix_and_boundaryRows
    R MR controlK9QRadius GR hM hQ hGRad hRad

/-- Control `k=9` R penalty hbox specialized to the imported
`controlK9QRadius` row-radius payload. -/
theorem controlK9RPenaltyBox_of_matrix_and_importedQRadius
    (R MR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hM : Q3.Proofs.matrixEntrywiseAbsLe R controlK9R MR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hRad : ∀ i j,
      MR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j ≤
        controlK9RPenaltyRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauR)
      (Q3.Proofs.penaltyMatrix controlK9R controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauR)
      controlK9RPenaltyRadius := by
  exact controlK9RPenaltyBox_of_matrix_and_boundaryRows
    R MR controlK9QRadius GR hM hQ hGRad hRad

/- 
Q3 obstruction wall:
- wall: Matrix-identification / Step32F coefficient certified-block handoff
- role: tactical adapter from penalty-box certificates to certified coefficient blocks
- input: concrete coefficient dictionary, analytic split, future D/R penalty hboxes
- output: control CertifiedCenteredBSplineCoeffBlock once analytic hboxes are supplied
- reviewer question answered: does the interval-backed certificate receiver feed the
  existing analytic coefficient block, rather than stopping at a penalty wrapper?
-/
/-- Control active coefficient block from the future analytic penalty-box
hypotheses. -/
noncomputable def controlK9CertifiedCoeffBlock_of_penalty_boxes
    (R : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hDbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix
        (controlK9AnalyticDFromR R) controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauD)
      (Q3.Proofs.penaltyMatrix controlK9D controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauD)
      controlK9DPenaltyRadius)
    (hRbox : Q3.Proofs.matrixEntrywiseAbsLe
      (Q3.Proofs.penaltyMatrix R controlK9AnalyticQ
        CenteredCoeffPenaltyImport.controlK9TauR)
      (Q3.Proofs.penaltyMatrix controlK9R controlK9Q
        CenteredCoeffPenaltyImport.controlK9TauR)
      controlK9RPenaltyRadius) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell where
  D := controlK9AnalyticDFromR R
  R := R
  theta := controlK9Theta
  theta_nonneg := controlK9Theta_nonneg
  cert :=
    controlK9FinitePenaltyCert_of_penalty_boxes
      (controlK9AnalyticDFromR R) R controlK9AnalyticQ hDbox hRbox
  split := controlK9AnalyticSplitFromR R

/-- Control active coefficient block directly from base D/R hboxes plus the
imported Q-row radius payload.  The analytic enclosure facts remain explicit
inputs; this definition only closes the receiver plumbing. -/
noncomputable def controlK9CertifiedCoeffBlock_of_importedQRadius
    (R MRD MRR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hD : Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDFromR R) controlK9D MRD)
    (hR : Q3.Proofs.matrixEntrywiseAbsLe R controlK9R MRR)
    (hQ : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticQ controlK9Q controlK9QRadius)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hDRad : ∀ i j,
      MRD i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j ≤
        controlK9DPenaltyRadius i j)
    (hRRad : ∀ i j,
      MRR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j ≤
        controlK9RPenaltyRadius i j) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell :=
  controlK9CertifiedCoeffBlock_of_penalty_boxes R
    (controlK9DPenaltyBox_of_matrix_and_importedQRadius
      R MRD GR hD hQ hGRad hDRad)
    (controlK9RPenaltyBox_of_matrix_and_importedQRadius
      R MRR GR hR hQ hGRad hRRad)

/-- Control active coefficient block directly from base D/R hboxes plus the
Lean-checked imported Q-row hbox.  Gram-radius and D/R dominance remain
explicit generated obligations. -/
noncomputable def controlK9CertifiedCoeffBlock_of_importedQRadius_hbox
    (R MRD MRR GR : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hD : Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDFromR R) controlK9D MRD)
    (hR : Q3.Proofs.matrixEntrywiseAbsLe R controlK9R MRR)
    (hGRad : ∀ i j,
      Finset.univ.sum
          (fun r : BoundaryIndex2 =>
            controlK9QRadius r i * (|controlK9Q r j| + controlK9QRadius r j) +
              |controlK9Q r i| * controlK9QRadius r j) ≤
        GR i j)
    (hDRad : ∀ i j,
      MRD i j + |CenteredCoeffPenaltyImport.controlK9TauD| * GR i j ≤
        controlK9DPenaltyRadius i j)
    (hRRad : ∀ i j,
      MRR i j + |CenteredCoeffPenaltyImport.controlK9TauR| * GR i j ≤
        controlK9RPenaltyRadius i j) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell :=
  controlK9CertifiedCoeffBlock_of_importedQRadius
    R MRD MRR GR hD hR controlK9QRadius_hbox hGRad hDRad hRRad

end CenteredCoeffCertifiedBlockImport
end PSDpd
end Q3
