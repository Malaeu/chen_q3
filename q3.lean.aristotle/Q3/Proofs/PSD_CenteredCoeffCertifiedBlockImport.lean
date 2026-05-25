import Q3.Proofs.PSD_CenteredCoeffDictionaryImport
import Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 0

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffCertifiedBlockImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
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

end CenteredCoeffCertifiedBlockImport
end PSDpd
end Q3
