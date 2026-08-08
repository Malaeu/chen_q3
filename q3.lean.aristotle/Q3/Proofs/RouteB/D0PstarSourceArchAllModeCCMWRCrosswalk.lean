import Q3.Proofs.RouteB.D0PstarSourceArchOffDiagonalCCMWRCrosswalk
import Q3.Proofs.RouteB.D0PstarSourceArchDiagonalCCMWRCrosswalk

noncomputable section

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform RealInnerProductSpace ComplexConjugate

namespace Q3.RouteB.D0Pstar

theorem sourceArchimedeanModePairing_eq_neg_ccmWREntry
    (i : PairIndex) (n r : ℤ) :
    sourceArchimedeanModePairing i n r =
      -(Q3.RouteB.ccmWREntry (L_m i) n r : ℂ) := by
  by_cases h : n = r
  · subst r
    exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_diag i n
  · exact sourceArchimedeanModePairing_eq_neg_ccmWREntry_of_ne i h

end Q3.RouteB.D0Pstar
