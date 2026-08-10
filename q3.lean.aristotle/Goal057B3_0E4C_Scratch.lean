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

example (i : PairIndex) :
    sourceArchimedeanModePairing i 0 0 =
      -(Q3.RouteB.ccmWREntry (L_m i) 0 0 : ℂ) := by
  exact sourceArchimedeanModePairing_eq_neg_ccmWREntry i 0 0

example (i : PairIndex) :
    sourceArchimedeanModePairing i 0 1 =
      -(Q3.RouteB.ccmWREntry (L_m i) 0 1 : ℂ) := by
  exact sourceArchimedeanModePairing_eq_neg_ccmWREntry i 0 1

example (i : PairIndex) :
    sourceArchimedeanModePairing i 1 0 =
      -(Q3.RouteB.ccmWREntry (L_m i) 1 0 : ℂ) := by
  exact sourceArchimedeanModePairing_eq_neg_ccmWREntry i 1 0

#print axioms sourceArchimedeanModePairing_eq_neg_ccmWREntry

end Q3.RouteB.D0Pstar
