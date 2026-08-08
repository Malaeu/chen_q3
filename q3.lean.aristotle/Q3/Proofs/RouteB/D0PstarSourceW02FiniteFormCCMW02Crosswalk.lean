import Q3.Proofs.RouteB.D0PstarSourceW02ModePairing
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- B3.0H hole-free preflight: lift the exact entrywise source-W02 crosswalk
to the literal finite CCM carrier, retaining conjugate-linearity in the first
coefficient slot and linearity in the second. -/
theorem sourceW02FiniteForm_eq_ccmW02MatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceW02ModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmW02Entry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k := by
  classical
  simp only [sourceW02ModePairing_eq_ccmW02Entry]

#print axioms sourceW02FiniteForm_eq_ccmW02MatrixForm

end Q3.RouteB.D0Pstar
