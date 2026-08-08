import Q3.Proofs.RouteB.D0PstarSourcePrimeModePairing
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- B3.0J preflight candidate: lift the exact positive source-prime entrywise
crosswalk to the literal finite CCM carrier, retaining conjugate-linearity in
the first coefficient slot and linearity in the second.  The later complete
Weil ledger, not this positive component, owns the prime subtraction. -/
theorem sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourcePrimeModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmPrimeEntryN1
            i.m
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k := by
  classical
  simp only [sourcePrimeModePairing_eq_ccmPrimeEntryN1]

#print axioms sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm

end Q3.RouteB.D0Pstar
