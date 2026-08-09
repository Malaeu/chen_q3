import Q3.Proofs.RouteB.D0PstarSourceW02FiniteFormCCMW02Crosswalk
import Q3.Proofs.RouteB.D0PstarSourceArchFiniteFormCCMWRCrosswalk
import Q3.Proofs.RouteB.D0PstarSourcePrimeFiniteFormCCMPrimeCrosswalk
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-- B3.0K preflight candidate: assemble the exact three-component source Weil
ledger on the literal finite CCM carrier.  The source W02 component is added,
the source archimedean component is already the negative WR contribution, and
the positive source-prime component is subtracted exactly once. -/
theorem sourceWeilFiniteForm_eq_ccmWeilMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    ((∑ j, ∑ k,
        star (c j) *
          sourceW02ModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k) +
      (∑ j, ∑ k,
        star (c j) *
          sourceArchimedeanModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k) -
      (∑ j, ∑ k,
        star (c j) *
          sourcePrimeModePairing i
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) *
          d k)) =
      ∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWeilMatFinite i.m i.N j k : ℂ) *
          d k := by
  classical
  rw [sourceW02FiniteForm_eq_ccmW02MatrixForm,
    sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm,
    sourcePrimeFiniteForm_eq_ccmPrimeMatrixForm]
  have hL : L_m i = Q3.RouteB.ccmL i.m := rfl
  rw [hL]
  simp only [Q3.RouteB.ccmWeilMatFinite_apply, Q3.RouteB.ccmWeilTauN1]
  push_cast
  simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib]
  ring

#print axioms sourceWeilFiniteForm_eq_ccmWeilMatrixForm

end Q3.RouteB.D0Pstar
