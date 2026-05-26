import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport
import Q3.Proofs.PSD_CenteredCoeffPrimeDictionaryBoundsImport
import Q3.Proofs.PSD_CenteredBSplineRBoundsImport

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffPrimeEntryHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport
open CenteredCoeffPrimeDictionaryBoundsImport

/-!
Step32 prime-side entry hbox surface.

This module exposes the analytic primary/control `P` entries as the finite
prime kernel profiles generated from the active dictionary.  The remaining
hbox certificates must prove scalar midpoint-radius enclosures for these
finite sums.
-/

/-- Primary `k=11` analytic prime entries are the finite prime kernel profile
on the active packet centers. -/
theorem primaryK11AnalyticP_entry (i j : CoeffIndex23) :
    primaryK11AnalyticP i j =
      centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i) := by
  simp [primaryK11AnalyticP, primaryK11CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineFinitePrimePacketCoeffKernelData]

/-- Once the finite prime profile has a scalar entry enclosure, it gives the
primary analytic `P` entry hbox required by the active Step32 certificate. -/
theorem primaryK11AnalyticP_entry_hbox_of_profile_hbox
    (hprofile :
      ∀ i j : CoeffIndex23,
        |centeredBSplineFinitePrimeKernelProfile
            11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
            (primaryK11Center j - primaryK11Center i) -
          primaryK11P i j| ≤ primaryK11PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius := by
  intro i j
  simpa [primaryK11AnalyticP_entry i j] using hprofile i j

/-- Control `k=9` analytic prime entries are the finite prime kernel profile
on the active packet centers. -/
theorem controlK9AnalyticP_entry (i j : CoeffIndex23) :
    controlK9AnalyticP i j =
      centeredBSplineFinitePrimeKernelProfile
        9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
        (controlK9Center j - controlK9Center i) := by
  simp [controlK9AnalyticP, controlK9CoeffAnalyticKernelContract,
    BSplineAnalyticKernelContract.toFormulaContract,
    BSplineAnalyticKernelContract.toBasisFormulaContract,
    BSplineBasisFormulaContract.toFormulaContract,
    PacketKernelPairingData.toBilinearMatrixExpansion,
    PacketKernelPairingData.matrix, matrixOfKernel,
    centeredBSplineCoeffAnalyticKernelContract,
    centeredBSplineFinitePrimePacketCoeffKernelData]

/-- Once the finite prime profile has a scalar entry enclosure, it gives the
control analytic `P` entry hbox required by the active Step32 certificate. -/
theorem controlK9AnalyticP_entry_hbox_of_profile_hbox
    (hprofile :
      ∀ i j : CoeffIndex23,
        |centeredBSplineFinitePrimeKernelProfile
            9 controlK9Ell controlK9PrimeWeight controlK9PrimeShift
            (controlK9Center j - controlK9Center i) -
          controlK9P i j| ≤ controlK9PRadius i j) :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius := by
  intro i j
  simpa [controlK9AnalyticP_entry i j] using hprofile i j

end CenteredCoeffPrimeEntryHboxImport
end PSDpd
end Q3
