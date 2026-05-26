import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffEntryHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffAnalyticP0Import

/-!
Step32L entry-hbox certificate bundle.

Step32K names the analytic `P0` matrix.  This file freezes the exact generated
certificate shape needed next: entrywise hboxes for analytic `A`, `P`, and
`P0` against the imported midpoint/radius payloads.
-/

structure PrimaryK11BaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticA primaryK11A primaryK11ARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP primaryK11P primaryK11PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius

structure ControlK9BaseEntryHboxCert : Prop where
  hA : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticA controlK9A controlK9ARadius
  hP : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP controlK9P controlK9PRadius
  hP0 : Q3.Proofs.matrixEntrywiseAbsLe
    controlK9AnalyticP0 controlK9P0 controlK9P0Radius

/-- Active primary/control entry-hbox certificate bundle. -/
structure ActiveCenteredCoeffEntryHboxCert : Prop where
  primary : PrimaryK11BaseEntryHboxCert
  control : ControlK9BaseEntryHboxCert

noncomputable def primaryK11CertifiedCoeffBlock_of_entryHboxCert
    (cert : PrimaryK11BaseEntryHboxCert) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell :=
  primaryK11CertifiedCoeffBlock_of_analyticBaseMatrixHboxes
    cert.hA cert.hP cert.hP0

noncomputable def controlK9CertifiedCoeffBlock_of_entryHboxCert
    (cert : ControlK9BaseEntryHboxCert) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell :=
  controlK9CertifiedCoeffBlock_of_analyticBaseMatrixHboxes
    cert.hA cert.hP cert.hP0

noncomputable def primaryK11CertifiedCoeffBlock_of_activeEntryHboxCert
    (cert : ActiveCenteredCoeffEntryHboxCert) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell :=
  primaryK11CertifiedCoeffBlock_of_entryHboxCert cert.primary

noncomputable def controlK9CertifiedCoeffBlock_of_activeEntryHboxCert
    (cert : ActiveCenteredCoeffEntryHboxCert) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell :=
  controlK9CertifiedCoeffBlock_of_entryHboxCert cert.control

end CenteredCoeffEntryHboxImport
end PSDpd
end Q3
