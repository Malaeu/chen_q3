import Q3.Proofs.PSD_CenteredCoeffBaseHboxImport

set_option linter.mathlibStandardSet false

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Q3
namespace PSDpd
namespace CenteredCoeffAnalyticP0Import

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffBaseHboxImport

/-!
Step32K analytic `P0` receiver.

Step21 computes interval enclosures for the continuous prime-main kernel

`P0(d) = int_0^(2L) exp(a/2) * (r_k((d-a)/ell) + r_k((d+a)/ell)) da`.

This file introduces that analytic matrix object in Lean and plugs it into the
Step32J base-hbox wrappers.  The numerical hbox facts are still explicit
premises; they are the next generated Step21 certificates.
-/

/-- Continuous prime-main centered B-spline kernel profile from Step21. -/
def centeredBSplineP0KernelProfile
    (k : Nat) (ell L d : Real) : Real :=
  ∫ a in (0 : Real)..(2 * L),
    Real.exp (a / 2) *
      (centeredBSplineR k ((d - a) / ell) +
        centeredBSplineR k ((d + a) / ell))

/-- Matrix form of the continuous prime-main kernel on packet centers. -/
def centeredBSplineP0KernelMatrix {ι : Type*}
    (k : Nat) (ell L : Real) (center : ι -> Real) :
    Matrix ι ι Real :=
  fun i j => centeredBSplineP0KernelProfile k ell L (center j - center i)

/-- Active L=3 support radius used by the Step21/Step22 payloads. -/
def activeL3SupportRadiusRat : Rat := 3

def activeL3SupportRadius : Real := (activeL3SupportRadiusRat : Real)

def primaryK11AnalyticP0 : Matrix CoeffIndex23 CoeffIndex23 Real :=
  centeredBSplineP0KernelMatrix
    11 primaryK11Ell activeL3SupportRadius primaryK11Center

theorem primaryK11AnalyticP0_entry (i j : CoeffIndex23) :
    primaryK11AnalyticP0 i j =
      centeredBSplineP0KernelProfile
        11 primaryK11Ell activeL3SupportRadius
          (primaryK11Center j - primaryK11Center i) := by
  rfl

noncomputable def primaryK11CertifiedCoeffBlock_of_analyticBaseMatrixHboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticA primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell :=
  primaryK11CertifiedCoeffBlock_of_baseMatrixHboxes
    primaryK11AnalyticP0 hA hP hP0

def controlK9AnalyticP0 : Matrix CoeffIndex23 CoeffIndex23 Real :=
  centeredBSplineP0KernelMatrix
    9 controlK9Ell activeL3SupportRadius controlK9Center

theorem controlK9AnalyticP0_entry (i j : CoeffIndex23) :
    controlK9AnalyticP0 i j =
      centeredBSplineP0KernelProfile
        9 controlK9Ell activeL3SupportRadius
          (controlK9Center j - controlK9Center i) := by
  rfl

noncomputable def controlK9CertifiedCoeffBlock_of_analyticBaseMatrixHboxes
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticA controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell :=
  controlK9CertifiedCoeffBlock_of_baseMatrixHboxes
    controlK9AnalyticP0 hA hP hP0

end CenteredCoeffAnalyticP0Import
end PSDpd
end Q3
