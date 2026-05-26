import Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3
namespace PSDpd
namespace CenteredCoeffBaseHboxImport

open CenteredCoeffPayloadImport
open CenteredCoeffDictionaryImport
open CenteredCoeffCertifiedBlockImport
open CenteredCoeffPenaltyRadiusDominanceImport

/-!
Step32J base-matrix hbox receiver.

The active Step18--22 CSV contract gives entrywise hboxes for the base
matrices `A`, `P`, and `P0`.  This file proves the sharp algebraic propagation
from those base hboxes to the `Dtheta`/`Rkappa` hboxes consumed by the certified
coefficient-block wrappers.
-/

def matrixRkappa {ι : Type*}
    (A P0 : Matrix ι ι Real) (kappa : Real) :
    Matrix ι ι Real :=
  matrixScaledSub A P0 kappa

def matrixDtheta {ι : Type*}
    (A P P0 : Matrix ι ι Real) (kappa theta : Real) :
    Matrix ι ι Real :=
  fun i j => (1 - theta) * A i j - P i j + theta * kappa * P0 i j

theorem matrixRkappa_hbox {ι : Type*}
    (A A0 P0 P00 AR P0R : Matrix ι ι Real) (kappa : Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe A A0 AR)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe P0 P00 P0R) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (matrixRkappa A P0 kappa)
      (matrixRkappa A0 P00 kappa)
      (fun i j => AR i j + |kappa| * P0R i j) := by
  intro i j
  have hAij := hA i j
  have hP0ij := hP0 i j
  unfold matrixRkappa matrixScaledSub
  calc
    |(A i j - kappa * P0 i j) - (A0 i j - kappa * P00 i j)| =
        |(A i j - A0 i j) - kappa * (P0 i j - P00 i j)| := by
      ring_nf
    _ ≤ |A i j - A0 i j| + |kappa * (P0 i j - P00 i j)| := by
      simpa using
        (_root_.abs_sub_le (A i j - A0 i j) (0 : Real)
          (kappa * (P0 i j - P00 i j)))
    _ = |A i j - A0 i j| + |kappa| * |P0 i j - P00 i j| := by
      rw [abs_mul]
    _ ≤ AR i j + |kappa| * P0R i j := by
      exact add_le_add hAij
        (mul_le_mul_of_nonneg_left hP0ij (abs_nonneg kappa))

theorem matrixDtheta_hbox {ι : Type*}
    (A A0 P Pm P0 P00 AR PR P0R : Matrix ι ι Real)
    (kappa theta : Real)
    (htheta_nonneg : 0 ≤ theta)
    (htheta_le_one : theta ≤ 1)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe A A0 AR)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe P Pm PR)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe P0 P00 P0R) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (matrixDtheta A P P0 kappa theta)
      (matrixDtheta A0 Pm P00 kappa theta)
      (fun i j => (1 - theta) * AR i j + PR i j +
        theta * |kappa| * P0R i j) := by
  intro i j
  have hAij := hA i j
  have hPij := hP i j
  have hP0ij := hP0 i j
  have htheta_factor_nonneg : 0 ≤ 1 - theta := sub_nonneg.mpr htheta_le_one
  have hAterm :
      |(1 - theta) * (A i j - A0 i j)| ≤ (1 - theta) * AR i j := by
    rw [abs_mul, abs_of_nonneg htheta_factor_nonneg]
    exact mul_le_mul_of_nonneg_left hAij htheta_factor_nonneg
  have hPterm : |-(P i j - Pm i j)| ≤ PR i j := by
    simpa [abs_sub_comm] using hPij
  have hP0term :
      |theta * kappa * (P0 i j - P00 i j)| ≤
        theta * |kappa| * P0R i j := by
    calc
      |theta * kappa * (P0 i j - P00 i j)| =
          theta * |kappa| * |P0 i j - P00 i j| := by
        rw [abs_mul, abs_mul, abs_of_nonneg htheta_nonneg]
      _ ≤ theta * |kappa| * P0R i j := by
        exact mul_le_mul_of_nonneg_left hP0ij
          (mul_nonneg htheta_nonneg (abs_nonneg kappa))
  set x := (1 - theta) * (A i j - A0 i j)
  set y := -(P i j - Pm i j)
  set z := theta * kappa * (P0 i j - P00 i j)
  have hxyz : |x + y + z| ≤ |x| + |y| + |z| := by
    calc
      |x + y + z| ≤ |x + y| + |z| := by
        exact _root_.abs_add_le (x + y) z
      _ ≤ |x| + |y| + |z| := by
        have hxy := _root_.abs_add_le x y
        linarith
  calc
    |matrixDtheta A P P0 kappa theta i j -
        matrixDtheta A0 Pm P00 kappa theta i j| =
        |x + y + z| := by
      simp [matrixDtheta, x, y, z]
      ring_nf
    _ ≤ |x| + |y| + |z| := hxyz
    _ ≤ (1 - theta) * AR i j + PR i j +
        theta * |kappa| * P0R i j := by
      have hx : |x| ≤ (1 - theta) * AR i j := by
        simpa [x] using hAterm
      have hy : |y| ≤ PR i j := by
        simpa [y] using hPterm
      have hz : |z| ≤ theta * |kappa| * P0R i j := by
        simpa [z] using hP0term
      linarith

def primaryK11AnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11CoeffAnalyticKernelContract.toFormulaContract.A

def primaryK11AnalyticP : Matrix CoeffIndex23 CoeffIndex23 Real :=
  primaryK11CoeffAnalyticKernelContract.toFormulaContract.P

theorem primaryK11AnalyticC_eq_matrixSub :
    primaryK11AnalyticC =
      matrixSub primaryK11AnalyticA primaryK11AnalyticP := by
  rfl

def primaryK11AnalyticRkappa
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa primaryK11AnalyticA P0a primaryK11Kappa

def primaryK11AnalyticDtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta primaryK11AnalyticA primaryK11AnalyticP P0a
    primaryK11Kappa primaryK11Theta

theorem primaryK11AnalyticDFromR_eq_Dtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    primaryK11AnalyticDFromR (primaryK11AnalyticRkappa P0a) =
      primaryK11AnalyticDtheta P0a := by
  ext i j
  simp [primaryK11AnalyticDFromR, primaryK11AnalyticC_eq_matrixSub,
    primaryK11AnalyticRkappa, primaryK11AnalyticDtheta, matrixRkappa,
    matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem primaryK11Theta_le_one : primaryK11Theta ≤ 1 := by
  norm_num [primaryK11Theta, primaryK11ThetaRat]

theorem primaryK11AnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticA primaryK11A primaryK11ARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticRkappa P0a) primaryK11R primaryK11RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      primaryK11AnalyticA primaryK11A P0a primaryK11P0
      primaryK11ARadius primaryK11P0Radius primaryK11Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [primaryK11AnalyticRkappa, primaryK11R, primaryK11RRat,
    primaryK11A, primaryK11ARat, primaryK11P0, primaryK11P0Rat,
    primaryK11RBaseRadius, primaryK11RBaseRadiusRat,
    primaryK11ARadius, primaryK11ARadiusRat,
    primaryK11P0Radius, primaryK11P0RadiusRat,
    primaryK11Kappa, primaryK11KappaRat, matrixRkappa, matrixScaledSub,
    matrixScaledSubRat, Rat.cast_abs] using hij

theorem primaryK11AnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticA primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (primaryK11AnalyticDtheta P0a) primaryK11D primaryK11DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      primaryK11AnalyticA primaryK11A primaryK11AnalyticP primaryK11P
      P0a primaryK11P0 primaryK11ARadius primaryK11PRadius primaryK11P0Radius
      primaryK11Kappa primaryK11Theta primaryK11Theta_nonneg primaryK11Theta_le_one
      hA hP hP0
  intro i j
  have hij := h i j
  have hDentry :
      primaryK11D i j =
        (1 - primaryK11Theta) * primaryK11A i j -
          primaryK11P i j +
            primaryK11Theta * primaryK11Kappa * primaryK11P0 i j := by
    simp [primaryK11D, primaryK11DRat, primaryK11CRat,
      primaryK11RRat, primaryK11A, primaryK11ARat,
      primaryK11P, primaryK11PRat, primaryK11P0, primaryK11P0Rat,
      primaryK11Theta, primaryK11ThetaRat, primaryK11Kappa, primaryK11KappaRat,
      matrixScaledSubRat, matrixSubRat]
    ring
  rw [hDentry]
  simpa [primaryK11AnalyticDtheta, primaryK11D, primaryK11DRat,
    primaryK11A, primaryK11ARat, primaryK11P, primaryK11PRat,
    primaryK11P0, primaryK11P0Rat,
    primaryK11DBaseRadius, primaryK11DBaseRadiusRat,
    primaryK11ARadius, primaryK11ARadiusRat,
    primaryK11PRadius, primaryK11PRadiusRat,
    primaryK11P0Radius, primaryK11P0RadiusRat,
    primaryK11Kappa, primaryK11KappaRat,
    primaryK11Theta, primaryK11ThetaRat,
    matrixDtheta, matrixScaledSubRat, Rat.cast_abs] using hij

noncomputable def primaryK11CertifiedCoeffBlock_of_baseMatrixHboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticA primaryK11A primaryK11ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a primaryK11P0 primaryK11P0Radius) :
    CertifiedCenteredBSplineCoeffBlock
      11 primaryK11Ell primaryK11Center primaryK11PrimeWeight primaryK11PrimeShift
      primaryK11_hk primaryK11_hell := by
  refine primaryK11CertifiedCoeffBlock_of_importedPenaltyRadiusDominance
    (primaryK11AnalyticRkappa P0a) ?_ ?_
  · rw [primaryK11AnalyticDFromR_eq_Dtheta]
    exact primaryK11AnalyticDtheta_hbox_of_base_hboxes P0a hA hP hP0
  · exact primaryK11AnalyticRkappa_hbox_of_base_hboxes P0a hA hP0

def controlK9AnalyticA : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9CoeffAnalyticKernelContract.toFormulaContract.A

def controlK9AnalyticP : Matrix CoeffIndex23 CoeffIndex23 Real :=
  controlK9CoeffAnalyticKernelContract.toFormulaContract.P

theorem controlK9AnalyticC_eq_matrixSub :
    controlK9AnalyticC =
      matrixSub controlK9AnalyticA controlK9AnalyticP := by
  rfl

def controlK9AnalyticRkappa
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixRkappa controlK9AnalyticA P0a controlK9Kappa

def controlK9AnalyticDtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    Matrix CoeffIndex23 CoeffIndex23 Real :=
  matrixDtheta controlK9AnalyticA controlK9AnalyticP P0a
    controlK9Kappa controlK9Theta

theorem controlK9AnalyticDFromR_eq_Dtheta
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real) :
    controlK9AnalyticDFromR (controlK9AnalyticRkappa P0a) =
      controlK9AnalyticDtheta P0a := by
  ext i j
  simp [controlK9AnalyticDFromR, controlK9AnalyticC_eq_matrixSub,
    controlK9AnalyticRkappa, controlK9AnalyticDtheta, matrixRkappa,
    matrixDtheta, matrixScaledSub, matrixSub]
  ring

theorem controlK9Theta_le_one : controlK9Theta ≤ 1 := by
  norm_num [controlK9Theta, controlK9ThetaRat]

theorem controlK9AnalyticRkappa_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticA controlK9A controlK9ARadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticRkappa P0a) controlK9R controlK9RBaseRadius := by
  have h :=
    matrixRkappa_hbox
      controlK9AnalyticA controlK9A P0a controlK9P0
      controlK9ARadius controlK9P0Radius controlK9Kappa hA hP0
  intro i j
  have hij := h i j
  simpa [controlK9AnalyticRkappa, controlK9R, controlK9RRat,
    controlK9A, controlK9ARat, controlK9P0, controlK9P0Rat,
    controlK9RBaseRadius, controlK9RBaseRadiusRat,
    controlK9ARadius, controlK9ARadiusRat,
    controlK9P0Radius, controlK9P0RadiusRat,
    controlK9Kappa, controlK9KappaRat, matrixRkappa, matrixScaledSub,
    matrixScaledSubRat, Rat.cast_abs] using hij

theorem controlK9AnalyticDtheta_hbox_of_base_hboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticA controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    Q3.Proofs.matrixEntrywiseAbsLe
      (controlK9AnalyticDtheta P0a) controlK9D controlK9DBaseRadius := by
  have h :=
    matrixDtheta_hbox
      controlK9AnalyticA controlK9A controlK9AnalyticP controlK9P
      P0a controlK9P0 controlK9ARadius controlK9PRadius controlK9P0Radius
      controlK9Kappa controlK9Theta controlK9Theta_nonneg controlK9Theta_le_one
      hA hP hP0
  intro i j
  have hij := h i j
  have hDentry :
      controlK9D i j =
        (1 - controlK9Theta) * controlK9A i j -
          controlK9P i j +
            controlK9Theta * controlK9Kappa * controlK9P0 i j := by
    simp [controlK9D, controlK9DRat, controlK9CRat,
      controlK9RRat, controlK9A, controlK9ARat,
      controlK9P, controlK9PRat, controlK9P0, controlK9P0Rat,
      controlK9Theta, controlK9ThetaRat, controlK9Kappa, controlK9KappaRat,
      matrixScaledSubRat, matrixSubRat]
    ring
  rw [hDentry]
  simpa [controlK9AnalyticDtheta, controlK9D, controlK9DRat,
    controlK9A, controlK9ARat, controlK9P, controlK9PRat,
    controlK9P0, controlK9P0Rat,
    controlK9DBaseRadius, controlK9DBaseRadiusRat,
    controlK9ARadius, controlK9ARadiusRat,
    controlK9PRadius, controlK9PRadiusRat,
    controlK9P0Radius, controlK9P0RadiusRat,
    controlK9Kappa, controlK9KappaRat,
    controlK9Theta, controlK9ThetaRat,
    matrixDtheta, matrixScaledSubRat, Rat.cast_abs] using hij

noncomputable def controlK9CertifiedCoeffBlock_of_baseMatrixHboxes
    (P0a : Matrix CoeffIndex23 CoeffIndex23 Real)
    (hA : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticA controlK9A controlK9ARadius)
    (hP : Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius)
    (hP0 : Q3.Proofs.matrixEntrywiseAbsLe
      P0a controlK9P0 controlK9P0Radius) :
    CertifiedCenteredBSplineCoeffBlock
      9 controlK9Ell controlK9Center controlK9PrimeWeight controlK9PrimeShift
      controlK9_hk controlK9_hell := by
  refine controlK9CertifiedCoeffBlock_of_importedPenaltyRadiusDominance
    (controlK9AnalyticRkappa P0a) ?_ ?_
  · rw [controlK9AnalyticDFromR_eq_Dtheta]
    exact controlK9AnalyticDtheta_hbox_of_base_hboxes P0a hA hP hP0
  · exact controlK9AnalyticRkappa_hbox_of_base_hboxes P0a hA hP0

end CenteredCoeffBaseHboxImport
end PSDpd
end Q3
