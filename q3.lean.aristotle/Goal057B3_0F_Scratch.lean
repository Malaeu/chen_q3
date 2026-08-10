import Q3.Proofs.RouteB.D0PstarSourceArchAllModeCCMWRCrosswalk
import Q3.Proofs.RouteB.CCMFiniteWeilSourceMatrix

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

theorem sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  classical
  simp [sourceArchimedeanModePairing_eq_neg_ccmWREntry]

example
    (i : PairIndex)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      -(∑ j, ∑ k,
        star (c j) *
          (Q3.RouteB.ccmWREntry
            (L_m i)
            (ccmModeFinite i.N j)
            (ccmModeFinite i.N k) : ℂ) *
          d k) := by
  exact sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm i c d

example
    (i : PairIndex)
    (a : ℂ)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star ((a • c) j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        d k) =
      star a *
        (∑ j, ∑ k,
          star (c j) *
            sourceArchimedeanModePairing i
              (ccmModeFinite i.N j)
              (ccmModeFinite i.N k) *
            d k) := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [star_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

example
    (i : PairIndex)
    (a : ℂ)
    (c d : CCMModeFinite i.N → ℂ) :
    (∑ j, ∑ k,
      star (c j) *
        sourceArchimedeanModePairing i
          (ccmModeFinite i.N j)
          (ccmModeFinite i.N k) *
        (a • d) k) =
      a *
        (∑ j, ∑ k,
          star (c j) *
            sourceArchimedeanModePairing i
              (ccmModeFinite i.N j)
              (ccmModeFinite i.N k) *
            d k) := by
  classical
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

example (N : ℕ) (j : CCMModeFinite N) :
    ccmModeFinite N j = (j.1 : ℤ) - N := rfl

example :
    let A : Matrix (Fin 2) (Fin 2) ℂ :=
      fun j k => if j = 0 ∧ k = 1 then 1 else 0
    let c : Fin 2 → ℂ := fun j => if j = 0 then 1 else 0
    let d : Fin 2 → ℂ := fun k => if k = 1 then 1 else 0
    (∑ j, ∑ k, star (c j) * A j k * d k) = 1 ∧
      (∑ j, ∑ k, star (c j) * A k j * d k) = 0 := by
  norm_num [Fin.sum_univ_two]

#print axioms sourceArchimedeanFiniteForm_eq_neg_ccmWRMatrixForm

end Q3.RouteB.D0Pstar
