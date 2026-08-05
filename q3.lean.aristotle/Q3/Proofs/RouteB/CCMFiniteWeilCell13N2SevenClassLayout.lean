import Q3.Proofs.RouteB.CCMFiniteWeilCell13N2ClassCrosswalk

set_option linter.mathlibStandardSet false

/-!
# Exact seven-class layout of the CCM cell `(13, 2)`

This file materializes only the typed `Fin 5 × Fin 5` source layout.  It uses
the literal CCM matrix, its exact symmetries, and the two antipodal identities.
It contains no numerical enclosure, component ball, or analytic estimate.
-/

namespace Q3.RouteB

noncomputable section

private theorem ccmSevenClassPlantCNotD :
    ccmQKernel 1 (-2) 2 (1 / 4) = ccmQKernel 1 (-2) 0 (1 / 4) ∧
      ccmQKernel 1 (-2) 0 (1 / 4) ≠
        ccmQKernel 1 (-2) 1 (1 / 4) := by
  constructor
  · norm_num [ccmQKernel, Real.sin_neg]
    ring_nf
  · norm_num [ccmQKernel, Real.sin_neg]
    ring_nf
    rw [Real.sin_pi, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two]
    field_simp [Real.pi_ne_zero]
    norm_num

private theorem ccmSevenClassPlantFNotE :
    ccmQKernel 1 (-1) 1 (1 / 4) = ccmQKernel 1 (-1) 0 (1 / 4) ∧
      ccmQKernel 1 (-1) 0 (1 / 4) ≠
        ccmQKernel 1 (-1) (-1) (1 / 4) := by
  constructor
  · norm_num [ccmQKernel, Real.sin_neg]
    ring_nf
  · norm_num [ccmQKernel, Real.sin_neg, Real.cos_neg]
    ring_nf
    rw [show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.sin_pi_div_two, Real.cos_pi_div_two]
    simp [Real.pi_ne_zero]

private theorem ccmSevenClassPlantOneAxisReversal :
    ccmQKernel 1 (-2) (-1) (1 / 4) ≠
      ccmQKernel 1 (-2) 1 (1 / 4) := by
  norm_num [ccmQKernel, Real.sin_neg]
  ring_nf
  rw [Real.sin_pi, show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
    Real.sin_pi_div_two]
  field_simp [Real.pi_ne_zero]
  norm_num

/-- The literal CCM `(13, 2)` matrix has exactly the fixed seven source
classes used by the future cancellation-preserving enclosure receiver. -/
theorem ccmWeilMatFinite_13_2_eq_seven_class_layout :
    ccmWeilMatFinite 13 2 =
      (![![ccmWeilTauN1 13 (-2) (-2),
          ccmWeilTauN1 13 (-2) (-1),
          ccmWeilTauN1 13 (-2) 0,
          ccmWeilTauN1 13 (-2) 1,
          ccmWeilTauN1 13 (-2) 0],
        ![ccmWeilTauN1 13 (-2) (-1),
          ccmWeilTauN1 13 (-1) (-1),
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 (-2) 1],
        ![ccmWeilTauN1 13 (-2) 0,
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 0 0,
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 (-2) 0],
        ![ccmWeilTauN1 13 (-2) 1,
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 (-1) 0,
          ccmWeilTauN1 13 (-1) (-1),
          ccmWeilTauN1 13 (-2) (-1)],
        ![ccmWeilTauN1 13 (-2) 0,
          ccmWeilTauN1 13 (-2) 1,
          ccmWeilTauN1 13 (-2) 0,
          ccmWeilTauN1 13 (-2) (-1),
          ccmWeilTauN1 13 (-2) (-2)]] :
        Matrix (CCMModeFinite 2) (CCMModeFinite 2) ℝ) := by
  have hm : 2 ≤ (13 : ℕ) := by norm_num
  have h04 := ccmWeilTauN1_neg_self_eq_neg_zero 13 2
  have h13 := ccmWeilTauN1_neg_self_eq_neg_zero 13 1
  have h10 :
      ccmWeilTauN1 13 (-1) (-2) = ccmWeilTauN1 13 (-2) (-1) :=
    ccmWeilTauN1_symm 13 hm (-1) (-2)
  have h14 : ccmWeilTauN1 13 (-1) 2 = ccmWeilTauN1 13 (-2) 1 := by
    rw [ccmWeilTauN1_symm 13 hm (-1) 2]
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) 1
  have h20 : ccmWeilTauN1 13 0 (-2) = ccmWeilTauN1 13 (-2) 0 :=
    ccmWeilTauN1_symm 13 hm 0 (-2)
  have h21 : ccmWeilTauN1 13 0 (-1) = ccmWeilTauN1 13 (-1) 0 :=
    ccmWeilTauN1_symm 13 hm 0 (-1)
  have h23 : ccmWeilTauN1 13 0 1 = ccmWeilTauN1 13 (-1) 0 := by
    calc
      ccmWeilTauN1 13 0 1 = ccmWeilTauN1 13 0 (-1) := by
        simpa only [neg_zero, neg_neg] using
          ccmWeilTauN1_neg_neg 13 hm 0 (-1)
      _ = ccmWeilTauN1 13 (-1) 0 := h21
  have h24 : ccmWeilTauN1 13 0 2 = ccmWeilTauN1 13 (-2) 0 := by
    calc
      ccmWeilTauN1 13 0 2 = ccmWeilTauN1 13 0 (-2) := by
        simpa only [neg_zero, neg_neg] using
          ccmWeilTauN1_neg_neg 13 hm 0 (-2)
      _ = ccmWeilTauN1 13 (-2) 0 := h20
  have h30 : ccmWeilTauN1 13 1 (-2) = ccmWeilTauN1 13 (-2) 1 :=
    ccmWeilTauN1_symm 13 hm 1 (-2)
  have h31 : ccmWeilTauN1 13 1 (-1) = ccmWeilTauN1 13 (-1) 0 := by
    rw [ccmWeilTauN1_symm 13 hm 1 (-1)]
    exact h13
  have h32 : ccmWeilTauN1 13 1 0 = ccmWeilTauN1 13 (-1) 0 := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-1) 0
  have h33 : ccmWeilTauN1 13 1 1 = ccmWeilTauN1 13 (-1) (-1) := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-1) (-1)
  have h34 : ccmWeilTauN1 13 1 2 = ccmWeilTauN1 13 (-2) (-1) := by
    rw [ccmWeilTauN1_symm 13 hm 1 2]
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) (-1)
  have h40 : ccmWeilTauN1 13 2 (-2) = ccmWeilTauN1 13 (-2) 0 := by
    rw [ccmWeilTauN1_symm 13 hm 2 (-2)]
    exact h04
  have h41 : ccmWeilTauN1 13 2 (-1) = ccmWeilTauN1 13 (-2) 1 := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) 1
  have h42 : ccmWeilTauN1 13 2 0 = ccmWeilTauN1 13 (-2) 0 := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) 0
  have h43 : ccmWeilTauN1 13 2 1 = ccmWeilTauN1 13 (-2) (-1) := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) (-1)
  have h44 : ccmWeilTauN1 13 2 2 = ccmWeilTauN1 13 (-2) (-2) := by
    simpa using ccmWeilTauN1_neg_neg 13 hm (-2) (-2)
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ccmWeilMatFinite, ccmModeFinite, h04, h13, h10, h14, h20, h21,
      h23, h24, h30, h31, h32, h33, h34, h40, h41, h42, h43, h44]

end

end Q3.RouteB
