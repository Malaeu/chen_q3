/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MuntzV3SymmetricTrialCrosswalk.lean
Source SHA-256: ebede2df7ff55b811bafd1dcbbb55baea064658b406611bbec4e093fd94c6f9b
Body copied byte-for-byte; import path rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.ExactClassClosure

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace EStarMuntzZeroMassContinuation

/-- The positive-half representative of a symmetric source trial.  All Muntz
objects in this project evaluate their input only at positive real arguments. -/
noncomputable def positiveHalf (h : ℝ → ℂ) : ℝ → ℂ :=
  (Set.Ici (0 : ℝ)).indicator h

@[simp] theorem positiveHalf_eq_of_nonneg
    (h : ℝ → ℂ) {u : ℝ} (hu : 0 ≤ u) :
    positiveHalf h u = h u := by
  simp [positiveHalf, hu]

@[simp] theorem positiveHalf_eq_zero_of_neg
    (h : ℝ → ℂ) {u : ℝ} (hu : u < 0) :
    positiveHalf h u = 0 := by
  simp [positiveHalf, not_le.mpr hu]

theorem Estar_positiveHalf_of_pos
    (h : ℝ → ℂ) {u : ℝ} (hu : 0 < u) :
    Estar (positiveHalf h) u = Estar h u := by
  unfold Estar
  apply congrArg (fun z : ℂ => (Real.sqrt u : ℂ) * z)
  apply tsum_congr
  intro n
  rw [positiveHalf_eq_of_nonneg]
  positivity

theorem Mellin_positiveHalf (h : ℝ → ℂ) :
    Mellin (positiveHalf h) = Mellin h := by
  funext s
  unfold Mellin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  rw [positiveHalf_eq_of_nonneg h hu.le]

theorem Gwin_positiveHalf
    (h : ℝ → ℂ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Gwin (positiveHalf h) Λ = Gwin h Λ := by
  funext s
  unfold Gwin
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  have hu0 : 0 < u := (inv_pos.mpr hΛ0).trans hu.1
  rw [Estar_positiveHalf_of_pos h hu0]

theorem Rminus_positiveHalf
    (h : ℝ → ℂ) (Λ : ℝ) :
    Rminus (positiveHalf h) Λ = Rminus h Λ := by
  funext s
  unfold Rminus
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  rw [Estar_positiveHalf_of_pos h hu.1]

theorem Rplus_positiveHalf
    (h : ℝ → ℂ) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Rplus (positiveHalf h) Λ = Rplus h Λ := by
  funext s
  unfold Rplus
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
  have hΛ0 : 0 < Λ := zero_lt_one.trans_le hΛ
  rw [Estar_positiveHalf_of_pos h (hΛ0.trans hu)]

theorem ZetaMellinPoleSub_positiveHalf (h : ℝ → ℂ) :
    ZetaMellinPoleSub (positiveHalf h) = ZetaMellinPoleSub h := by
  funext w
  unfold ZetaMellinPoleSub MellinDivOne
  rw [Mellin_positiveHalf h]

/-- The exact-class continued Muntz identity for a symmetric source trial.
The proof restricts the trial to its positive half, applies the closed v3
receiver, and explicitly transports every Muntz object back to the original
function.  It does not identify a finite Galerkin ground family or prove a
cofinal limit. -/
theorem continued_window_identity_symmetricTrial_v3Class
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (-b) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s := by
  have hmeasPos : Measurable (positiveHalf h) :=
    hmeas.indicator measurableSet_Ici
  have hsuppPos :
      ∀ u, u ∉ Set.Icc (0 : ℝ) b → positiveHalf h u = 0 := by
    intro u hu
    by_cases hu0 : 0 ≤ u
    · rw [positiveHalf_eq_of_nonneg h hu0]
      apply hsupp
      intro husym
      exact hu ⟨hu0, husym.2⟩
    · exact positiveHalf_eq_zero_of_neg h (lt_of_not_ge hu0)
  have hlipPos :
      LipschitzOnWith K (positiveHalf h) (Set.Ico (0 : ℝ) b) := by
    intro x hx y hy
    simpa [positiveHalf_eq_of_nonneg h hx.1,
      positiveHalf_eq_of_nonneg h hy.1] using hlip hx hy
  have hmassPos :
      ∫ u in Set.Ioi (0 : ℝ), positiveHalf h u = 0 := by
    calc
      (∫ u in Set.Ioi (0 : ℝ), positiveHalf h u) =
          ∫ u in Set.Ioi (0 : ℝ), h u := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        rw [positiveHalf_eq_of_nonneg h hu.le]
      _ = 0 := hmass
  have hcontinued :=
    continued_window_identity_v3Class
      (positiveHalf h) b K hb hmeasPos hsuppPos hlipPos hmassPos Λ hΛ
  rw [Gwin_positiveHalf h Λ hΛ,
    ZetaMellinPoleSub_positiveHalf h,
    Rminus_positiveHalf h Λ,
    Rplus_positiveHalf h Λ hΛ] at hcontinued
  exact hcontinued

#print axioms continued_window_identity_symmetricTrial_v3Class

end EStarMuntzZeroMassContinuation
