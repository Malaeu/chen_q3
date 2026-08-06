/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/Main.lean
Source SHA-256: 0b2e52db207610f0e63c3dac3e61c5d14f26d0119ccd11756cdbeeab80f3b888
Body copied byte-for-byte; no import or namespace rewrite required.
Port date: 2026-08-06
-/

import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Set Filter MeasureTheory Complex

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace EStarMuntzZeroMassContinuation

noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.sqrt u * ∑' n : ℕ+, h (n * u)

noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), k u * (u : ℂ) ^ (s - 1)

noncomputable def Gwin (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (Λ⁻¹) Λ, Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rminus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (0 : ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rplus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)

def H : Set ℂ := {w : ℂ | 0 < w.re}

noncomputable def MellinDivOne (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  dslope (Mellin h) 1 w

noncomputable def ZetaResidueFactor : ℂ → ℂ :=
  Function.update (fun z => (z - 1) * riemannZeta z) 1 1

noncomputable def ZetaMellinPoleSub (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  ZetaResidueFactor w * MellinDivOne h w

lemma one_mem_H : (1 : ℂ) ∈ H := by simp [H]

/-- At `s = 1`, the Mellin kernel is one, so zero mass gives a zero. -/
theorem mellin_one_eq_zero (h : ℝ → ℂ)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) : Mellin h 1 = 0 := by
  simpa [Mellin] using hmass

lemma mellinDivOne_value_one (h : ℝ → ℂ) :
    MellinDivOne h 1 = deriv (Mellin h) 1 := by
  simp [MellinDivOne, dslope_same]

lemma mellinDivOne_of_ne (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1) :
    MellinDivOne h w = (Mellin h w - Mellin h 1) / (w - 1) := by
  rw [MellinDivOne, dslope_of_ne (Mellin h) hw]
  simp [slope, div_eq_inv_mul, mul_comm]

lemma mellinDivOne_of_ne_of_zero (h : ℝ → ℂ) (hz : Mellin h 1 = 0)
    {w : ℂ} (hw : w ≠ 1) : MellinDivOne h w = Mellin h w / (w - 1) := by
  rw [mellinDivOne_of_ne h hw, hz, sub_zero]

lemma mellinDivOne_analyticOn (h : ℝ → ℂ) (ha : AnalyticOnNhd ℂ (Mellin h) H) :
    AnalyticOnNhd ℂ (MellinDivOne h) H := by
  intro w hw
  by_cases heq : w = 1
  · subst w
    rcases ha 1 one_mem_H with ⟨p, hp⟩
    exact ⟨p.fslope, hp.has_fpower_series_dslope_fslope⟩
  · have hnum : AnalyticAt ℂ (fun z => Mellin h z - Mellin h 1) w :=
      (ha w hw).sub analyticAt_const
    have hden : AnalyticAt ℂ (fun z : ℂ => z - 1) w := analyticAt_id.sub analyticAt_const
    have hq := hnum.div hden (sub_ne_zero.mpr heq)
    apply hq.congr
    filter_upwards [eventually_ne_nhds heq] with z hz
    exact (mellinDivOne_of_ne h hz).symm

lemma zetaResidueFactor_value_one : ZetaResidueFactor 1 = 1 := by
  simp [ZetaResidueFactor]

lemma zetaResidueFactor_of_ne {w : ℂ} (hw : w ≠ 1) :
    ZetaResidueFactor w = (w - 1) * riemannZeta w := by
  simp [ZetaResidueFactor, Function.update_of_ne hw]

lemma zetaResidueFactor_continuousAt_one : ContinuousAt ZetaResidueFactor 1 := by
  rw [ZetaResidueFactor, continuousAt_update_same]
  exact riemannZeta_residue_one

lemma zetaResidueFactor_analyticAt_one : AnalyticAt ℂ ZetaResidueFactor 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hd : DifferentiableAt ℂ (fun x : ℂ => (x - 1) * riemannZeta x) z :=
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).mul
        (differentiableAt_riemannZeta hz)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact zetaResidueFactor_of_ne hx
  · exact zetaResidueFactor_continuousAt_one

lemma zetaResidueFactor_analyticOn : AnalyticOnNhd ℂ ZetaResidueFactor H := by
  intro w hw
  by_cases heq : w = 1
  · simpa [heq] using zetaResidueFactor_analyticAt_one
  · rw [Complex.analyticAt_iff_eventually_differentiableAt]
    filter_upwards [eventually_ne_nhds heq] with z hz
    have hd : DifferentiableAt ℂ (fun x : ℂ => (x - 1) * riemannZeta x) z :=
      (differentiableAt_id.sub (differentiableAt_const (1 : ℂ))).mul
        (differentiableAt_riemannZeta hz)
    apply hd.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hz] with x hx
    exact zetaResidueFactor_of_ne hx

lemma zetaMellinPoleSub_analyticOn (h : ℝ → ℂ)
    (ha : AnalyticOnNhd ℂ (Mellin h) H) :
    AnalyticOnNhd ℂ (ZetaMellinPoleSub h) H :=
  zetaResidueFactor_analyticOn.mul (mellinDivOne_analyticOn h ha)

lemma zetaMellinPoleSub_off_pole (h : ℝ → ℂ) (hz : Mellin h 1 = 0)
    {w : ℂ} (hwH : w ∈ H) (hw : w ≠ 1) :
    ZetaMellinPoleSub h w = riemannZeta w * Mellin h w := by
  have _hpos : 0 < w.re := hwH
  rw [ZetaMellinPoleSub, zetaResidueFactor_of_ne hw,
    mellinDivOne_of_ne_of_zero h hz hw]
  field_simp [sub_ne_zero.mpr hw]

lemma zetaMellinPoleSub_value_one (h : ℝ → ℂ) :
    ZetaMellinPoleSub h 1 = deriv (Mellin h) 1 := by
  simp [ZetaMellinPoleSub, zetaResidueFactor_value_one, mellinDivOne_value_one]

def shiftedHalfPlane : Set ℂ := {s : ℂ | -(1 / 2 : ℝ) < s.re}

lemma shiftedHalfPlane_isPreconnected : IsPreconnected shiftedHalfPlane := by
  apply Convex.isPreconnected
  simp only [shiftedHalfPlane]
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at hx hy ⊢
  simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
  have hab' : b = 1 - a := by linarith
  have ha' : a ≤ 1 := by linarith
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    subst ha0 hb1; linarith
  · by_cases ha1 : a = 1
    · subst ha1
      have hb0 : b = 0 := by linarith
      rw [hb0]
      simp
      linarith
    · have ha'' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
      have hb'' : 0 < b := lt_of_le_of_ne hb (by intro h; subst h; exact ha1 (by linarith))
      nlinarith [hx, hy]

/-- Identity-theorem glue used by the continued window identity. -/
theorem continued_window_identity_of_analytic
    (h : ℝ → ℂ) (Λ : ℝ)
    (hmellin : AnalyticOnNhd ℂ (Mellin h) H)
    (hmass : Mellin h 1 = 0)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) shiftedHalfPlane)
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) shiftedHalfPlane)
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) shiftedHalfPlane)
    (habs : ∀ s : ℂ, 1 / 2 < s.re →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) - Rminus h Λ s - Rplus h Λ s := by
  -- Define the RHS function
  let F : ℂ → ℂ := fun s => ZetaMellinPoleSub h (s + 1 / 2) - Rminus h Λ s - Rplus h Λ s
  -- Show F is analytic on shiftedHalfPlane
  have hF : AnalyticOnNhd ℂ F shiftedHalfPlane := by
    apply AnalyticOnNhd.sub
    apply AnalyticOnNhd.sub
    · let g : ℂ → ℂ := fun s => s + 1/2
      have hg : AnalyticOnNhd ℂ g shiftedHalfPlane := analyticOnNhd_id.add analyticOnNhd_const
      have hmap : ∀ s ∈ shiftedHalfPlane, g s ∈ H := by
        intro s hs
        simp only [H, shiftedHalfPlane, g] at *
        norm_num at *
        linarith
      exact (zetaMellinPoleSub_analyticOn h hmellin).comp hg hmap
    · exact hRm
    · exact hRp
  -- For s.re > 1/2, the RHS equals the LHS by habs
  have hFEqOn : ∀ s : ℂ, 1/2 < s.re → F s = Gwin h Λ s := by
    intro s hs
    simp only [F]
    rw [habs s hs]
    congr 1
    rw [zetaMellinPoleSub_off_pole h hmass]
    · simp [H]; norm_num; linarith
    · intro heq
      have : s.re = 1/2 := by
        have := congr_arg Complex.re heq
        norm_num at this
        linarith
      linarith
  -- Use identity theorem
  have hI : ∀ z : ℂ, z ∈ shiftedHalfPlane → F z = Gwin h Λ z := by
    have hmem : (1 : ℂ) ∈ shiftedHalfPlane := by simp [shiftedHalfPlane]; norm_num
    apply AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq hF hG shiftedHalfPlane_isPreconnected hmem
    rw [Filter.eventuallyEq_iff_exists_mem]
    use {s : ℂ | 1/2 < s.re}
    constructor
    · have : IsOpen {s : ℂ | 1/2 < s.re} := isOpen_lt continuous_const Complex.continuous_re
      exact this.mem_nhds (by norm_num : (1 : ℂ) ∈ {s : ℂ | 1/2 < s.re})
    · intro s hs
      exact hFEqOn s hs
  exact fun s hs => (hI s hs).symm

/-- The raw zeta product agrees with the continuation only away from the pole. -/
theorem continued_window_identity_raw_off_pole
    (h : ℝ → ℂ) (Λ : ℝ) (hmass : Mellin h 1 = 0)
    (hcont : ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) - Rminus h Λ s - Rplus h Λ s) :
    ∀ s : ℂ, -(1 / 2 : ℝ) < s.re → s ≠ 1 / 2 →
      Gwin h Λ s = riemannZeta (s + 1 / 2) * Mellin h (s + 1 / 2) -
        Rminus h Λ s - Rplus h Λ s := by
  intro s hs hsp
  rw [hcont s hs, zetaMellinPoleSub_off_pole h hmass]
  · simp [H]
    norm_num
    linarith
  · intro heq
    apply hsp
    apply Complex.ext
    · have hre := congr_arg Complex.re heq
      norm_num at hre ⊢
      linarith
    · have him := congr_arg Complex.im heq
      norm_num at him ⊢
      exact him

/-- At the pole the continued value is the derivative of the Mellin transform. -/
theorem continued_window_identity_pole_value
    (h : ℝ → ℂ) (Λ : ℝ)
    (hcont : ∀ s : ℂ, -(1 / 2 : ℝ) < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + 1 / 2) - Rminus h Λ s - Rplus h Λ s) :
    Gwin h Λ (1 / 2) = deriv (Mellin h) 1 - Rminus h Λ (1 / 2) - Rplus h Λ (1 / 2) := by
  rw [hcont (1 / 2) (by norm_num), show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    zetaMellinPoleSub_value_one]

end EStarMuntzZeroMassContinuation
