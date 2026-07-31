/-
Provenance source: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/muntz_r6/RequestProject/PoleSubtracted.lean
Provenance SHA-256: 4b20c3d9b505a40ff7c1472798697e36ce34cd4a716c3a9dbbb76d11181aed8d
exported verbatim, imports renamed only
Export date: 2026-07-31
-/

import Mathlib.Analysis.Calculus.DSlope
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.NumberTheory.LSeries.RiemannZeta
import RequestProject.R6Export.Main

open MeasureTheory Set Filter Complex Function
open scoped Topology

namespace EStarMuntzZeroMassContinuation.R6Export

noncomputable def MellinDivOne (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  dslope (Mellin h) 1 w

noncomputable def ZetaResidueFactor (w : ℂ) : ℂ :=
  Function.update (fun z : ℂ => (z - 1) * riemannZeta z) 1 1 w

noncomputable def ZetaMellinPoleSub (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  ZetaResidueFactor w * MellinDivOne h w

theorem Mellin_one_eq_mass (h : ℝ → ℂ) :
    Mellin h 1 = ∫ u in Set.Ioi (0 : ℝ), h u := by
  unfold Mellin
  apply MeasureTheory.integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  simp

theorem Mellin_one_eq_zero_of_zeroMass (h : ℝ → ℂ)
    (hmass : ∫ u in Set.Ioi (0 : ℝ), h u = 0) : Mellin h 1 = 0 := by
  rw [Mellin_one_eq_mass, hmass]

@[simp] theorem MellinDivOne_one (h : ℝ → ℂ) :
    MellinDivOne h 1 = deriv (Mellin h) 1 := by
  simp [MellinDivOne, dslope_same]

theorem MellinDivOne_of_ne (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1) :
    MellinDivOne h w = (Mellin h w - Mellin h 1) / (w - 1) := by
  rw [MellinDivOne, dslope_of_ne _ hw]
  simp [slope, vsub_eq_sub, div_eq_inv_mul]

theorem MellinDivOne_of_ne_of_zero (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1)
    (hzero : Mellin h 1 = 0) :
    MellinDivOne h w = Mellin h w / (w - 1) := by
  rw [MellinDivOne_of_ne h hw, hzero, sub_zero]

theorem MellinDivOne_analyticOn_halfPlane (h : ℝ → ℂ)
    (hM : DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re}) :
    AnalyticOnNhd ℂ (MellinDivOne h) {w : ℂ | 0 < w.re} := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  apply DifferentiableOn.analyticOnNhd _ hopen
  change DifferentiableOn ℂ (dslope (Mellin h) 1) {w : ℂ | 0 < w.re}
  exact (Complex.differentiableOn_dslope (hopen.mem_nhds (by norm_num))).2 hM

@[simp] theorem ZetaResidueFactor_one : ZetaResidueFactor 1 = 1 := by
  simp [ZetaResidueFactor]

theorem ZetaResidueFactor_of_ne {w : ℂ} (hw : w ≠ 1) :
    ZetaResidueFactor w = (w - 1) * riemannZeta w := by
  simp [ZetaResidueFactor, hw]

private theorem zetaResidueFactor_continuousAt_one :
    ContinuousAt ZetaResidueFactor 1 := by
  apply continuousAt_update_same.mpr
  exact riemannZeta_residue_one

private theorem zetaResidueFactor_analyticAt_one :
    AnalyticAt ℂ ZetaResidueFactor 1 := by
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
  · filter_upwards [self_mem_nhdsWithin] with w hw
    have hbase : DifferentiableAt ℂ (fun z : ℂ => (z - 1) * riemannZeta z) w :=
      (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ)))).mul
        (differentiableAt_riemannZeta hw)
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hw] with z hz
    exact ZetaResidueFactor_of_ne hz
  · exact zetaResidueFactor_continuousAt_one

theorem ZetaResidueFactor_analyticOn_halfPlane :
    AnalyticOnNhd ℂ ZetaResidueFactor {w : ℂ | 0 < w.re} := by
  intro w hw
  by_cases heq : w = 1
  · simpa [heq] using zetaResidueFactor_analyticAt_one
  · have hd : DifferentiableOn ℂ ZetaResidueFactor ({1}ᶜ : Set ℂ) := by
      intro z hz
      have hzne : z ≠ 1 := hz
      have hbase : DifferentiableAt ℂ (fun q : ℂ => (q - 1) * riemannZeta q) z :=
        (differentiableAt_id.sub (differentiableAt_const (c := (1 : ℂ)))).mul
          (differentiableAt_riemannZeta hzne)
      apply DifferentiableAt.differentiableWithinAt
      apply hbase.congr_of_eventuallyEq
      filter_upwards [eventually_ne_nhds hzne] with q hq
      exact ZetaResidueFactor_of_ne hq
    exact (hd.analyticOnNhd isOpen_compl_singleton) w heq

 theorem ZetaMellinPoleSub_analyticOn_halfPlane (h : ℝ → ℂ)
    (hM : DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re}) :
    AnalyticOnNhd ℂ (ZetaMellinPoleSub h) {w : ℂ | 0 < w.re} :=
  ZetaResidueFactor_analyticOn_halfPlane.mul (MellinDivOne_analyticOn_halfPlane h hM)

theorem ZetaMellinPoleSub_of_ne_of_zero (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1)
    (hzero : Mellin h 1 = 0) :
    ZetaMellinPoleSub h w = riemannZeta w * Mellin h w := by
  rw [ZetaMellinPoleSub, ZetaResidueFactor_of_ne hw,
    MellinDivOne_of_ne_of_zero h hw hzero]
  field_simp [sub_ne_zero.mpr hw]

@[simp] theorem ZetaMellinPoleSub_one (h : ℝ → ℂ) :
    ZetaMellinPoleSub h 1 = deriv (Mellin h) 1 := by
  simp [ZetaMellinPoleSub]

/-- PL2: the pole-subtracted continuation takes the nonzero derivative value at the pole. -/
theorem pole_value_nonzero_plant (h : ℝ → ℂ)
    (hneg : (deriv (Mellin h) 1).re < 0) :
    ZetaMellinPoleSub h 1 = deriv (Mellin h) 1 ∧ ZetaMellinPoleSub h 1 ≠ 0 := by
  rw [ZetaMellinPoleSub_one]
  exact ⟨rfl, fun hz => by simp [hz] at hneg⟩

/-- PL3a: deleting the residue factor cannot preserve the off-pole equality unless that
factor happens to be one (or the divided Mellin factor vanishes). -/
theorem removing_residue_factor_breaks (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1)
    (hzero : Mellin h 1 = 0) (hM : MellinDivOne h w ≠ 0)
    (hfac : (w - 1) * riemannZeta w ≠ 1) :
    MellinDivOne h w ≠ riemannZeta w * Mellin h w := by
  intro heq
  have hreg := ZetaMellinPoleSub_of_ne_of_zero h hw hzero
  rw [ZetaMellinPoleSub, ZetaResidueFactor_of_ne hw] at hreg
  apply hfac
  apply mul_right_cancel₀ hM
  exact hreg.trans heq.symm |>.trans (one_mul _).symm

/-- PL3b: deleting division by `w-1` changes the off-pole product unless the missing
factor is one (or the raw product vanishes). -/
theorem removing_mellin_division_breaks (h : ℝ → ℂ) {w : ℂ} (hw : w ≠ 1)
    (hraw : riemannZeta w * Mellin h w ≠ 0) (hwfac : w - 1 ≠ 1) :
    ZetaResidueFactor w * Mellin h w ≠ riemannZeta w * Mellin h w := by
  rw [ZetaResidueFactor_of_ne hw]
  intro heq
  apply hwfac
  exact mul_right_cancel₀ hraw (by simpa [mul_assoc] using heq)

private theorem halfPlane_open (c : ℝ) : IsOpen {z : ℂ | c < z.re} :=
  isOpen_lt continuous_const Complex.continuous_re

private theorem halfPlane_preconnected (c : ℝ) : IsPreconnected {z : ℂ | c < z.re} := by
  exact (convex_halfSpace_gt (LinearMap.isLinear Complex.reCLM.toLinearMap) c).isPreconnected

private theorem shift_half_analytic :
    AnalyticOnNhd ℂ (fun s : ℂ => s + (1 : ℂ) / 2) Set.univ :=
  (analyticOnNhd_id.add analyticOnNhd_const)

/-- T5, identity-theorem glue. The hypotheses isolate the analytic facts about the three
integral terms; these are precisely what is needed to reuse the continuation argument. -/
theorem poleSubtracted_continuation
    (h : ℝ → ℂ) (Λ : ℝ)
    (hM : DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re})
    (hzero : Mellin h 1 = 0)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (habs : ∀ s : ℂ, (1 : ℝ) / 2 < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + (1 : ℂ) / 2) - Rminus h Λ s + Rplus h Λ s) :
    ∀ s : ℂ, -(1 : ℝ) / 2 < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + (1 : ℂ) / 2) - Rminus h Λ s + Rplus h Λ s := by
  let U : Set ℂ := {s : ℂ | -(1 : ℝ) / 2 < s.re}
  let F : ℂ → ℂ := fun s => ZetaMellinPoleSub h (s + (1 : ℂ) / 2) -
    Rminus h Λ s + Rplus h Λ s
  have hshift : AnalyticOnNhd ℂ (fun s : ℂ => s + (1 : ℂ) / 2) U :=
    shift_half_analytic.mono (Set.subset_univ U)
  have hmap : Set.MapsTo (fun s : ℂ => s + (1 : ℂ) / 2) U {w : ℂ | 0 < w.re} := by
    intro s hs
    dsimp [U] at hs
    norm_num at hs ⊢
    linarith
  have hzshift : AnalyticOnNhd ℂ (fun s : ℂ => ZetaMellinPoleSub h (s + (1 : ℂ) / 2)) U := by
    simpa [Function.comp_def] using
      (ZetaMellinPoleSub_analyticOn_halfPlane h hM).comp hshift hmap
  have hF : AnalyticOnNhd ℂ F U := hzshift.sub hRm |>.add hRp
  have hone : (1 : ℂ) ∈ U := by norm_num [U]
  have hevent : Gwin h Λ =ᶠ[𝓝 (1 : ℂ)] F := by
    filter_upwards [(halfPlane_open ((1 : ℝ) / 2)).mem_nhds (by norm_num : (1 : ℝ) / 2 < (1 : ℂ).re)] with s hs
    exact habs s hs
  have heq : Set.EqOn (Gwin h Λ) F U :=
    hG.eqOn_of_preconnected_of_eventuallyEq hF (halfPlane_preconnected (-(1 : ℝ) / 2)) hone hevent
  intro s hs
  exact heq (show s ∈ U from hs)

/-- Away from the pole, T5 is the ordinary zeta--Mellin formula. -/
theorem poleSubtracted_continuation_punctured
    (h : ℝ → ℂ) (Λ : ℝ)
    (hM : DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re})
    (hzero : Mellin h 1 = 0)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (habs : ∀ s : ℂ, (1 : ℝ) / 2 < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + (1 : ℂ) / 2) - Rminus h Λ s + Rplus h Λ s)
    (s : ℂ) (hs : -(1 : ℝ) / 2 < s.re) (hsp : s ≠ (1 : ℂ) / 2) :
    Gwin h Λ s = riemannZeta (s + (1 : ℂ) / 2) * Mellin h (s + (1 : ℂ) / 2) -
      Rminus h Λ s + Rplus h Λ s := by
  rw [poleSubtracted_continuation h Λ hM hzero hG hRm hRp habs s hs,
    ZetaMellinPoleSub_of_ne_of_zero h (by intro heq; apply hsp; linear_combination heq) hzero]

/-- The continuation's value at the removed pole. -/
theorem poleSubtracted_continuation_pole_value
    (h : ℝ → ℂ) (Λ : ℝ)
    (hM : DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re})
    (hzero : Mellin h 1 = 0)
    (hG : AnalyticOnNhd ℂ (Gwin h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRm : AnalyticOnNhd ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (hRp : AnalyticOnNhd ℂ (Rplus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re})
    (habs : ∀ s : ℂ, (1 : ℝ) / 2 < s.re →
      Gwin h Λ s = ZetaMellinPoleSub h (s + (1 : ℂ) / 2) - Rminus h Λ s + Rplus h Λ s) :
    Gwin h Λ ((1 : ℂ) / 2) = deriv (Mellin h) 1 - Rminus h Λ ((1 : ℂ) / 2) +
      Rplus h Λ ((1 : ℂ) / 2) := by
  have hc := poleSubtracted_continuation h Λ hM hzero hG hRm hRp habs
    ((1 : ℂ) / 2) (by norm_num)
  rw [show (1 : ℂ) / 2 + 1 / 2 = 1 by norm_num, ZetaMellinPoleSub_one] at hc
  exact hc

end EStarMuntzZeroMassContinuation.R6Export
