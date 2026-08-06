/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MellinCompactSupportAnalyticity.lean
Source SHA-256: 743e7cecf175a0be8c94d844c334ab66bfa5858696e6269a743b17ce0edfe148
Body copied byte-for-byte; import path rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.Core
open Set Filter MeasureTheory Complex Asymptotics
open scoped Topology
namespace EStarMuntzZeroMassContinuation
theorem mellin_compactSupport_analyticOnNhd
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hmeas : Measurable h)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) b → h u = 0)
    (hlip : LipschitzOnWith K h (Set.Ico 0 b)) :
    AnalyticOnNhd ℂ
      (fun s ↦ ∫ u in Set.Ioi (0 : ℝ), h u * (u : ℂ) ^ (s - 1))
      {s : ℂ | 0 < s.re} := by
  let C : ℝ := ‖h 0‖ + (K : ℝ) * |b|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hbound_Ico : ∀ u ∈ Set.Ico (0 : ℝ) b, ‖h u‖ ≤ C := by
    intro u hu
    have hb : 0 < b := lt_of_le_of_lt hu.1 hu.2
    have hdist := hlip.dist_le_mul u hu 0 ⟨le_rfl, hb⟩
    calc
      ‖h u‖ ≤ dist (h u) (h 0) + ‖h 0‖ := by
        rw [dist_eq_norm]; exact norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * dist u 0 + ‖h 0‖ := by gcongr
      _ ≤ (K : ℝ) * |b| + ‖h 0‖ := by
        gcongr
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1, abs_of_pos hb]
        exact hu.2.le
      _ = C := by simp [C, add_comm]
  have hbound_ae : ∀ᵐ u : ℝ, ‖h u‖ ≤ C := by
    have hb_ae : ∀ᵐ u : ℝ, u ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hb_ae] with u hub
    by_cases hu : u ∈ Set.Icc (0 : ℝ) b
    · exact hbound_Ico u ⟨hu.1, lt_of_le_of_ne hu.2 hub⟩
    · simpa [hsupp u hu] using hC
  have hlocal : LocallyIntegrableOn h (Set.Ioi 0) := by
    apply (locallyIntegrableOn_const C).mono hmeas.aestronglyMeasurable
    filter_upwards [hbound_ae] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hu
  have htop : ∀ A : ℝ, h =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm; exact hsupp x (by simp only [Set.mem_Icc, not_and_or]; exact Or.inr (not_le.mpr hx))
    · rfl
  have hbot : h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    by_cases hb : 0 < b
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hb)] with u hu hub
      have hu' : u ∈ Set.Ico (0 : ℝ) b := ⟨hu.le, hub⟩
      simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hbound_Ico u hu'
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hout : u ∉ Set.Icc (0 : ℝ) b := by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr (lt_of_le_of_lt (not_lt.mp hb) hu))
      simpa [hsupp u hout] using hC
  have heq :
      (fun s ↦ ∫ u in Set.Ioi (0 : ℝ), h u * (u : ℂ) ^ (s - 1)) = mellin h := by
    funext s
    unfold mellin
    apply integral_congr_ae
    filter_upwards with u
    simp only [smul_eq_mul]
    rw [mul_comm]
  have hdiff : DifferentiableOn ℂ (mellin h) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (mellin_differentiableAt_of_isBigO_rpow hlocal
      (htop (s.re + 1)) (by linarith) hbot hs).differentiableWithinAt
  rw [heq]
  exact hdiff.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)
end EStarMuntzZeroMassContinuation
