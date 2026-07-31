/-
Provenance source: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/muntz_r6/RequestProject/WindowAnalyticity.lean
Provenance SHA-256: e427a3d579a03d9369c35eaa042bf3ac18d4429f6799ecf9ca22ebd4fa86ea71
exported verbatim, imports renamed only
Export date: 2026-07-31
-/

import RequestProject.R6Export.IntegralAnalyticity

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation.R6Export

/-- The concrete compact window integral is entire. -/
theorem Gwin_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Gwin h Λ) := by
  let f : ℝ → ℂ := Set.Ioo (Λ⁻¹) Λ |>.indicator (Estar h)
  have hfmeas : Measurable f :=
    (Estar_measurable h a b ha hsupp hlip.continuous.measurable).indicator measurableSet_Ioo
  have hlocal0 := Estar_locallyIntegrableOn_Ioi h a b ha hab K hsupp hlip
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply hlocal0.mono hfmeas.aestronglyMeasurable
    filter_upwards with u
    simp [f, Set.indicator_apply]
    split_ifs <;> simp
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop Λ] with x hx
      symm
      simp [f, not_lt_of_ge hx.le]
    · rfl
  have hbot : ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) := by
    intro B
    apply (isBigO_zero (fun x : ℝ => x ^ (-B)) (𝓝[>] (0 : ℝ))).congr'
    · have hInv : 0 < Λ⁻¹ := inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ)
      filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hInv)] with x hx
      symm
      simp [f, not_lt_of_ge hx.le]
    · rfl
  have heq : Gwin h Λ = mellin f := by
    funext s
    unfold Gwin mellin
    rw [← integral_indicator measurableSet_Ioo,
      ← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases hwin : u ∈ Set.Ioo Λ⁻¹ Λ
    · have hpos : u ∈ Set.Ioi (0 : ℝ) :=
        lt_of_lt_of_le (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ)) hwin.1.le
      simp [hwin, hpos, mul_comm]
    · simp [hwin]
  rw [heq]
  intro s
  exact mellin_differentiableAt_of_isBigO_rpow hlocal (htop (s.re + 1)) (by linarith)
    (hbot (s.re - 1)) (by linarith)

end EStarMuntzZeroMassContinuation.R6Export
