import RequestProject.PoleSubtracted

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology

namespace EStarMuntzZeroMassContinuation

/-- The concrete compactly-supported Lipschitz Mellin transform is holomorphic on the
right half-plane. -/
theorem Mellin_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) :
    DifferentiableOn ℂ (Mellin h) {w : ℂ | 0 < w.re} := by
  have hlocal : LocallyIntegrableOn h (Ioi 0) :=
    hlip.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have htop : ∀ A : ℝ, h =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm
      exact hsupp x (by
        simp only [mem_Icc, not_and_or]
        exact Or.inr (not_le_of_gt hx))
    · rfl
  have hbot : h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    apply (isBigO_zero (fun x : ℝ => x ^ (-(0 : ℝ))) (𝓝[>] (0 : ℝ))).congr'
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds ha)] with x hx
      symm
      exact hsupp x (by
        simp only [mem_Icc, not_and_or]
        exact Or.inl (not_le_of_gt hx))
    · rfl
  rw [show Mellin h = mellin h by
    funext s
    unfold Mellin mellin
    apply integral_congr_ae
    filter_upwards with u
    simp [mul_comm]]
  intro w hw
  exact (mellin_differentiableAt_of_isBigO_rpow hlocal (htop (w.re + 1)) (by linarith)
    hbot hw).differentiableWithinAt

end EStarMuntzZeroMassContinuation
