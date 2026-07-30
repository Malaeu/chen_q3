import RequestProject.WindowAnalyticity

open MeasureTheory Set Filter Complex Asymptotics
open scoped Topology BigOperators

namespace EStarMuntzZeroMassContinuation

/-- The concrete right tail is entire. -/
theorem Rplus_differentiable
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h) (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    Differentiable ℂ (Rplus h Λ) := by
  -- Since h is supported in [a, b], Estar h u = 0 for u > b
  -- So Rplus h Λ is an integral over a bounded interval, hence entire
  intro s
  -- Rewrite Rplus as integral over (Λ, b] ∩ (Λ, ∞)
  have hsupp' : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0 := by
    intro v hv
    apply hsupp
    intro hvab
    apply hv
    exact ⟨ha.le.trans hvab.1, hvab.2⟩
  -- For u > b, Estar h u = 0
  have hEstar_zero : ∀ u, b < u → Estar h u = 0 := fun u hu =>
    Estar_eq_zero_of_gt h b u (by linarith) hsupp' hu
  -- Define f as indicator of Estar h on (Λ, b]
  let f : ℝ → ℂ := Set.Ioc Λ b |>.indicator (Estar h)
  have hfmeas : Measurable f :=
    (Estar_measurable h a b ha hsupp hlip.continuous.measurable).indicator measurableSet_Ioc
  -- f is locally integrable on (0, ∞)
  have hlocal0 := Estar_locallyIntegrableOn_Ioi h a b ha hab K hsupp hlip
  have hlocal : LocallyIntegrableOn f (Set.Ioi 0) := by
    apply hlocal0.mono hfmeas.aestronglyMeasurable
    filter_upwards with u
    simp [f, Set.indicator_apply]
    split_ifs <;> simp
  -- f =O[atTop] x^(-A) for any A (since f = 0 for x > b)
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have htop : ∀ A : ℝ, f =O[atTop] (fun x : ℝ => x ^ (-A)) := by
    intro A
    apply (isBigO_zero (fun x : ℝ => x ^ (-A)) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm
      simp [f, not_and_of_not_right _ (by linarith : ¬ x ≤ b)]
    · rfl
  -- f =O[𝓝[>] 0] x^(-B) for any B (since f = 0 near 0 for x ≤ Λ)
  have hbot : ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-B)) := by
    intro B
    apply (isBigO_zero (fun x : ℝ => x ^ (-B)) (𝓝[>] (0 : ℝ))).congr'
    · filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hΛpos)] with x hx
      symm
      simp [f, (by linarith : ¬ Λ < x)]
    · rfl
  -- Rplus h Λ = mellin f
  have heq : Rplus h Λ = mellin f := by
    funext s
    unfold Rplus mellin
    simp_rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards with u
    simp only [f, Set.indicator_apply]
    by_cases huLambda : Λ < u
    · by_cases hu0 : 0 < u
      · by_cases huIoc : u ∈ Set.Ioc Λ b
        · -- Λ < u, 0 < u, u ∈ Ioc Λ b
          simp [huLambda, hu0, huIoc, smul_eq_mul, mul_comm]
        · -- Λ < u, 0 < u, u ∉ Ioc Λ b
          -- u > Λ and u ∉ (Λ, b] means u > b, so Estar h u = 0
          have hu_gt_b : b < u := by
            simp only [Set.mem_Ioc] at huIoc
            push_neg at huIoc
            tauto
          rw [hEstar_zero u hu_gt_b]
          simp
      · -- Λ < u, ¬(0 < u) → contradiction since Λ ≥ 1
        linarith
    · -- ¬(Λ < u), so LHS = 0
      simp [huLambda]
  rw [heq]
  exact mellin_differentiableAt_of_isBigO_rpow hlocal (htop (s.re + 1)) (by linarith)
    (hbot (s.re - 1)) (by linarith)

/-- The zero-mass left tail is holomorphic on `re s > -1/2`. -/
theorem Rminus_differentiableOn_halfPlane
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) :
    DifferentiableOn ℂ (Rminus h Λ) {s : ℂ | -(1 : ℝ) / 2 < s.re} := by
  sorry

end EStarMuntzZeroMassContinuation
