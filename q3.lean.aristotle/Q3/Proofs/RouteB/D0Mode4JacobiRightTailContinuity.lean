import Q3.Proofs.RouteB.D0Mode4JacobiRightTailLimit

/-!
# Continuity in the spectral parameter of the mode-four right tail

The finite backward tails are continuous in `Λ` on the pole-free half-line `Λ ≤ 20`.
Their uniform geometric error then transfers continuity to the infinite right-tail limit.
This file does not construct or select a spectral value, eigenrow, finite truncation, or PSWF.
-/

open Filter Set Topology

noncomputable section

private theorem mode4JacobiG_pos_for_continuity
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < mode4JacobiG mProject := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  unfold mode4JacobiG
  positivity

private theorem mode4TailMap_comp_continuousOn_lambda
    (mProject q : ℕ)
    (x : ℝ → ℝ)
    (hm : 2 ≤ mProject)
    (hq : 3 ≤ q)
    (hsep :
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q *
            (mode4JacobiIndex q + 1) -
          20)
    (hxContinuous : ContinuousOn x (Set.Iic 20))
    (hxMaps : Set.MapsTo x (Set.Iic 20) (Set.Icc 0 (1 / 2))) :
    ContinuousOn
      (fun Λ : ℝ =>
        mode4TailMap (mode4JacobiG mProject) Λ q (x Λ))
      (Set.Iic 20) := by
  have hG : 0 < mode4JacobiG mProject :=
    mode4JacobiG_pos_for_continuity mProject hm
  unfold mode4TailMap
  apply continuousOn_const.div
  · unfold mode4JacobiCenter
    fun_prop
  · intro Λ hΛ
    have hdenLower := mode4JacobiCenter_sub_upper_mul_lower_bound
      (mode4JacobiG mProject) Λ (x Λ) q hG hq hsep hΛ (hxMaps hΛ)
    nlinarith

theorem mode4BackwardTail_continuousOn_lambda
    (mProject K n : ℕ)
    (terminal : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hterminal : terminal ∈ Set.Icc 0 (1 / 2)) :
    ContinuousOn
      (fun Λ : ℝ =>
        mode4BackwardTail mProject Λ K n terminal)
      (Set.Iic 20) := by
  induction n generalizing K with
  | zero =>
      simpa [mode4BackwardTail] using
        (continuousOn_const : ContinuousOn (fun _ : ℝ => terminal) (Set.Iic 20))
  | succ n ih =>
      have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
      have hsepSucc : ∀ q ≥ K + 1,
          (31 / 24 : ℝ) * mode4JacobiG mProject ≤
            mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_succ K) hq)
      have hinnerContinuous :
          ContinuousOn
            (fun Λ : ℝ =>
              mode4BackwardTail mProject Λ (K + 1) n terminal)
            (Set.Iic 20) :=
        ih (K := K + 1) hKsucc hsepSucc
      have hinnerMaps :
          Set.MapsTo
            (fun Λ : ℝ =>
              mode4BackwardTail mProject Λ (K + 1) n terminal)
            (Set.Iic 20) (Set.Icc 0 (1 / 2)) := by
        intro Λ hΛ
        exact (mode4BackwardTail_mapsTo_and_lipschitz
          mProject (K + 1) n Λ hm hKsucc hsepSucc hΛ).1 hterminal
      simpa only [mode4BackwardTail] using
        mode4TailMap_comp_continuousOn_lambda
          mProject K
          (fun Λ : ℝ =>
            mode4BackwardTail mProject Λ (K + 1) n terminal)
          hm hK (hsep K le_rfl) hinnerContinuous hinnerMaps

theorem mode4RightTailLimit_eq_backwardTail_shift
    (mProject K n : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4RightTailLimit mProject Λ K =
      mode4BackwardTail mProject Λ K n
        (mode4RightTailLimit mProject Λ (K + n)) := by
  induction n generalizing K with
  | zero => simp [mode4BackwardTail]
  | succ n ih =>
      have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
      have hsepSucc : ∀ q ≥ K + 1,
          (31 / 24 : ℝ) * mode4JacobiG mProject ≤
            mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_succ K) hq)
      rw [mode4RightTailLimit_eq_tailMap_succ
        mProject K Λ hm hK hsep hΛ]
      change
        mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4RightTailLimit mProject Λ (K + 1)) =
          mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4BackwardTail mProject Λ (K + 1) n
              (mode4RightTailLimit mProject Λ (K + (n + 1))))
      apply congrArg (mode4TailMap (mode4JacobiG mProject) Λ K)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (K := K + 1) hKsucc hsepSucc

theorem mode4BackwardTail_zero_dist_rightTailLimit_le
    (mProject K n : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    dist
        (mode4BackwardTail mProject Λ K n 0)
        (mode4RightTailLimit mProject Λ K) ≤
      (1 / 2 : ℝ) * (3 / 16 : ℝ) ^ n := by
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKshift : 3 ≤ K + n := le_trans hK hKn
  have hsepShift : ∀ q ≥ K + n,
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
    intro q hq
    exact hsep q (le_trans hKn hq)
  have htailMem := mode4RightTailLimit_mem_Icc
    mProject (K + n) Λ hm hKshift hsepShift hΛ
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hdiameter :
      dist (0 : ℝ) (mode4RightTailLimit mProject Λ (K + n)) ≤
        (1 / 2 : ℝ) := by
    rw [Real.dist_eq, abs_sub_comm, sub_zero, abs_of_nonneg htailMem.1]
    exact htailMem.2
  rw [mode4RightTailLimit_eq_backwardTail_shift
    mProject K n Λ hm hK hsep hΛ]
  calc
    dist
          (mode4BackwardTail mProject Λ K n 0)
          (mode4BackwardTail mProject Λ K n
            (mode4RightTailLimit mProject Λ (K + n))) ≤
        (3 / 16 : ℝ) ^ n *
          dist (0 : ℝ) (mode4RightTailLimit mProject Λ (K + n)) := by
      simpa using
        (mode4BackwardTail_mapsTo_and_lipschitz
          mProject K n Λ hm hK hsep hΛ).2.dist_le_mul
            0 hzero
            (mode4RightTailLimit mProject Λ (K + n)) htailMem
    _ ≤ (3 / 16 : ℝ) ^ n * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hdiameter (by positivity)
    _ = (1 / 2 : ℝ) * (3 / 16 : ℝ) ^ n := by ring

theorem mode4RightTailLimit_continuousOn_lambda
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20) :
    ContinuousOn
      (fun Λ : ℝ =>
        mode4RightTailLimit mProject Λ K)
      (Set.Iic 20) := by
  apply continuousOn_of_uniform_approx_of_continuousOn
  intro u hu
  rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hεu⟩
  have hpow :
      Tendsto
        (fun n : ℕ => (1 / 2 : ℝ) * (3 / 16 : ℝ) ^ n)
        atTop (𝓝 0) := by
    have hgeom :
        Tendsto (fun n : ℕ => (3 / 16 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa using tendsto_const_nhds.mul hgeom
  have heventually :
      ∀ᶠ n : ℕ in atTop, (1 / 2 : ℝ) * (3 / 16 : ℝ) ^ n < ε :=
    hpow.eventually (Iio_mem_nhds hε)
  obtain ⟨n, hn⟩ := heventually.exists
  refine ⟨
    (fun Λ : ℝ => mode4BackwardTail mProject Λ K n 0),
    mode4BackwardTail_continuousOn_lambda
      mProject K n 0 hm hK hsep (by norm_num), ?_⟩
  intro Λ hΛ
  apply hεu
  rw [dist_comm]
  exact lt_of_le_of_lt
    (mode4BackwardTail_zero_dist_rightTailLimit_le
      mProject K n Λ hm hK hsep hΛ)
    hn

#print axioms mode4BackwardTail_continuousOn_lambda
#print axioms mode4RightTailLimit_eq_backwardTail_shift
#print axioms mode4BackwardTail_zero_dist_rightTailLimit_le
#print axioms mode4RightTailLimit_continuousOn_lambda
