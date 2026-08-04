import Q3.Proofs.RouteB.D0Mode4JacobiTailContraction

/-!
# The mode-four infinite right tail

This file constructs the terminal-independent limit of the contracting right-tail compositions.
The positive tail variable is the unphased ratio `a_q / a_(q-1)`, equivalently the negative of
the project-phased ratio `b_q / b_(q-1)`.  Nothing here constructs or selects an eigenvalue,
an eigenrow, a finite truncation, or a PSWF.
-/

open Filter Set Topology

noncomputable section

/-- The finite composition `F_K ∘ F_(K+1) ∘ ... ∘ F_(K+n-1)`. -/
def mode4BackwardTail
    (mProject : ℕ) (Λ : ℝ) (K : ℕ) :
    ℕ → ℝ → ℝ
  | 0, x => x
  | n + 1, x =>
      mode4TailMap (mode4JacobiG mProject) Λ K
        (mode4BackwardTail mProject Λ (K + 1) n x)

theorem mode4BackwardTail_mapsTo_and_lipschitz
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
    Set.MapsTo
        (mode4BackwardTail mProject Λ K n)
        (Set.Icc 0 (1 / 2))
        (Set.Icc 0 (1 / 2)) ∧
      LipschitzOnWith
        ((3 / 16 : NNReal) ^ n)
        (mode4BackwardTail mProject Λ K n)
        (Set.Icc 0 (1 / 2)) := by
  induction n generalizing K with
  | zero =>
      constructor
      · intro x hx
        simpa [mode4BackwardTail] using hx
      · simpa [mode4BackwardTail] using
          (LipschitzWith.id.lipschitzOnWith :
            LipschitzOnWith (1 : NNReal) (id : ℝ → ℝ) (Set.Icc 0 (1 / 2)))
  | succ n ih =>
      have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
      have hsepSucc : ∀ q ≥ K + 1,
          (31 / 24 : ℝ) * mode4JacobiG mProject ≤
            mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_succ K) hq)
      have hinner := ih (K := K + 1) hKsucc hsepSucc
      have houter := mode4TailMap_mapsTo_and_contracts
        mProject K Λ hm hK (hsep K le_rfl) hΛ
      constructor
      · exact houter.1.comp hinner.1
      · have hcomp := houter.2.comp hinner.2 hinner.1
        simpa [mode4BackwardTail, Function.comp_def, pow_succ, mul_comm] using hcomp

private theorem mode4BackwardTail_succ_eq
    (mProject K n : ℕ) (Λ terminal : ℝ) :
    mode4BackwardTail mProject Λ K (n + 1) terminal =
      mode4BackwardTail mProject Λ K n
        (mode4TailMap (mode4JacobiG mProject) Λ (K + n) terminal) := by
  induction n generalizing K with
  | zero => simp [mode4BackwardTail]
  | succ n ih =>
      change
        mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4BackwardTail mProject Λ (K + 1) (n + 1) terminal) =
          mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4BackwardTail mProject Λ (K + 1) n
              (mode4TailMap (mode4JacobiG mProject) Λ (K + (n + 1)) terminal))
      apply congrArg (mode4TailMap (mode4JacobiG mProject) Λ K)
      rw [ih (K + 1)]
      congr 1
      simp [Nat.add_comm, Nat.add_left_comm]

private theorem mode4BackwardTail_dist_le
    (mProject K n : ℕ)
    (Λ x y : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hx : x ∈ Set.Icc 0 (1 / 2))
    (hy : y ∈ Set.Icc 0 (1 / 2)) :
    dist (mode4BackwardTail mProject Λ K n x)
        (mode4BackwardTail mProject Λ K n y) ≤
      ((3 / 16 : ℝ) ^ n) * dist x y := by
  have hlip :=
    (mode4BackwardTail_mapsTo_and_lipschitz
      mProject K n Λ hm hK hsep hΛ).2
  simpa using hlip.dist_le_mul x hx y hy

theorem mode4BackwardTail_cauchy
    (mProject K : ℕ)
    (Λ terminal : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hterminal : terminal ∈ Set.Icc 0 (1 / 2)) :
    CauchySeq
      (fun n =>
        mode4BackwardTail mProject Λ K n terminal) := by
  refine cauchySeq_of_le_geometric (3 / 16 : ℝ) (1 / 2 : ℝ) (by norm_num) ?_
  intro n
  rw [mode4BackwardTail_succ_eq]
  rw [dist_comm]
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKthree : 3 ≤ K + n := le_trans hK hKn
  have htail := mode4TailMap_mapsTo_and_contracts
    mProject (K + n) Λ hm hKthree (hsep (K + n) hKn) hΛ
  have htailTerminal :
      mode4TailMap (mode4JacobiG mProject) Λ (K + n) terminal ∈
        Set.Icc 0 (1 / 2) := htail.1 hterminal
  have hterminalDiameter :
      dist (mode4TailMap (mode4JacobiG mProject) Λ (K + n) terminal)
          terminal ≤ (1 / 2 : ℝ) := by
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith [htailTerminal.1, htailTerminal.2,
      hterminal.1, hterminal.2]
  calc
    dist
          (mode4BackwardTail mProject Λ K n
            (mode4TailMap (mode4JacobiG mProject) Λ (K + n) terminal))
          (mode4BackwardTail mProject Λ K n terminal) ≤
        (3 / 16 : ℝ) ^ n *
          dist (mode4TailMap (mode4JacobiG mProject) Λ (K + n) terminal)
            terminal :=
      mode4BackwardTail_dist_le mProject K n Λ _ _ hm hK hsep hΛ
        htailTerminal hterminal
    _ ≤ (3 / 16 : ℝ) ^ n * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_left hterminalDiameter (by positivity)
    _ = (1 / 2 : ℝ) * (3 / 16 : ℝ) ^ n := by ring

noncomputable def mode4RightTailLimit
    (mProject : ℕ) (Λ : ℝ) (K : ℕ) : ℝ :=
  limUnder atTop
    (fun n =>
      mode4BackwardTail mProject Λ K n 0)

theorem mode4BackwardTail_tendsto_rightTailLimit
    (mProject K : ℕ)
    (Λ terminal : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hterminal : terminal ∈ Set.Icc 0 (1 / 2)) :
    Tendsto
      (fun n =>
        mode4BackwardTail mProject Λ K n terminal)
      atTop
      (𝓝 (mode4RightTailLimit mProject Λ K)) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hzeroCauchy := mode4BackwardTail_cauchy
    mProject K Λ 0 hm hK hsep hΛ hzero
  have hzeroTendsto :
      Tendsto
        (fun n => mode4BackwardTail mProject Λ K n 0)
        atTop
        (𝓝 (mode4RightTailLimit mProject Λ K)) := by
    simpa [mode4RightTailLimit] using hzeroCauchy.tendsto_limUnder
  have hdistTendsto :
      Tendsto
        (fun n =>
          dist (mode4BackwardTail mProject Λ K n 0)
            (mode4BackwardTail mProject Λ K n terminal))
        atTop
        (𝓝 0) := by
    refine squeeze_zero
      (g := fun n => (3 / 16 : ℝ) ^ n * dist (0 : ℝ) terminal)
      (fun _ => dist_nonneg) (fun n => ?_) ?_
    · exact mode4BackwardTail_dist_le
        mProject K n Λ 0 terminal hm hK hsep hΛ hzero hterminal
    · have hpow :
          Tendsto (fun n : ℕ => (3 / 16 : ℝ) ^ n) atTop (𝓝 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
      simpa using hpow.mul_const (dist (0 : ℝ) terminal)
  exact hzeroTendsto.congr_dist hdistTendsto

theorem mode4RightTailLimit_mem_Icc
    (mProject K : ℕ)
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
    mode4RightTailLimit mProject Λ K ∈
      Set.Icc 0 (1 / 2) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have htendsto := mode4BackwardTail_tendsto_rightTailLimit
    mProject K Λ 0 hm hK hsep hΛ hzero
  apply isClosed_Icc.mem_of_tendsto htendsto
  exact Eventually.of_forall fun n =>
    (mode4BackwardTail_mapsTo_and_lipschitz
      mProject K n Λ hm hK hsep hΛ).1 hzero

theorem mode4RightTailLimit_eq_tailMap_succ
    (mProject K : ℕ)
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
      mode4TailMap
        (mode4JacobiG mProject) Λ K
        (mode4RightTailLimit mProject Λ (K + 1)) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
  have hsepSucc : ∀ q ≥ K + 1,
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
    intro q hq
    exact hsep q (le_trans (Nat.le_succ K) hq)
  have hlimK := mode4BackwardTail_tendsto_rightTailLimit
    mProject K Λ 0 hm hK hsep hΛ hzero
  have hlimSucc := mode4BackwardTail_tendsto_rightTailLimit
    mProject (K + 1) Λ 0 hm hKsucc hsepSucc hΛ hzero
  have hmemSucc := mode4RightTailLimit_mem_Icc
    mProject (K + 1) Λ hm hKsucc hsepSucc hΛ
  have houter := mode4TailMap_mapsTo_and_contracts
    mProject K Λ hm hK (hsep K le_rfl) hΛ
  have htermsSucc : ∀ n,
      mode4BackwardTail mProject Λ (K + 1) n 0 ∈ Set.Icc 0 (1 / 2) := by
    intro n
    exact (mode4BackwardTail_mapsTo_and_lipschitz
      mProject (K + 1) n Λ hm hKsucc hsepSucc hΛ).1 hzero
  have hwithin :
      Tendsto
        (fun n => mode4BackwardTail mProject Λ (K + 1) n 0)
        atTop
        (𝓝[Set.Icc 0 (1 / 2)]
          (mode4RightTailLimit mProject Λ (K + 1))) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨hlimSucc, Eventually.of_forall htermsSucc⟩
  have hmapTendsto :
      Tendsto
        (fun n =>
          mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4BackwardTail mProject Λ (K + 1) n 0))
        atTop
        (𝓝
          (mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4RightTailLimit mProject Λ (K + 1)))) :=
    (houter.2.continuousOn
      (mode4RightTailLimit mProject Λ (K + 1)) hmemSucc).tendsto.comp hwithin
  have hshift :
      Tendsto
        (fun n => mode4BackwardTail mProject Λ K (n + 1) 0)
        atTop
        (𝓝 (mode4RightTailLimit mProject Λ K)) :=
    (tendsto_add_atTop_iff_nat 1).mpr hlimK
  have hshiftMap :
      Tendsto
        (fun n => mode4BackwardTail mProject Λ K (n + 1) 0)
        atTop
        (𝓝
          (mode4TailMap (mode4JacobiG mProject) Λ K
            (mode4RightTailLimit mProject Λ (K + 1)))) := by
    simpa only [mode4BackwardTail] using hmapTendsto
  exact tendsto_nhds_unique hshift hshiftMap

#print axioms mode4BackwardTail_mapsTo_and_lipschitz
#print axioms mode4BackwardTail_cauchy
#print axioms mode4BackwardTail_tendsto_rightTailLimit
#print axioms mode4RightTailLimit_eq_tailMap_succ
