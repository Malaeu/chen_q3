import Q3.Proofs.RouteB.D0Mode4JacobiRightTailLimit

/-!
# Monotonicity of the mode-four exact right tail

The finite backward continued fractions are monotone in the shifted spectral
parameter `Lambda`.  Passing to their already-constructed exact limit proves
the same monotonicity for `mode4RightTailLimit` on the pole-free half-line.

This is a source-producing order fact for the exact Schur correction.  It does
not assert existence or indexing of a PSWF eigenvalue, a zero count, a Fourier
eigenrelation, or a CCM rate.
-/

open Filter Set

noncomputable section

private theorem mode4JacobiG_pos_for_tail_monotonicity
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < mode4JacobiG mProject := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  unfold mode4JacobiG
  positivity

/-- On the contraction box, increasing either `Lambda` or the terminal value
increases one exact continued-fraction step. -/
theorem mode4TailMap_mono_lambda_and_terminal
    (mProject q : ℕ) (Λ₁ Λ₂ x₁ x₂ : ℝ)
    (hm : 2 ≤ mProject)
    (hq : 3 ≤ q)
    (hsep :
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ₁ : Λ₁ ≤ 20)
    (hΛ₂ : Λ₂ ≤ 20)
    (hΛ : Λ₁ ≤ Λ₂)
    (hx₁ : x₁ ∈ Set.Icc 0 (1 / 2))
    (hx₂ : x₂ ∈ Set.Icc 0 (1 / 2))
    (hx : x₁ ≤ x₂) :
    mode4TailMap (mode4JacobiG mProject) Λ₁ q x₁ ≤
      mode4TailMap (mode4JacobiG mProject) Λ₂ q x₂ := by
  let G := mode4JacobiG mProject
  let L := mode4JacobiLower G q
  let U := mode4JacobiUpper G q
  let C₁ := mode4JacobiCenter G Λ₁ q
  let C₂ := mode4JacobiCenter G Λ₂ q
  have hG : 0 < G :=
    mode4JacobiG_pos_for_tail_monotonicity mProject hm
  have hL : 0 ≤ L := (mode4JacobiLower_pos G q hG hq).le
  have hU : 0 ≤ U := (mode4JacobiUpper_pos G q hG).le
  have hden₁ : 0 < C₁ - U * x₁ := by
    have hbound := mode4JacobiCenter_sub_upper_mul_lower_bound
      G Λ₁ x₁ q hG hq hsep hΛ₁ hx₁
    nlinarith
  have hden₂ : 0 < C₂ - U * x₂ := by
    have hbound := mode4JacobiCenter_sub_upper_mul_lower_bound
      G Λ₂ x₂ q hG hq hsep hΛ₂ hx₂
    nlinarith
  have hden : C₂ - U * x₂ ≤ C₁ - U * x₁ := by
    have hcenter : C₂ ≤ C₁ := by
      unfold C₁ C₂ mode4JacobiCenter
      linarith
    nlinarith [mul_le_mul_of_nonneg_left hx hU]
  change L / (C₁ - U * x₁) ≤ L / (C₂ - U * x₂)
  exact div_le_div_of_nonneg_left hL hden₂ hden

/-- Every finite backward tail with a fixed admissible terminal value is
monotone in `Lambda` on `(-infinity, 20]`. -/
theorem mode4BackwardTail_monotoneOn_lambda
    (mProject K n : ℕ) (terminal : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hterminal : terminal ∈ Set.Icc 0 (1 / 2)) :
    MonotoneOn
      (fun Λ : ℝ => mode4BackwardTail mProject Λ K n terminal)
      (Set.Iic 20) := by
  induction n generalizing K with
  | zero =>
      intro Λ₁ hΛ₁ Λ₂ hΛ₂ hΛ
      simp [mode4BackwardTail]
  | succ n ih =>
      intro Λ₁ hΛ₁ Λ₂ hΛ₂ hΛ
      have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
      have hsepSucc :
          ∀ q ≥ K + 1,
            (31 / 24 : ℝ) * mode4JacobiG mProject ≤
              mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans (Nat.le_succ K) hq)
      have hx₁ :
          mode4BackwardTail mProject Λ₁ (K + 1) n terminal ∈
            Set.Icc 0 (1 / 2) :=
        (mode4BackwardTail_mapsTo_and_lipschitz
          mProject (K + 1) n Λ₁ hm hKsucc hsepSucc hΛ₁).1 hterminal
      have hx₂ :
          mode4BackwardTail mProject Λ₂ (K + 1) n terminal ∈
            Set.Icc 0 (1 / 2) :=
        (mode4BackwardTail_mapsTo_and_lipschitz
          mProject (K + 1) n Λ₂ hm hKsucc hsepSucc hΛ₂).1 hterminal
      have hx :
          mode4BackwardTail mProject Λ₁ (K + 1) n terminal ≤
            mode4BackwardTail mProject Λ₂ (K + 1) n terminal :=
        ih (K := K + 1) hKsucc hsepSucc hΛ₁ hΛ₂ hΛ
      simpa only [mode4BackwardTail] using
        mode4TailMap_mono_lambda_and_terminal
          mProject K Λ₁ Λ₂
          (mode4BackwardTail mProject Λ₁ (K + 1) n terminal)
          (mode4BackwardTail mProject Λ₂ (K + 1) n terminal)
          hm hK (hsep K le_rfl) hΛ₁ hΛ₂ hΛ hx₁ hx₂ hx

/-- The exact infinite right-tail correction is monotone in the shifted
spectral parameter on the full contraction domain. -/
theorem mode4RightTailLimit_monotoneOn_lambda
    (mProject K : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20) :
    MonotoneOn
      (fun Λ : ℝ => mode4RightTailLimit mProject Λ K)
      (Set.Iic 20) := by
  intro Λ₁ hΛ₁ Λ₂ hΛ₂ hΛ
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (1 / 2) := by norm_num
  have htendsto₁ := mode4BackwardTail_tendsto_rightTailLimit
    mProject K Λ₁ 0 hm hK hsep hΛ₁ hzero
  have htendsto₂ := mode4BackwardTail_tendsto_rightTailLimit
    mProject K Λ₂ 0 hm hK hsep hΛ₂ hzero
  have hfinite :
      (fun n : ℕ => mode4BackwardTail mProject Λ₁ K n 0) ≤ᶠ[atTop]
        (fun n : ℕ => mode4BackwardTail mProject Λ₂ K n 0) :=
    Eventually.of_forall fun n =>
      mode4BackwardTail_monotoneOn_lambda
        mProject K n 0 hm hK hsep hzero hΛ₁ hΛ₂ hΛ
  exact le_of_tendsto_of_tendsto htendsto₁ htendsto₂ hfinite

#print axioms mode4TailMap_mono_lambda_and_terminal
#print axioms mode4BackwardTail_monotoneOn_lambda
#print axioms mode4RightTailLimit_monotoneOn_lambda
