import Q3.Proofs.RouteB.D0Mode4JacobiRightTailContinuity

/-!
# The mode-four left continuant and root function

This file constructs the finite left-boundary solution and the division-free residual which
matches it to the infinite positive right tail.  It does not prove that the residual has a root,
select a spectral branch, construct an eigenrow, or identify a PSWF source mode.
-/

open Set Topology

noncomputable section

/-- `(a_(q-1), a_q)` for the left-boundary solution normalized by
`a_(-1)=0`, `a_0=1`. -/
noncomputable def mode4LeftPair
    (G Λ : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 1)
  | q + 1 =>
      let y := mode4LeftPair G Λ q
      (y.2,
        (mode4JacobiCenter G Λ q * y.2 -
          mode4JacobiLower G q * y.1) /
          mode4JacobiUpper G q)

/-- Division-free matching of the left solution to the infinite positive
right tail at index `K`. -/
noncomputable def mode4RootFunction
    (mProject K : ℕ) (Λ : ℝ) : ℝ :=
  let y :=
    mode4LeftPair (mode4JacobiG mProject) Λ K
  y.2 -
    mode4RightTailLimit mProject Λ K * y.1

private theorem mode4JacobiG_pos_for_leftPair
    (mProject : ℕ) (hm : 2 ≤ mProject) :
    0 < mode4JacobiG mProject := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) hm)
  unfold mode4JacobiG
  positivity

theorem mode4LeftPair_succ_transfer
    (mProject q : ℕ)
    (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    let G := mode4JacobiG mProject
    let yq := mode4LeftPair G Λ q
    let yq1 := mode4LeftPair G Λ (q + 1)
    yq1.1 = yq.2 ∧
      mode4JacobiUpper G q * yq1.2 =
        mode4JacobiCenter G Λ q * yq.2 -
          mode4JacobiLower G q * yq.1 := by
  have hG : 0 < mode4JacobiG mProject :=
    mode4JacobiG_pos_for_leftPair mProject hm
  have hUne : mode4JacobiUpper (mode4JacobiG mProject) q ≠ 0 :=
    (mode4JacobiUpper_pos (mode4JacobiG mProject) q hG).ne'
  simp only [mode4LeftPair]
  constructor
  · trivial
  · exact mul_div_cancel₀ _ hUne

theorem mode4LeftPair_continuous_lambda
    (mProject q : ℕ)
    (hm : 2 ≤ mProject) :
    Continuous
      (fun Λ : ℝ =>
        mode4LeftPair
          (mode4JacobiG mProject) Λ q) := by
  have hG : 0 < mode4JacobiG mProject :=
    mode4JacobiG_pos_for_leftPair mProject hm
  induction q with
  | zero =>
      simpa [mode4LeftPair] using
        (continuous_const : Continuous (fun _ : ℝ => ((0 : ℝ), (1 : ℝ))))
  | succ q ih =>
      have hUne : mode4JacobiUpper (mode4JacobiG mProject) q ≠ 0 :=
        (mode4JacobiUpper_pos (mode4JacobiG mProject) q hG).ne'
      have hnum : Continuous
          (fun Λ : ℝ =>
            mode4JacobiCenter (mode4JacobiG mProject) Λ q *
                (mode4LeftPair (mode4JacobiG mProject) Λ q).2 -
              mode4JacobiLower (mode4JacobiG mProject) q *
                (mode4LeftPair (mode4JacobiG mProject) Λ q).1) := by
        unfold mode4JacobiCenter
        fun_prop
      have hnext : Continuous
          (fun Λ : ℝ =>
            (mode4JacobiCenter (mode4JacobiG mProject) Λ q *
                  (mode4LeftPair (mode4JacobiG mProject) Λ q).2 -
                mode4JacobiLower (mode4JacobiG mProject) q *
                  (mode4LeftPair (mode4JacobiG mProject) Λ q).1) /
              mode4JacobiUpper (mode4JacobiG mProject) q) :=
        hnum.div continuous_const (fun _ => hUne)
      simpa only [mode4LeftPair] using ih.snd.prodMk hnext

theorem mode4RootFunction_eq_zero_iff_match
    (mProject K : ℕ)
    (Λ : ℝ) :
    mode4RootFunction mProject K Λ = 0 ↔
      (mode4LeftPair
        (mode4JacobiG mProject) Λ K).2 =
        mode4RightTailLimit mProject Λ K *
          (mode4LeftPair
            (mode4JacobiG mProject) Λ K).1 := by
  simp [mode4RootFunction, sub_eq_zero]

theorem mode4RootFunction_continuousOn_lambda
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
      (mode4RootFunction mProject K)
      (Set.Iic 20) := by
  have hleft := mode4LeftPair_continuous_lambda mProject K hm
  have hright := mode4RightTailLimit_continuousOn_lambda
    mProject K hm hK hsep
  unfold mode4RootFunction
  exact hleft.snd.continuousOn.sub (hright.mul hleft.fst.continuousOn)

#print axioms mode4LeftPair_succ_transfer
#print axioms mode4LeftPair_continuous_lambda
#print axioms mode4RootFunction_eq_zero_iff_match
#print axioms mode4RootFunction_continuousOn_lambda
