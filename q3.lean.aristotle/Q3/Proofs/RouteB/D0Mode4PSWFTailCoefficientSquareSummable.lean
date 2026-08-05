import Q3.Proofs.RouteB.D0Mode4PSWFRiccatiOrbitUniqueness

/-!
# The canonical square-summable mode-four tail coefficient row

Starting from coefficient `1`, multiply successively by the committed positive
right-tail ratios.  The invariant cone gives geometric decay, while the
all-index tail identity gives both the project Jacobi recurrence and, through
the proved coefficient crosswalk, the exact source-shaped even-Legendre
recurrence.

This file constructs only an abstract tail coefficient row.  It does not
identify that row with a regular PSWF, a differential eigenfunction, a Weyl
solution, or an operator resolvent.
-/

open Filter Set Topology

noncomputable section

/-- The terminal-independent tail is strictly positive throughout the
certified cone regime. -/
theorem mode4RightTailLimit_pos
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    0 < mode4RightTailLimit mProject Λ K := by
  let G := mode4JacobiG mProject
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hKsucc : 3 ≤ K + 1 := le_trans hK (Nat.le_succ K)
  have hsepSucc :
      ∀ q ≥ K + 1,
        (31 / 24 : ℝ) * G ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
    intro q hq
    exact hsep q (le_trans (Nat.le_succ K) hq)
  have hnext := mode4RightTailLimit_mem_Icc
    mProject (K + 1) Λ hm hKsucc hsepSucc hΛ
  have hdenLower := mode4JacobiCenter_sub_upper_mul_lower_bound
    G Λ (mode4RightTailLimit mProject Λ (K + 1)) K hG hK
      (hsep K le_rfl) hΛ hnext
  have hden :
      0 < mode4JacobiCenter G Λ K -
        mode4JacobiUpper G K * mode4RightTailLimit mProject Λ (K + 1) := by
    linarith
  rw [mode4RightTailLimit_eq_tailMap_succ mProject K Λ hm hK hsep hΛ]
  unfold mode4TailMap
  exact div_pos (mode4JacobiLower_pos G K hG hK) hden

/-- The canonical positive tail coefficient row, normalized by `u 0 = 1`. -/
noncomputable def mode4TailCoefficientRow
    (mProject : ℕ) (Λ : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      mode4RightTailLimit mProject Λ (K + n) *
        mode4TailCoefficientRow mProject Λ K n

@[simp] theorem mode4TailCoefficientRow_zero
    (mProject K : ℕ) (Λ : ℝ) :
    mode4TailCoefficientRow mProject Λ K 0 = 1 := rfl

@[simp] theorem mode4TailCoefficientRow_succ
    (mProject K n : ℕ) (Λ : ℝ) :
    mode4TailCoefficientRow mProject Λ K (n + 1) =
      mode4RightTailLimit mProject Λ (K + n) *
        mode4TailCoefficientRow mProject Λ K n := rfl

theorem mode4TailCoefficientRow_pos
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n, 0 < mode4TailCoefficientRow mProject Λ K n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [mode4TailCoefficientRow_succ]
      have hKn : K ≤ K + n := Nat.le_add_right K n
      exact mul_pos
        (mode4RightTailLimit_pos mProject (K + n) Λ hm
          (le_trans hK hKn)
          (fun q hq => hsep q (le_trans hKn hq)) hΛ)
        ih

theorem mode4TailCoefficientRow_le_half_pow
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      mode4TailCoefficientRow mProject Λ K n ≤ (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [mode4TailCoefficientRow_succ]
      have hKn : K ≤ K + n := Nat.le_add_right K n
      have hKshift : 3 ≤ K + n := le_trans hK hKn
      have hsepShift :
          ∀ q ≥ K + n,
            (31 / 24 : ℝ) * mode4JacobiG mProject ≤
              mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20 := by
        intro q hq
        exact hsep q (le_trans hKn hq)
      have hR := mode4RightTailLimit_mem_Icc
        mProject (K + n) Λ hm hKshift hsepShift hΛ
      have hu0 : 0 ≤ mode4TailCoefficientRow mProject Λ K n :=
        (mode4TailCoefficientRow_pos mProject K Λ hm hK hsep hΛ n).le
      calc
        mode4RightTailLimit mProject Λ (K + n) *
            mode4TailCoefficientRow mProject Λ K n ≤
          (1 / 2 : ℝ) * mode4TailCoefficientRow mProject Λ K n :=
            mul_le_mul_of_nonneg_right hR.2 hu0
        _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) := by
          rw [pow_succ]
          ring

theorem mode4TailCoefficientRow_sq_summable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Summable (fun n => (mode4TailCoefficientRow mProject Λ K n) ^ 2) := by
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hgeom
  have hu0 : 0 ≤ mode4TailCoefficientRow mProject Λ K n :=
    (mode4TailCoefficientRow_pos mProject K Λ hm hK hsep hΛ n).le
  have hu := mode4TailCoefficientRow_le_half_pow
    mProject K Λ hm hK hsep hΛ n
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc
    (mode4TailCoefficientRow mProject Λ K n) ^ 2 ≤
        ((1 / 2 : ℝ) ^ n) ^ 2 := by nlinarith
    _ = (1 / 4 : ℝ) ^ n := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]

theorem mode4TailCoefficientRow_ratio_eq_rightTailLimit
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      mode4TailCoefficientRow mProject Λ K (n + 1) /
          mode4TailCoefficientRow mProject Λ K n =
        mode4RightTailLimit mProject Λ (K + n) := by
  intro n
  rw [mode4TailCoefficientRow_succ]
  field_simp [ne_of_gt (mode4TailCoefficientRow_pos
    mProject K Λ hm hK hsep hΛ n)]

theorem mode4TailCoefficientRow_projectJacobi_recurrence
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      mode4JacobiLower (mode4JacobiG mProject) (K + n) *
            mode4TailCoefficientRow mProject Λ K n -
          mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
            mode4TailCoefficientRow mProject Λ K (n + 1) +
        mode4JacobiUpper (mode4JacobiG mProject) (K + n) *
          mode4TailCoefficientRow mProject Λ K (n + 2) = 0 := by
  intro n
  let G := mode4JacobiG mProject
  let q := K + n
  let R := mode4RightTailLimit mProject Λ q
  let Rnext := mode4RightTailLimit mProject Λ (q + 1)
  have hqK : K ≤ q := by
    unfold q
    omega
  have hq : 3 ≤ q := le_trans hK hqK
  have hsepQ :
      ∀ j ≥ q,
        (31 / 24 : ℝ) * G ≤
          mode4JacobiIndex j * (mode4JacobiIndex j + 1) - 20 := by
    intro j hj
    exact hsep j (le_trans hqK hj)
  have hqsucc : 3 ≤ q + 1 := le_trans hq (Nat.le_succ q)
  have hsepSucc :
      ∀ j ≥ q + 1,
        (31 / 24 : ℝ) * G ≤
          mode4JacobiIndex j * (mode4JacobiIndex j + 1) - 20 := by
    intro j hj
    exact hsepQ j (le_trans (Nat.le_succ q) hj)
  have hG : 0 < G := by
    unfold G mode4JacobiG
    positivity
  have hRnext := mode4RightTailLimit_mem_Icc
    mProject (q + 1) Λ hm hqsucc hsepSucc hΛ
  have hdenLower := mode4JacobiCenter_sub_upper_mul_lower_bound
    G Λ Rnext q hG hq (hsepQ q le_rfl) hΛ hRnext
  have hden : 0 < mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext := by
    linarith
  have htail := mode4RightTailLimit_eq_tailMap_succ
    mProject q Λ hm hq hsepQ hΛ
  change R =
    mode4JacobiLower G q /
      (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext) at htail
  have hcross :
      R * (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext) =
        mode4JacobiLower G q :=
    (eq_div_iff hden.ne').mp htail
  change
    mode4JacobiLower G q * mode4TailCoefficientRow mProject Λ K n -
          mode4JacobiCenter G Λ q *
            mode4TailCoefficientRow mProject Λ K (n + 1) +
        mode4JacobiUpper G q *
          mode4TailCoefficientRow mProject Λ K (n + 2) = 0
  rw [mode4TailCoefficientRow_succ, mode4TailCoefficientRow_succ]
  change
    mode4JacobiLower G q * mode4TailCoefficientRow mProject Λ K n -
          mode4JacobiCenter G Λ q *
            (R * mode4TailCoefficientRow mProject Λ K n) +
        mode4JacobiUpper G q *
          (Rnext * (R * mode4TailCoefficientRow mProject Λ K n)) = 0
  calc
    mode4JacobiLower G q * mode4TailCoefficientRow mProject Λ K n -
            mode4JacobiCenter G Λ q *
              (R * mode4TailCoefficientRow mProject Λ K n) +
          mode4JacobiUpper G q *
            (Rnext * (R * mode4TailCoefficientRow mProject Λ K n)) =
        (mode4JacobiLower G q -
            R * (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext)) *
          mode4TailCoefficientRow mProject Λ K n := by ring
    _ = 0 := by rw [hcross]; ring

theorem mode4TailCoefficientRow_pswfLegendre_recurrence
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      mode4PSWFLegendreSubdiagonal
            (mode4JacobiG mProject) (K + n) *
            mode4TailCoefficientRow mProject Λ K n +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) (K + n) -
              (Λ + mode4JacobiG mProject)) *
            mode4TailCoefficientRow mProject Λ K (n + 1) +
        mode4PSWFLegendreSuperdiagonal
            (mode4JacobiG mProject) (K + n) *
          mode4TailCoefficientRow mProject Λ K (n + 2) = 0 := by
  intro n
  let G := mode4JacobiG mProject
  let q := K + n
  have hcross := mode4JacobiCoefficients_eq_pswfLegendre_evenCrosswalk G Λ q
  have hsub : mode4PSWFLegendreSubdiagonal G q = -mode4JacobiLower G q := by
    linarith [hcross.1]
  have hdiag :
      mode4PSWFLegendreDiagonal G q - (Λ + G) =
        mode4JacobiCenter G Λ q := hcross.2.1.symm
  have hsuper : mode4PSWFLegendreSuperdiagonal G q = -mode4JacobiUpper G q := by
    linarith [hcross.2.2]
  change
    mode4PSWFLegendreSubdiagonal G q *
          mode4TailCoefficientRow mProject Λ K n +
        (mode4PSWFLegendreDiagonal G q - (Λ + G)) *
          mode4TailCoefficientRow mProject Λ K (n + 1) +
      mode4PSWFLegendreSuperdiagonal G q *
        mode4TailCoefficientRow mProject Λ K (n + 2) = 0
  rw [hsub, hdiag, hsuper]
  have hproject := mode4TailCoefficientRow_projectJacobi_recurrence
    mProject K Λ hm hK hsep hΛ n
  change
    mode4JacobiLower G q * mode4TailCoefficientRow mProject Λ K n -
          mode4JacobiCenter G Λ q *
            mode4TailCoefficientRow mProject Λ K (n + 1) +
        mode4JacobiUpper G q *
          mode4TailCoefficientRow mProject Λ K (n + 2) = 0 at hproject
  linarith

#print axioms mode4RightTailLimit_pos
#print axioms mode4TailCoefficientRow_pos
#print axioms mode4TailCoefficientRow_le_half_pow
#print axioms mode4TailCoefficientRow_sq_summable
#print axioms mode4TailCoefficientRow_ratio_eq_rightTailLimit
#print axioms mode4TailCoefficientRow_projectJacobi_recurrence
#print axioms mode4TailCoefficientRow_pswfLegendre_recurrence
