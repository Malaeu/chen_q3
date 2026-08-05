import Q3.Proofs.RouteB.D0Mode4PSWFTailCoefficientSquareSummable

/-!
# The canonical mode-four tail row in Hermitian Jacobi coordinates

The explicit positive diagonal scale below conjugates the already constructed
canonical square-summable tail row to the symmetric off-diagonal coordinates
used by `mode4HermitianSchurMatrix`.  The final scalar identity is deliberately
called a boundary flux: this file does not construct a differential operator,
an infinite operator, a resolvent, a regular PSWF row, or a Weyl solution.
-/

open Set

noncomputable section

/-- Positive diagonal scale normalized at the first retained coefficient.
It is derived solely from the exact project Jacobi coefficients. -/
noncomputable def mode4TailHermitianScale
    (K n : ℕ) : ℝ :=
  Real.sqrt
    ((4 * (K : ℝ) - 3) /
      (4 * ((K + n : ℕ) : ℝ) - 3))

/-- The canonical abstract tail row in symmetric Jacobi coordinates. -/
noncomputable def mode4HermitianTailCoefficientRow
    (mProject : ℕ) (Λ : ℝ) (K : ℕ) (n : ℕ) : ℝ :=
  mode4TailHermitianScale K n *
    mode4TailCoefficientRow mProject Λ K n

private theorem mode4TailHermitianScale_pos
    (K n : ℕ) (hK : 3 ≤ K) :
    0 < mode4TailHermitianScale K n := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold mode4TailHermitianScale
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (by linarith)

private theorem mode4TailHermitianScale_le_one
    (K n : ℕ) (hK : 3 ≤ K) :
    mode4TailHermitianScale K n ≤ 1 := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold mode4TailHermitianScale
  rw [Real.sqrt_le_one]
  exact (div_le_one (by linarith)).2 (by linarith)

private theorem mode4TailHermitianScale_sq
    (K n : ℕ) (hK : 3 ≤ K) :
    mode4TailHermitianScale K n ^ 2 =
      (4 * (K : ℝ) - 3) /
        (4 * ((K + n : ℕ) : ℝ) - 3) := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold mode4TailHermitianScale
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

private theorem mode4TailHermitianScale_zero
    (K : ℕ) (hK : 3 ≤ K) :
    mode4TailHermitianScale K 0 = 1 := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hne : 4 * (K : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  unfold mode4TailHermitianScale
  norm_num [hne]

private theorem mode4TailHermitianScale_lower_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiLower G (K + n) * mode4TailHermitianScale K (n + 1) =
      mode4JacobiSymmetricOff G (K - 1 + n) * mode4TailHermitianScale K n := by
  have hq : 3 ≤ K + n := le_trans hK (Nat.le_add_right K n)
  have hidx : K - 1 + n + 1 = K + n := by omega
  have hleft :
      0 ≤ mode4JacobiLower G (K + n) * mode4TailHermitianScale K (n + 1) :=
    (mul_pos (mode4JacobiLower_pos G (K + n) hG hq)
      (mode4TailHermitianScale_pos K (n + 1) hK)).le
  have hright :
      0 ≤ mode4JacobiSymmetricOff G (K - 1 + n) *
          mode4TailHermitianScale K n := by
    exact mul_nonneg (Real.sqrt_nonneg _) (mode4TailHermitianScale_pos K n hK).le
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, mul_pow,
    mode4JacobiSymmetricOff_sq G (K - 1 + n) hG, hidx,
    mode4TailHermitianScale_sq K (n + 1) hK,
    mode4TailHermitianScale_sq K n hK]
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold mode4JacobiLower mode4JacobiUpper mode4JacobiIndex
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
  field_simp <;> ring

private theorem mode4TailHermitianScale_upper_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiUpper G (K + n) * mode4TailHermitianScale K (n + 1) =
      mode4JacobiSymmetricOff G (K + n) * mode4TailHermitianScale K (n + 2) := by
  have hqSucc : 3 ≤ K + n + 1 := by omega
  have hLpos : 0 < mode4JacobiLower G (K + n + 1) :=
    mode4JacobiLower_pos G (K + n + 1) hG hqSucc
  have hlower := mode4TailHermitianScale_lower_balance G K (n + 1) hG hK
  have hidxLower : K + (n + 1) = K + n + 1 := by omega
  have hidxOff : K - 1 + (n + 1) = K + n := by omega
  rw [hidxLower, hidxOff] at hlower
  have hsq := mode4JacobiSymmetricOff_sq G (K + n) hG
  apply mul_left_cancel₀ (ne_of_gt hLpos)
  calc
    mode4JacobiLower G (K + n + 1) *
        (mode4JacobiUpper G (K + n) * mode4TailHermitianScale K (n + 1)) =
      (mode4JacobiLower G (K + n + 1) * mode4JacobiUpper G (K + n)) *
        mode4TailHermitianScale K (n + 1) := by ring
    _ = mode4JacobiSymmetricOff G (K + n) ^ 2 *
        mode4TailHermitianScale K (n + 1) := by rw [hsq]
    _ = mode4JacobiSymmetricOff G (K + n) *
        (mode4JacobiSymmetricOff G (K + n) *
          mode4TailHermitianScale K (n + 1)) := by ring
    _ = mode4JacobiSymmetricOff G (K + n) *
        (mode4JacobiLower G (K + n + 1) *
          mode4TailHermitianScale K (n + 2)) := by rw [hlower]
    _ = mode4JacobiLower G (K + n + 1) *
        (mode4JacobiSymmetricOff G (K + n) *
          mode4TailHermitianScale K (n + 2)) := by ring

private theorem mode4TailHermitianScale_boundary_balance
    (G : ℝ) (K : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiSymmetricOff G (K - 1) * mode4TailHermitianScale K 1 =
      mode4JacobiUpper G (K - 1) * mode4TailHermitianScale K 0 := by
  have hleft :
      0 ≤ mode4JacobiSymmetricOff G (K - 1) * mode4TailHermitianScale K 1 := by
    exact mul_nonneg (Real.sqrt_nonneg _) (mode4TailHermitianScale_pos K 1 hK).le
  have hright :
      0 ≤ mode4JacobiUpper G (K - 1) * mode4TailHermitianScale K 0 :=
    (mul_pos (mode4JacobiUpper_pos G (K - 1) hG)
      (mode4TailHermitianScale_pos K 0 hK)).le
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, mul_pow, mode4JacobiSymmetricOff_sq G (K - 1) hG,
    mode4TailHermitianScale_sq K 1 hK,
    mode4TailHermitianScale_sq K 0 hK]
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hidx : K - 1 + 1 = K := by omega
  rw [hidx]
  unfold mode4JacobiLower mode4JacobiUpper mode4JacobiIndex
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
  field_simp <;> ring

theorem mode4HermitianTailCoefficientRow_zero
    (mProject K : ℕ) (Λ : ℝ)
    (hK : 3 ≤ K) :
    mode4HermitianTailCoefficientRow mProject Λ K 0 = 1 := by
  unfold mode4HermitianTailCoefficientRow
  rw [mode4TailCoefficientRow_zero, mode4TailHermitianScale_zero K hK]
  norm_num

theorem mode4HermitianTailCoefficientRow_pos
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n, 0 < mode4HermitianTailCoefficientRow mProject Λ K n := by
  intro n
  unfold mode4HermitianTailCoefficientRow
  exact mul_pos (mode4TailHermitianScale_pos K n hK)
    (mode4TailCoefficientRow_pos mProject K Λ hm hK hsep hΛ n)

theorem mode4HermitianTailCoefficientRow_sq_summable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Summable (fun n =>
      (mode4HermitianTailCoefficientRow mProject Λ K n) ^ 2) := by
  have hu := mode4TailCoefficientRow_sq_summable
    mProject K Λ hm hK hsep hΛ
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hu
  have hs0 := (mode4TailHermitianScale_pos K n hK).le
  have hs1 := mode4TailHermitianScale_le_one K n hK
  have hs2 : mode4TailHermitianScale K n ^ 2 ≤ 1 := by nlinarith
  unfold mode4HermitianTailCoefficientRow
  rw [mul_pow]
  simpa using mul_le_mul_of_nonneg_right hs2
    (sq_nonneg (mode4TailCoefficientRow mProject Λ K n))

theorem mode4HermitianTailCoefficientRow_recurrence
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
          mode4HermitianTailCoefficientRow mProject Λ K n -
        mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
          mode4HermitianTailCoefficientRow mProject Λ K (n + 1) +
        mode4JacobiSymmetricOff (mode4JacobiG mProject) (K + n) *
          mode4HermitianTailCoefficientRow mProject Λ K (n + 2) = 0 := by
  intro n
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hraw := mode4TailCoefficientRow_projectJacobi_recurrence
    mProject K Λ hm hK hsep hΛ n
  have hlower := mode4TailHermitianScale_lower_balance
    (mode4JacobiG mProject) K n hG hK
  have hupper := mode4TailHermitianScale_upper_balance
    (mode4JacobiG mProject) K n hG hK
  unfold mode4HermitianTailCoefficientRow
  calc
    _ = mode4TailHermitianScale K (n + 1) *
        (mode4JacobiLower (mode4JacobiG mProject) (K + n) *
            mode4TailCoefficientRow mProject Λ K n -
          mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
            mode4TailCoefficientRow mProject Λ K (n + 1) +
          mode4JacobiUpper (mode4JacobiG mProject) (K + n) *
            mode4TailCoefficientRow mProject Λ K (n + 2)) := by
      rw [show
        mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
            (mode4TailHermitianScale K n *
              mode4TailCoefficientRow mProject Λ K n) =
          (mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
            mode4TailHermitianScale K n) *
              mode4TailCoefficientRow mProject Λ K n by ring,
        ← hlower]
      rw [show
        mode4JacobiSymmetricOff (mode4JacobiG mProject) (K + n) *
            (mode4TailHermitianScale K (n + 2) *
              mode4TailCoefficientRow mProject Λ K (n + 2)) =
          (mode4JacobiSymmetricOff (mode4JacobiG mProject) (K + n) *
            mode4TailHermitianScale K (n + 2)) *
              mode4TailCoefficientRow mProject Λ K (n + 2) by ring,
        ← hupper]
      ring
    _ = 0 := by rw [hraw, mul_zero]

theorem mode4HermitianTail_boundaryFlux_eq_schurCorrection
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K) :
    mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) *
        (mode4HermitianTailCoefficientRow mProject Λ K 1 /
          mode4HermitianTailCoefficientRow mProject Λ K 0) =
      mode4JacobiUpper (mode4JacobiG mProject) (K - 1) *
        mode4RightTailLimit mProject Λ K := by
  have hG : 0 < mode4JacobiG mProject := by
    unfold mode4JacobiG
    positivity
  have hbalance := mode4TailHermitianScale_boundary_balance
    (mode4JacobiG mProject) K hG hK
  rw [mode4HermitianTailCoefficientRow_zero mProject K Λ hK]
  unfold mode4HermitianTailCoefficientRow
  rw [mode4TailCoefficientRow_succ, mode4TailCoefficientRow_zero]
  norm_num
  rw [mode4TailHermitianScale_zero K hK] at hbalance
  calc
    mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) *
        (mode4TailHermitianScale K 1 * mode4RightTailLimit mProject Λ K) =
      (mode4JacobiSymmetricOff (mode4JacobiG mProject) (K - 1) *
        mode4TailHermitianScale K 1) * mode4RightTailLimit mProject Λ K := by ring
    _ = (mode4JacobiUpper (mode4JacobiG mProject) (K - 1) * 1) *
        mode4RightTailLimit mProject Λ K := by rw [hbalance]
    _ = _ := by ring

#print axioms mode4HermitianTailCoefficientRow_zero
#print axioms mode4HermitianTailCoefficientRow_pos
#print axioms mode4HermitianTailCoefficientRow_sq_summable
#print axioms mode4HermitianTailCoefficientRow_recurrence
#print axioms mode4HermitianTail_boundaryFlux_eq_schurCorrection
