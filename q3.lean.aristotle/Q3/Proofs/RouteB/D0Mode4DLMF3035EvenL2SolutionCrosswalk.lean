import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource

/-!
# DLMF 30.3.5 characteristic equation and the normalized square-summable row

This file identifies the independent pole-safe even DLMF characteristic
equation with square summability of the uniquely normalized finite-left
recurrence row.  The forward implication splices that row to the
contraction-selected infinite right branch and proves geometric decay.  The
reverse implication uses a local positive diagonal symmetrization and a
discrete-Wronskian uniqueness argument to exclude the dominant solution.

Only the source-side characteristic module is imported directly.  In
particular, the proof does not import the later canonical tail-row or
Hermitian-tail uniqueness modules; their bounded algebraic ingredients are
proved privately here.  The project root function, endpoint spectral arithmetic,
the finite-limit spectral carrier, mode selection, and all Route/RH consumers
are absent from this proof.

Source conventions are inherited unchanged from the allowed import: NIST
DLMF 30.3.5 and 30.3.7, order zero, even degree `2*q`, `G = gamma^2`, project
`Lambda =` DLMF `lambda`, and split degree `2*(K-1)`.

Knowledge preflight receipt: the exact query `DLMF 30.3.5 characteristic
equation normalized left coefficient square summable l2 Jacobi solution
crosswalk` returned no exact hit in any knowledge layer.  Strict startup at
`2416bed3` passed `P9_STRICT_PASS`; the two directly relevant supplier hashes
were `5ee718a3...4919c` and `0822a359...1ab06`.
-/

open Filter Topology

namespace Q3.RouteB

noncomputable section

/-- Normalized left coefficient selected by the parity boundary
`a₋₁ = 0`, `a₀ = 1`. -/
noncomputable def mode4DLMF3035EvenLeftCoefficient
    (G Λ : ℝ) (q : ℕ) : ℝ :=
  (mode4DLMF3035EvenLeftPair G Λ q).2

private theorem leftPair_fst_eq_prev
    (G Λ : ℝ) (q : ℕ) (hq : 1 ≤ q) :
    (mode4LeftPair G Λ q).1 =
      (mode4LeftPair G Λ (q - 1)).2 := by
  cases q with
  | zero => omega
  | succ n => simp [mode4LeftPair]

private theorem leftPair_row_recurrence
    (mProject : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject) :
    ∀ q : ℕ,
      mode4JacobiLower (mode4JacobiG mProject) q *
          (mode4LeftPair (mode4JacobiG mProject) Λ (q - 1)).2 -
        mode4JacobiCenter (mode4JacobiG mProject) Λ q *
          (mode4LeftPair (mode4JacobiG mProject) Λ q).2 +
        mode4JacobiUpper (mode4JacobiG mProject) q *
          (mode4LeftPair (mode4JacobiG mProject) Λ (q + 1)).2 = 0 := by
  intro q
  have htransfer := mode4LeftPair_succ_transfer mProject q Λ hm
  dsimp only at htransfer
  cases q with
  | zero =>
      have hlower : mode4JacobiLower (mode4JacobiG mProject) 0 = 0 := by
        simp [mode4JacobiLower, mode4JacobiIndex]
      rw [hlower] at htransfer ⊢
      norm_num at htransfer ⊢
      linarith [htransfer.2]
  | succ n =>
      have hfst := leftPair_fst_eq_prev
        (mode4JacobiG mProject) Λ (n + 1) (by omega)
      rw [hfst] at htransfer
      have hprev : n + 1 - 1 = n := by omega
      have hnext : n + 1 + 1 = n + 2 := by omega
      rw [hprev, hnext] at htransfer ⊢
      linarith [htransfer.2]

private noncomputable def l2SymmetricOff
    (G : ℝ) (q : ℕ) : ℝ :=
  Real.sqrt
    (mode4JacobiLower G (q + 1) * mode4JacobiUpper G q)

private theorem l2SymmetricOff_sq
    (G : ℝ) (q : ℕ) (hG : 0 < G) :
    l2SymmetricOff G q ^ 2 =
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q := by
  unfold l2SymmetricOff
  exact Real.sq_sqrt <| mul_nonneg
    (by
      by_cases hq : 3 ≤ q + 1
      · exact (mode4JacobiLower_pos G (q + 1) hG hq).le
      · have hq_le : q ≤ 1 := by omega
        interval_cases q <;>
          simp [mode4JacobiLower, mode4JacobiIndex] <;>
          positivity)
    (mode4JacobiUpper_pos G q hG).le

private theorem l2SymmetricOff_pos
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 2 ≤ q) :
    0 < l2SymmetricOff G q := by
  unfold l2SymmetricOff
  apply Real.sqrt_pos.2
  exact mul_pos
    (mode4JacobiLower_pos G (q + 1) hG (by omega))
    (mode4JacobiUpper_pos G q hG)

private theorem l2SymmetricOff_le_G
    (G : ℝ) (q : ℕ)
    (hG : 0 < G)
    (hq : 2 ≤ q) :
    l2SymmetricOff G q ≤ G := by
  have hqSucc : 3 ≤ q + 1 := by omega
  have hL0 : 0 ≤ mode4JacobiLower G (q + 1) :=
    (mode4JacobiLower_pos G (q + 1) hG hqSucc).le
  have hU0 : 0 ≤ mode4JacobiUpper G q :=
    (mode4JacobiUpper_pos G q hG).le
  have hL := mode4JacobiLower_le_one_third_mul_G G (q + 1) hG hqSucc
  have hU := mode4JacobiUpper_le_one_quarter_mul_G G q hG
  have hprod :
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤ G ^ 2 := by
    calc
      mode4JacobiLower G (q + 1) * mode4JacobiUpper G q ≤
          ((1 / 3 : ℝ) * G) * ((1 / 4 : ℝ) * G) :=
        mul_le_mul hL hU hU0 (by positivity)
      _ ≤ G ^ 2 := by nlinarith [sq_pos_of_pos hG]
  unfold l2SymmetricOff
  exact (Real.sqrt_le_left hG.le).2 hprod

private noncomputable def l2Scale
    (K n : ℕ) : ℝ :=
  Real.sqrt
    ((4 * (K : ℝ) - 3) /
      (4 * ((K + n : ℕ) : ℝ) - 3))

private theorem l2Scale_pos
    (K n : ℕ) (hK : 3 ≤ K) :
    0 < l2Scale K n := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold l2Scale
  apply Real.sqrt_pos.2
  exact div_pos (by linarith) (by linarith)

private theorem l2Scale_le_one
    (K n : ℕ) (hK : 3 ≤ K) :
    l2Scale K n ≤ 1 := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold l2Scale
  rw [Real.sqrt_le_one]
  exact (div_le_one (by linarith)).2 (by linarith)

private theorem l2Scale_sq
    (K n : ℕ) (hK : 3 ≤ K) :
    l2Scale K n ^ 2 =
      (4 * (K : ℝ) - 3) /
        (4 * ((K + n : ℕ) : ℝ) - 3) := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hKn : K ≤ K + n := Nat.le_add_right K n
  have hKnreal : (K : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast hKn
  unfold l2Scale
  exact Real.sq_sqrt (div_nonneg (by linarith) (by linarith))

private theorem l2Scale_zero
    (K : ℕ) (hK : 3 ≤ K) :
    l2Scale K 0 = 1 := by
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hne : 4 * (K : ℝ) - 3 ≠ 0 := ne_of_gt (by linarith)
  unfold l2Scale
  norm_num [hne]

private theorem l2Scale_lower_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiLower G (K + n) * l2Scale K (n + 1) =
      l2SymmetricOff G (K - 1 + n) * l2Scale K n := by
  have hq : 3 ≤ K + n := le_trans hK (Nat.le_add_right K n)
  have hidx : K - 1 + n + 1 = K + n := by omega
  have hleft :
      0 ≤ mode4JacobiLower G (K + n) * l2Scale K (n + 1) :=
    (mul_pos (mode4JacobiLower_pos G (K + n) hG hq)
      (l2Scale_pos K (n + 1) hK)).le
  have hright :
      0 ≤ l2SymmetricOff G (K - 1 + n) * l2Scale K n := by
    exact mul_nonneg (Real.sqrt_nonneg _) (l2Scale_pos K n hK).le
  apply (sq_eq_sq₀ hleft hright).mp
  rw [mul_pow, mul_pow, l2SymmetricOff_sq G (K - 1 + n) hG, hidx,
    l2Scale_sq K (n + 1) hK, l2Scale_sq K n hK]
  have hKreal : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hnreal : (0 : ℝ) ≤ (n : ℝ) := by positivity
  unfold mode4JacobiLower mode4JacobiUpper mode4JacobiIndex
  push_cast [Nat.cast_sub (by omega : 1 ≤ K)]
  field_simp
  ring

private theorem l2Scale_upper_balance
    (G : ℝ) (K n : ℕ) (hG : 0 < G) (hK : 3 ≤ K) :
    mode4JacobiUpper G (K + n) * l2Scale K (n + 1) =
      l2SymmetricOff G (K + n) * l2Scale K (n + 2) := by
  have hqSucc : 3 ≤ K + n + 1 := by omega
  have hLpos : 0 < mode4JacobiLower G (K + n + 1) :=
    mode4JacobiLower_pos G (K + n + 1) hG hqSucc
  have hlower := l2Scale_lower_balance G K (n + 1) hG hK
  have hidxLower : K + (n + 1) = K + n + 1 := by omega
  have hidxOff : K - 1 + (n + 1) = K + n := by omega
  rw [hidxLower, hidxOff] at hlower
  have hsq := l2SymmetricOff_sq G (K + n) hG
  apply mul_left_cancel₀ (ne_of_gt hLpos)
  calc
    mode4JacobiLower G (K + n + 1) *
        (mode4JacobiUpper G (K + n) * l2Scale K (n + 1)) =
      (mode4JacobiLower G (K + n + 1) * mode4JacobiUpper G (K + n)) *
        l2Scale K (n + 1) := by ring
    _ = l2SymmetricOff G (K + n) ^ 2 * l2Scale K (n + 1) := by rw [hsq]
    _ = l2SymmetricOff G (K + n) *
        (l2SymmetricOff G (K + n) * l2Scale K (n + 1)) := by ring
    _ = l2SymmetricOff G (K + n) *
        (mode4JacobiLower G (K + n + 1) * l2Scale K (n + 2)) := by rw [hlower]
    _ = mode4JacobiLower G (K + n + 1) *
        (l2SymmetricOff G (K + n) * l2Scale K (n + 2)) := by ring

private noncomputable def l2TailRow
    (mProject : ℕ) (Λ : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      mode4RightTailLimit mProject Λ (K + n) *
        l2TailRow mProject Λ K n

@[simp] private theorem l2TailRow_zero
    (mProject K : ℕ) (Λ : ℝ) :
    l2TailRow mProject Λ K 0 = 1 := rfl

@[simp] private theorem l2TailRow_succ
    (mProject K n : ℕ) (Λ : ℝ) :
    l2TailRow mProject Λ K (n + 1) =
      mode4RightTailLimit mProject Λ (K + n) *
        l2TailRow mProject Λ K n := rfl

private theorem l2TailRow_nonneg
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n, 0 ≤ l2TailRow mProject Λ K n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [l2TailRow_succ]
      have hKn : K ≤ K + n := Nat.le_add_right K n
      have hR := mode4RightTailLimit_mem_Icc
        mProject (K + n) Λ hm (le_trans hK hKn)
        (fun q hq => hsep q (le_trans hKn hq)) hΛ
      exact mul_nonneg hR.1 ih

private theorem l2TailRow_le_half_pow
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n, l2TailRow mProject Λ K n ≤ (1 / 2 : ℝ) ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [l2TailRow_succ]
      have hKn : K ≤ K + n := Nat.le_add_right K n
      have hR := mode4RightTailLimit_mem_Icc
        mProject (K + n) Λ hm (le_trans hK hKn)
        (fun q hq => hsep q (le_trans hKn hq)) hΛ
      have hu0 := l2TailRow_nonneg mProject K Λ hm hK hsep hΛ n
      calc
        mode4RightTailLimit mProject Λ (K + n) * l2TailRow mProject Λ K n ≤
            (1 / 2 : ℝ) * l2TailRow mProject Λ K n :=
          mul_le_mul_of_nonneg_right hR.2 hu0
        _ ≤ (1 / 2 : ℝ) * (1 / 2 : ℝ) ^ n :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 2 : ℝ) ^ (n + 1) := by rw [pow_succ]; ring

private theorem l2TailRow_sq_summable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Summable (fun n => (l2TailRow mProject Λ K n) ^ 2) := by
  have hgeom : Summable (fun n : ℕ => (1 / 4 : ℝ) ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hgeom
  have hu0 := l2TailRow_nonneg mProject K Λ hm hK hsep hΛ n
  have hu := l2TailRow_le_half_pow mProject K Λ hm hK hsep hΛ n
  have hhalf0 : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
  calc
    (l2TailRow mProject Λ K n) ^ 2 ≤ ((1 / 2 : ℝ) ^ n) ^ 2 := by nlinarith
    _ = (1 / 4 : ℝ) ^ n := by
      rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm]

private theorem l2TailRow_recurrence
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
            l2TailRow mProject Λ K n -
          mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
            l2TailRow mProject Λ K (n + 1) +
        mode4JacobiUpper (mode4JacobiG mProject) (K + n) *
          l2TailRow mProject Λ K (n + 2) = 0 := by
  intro n
  let G := mode4JacobiG mProject
  let q := K + n
  let R := mode4RightTailLimit mProject Λ q
  let Rnext := mode4RightTailLimit mProject Λ (q + 1)
  have hqK : K ≤ q := by unfold q; omega
  have hq : 3 ≤ q := le_trans hK hqK
  have hsepQ : ∀ j ≥ q,
      (31 / 24 : ℝ) * G ≤
        mode4JacobiIndex j * (mode4JacobiIndex j + 1) - 20 := by
    intro j hj
    exact hsep j (le_trans hqK hj)
  have hqsucc : 3 ≤ q + 1 := le_trans hq (Nat.le_succ q)
  have hsepSucc : ∀ j ≥ q + 1,
      (31 / 24 : ℝ) * G ≤
        mode4JacobiIndex j * (mode4JacobiIndex j + 1) - 20 := by
    intro j hj
    exact hsepQ j (le_trans (Nat.le_succ q) hj)
  have hG : 0 < G := by unfold G mode4JacobiG; positivity
  have hRnext := mode4RightTailLimit_mem_Icc
    mProject (q + 1) Λ hm hqsucc hsepSucc hΛ
  have hdenLower := mode4JacobiCenter_sub_upper_mul_lower_bound
    G Λ Rnext q hG hq (hsepQ q le_rfl) hΛ hRnext
  have hden : 0 < mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext := by
    linarith
  have htail := mode4RightTailLimit_eq_tailMap_succ
    mProject q Λ hm hq hsepQ hΛ
  change R = mode4JacobiLower G q /
    (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext) at htail
  have hcross :
      R * (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext) =
        mode4JacobiLower G q :=
    (eq_div_iff hden.ne').mp htail
  change
    mode4JacobiLower G q * l2TailRow mProject Λ K n -
        mode4JacobiCenter G Λ q * l2TailRow mProject Λ K (n + 1) +
      mode4JacobiUpper G q * l2TailRow mProject Λ K (n + 2) = 0
  rw [l2TailRow_succ, l2TailRow_succ]
  change
    mode4JacobiLower G q * l2TailRow mProject Λ K n -
        mode4JacobiCenter G Λ q * (R * l2TailRow mProject Λ K n) +
      mode4JacobiUpper G q * (Rnext * (R * l2TailRow mProject Λ K n)) = 0
  calc
    _ = (mode4JacobiLower G q -
        R * (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * Rnext)) *
          l2TailRow mProject Λ K n := by ring
    _ = 0 := by rw [hcross]; ring

private noncomputable def l2HermitianTailRow
    (mProject : ℕ) (Λ : ℝ) (K n : ℕ) : ℝ :=
  l2Scale K n * l2TailRow mProject Λ K n

private theorem l2HermitianTailRow_zero
    (mProject K : ℕ) (Λ : ℝ) (hK : 3 ≤ K) :
    l2HermitianTailRow mProject Λ K 0 = 1 := by
  unfold l2HermitianTailRow
  rw [l2TailRow_zero, l2Scale_zero K hK]
  norm_num

private theorem l2HermitianTailRow_sq_summable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    Summable (fun n => (l2HermitianTailRow mProject Λ K n) ^ 2) := by
  have hu := l2TailRow_sq_summable mProject K Λ hm hK hsep hΛ
  refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hu
  have hs0 := (l2Scale_pos K n hK).le
  have hs1 := l2Scale_le_one K n hK
  have hs2 : l2Scale K n ^ 2 ≤ 1 := by nlinarith
  unfold l2HermitianTailRow
  rw [mul_pow]
  simpa using mul_le_mul_of_nonneg_right hs2 (sq_nonneg (l2TailRow mProject Λ K n))

private theorem l2HermitianTailRow_recurrence
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ∀ n,
      l2SymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
          l2HermitianTailRow mProject Λ K n -
        mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
          l2HermitianTailRow mProject Λ K (n + 1) +
        l2SymmetricOff (mode4JacobiG mProject) (K + n) *
          l2HermitianTailRow mProject Λ K (n + 2) = 0 := by
  intro n
  have hG : 0 < mode4JacobiG mProject := by unfold mode4JacobiG; positivity
  have hraw := l2TailRow_recurrence mProject K Λ hm hK hsep hΛ n
  have hlower := l2Scale_lower_balance
    (mode4JacobiG mProject) K n hG hK
  have hupper := l2Scale_upper_balance
    (mode4JacobiG mProject) K n hG hK
  unfold l2HermitianTailRow
  calc
    _ = l2Scale K (n + 1) *
        (mode4JacobiLower (mode4JacobiG mProject) (K + n) *
            l2TailRow mProject Λ K n -
          mode4JacobiCenter (mode4JacobiG mProject) Λ (K + n) *
            l2TailRow mProject Λ K (n + 1) +
          mode4JacobiUpper (mode4JacobiG mProject) (K + n) *
            l2TailRow mProject Λ K (n + 2)) := by
      rw [show
        l2SymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
            (l2Scale K n * l2TailRow mProject Λ K n) =
          (l2SymmetricOff (mode4JacobiG mProject) (K - 1 + n) *
            l2Scale K n) * l2TailRow mProject Λ K n by ring,
        ← hlower]
      rw [show
        l2SymmetricOff (mode4JacobiG mProject) (K + n) *
            (l2Scale K (n + 2) * l2TailRow mProject Λ K (n + 2)) =
          (l2SymmetricOff (mode4JacobiG mProject) (K + n) *
            l2Scale K (n + 2)) * l2TailRow mProject Λ K (n + 2) by ring,
        ← hupper]
      ring
    _ = 0 := by rw [hraw, mul_zero]

private theorem sqSummable_tendsto_zero
    {a : ℕ → ℝ}
    (ha : Summable (fun n => (a n) ^ 2)) :
    Tendsto a atTop (𝓝 0) := by
  have hsquare : Tendsto (fun n => (a n) ^ 2) atTop (𝓝 0) :=
    ha.tendsto_atTop_zero
  have habs : Tendsto (fun n => |a n|) atTop (𝓝 0) := by
    have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsquare
    simpa [Function.comp_def, Real.sqrt_sq_eq_abs] using hsqrt
  exact (tendsto_zero_iff_abs_tendsto_zero a).2
    (by simpa [Function.comp_def] using habs)

private theorem l2Hermitian_sqSummable_unique_up_to_scale
    (G Λ : ℝ) (K : ℕ)
    (hG : 0 < G)
    (hK : 3 ≤ K)
    (a b : ℕ → ℝ)
    (ha0 : a 0 ≠ 0)
    (haRec : ∀ n,
      l2SymmetricOff G (K - 1 + n) * a n -
        mode4JacobiCenter G Λ (K + n) * a (n + 1) +
        l2SymmetricOff G (K + n) * a (n + 2) = 0)
    (hbRec : ∀ n,
      l2SymmetricOff G (K - 1 + n) * b n -
        mode4JacobiCenter G Λ (K + n) * b (n + 1) +
        l2SymmetricOff G (K + n) * b (n + 2) = 0)
    (haSq : Summable (fun n => (a n) ^ 2))
    (hbSq : Summable (fun n => (b n) ^ 2)) :
    ∃ c : ℝ, ∀ n, b n = c * a n := by
  let W : ℕ → ℝ := fun n => a n * b (n + 1) - a (n + 1) * b n
  let J : ℕ → ℝ := fun n => l2SymmetricOff G (K - 1 + n) * W n
  have haLim := sqSummable_tendsto_zero haSq
  have hbLim := sqSummable_tendsto_zero hbSq
  have hshift : Tendsto (fun n : ℕ => n + 1) atTop atTop :=
    Filter.tendsto_add_atTop_nat 1
  have haSuccLim : Tendsto (fun n => a (n + 1)) atTop (𝓝 0) :=
    haLim.comp hshift
  have hbSuccLim : Tendsto (fun n => b (n + 1)) atTop (𝓝 0) :=
    hbLim.comp hshift
  have hWLim : Tendsto W atTop (𝓝 0) := by
    have h := (haLim.mul hbSuccLim).sub (haSuccLim.mul hbLim)
    simpa [W] using h
  have hWrec : ∀ n,
      l2SymmetricOff G (K + n) * W (n + 1) =
        l2SymmetricOff G (K - 1 + n) * W n := by
    intro n
    have ha := haRec n
    have hb := hbRec n
    change l2SymmetricOff G (K + n) *
        (a (n + 1) * b (n + 2) - a (n + 2) * b (n + 1)) =
      l2SymmetricOff G (K - 1 + n) *
        (a n * b (n + 1) - a (n + 1) * b n)
    linear_combination a (n + 1) * hb - b (n + 1) * ha
  have hJsucc : ∀ n, J (n + 1) = J n := by
    intro n
    have hidx : K - 1 + (n + 1) = K + n := by omega
    change l2SymmetricOff G (K - 1 + (n + 1)) * W (n + 1) =
      l2SymmetricOff G (K - 1 + n) * W n
    rw [hidx]
    exact hWrec n
  have hJconst : ∀ n, J n = J 0 := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [hJsucc n, ih]
  have hJbound : ∀ n, |J 0| ≤ G * |W n| := by
    intro n
    rw [← hJconst n]
    have hq : 2 ≤ K - 1 + n := by omega
    have hoff0 := (l2SymmetricOff_pos G (K - 1 + n) hG hq).le
    have hoff := l2SymmetricOff_le_G G (K - 1 + n) hG hq
    unfold J
    rw [abs_mul, abs_of_nonneg hoff0]
    exact mul_le_mul_of_nonneg_right hoff (abs_nonneg _)
  have hboundLim : Tendsto (fun n => G * |W n|) atTop (𝓝 0) := by
    simpa using hWLim.abs.const_mul G
  have hJzero : J 0 = 0 := by
    have hle : |J 0| ≤ 0 :=
      ge_of_tendsto hboundLim (Filter.Eventually.of_forall hJbound)
    exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
  have hWallZero : ∀ n, W n = 0 := by
    intro n
    have hJn : J n = 0 := by rw [hJconst n, hJzero]
    have hq : 2 ≤ K - 1 + n := by omega
    have hoff := l2SymmetricOff_pos G (K - 1 + n) hG hq
    unfold J at hJn
    exact (mul_eq_zero.mp hJn).resolve_left (ne_of_gt hoff)
  let c : ℝ := b 0 / a 0
  have hzero : b 0 = c * a 0 := by unfold c; field_simp
  have hone : b 1 = c * a 1 := by
    have hw := hWallZero 0
    dsimp [W] at hw
    unfold c
    field_simp
    nlinarith
  refine ⟨c, fun n => Nat.twoStepInduction
    (P := fun j => b j = c * a j) hzero hone ?_ n⟩
  intro n hn hnSucc
  have ha := haRec n
  have hb := hbRec n
  have hq : 2 ≤ K + n := by omega
  have hoff := l2SymmetricOff_pos G (K + n) hG hq
  have hdiff :
      l2SymmetricOff G (K + n) * (b (n + 2) - c * a (n + 2)) = 0 := by
    rw [hn, hnSucc] at hb
    linear_combination hb - c * ha
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hdiff).resolve_left (ne_of_gt hoff))

private theorem left_tail_eq_mul_l2TailRow
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hmatch :
      (mode4LeftPair (mode4JacobiG mProject) Λ K).2 =
        mode4RightTailLimit mProject Λ K *
          (mode4LeftPair (mode4JacobiG mProject) Λ (K - 1)).2) :
    ∀ n,
      (mode4LeftPair (mode4JacobiG mProject) Λ (K - 1 + n)).2 =
        (mode4LeftPair (mode4JacobiG mProject) Λ (K - 1)).2 *
          l2TailRow mProject Λ K n := by
  let G := mode4JacobiG mProject
  let r : ℕ → ℝ := fun q => (mode4LeftPair G Λ q).2
  have hG : 0 < G := by unfold G mode4JacobiG; positivity
  have hraw : ∀ q,
      mode4JacobiLower G q * r (q - 1) -
        mode4JacobiCenter G Λ q * r q +
        mode4JacobiUpper G q * r (q + 1) = 0 := by
    simpa [G, r] using leftPair_row_recurrence mProject Λ hm
  change r K = mode4RightTailLimit mProject Λ K * r (K - 1) at hmatch
  intro n
  exact Nat.twoStepInduction
    (P := fun j =>
      r (K - 1 + j) = r (K - 1) * l2TailRow mProject Λ K j)
    (by simp)
    (by
      change r (K - 1 + 1) = r (K - 1) * l2TailRow mProject Λ K 1
      have hidx : K - 1 + 1 = K := by omega
      rw [hidx, hmatch, l2TailRow_succ]
      simp
      ring)
    (fun j hj hjSucc => by
      change r (K - 1 + (j + 2)) =
        r (K - 1) * l2TailRow mProject Λ K (j + 2)
      change r (K - 1 + j) =
        r (K - 1) * l2TailRow mProject Λ K j at hj
      change r (K - 1 + (j + 1)) =
        r (K - 1) * l2TailRow mProject Λ K (j + 1) at hjSucc
      have hr :
          mode4JacobiLower G (K + j) * r (K - 1 + j) -
            mode4JacobiCenter G Λ (K + j) * r (K - 1 + (j + 1)) +
            mode4JacobiUpper G (K + j) * r (K - 1 + (j + 2)) = 0 := by
        have hprev : K + j - 1 = K - 1 + j := by omega
        have hhere : K + j = K - 1 + (j + 1) := by omega
        have hnext : K + j + 1 = K - 1 + (j + 2) := by omega
        simpa only [hprev, hhere, hnext] using hraw (K + j)
      have ht :
          mode4JacobiLower G (K + j) * l2TailRow mProject Λ K j -
            mode4JacobiCenter G Λ (K + j) * l2TailRow mProject Λ K (j + 1) +
            mode4JacobiUpper G (K + j) * l2TailRow mProject Λ K (j + 2) = 0 := by
        simpa [G] using l2TailRow_recurrence mProject K Λ hm hK hsep hΛ j
      rw [hj, hjSucc] at hr
      have hdiff :
          mode4JacobiUpper G (K + j) *
            (r (K - 1 + (j + 2)) -
              r (K - 1) * l2TailRow mProject Λ K (j + 2)) = 0 := by
        linear_combination hr - r (K - 1) * ht
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp hdiff).resolve_left
          (ne_of_gt (mode4JacobiUpper_pos G (K + j) hG))))
    n

/-- The pole-safe even DLMF characteristic equation holds exactly when its
parity-normalized global left recurrence row is square summable. -/
theorem
    mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20) :
    mode4DLMF3035EvenCharacteristicEquation
        (mode4JacobiG mProject) Λ (2 * (K - 1))
      ↔
    Summable
      (fun q : ℕ =>
        ‖mode4DLMF3035EvenLeftCoefficient
            (mode4JacobiG mProject) Λ q‖ ^ 2) := by
  let G := mode4JacobiG mProject
  let r : ℕ → ℝ := fun q => (mode4LeftPair G Λ q).2
  have hG : 0 < G := by unfold G mode4JacobiG; positivity
  have hEven : Even (2 * (K - 1)) := ⟨K - 1, by omega⟩
  have hindex : 2 * (K - 1) / 2 + 1 = K := by omega
  have hfst : (mode4LeftPair G Λ K).1 = r (K - 1) := by
    simpa [r] using leftPair_fst_eq_prev G Λ K (by omega)
  constructor
  · intro hchar
    have hsourceMatch :
        (mode4DLMF3035EvenLeftPair G Λ K).2 =
          mode4DLMF3035EvenRightRatio G Λ K *
            (mode4DLMF3035EvenLeftPair G Λ K).1 := by
      unfold mode4DLMF3035EvenCharacteristicEquation at hchar
      simpa only [hindex] using hchar.2
    have hmatch : r K = mode4RightTailLimit mProject Λ K * r (K - 1) := by
      rw [mode4DLMF3035EvenLeftPair_eq_mode4LeftPair] at hsourceMatch
      rw [mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
        mProject K Λ hm hK hsep hΛ] at hsourceMatch
      simpa [r, hfst] using hsourceMatch
    have hsplice := left_tail_eq_mul_l2TailRow mProject K Λ hm hK hsep hΛ
      (by simpa [G, r] using hmatch)
    have htailBase := l2TailRow_sq_summable mProject K Λ hm hK hsep hΛ
    have htailScaled := htailBase.mul_left (r (K - 1) ^ 2)
    have htail : Summable (fun n => (r (K - 1 + n)) ^ 2) := by
      simpa [G, r, hsplice, mul_pow] using htailScaled
    have htail' : Summable (fun n => (r (n + (K - 1))) ^ 2) := by
      simpa [Nat.add_comm] using htail
    have hall : Summable (fun q => (r q) ^ 2) :=
      (summable_nat_add_iff (f := fun q => (r q) ^ 2) (K - 1)).1 htail'
    simpa [mode4DLMF3035EvenLeftCoefficient,
      mode4DLMF3035EvenLeftPair_eq_mode4LeftPair,
      G, r, Real.norm_eq_abs, sq_abs] using hall
  · intro hs
    have hrSq : Summable (fun q => (r q) ^ 2) := by
      simpa [mode4DLMF3035EvenLeftCoefficient,
        mode4DLMF3035EvenLeftPair_eq_mode4LeftPair,
        G, r, Real.norm_eq_abs, sq_abs] using hs
    have hrShift' : Summable (fun n => (r (n + (K - 1))) ^ 2) :=
      (summable_nat_add_iff (f := fun q => (r q) ^ 2) (K - 1)).2 hrSq
    have hrShift : Summable (fun n => (r (K - 1 + n)) ^ 2) := by
      simpa [Nat.add_comm] using hrShift'
    let b : ℕ → ℝ := fun n => l2Scale K n * r (K - 1 + n)
    have hbSq : Summable (fun n => (b n) ^ 2) := by
      refine Summable.of_nonneg_of_le (fun n => sq_nonneg _) (fun n => ?_) hrShift
      have hs0 := (l2Scale_pos K n hK).le
      have hs1 := l2Scale_le_one K n hK
      have hs2 : l2Scale K n ^ 2 ≤ 1 := by nlinarith
      unfold b
      rw [mul_pow]
      simpa using mul_le_mul_of_nonneg_right hs2 (sq_nonneg (r (K - 1 + n)))
    have hraw : ∀ q,
        mode4JacobiLower G q * r (q - 1) -
          mode4JacobiCenter G Λ q * r q +
          mode4JacobiUpper G q * r (q + 1) = 0 := by
      simpa [G, r] using leftPair_row_recurrence mProject Λ hm
    have hbRec : ∀ n,
        l2SymmetricOff G (K - 1 + n) * b n -
          mode4JacobiCenter G Λ (K + n) * b (n + 1) +
          l2SymmetricOff G (K + n) * b (n + 2) = 0 := by
      intro n
      have hr :
          mode4JacobiLower G (K + n) * r (K - 1 + n) -
            mode4JacobiCenter G Λ (K + n) * r (K - 1 + (n + 1)) +
            mode4JacobiUpper G (K + n) * r (K - 1 + (n + 2)) = 0 := by
        have hprev : K + n - 1 = K - 1 + n := by omega
        have hhere : K + n = K - 1 + (n + 1) := by omega
        have hnext : K + n + 1 = K - 1 + (n + 2) := by omega
        simpa only [hprev, hhere, hnext] using hraw (K + n)
      have hlower := l2Scale_lower_balance G K n hG hK
      have hupper := l2Scale_upper_balance G K n hG hK
      unfold b
      calc
        _ = l2Scale K (n + 1) *
            (mode4JacobiLower G (K + n) * r (K - 1 + n) -
              mode4JacobiCenter G Λ (K + n) * r (K - 1 + (n + 1)) +
              mode4JacobiUpper G (K + n) * r (K - 1 + (n + 2))) := by
          rw [show
            l2SymmetricOff G (K - 1 + n) *
                (l2Scale K n * r (K - 1 + n)) =
              (l2SymmetricOff G (K - 1 + n) * l2Scale K n) *
                r (K - 1 + n) by ring,
            ← hlower]
          rw [show
            l2SymmetricOff G (K + n) *
                (l2Scale K (n + 2) * r (K - 1 + (n + 2))) =
              (l2SymmetricOff G (K + n) * l2Scale K (n + 2)) *
                r (K - 1 + (n + 2)) by ring,
            ← hupper]
          ring
        _ = 0 := by rw [hr, mul_zero]
    have ha0 : l2HermitianTailRow mProject Λ K 0 ≠ 0 := by
      rw [l2HermitianTailRow_zero mProject K Λ hK]
      norm_num
    have haRec := l2HermitianTailRow_recurrence mProject K Λ hm hK hsep hΛ
    have haSq := l2HermitianTailRow_sq_summable mProject K Λ hm hK hsep hΛ
    rcases l2Hermitian_sqSummable_unique_up_to_scale
      G Λ K hG hK (l2HermitianTailRow mProject Λ K) b
      ha0 haRec hbRec haSq hbSq with ⟨c, hc⟩
    have hc0 := hc 0
    have hc1 := hc 1
    have hcEq : c = r (K - 1) := by
      unfold b at hc0
      rw [l2Scale_zero K hK, l2HermitianTailRow_zero mProject K Λ hK] at hc0
      norm_num at hc0
      linarith
    have hcanon1 :
        l2HermitianTailRow mProject Λ K 1 =
          l2Scale K 1 * mode4RightTailLimit mProject Λ K := by
      unfold l2HermitianTailRow
      rw [l2TailRow_succ]
      simp
    have hidx1 : K - 1 + 1 = K := by omega
    unfold b at hc1
    rw [hidx1, hcanon1, hcEq] at hc1
    have hs1ne := (l2Scale_pos K 1 hK).ne'
    have hmatch : r K = mode4RightTailLimit mProject Λ K * r (K - 1) := by
      apply (mul_left_cancel₀ hs1ne)
      linear_combination hc1
    refine ⟨hEven, ?_⟩
    dsimp only
    rw [hindex]
    rw [mode4DLMF3035EvenLeftPair_eq_mode4LeftPair]
    rw [mode4DLMF3035EvenRightRatio_eq_mode4RightTailLimit
      mProject K Λ hm hK hsep hΛ]
    simpa [G, r, hfst] using hmatch

#print axioms mode4DLMF3035EvenCharacteristicEquation_iff_leftCoefficient_sqSummable

end

end Q3.RouteB
