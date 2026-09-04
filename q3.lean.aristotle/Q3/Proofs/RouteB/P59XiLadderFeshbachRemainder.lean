import Mathlib

set_option linter.mathlibStandardSet false

/-!
# Goal 058 · P59 · exact Xi-ladder compression, block equations, Feshbach remainder

This file formalizes the finite linear algebra behind the judge's
`Q2_A_LADDER_COMPRESSION` block: the three-row orthonormal ladder synthesis,
its compression blocks, the two projected eigen-equations of an *exact*
eigenpair, the exact `d2` remainder identity, the Feshbach elimination of the
complement, and the directional-accuracy plant.

Everything is stated over `ℝ` for a finite symmetric matrix
`K : Matrix (Fin n) (Fin n) ℝ`.  Writing

* `B : Matrix (Fin n) (Fin 3) ℝ` with `Bᵀ * B = 1` for the ladder synthesis,
* `P = B * Bᵀ`, `Q = 1 - P` for the ladder projection and its complement,
* `A = Bᵀ * K * B`, `C = Bᵀ * K * Q`, `D = Q * K * Q` for the blocks,
* `p = Bᵀ *ᵥ u`, `r = Q *ᵥ u` for the coordinates of an exact eigenvector,

the content is:

1. `ladderProj_isSymm`, `ladderProj_mul_self`, `ladderComplement_isSymm`,
   `ladderComplement_mul_self`, `ladderProj_mul_ladderComplement`;
2. the blocks `ladderBlockA`, `ladderBlockC`, `ladderBlockD`;
3. `ladder_projected_eigen_equation_head` : `(A - lam • 1) *ᵥ p + C *ᵥ r = 0`
   and `ladder_projected_eigen_equation_tail` : `Cᵀ *ᵥ p + (D - lam • 1) *ᵥ r = 0`
   (an `n`-vector identity, `r` already living in the range of `Q`);
4. `ladder_d2_eq_ladderRow_overlap` : `⟪e0, p⟫ = ⟪B *ᵥ e0, u⟫`,
   `ladder_d2_exact_remainder` : `⟪e0, p⟫ - ⟪e0, z⟫ = ⟪e0, p - z⟫`,
   its normalized form and the Cauchy–Schwarz bound;
5. `ladder_feshbach_tail_eq` : `r = -(G * Cᵀ) *ᵥ p` and
   `ladder_feshbach_effective_equation` : `(A - C * G * Cᵀ - lam • 1) *ᵥ p = 0`,
   under the *weakest* clean hypothesis `G *ᵥ ((D - lam • 1) *ᵥ r) = r`, which
   is in turn supplied by a `Q`-block inverse `G * (D - lam • 1) * Q = Q`;
6. `directionalPlantVector` : the family `u θ = √(1-θ²) • b + θ • y` with
   `⟪u θ, u θ⟫ = 1`, `⟪u θ, b⟫ = √(1-θ²) → 1` and `⟪y, u θ⟫ = θ`.

Nothing here assumes the scalar remainder is small, identifies the raw
compressed Ritz vector `z` with the exact eigenvector, or introduces a
complement floor or any `O(T_m)` premise.  `z` is an arbitrary vector
throughout; the remainder identities are exact and unconditional.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

/-! ### 1. The orthonormal ladder synthesis and its two projections -/

/-- Ladder projection `P = B Bᵀ` attached to a synthesis matrix `B`. -/
def ladderProj {n : ℕ} (B : Matrix (Fin n) (Fin 3) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  B * Bᵀ

/-- Complement `Q = 1 - P` of the ladder projection. -/
def ladderComplement {n : ℕ} (B : Matrix (Fin n) (Fin 3) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  1 - ladderProj B

variable {n : ℕ}

theorem ladderProj_isSymm (B : Matrix (Fin n) (Fin 3) ℝ) : (ladderProj B).IsSymm := by
  unfold Matrix.IsSymm ladderProj
  rw [Matrix.transpose_mul, Matrix.transpose_transpose]

theorem ladderProj_mul_self (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) :
    ladderProj B * ladderProj B = ladderProj B := by
  unfold ladderProj
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc Bᵀ B Bᵀ, hB, Matrix.one_mul]

theorem ladderComplement_isSymm (B : Matrix (Fin n) (Fin 3) ℝ) :
    (ladderComplement B).IsSymm := by
  unfold Matrix.IsSymm ladderComplement
  rw [Matrix.transpose_sub, Matrix.transpose_one, (ladderProj_isSymm B).eq]

theorem ladderComplement_mul_self (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) :
    ladderComplement B * ladderComplement B = ladderComplement B := by
  have h := ladderProj_mul_self B hB
  unfold ladderComplement
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]
  abel

theorem ladderProj_mul_ladderComplement (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) :
    ladderProj B * ladderComplement B = 0 := by
  unfold ladderComplement
  rw [Matrix.mul_sub, Matrix.mul_one, ladderProj_mul_self B hB, sub_self]

theorem ladderComplement_mul_ladderProj (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) :
    ladderComplement B * ladderProj B = 0 := by
  unfold ladderComplement
  rw [Matrix.sub_mul, Matrix.one_mul, ladderProj_mul_self B hB, sub_self]

/-- `P + Q = 1`: the ladder projection and its complement resolve the identity. -/
theorem ladderProj_add_ladderComplement (B : Matrix (Fin n) (Fin 3) ℝ) :
    ladderProj B + ladderComplement B = 1 := by
  unfold ladderComplement
  abel

/-! ### 2. The compression blocks -/

/-- In-ladder block `A = Bᵀ K B`. -/
def ladderBlockA (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  Bᵀ * K * B

/-- Coupling block `C = Bᵀ K Q`. -/
def ladderBlockC (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ) :
    Matrix (Fin 3) (Fin n) ℝ :=
  Bᵀ * K * ladderComplement B

/-- Complement block `D = Q K Q`. -/
def ladderBlockD (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  ladderComplement B * K * ladderComplement B

theorem ladderBlockA_isSymm (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ)
    (hK : K.IsSymm) : (ladderBlockA K B).IsSymm := by
  unfold Matrix.IsSymm ladderBlockA
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq,
    Matrix.mul_assoc]

theorem ladderBlockD_isSymm (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ)
    (hK : K.IsSymm) : (ladderBlockD K B).IsSymm := by
  unfold Matrix.IsSymm ladderBlockD
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hK.eq, (ladderComplement_isSymm B).eq,
    Matrix.mul_assoc]

/-- `Cᵀ = Q K B`. -/
theorem ladderBlockC_transpose (K : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin 3) ℝ)
    (hK : K.IsSymm) :
    (ladderBlockC K B)ᵀ = ladderComplement B * K * B := by
  unfold ladderBlockC
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, hK.eq,
    (ladderComplement_isSymm B).eq, Matrix.mul_assoc]

/-! ### 3. The two projected eigen-equations of an exact eigenpair -/

/-- Head row of the block resolution: `A Bᵀ + C Q = Bᵀ K`. -/
private theorem ladder_head_rowSum (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) :
    ladderBlockA K B * Bᵀ + ladderBlockC K B * ladderComplement B = Bᵀ * K := by
  have hQQ := ladderComplement_mul_self B hB
  have hPQ := ladderProj_add_ladderComplement B
  calc ladderBlockA K B * Bᵀ + ladderBlockC K B * ladderComplement B
      = Bᵀ * K * (ladderProj B + ladderComplement B) := by
        unfold ladderBlockA ladderBlockC ladderProj
        rw [Matrix.mul_add, Matrix.mul_assoc (Bᵀ * K) (ladderComplement B) (ladderComplement B),
          hQQ, Matrix.mul_assoc (Bᵀ * K) B Bᵀ]
    _ = Bᵀ * K := by rw [hPQ, Matrix.mul_one]

/-- Tail row of the block resolution: `Cᵀ Bᵀ + D Q = Q K`. -/
private theorem ladder_tail_rowSum (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) (hK : K.IsSymm) :
    (ladderBlockC K B)ᵀ * Bᵀ + ladderBlockD K B * ladderComplement B
      = ladderComplement B * K := by
  have hQQ := ladderComplement_mul_self B hB
  have hPQ := ladderProj_add_ladderComplement B
  calc (ladderBlockC K B)ᵀ * Bᵀ + ladderBlockD K B * ladderComplement B
      = ladderComplement B * K * (ladderProj B + ladderComplement B) := by
        rw [ladderBlockC_transpose K B hK]
        unfold ladderBlockD ladderProj
        rw [Matrix.mul_add,
          Matrix.mul_assoc (ladderComplement B * K) (ladderComplement B) (ladderComplement B),
          hQQ, Matrix.mul_assoc (ladderComplement B * K) B Bᵀ]
    _ = ladderComplement B * K := by rw [hPQ, Matrix.mul_one]

/-- **Head projected eigen-equation.**  For an exact eigenpair `K u = lam • u` the
ladder coordinates `p = Bᵀ *ᵥ u` and `r = Q *ᵥ u` satisfy
`(A - lam • 1) *ᵥ p + C *ᵥ r = 0`. -/
theorem ladder_projected_eigen_equation_head (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1)
    (lam : ℝ) (u : Fin n → ℝ) (hu : K *ᵥ u = lam • u) :
    (ladderBlockA K B - lam • 1) *ᵥ (Bᵀ *ᵥ u)
      + ladderBlockC K B *ᵥ (ladderComplement B *ᵥ u) = 0 := by
  have hsum : ladderBlockA K B *ᵥ (Bᵀ *ᵥ u)
      + ladderBlockC K B *ᵥ (ladderComplement B *ᵥ u) = lam • (Bᵀ *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
      ladder_head_rowSum K B hB, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_add_eq_add_sub, hsum,
    sub_self]

/-- **Tail projected eigen-equation.**  As an `n`-vector identity (`r = Q *ᵥ u`
already lives in the range of `Q`):  `Cᵀ *ᵥ p + (D - lam • 1) *ᵥ r = 0`. -/
theorem ladder_projected_eigen_equation_tail (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) (hK : K.IsSymm)
    (lam : ℝ) (u : Fin n → ℝ) (hu : K *ᵥ u = lam • u) :
    (ladderBlockC K B)ᵀ *ᵥ (Bᵀ *ᵥ u)
      + (ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u) = 0 := by
  have hsum : (ladderBlockC K B)ᵀ *ᵥ (Bᵀ *ᵥ u)
      + ladderBlockD K B *ᵥ (ladderComplement B *ᵥ u)
        = lam • (ladderComplement B *ᵥ u) := by
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec,
      ladder_tail_rowSum K B hB hK, ← Matrix.mulVec_mulVec, hu, Matrix.mulVec_smul]
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← add_sub_assoc, hsum,
    sub_self]

/-! ### 4. The exact `d2` remainder -/

/-- First ladder coordinate direction `e0` in `Fin 3`. -/
def ladderE0 : Fin 3 → ℝ := Pi.single 0 1

/-- Euclidean length on the three-dimensional ladder coordinate space. -/
def ladderNorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

theorem ladderNorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ ladderNorm v := Real.sqrt_nonneg _

theorem ladderE0_dotProduct (v : Fin 3 → ℝ) : ladderE0 ⬝ᵥ v = v 0 := by
  unfold ladderE0
  exact single_one_dotProduct 0 v

/-- Cauchy–Schwarz against the unit vector `e0`. -/
theorem abs_ladderE0_dotProduct_le (v : Fin 3 → ℝ) :
    |ladderE0 ⬝ᵥ v| ≤ ladderNorm v := by
  have hsum : (v 0) ^ 2 ≤ v ⬝ᵥ v := by
    have hpos : ∀ i ∈ (Finset.univ : Finset (Fin 3)), 0 ≤ v i * v i :=
      fun i _ => mul_self_nonneg _
    have h := Finset.single_le_sum hpos (Finset.mem_univ (0 : Fin 3))
    simpa [dotProduct, sq] using h
  calc |ladderE0 ⬝ᵥ v| = Real.sqrt ((v 0) ^ 2) := by
        rw [ladderE0_dotProduct, Real.sqrt_sq_eq_abs]
    _ ≤ Real.sqrt (v ⬝ᵥ v) := Real.sqrt_le_sqrt hsum
    _ = ladderNorm v := rfl

/-- `d2 = ⟪e0, p⟫` is the overlap of the exact eigenvector with the first ladder
row `y = B *ᵥ e0`. -/
theorem ladder_d2_eq_ladderRow_overlap (B : Matrix (Fin n) (Fin 3) ℝ) (u : Fin n → ℝ) :
    ladderE0 ⬝ᵥ (Bᵀ *ᵥ u) = (B *ᵥ ladderE0) ⬝ᵥ u := by
  rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- **Exact remainder identity.**  For *any* raw compressed vector `z` the defect
of the compressed overlap is exactly the `e0`-coordinate of the coordinate
defect.  No smallness, no identification of `z` with `p`. -/
theorem ladder_d2_exact_remainder (p z : Fin 3 → ℝ) :
    ladderE0 ⬝ᵥ p - ladderE0 ⬝ᵥ z = ladderE0 ⬝ᵥ (p - z) := by
  rw [dotProduct_sub]

/-- Normalized form of the exact remainder: with `s = ‖p‖ ≠ 0` and `p̂ = s⁻¹ • p`,
`d2 - ⟪e0,z⟫ = (s - 1) * ⟪e0,z⟫ + s * ⟪e0, p̂ - z⟫`. -/
theorem ladder_d2_exact_remainder_normalized (p z p' : Fin 3 → ℝ)
    (s : ℝ) (hs : s = ladderNorm p) (hs0 : s ≠ 0) (hp' : p' = s⁻¹ • p) :
    ladderE0 ⬝ᵥ p - ladderE0 ⬝ᵥ z
      = (s - 1) * (ladderE0 ⬝ᵥ z) + s * (ladderE0 ⬝ᵥ (p' - z)) := by
  subst hs
  have hsp : ladderNorm p • p' = p := by
    rw [hp', smul_smul, mul_inv_cancel₀ hs0, one_smul]
  have hE : ladderNorm p * (ladderE0 ⬝ᵥ p') = ladderE0 ⬝ᵥ p := by
    rw [← smul_eq_mul, ← dotProduct_smul, hsp]
  rw [dotProduct_sub, ← hE]
  ring

/-- Cauchy–Schwarz bound for the normalized exact remainder. -/
theorem ladder_d2_remainder_bound (p z p' : Fin 3 → ℝ)
    (s : ℝ) (hs : s = ladderNorm p) (hs0 : s ≠ 0) (hp' : p' = s⁻¹ • p) :
    |ladderE0 ⬝ᵥ p - ladderE0 ⬝ᵥ z|
      ≤ |1 - s| * |ladderE0 ⬝ᵥ z| + s * ladderNorm (p' - z) := by
  have hsnn : 0 ≤ s := hs ▸ ladderNorm_nonneg p
  have hid := ladder_d2_exact_remainder_normalized p z p' s hs hs0 hp'
  have hcs := abs_ladderE0_dotProduct_le (p' - z)
  calc |ladderE0 ⬝ᵥ p - ladderE0 ⬝ᵥ z|
      = |(s - 1) * (ladderE0 ⬝ᵥ z) + s * (ladderE0 ⬝ᵥ (p' - z))| := by rw [hid]
    _ ≤ |(s - 1) * (ladderE0 ⬝ᵥ z)| + |s * (ladderE0 ⬝ᵥ (p' - z))| := abs_add_le _ _
    _ = |1 - s| * |ladderE0 ⬝ᵥ z| + s * |ladderE0 ⬝ᵥ (p' - z)| := by
        rw [abs_mul, abs_mul, abs_sub_comm, abs_of_nonneg hsnn]
    _ ≤ |1 - s| * |ladderE0 ⬝ᵥ z| + s * ladderNorm (p' - z) := by
        have hmul := mul_le_mul_of_nonneg_left hcs hsnn
        linarith

/-! ### 5. Feshbach elimination of the complement -/

/-- A `Q`-block inverse `G * (D - lam • 1) * Q = Q` supplies the weak Feshbach
hypothesis on every vector of the form `r = Q *ᵥ u`. -/
theorem ladder_feshbach_hypothesis_of_blockInverse (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (lam : ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G * (ladderBlockD K B - lam • 1) * ladderComplement B = ladderComplement B)
    (u : Fin n → ℝ) :
    G *ᵥ ((ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u))
      = ladderComplement B *ᵥ u := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hG]

/-- **Feshbach tail.**  Under the weakest clean hypothesis — `G` inverts
`D - lam • 1` on the single vector `r = Q *ᵥ u` — the complement component is
determined by the ladder component: `r = -(G * Cᵀ) *ᵥ p`. -/
theorem ladder_feshbach_tail_eq (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) (hK : K.IsSymm)
    (lam : ℝ) (u : Fin n → ℝ) (hu : K *ᵥ u = lam • u)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G *ᵥ ((ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u))
        = ladderComplement B *ᵥ u) :
    ladderComplement B *ᵥ u
      = -((G * (ladderBlockC K B)ᵀ) *ᵥ (Bᵀ *ᵥ u)) := by
  have htail := ladder_projected_eigen_equation_tail K B hB hK lam u hu
  have hDr : (ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u)
      = -((ladderBlockC K B)ᵀ *ᵥ (Bᵀ *ᵥ u)) := eq_neg_of_add_eq_zero_right htail
  rw [← hG, hDr, Matrix.mulVec_neg, Matrix.mulVec_mulVec]

/-- **Feshbach effective equation.**  The exact in-ladder component `p` is an
eigenvector of the Feshbach-corrected matrix `A - C G Cᵀ`, not of the raw
compression `A`. -/
theorem ladder_feshbach_effective_equation (K : Matrix (Fin n) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin 3) ℝ) (hB : Bᵀ * B = 1) (hK : K.IsSymm)
    (lam : ℝ) (u : Fin n → ℝ) (hu : K *ᵥ u = lam • u)
    (G : Matrix (Fin n) (Fin n) ℝ)
    (hG : G *ᵥ ((ladderBlockD K B - lam • 1) *ᵥ (ladderComplement B *ᵥ u))
        = ladderComplement B *ᵥ u) :
    (ladderBlockA K B - ladderBlockC K B * G * (ladderBlockC K B)ᵀ - lam • 1)
        *ᵥ (Bᵀ *ᵥ u) = 0 := by
  have hhead := ladder_projected_eigen_equation_head K B hB lam u hu
  have hr := ladder_feshbach_tail_eq K B hB hK lam u hu G hG
  have hCr : ladderBlockC K B *ᵥ (ladderComplement B *ᵥ u)
      = -((ladderBlockC K B * G * (ladderBlockC K B)ᵀ) *ᵥ (Bᵀ *ᵥ u)) := by
    rw [hr, Matrix.mulVec_neg,
      Matrix.mulVec_mulVec (Bᵀ *ᵥ u) (ladderBlockC K B) (G * (ladderBlockC K B)ᵀ),
      ← Matrix.mul_assoc (ladderBlockC K B) G ((ladderBlockC K B)ᵀ)]
  rw [hCr, ← sub_eq_add_neg] at hhead
  have hM : ladderBlockA K B - ladderBlockC K B * G * (ladderBlockC K B)ᵀ - lam • 1
      = (ladderBlockA K B - lam • 1) - ladderBlockC K B * G * (ladderBlockC K B)ᵀ := by
    abel
  rw [hM, Matrix.sub_mulVec]
  exact hhead

/-! ### 6. The `u θ` directional-accuracy plant -/

/-- The family `u θ = √(1-θ²) • b + θ • y`. -/
def directionalPlantVector (b y : Fin n → ℝ) (θ : ℝ) : Fin n → ℝ :=
  Real.sqrt (1 - θ ^ 2) • b + θ • y

theorem directionalPlantVector_self (b y : Fin n → ℝ)
    (hb : b ⬝ᵥ b = 1) (hy : y ⬝ᵥ y = 1) (hby : b ⬝ᵥ y = 0)
    (θ : ℝ) (hθ : θ ^ 2 ≤ 1) :
    directionalPlantVector b y θ ⬝ᵥ directionalPlantVector b y θ = 1 := by
  have hyb : y ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact hby
  have h1 : (0 : ℝ) ≤ 1 - θ ^ 2 := by linarith
  have hc : Real.sqrt (1 - θ ^ 2) * Real.sqrt (1 - θ ^ 2) = 1 - θ ^ 2 :=
    Real.mul_self_sqrt h1
  simp only [directionalPlantVector, add_dotProduct, dotProduct_add, smul_dotProduct,
    dotProduct_smul, smul_eq_mul, hb, hy, hby, hyb]
  linear_combination hc

theorem directionalPlantVector_dotProduct_left (b y : Fin n → ℝ)
    (hb : b ⬝ᵥ b = 1) (hby : b ⬝ᵥ y = 0) (θ : ℝ) :
    directionalPlantVector b y θ ⬝ᵥ b = Real.sqrt (1 - θ ^ 2) := by
  have hyb : y ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact hby
  simp only [directionalPlantVector, add_dotProduct, smul_dotProduct, smul_eq_mul, hb, hyb]
  ring

theorem directionalPlantVector_dotProduct_right (b y : Fin n → ℝ)
    (hy : y ⬝ᵥ y = 1) (hby : b ⬝ᵥ y = 0) (θ : ℝ) :
    y ⬝ᵥ directionalPlantVector b y θ = θ := by
  have hyb : y ⬝ᵥ b = 0 := by rw [dotProduct_comm]; exact hby
  simp only [directionalPlantVector, dotProduct_add, dotProduct_smul, smul_eq_mul, hy, hyb]
  ring

/-- The directional accuracy toward `b` tends to `1`, while the `y`-overlap is
exactly `θ`.  Perfect directional accuracy therefore gives no relative control
of the small orthogonal coordinate. -/
theorem directionalPlantVector_tendsto (b y : Fin n → ℝ)
    (hb : b ⬝ᵥ b = 1) (hby : b ⬝ᵥ y = 0) :
    Filter.Tendsto (fun θ : ℝ => directionalPlantVector b y θ ⬝ᵥ b)
      (nhds 0) (nhds 1) := by
  have hfun : (fun θ : ℝ => directionalPlantVector b y θ ⬝ᵥ b)
      = fun θ : ℝ => Real.sqrt (1 - θ ^ 2) := by
    funext θ
    exact directionalPlantVector_dotProduct_left b y hb hby θ
  rw [hfun]
  have hcont : Continuous fun θ : ℝ => Real.sqrt (1 - θ ^ 2) := by
    exact Real.continuous_sqrt.comp (continuous_const.sub (continuous_pow 2))
  simpa using hcont.continuousAt.tendsto (x := (0 : ℝ))

#print axioms ladderProj
#print axioms ladderComplement
#print axioms ladderProj_isSymm
#print axioms ladderProj_mul_self
#print axioms ladderComplement_isSymm
#print axioms ladderComplement_mul_self
#print axioms ladderProj_mul_ladderComplement
#print axioms ladderComplement_mul_ladderProj
#print axioms ladderProj_add_ladderComplement
#print axioms ladderBlockA
#print axioms ladderBlockC
#print axioms ladderBlockD
#print axioms ladderBlockA_isSymm
#print axioms ladderBlockD_isSymm
#print axioms ladderBlockC_transpose
#print axioms ladder_projected_eigen_equation_head
#print axioms ladder_projected_eigen_equation_tail
#print axioms ladderE0
#print axioms ladderNorm
#print axioms ladderNorm_nonneg
#print axioms ladderE0_dotProduct
#print axioms abs_ladderE0_dotProduct_le
#print axioms ladder_d2_eq_ladderRow_overlap
#print axioms ladder_d2_exact_remainder
#print axioms ladder_d2_exact_remainder_normalized
#print axioms ladder_d2_remainder_bound
#print axioms ladder_feshbach_hypothesis_of_blockInverse
#print axioms ladder_feshbach_tail_eq
#print axioms ladder_feshbach_effective_equation
#print axioms directionalPlantVector
#print axioms directionalPlantVector_self
#print axioms directionalPlantVector_dotProduct_left
#print axioms directionalPlantVector_dotProduct_right
#print axioms directionalPlantVector_tendsto

end Q3.RouteB
