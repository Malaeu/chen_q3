import Mathlib

set_option linter.mathlibStandardSet false

/-!
# P59 sign-free Ritz inequality (GOAL058, REQ-2026-09-04-SIGNFREE)

The judge's directive `PROSHKA_VERDICT_GOAL058_SIGNFREE_RITZ_INSIDE_CCM_UNIFORM_ERROR_ATOM_2026-09-04.md`,
section S1, asks for the finite spectral inequality

  `(lambda_2 - lambda_1) * (1 - w_1) <= sum_j (lambda_j - lambda_1) * w_j = R(q) - lambda_1`   (SF)

with **no** sign hypothesis on `lambda_1` or `lambda_2` anywhere in the head.
Here `u` is an ordered orthonormal eigenbasis of a finite-dimensional real
inner product space, `q` is a unit vector, `w_j = ⟪u j, q⟫ ^ 2` and
`R q = ⟪q, K q⟫`.

Notation: `⟪x, y⟫` is the real inner product (`open scoped RealInnerProductSpace`).

The already existing declaration
`Q3.RouteB.hermitian_relative_ritz_projective_defect_le_rayleigh_excess_div_gap`
(`Q3/Proofs/RouteB/RelativeRitzFinite.lean`) proves only the *divided* complex
Hermitian form, and it carries `0 < lambda1` plus a strict gap in its head.
This file supplies what is missing: the undivided sign-free inequality (SF),
the division corollary isolated behind `0 < lambda2 - lambda1`, the projective
distance corollary, and the three mandatory controls.

Contents:

* `signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess` — (SF), sign-free.
* `signFreeRitz_rayleighExcess_eq_weighted_sum` — the middle equality of (SF).
* `signFreeRitz_projectiveDefect_le_rayleighExcess_div_gap` — division form,
  the only statement carrying `0 < lambda2 - lambda1`.
* `signFreeRitz_dist_sq_eq_two_mul_one_sub_sqrt` and
  `signFreeRitz_dist_sq_le_two_mul_projectiveDefect` — projective distance.
* Control (i) `plantNegBottom_equality_control` — `K = diag (-2, -1)`, equality.
* Control (ii) `signFreeRitz_zero_gap_control` — `lambda_2 = lambda_1`, no division.
* Control (iii) `plantThreeLevel_defect_small_ratio_one` and
  `plantThreeLevel_defect_arbitrarily_small_ratio_one` — `p -> 0` does not
  force the Ritz ratio to zero.

No asymptotic or source-specific estimate is a hypothesis or a conclusion here.
-/

noncomputable section

namespace Q3.RouteB.SignFreeRitz

open scoped RealInnerProductSpace

/-! ## 1. The weighted-sum core -/

/-- Core of (SF) at the level of weights only: if every index other than the
bottom index `j₁` carries an eigenvalue at least `l2`, and the weights are
nonnegative and sum to one, then the gap times the defect is bounded by the
weighted excess sum.  No sign of any eigenvalue is used. -/
theorem gap_mul_defect_le_weighted_excess_sum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lam w : ι → ℝ) (j₁ : ι) (l2 : ℝ)
    (hlam : ∀ j, j ≠ j₁ → l2 ≤ lam j)
    (hw : ∀ j, 0 ≤ w j) (hsum : ∑ j, w j = 1) :
    (l2 - lam j₁) * (1 - w j₁) ≤ ∑ j, (lam j - lam j₁) * w j := by
  have hsplit : ∑ j, (lam j - lam j₁) * w j
      = ∑ j ∈ Finset.univ.erase j₁, (lam j - lam j₁) * w j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j₁)]
    simp
  have hrest : ∑ j ∈ Finset.univ.erase j₁, w j = 1 - w j₁ := by
    have h := Finset.add_sum_erase Finset.univ w (Finset.mem_univ j₁)
    rw [hsum] at h
    linarith
  calc (l2 - lam j₁) * (1 - w j₁)
      = ∑ j ∈ Finset.univ.erase j₁, (l2 - lam j₁) * w j := by
        rw [← Finset.mul_sum, hrest]
    _ ≤ ∑ j ∈ Finset.univ.erase j₁, (lam j - lam j₁) * w j :=
        Finset.sum_le_sum fun j hj =>
          mul_le_mul_of_nonneg_right
            (by have := hlam j (Finset.ne_of_mem_erase hj); linarith) (hw j)
    _ = ∑ j, (lam j - lam j₁) * w j := hsplit.symm

/-! ## 2. Weights and Rayleigh quotient in an eigenbasis -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Parseval: the spectral weights of a vector sum to its squared norm. -/
theorem sum_sq_inner_eq_norm_sq {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (q : E) :
    ∑ j, ⟪b j, q⟫ ^ 2 = ‖q‖ ^ 2 := by
  have h := b.sum_inner_mul_inner q q
  rw [real_inner_self_eq_norm_sq] at h
  rw [← h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_comm q (b j)]
  ring

/-- The Rayleigh quotient of a unit vector is the weighted eigenvalue sum.
Only the eigen-equations on an orthonormal basis are used; symmetry of `K` is
a consequence of them, not an extra hypothesis. -/
theorem rayleigh_eq_weighted_eigenvalue_sum {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (K : E →ₗ[ℝ] E) (lam : ι → ℝ)
    (hK : ∀ j, K (b j) = lam j • b j) (q : E) :
    ⟪q, K q⟫ = ∑ j, lam j * ⟪b j, q⟫ ^ 2 := by
  have hq : q = ∑ j, ⟪b j, q⟫ • b j := (b.sum_repr' q).symm
  have hKq : K q = ∑ j, (lam j * ⟪b j, q⟫) • b j := by
    conv_lhs => rw [hq]
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, hK j, smul_smul, mul_comm]
  rw [hKq, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [real_inner_smul_right, real_inner_comm q (b j)]
  ring

/-! ## 3. The sign-free inequality (SF) -/

variable {n : ℕ}

private theorem one_le_of_ne_zero (j : Fin (n + 2)) (hj : j ≠ 0) :
    (1 : Fin (n + 2)) ≤ j := by
  have hval : j.val ≠ 0 := by
    intro h
    exact hj (Fin.ext (by simpa using h))
  have : (1 : Fin (n + 2)).val = 1 := by simp
  rw [Fin.le_def, this]
  omega

/-- The middle equality of (SF): the Rayleigh excess over the bottom level is
the weighted excess sum. -/
theorem signFreeRitz_rayleighExcess_eq_weighted_sum
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (K : E →ₗ[ℝ] E)
    (lam : Fin (n + 2) → ℝ) (hK : ∀ j, K (b j) = lam j • b j)
    (q : E) (hq : ‖q‖ = 1) :
    ⟪q, K q⟫ - lam 0 = ∑ j, (lam j - lam 0) * ⟪b j, q⟫ ^ 2 := by
  have hw : ∑ j, ⟪b j, q⟫ ^ 2 = 1 := by
    rw [sum_sq_inner_eq_norm_sq b q, hq]; norm_num
  have hexp : ∑ j, (lam j - lam 0) * ⟪b j, q⟫ ^ 2
      = (∑ j, lam j * ⟪b j, q⟫ ^ 2) - lam 0 * ∑ j, ⟪b j, q⟫ ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hexp, hw, rayleigh_eq_weighted_eigenvalue_sum b K lam hK q]
  ring

/-- **(SF), sign-free.** For an ordered orthonormal eigenbasis of a finite
dimensional real inner product space and a unit trial vector `q`, the spectral
gap times the projective defect `1 - w_1` is at most the Rayleigh excess over
the bottom level.  No positivity of `lam 0`, `lam 1` or of the gap is assumed,
and nothing is divided. -/
theorem signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (K : E →ₗ[ℝ] E)
    (lam : Fin (n + 2) → ℝ) (hK : ∀ j, K (b j) = lam j • b j)
    (hmono : Monotone lam) (q : E) (hq : ‖q‖ = 1) :
    (lam 1 - lam 0) * (1 - ⟪b 0, q⟫ ^ 2) ≤ ⟪q, K q⟫ - lam 0 := by
  classical
  have hw : ∑ j, ⟪b j, q⟫ ^ 2 = 1 := by
    rw [sum_sq_inner_eq_norm_sq b q, hq]; norm_num
  rw [signFreeRitz_rayleighExcess_eq_weighted_sum b K lam hK q hq]
  exact gap_mul_defect_le_weighted_excess_sum lam (fun j => ⟪b j, q⟫ ^ 2) 0 (lam 1)
    (fun j hj => hmono (one_le_of_ne_zero j hj)) (fun j => sq_nonneg _) hw

/-- Division corollary.  This is the **only** statement that needs a positive
gap, and it needs nothing else: still no sign on `lam 0` or `lam 1`. -/
theorem signFreeRitz_projectiveDefect_le_rayleighExcess_div_gap
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (K : E →ₗ[ℝ] E)
    (lam : Fin (n + 2) → ℝ) (hK : ∀ j, K (b j) = lam j • b j)
    (hmono : Monotone lam) (q : E) (hq : ‖q‖ = 1)
    (hgap : 0 < lam 1 - lam 0) :
    1 - ⟪b 0, q⟫ ^ 2 ≤ (⟪q, K q⟫ - lam 0) / (lam 1 - lam 0) := by
  rw [le_div_iff₀ hgap, mul_comm]
  exact signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess b K lam hK hmono q hq

/-- Control (ii): the zero-gap case.  (SF) still holds, with both sides
meaningful and no division performed; it degenerates to nonnegativity of the
Rayleigh excess. -/
theorem signFreeRitz_zero_gap_control
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (K : E →ₗ[ℝ] E)
    (lam : Fin (n + 2) → ℝ) (hK : ∀ j, K (b j) = lam j • b j)
    (hmono : Monotone lam) (q : E) (hq : ‖q‖ = 1) (hzero : lam 1 = lam 0) :
    (lam 1 - lam 0) * (1 - ⟪b 0, q⟫ ^ 2) ≤ ⟪q, K q⟫ - lam 0 ∧
      0 ≤ ⟪q, K q⟫ - lam 0 := by
  have h := signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess b K lam hK hmono q hq
  refine ⟨h, ?_⟩
  rw [hzero] at h
  simpa using h

/-! ## 4. Projective distance -/

/-- With sign alignment `0 ≤ ⟪x, q⟫`, the squared distance of two unit vectors
is exactly `2 (1 - sqrt (1 - p))`, where `p = 1 - ⟪x, q⟫ ^ 2` is the projective
defect. -/
theorem signFreeRitz_dist_sq_eq_two_mul_one_sub_sqrt
    (x q : E) (hx : ‖x‖ = 1) (hq : ‖q‖ = 1) (halign : 0 ≤ ⟪x, q⟫) :
    ‖x - q‖ ^ 2 = 2 * (1 - Real.sqrt (1 - (1 - ⟪x, q⟫ ^ 2))) := by
  have hsq : Real.sqrt (1 - (1 - ⟪x, q⟫ ^ 2)) = ⟪x, q⟫ := by
    have : (1 : ℝ) - (1 - ⟪x, q⟫ ^ 2) = ⟪x, q⟫ ^ 2 := by ring
    rw [this, Real.sqrt_sq halign]
  rw [norm_sub_pow_two_real, hx, hq, hsq]
  ring

/-- With sign alignment, the squared projective distance is at most twice the
projective defect. -/
theorem signFreeRitz_dist_sq_le_two_mul_projectiveDefect
    (x q : E) (hx : ‖x‖ = 1) (hq : ‖q‖ = 1) (halign : 0 ≤ ⟪x, q⟫) :
    ‖x - q‖ ^ 2 ≤ 2 * (1 - ⟪x, q⟫ ^ 2) := by
  have hle : ⟪x, q⟫ ≤ 1 := by
    have h := real_inner_le_norm x q
    rw [hx, hq] at h
    simpa using h
  rw [norm_sub_pow_two_real, hx, hq]
  nlinarith [halign, hle]

/-- The same, stated for the bottom eigenvector `xi = b 0` of the eigenbasis. -/
theorem signFreeRitz_eigenvector_dist_sq_le_two_mul_projectiveDefect
    (b : OrthonormalBasis (Fin (n + 2)) ℝ E) (q : E) (hq : ‖q‖ = 1)
    (halign : 0 ≤ ⟪b 0, q⟫) :
    ‖b 0 - q‖ ^ 2 ≤ 2 * (1 - ⟪b 0, q⟫ ^ 2) :=
  signFreeRitz_dist_sq_le_two_mul_projectiveDefect (b 0) q (b.orthonormal.1 0) hq halign

end Space

/-! ## 5. Control plants -/

/-- Diagonal operator with prescribed eigenvalues on the standard orthonormal
basis of `EuclideanSpace ℝ (Fin m)`. -/
def diagOp {m : ℕ} (lam : Fin m → ℝ) :
    EuclideanSpace ℝ (Fin m) →ₗ[ℝ] EuclideanSpace ℝ (Fin m) :=
  (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.constr ℝ
    fun j => lam j • EuclideanSpace.basisFun (Fin m) ℝ j

@[simp] theorem diagOp_apply_basisFun {m : ℕ} (lam : Fin m → ℝ) (j : Fin m) :
    diagOp lam (EuclideanSpace.basisFun (Fin m) ℝ j)
      = lam j • EuclideanSpace.basisFun (Fin m) ℝ j := by
  simp only [diagOp]
  rw [← OrthonormalBasis.coe_toBasis]
  exact Module.Basis.constr_basis _ ℝ _ j

theorem inner_basisFun_basisFun {m : ℕ} (i j : Fin m) :
    ⟪EuclideanSpace.basisFun (Fin m) ℝ i, EuclideanSpace.basisFun (Fin m) ℝ j⟫
      = if i = j then 1 else 0 := by
  classical
  simpa using
    (orthonormal_iff_ite.mp (EuclideanSpace.basisFun (Fin m) ℝ).orthonormal i j)

/-- Control (i): the mandatory negative-bottom equality plant `K = diag (-2, -1)`. -/
def plantNegBottomLam : Fin 2 → ℝ := ![-2, -1]

/-- Trial vector `(sqrt (1 - t ^ 2), t)` of the negative-bottom plant. -/
def plantNegBottomTrial (t : ℝ) : EuclideanSpace ℝ (Fin 2) :=
  Real.sqrt (1 - t ^ 2) • EuclideanSpace.basisFun (Fin 2) ℝ 0
    + t • EuclideanSpace.basisFun (Fin 2) ℝ 1

theorem plantNegBottomLam_monotone : Monotone plantNegBottomLam := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [plantNegBottomLam, Fin.le_def]

theorem plantNegBottom_eigen (j : Fin 2) :
    diagOp plantNegBottomLam (EuclideanSpace.basisFun (Fin 2) ℝ j)
      = plantNegBottomLam j • EuclideanSpace.basisFun (Fin 2) ℝ j :=
  diagOp_apply_basisFun _ j

theorem plantNegBottom_inner_zero (t : ℝ) :
    ⟪EuclideanSpace.basisFun (Fin 2) ℝ 0, plantNegBottomTrial t⟫
      = Real.sqrt (1 - t ^ 2) := by
  rw [plantNegBottomTrial, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_basisFun_basisFun, inner_basisFun_basisFun]
  norm_num

theorem plantNegBottom_inner_one (t : ℝ) :
    ⟪EuclideanSpace.basisFun (Fin 2) ℝ 1, plantNegBottomTrial t⟫ = t := by
  rw [plantNegBottomTrial, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_basisFun_basisFun, inner_basisFun_basisFun]
  norm_num

theorem plantNegBottom_norm (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖plantNegBottomTrial t‖ = 1 := by
  have hnn : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  have hsum := sum_sq_inner_eq_norm_sq (EuclideanSpace.basisFun (Fin 2) ℝ)
    (plantNegBottomTrial t)
  rw [Fin.sum_univ_two, plantNegBottom_inner_zero, plantNegBottom_inner_one,
    Real.sq_sqrt hnn] at hsum
  have hnorm : ‖plantNegBottomTrial t‖ ^ 2 = 1 := by linarith
  have hpos : (0 : ℝ) ≤ ‖plantNegBottomTrial t‖ := norm_nonneg _
  nlinarith [hnorm, hpos]

/-- **Control (i).**  With `K = diag (-2, -1)` (a strictly negative spectrum)
and `q = (sqrt (1 - t ^ 2), t)`, the sign-free inequality (SF) holds with
equality, both sides being `t ^ 2`. -/
theorem plantNegBottom_equality_control (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    plantNegBottomLam 0 = -2 ∧ plantNegBottomLam 1 = -1 ∧
      ‖plantNegBottomTrial t‖ = 1 ∧
      1 - ⟪EuclideanSpace.basisFun (Fin 2) ℝ 0, plantNegBottomTrial t⟫ ^ 2 = t ^ 2 ∧
      ⟪plantNegBottomTrial t, diagOp plantNegBottomLam (plantNegBottomTrial t)⟫
          - plantNegBottomLam 0 = t ^ 2 ∧
      (plantNegBottomLam 1 - plantNegBottomLam 0)
            * (1 - ⟪EuclideanSpace.basisFun (Fin 2) ℝ 0, plantNegBottomTrial t⟫ ^ 2)
        = ⟪plantNegBottomTrial t, diagOp plantNegBottomLam (plantNegBottomTrial t)⟫
            - plantNegBottomLam 0 := by
  have hnn : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  have hdefect :
      1 - ⟪EuclideanSpace.basisFun (Fin 2) ℝ 0, plantNegBottomTrial t⟫ ^ 2 = t ^ 2 := by
    rw [plantNegBottom_inner_zero, Real.sq_sqrt hnn]; ring
  have hray : ⟪plantNegBottomTrial t, diagOp plantNegBottomLam (plantNegBottomTrial t)⟫
      = -2 + t ^ 2 := by
    rw [rayleigh_eq_weighted_eigenvalue_sum (EuclideanSpace.basisFun (Fin 2) ℝ)
      (diagOp plantNegBottomLam) plantNegBottomLam plantNegBottom_eigen,
      Fin.sum_univ_two, plantNegBottom_inner_zero, plantNegBottom_inner_one,
      Real.sq_sqrt hnn]
    simp only [plantNegBottomLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring
  refine ⟨by simp [plantNegBottomLam], by simp [plantNegBottomLam],
    plantNegBottom_norm t ht0 ht1, hdefect, ?_, ?_⟩
  · rw [hray]
    simp only [plantNegBottomLam, Matrix.cons_val_zero]
    ring
  · rw [hray, hdefect]
    simp only [plantNegBottomLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    ring

/-- The negative-bottom plant does satisfy every hypothesis of (SF): the
inequality is not vacuous on a negative spectrum. -/
theorem plantNegBottom_signFree_instance (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (plantNegBottomLam 1 - plantNegBottomLam 0)
        * (1 - ⟪EuclideanSpace.basisFun (Fin 2) ℝ 0, plantNegBottomTrial t⟫ ^ 2)
      ≤ ⟪plantNegBottomTrial t, diagOp plantNegBottomLam (plantNegBottomTrial t)⟫
          - plantNegBottomLam 0 :=
  signFreeRitz_gap_mul_projectiveDefect_le_rayleighExcess
    (n := 0) (EuclideanSpace.basisFun (Fin 2) ℝ) (diagOp plantNegBottomLam)
    plantNegBottomLam plantNegBottom_eigen plantNegBottomLam_monotone
    (plantNegBottomTrial t) (plantNegBottom_norm t ht0 ht1)

/-! ### Control (iii): three levels, `p -> 0` with ratio pinned at one -/

/-- Eigenvalues `diag (0, 1, m ^ 2)`. -/
def plantThreeLevelLam (m : ℝ) : Fin 3 → ℝ := ![0, 1, m ^ 2]

/-- Trial vector `(sqrt (1 - m⁻¹ ^ 2), 0, m⁻¹)`. -/
def plantThreeLevelTrial (m : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  Real.sqrt (1 - (1 / m) ^ 2) • EuclideanSpace.basisFun (Fin 3) ℝ 0
    + (1 / m) • EuclideanSpace.basisFun (Fin 3) ℝ 2

theorem plantThreeLevelLam_monotone {m : ℝ} (hm : 1 ≤ m) :
    Monotone (plantThreeLevelLam m) := by
  have hsq : (1 : ℝ) ≤ m ^ 2 := by nlinarith
  have habs : (1 : ℝ) ≤ |m| := by
    rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ m)]; exact hm
  have hsq0 : (0 : ℝ) ≤ m ^ 2 := sq_nonneg m
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [plantThreeLevelLam, Fin.le_def]

theorem plantThreeLevel_eigen (m : ℝ) (j : Fin 3) :
    diagOp (plantThreeLevelLam m) (EuclideanSpace.basisFun (Fin 3) ℝ j)
      = plantThreeLevelLam m j • EuclideanSpace.basisFun (Fin 3) ℝ j :=
  diagOp_apply_basisFun _ j

theorem plantThreeLevel_inner_zero (m : ℝ) :
    ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0, plantThreeLevelTrial m⟫
      = Real.sqrt (1 - (1 / m) ^ 2) := by
  rw [plantThreeLevelTrial, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_basisFun_basisFun, inner_basisFun_basisFun]
  norm_num [Fin.ext_iff]

theorem plantThreeLevel_inner_one (m : ℝ) :
    ⟪EuclideanSpace.basisFun (Fin 3) ℝ 1, plantThreeLevelTrial m⟫ = 0 := by
  rw [plantThreeLevelTrial, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_basisFun_basisFun, inner_basisFun_basisFun]
  norm_num [Fin.ext_iff]

theorem plantThreeLevel_inner_two (m : ℝ) :
    ⟪EuclideanSpace.basisFun (Fin 3) ℝ 2, plantThreeLevelTrial m⟫ = 1 / m := by
  rw [plantThreeLevelTrial, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, inner_basisFun_basisFun, inner_basisFun_basisFun]
  norm_num [Fin.ext_iff]

theorem plantThreeLevel_norm {m : ℝ} (hm : 1 ≤ m) :
    ‖plantThreeLevelTrial m‖ = 1 := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm
  have hnn : (0 : ℝ) ≤ 1 - (1 / m) ^ 2 := by
    have h1 : (1 / m) ≤ 1 := by rw [div_le_one hm0]; exact hm
    have h0 : (0 : ℝ) ≤ 1 / m := le_of_lt (by positivity)
    nlinarith
  have hsum := sum_sq_inner_eq_norm_sq (EuclideanSpace.basisFun (Fin 3) ℝ)
    (plantThreeLevelTrial m)
  rw [Fin.sum_univ_three, plantThreeLevel_inner_zero, plantThreeLevel_inner_one,
    plantThreeLevel_inner_two, Real.sq_sqrt hnn] at hsum
  have hnorm : ‖plantThreeLevelTrial m‖ ^ 2 = 1 := by linarith
  have hpos : (0 : ℝ) ≤ ‖plantThreeLevelTrial m‖ := norm_nonneg _
  nlinarith [hnorm, hpos]

/-- **Control (iii).**  With `K = diag (0, 1, m ^ 2)` and
`q = (sqrt (1 - m⁻¹ ^ 2), 0, m⁻¹)` the projective defect is `p = 1 / m ^ 2`
while the Ritz ratio `eta = (R q - lam 0) / (lam 1 - lam 0)` equals `1`.
So `p -> 0` does not imply `eta -> 0`, and (SF) still holds. -/
theorem plantThreeLevel_defect_small_ratio_one {m : ℝ} (hm : 1 ≤ m) :
    ‖plantThreeLevelTrial m‖ = 1 ∧
      1 - ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0, plantThreeLevelTrial m⟫ ^ 2
        = 1 / m ^ 2 ∧
      (⟪plantThreeLevelTrial m,
            diagOp (plantThreeLevelLam m) (plantThreeLevelTrial m)⟫
          - plantThreeLevelLam m 0)
        / (plantThreeLevelLam m 1 - plantThreeLevelLam m 0) = 1 ∧
      (plantThreeLevelLam m 1 - plantThreeLevelLam m 0)
          * (1 - ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0, plantThreeLevelTrial m⟫ ^ 2)
        ≤ ⟪plantThreeLevelTrial m,
              diagOp (plantThreeLevelLam m) (plantThreeLevelTrial m)⟫
            - plantThreeLevelLam m 0 := by
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le zero_lt_one hm
  have hne : m ≠ 0 := ne_of_gt hm0
  have hnn : (0 : ℝ) ≤ 1 - (1 / m) ^ 2 := by
    have h1 : (1 / m) ≤ 1 := by rw [div_le_one hm0]; exact hm
    have h0 : (0 : ℝ) ≤ 1 / m := le_of_lt (by positivity)
    nlinarith
  have hdefect :
      1 - ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0, plantThreeLevelTrial m⟫ ^ 2
        = 1 / m ^ 2 := by
    rw [plantThreeLevel_inner_zero, Real.sq_sqrt hnn]
    field_simp
    ring
  have hray : ⟪plantThreeLevelTrial m,
      diagOp (plantThreeLevelLam m) (plantThreeLevelTrial m)⟫ = 1 := by
    rw [rayleigh_eq_weighted_eigenvalue_sum (EuclideanSpace.basisFun (Fin 3) ℝ)
      (diagOp (plantThreeLevelLam m)) (plantThreeLevelLam m)
      (plantThreeLevel_eigen m),
      Fin.sum_univ_three, plantThreeLevel_inner_zero, plantThreeLevel_inner_one,
      plantThreeLevel_inner_two, Real.sq_sqrt hnn]
    simp only [plantThreeLevelLam, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    field_simp
    ring
  refine ⟨plantThreeLevel_norm hm, hdefect, ?_, ?_⟩
  · rw [hray]
    simp only [plantThreeLevelLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  · rw [hray, hdefect]
    simp only [plantThreeLevelLam, Matrix.cons_val_zero, Matrix.cons_val_one]
    have h1 : (0 : ℝ) < 1 / m ^ 2 := by positivity
    have h2 : 1 / m ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith

/-- The defect of the three-level plant can be made arbitrarily small while
its Ritz ratio stays pinned at `1`. -/
theorem plantThreeLevel_defect_arbitrarily_small_ratio_one
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℝ, 1 ≤ m ∧
      1 - ⟪EuclideanSpace.basisFun (Fin 3) ℝ 0, plantThreeLevelTrial m⟫ ^ 2 < ε ∧
      (⟪plantThreeLevelTrial m,
            diagOp (plantThreeLevelLam m) (plantThreeLevelTrial m)⟫
          - plantThreeLevelLam m 0)
        / (plantThreeLevelLam m 1 - plantThreeLevelLam m 0) = 1 := by
  have hd : (0 : ℝ) < 1 / ε := by positivity
  have hm : (1 : ℝ) ≤ 1 + 1 / ε := by linarith
  obtain ⟨_, hdef, hratio, _⟩ := plantThreeLevel_defect_small_ratio_one hm
  refine ⟨1 + 1 / ε, hm, ?_, hratio⟩
  rw [hdef, div_lt_iff₀ (by positivity : (0 : ℝ) < (1 + 1 / ε) ^ 2)]
  have key : ε * (1 + 1 / ε) ^ 2 = ε + 2 + 1 / ε := by
    field_simp
    ring
  rw [key]
  linarith

end Q3.RouteB.SignFreeRitz
