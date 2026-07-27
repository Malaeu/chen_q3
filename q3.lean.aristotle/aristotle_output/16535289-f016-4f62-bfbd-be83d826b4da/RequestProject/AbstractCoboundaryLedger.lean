import Mathlib

/-!
# Abstract Coboundary Ledger

Basis-invariant operator-algebra core of a "combined defect" ledger: exact finite
identities around a compressed eigenproblem `M = S T S + C`, with a three-factor
projection `S = A · B · P` and a parity involution `J`.  Pure linear algebra over
`ℂ`; no analysis, no unitarity, no groups.

We work over `Matrix n n ℂ` with `Fintype n`, `DecidableEq n`, using the
`star`/adjoint (`ᴴ = Matrix.conjTranspose`) based inner product

  `ip v w = star v ⬝ᵥ w`   (conjugate-linear in the first slot),

for which the master adjoint relation is
`ip (M *ᵥ v) w = ip v (Mᴴ *ᵥ w)`.  Every statement is basis-invariant: the only
positivity used is definiteness of the standard Hermitian form,
`ip v v = 0 ↔ v = 0` (`q2_eq_zero`); no raw-coordinate PSD tricks.

## Standing notation
* `S = Sᴴ = S * S` (orthogonal projection), `Q := 1 − S`.
* `C = S * C * S` (locality of the correction).
* `q ≠ 0`, `S *ᵥ q = q`, `μ : ℂ`.
* `A, B, P` orthogonal projections, `J` a parity involution with
  `P = (1 + J)/2`, `P₋ := (1 − J)/2` (over matrices, `2⁻¹ • (1 ± J)`).

## Target theorems
`T0_fixed_point_chain`, `T1_coboundary`, `T2_residual`, the channel identities
`T3_channel_A/B/P`, `T3_telescope`, `T3_op_identity`, `T4_parity_channel`, and the
S10 lock `T5a_triple_not_selfadjoint` / `T5b_S10_lock`, plus the planted-failure
lemmas `PL1_locality_load_bearing`, `PL2_order_swap`, `PL3_parity_revival`.

## Instantiation obligations remaining OUTSIDE this file
This file is the *abstract* algebraic core.  To connect it to the project's
source-locked RH-route objects one must still identify the concrete matrices with
the ledger symbols, namely:
* `S`  with the compression/gauge projection of the finite approximant `F_j`;
* `A, B, P`  with the three factors of that projection and `J` with the parity
  (functional-equation) involution used in `H2aPenalty`/`H2aBridge`;
* `T`  with the compressed operator, `C` with the (local) correction, and `q`
  with the ground state, verifying `S *ᵥ q = q`, `C = S * C * S`, the eigen
  relation `S T S q + C q = μ • q`, and the parity intertwining
  `J A J = A`, `J B J = B`, `J T J = T`.
None of these identifications are performed here.
-/

open Matrix

namespace ACL

set_option linter.unusedSectionVars false

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Star/adjoint based inner product on `n → ℂ`, conjugate-linear in the first slot. -/
noncomputable def ip (v w : n → ℂ) : ℂ := star v ⬝ᵥ w

/-! ### Basic inner-product algebra -/

/-- Master adjoint relation (move an operator to the right slot). -/
lemma ip_mulVec_left (M : Matrix n n ℂ) (v w : n → ℂ) :
    ip (M *ᵥ v) w = ip v (Mᴴ *ᵥ w) := by
  unfold ip; rw [Matrix.star_mulVec, Matrix.dotProduct_mulVec]

/-- Move an operator to the left slot. -/
lemma ip_mulVec_right (M : Matrix n n ℂ) (v w : n → ℂ) :
    ip v (M *ᵥ w) = ip (Mᴴ *ᵥ v) w := by
  unfold ip
  rw [Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

lemma ip_sub_right (v a b : n → ℂ) : ip v (a - b) = ip v a - ip v b := by
  unfold ip; simp [dotProduct_sub]

lemma ip_sub_left (a b w : n → ℂ) : ip (a - b) w = ip a w - ip b w := by
  unfold ip; simp [sub_dotProduct, star_sub]

lemma ip_add_right (v a b : n → ℂ) : ip v (a + b) = ip v a + ip v b := by
  unfold ip; simp [dotProduct_add]

/-! ### The definite quadratic form -/

/-- Squared norm `‖v‖² = ∑ ‖vᵢ‖²`, the real part of `ip v v`. -/
noncomputable def q2 (v : n → ℂ) : ℝ := ∑ i, Complex.normSq (v i)

lemma q2_eq (v : n → ℂ) : (q2 v : ℂ) = ip v v := by
  unfold q2 ip; push_cast; simp [dotProduct, Pi.star_apply, mul_comm, Complex.mul_conj]

lemma q2_nonneg (v : n → ℂ) : 0 ≤ q2 v :=
  Finset.sum_nonneg (fun i _ => Complex.normSq_nonneg (v i))

/-- Definiteness of the Hermitian form. -/
lemma q2_eq_zero (v : n → ℂ) : q2 v = 0 ↔ v = 0 := by
  unfold q2
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg (v i))]
  constructor
  · intro h; funext i; have := h i (Finset.mem_univ i)
    simpa [Complex.normSq_eq_zero] using this
  · intro h i _; simp [h]

lemma one_sub_proj_sa {R : Matrix n n ℂ} (hR : Rᴴ = R) :
    ((1 : Matrix n n ℂ) - R)ᴴ = 1 - R := by simp [hR]

lemma one_sub_proj_id {R : Matrix n n ℂ} (hR2 : R * R = R) :
    ((1 : Matrix n n ℂ) - R) * (1 - R) = 1 - R := by
  have : ((1 : Matrix n n ℂ) - R) * (1 - R) = 1 - R - R + R * R := by noncomm_ring
  rw [this, hR2]; abel

lemma proj_ip_self {R : Matrix n n ℂ} (hR : Rᴴ = R) (hR2 : R * R = R) (v : n → ℂ) :
    ip (R *ᵥ v) (R *ᵥ v) = ip v (R *ᵥ v) := by
  rw [ip_mulVec_left, mulVec_mulVec, hR, hR2]

/-- Pythagorean decomposition for an orthogonal projection `R`. -/
lemma q2_decomp {R : Matrix n n ℂ} (hR : Rᴴ = R) (hR2 : R * R = R) (v : n → ℂ) :
    q2 v = q2 (R *ᵥ v) + q2 ((1 - R) *ᵥ v) := by
  have key : ip v v = ip (R *ᵥ v) (R *ᵥ v) + ip ((1 - R) *ᵥ v) ((1 - R) *ᵥ v) := by
    rw [proj_ip_self hR hR2, proj_ip_self (one_sub_proj_sa hR) (one_sub_proj_id hR2),
      ← ip_add_right]
    congr 1; rw [sub_mulVec, one_mulVec]; abel
  have : ((q2 v : ℂ)) = ((q2 (R *ᵥ v) : ℂ)) + ((q2 ((1 - R) *ᵥ v) : ℂ)) := by
    rw [q2_eq, q2_eq, q2_eq]; exact key
  exact_mod_cast this

/-- Orthogonal projections are norm-nonincreasing. -/
lemma q2_proj_le {R : Matrix n n ℂ} (hR : Rᴴ = R) (hR2 : R * R = R) (v : n → ℂ) :
    q2 (R *ᵥ v) ≤ q2 v := by
  have h1 := q2_decomp hR hR2 v
  have h2 := q2_nonneg ((1 - R) *ᵥ v)
  linarith

/-- Norm equality forces the fixed-point relation. -/
lemma proj_fixed {R : Matrix n n ℂ} (hR : Rᴴ = R) (hR2 : R * R = R) (v : n → ℂ)
    (h : q2 (R *ᵥ v) = q2 v) : R *ᵥ v = v := by
  have hd := q2_decomp hR hR2 v
  have h0 : q2 ((1 - R) *ᵥ v) = 0 := by linarith
  rw [q2_eq_zero] at h0
  rw [sub_mulVec, one_mulVec, sub_eq_zero] at h0
  exact h0.symm

/-- Adjoint of a triple product of self-adjoint matrices reverses the order. -/
lemma star_ABP {A B P : Matrix n n ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) (hP : Pᴴ = P) :
    (A * B * P)ᴴ = P * B * A := by
  simp [Matrix.conjTranspose_mul, hA, hB, hP, mul_assoc]

/-- `P₋ = 1 − P` when `P = (1 + J)/2`. -/
lemma Pminus_eq {P J : Matrix n n ℂ} (hPJ : P = (2 : ℂ)⁻¹ • (1 + J)) :
    (2 : ℂ)⁻¹ • ((1 : Matrix n n ℂ) - J) = 1 - P := by
  subst hPJ
  ext i j
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.one_apply, smul_eq_mul]
  ring

/-! ### T0 — fixed-point chain (R4) -/

/-- **T0.** If `S = A·B·P` (all orthogonal projections), `P = (1+J)/2`, and
`S q = q`, then `P q = q`, `B q = q`, `A q = q`, and `J q = q`.  The proof is the
norm chain `‖q‖ = ‖ABPq‖ ≤ ‖BPq‖ ≤ ‖Pq‖ ≤ ‖q‖`, forcing equality at each step. -/
theorem T0_fixed_point_chain
    (A B P J : Matrix n n ℂ) (q : n → ℂ)
    (hAsa : Aᴴ = A) (hA2 : A * A = A)
    (hBsa : Bᴴ = B) (hB2 : B * B = B)
    (hPsa : Pᴴ = P) (hP2 : P * P = P)
    (hPJ : P = (2 : ℂ)⁻¹ • (1 + J))
    (hSq : (A * B * P) *ᵥ q = q) :
    P *ᵥ q = q ∧ B *ᵥ q = q ∧ A *ᵥ q = q ∧ J *ᵥ q = q := by
  rw [← mulVec_mulVec, ← mulVec_mulVec] at hSq
  have hle1 := q2_proj_le hPsa hP2 q
  have hle2 := q2_proj_le hBsa hB2 (P *ᵥ q)
  have hle3 := q2_proj_le hAsa hA2 (B *ᵥ (P *ᵥ q))
  have heq : q2 (A *ᵥ (B *ᵥ (P *ᵥ q))) = q2 q := by rw [hSq]
  have hPq : P *ᵥ q = q := proj_fixed hPsa hP2 q (by linarith)
  have hBeq : q2 (B *ᵥ (P *ᵥ q)) = q2 q := by linarith
  rw [hPq] at hBeq
  have hBq : B *ᵥ q = q := proj_fixed hBsa hB2 q hBeq
  rw [hPq, hBq] at heq
  have hAq : A *ᵥ q = q := proj_fixed hAsa hA2 q heq
  refine ⟨hPq, hBq, hAq, ?_⟩
  have h := hPq
  rw [hPJ, smul_mulVec, add_mulVec, one_mulVec] at h
  have h2 : q + J *ᵥ q = (2 : ℂ) • q := by
    have := congrArg (fun x => (2 : ℂ) • x) h
    simp only [smul_smul] at this
    norm_num at this
    rw [this]
  have h3 : J *ᵥ q = (2 : ℂ) • q - q := by rw [← h2]; abel
  rw [h3]; module

/-! ### T1 — exact coboundary identity -/

/-- **T1.** Assuming `S q = q`, `C = S C S`, and the eigen-relation
`S T S q + C q = μ • q`, for every `v`
`⟪v, (T − μ) q⟫ = ⟪Q v, Q (T q)⟫ − ⟪S v, C q⟫`.

Note: `T = Tᴴ` is *not* needed and is not assumed.  The locality hypothesis
`hCloc` is genuinely used here (through `S (C q) = C q`), but it is in fact
*redundant*: the eigen-relation alone already forces the identity, see
`T1_coboundary_no_locality`. -/
theorem T1_coboundary
    (S T C : Matrix n n ℂ) (q : n → ℂ) (μ : ℂ)
    (hSsa : Sᴴ = S) (hSid : S * S = S) (hSq : S *ᵥ q = q)
    (hCloc : C = S * C * S)
    (heig : S *ᵥ (T *ᵥ (S *ᵥ q)) + C *ᵥ q = μ • q) :
    ∀ v : n → ℂ,
      ip v (T *ᵥ q - μ • q)
        = ip ((1 - S) *ᵥ v) ((1 - S) *ᵥ (T *ᵥ q)) - ip (S *ᵥ v) (C *ᵥ q) := by
  have hSC : S *ᵥ (C *ᵥ q) = C *ᵥ q := by
    conv_rhs => rw [hCloc, ← mulVec_mulVec, ← mulVec_mulVec, hSq]
  rw [hSq] at heig
  intro v
  rw [ip_mulVec_left, mulVec_mulVec, one_sub_proj_sa hSsa, one_sub_proj_id hSid,
    ip_mulVec_left, hSsa, ← ip_sub_right]
  congr 1
  rw [sub_mulVec, one_mulVec, hSC, ← heig]; abel

/-- Documentation lemma: the T1 identity actually follows from the eigen-relation
alone (locality `C = S C S` is not needed for it). -/
theorem T1_coboundary_no_locality
    (S T C : Matrix n n ℂ) (q : n → ℂ) (μ : ℂ)
    (hSsa : Sᴴ = S) (hSid : S * S = S) (hSq : S *ᵥ q = q)
    (heig : S *ᵥ (T *ᵥ (S *ᵥ q)) + C *ᵥ q = μ • q) :
    ∀ v : n → ℂ,
      ip v (T *ᵥ q - μ • q)
        = ip ((1 - S) *ᵥ v) ((1 - S) *ᵥ (T *ᵥ q)) - ip (S *ᵥ v) (C *ᵥ q) := by
  rw [hSq] at heig
  have hC : C *ᵥ q = μ • q - S *ᵥ (T *ᵥ q) := by rw [← heig]; abel
  have hSC : S *ᵥ (C *ᵥ q) = C *ᵥ q := by
    rw [hC, mulVec_sub, mulVec_smul, hSq, mulVec_mulVec, hSid]
  intro v
  rw [ip_mulVec_left, mulVec_mulVec, one_sub_proj_sa hSsa, one_sub_proj_id hSid,
    ip_mulVec_left, hSsa, ← ip_sub_right]
  congr 1
  rw [sub_mulVec, one_mulVec, hSC, ← heig]; abel

/-! ### T2 — residual plant form -/

/-- **T2.** Same hypotheses as T1 except the eigen-relation; with
`r := S T S q + C q − μ • q`, for every `v`
`⟪v, (T − μ) q⟫ = ⟪Q v, Q (T q)⟫ − ⟪S v, C q⟫ + ⟪v, r⟫`.
Here locality `C = S C S` *is* load-bearing (cf. `PL1_locality_load_bearing`). -/
theorem T2_residual
    (S T C : Matrix n n ℂ) (q : n → ℂ) (μ : ℂ)
    (hSsa : Sᴴ = S) (hSid : S * S = S) (hSq : S *ᵥ q = q)
    (hCloc : C = S * C * S) :
    ∀ v : n → ℂ,
      ip v (T *ᵥ q - μ • q)
        = ip ((1 - S) *ᵥ v) ((1 - S) *ᵥ (T *ᵥ q)) - ip (S *ᵥ v) (C *ᵥ q)
          + ip v (S *ᵥ (T *ᵥ (S *ᵥ q)) + C *ᵥ q - μ • q) := by
  have hSC : S *ᵥ (C *ᵥ q) = C *ᵥ q := by
    conv_rhs => rw [hCloc, ← mulVec_mulVec, ← mulVec_mulVec, hSq]
  intro v
  rw [ip_mulVec_left, mulVec_mulVec, one_sub_proj_sa hSsa, one_sub_proj_id hSid,
    ip_mulVec_left, hSsa, ← ip_sub_right, ← ip_add_right]
  congr 1
  rw [hSq, sub_mulVec, one_mulVec, hSC]; abel

/-! ### T3 — channel formulas -/

/-- **T3, channel A.** -/
theorem T3_channel_A (A T V : Matrix n n ℂ) (q : n → ℂ)
    (hAsa : Aᴴ = A) (hAq : A *ᵥ q = q) :
    ip ((A * V - V * A) *ᵥ q) (T *ᵥ q) = - ip (V *ᵥ q) ((1 - A) *ᵥ (T *ᵥ q)) := by
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hAq, ip_sub_left, ip_mulVec_left, hAsa,
    sub_mulVec, one_mulVec, ip_sub_right]
  ring

/-- **T3, channel B.** -/
theorem T3_channel_B (A B T V : Matrix n n ℂ) (q : n → ℂ)
    (hAsa : Aᴴ = A) (hBsa : Bᴴ = B) (hBq : B *ᵥ q = q) :
    ip ((A * (B * V - V * B)) *ᵥ q) (T *ᵥ q)
      = - ip (V *ᵥ q) (((1 - B) * A) *ᵥ (T *ᵥ q)) := by
  rw [← mulVec_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hBq,
    ip_mulVec_left, hAsa, ip_sub_left, ip_mulVec_left, hBsa,
    sub_mul, one_mul, sub_mulVec, ← mulVec_mulVec, ip_sub_right]
  ring

/-- **T3, channel P.**  Right factors are `B · A` (i.e. `star (A·B)`): do not
commute them. -/
theorem T3_channel_P (A B P J T V : Matrix n n ℂ) (q : n → ℂ)
    (hAsa : Aᴴ = A) (hBsa : Bᴴ = B) (hPsa : Pᴴ = P) (hPq : P *ᵥ q = q)
    (hPJ : P = (2 : ℂ)⁻¹ • (1 + J)) :
    ip ((A * B * (P * V - V * P)) *ᵥ q) (T *ᵥ q)
      = - ip (V *ᵥ q) ((((2 : ℂ)⁻¹ • (1 - J)) * B * A) *ᵥ (T *ᵥ q)) := by
  rw [Pminus_eq hPJ]
  rw [← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hPq,
    ip_mulVec_left, hAsa, ip_mulVec_left, hBsa, ip_sub_left, ip_mulVec_left, hPsa]
  rw [← mulVec_mulVec, ← mulVec_mulVec, sub_mulVec, one_mulVec, ip_sub_right]
  ring

/-- **T3, telescope sum.** `X(V) = − ⟪V q, (1 − star S)(T q)⟫`. -/
theorem T3_telescope (S T V : Matrix n n ℂ) (q : n → ℂ) (hSq : S *ᵥ q = q) :
    ip ((S * V - V * S) *ᵥ q) (T *ᵥ q) = - ip (V *ᵥ q) ((1 - Sᴴ) *ᵥ (T *ᵥ q)) := by
  rw [sub_mulVec, ← mulVec_mulVec, ← mulVec_mulVec, hSq, ip_sub_left, ip_mulVec_left,
    sub_mulVec, one_mulVec, ip_sub_right]
  ring

/-- **T3, operator identity.**
`(1 − A) + (1 − B)·A + P₋·B·A = 1 − P·B·A`  ( `= 1 − star S` ). -/
theorem T3_op_identity (A B P J : Matrix n n ℂ) (hPJ : P = (2 : ℂ)⁻¹ • (1 + J)) :
    (1 - A) + (1 - B) * A + (((2 : ℂ)⁻¹ • (1 - J)) * B * A) = 1 - P * B * A := by
  rw [Pminus_eq hPJ]; noncomm_ring

/-! ### T4 — parity channel vanishes -/

/-- **T4.** In the T3 setting, if additionally `J A J = A`, `J B J = B`,
`J T J = T` (and `J² = 1`), then `P₋ · B · A · (T q) = 0`, so the third channel
is identically zero.  (`J q = q` is automatic from T0.) -/
theorem T4_parity_channel (A B P J T : Matrix n n ℂ) (q : n → ℂ)
    (hAsa : Aᴴ = A) (hA2 : A * A = A) (hBsa : Bᴴ = B) (hB2 : B * B = B)
    (hPsa : Pᴴ = P) (hP2 : P * P = P) (hPJ : P = (2 : ℂ)⁻¹ • (1 + J))
    (hSq : (A * B * P) *ᵥ q = q)
    (hJA : J * A * J = A) (hJB : J * B * J = B) (hJT : J * T * J = T)
    (hJ2 : J * J = 1) :
    ((((2 : ℂ)⁻¹ • (1 - J)) * B * A) *ᵥ (T *ᵥ q) = 0) ∧
      ∀ V : Matrix n n ℂ, ip ((A * B * (P * V - V * P)) *ᵥ q) (T *ᵥ q) = 0 := by
  obtain ⟨hPq, hBq, hAq, hJq⟩ :=
    T0_fixed_point_chain A B P J q hAsa hA2 hBsa hB2 hPsa hP2 hPJ hSq
  have hJA' : J * A = A * J := by
    have h := congrArg (· * J) hJA
    simp only at h; rw [mul_assoc, mul_assoc, hJ2, mul_one] at h; rw [h]
  have hJB' : J * B = B * J := by
    have h := congrArg (· * J) hJB
    simp only at h; rw [mul_assoc, mul_assoc, hJ2, mul_one] at h; rw [h]
  have hJT' : J * T = T * J := by
    have h := congrArg (· * J) hJT
    simp only at h; rw [mul_assoc, mul_assoc, hJ2, mul_one] at h; rw [h]
  have hvanish : (((2 : ℂ)⁻¹ • (1 - J)) * B * A) *ᵥ (T *ᵥ q) = 0 := by
    have hc : J * B * A * T = B * A * T * J := by
      rw [show J * B * A * T = (J * B) * (A * T) by noncomm_ring, hJB',
          show (B * J) * (A * T) = B * (J * A) * T by noncomm_ring, hJA',
          show B * (A * J) * T = (B * A) * (J * T) by noncomm_ring, hJT']
      noncomm_ring
    have hJfix : (B * A * T * J) *ᵥ q = (B * A * T) *ᵥ q := by rw [← mulVec_mulVec, hJq]
    have key : (((1 : Matrix n n ℂ) - J) * B * A * T) *ᵥ q = 0 := by
      rw [show ((1 : Matrix n n ℂ) - J) * B * A * T = B * A * T - J * B * A * T by noncomm_ring,
        sub_mulVec, hc, hJfix, sub_self]
    rw [mulVec_mulVec,
      show ((2 : ℂ)⁻¹ • ((1 : Matrix n n ℂ) - J)) * B * A * T
          = (2 : ℂ)⁻¹ • (((1 : Matrix n n ℂ) - J) * B * A * T) by
        rw [smul_mul_assoc, smul_mul_assoc, smul_mul_assoc],
      smul_mulVec, key, smul_zero]
  refine ⟨hvanish, ?_⟩
  intro V
  rw [T3_channel_P A B P J T V q hAsa hBsa hPsa hPq hPJ, hvanish]
  simp [ip]

/-! ### T5 — S10 lock -/

/-- **T5(a).**  A triple product of orthogonal projections need not be
self-adjoint. -/
theorem T5a_triple_not_selfadjoint :
    ∃ (A B P : Matrix (Fin 2) (Fin 2) ℂ),
      (Aᴴ = A ∧ A * A = A) ∧ (Bᴴ = B ∧ B * B = B) ∧ (Pᴴ = P ∧ P * P = P) ∧
        (A * B * P)ᴴ ≠ A * B * P := by
  refine ⟨!![1,0;0,0], !![1/2,1/2;1/2,1/2], 1, ⟨?_,?_⟩, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · exact one_mul 1
  · intro h
    have := congrFun (congrFun h 0) 1
    norm_num [Matrix.conjTranspose_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply, Complex.ext_iff] at this

/-- **T5(b).**  If `A·B = B·A = B` (i.e. `Ran B ⊆ Ran A`) and `B·P = P·B`, then
`A·B·P = B·P` and `B·P` is an orthogonal projection.

(The hypothesis `hBA : B·A = B` is part of the requested statement but turns out
not to be needed; `A` is only required to satisfy `A·B = B`.) -/
theorem T5b_S10_lock (A B P : Matrix n n ℂ)
    (hBsa : Bᴴ = B) (hB2 : B * B = B) (hPsa : Pᴴ = P) (hP2 : P * P = P)
    (hAB : A * B = B) (hBA : B * A = B) (hBP : B * P = P * B) :
    A * B * P = B * P ∧ (B * P)ᴴ = B * P ∧ (B * P) * (B * P) = B * P := by
  refine ⟨by rw [hAB], ?_, ?_⟩
  · rw [Matrix.conjTranspose_mul, hPsa, hBsa, ← hBP]
  · have h : (B * P) * (B * P) = B * (P * B) * P := by noncomm_ring
    rw [h, ← hBP, show B * (B * P) * P = (B * B) * (P * P) by noncomm_ring, hB2, hP2]

/-! ### Planted-failure theorems -/

/-- **PL1 (locality is load-bearing).**  We exhibit data over `Fin 2` with
`Sᴴ = S`, `S² = S`, `S q = q`, but `C ≠ S C S`, for which the coboundary
identity of T1 fails for some `v` (here `T = 0`, `μ = 0`, so the only surviving
term is `⟪S v, C q⟫`, which is nonzero because `C q ∉ Ran S`).

Remark on faithfulness: the *literal* T1 hypotheses also include the eigen
relation `S T S q + C q = μ • q`, and that relation *by itself* forces the T1
identity (see `T1_coboundary_no_locality`); hence with the eigen relation kept,
the identity can never be broken.  The genuine content of "locality is
load-bearing" is therefore that dropping `C = S C S` breaks the coboundary
identity, which is exactly what we exhibit (with the eigen relation dropped, as
it must be). -/
theorem PL1_locality_load_bearing :
    ∃ (S T C : Matrix (Fin 2) (Fin 2) ℂ) (q : Fin 2 → ℂ) (μ : ℂ) (v : Fin 2 → ℂ),
      (Sᴴ = S) ∧ (S * S = S) ∧ (S *ᵥ q = q) ∧ (C ≠ S * C * S) ∧
        ip v (T *ᵥ q - μ • q)
          ≠ ip ((1 - S) *ᵥ v) ((1 - S) *ᵥ (T *ᵥ q)) - ip (S *ᵥ v) (C *ᵥ q) := by
  refine ⟨!![1,0;0,0], 0, !![1,0;1,0], ![1,0], 0, ![1,0], ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.conjTranspose_apply, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff]
  · ext i; fin_cases i <;> norm_num [Matrix.mulVec, Fin.sum_univ_two, dotProduct]
  · intro h
    have := congrFun (congrFun h 1) 0
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Complex.ext_iff] at this
  · unfold ip
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.star_apply, Complex.ext_iff]

/-- **PL2 (order swap detected).**  With `A·B ≠ B·A` and `S q = q`, the
wrong-order right-hand side `− ⟪V q, P₋ A B (T q)⟫` disagrees with the true third
channel `⟪A·B·(P·V − V·P) q, T q⟫`. -/
theorem PL2_order_swap :
    ∃ (A B P J T V : Matrix (Fin 3) (Fin 3) ℂ) (q : Fin 3 → ℂ),
      (Aᴴ = A ∧ A * A = A) ∧ (Bᴴ = B ∧ B * B = B) ∧ (Pᴴ = P ∧ P * P = P) ∧
        P = (2 : ℂ)⁻¹ • (1 + J) ∧ A * B ≠ B * A ∧ (A * B * P) *ᵥ q = q ∧
        ip ((A * B * (P * V - V * P)) *ᵥ q) (T *ᵥ q)
          ≠ - ip (V *ᵥ q) ((((2 : ℂ)⁻¹ • (1 - J)) * A * B) *ᵥ (T *ᵥ q)) := by
  refine ⟨!![1,0,0;0,1,0;0,0,0], !![1,0,0;0,1/2,1/2;0,1/2,1/2], !![1,0,0;0,0,0;0,0,1],
    !![1,0,0;0,-1,0;0,0,1], !![0,0,0;0,0,0;1,0,0], !![0,0,0;1,0,0;0,0,0], ![1,0,0],
    ⟨?_,?_⟩, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_fin_three, Matrix.add_apply,
      Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Complex.ext_iff]
  · intro h
    have := congrFun (congrFun h 1) 2
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Complex.ext_iff] at this
  · ext i; fin_cases i <;>
      simp [Matrix.mulVec_cons, Matrix.mulVec_empty, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Function.comp, Matrix.vecHead, Matrix.vecTail]
  · unfold ip
    simp [Matrix.one_fin_three, Matrix.mulVec_cons, Matrix.mulVec_empty, dotProduct,
      Fin.sum_univ_three, Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Pi.star_apply, Function.comp,
      Matrix.vecHead, Matrix.vecTail]

/-- **PL3 (parity revival).**  With `J B J ≠ B` (parity of `B` broken), the third
channel is nonzero for some `V`, even though `J A J = A` and `J T J = T`. -/
theorem PL3_parity_revival :
    ∃ (A B P J T V : Matrix (Fin 3) (Fin 3) ℂ) (q : Fin 3 → ℂ),
      (Aᴴ = A ∧ A * A = A) ∧ (Bᴴ = B ∧ B * B = B) ∧ (Pᴴ = P ∧ P * P = P) ∧
        P = (2 : ℂ)⁻¹ • (1 + J) ∧ (A * B * P) *ᵥ q = q ∧
        J * A * J = A ∧ J * T * J = T ∧ J * B * J ≠ B ∧
        ip ((A * B * (P * V - V * P)) *ᵥ q) (T *ᵥ q) ≠ 0 := by
  refine ⟨!![1,0,0;0,1,0;0,0,0], !![1,0,0;0,1/2,1/2;0,1/2,1/2], !![1,0,0;0,1,0;0,0,0],
    !![1,0,0;0,1,0;0,0,-1], !![0,0,0;1,0,0;0,0,0], !![0,0,0;0,0,0;1,0,0], ![1,0,0],
    ⟨?_,?_⟩, ⟨?_,?_⟩, ⟨?_,?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.conjTranspose_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.one_fin_three, Matrix.add_apply,
      Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.vecHead, Matrix.vecTail, Complex.ext_iff]
  · ext i; fin_cases i <;>
      simp [Matrix.mulVec_cons, Matrix.mulVec_empty, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_two, Function.comp, Matrix.vecHead, Matrix.vecTail]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.vecHead,
      Matrix.vecTail, Complex.ext_iff]
  · intro h
    have := congrFun (congrFun h 1) 2
    norm_num [Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.vecHead, Matrix.vecTail, Complex.ext_iff] at this
  · unfold ip
    simp [Matrix.mulVec_cons, Matrix.mulVec_empty, dotProduct,
      Fin.sum_univ_three, Matrix.smul_cons, Matrix.smul_empty, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Pi.star_apply, Function.comp,
      Matrix.vecHead, Matrix.vecTail]

end ACL
