/-
Q3 Aristotle Bridge Lemmas
==========================

This file bridges between Aristotle-generated proofs and Q3 axiom definitions.

Key difference: Aristotle uses ξ(n) = log(n), Q3 uses xi_n(n) = log(n)/(2π).
The rescaling: xi_n = ξ / (2π), so (xi_n_i - xi_n_j)² = (ξ_i - ξ_j)² / (4π²).

For heat kernel T_P with exponent -(Δξ)²/(4t):
  T_P_Q3(t) uses xi_n: exp(-(xi_n_i - xi_n_j)²/(4t))
  T_P_Aristotle(t') uses ξ: exp(-(ξ_i - ξ_j)²/(4t'))

Setting t' = t · (2π)² gives T_P_Q3(t) = T_P_Aristotle(t').
So contraction at t_Aristotle implies contraction at t_Q3 = t_Aristotle/(4π²).

The mathematical content is equivalent; this file provides formal bridges.
-/

import Q3.Basic.Defs
import Q3.Axioms
import Q3.Proofs.RKHS_contraction

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

open scoped BigOperators
open scoped Real
open scoped Classical
open scoped Matrix.Norms.L2Operator

set_option maxHeartbeats 400000

namespace Q3.Bridge

/-! ## Coordinate Rescaling -/

/-- Aristotle's spectral coordinate: ξ(n) = log(n) -/
noncomputable def xi_aristotle (n : ℕ) : ℝ := Real.log n

/-- The rescaling relation: xi_n = xi_aristotle / (2π) -/
lemma xi_rescaling (n : ℕ) : Q3.xi_n n = xi_aristotle n / (2 * Real.pi) := by
  unfold Q3.xi_n xi_aristotle
  ring

/-- Squared difference rescaling -/
lemma xi_diff_sq_rescaling (n m : ℕ) :
    (Q3.xi_n n - Q3.xi_n m)^2 = (xi_aristotle n - xi_aristotle m)^2 / (4 * Real.pi^2) := by
  rw [xi_rescaling n, xi_rescaling m]
  field_simp
  ring

/-! ## Heat Parameter Rescaling -/

/-- If Aristotle proves contraction at t_A, Q3 has contraction at t_A / (4π²) -/
lemma heat_param_rescaling (t_aristotle : ℝ) (ht : t_aristotle > 0) :
    let t_q3 := t_aristotle / (4 * Real.pi^2)
    t_q3 > 0 := by
  simp only
  positivity

/-- The exponential factors are equal under rescaling -/
lemma exp_factor_eq (n m : ℕ) (t_aristotle : ℝ) (ht : t_aristotle > 0) :
    let t_q3 := t_aristotle / (4 * Real.pi^2)
    Real.exp (-(Q3.xi_n n - Q3.xi_n m)^2 / (4 * t_q3)) =
    Real.exp (-(xi_aristotle n - xi_aristotle m)^2 / (4 * t_aristotle)) := by
  simp only
  congr 1
  rw [xi_diff_sq_rescaling]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hpi2 : Real.pi^2 ≠ 0 := pow_ne_zero 2 hpi
  have ht4 : 4 * Real.pi^2 ≠ 0 := by positivity
  field_simp [ht4, ht.ne']

/-! ## K Parameter Rescaling -/

/-- Aristotle's K parameter from Q3's K -/
noncomputable def K_ar (K_Q3 : ℝ) : ℝ := 2 * Real.pi * K_Q3

/-- Membership in Q3.Nodes K iff log(n) ≤ 2πK.
    PROVEN: follows from definition of Q3.Nodes and xi_n. -/
theorem mem_Q3Nodes_iff_log_le (n : ℕ) (K : ℝ) (hK : K ≥ 0) :
    n ∈ Q3.Nodes K ↔ 2 ≤ n ∧ Real.log n ≤ K_ar K := by
  unfold Q3.Nodes Q3.xi_n K_ar
  have hn_cast : (2 : ℕ) ≤ n → (n : ℝ) ≥ 1 := by
    intro h
    have : (n : ℝ) ≥ (2 : ℝ) := Nat.cast_le.mpr h
    linarith
  have h2pi_pos : 2 * Real.pi > 0 := mul_pos (by norm_num) Real.pi_pos
  constructor
  · intro ⟨habs, hn⟩
    constructor
    · exact hn
    · have hpos : Real.log n / (2 * Real.pi) ≥ 0 := by
        apply div_nonneg
        · exact Real.log_nonneg (hn_cast hn)
        · exact h2pi_pos.le
      rw [abs_of_nonneg hpos] at habs
      calc Real.log n = Real.log n / (2 * Real.pi) * (2 * Real.pi) := by
             field_simp
           _ ≤ K * (2 * Real.pi) := by
             apply mul_le_mul_of_nonneg_right habs h2pi_pos.le
           _ = 2 * Real.pi * K := by ring
  · intro ⟨hn, hlog⟩
    constructor
    · have hpos : Real.log n / (2 * Real.pi) ≥ 0 := by
        apply div_nonneg
        · exact Real.log_nonneg (hn_cast hn)
        · exact h2pi_pos.le
      rw [abs_of_nonneg hpos]
      calc Real.log n / (2 * Real.pi) ≤ (2 * Real.pi * K) / (2 * Real.pi) := by
             apply div_le_div_of_nonneg_right hlog h2pi_pos.le
           _ = K := by field_simp
    · exact hn

/-- Every element of Q3.Nodes K is in Aristotle's nodes finset.
    PROVEN: follows from log(n) ≤ K_ar K ⟹ n ≤ exp(K_ar K) ⟹ n ∈ range. -/
theorem mem_nodes_finset_of_mem_Q3Nodes (n : ℕ) (K : ℝ) (hK : K ≥ 1) :
    n ∈ Q3.Nodes K → n ∈ _root_.nodes (K_ar K) := by
  intro hmem
  -- Use the characterization of Q3.Nodes membership
  have hK_nonneg : K ≥ 0 := le_trans (by norm_num) hK
  rw [mem_Q3Nodes_iff_log_le n K hK_nonneg] at hmem
  obtain ⟨hn2, hlog⟩ := hmem
  -- Unfold nodes definition
  unfold _root_.nodes
  simp only [Finset.mem_filter, Finset.mem_range]
  -- Need: n < floor(exp(K_ar K)) + 1 ∧ 1 ≤ n ∧ log n ≤ K_ar K
  refine ⟨?_, ?_, hlog⟩
  · -- n < floor(exp(K_ar K)) + 1
    have hn_pos : (0 : ℝ) < n := by
      have : (2 : ℕ) ≤ n := hn2
      have : (2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr this
      linarith
    have hexp_log : Real.exp (Real.log n) = n := Real.exp_log hn_pos
    have hle_exp : (n : ℝ) ≤ Real.exp (K_ar K) := by
      rw [← hexp_log]
      exact Real.exp_le_exp.mpr hlog
    have hle_floor : n ≤ Nat.floor (Real.exp (K_ar K)) := by
      exact Nat.le_floor hle_exp
    omega
  · -- 1 ≤ n
    omega

/-! ## Weight Functions Agreement -/

/-- The RKHS weights are identical in both formulations -/
lemma w_RKHS_eq (n : ℕ) : Q3.w_RKHS n = ArithmeticFunction.vonMangoldt n / Real.sqrt n := rfl

/-- Aristotle's w_RKHS equals Q3's w_RKHS -/
lemma w_RKHS_aristotle_eq (n : ℕ) : _root_.w_RKHS n = Q3.w_RKHS n := rfl

/-! ## Submatrix Operator Norm Bound -/

private noncomputable def extend_vec {ι κ : Type*} (f : κ → ι) (v : EuclideanSpace ℝ κ) :
    EuclideanSpace ℝ ι :=
  (WithLp.toLp 2 (fun i => if h : ∃ k, f k = i then v (Classical.choose h) else 0) :
    EuclideanSpace ℝ ι)

private lemma extend_vec_apply {ι κ : Type*} [DecidableEq ι]
    (f : κ → ι) (hf : Function.Injective f) (v : EuclideanSpace ℝ κ) (k : κ) :
    extend_vec f v (f k) = v k := by
  classical
  have h' : ∃ k', f k' = f k := ⟨k, rfl⟩
  have hk' : Classical.choose h' = k := hf (Classical.choose_spec h')
  change (if h : ∃ k', f k' = f k then v (Classical.choose h) else 0) = v k
  simpa [h', hk']

private lemma norm_restrict_le {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (f : κ → ι) (hf : Function.Injective f) (w : EuclideanSpace ℝ ι) :
    ‖(WithLp.toLp 2 (fun k : κ => w (f k)) : EuclideanSpace ℝ κ)‖ ≤ ‖w‖ := by
  classical
  have hsum_image :
      (∑ k : κ, (w (f k)) ^ 2) =
        ∑ i ∈ (Finset.univ.image f), (w i) ^ 2 := by
    have h :=
        (Finset.sum_image (s := (Finset.univ : Finset κ)) (g := f)
          (f := fun i : ι => (w i) ^ 2) (by
            intro x hx y hy hxy
            exact hf hxy))
    simpa using h.symm
  have hsum_le :
      ∑ i ∈ (Finset.univ.image f), (w i) ^ 2 ≤ ∑ i : ι, (w i) ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
    · intro i hi
      exact Finset.mem_univ i
    · intro i hi hnot
      exact sq_nonneg _
  have hsum :
      ∑ k : κ, (w (f k)) ^ 2 ≤ ∑ i : ι, (w i) ^ 2 := by
    calc
      ∑ k : κ, (w (f k)) ^ 2
          = ∑ i ∈ (Finset.univ.image f), (w i) ^ 2 := hsum_image
      _ ≤ ∑ i : ι, (w i) ^ 2 := hsum_le
  have hsqrt := Real.sqrt_le_sqrt hsum
  have hnorm_left :
      ‖(WithLp.toLp 2 (fun k : κ => w (f k)) : EuclideanSpace ℝ κ)‖ =
        √(∑ k : κ, (w (f k)) ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using
      (EuclideanSpace.norm_eq (WithLp.toLp 2 (fun k : κ => w (f k)) : EuclideanSpace ℝ κ))
  have hnorm_right :
      ‖w‖ = √(∑ i : ι, (w i) ^ 2) := by
    simpa [Real.norm_eq_abs, sq_abs] using (EuclideanSpace.norm_eq w)
  calc
    ‖(WithLp.toLp 2 (fun k : κ => w (f k)) : EuclideanSpace ℝ κ)‖
        = √(∑ k : κ, (w (f k)) ^ 2) := hnorm_left
    _ ≤ √(∑ i : ι, (w i) ^ 2) := hsqrt
    _ = ‖w‖ := hnorm_right.symm

private lemma norm_extend_eq {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
    (f : κ → ι) (hf : Function.Injective f) (v : EuclideanSpace ℝ κ) :
    ‖(extend_vec f v : EuclideanSpace ℝ ι)‖ = ‖v‖ := by
  classical
  have hsum_image :
      ∑ i ∈ (Finset.univ.image f), (extend_vec f v i) ^ 2 = ∑ k : κ, (v k) ^ 2 := by
    have h :=
        (Finset.sum_image (s := (Finset.univ : Finset κ)) (g := f)
          (f := fun i : ι => (extend_vec f v i) ^ 2) (by
            intro x hx y hy hxy
            exact hf hxy))
    simpa [extend_vec_apply, hf] using h
  have hsum_total :
      ∑ i : ι, (extend_vec f v i) ^ 2 =
        ∑ i ∈ (Finset.univ.image f), (extend_vec f v i) ^ 2 := by
    have hsubset : (Finset.univ.image f) ⊆ (Finset.univ : Finset ι) := by
      intro i hi
      exact Finset.mem_univ i
    have hzero :
        ∀ i ∈ (Finset.univ : Finset ι), i ∉ (Finset.univ.image f) →
          (extend_vec f v i) ^ 2 = 0 := by
      intro i _ hnot
      have hnot' : ¬ ∃ k, f k = i := by
        intro h
        have : i ∈ (Finset.univ.image f) := by
          rcases h with ⟨k, hk⟩
          exact Finset.mem_image.mpr ⟨k, Finset.mem_univ k, hk⟩
        exact hnot this
      have hz : extend_vec f v i = 0 := by
        simpa [extend_vec, hnot']
      simpa [hz]
    have h := Finset.sum_subset hsubset hzero
    simpa using h.symm
  have hsum :
      ∑ i : ι, (extend_vec f v i) ^ 2 = ∑ k : κ, (v k) ^ 2 :=
    hsum_total.trans hsum_image
  have hsqrt := congrArg Real.sqrt hsum
  simpa [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs] using hsqrt

private lemma opNorm_submatrix_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ]
    (A : Matrix ι ι ℝ) (f : κ → ι) (hf : Function.Injective f) :
    ‖(Matrix.toEuclideanLin (Matrix.submatrix A f f)).toContinuousLinearMap‖ ≤
      ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ := by
  classical
  let restrict : EuclideanSpace ℝ ι → EuclideanSpace ℝ κ :=
    fun w => (WithLp.toLp 2 (fun k : κ => w (f k)) : EuclideanSpace ℝ κ)
  have h_submatrix : ∀ v,
      (Matrix.toEuclideanLin (Matrix.submatrix A f f)) v =
        restrict ((Matrix.toEuclideanLin A) (extend_vec f v)) := by
    intro v
    ext k
    simp [Matrix.toEuclideanLin_apply, WithLp.toLp, WithLp.ofLp, Matrix.submatrix,
      Matrix.mulVec, restrict]
    -- Reduce to sums over the image of f.
    have hsum_image :
        ∑ i ∈ (Finset.univ.image f), A (f k) i * extend_vec f v i =
          ∑ j : κ, A (f k) (f j) * v j := by
      have h :=
          (Finset.sum_image (s := (Finset.univ : Finset κ)) (g := f)
            (f := fun i : ι => A (f k) i * extend_vec f v i) (by
              intro x hx y hy hxy
              exact hf hxy))
      simpa [extend_vec_apply, hf] using h
    have hsum_total :
        ∑ i ∈ (Finset.univ.image f), A (f k) i * extend_vec f v i =
          ∑ i : ι, A (f k) i * extend_vec f v i := by
      have hsubset : (Finset.univ.image f) ⊆ (Finset.univ : Finset ι) := by
        intro i hi
        exact Finset.mem_univ i
      have hzero :
          ∀ i ∈ (Finset.univ : Finset ι), i ∉ (Finset.univ.image f) →
            A (f k) i * extend_vec f v i = 0 := by
        intro i _ hnot
        have hnot' : ¬ ∃ j, f j = i := by
          intro h
          have : i ∈ (Finset.univ.image f) := by
            rcases h with ⟨j, hj⟩
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj⟩
          exact hnot this
        have hz : extend_vec f v i = 0 := by
          simpa [extend_vec, hnot']
        simpa [hz]
      have h := Finset.sum_subset hsubset hzero
      simpa using h
    calc
      ∑ j : κ, A (f k) (f j) * v j
          = ∑ i ∈ (Finset.univ.image f), A (f k) i * extend_vec f v i := by
              symm
              exact hsum_image
      _ = ∑ i : ι, A (f k) i * extend_vec f v i := by
              exact hsum_total
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ ?_
  · exact norm_nonneg _
  · intro v
    have hA :=
      (Matrix.toEuclideanLin A).toContinuousLinearMap.le_opNorm
        (extend_vec f v : EuclideanSpace ℝ ι)
    calc
      ‖(Matrix.toEuclideanLin (Matrix.submatrix A f f)).toContinuousLinearMap v‖
          = ‖(Matrix.toEuclideanLin (Matrix.submatrix A f f)) v‖ := by rfl
      _ = ‖restrict ((Matrix.toEuclideanLin A) (extend_vec f v))‖ := by
            simp [h_submatrix]
      _ ≤ ‖(Matrix.toEuclideanLin A) (extend_vec f v : EuclideanSpace ℝ ι)‖ := by
              dsimp [restrict]
              exact norm_restrict_le f hf ((Matrix.toEuclideanLin A)
                (extend_vec f v : EuclideanSpace ℝ ι))
      _ ≤ ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ * ‖extend_vec f v‖ := hA
      _ = ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ * ‖v‖ := by
              simp [norm_extend_eq f hf]

/-! ## Matrix Entry Rescaling -/

/-- Bridge: xi_aristotle = _root_.ξ (both are log(n)) -/
lemma xi_aristotle_eq_root_xi (n : ℕ) : xi_aristotle n = _root_.ξ n := rfl

/-- The exponential kernel entries are equal under t-rescaling.
    This is the key bridge lemma: T_P_matrix entries match under coordinate change.
    PROVEN using exp_factor_eq + coordinate equivalence. -/
theorem exp_entry_rescale (i j : ℕ) (t_ar : ℝ) (ht : t_ar > 0) :
    let t_q3 := t_ar / (4 * Real.pi^2)
    Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t_q3)) =
    Real.exp (-(_root_.ξ i - _root_.ξ j)^2 / (4 * t_ar)) := by
  simp only
  rw [← xi_aristotle_eq_root_xi i, ← xi_aristotle_eq_root_xi j]
  exact exp_factor_eq i j t_ar ht

/-! ## Node Set Equivalence -/

/-- Aristotle's nodes for K_ar vs Q3's Nodes for K.
    Aristotle: nodes(K_ar) = {n | 1 ≤ n ∧ log(n) ≤ K_ar}
    Q3: Nodes(K) = {n | |xi_n n| ≤ K ∧ n ≥ 2}

    With K_ar = 2πK:
    - log(n) ≤ 2πK ⟺ log(n)/(2π) ≤ K ⟺ xi_n n ≤ K
    - For n ≥ 2, xi_n n = log(n)/(2π) ≥ 0, so |xi_n n| = xi_n n -/
lemma mem_Q3Nodes_iff (n : ℕ) (K : ℝ) (hK : K ≥ 0) :
    n ∈ Q3.Nodes K ↔ n ≥ 2 ∧ Q3.xi_n n ≤ K := by
  unfold Q3.Nodes Q3.xi_n
  have hn_ge_1 : n ≥ 2 → (n : ℝ) ≥ 1 := fun h =>
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (Nat.cast_le.mpr h)
  have h2pi_pos : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  constructor
  · intro ⟨habs, hn⟩
    have hpos : Real.log n / (2 * Real.pi) ≥ 0 := by
      apply div_nonneg
      · exact Real.log_nonneg (hn_ge_1 hn)
      · exact le_of_lt h2pi_pos
    rw [abs_of_nonneg hpos] at habs
    exact ⟨hn, habs⟩
  · intro ⟨hn, hle⟩
    constructor
    · have hpos : Real.log n / (2 * Real.pi) ≥ 0 := by
        apply div_nonneg
        · exact Real.log_nonneg (hn_ge_1 hn)
        · exact le_of_lt h2pi_pos
      rw [abs_of_nonneg hpos]
      exact hle
    · exact hn

/-! ## RKHS Contraction Bridge Theorem -/

/-- **Bridge axiom** (well-justified): Aristotle's RKHS_contraction → Q3's axiom.

    **Mathematical proof** (verified in RKHS_contraction.lean):
    1. Aristotle proves: `RKHS_contraction (K_ar K)` where `K_ar K = 2πK`
       giving ∃ t_ar > 0, ∃ ρ < 1, T_P_norm (K_ar K) t_ar ≤ ρ

    2. Define t_Q3 := t_ar / (4π²). Then t_Q3 > 0.

    3. By `exp_entry_rescale`: T_P_Q3[i,j](t_Q3) = T_P_Aristotle[i,j](t_ar)
       (matrix entries are identical under coordinate rescaling)

    4. Therefore ||T_P_Q3(t_Q3)|| = ||T_P_Aristotle(t_ar)|| ≤ ρ < 1

    **Why this is an axiom not a theorem**:
    - Aristotle's proof uses `Node K` (subtype) with fixed `nodes K`
    - Q3's axiom uses arbitrary `S : Finset ℕ` with membership condition
    - Full formalization requires subtype/finset conversion (tedious, not mathematically interesting)

    **Source**: `Q3/Proofs/RKHS_contraction.lean` theorem `RKHS_contraction` -/
theorem RKHS_contraction_bridge (K : ℝ) (hK : K ≥ 1) :
    ∃ t > 0, ∃ ρ : ℝ, ρ < 1 ∧
    ∀ (S : Finset ℕ), (∀ n ∈ S, n ∈ Q3.Nodes K) →
      let T_P : Matrix S S ℝ := fun i j =>
        Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
        Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t))
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤ ρ := by
  classical
  have h2pi_ge_one : (1 : ℝ) ≤ 2 * Real.pi := by
    have h2pi_gt : (1 : ℝ) < 2 * Real.pi := by
      nlinarith [Real.pi_gt_three]
    exact le_of_lt h2pi_gt
  have h2pi_pos : 0 ≤ 2 * Real.pi := by
    nlinarith [Real.pi_pos]
  have hK_ar : K_ar K ≥ 1 := by
    have h2pi_le : 2 * Real.pi ≤ 2 * Real.pi * K := by
      simpa using (mul_le_mul_of_nonneg_left hK h2pi_pos)
    unfold K_ar
    exact le_trans h2pi_ge_one h2pi_le
  obtain ⟨t_ar, ht_ar, ρ, hρ_lt, h_norm⟩ :=
    _root_.RKHS_contraction (K_ar K) hK_ar
  let t_q3 := t_ar / (4 * Real.pi^2)
  have ht_q3 : t_q3 > 0 := by
    have hpi : 0 < 4 * Real.pi^2 := by positivity
    exact div_pos ht_ar hpi
  refine ⟨t_q3, ht_q3, ρ, hρ_lt, ?_⟩
  intro S hS
  let toNode : S → _root_.Node (K_ar K) := fun s =>
    ⟨s.1, mem_nodes_finset_of_mem_Q3Nodes s.1 K hK (hS s.1 s.2)⟩
  have h_inj : Function.Injective toNode := by
    intro a b h
    apply Subtype.ext
    have hval :
        (toNode a).1 = (toNode b).1 :=
      congrArg (fun x : _root_.Node (K_ar K) => x.1) h
    simpa [toNode] using hval
  let T_full : Matrix (_root_.Node (K_ar K)) (_root_.Node (K_ar K)) ℝ :=
    _root_.T_P_matrix (K_ar K) t_ar
  have hnode_nonempty : Nonempty (_root_.Node (K_ar K)) := by
    refine ⟨⟨1, ?_⟩⟩
    unfold _root_.nodes
    refine Finset.mem_filter.mpr ?_
    refine ⟨?_, ?_⟩
    · have h_exp : 1 ≤ Real.exp (K_ar K) :=
        (Real.one_le_exp_iff).2 (by linarith [hK_ar])
      have h_floor : 1 ≤ Nat.floor (Real.exp (K_ar K)) :=
        (Nat.one_le_floor_iff _).2 h_exp
      exact (Finset.mem_range).2 ((Nat.lt_succ_iff).2 h_floor)
    · refine ⟨by norm_num, ?_⟩
      have hK_ar_nonneg : 0 ≤ K_ar K := by linarith [hK_ar]
      simpa [Real.log_one] using hK_ar_nonneg
  letI : Nonempty (_root_.Node (K_ar K)) := hnode_nonempty
  let T_P : Matrix S S ℝ := fun i j =>
    Real.sqrt (Q3.w_RKHS i) * Real.sqrt (Q3.w_RKHS j) *
    Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t_q3))
  have h_TP_eq : T_P = Matrix.submatrix T_full toNode toNode := by
    ext i j
    have h_exp :
        Real.exp (-(Q3.xi_n i - Q3.xi_n j)^2 / (4 * t_q3)) =
          Real.exp (-(_root_.ξ i - _root_.ξ j)^2 / (4 * t_ar)) := by
      simpa [xi_aristotle_eq_root_xi, t_q3] using
        exp_factor_eq (i : ℕ) (j : ℕ) t_ar ht_ar
    simp [T_P, T_full, _root_.T_P_matrix, Matrix.submatrix, toNode,
      w_RKHS_aristotle_eq, h_exp]
  have h_sub :
      ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖ ≤
        ‖(Matrix.toEuclideanLin T_full).toContinuousLinearMap‖ := by
    classical
    by_cases hS_empty : S = ∅
    · subst hS_empty
      have hzero : (Matrix.toEuclideanLin T_P).toContinuousLinearMap = 0 := by
        ext v i
        cases i with
        | mk val property => cases property
      calc
        ‖(Matrix.toEuclideanLin T_P).toContinuousLinearMap‖
            = ‖(0 : EuclideanSpace ℝ { x // x ∈ (∅ : Finset ℕ) } →L[ℝ]
                  EuclideanSpace ℝ { x // x ∈ (∅ : Finset ℕ) })‖ := by
                rw [hzero]
        _ = 0 := ContinuousLinearMap.opNorm_zero
        _ ≤ ‖(Matrix.toEuclideanLin T_full).toContinuousLinearMap‖ := by
              exact norm_nonneg _
    · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      have hS_type : Nonempty (S : Type _) := (Finset.nonempty_coe_sort).2 hS_nonempty
      letI : Nonempty (S : Type _) := hS_type
      simpa [h_TP_eq] using (opNorm_submatrix_le (A := T_full) (f := toNode) h_inj)
  have h_norm_full :
      ‖(Matrix.toEuclideanLin T_full).toContinuousLinearMap‖ ≤ ρ := by
    simpa [_root_.T_P_norm, T_full] using h_norm
  exact le_trans h_sub h_norm_full

/-- **Bridge axiom**: RKHS contraction in bundled form for main theorems.

    This bridges directly to Q3.RKHS_contraction_data which uses:
    - `Set ℕ` with `[Fintype Nodes_K]` instance
    - `‖T_P‖` as matrix operator norm

    **Source**: `RKHS_contraction_bridge` + type coercion -/
theorem RKHS_contraction_data_of_bridge (K : ℝ) (hK : K ≥ 1) :
    Q3.RKHS_contraction_data K := by
  unfold Q3.RKHS_contraction_data
  exact RKHS_contraction_bridge K hK

/-! ## Documentation of Bridge Status

### Proven by Aristotle (in aristotle coordinates ξ = log n):
1. RKHS_contraction: ∃ t > 0, ∃ ρ < 1, ||T_P|| ≤ ρ ✓
2. A3_bridge: λ_min(T_M[P_A] - T_P) ≥ c₀/4 ✓
3. Q_Lipschitz: Q is Lipschitz on W_K ✓
4. Q_nonneg_on_atoms: A3 + RKHS ⟹ Q ≥ 0 on atoms ✓
5. A1_density: Fejér×heat atoms dense in W_K ✓

### Bridge Status:
- Mathematical equivalence: ✓ (coordinate rescaling by 2π)
- Formal Lean equivalence: Requires explicit proofs

### Why the bridge is mathematically sound:
- The spectral coordinate xi_n = ξ/(2π) is just a rescaling
- All inequalities and bounds transfer under rescaling
- The contraction constant ρ < 1 is preserved
- The positivity Q ≥ 0 is coordinate-independent
-/

end Q3.Bridge
