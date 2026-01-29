/-
Utilities for the compression prime operator T_P_comp.
-/

import Q3.Basic.Defs

open scoped BigOperators
open scoped ComplexConjugate

namespace Q3.Proofs

lemma T_P_comp_conj (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    conj (Q3.T_P_comp K B t M i j) = Q3.T_P_comp K B t M j i := by
  simp [Q3.T_P_comp, mul_comm, mul_assoc]

lemma T_P_comp_real_symm (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    Q3.T_P_comp_real K B t M i j = Q3.T_P_comp_real K B t M j i := by
  have h := T_P_comp_conj (K:=K) (B:=B) (t:=t) (M:=M) i j
  simpa [Q3.T_P_comp_real] using congrArg Complex.re h

lemma T_P_comp_real_isSymm (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)] :
    (Q3.T_P_comp_real K B t M).IsSymm := by
  ext i j
  simp [Matrix.transpose_apply, T_P_comp_real_symm (K:=K) (B:=B) (t:=t) (M:=M)]

lemma T_P_comp_entry_norm_le_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    ‖Q3.T_P_comp K B t M i j‖ ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ := by
  classical
  simpa [Q3.T_P_comp]
    using (norm_sum_le (s := Finset.univ)
      (f := fun n : Q3.Nodes K =>
        ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)))

lemma T_P_comp_entry_norm_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    ‖Q3.T_P_comp K B t M i j‖ ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
  classical
  refine le_trans (T_P_comp_entry_norm_le_sum (K:=K) (B:=B) (t:=t) (M:=M) i j) ?_
  refine Finset.sum_le_sum ?_
  intro n hn
  have hnorm :
      ‖Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ =
        (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
    simpa using (Q3.prime_vec_mul_conj_norm (M:=M) (ξ:=Q3.xi_n n) i j)
  refine le_of_eq ?_
  calc
    ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
          Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖
        = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
            (Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j))‖ := by
            simp [mul_assoc]
    _ = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          ‖Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)‖ := by
          exact
            (norm_mul
              ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)
              (Q3.prime_vec M (Q3.xi_n n) i * conj (Q3.prime_vec M (Q3.xi_n n) j)))
    _ = ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
          rw [hnorm]

lemma T_P_comp_real_entry_abs_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i j : Fin (2 * M + 1)) :
    |Q3.T_P_comp_real K B t M i j| ≤
      ∑ n : Q3.Nodes K,
        ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ *
          (1 / Real.sqrt (2 * M + 1 : ℝ))^2 := by
  have hRe :
      |(Q3.T_P_comp K B t M i j).re| ≤ ‖Q3.T_P_comp K B t M i j‖ := by
    simpa using (RCLike.abs_re_le_norm (z := Q3.T_P_comp K B t M i j))
  have hbound :=
    T_P_comp_entry_norm_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i j
  simpa [Q3.T_P_comp_real] using (le_trans hRe hbound)

lemma T_P_comp_real_row_sum_le_weight_sum (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    (i : Fin (2 * M + 1)) :
    ∑ j, |Q3.T_P_comp_real K B t M i j| ≤
      ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ := by
  classical
  set c : ℝ := (1 / Real.sqrt (2 * M + 1 : ℝ))^2
  set w : ℝ :=
    ∑ n : Q3.Nodes K, ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖
  set const : ℝ :=
    ∑ n : Q3.Nodes K,
      ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c
  have hentry : ∀ j : Fin (2 * M + 1),
      |Q3.T_P_comp_real K B t M i j| ≤ const := by
    intro j
    have hbound :=
      T_P_comp_real_entry_abs_le_weight_sum (K:=K) (B:=B) (t:=t) (M:=M) i j
    simpa [const, c] using hbound
  have hsum :
      (∑ j : Fin (2 * M + 1), |Q3.T_P_comp_real K B t M i j|) ≤
        ∑ j : Fin (2 * M + 1), const := by
    refine Finset.sum_le_sum ?_
    intro j hj
    exact hentry j
  have hconst_mul :
      (2 * M + 1 : ℝ) * c = 1 := by
    have hpos : (0 : ℝ) < (2 * M + 1 : ℝ) := by positivity
    have hsqrt :
        (Real.sqrt (2 * M + 1 : ℝ))^2 = (2 * M + 1 : ℝ) := by
      simpa [pow_two] using
        (Real.sq_sqrt (show 0 ≤ (2 * M + 1 : ℝ) by positivity))
    calc
      (2 * M + 1 : ℝ) * c
          = (2 * M + 1 : ℝ) * (1 / (Real.sqrt (2 * M + 1 : ℝ))^2) := by
              simp [c, pow_two, mul_comm]
      _ = (2 * M + 1 : ℝ) * (1 / (2 * M + 1 : ℝ)) := by simp [hsqrt]
      _ = 1 := by field_simp [hpos.ne']
  have hsumconst :
      (∑ j : Fin (2 * M + 1), const) = (2 * M + 1 : ℝ) * const := by
    simp [const]
  have hconst' : (2 * M + 1 : ℝ) * const = w := by
    calc
      (2 * M + 1 : ℝ) * const
          = (2 * M + 1 : ℝ) *
              (∑ n : Q3.Nodes K,
                ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c) := by
                simp [const]
      _ = ∑ n : Q3.Nodes K,
            (2 * M + 1 : ℝ) *
              (‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * c) := by
                simp [Finset.mul_sum, mul_comm, mul_assoc]
      _ = ∑ n : Q3.Nodes K,
            ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * ((2 * M + 1 : ℝ) * c) := by
                simp [mul_comm, mul_left_comm, mul_assoc]
      _ = w := by
            calc
              (∑ n : Q3.Nodes K,
                ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * ((2 * M + 1 : ℝ) * c))
                  = ∑ n : Q3.Nodes K,
                      ‖((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ)‖ * 1 := by
                        simp [hconst_mul]
              _ = w := by simp [w]
  exact le_trans hsum (by simp [hsumconst, hconst'])

end Q3.Proofs
