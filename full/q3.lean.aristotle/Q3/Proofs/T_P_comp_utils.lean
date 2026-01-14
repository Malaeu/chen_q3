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

end Q3.Proofs
