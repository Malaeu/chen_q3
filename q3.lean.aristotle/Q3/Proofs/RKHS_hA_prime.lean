/-
Nontrivial `hA` (factorization form) for the prime compression operator
======================================================================

This file records the *exact* matrix factorization behind the Rayleigh prime block:

`T_P_comp = V† · D · V`,

where
- `V` is the “evaluation matrix” built from `prime_vec`, and
- `D` is the diagonal matrix of prime weights `w_Q(n) * Φ(ξ_n)`.

This is the algebraic heart of the desired compression statement `A = ι* T ι`.
It is not (yet) the *isometric* compression used in C1: `V` is not an isometry in general.
We keep this lemma as the canonical “nontrivial hA target” for a future true-RKHS embedding.
-/

import Q3.Basic.Defs

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open scoped ComplexConjugate

namespace Q3.Proofs

namespace PrimeCompressionFactorization

open Q3

variable (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]

/-- Evaluation matrix: rows are the conjugated prime evaluation vectors. -/
noncomputable def V :
    Matrix (Q3.Nodes K) (Fin (2 * M + 1)) ℂ :=
  fun n i => conj (Q3.prime_vec M (Q3.xi_n n) i)

/-- Diagonal matrix of weights `w_Q(n) * Φ(ξ_n)` (complexified). -/
noncomputable def D :
    Matrix (Q3.Nodes K) (Q3.Nodes K) ℂ :=
  Matrix.diagonal (fun n : Q3.Nodes K =>
    ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℝ))

/-- Exact matrix identity: `T_P_comp = V† · D · V`. -/
theorem T_P_comp_eq_conjTranspose_mul_D_mul_V :
    Q3.T_P_comp K B t M =
      (V (K := K) (M := M)).conjTranspose *
        (D (K := K) (B := B) (t := t) * V (K := K) (M := M)) := by
  classical
  ext i j
  simp [Q3.T_P_comp, V, D, Matrix.mul_apply, Matrix.conjTranspose, Matrix.diagonal,
    mul_assoc, mul_left_comm, mul_comm]

end PrimeCompressionFactorization

end Q3.Proofs
