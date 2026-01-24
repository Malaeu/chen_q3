import Q3.Basic.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
C1 embedding: finite-dimensional dictionary model (Option B).

We realize the compression subspace V as `EuclideanSpace ℂ (Fin (2*M+1))`,
choose the standard orthonormal basis `ψ`, and define kernel sections `k n` by
their coordinates `prime_vec`. With this concrete model, `h_eval` closes by `simp`.
-/

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexConjugate

namespace Q3

abbrev mDim (M : ℕ) : Type := Fin (2 * M + 1)

abbrev H (M : ℕ) : Type := EuclideanSpace ℂ (mDim M)

def psi (M : ℕ) : mDim M → H M :=
  fun i => EuclideanSpace.single i (1 : ℂ)

lemma psi_orthonormal (M : ℕ) : Orthonormal ℂ (psi M) := by
  simpa [psi] using (EuclideanSpace.orthonormal_single (𝕜:=ℂ) (ι:=mDim M))

def k (K : ℝ) (M : ℕ) [Fintype (Nodes K)] : Nodes K → H M :=
  fun n => fun i => prime_vec M (xi_n n) i

lemma h_eval (K : ℝ) (M : ℕ) [Fintype (Nodes K)]
    (n : Nodes K) (i : mDim M) :
    ⟪psi M i, k (K := K) M n⟫_ℂ = prime_vec M (xi_n n) i := by
  simp [psi, k, EuclideanSpace.inner_single_left]

def eval (K : ℝ) (M : ℕ) [Fintype (Nodes K)] (n : Nodes K) (f : H M) : ℂ :=
  conj (⟪f, k (K := K) M n⟫_ℂ)

lemma h_evalFun (K : ℝ) (M : ℕ) [Fintype (Nodes K)]
    (n : Nodes K) (i : mDim M) :
    eval (K := K) M n (psi M i) = conj (prime_vec M (xi_n n) i) := by
  simp [eval, h_eval]

lemma T_P_comp_eq_compression (K B t : ℝ) (M : ℕ) [Fintype (Nodes K)] :
    Q3.T_P_comp K B t M =
      fun i j =>
        ∑ n : Nodes K,
          ((Q3.w_Q n * Q3.fejer_heat_window B t (Q3.xi_n n)) : ℂ) *
            ⟪psi M i, k (K := K) M n⟫_ℂ * conj (⟪psi M j, k (K := K) M n⟫_ℂ) := by
  ext i j
  simp [Q3.T_P_comp, h_eval]

end Q3
