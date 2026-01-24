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

namespace Q3

abbrev mDim (M : ℕ) : Type := Fin (2 * M + 1)

abbrev H (M : ℕ) : Type := EuclideanSpace ℂ (mDim M)

def psi (M : ℕ) : mDim M → H M :=
  fun i => (EuclideanSpace.basisFun (mDim M) ℂ) i

lemma psi_orthonormal (M : ℕ) : Orthonormal ℂ (psi M) := by
  simpa [psi] using (EuclideanSpace.basisFun (mDim M) ℂ).orthonormal

def k (K : ℝ) (M : ℕ) [Fintype (Nodes K)] : Nodes K → H M :=
  fun n => fun i => prime_vec M (xi_n n) i

lemma h_eval (K : ℝ) (M : ℕ) [Fintype (Nodes K)]
    (n : Nodes K) (i : mDim M) :
    ⟪psi M i, k (K := K) M n⟫ = prime_vec M (xi_n n) i := by
  simpa [psi, k] using
    (EuclideanSpace.basisFun_inner (x := k (K := K) M n) (i := i))

def eval (K : ℝ) (M : ℕ) [Fintype (Nodes K)] (n : Nodes K) (f : H M) : ℂ :=
  conj (⟪f, k (K := K) M n⟫)

lemma h_evalFun (K : ℝ) (M : ℕ) [Fintype (Nodes K)]
    (n : Nodes K) (i : mDim M) :
    eval (K := K) M n (psi M i) = conj (prime_vec M (xi_n n) i) := by
  simp [eval, h_eval]

end Q3
