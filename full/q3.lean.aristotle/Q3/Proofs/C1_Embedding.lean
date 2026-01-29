/-
C1 Embedding (Option B)
=======================

Option B builds a finite-dimensional dictionary subspace and embeds a Euclidean
space into the RKHS by choosing an orthonormal basis of that span. The resulting
compression map is used for the Rayleigh ↔ RKHS operator comparison.
-/-

import Q3.Basic.Defs
import Mathlib
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators
open scoped InnerProductSpace
open scoped ComplexConjugate

namespace Q3.Proofs.C1Embedding

section Compression

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
  [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 H] [CompleteSpace E] [CompleteSpace H]

/-- Compression of a bounded operator by a linear isometry. -/
noncomputable def compression (ι : E →ₗᵢ[𝕜] H) (T : H →L[𝕜] H) : E →L[𝕜] E :=
  (ι.toContinuousLinearMap.adjoint).comp (T.comp ι.toContinuousLinearMap)

/-- C1: compression does not increase the operator norm. -/
lemma compression_opNorm_le [Nontrivial E] (ι : E →ₗᵢ[𝕜] H) (T : H →L[𝕜] H) :
    ‖compression ι T‖ ≤ ‖T‖ := by
  have hι : ‖ι.toContinuousLinearMap‖ = 1 :=
    (LinearIsometry.norm_toContinuousLinearMap (f := ι))
  have hιadj : ‖ι.toContinuousLinearMap.adjoint‖ = 1 := by
    have h' :
        ‖ι.toContinuousLinearMap.adjoint‖ = ‖ι.toContinuousLinearMap‖ :=
      (LinearIsometryEquiv.norm_map (ContinuousLinearMap.adjoint) (ι.toContinuousLinearMap))
    calc
      ‖ι.toContinuousLinearMap.adjoint‖ = ‖ι.toContinuousLinearMap‖ := h'
      _ = 1 := hι
  have h1 :
      ‖(ι.toContinuousLinearMap.adjoint).comp (T.comp ι.toContinuousLinearMap)‖ ≤
        ‖ι.toContinuousLinearMap.adjoint‖ * ‖T.comp ι.toContinuousLinearMap‖ := by
    simpa using
      (ContinuousLinearMap.opNorm_comp_le (h := ι.toContinuousLinearMap.adjoint)
        (f := T.comp ι.toContinuousLinearMap))
  have h2 :
      ‖T.comp ι.toContinuousLinearMap‖ ≤ ‖T‖ * ‖ι.toContinuousLinearMap‖ := by
    simpa using (ContinuousLinearMap.opNorm_comp_le (h := T) (f := ι.toContinuousLinearMap))
  calc
    ‖compression ι T‖
        = ‖(ι.toContinuousLinearMap.adjoint).comp (T.comp ι.toContinuousLinearMap)‖ := rfl
    _ ≤ ‖ι.toContinuousLinearMap.adjoint‖ * ‖T.comp ι.toContinuousLinearMap‖ := h1
    _ ≤ ‖ι.toContinuousLinearMap.adjoint‖ * (‖T‖ * ‖ι.toContinuousLinearMap‖) := by
          exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖T‖ := by
          simp [hι, hιadj]

lemma compression_lift_eq (ι : E →ₗᵢ[𝕜] H) (A : E →L[𝕜] E) :
    compression ι
        (ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)) = A := by
  have h_adj :
      (ι.toContinuousLinearMap.adjoint).comp ι.toContinuousLinearMap = 1 := by
    have hnorm : ∀ x : E, ‖ι.toContinuousLinearMap x‖ = ‖x‖ := by
      intro x
      simpa using (ι.norm_map x)
    exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self
      (u := ι.toContinuousLinearMap)).1 hnorm
  have h_adj_apply : ∀ x : E, (ι.toContinuousLinearMap.adjoint) (ι x) = x := by
    intro x
    have h' := congrArg (fun f => f x) h_adj
    simpa [ContinuousLinearMap.comp_apply] using h'
  ext x
  simp [compression, ContinuousLinearMap.comp_apply, h_adj_apply]

lemma opNorm_lift_le [Nontrivial E] (ι : E →ₗᵢ[𝕜] H) (A : E →L[𝕜] E) :
    ‖ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)‖ ≤ ‖A‖ := by
  have hι : ‖ι.toContinuousLinearMap‖ = 1 :=
    (LinearIsometry.norm_toContinuousLinearMap (f := ι))
  have hιadj : ‖ι.toContinuousLinearMap.adjoint‖ = 1 := by
    have h' :
        ‖ι.toContinuousLinearMap.adjoint‖ = ‖ι.toContinuousLinearMap‖ :=
      (LinearIsometryEquiv.norm_map (ContinuousLinearMap.adjoint) (ι.toContinuousLinearMap))
    calc
      ‖ι.toContinuousLinearMap.adjoint‖ = ‖ι.toContinuousLinearMap‖ := h'
      _ = 1 := hι
  have h1 :
      ‖ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)‖ ≤
        ‖ι.toContinuousLinearMap‖ * ‖A.comp ι.toContinuousLinearMap.adjoint‖ := by
    simpa using
      (ContinuousLinearMap.opNorm_comp_le (h := ι.toContinuousLinearMap)
        (f := A.comp ι.toContinuousLinearMap.adjoint))
  have h2 :
      ‖A.comp ι.toContinuousLinearMap.adjoint‖ ≤ ‖A‖ * ‖ι.toContinuousLinearMap.adjoint‖ := by
    simpa using
      (ContinuousLinearMap.opNorm_comp_le (h := A) (f := ι.toContinuousLinearMap.adjoint))
  calc
    ‖ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)‖
        ≤ ‖ι.toContinuousLinearMap‖ * ‖A.comp ι.toContinuousLinearMap.adjoint‖ := h1
    _ ≤ ‖ι.toContinuousLinearMap‖ * (‖A‖ * ‖ι.toContinuousLinearMap.adjoint‖) := by
          exact mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = ‖A‖ := by
          simp [hι, hιadj, mul_assoc]

end Compression

section Dictionary

variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- Finite dictionary span for Option B. -/
noncomputable def dictSubmodule {n : ℕ} (d : Fin n → H) : Submodule 𝕜 H :=
  Submodule.span 𝕜 (Set.range d)

/-- Option B embedding: Euclidean space → H via an orthonormal basis of the dictionary span. -/
noncomputable def dictEmbedding {n : ℕ} (d : Fin n → H) :
    EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 (dictSubmodule (𝕜 := 𝕜) d))) →ₗᵢ[𝕜] H := by
  classical
  let V : Submodule 𝕜 H := dictSubmodule (𝕜 := 𝕜) d
  haveI : FiniteDimensional 𝕜 V :=
    FiniteDimensional.span_of_finite 𝕜 (Set.finite_range d)
  exact V.subtypeₗᵢ.comp (stdOrthonormalBasis 𝕜 V).repr.symm.toLinearIsometry

/-- Casted version of the dictionary embedding to a fixed dimension `m`. -/
noncomputable def dictEmbeddingCast {n m : ℕ} (d : Fin n → H)
    (hdim : Module.finrank 𝕜 (dictSubmodule (𝕜 := 𝕜) d) = m) :
    EuclideanSpace 𝕜 (Fin m) →ₗᵢ[𝕜] H := by
  classical
  have e : Fin m ≃ Fin (Module.finrank 𝕜 (dictSubmodule (𝕜 := 𝕜) d)) := by
    cases hdim
    exact Equiv.refl _
  let e' :
      EuclideanSpace 𝕜 (Fin m) ≃ₗᵢ[𝕜]
        EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 (dictSubmodule (𝕜 := 𝕜) d))) := by
    simpa [EuclideanSpace] using
      (LinearIsometryEquiv.piLpCongrLeft 2 𝕜 (E := 𝕜) e)
  let e'' :
      EuclideanSpace 𝕜 (Fin m) →ₗᵢ[𝕜]
        EuclideanSpace 𝕜 (Fin (Module.finrank 𝕜 (dictSubmodule (𝕜 := 𝕜) d))) :=
    e'.toLinearIsometry
  exact (dictEmbedding (𝕜 := 𝕜) d).comp e''

end Dictionary

end Q3.Proofs.C1Embedding

/-!
C1 embedding: finite-dimensional dictionary model (Option B).

We realize the compression subspace V as `EuclideanSpace ℂ (Fin (2*M+1))`,
choose the standard orthonormal basis `ψ`, and define kernel sections `k n` by
their coordinates `prime_vec`. With this concrete model, `h_eval` closes by `simp`.
-/-

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

