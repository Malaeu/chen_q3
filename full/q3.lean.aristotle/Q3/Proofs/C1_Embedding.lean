/-
C1 Embedding (Option B)
=======================

Option B builds a finite-dimensional dictionary subspace and embeds a Euclidean
space into the RKHS by choosing an orthonormal basis of that span. The resulting
compression map is used for the Rayleigh ↔ RKHS operator comparison.
-/

import Mathlib

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

open scoped BigOperators

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

end Dictionary

end Q3.Proofs.C1Embedding
