/-
C1 Embedding Bridge
==================

Lightweight re-export of the C1 compression bound into `Q3.Proofs`.
-/

import Q3.Proofs.C1_Embedding

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

namespace Q3.Proofs

open Q3.Proofs.C1Embedding

/-- C1: compression by a linear isometry does not increase the operator norm. -/
lemma C1_compression_opNorm_le {𝕜 : Type*} [RCLike 𝕜]
    {E H : Type*} [NormedAddCommGroup E] [NormedAddCommGroup H]
    [InnerProductSpace 𝕜 E] [InnerProductSpace 𝕜 H]
    [CompleteSpace E] [CompleteSpace H] [Nontrivial E]
    (ι : E →ₗᵢ[𝕜] H) (T : H →L[𝕜] H) :
    ‖compression ι T‖ ≤ ‖T‖ := by
  simpa using (compression_opNorm_le (ι := ι) (T := T))

/-- Matrix form: if a matrix induces a compression map, its opNorm is bounded by the RKHS norm. -/
lemma C1_opNorm_toEuclideanLin_le_of_compression {𝕜 : Type*} [RCLike 𝕜]
    {n : Type*} [Fintype n] [DecidableEq n]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
    [Nontrivial (EuclideanSpace 𝕜 n)]
    (ι : EuclideanSpace 𝕜 n →ₗᵢ[𝕜] H) (T : H →L[𝕜] H) (A : Matrix n n 𝕜)
    (hA : (Matrix.toEuclideanLin A).toContinuousLinearMap = compression ι T) :
    ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖ ≤ ‖T‖ := by
  simpa [hA] using (C1_compression_opNorm_le (ι := ι) (T := T))

end Q3.Proofs
