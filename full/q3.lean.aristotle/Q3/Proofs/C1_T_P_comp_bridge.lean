/-
C1 Bridge for T_P_comp_real
===========================

This lemma packages the C1 compression bound for the concrete matrix
`T_P_comp_real`. It is purely conditional: once an embedding realizes the
matrix as a compression, the operator norm bound follows.
-/

import Q3.Basic.Defs
import Q3.Proofs.C1_Embedding_Bridge

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

namespace Q3.Proofs

open Q3.Proofs.C1Embedding

/-- If `T_P_comp_real` is realized as a compression, its opNorm is bounded by `‖T‖`. -/
lemma T_P_comp_real_opNorm_le_of_compression
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (ι : EuclideanSpace ℝ (Fin (2 * M + 1)) →ₗᵢ[ℝ] H) (T : H →L[ℝ] H)
    (hA : (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap =
      compression ι T) :
    ‖(Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap‖ ≤ ‖T‖ := by
  simpa using
    (C1_opNorm_toEuclideanLin_le_of_compression
      (ι := ι) (T := T) (A := Q3.T_P_comp_real K B t M) hA)

end Q3.Proofs
