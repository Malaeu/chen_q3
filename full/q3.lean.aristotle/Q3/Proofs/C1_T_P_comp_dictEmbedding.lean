/-
Dictionary Embedding Bridge for T_P_comp_real
============================================

Option B specialization: uses the dictionary embedding `dictEmbedding` and
reduces the `T_P_comp_real` norm bound to the C1 compression lemma.
-/

import Q3.Basic.Defs
import Q3.Proofs.C1_Embedding
import Q3.Proofs.C1_T_P_comp_bridge

set_option linter.mathlibStandardSet false
set_option linter.unusedVariables false

noncomputable section

namespace Q3.Proofs

open Q3.Proofs.C1Embedding

/-- If `T_P_comp_real` is realized as a compression via `dictEmbedding`, then its opNorm is bounded. -/
lemma T_P_comp_real_opNorm_le_of_dictEmbedding
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1)
    (T : H →L[ℝ] H)
    (hA :
      (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap =
        compression (dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim) T) :
    ‖(Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap‖ ≤ ‖T‖ := by
  simpa using
    (T_P_comp_real_opNorm_le_of_compression (K := K) (B := B) (t := t) (M := M)
      (ι := dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim)
      (T := T) hA)

end Q3.Proofs
