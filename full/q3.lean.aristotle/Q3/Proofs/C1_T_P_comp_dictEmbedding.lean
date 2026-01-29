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

/-- Option B helper: `T_P_comp_real` is (tautologically) the compression of its lift along
`dictEmbeddingCast`. This removes the need to provide a separate `hA` hypothesis when the
ambient operator is chosen as the lifted one. -/
lemma T_P_comp_real_eq_compression_lift_of_dictEmbedding
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1) :
    let ι :=
      dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
    let A :
        (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
        (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap
    let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
    (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap = compression ι T := by
  classical
  intro ι A T
  simpa [T, A] using (compression_lift_eq (ι := ι) (A := A)).symm

/-- Consequence of `T_P_comp_real_eq_compression_lift_of_dictEmbedding`: for the lifted operator,
the C1 bound gives `‖T_P_comp_real‖ ≤ ‖T‖`. -/
lemma T_P_comp_real_opNorm_le_lift_of_dictEmbedding
    (K B t : ℝ) (M : ℕ) [Fintype (Q3.Nodes K)]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {n : ℕ} (d : Fin n → H)
    (hdim : Module.finrank ℝ (dictSubmodule (𝕜 := ℝ) d) = 2 * M + 1) :
    let ι :=
      dictEmbeddingCast (𝕜 := ℝ) (d := d) (m := 2 * M + 1) hdim
    let A :
        (EuclideanSpace ℝ (Fin (2 * M + 1))) →L[ℝ]
          (EuclideanSpace ℝ (Fin (2 * M + 1))) :=
        (Matrix.toEuclideanLin (Q3.T_P_comp_real K B t M)).toContinuousLinearMap
    let T : H →L[ℝ] H := ι.toContinuousLinearMap.comp (A.comp ι.toContinuousLinearMap.adjoint)
    ‖A‖ ≤ ‖T‖ := by
  classical
  intro ι A T
  have hA :
      A = compression ι T :=
    (T_P_comp_real_eq_compression_lift_of_dictEmbedding (K := K) (B := B) (t := t) (M := M)
        (d := d) (hdim := hdim))
  simpa [hA] using (compression_opNorm_le (ι := ι) (T := T))

end Q3.Proofs
