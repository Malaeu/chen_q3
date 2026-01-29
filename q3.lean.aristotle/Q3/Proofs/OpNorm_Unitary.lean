/-
Operator norm invariance under conjugation by isometries.

This is the core “unitary change-of-basis is harmless” fact used in the
Option 1b decision tree (replace exact ON-feature matching by an interpolated
basis + track a unitary conjugation on the finite-dimensional side).
-/

import Mathlib.Analysis.Normed.Operator.NormedSpace

set_option linter.mathlibStandardSet false

open scoped BigOperators

namespace Q3.Proofs

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]

open ContinuousLinearMap

/-! Postcomposition invariance for operator norm. -/

theorem opNorm_linearIsometryEquiv_comp
    (e : F ≃ₗᵢ[𝕜] G) (f : E →L[𝕜] F) :
    ‖(e.toLinearIsometry.toContinuousLinearMap).comp f‖ = ‖f‖ := by
  classical
  cases subsingleton_or_nontrivial F with
  | inl hF =>
      haveI : Subsingleton F := hF
      -- every map into a subsingleton space is zero, hence has norm 0
      have hf : f = 0 := by
        ext x
        exact Subsingleton.elim (f x) 0
      subst hf
      simp
  | inr hF =>
      haveI : Nontrivial F := hF
      haveI : Nontrivial G := Function.Injective.nontrivial e.injective
      refine le_antisymm ?_ ?_
      · -- ≤
        have h := (e.toLinearIsometry.toContinuousLinearMap).opNorm_comp_le f
        simpa [e.toLinearIsometry.norm_toContinuousLinearMap, one_mul] using h
      · -- ≥ : cancel using the inverse isometry.
        have h :=
          (e.symm.toLinearIsometry.toContinuousLinearMap).opNorm_comp_le
            ((e.toLinearIsometry.toContinuousLinearMap).comp f)
        have hcancel :
            (e.symm.toLinearIsometry.toContinuousLinearMap).comp
                ((e.toLinearIsometry.toContinuousLinearMap).comp f) = f := by
          ext x
          simp
        have hnorm1 : ‖e.symm.toLinearIsometry.toContinuousLinearMap‖ = 1 := by
          simpa using e.symm.toLinearIsometry.norm_toContinuousLinearMap
        have h' : ‖f‖ ≤ ‖(e.toLinearIsometry.toContinuousLinearMap).comp f‖ := by
          -- rewrite `h` using `hcancel` and `hnorm1`
          simpa [hcancel, hnorm1, one_mul] using h
        exact h'

/-! Conjugation invariance (domain+codomain). -/

theorem opNorm_conj_linearIsometryEquiv
    (e : E ≃ₗᵢ[𝕜] E) (T : E →L[𝕜] E) :
    ‖(e.symm.toLinearIsometry.toContinuousLinearMap).comp
        (T.comp e.toLinearIsometry.toContinuousLinearMap)‖ = ‖T‖ := by
  -- precomposition invariance is in Mathlib; postcomposition via lemma above
  have hpre :
      ‖T.comp e.toLinearIsometry.toContinuousLinearMap‖ = ‖T‖ :=
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv T e
  have hpost :
      ‖(e.symm.toLinearIsometry.toContinuousLinearMap).comp
          (T.comp e.toLinearIsometry.toContinuousLinearMap)‖ =
        ‖T.comp e.toLinearIsometry.toContinuousLinearMap‖ :=
    opNorm_linearIsometryEquiv_comp e.symm (T.comp e.toLinearIsometry.toContinuousLinearMap)
  simpa [hpre] using hpost

end

end Q3.Proofs
