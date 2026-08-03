import Q3.Proofs.RouteB.QuotientByRadicalSelfAdjoint
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix

namespace Q3.RouteB

/-- Choosing coordinates on the quotient by the full radical turns the
descended positive form and descended self-adjoint endomorphism into exactly
the real positive-definite weighted-symmetric matrix interface used by M1. -/
theorem quotientByRadical_toMatrix_posDef_weightedSymmetric
    {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm)
    (hpos : ∀ x, 0 ≤ B x x)
    (A : Module.End ℝ V)
    (hself : LinearMap.IsSelfAdjoint B A)
    (b : Module.Basis ι ℝ (V ⧸ LinearMap.ker B)) :
    let Qq := BilinForm.toMatrix b
      (quotientByRadicalForm B hB)
    let Dq := LinearMap.toMatrix b b
      (quotientByRadicalEnd B A hself)
    Qq.PosDef ∧ Qq * Dq = Dq.transpose * Qq := by
  let Bq : LinearMap.BilinForm ℝ (V ⧸ LinearMap.ker B) :=
    quotientByRadicalForm B hB
  let Aq : Module.End ℝ (V ⧸ LinearMap.ker B) :=
    quotientByRadicalEnd B A hself
  let Qq : Matrix ι ι ℝ := BilinForm.toMatrix b Bq
  let Dq : Matrix ι ι ℝ := LinearMap.toMatrix b b Aq
  change Qq.PosDef ∧ Qq * Dq = Dq.transpose * Qq
  have hBqSymm : Bq.IsSymm := by
    refine ⟨fun q r => ?_⟩
    refine Submodule.Quotient.induction_on (LinearMap.ker B) q ?_
    intro x
    refine Submodule.Quotient.induction_on (LinearMap.ker B) r ?_
    intro y
    simpa [Bq] using hB.eq x y
  have hQqHerm : Qq.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext i j
    simpa [Qq, BilinForm.toMatrix_apply] using
      hBqSymm.eq (b j) (b i)
  have hQqPos : Qq.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos hQqHerm
    intro x hx
    have hcoord : star x ⬝ᵥ (Qq *ᵥ x) =
        Bq (b.equivFun.symm x) (b.equivFun.symm x) := by
      simpa [Qq] using
        BilinForm.dotProduct_toMatrix_mulVec b Bq x x
    rw [hcoord]
    have hqx : b.equivFun.symm x ≠ 0 := by
      intro hzero
      apply hx
      exact b.equivFun.symm.injective (by simpa using hzero)
    have hnonneg := quotientByRadicalForm_nonneg B hB hpos
      (b.equivFun.symm x)
    have hne : Bq (b.equivFun.symm x) (b.equivFun.symm x) ≠ 0 := by
      intro hzero
      apply hqx
      exact (quotientByRadicalForm_definite B hB hpos
        (b.equivFun.symm x)).mp (by simpa [Bq] using hzero)
    exact lt_of_le_of_ne (by simpa [Bq] using hnonneg) hne.symm
  have hAqSelf : LinearMap.IsSelfAdjoint Bq Aq := by
    simpa [Bq, Aq] using
      quotientByRadicalEnd_isSelfAdjoint B hB A hself
  have hforms : Bq.compLeft Aq = Bq.compRight Aq := by
    apply LinearMap.ext
    intro (q : V ⧸ LinearMap.ker B)
    apply LinearMap.ext
    intro (r : V ⧸ LinearMap.ker B)
    exact hAqSelf q r
  refine ⟨hQqPos, ?_⟩
  calc
    Qq * Dq = BilinForm.toMatrix b (Bq.compRight Aq) := by
      simpa [Qq, Dq] using
        (BilinForm.toMatrix_compRight b Bq Aq).symm
    _ = BilinForm.toMatrix b (Bq.compLeft Aq) := by
      rw [hforms]
    _ = Dq.transpose * Qq := by
      simpa [Qq, Dq] using
        BilinForm.toMatrix_compLeft b Bq Aq

#print axioms quotientByRadical_toMatrix_posDef_weightedSymmetric

end Q3.RouteB
