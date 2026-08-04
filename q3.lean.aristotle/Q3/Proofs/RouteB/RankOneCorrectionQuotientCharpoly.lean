import Q3.Proofs.RouteB.RankOneCorrectionLagrangePolynomial
import Q3.Proofs.RouteB.RankOneCorrectionQuotientDescent
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Projection

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

open Matrix Polynomial
open scoped BigOperators

theorem charpoly_eq_X_mul_quotientSpanSingletonEnd_charpoly
    {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (f : Module.End ℝ V) (xi : V) (hxi0 : xi ≠ 0) (hkill : f xi = 0) :
    f.charpoly =
      Polynomial.X * (quotientSpanSingletonEnd f xi hkill).charpoly := by
  classical
  let p : Submodule ℝ V := ℝ ∙ xi
  obtain ⟨q, hpq⟩ := p.exists_isCompl
  let e : (p × q) ≃ₗ[ℝ] V := p.prodEquivOfIsCompl q hpq
  let eqQ : (V ⧸ p) ≃ₗ[ℝ] q := p.quotientEquivOfIsCompl q hpq
  let qend : Module.End ℝ (V ⧸ p) := quotientSpanSingletonEnd f xi hkill
  let g : Module.End ℝ q := eqQ.conj qend
  have hpfin : Module.finrank ℝ p = 1 := by
    simpa [p] using finrank_span_singleton hxi0
  let v : p := ⟨xi, Submodule.mem_span_singleton_self xi⟩
  have hv : v ≠ 0 := by
    intro hv0
    apply hxi0
    exact Subtype.ext_iff.mp hv0
  let bp : Module.Basis Unit ℝ p :=
    FiniteDimensional.basisSingleton Unit hpfin v hv
  let bq := Module.Free.chooseBasis ℝ q
  let b := bp.prod bq
  let psi : Module.End ℝ (p × q) := e.symm.conj f
  let A := LinearMap.toMatrix b b psi
  have hp_kill (x : p) : f x = 0 := by
    rcases Submodule.mem_span_singleton.mp x.2 with ⟨a, ha⟩
    rw [← ha]
    simp [hkill]
  have hpsi_left (x : p) : psi (x, 0) = 0 := by
    change e.symm (f (e (x, 0))) = 0
    rw [show e (x, 0) = (x : V) by simp [e], hp_kill x]
    simp
  have hA11 : A.toBlocks₁₁ = 0 := by
    ext i j
    change A (Sum.inl i) (Sum.inl j) = 0
    change (LinearMap.toMatrix b b psi) (Sum.inl i) (Sum.inl j) = 0
    rw [LinearMap.toMatrix_apply]
    have hb : b (Sum.inl j) = (bp j, 0) := by simp [b]
    rw [hb, hpsi_left]
    simp
  have hA21 : A.toBlocks₂₁ = 0 := by
    ext i j
    change A (Sum.inr i) (Sum.inl j) = 0
    change (LinearMap.toMatrix b b psi) (Sum.inr i) (Sum.inl j) = 0
    rw [LinearMap.toMatrix_apply]
    have hb : b (Sum.inl j) = (bp j, 0) := by simp [b]
    rw [hb, hpsi_left]
    simp
  have hquot (z : V) :
      eqQ (Submodule.Quotient.mk z) = (e.symm z).2 := by
    apply eqQ.symm.injective
    simp only [eqQ, Submodule.quotientEquivOfIsCompl_symm_apply,
      LinearEquiv.symm_apply_apply]
    apply (Submodule.Quotient.eq p).2
    have hsub : z - ((e.symm z).2 : V) = ((e.symm z).1 : V) := by
      calc
        z - ((e.symm z).2 : V) =
            e (e.symm z) - ((e.symm z).2 : V) := by
              rw [e.apply_symm_apply]
        _ = ((e.symm z).1 : V) + (e.symm z).2 - (e.symm z).2 := rfl
        _ = ((e.symm z).1 : V) := add_sub_cancel_right _ _
    rw [hsub]
    exact (e.symm z).1.2
  have hpsi_snd (y : q) : (psi (0, y)).2 = g y := by
    calc
      (psi (0, y)).2 = (e.symm (f y)).2 := by
        change (e.symm (f (e (0, y)))).2 = (e.symm (f y)).2
        rw [show e (0, y) = (y : V) by simp [e]]
      _ = eqQ (Submodule.Quotient.mk (f y)) := (hquot (f y)).symm
      _ = eqQ (qend (Submodule.Quotient.mk y)) := by
        rw [quotientSpanSingletonEnd_mk]
      _ = eqQ (qend (eqQ.symm y)) := by simp [eqQ]
      _ = g y := by rfl
  have hA22 : A.toBlocks₂₂ = LinearMap.toMatrix bq bq g := by
    ext i j
    change A (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bq bq g i j
    change (LinearMap.toMatrix b b psi) (Sum.inr i) (Sum.inr j) =
      LinearMap.toMatrix bq bq g i j
    rw [LinearMap.toMatrix_apply, LinearMap.toMatrix_apply]
    have hb : b (Sum.inr j) = (0, bq j) := by simp [b]
    rw [hb]
    change (bp.prod bq).repr (psi (0, bq j)) (Sum.inr i) =
      bq.repr (g (bq j)) i
    rw [Module.Basis.prod_repr_inr, hpsi_snd]
  calc
    f.charpoly = psi.charpoly := by
      symm
      exact e.symm.charpoly_conj f
    _ = A.charpoly := by
      symm
      exact LinearMap.charpoly_toMatrix psi b
    _ = (Matrix.fromBlocks A.toBlocks₁₁ A.toBlocks₁₂ 0
          A.toBlocks₂₂).charpoly := by
      congr 1
      rw [← hA21, Matrix.fromBlocks_toBlocks]
    _ = A.toBlocks₁₁.charpoly * A.toBlocks₂₂.charpoly := by
      rw [Matrix.charpoly_fromBlocks_zero₂₁]
    _ = Polynomial.X * g.charpoly := by
      rw [hA11, hA22, Matrix.charpoly_zero,
        LinearMap.charpoly_toMatrix]
      simp
    _ = Polynomial.X * qend.charpoly := by
      rw [show g.charpoly = qend.charpoly by
        exact eqQ.charpoly_conj qend]
    _ = Polynomial.X *
        (quotientSpanSingletonEnd f xi hkill).charpoly := by rfl

theorem rankOneCorrection_charpoly_eq_X_mul_quotient_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ)
    (hnormalized : eta ⬝ᵥ xi = 1) :
    (rankOneCorrection D xi eta).charpoly =
      Polynomial.X *
        (rankOneCorrectionQuotientEnd D xi eta hnormalized).charpoly := by
  have hxi0 : xi ≠ 0 := by
    intro hxi
    subst xi
    simp at hnormalized
  rw [← Matrix.charpoly_mulVecLin]
  exact charpoly_eq_X_mul_quotientSpanSingletonEnd_charpoly
    (rankOneCorrection D xi eta).mulVecLin xi hxi0
    (rankOneCorrection_kills_vector D xi eta hnormalized)

theorem sourceLagrangePolynomial_eq_signed_quotient_charpoly
    {n : Type*} [Fintype n] [DecidableEq n]
    (lam xi : n → ℝ)
    (hnormalized : (1 : n → ℝ) ⬝ᵥ xi = 1) :
    sourceLagrangePolynomial lam xi =
      -(Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
        (rankOneCorrectionQuotientEnd (Matrix.diagonal lam) xi
          (1 : n → ℝ) hnormalized).charpoly) := by
  have hamb := sourceLagrangePolynomial_charpoly_factor lam xi hnormalized
  rw [rankOneCorrection_charpoly_eq_X_mul_quotient_charpoly
    (Matrix.diagonal lam) xi (1 : n → ℝ) hnormalized] at hamb
  have hcancel :
      Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
          (rankOneCorrectionQuotientEnd (Matrix.diagonal lam) xi
            (1 : n → ℝ) hnormalized).charpoly =
        -sourceLagrangePolynomial lam xi := by
    apply (mul_left_cancel₀ Polynomial.X_ne_zero)
    calc
      Polynomial.X *
          (Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
            (rankOneCorrectionQuotientEnd (Matrix.diagonal lam) xi
              (1 : n → ℝ) hnormalized).charpoly) =
        Polynomial.C ((-1 : ℝ) ^ Fintype.card n) *
          (Polynomial.X *
            (rankOneCorrectionQuotientEnd (Matrix.diagonal lam) xi
              (1 : n → ℝ) hnormalized).charpoly) := by ring
      _ = -Polynomial.X * sourceLagrangePolynomial lam xi := hamb
      _ = Polynomial.X * (-sourceLagrangePolynomial lam xi) := by ring
  simpa using (congrArg Neg.neg hcancel).symm

#print axioms charpoly_eq_X_mul_quotientSpanSingletonEnd_charpoly
#print axioms rankOneCorrection_charpoly_eq_X_mul_quotient_charpoly
#print axioms sourceLagrangePolynomial_eq_signed_quotient_charpoly

end Q3.RouteB
