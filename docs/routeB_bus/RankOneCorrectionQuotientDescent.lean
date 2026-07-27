import Q3.Proofs.RouteB.RankOneCorrectionWeightedSymmetry
import Mathlib.LinearAlgebra.Quotient.Basic

set_option linter.mathlibStandardSet false

noncomputable section
namespace Q3.RouteB

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- A linear endomorphism that kills `x` induces an endomorphism of the
quotient by the span of `x`. -/
def quotientSpanSingletonEnd (f : V →ₗ[R] V) (x : V) (hx : f x = 0) :
    (V ⧸ R ∙ x) →ₗ[R] (V ⧸ R ∙ x) :=
  (R ∙ x).mapQ (R ∙ x) f (by
    intro y hy
    rcases (Submodule.mem_span_singleton.mp hy) with ⟨a, rfl⟩
    simp [hx])

@[simp] theorem quotientSpanSingletonEnd_mk
    (f : V →ₗ[R] V) (x : V) (hx : f x = 0) (y : V) :
    quotientSpanSingletonEnd f x hx (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (f y) := by
  simp [quotientSpanSingletonEnd]

/-- The normalized source rank-one correction descends to the quotient by the
calibration line.  Identification of this line with the exact radical and the
modified Hilbert metric remains a separate Route B obligation. -/
noncomputable def rankOneCorrectionQuotientEnd
    {n : Type*} [Fintype n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ)
    (hnormalized : eta ⬝ᵥ xi = 1) :
    ((n → ℝ) ⧸ ℝ ∙ xi) →ₗ[ℝ] ((n → ℝ) ⧸ ℝ ∙ xi) :=
  quotientSpanSingletonEnd (rankOneCorrection D xi eta).mulVecLin xi
    (rankOneCorrection_kills_vector D xi eta hnormalized)

@[simp] theorem rankOneCorrectionQuotientEnd_mk
    {n : Type*} [Fintype n]
    (D : Matrix n n ℝ) (xi eta : n → ℝ)
    (hnormalized : eta ⬝ᵥ xi = 1) (y : n → ℝ) :
    rankOneCorrectionQuotientEnd D xi eta hnormalized
        (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        (Matrix.mulVec (rankOneCorrection D xi eta) y) := by
  simp [rankOneCorrectionQuotientEnd]

#print axioms quotientSpanSingletonEnd_mk
#print axioms rankOneCorrectionQuotientEnd_mk

end Q3.RouteB
