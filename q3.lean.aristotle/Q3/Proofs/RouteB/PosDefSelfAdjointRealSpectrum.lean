import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Q3.RouteB

/-- A complex matrix that is self-adjoint for a positive-definite Hermitian
form is similar to a Hermitian matrix.  The weighted self-adjointness
orientation is the project convention `Q * D = Dᴴ * Q`.

This is only the abstract M1 core.  It does not construct the CvS quotient
metric or supply the concrete Theorem-5.10 determinant factorization. -/
theorem posDefSelfAdjoint_exists_hermitian
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℂ) (hQ : Q.PosDef)
    (hSA : Q * D = Dᴴ * Q) :
    ∃ H : Matrix n n ℂ, H.IsHermitian ∧ H.charpoly = D.charpoly := by
  let S : Matrix n n ℂ := CFC.sqrt Q
  have hSpos : S.PosDef := by
    simpa [S] using hQ.isStrictlyPositive.sqrt.posDef
  have hSsq : S * S = Q := by
    simpa [S] using CFC.sqrt_mul_sqrt_self Q
  have hSunit : IsUnit S := hSpos.isUnit
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSunit
  let Su : (Matrix n n ℂ)ˣ := hSunit.unit
  have hSu : (Su : Matrix n n ℂ) = S := hSunit.unit_spec
  let H : Matrix n n ℂ := S * D * S⁻¹
  refine ⟨H, ?_, ?_⟩
  · have hweighted : S * S * D = Dᴴ * (S * S) := by
      simpa [hSsq] using hSA
    have hconj : S⁻¹ * Dᴴ * S = S * D * S⁻¹ := by
      have hleft : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSdet
      have h1 : S * D = (S⁻¹ * Dᴴ * S) * S := by
        have h := congrArg (fun A : Matrix n n ℂ => S⁻¹ * A) hweighted
        simpa only [← Matrix.mul_assoc, hleft, one_mul] using h
      have h2 := congrArg (fun A : Matrix n n ℂ => A * S⁻¹) h1
      dsimp at h2
      have hcancel : (S⁻¹ * Dᴴ * S) * S * S⁻¹ = S⁻¹ * Dᴴ * S :=
        Matrix.mul_nonsing_inv_cancel_right S (S⁻¹ * Dᴴ * S) hSdet
      rw [hcancel] at h2
      exact h2.symm
    rw [Matrix.IsHermitian]
    change (S * D * S⁻¹)ᴴ = S * D * S⁻¹
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_nonsing_inv]
    simpa [Matrix.mul_assoc, hSpos.isHermitian.eq] using hconj
  · simpa [H, ← hSu] using Matrix.charpoly_units_conj Su D

#print axioms posDefSelfAdjoint_exists_hermitian

end Q3.RouteB
