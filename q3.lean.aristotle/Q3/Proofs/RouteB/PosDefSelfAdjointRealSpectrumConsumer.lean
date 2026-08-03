import Q3.Proofs.RouteB.PosDefSelfAdjointRealSpectrum
import Q3.Proofs.RouteB.HermitianDeterminantRealZeros

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Q3.RouteB

/-- The abstract M1 similarity theorem feeds the existing Hermitian
characteristic-polynomial consumer without changing the determinant
factorization or adding any concrete CvS supplier. -/
theorem zerosRealOn_of_posDefSelfAdjoint_charpoly_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℂ)
    (hQ : Q.PosDef)
    (hSA : Q * D = Dᴴ * Q)
    (F unit realFactor : ℂ → ℂ)
    (hunit : ∀ z, unit z ≠ 0)
    (hrealFactor : ZerosRealOn Set.univ realFactor)
    (hfactor : ∀ z,
      F z = unit z * (D.charpoly.eval z * realFactor z)) :
    ZerosRealOn Set.univ F := by
  obtain ⟨H, hH, hchar⟩ :=
    posDefSelfAdjoint_exists_hermitian Q D hQ hSA
  apply zerosRealOn_of_hermitian_charpoly_mul
    H hH F unit realFactor hunit hrealFactor
  intro z
  simpa [hchar] using hfactor z

#print axioms zerosRealOn_of_posDefSelfAdjoint_charpoly_mul

end Q3.RouteB
