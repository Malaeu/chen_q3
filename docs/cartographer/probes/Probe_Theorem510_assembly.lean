-- ПРОГОН №2. Цель списана с потребителя CanonicalRHRouteSkeleton.lean:114.
-- Сборка из двух СВОИХ доказанных станков: M1 + β8d.
import Q3.Proofs.RouteB.CanonicalRHRouteSkeleton
import Q3.Proofs.RouteB.HermitianDeterminantRealZeros
import Q3.Proofs.RouteB.PosDefSelfAdjointRealSpectrum

set_option maxHeartbeats 1000000
open Q3.RouteB Q3.RouteB.CanonicalRHRoute Matrix
open scoped ComplexOrder MatrixOrder

/-- `Theorem510RealZeroBridge` сводится к ОДНОМУ входу: разложению `hfactor`. -/
theorem theorem510_of_weighted_selfadjoint_factorization
    {Index : Type*} (C : CanonicalApproximation Index) (H2aAt : Index → Prop)
    (n : Index → Type) [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]
    (Q D : ∀ i, Matrix (n i) (n i) ℂ)
    (hQ : ∀ i, (Q i).PosDef)
    (hSA : ∀ i, Q i * D i = (D i)ᴴ * Q i)
    (unit realFactor : Index → ℂ → ℂ)
    (hunit : ∀ i z, unit i z ≠ 0)
    (hreal : ∀ i, ZerosRealOn Set.univ (realFactor i))
    (hfactor : ∀ i z,
      C.Pstar.family i z = unit i z * ((D i).charpoly.eval z * realFactor i z)) :
    Theorem510RealZeroBridge C H2aAt := by
  intro i _ _
  obtain ⟨H, hH, hchar⟩ :=
    posDefSelfAdjoint_exists_hermitian (Q i) (D i) (hQ i) (hSA i)
  refine zerosRealOn_of_hermitian_charpoly_mul H hH
    (C.Pstar.family i) (unit i) (realFactor i) (hunit i) (hreal i) ?_
  intro z
  simpa [hchar] using hfactor i z

#print axioms theorem510_of_weighted_selfadjoint_factorization
