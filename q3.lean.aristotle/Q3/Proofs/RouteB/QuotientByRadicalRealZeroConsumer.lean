import Q3.Proofs.RouteB.QuotientByRadicalPosDefMatrix
import Q3.Proofs.RouteB.PosDefSelfAdjointRealSpectrumRealConsumer

namespace Q3.RouteB

open scoped ComplexConjugate

theorem zerosRealOn_of_quotientByRadical_charpoly_mul
    {V ι : Type*} [AddCommGroup V] [Module ℝ V]
    [Fintype ι] [DecidableEq ι]
    (B : LinearMap.BilinForm ℝ V)
    (hB : B.IsSymm)
    (hpos : ∀ x, 0 ≤ B x x)
    (A : Module.End ℝ V)
    (hself : LinearMap.IsSelfAdjoint B A)
    (b : Module.Basis ι ℝ (V ⧸ LinearMap.ker B))
    (F unit realFactor : ℂ → ℂ)
    (hunit : ∀ z, unit z ≠ 0)
    (hrealFactor : ZerosRealOn Set.univ realFactor)
    (hfactor : ∀ z,
      F z = unit z *
        ((((LinearMap.toMatrix b b
          (quotientByRadicalEnd B A hself)).map
            (algebraMap ℝ ℂ)).charpoly.eval z) * realFactor z)) :
    ZerosRealOn Set.univ F := by
  let Qq := BilinForm.toMatrix b (quotientByRadicalForm B hB)
  let Dq := LinearMap.toMatrix b b (quotientByRadicalEnd B A hself)
  obtain ⟨hQq, hSAq⟩ :=
    quotientByRadical_toMatrix_posDef_weightedSymmetric B hB hpos A hself b
  apply zerosRealOn_of_realPosDefWeightedSymmetric_charpoly_mul
    Qq Dq hQq hSAq F unit realFactor hunit hrealFactor
  intro z
  simpa [Dq] using hfactor z

#print axioms zerosRealOn_of_quotientByRadical_charpoly_mul

end Q3.RouteB
