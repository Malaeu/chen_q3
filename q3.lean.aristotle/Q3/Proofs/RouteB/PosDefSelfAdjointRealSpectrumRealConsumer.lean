import Q3.Proofs.RouteB.PosDefSelfAdjointRealSpectrumConsumer

set_option linter.mathlibStandardSet false

noncomputable section

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Q3.RouteB

/-- Positive definiteness survives the canonical scalar extension
`ℝ → ℂ`. -/
theorem realPosDef_map_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q : Matrix n n ℝ) (hQ : Q.PosDef) :
    (Q.map (algebraMap ℝ ℂ)).PosDef := by
  let S : Matrix n n ℝ := CFC.sqrt Q
  let B : Matrix n n ℂ := S.map (algebraMap ℝ ℂ)
  have hSpos : S.PosDef := by
    simpa [S] using hQ.isStrictlyPositive.sqrt.posDef
  have hSsq : S * S = Q := by
    simpa [S] using CFC.sqrt_mul_sqrt_self Q
  have hBherm : B.IsHermitian := by
    apply hSpos.isHermitian.map
    intro x
    simp
  have hBunit : IsUnit B := by
    exact hSpos.isUnit.map (RingHom.mapMatrix (algebraMap ℝ ℂ))
  have hBinj : Function.Injective B.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr hBunit
  have hmap : B * B = Q.map (algebraMap ℝ ℂ) := by
    change S.map (algebraMap ℝ ℂ) * S.map (algebraMap ℝ ℂ) =
      Q.map (algebraMap ℝ ℂ)
    rw [← Matrix.map_mul, hSsq]
  have hgram : Q.map (algebraMap ℝ ℂ) = Bᴴ * B := by
    rw [hBherm.eq]
    exact hmap.symm
  rw [hgram]
  exact Matrix.PosDef.conjTranspose_mul_self B hBinj

/-- Real weighted symmetry becomes complex weighted self-adjointness after
entrywise scalar extension. -/
theorem realWeightedSymmetric_map_complex
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℝ)
    (hSA : Q * D = D.transpose * Q) :
    Q.map (algebraMap ℝ ℂ) * D.map (algebraMap ℝ ℂ) =
      (D.map (algebraMap ℝ ℂ))ᴴ * Q.map (algebraMap ℝ ℂ) := by
  have hD : D.transpose.map (algebraMap ℝ ℂ) =
      (D.map (algebraMap ℝ ℂ))ᴴ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial D]
    apply Matrix.conjTranspose_map
    intro x
    simp
  calc
    Q.map (algebraMap ℝ ℂ) * D.map (algebraMap ℝ ℂ) =
        (Q * D).map (algebraMap ℝ ℂ) := by rw [Matrix.map_mul]
    _ = (D.transpose * Q).map (algebraMap ℝ ℂ) := congrArg
      (fun M : Matrix n n ℝ => M.map (algebraMap ℝ ℂ)) hSA
    _ = D.transpose.map (algebraMap ℝ ℂ) *
        Q.map (algebraMap ℝ ℂ) := by rw [Matrix.map_mul]
    _ = (D.map (algebraMap ℝ ℂ))ᴴ *
        Q.map (algebraMap ℝ ℂ) := by rw [hD]

/-- The real finite-dimensional weighted-symmetric scaffold feeds the
complex M1 real-zero consumer after an explicit scalar extension. -/
theorem zerosRealOn_of_realPosDefWeightedSymmetric_charpoly_mul
    {n : Type*} [Fintype n] [DecidableEq n]
    (Q D : Matrix n n ℝ)
    (hQ : Q.PosDef)
    (hSA : Q * D = D.transpose * Q)
    (F unit realFactor : ℂ → ℂ)
    (hunit : ∀ z, unit z ≠ 0)
    (hrealFactor : ZerosRealOn Set.univ realFactor)
    (hfactor : ∀ z,
      F z = unit z *
        (((D.map (algebraMap ℝ ℂ)).charpoly.eval z) * realFactor z)) :
    ZerosRealOn Set.univ F := by
  apply zerosRealOn_of_posDefSelfAdjoint_charpoly_mul
    (Q.map (algebraMap ℝ ℂ)) (D.map (algebraMap ℝ ℂ))
    (realPosDef_map_complex Q hQ)
    (realWeightedSymmetric_map_complex Q D hSA)
    F unit realFactor hunit hrealFactor hfactor

#print axioms realPosDef_map_complex
#print axioms realWeightedSymmetric_map_complex
#print axioms zerosRealOn_of_realPosDefWeightedSymmetric_charpoly_mul

end Q3.RouteB
