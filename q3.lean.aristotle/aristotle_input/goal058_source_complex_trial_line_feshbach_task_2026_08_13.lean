import Q3.Proofs.RouteB.CCMProposition59ComplexHermitianConnector

set_option linter.mathlibStandardSet false

/-!
Aristotle input harness for
`GOAL058_ARISTOTLE_SOURCE_COMPLEX_TRIAL_LINE_FESHBACH`.

The intentional holes below are submission inputs only. The accepted output
must be a hole-free implementation of the single production file
`Q3/Proofs/RouteB/CCMProposition59ComplexTrialLineFeshbach.lean`, obeying the
source lock and falsifiers in the accompanying Proshka proof pack.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

noncomputable def complexTrialLineComplement
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (q : ι → ℂ) : Matrix ι ι ℂ :=
  1 - complexTrialLineProjection q

noncomputable def sourceCCMComplexTrialComplementBlock
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ :=
  let q := D0Pstar.sourceCCMComplexRow S i
  let K := D0Pstar.sourceCCMFiniteMatrix i
  let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
  let Q := complexTrialLineComplement q
  Q * (K - a •
    (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ)) * Q

theorem sourceCCMComplexTrialComplement_mulVec_Kq_eq_residual
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    let q := D0Pstar.sourceCCMComplexRow S i
    let K := D0Pstar.sourceCCMFiniteMatrix i
    let Q := complexTrialLineComplement q
    Q *ᵥ (K *ᵥ q) =
      D0Pstar.sourceCCMFiniteResidual S i := by
  sorry

theorem sourceCCMFiniteMatrix_sub_rayleigh_eq_complexTrialFeshbach
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex) :
    let q := D0Pstar.sourceCCMComplexRow S i
    let K := D0Pstar.sourceCCMFiniteMatrix i
    let a : ℂ := (D0Pstar.sourceCCMFiniteRayleigh S i : ℂ)
    let r := D0Pstar.sourceCCMFiniteResidual S i
    K - a •
        (1 : Matrix (CCMModeFinite i.N) (CCMModeFinite i.N) ℂ) =
      Matrix.vecMulVec q (star r) +
        Matrix.vecMulVec r (star q) +
          sourceCCMComplexTrialComplementBlock S i := by
  sorry

end Q3.RouteB
