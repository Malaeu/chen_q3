import Q3.Proofs.RouteB.CCMProposition59SourceTrialFeshbachPreflight

set_option linter.mathlibStandardSet false

/-!
Aristotle input harness for
`GOAL058_ARISTOTLE_COMPLEX_HERMITIAN_P59_CONNECTOR`.

The intentional holes below are submission inputs only.  The accepted output
must be a hole-free implementation of the single production file
`Q3/Proofs/RouteB/CCMProposition59ComplexHermitianConnector.lean`, obeying the
source lock and falsifiers in the accompanying Proshka proof pack.
-/

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators

noncomputable def complexTrialLineProjection
    {ι : Type*} (q : ι → ℂ) : Matrix ι ι ℂ :=
  Matrix.vecMulVec q (star q)

noncomputable def sourceCCMGroundProjectionScalar
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℂ :=
  star (D0Pstar.sourceCCMComplexRow S i) ⬝ᵥ
    (fun j => (xi j : ℂ))

noncomputable def sourceCCMGroundProjectionErrorSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) : ℝ :=
  xi ⬝ᵥ xi -
    Complex.normSq (sourceCCMGroundProjectionScalar S i xi)

noncomputable def proposition59CCMKernelL2
    (L : ℝ) (N : ℕ) (z : ℂ) : ℝ :=
  ‖((Real.sqrt L : ℂ)⁻¹)‖ *
    Real.sqrt
      (∑ j : CCMModeFinite N,
        Complex.normSq
          (proposition59PoleKernel L (-ccmModeFinite N j) z))

theorem complexTrialLineProjection_isHermitian
    {ι : Type*} (q : ι → ℂ) :
    (complexTrialLineProjection q).IsHermitian := by
  sorry

theorem complexTrialLineProjection_sq_of_unit
    {ι : Type*} [Fintype ι]
    (q : ι → ℂ)
    (hq : star q ⬝ᵥ q = 1) :
    complexTrialLineProjection q * complexTrialLineProjection q =
      complexTrialLineProjection q := by
  sorry

theorem sourceCCMGroundProjectionErrorSq_eq_sum_normSq
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (xi : CCMModeFinite i.N → ℝ) :
    sourceCCMGroundProjectionErrorSq S i xi =
      ∑ j,
        Complex.normSq
          ((xi j : ℂ) -
            sourceCCMGroundProjectionScalar S i xi *
              D0Pstar.sourceCCMComplexRow S i j) := by
  sorry

theorem proposition59CCMTransform_sub_sourceProjection_le
    (S : D0Pstar.ProlateCanonicalSourceData)
    (i : D0Pstar.PairIndex)
    (L : ℝ) (hL : 0 < L)
    (xi : CCMModeFinite i.N → ℝ) :
    0 ≤ sourceCCMGroundProjectionErrorSq S i xi ∧
    ∀ z : ℂ,
      ‖proposition59CCMTransform L i.N xi z -
          sourceCCMGroundProjectionScalar S i xi *
            proposition59CCMComplexTransform L i.N
              (D0Pstar.sourceCCMComplexRow S i) z‖
        ≤ proposition59CCMKernelL2 L i.N z *
            Real.sqrt (sourceCCMGroundProjectionErrorSq S i xi) := by
  sorry

end Q3.RouteB
