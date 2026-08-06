import Q3.Proofs.RouteB.D0PstarMuntzCenteredCoordinateLock

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Named object-first Galerkin residual crosswalk

This module materializes only the conditional Phase-4B interface selected by
the delegated Goal-056 strategic review.  The residual below is the literal
normalized projection-minus-full object on the exact `parent ∘ extract`
index.  Its Mellin coordinate is not defined from the already-known scalar
defect.

The crosswalk remains an explicit `Prop` hypothesis.  Nothing here proves the
weighted Fourier reconstruction, measure transport, residual decay, or
`SlotS2`.
-/

/-- The exact normalized object residual at the selected production index.

The order `projection - full object`, the `sTrial_m_N` normalization, source
trial, `MemLp` witness, and `parent ∘ extract` carrier are all load-bearing.
-/
noncomputable def selectedNormalizedGalerkinResidual
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    H_m (selectedPairIndex S k) :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  (selectedTrialNormalizer S k : ℂ) •
    ((gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp)

/-- The multiplicative Mellin coordinate of the literal selected residual.

The restricted measure is exactly `du/u` and the kernel orientation is
exactly `u^(-i*z)`.  This definition does not infer the object residual from
`rawFplus - scaledGwin`.
-/
noncomputable def selectedGalerkinResidualMellinCoordinate
    (S : ProlateCanonicalSourceData) (k : ℕ) (z : ℂ) : ℂ :=
  let i := selectedPairIndex S k
  ∫ u : ℝ,
      (selectedNormalizedGalerkinResidual S k) u *
        (u : ℂ) ^ (-Complex.I * z)
    ∂(dStar.restrict (I_m i))

/-- The exact missing Phase-4B crosswalk, exposed only as a local hypothesis.

This is a definition of a proposition, not an axiom and not a theorem that the
proposition holds.
-/
def D0PstarMuntzGalerkinResidualCrosswalkContract
    (S : ProlateCanonicalSourceData) : Prop :=
  ∀ k : ℕ, ∀ z : ℂ,
    selectedGalerkinCoordinateDefect S k z =
      selectedGalerkinResidualMellinCoordinate S k z

/-- The sole direct consumer of the named conditional crosswalk.

It replaces the Phase-4A scalar defect by the coordinate of the literal
object residual.  No estimate or limit argument is used.
-/
theorem selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate
    (S : ProlateCanonicalSourceData)
    (hXW : D0PstarMuntzGalerkinResidualCrosswalkContract S)
    (k : ℕ) (z : ℂ) :
    selectedFamily (canonicalApproximation S.canonical) k z =
      selectedMuntzApproximation S k z +
        selectedCenteringFactor S k *
          selectedGalerkinResidualMellinCoordinate S k (-z) := by
  rw [selectedFamily_eq_muntzApproximation_add_defect]
  rw [hXW k (-z)]

#print axioms selectedNormalizedGalerkinResidual
#print axioms selectedGalerkinResidualMellinCoordinate
#print axioms D0PstarMuntzGalerkinResidualCrosswalkContract
#print axioms selectedFamily_eq_muntzApproximation_add_objectResidualCoordinate

end Q3.RouteB.D0Pstar
