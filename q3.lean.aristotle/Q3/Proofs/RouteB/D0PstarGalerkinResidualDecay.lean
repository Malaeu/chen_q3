import Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualCrosswalk
import Mathlib.Analysis.Normed.Ring.Lemmas

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Conditional selected Galerkin residual decay receiver

This module isolates the exact scalar factorization behind the selected
normalized Galerkin residual.  It proves only the universal
bounded-times-zero receiver.  The varying-carrier projection-tail estimate
and bounded inverse-normalizer estimate remain explicit analytic suppliers.
-/

/-- Norm of the literal unnormalized projection-minus-full residual on the
existing selected `parent ∘ extract` path. -/
noncomputable def selectedUnnormalizedGalerkinResidualNorm
    (S : ProlateCanonicalSourceData) (k : ℕ) : ℝ :=
  let i := selectedPairIndex S k
  let h := selectedProlateTrial S k
  let hLp := S.source.eStar_memLp i
  ‖(gTrial_m_N i h hLp : H_m i) - gTrial_m i h hLp‖

/-- First analytic supplier contract: the selected unnormalized projection
tail vanishes. This proposition is not claimed unconditionally here. -/
def SelectedProjectionTailDecay
    (S : ProlateCanonicalSourceData) : Prop :=
  Tendsto
    (selectedUnnormalizedGalerkinResidualNorm S)
    atTop
    (𝓝 0)

/-- Second analytic supplier contract: the selected inverse projection
normalizers remain bounded. Pointwise `TrialNonzero` alone does not prove it. -/
def SelectedTrialNormalizerBounded
    (S : ProlateCanonicalSourceData) : Prop :=
  IsBoundedUnder (· ≤ ·) atTop
    (fun k : ℕ => ‖(selectedTrialNormalizer S k : ℂ)‖)

/-- Exact norm factorization of the literal normalized selected residual. -/
theorem norm_selectedNormalizedGalerkinResidual_eq
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    ‖selectedNormalizedGalerkinResidual S k‖ =
      ‖(selectedTrialNormalizer S k : ℂ)‖ *
        selectedUnnormalizedGalerkinResidualNorm S k := by
  simp [selectedNormalizedGalerkinResidual,
    selectedUnnormalizedGalerkinResidualNorm, norm_smul]

/-- Conditional selected residual decay from two independent analytic
suppliers. This theorem does not establish either supplier. -/
theorem selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded
    (S : ProlateCanonicalSourceData)
    (hTail : SelectedProjectionTailDecay S)
    (hNormalizer : SelectedTrialNormalizerBounded S) :
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop
      (𝓝 0) := by
  rw [show (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖) =
      fun k : ℕ => ‖(selectedTrialNormalizer S k : ℂ)‖ *
        selectedUnnormalizedGalerkinResidualNorm S k by
    funext k
    exact norm_selectedNormalizedGalerkinResidual_eq S k]
  apply Filter.isBoundedUnder_le_mul_tendsto_zero
  · simpa [SelectedTrialNormalizerBounded, Function.comp_def] using hNormalizer
  · exact hTail

#print axioms norm_selectedNormalizedGalerkinResidual_eq
#print axioms selectedNormalizedGalerkinResidual_norm_tendsto_zero_of_tail_and_bounded

end Q3.RouteB.D0Pstar
