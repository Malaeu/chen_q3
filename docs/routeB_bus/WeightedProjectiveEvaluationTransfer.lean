import Q3.Proofs.RouteB.PhaseAlignmentRateTransfer
import Q3.Proofs.RouteB.CompactEvaluationRateTransfer

set_option linter.mathlibStandardSet false

open Complex Filter Topology
open scoped Topology

noncomputable section
namespace Q3.RouteB

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A compact evaluation envelope weighted by the square-root projective
defect transfers directly to uniform convergence of the phase-aligned error. -/
theorem tendstoUniformlyOn_zero_of_weighted_projective_defect
    {ι α E : Type*} [NormedAddCommGroup E]
    {l : Filter ι} [NeBot l]
    (T : ι → H → α → E) (u v : ι → H)
    (K : Set α) (C : ι → ℝ)
    (hu : ∀ᶠ i in l, ‖u i‖ = 1)
    (hv : ∀ᶠ i in l, ‖v i‖ = 1)
    (hC : ∀ᶠ i in l, 0 ≤ C i)
    (hprojectiveRate : Tendsto
      (fun i => C i * √(2 * (1 - ‖inner ℂ (u i) (v i)‖ ^ 2)))
      l (𝓝 0))
    (hevaluation : ∀ᶠ i in l, ∀ z ∈ K,
      ‖T i (alignmentPhase (inner ℂ (u i) (v i)) • u i - v i) z‖ ≤
        C i * ‖alignmentPhase (inner ℂ (u i) (v i)) • u i - v i‖) :
    TendstoUniformlyOn
      (fun i z => T i
        (alignmentPhase (inner ℂ (u i) (v i)) • u i - v i) z)
      (fun _ => 0) l K := by
  let e : ι → H := fun i =>
    alignmentPhase (inner ℂ (u i) (v i)) • u i - v i
  have hnonneg : ∀ᶠ i in l, 0 ≤ C i * ‖e i‖ := by
    filter_upwards [hC] with i hCi
    exact mul_nonneg hCi (norm_nonneg _)
  have hweighted : ∀ᶠ i in l,
      C i * ‖e i‖ ≤
        C i * √(2 * (1 - ‖inner ℂ (u i) (v i)‖ ^ 2)) := by
    filter_upwards [hu, hv, hC] with i hui hvi hCi
    exact mul_le_mul_of_nonneg_left
      (phase_alignment_norm_le_sqrt_two_projective_defect
        (u i) (v i) hui hvi) hCi
  have hrate : Tendsto (fun i => C i * ‖e i‖) l (𝓝 0) :=
    squeeze_zero' hnonneg hweighted hprojectiveRate
  have hevaluation' : ∀ᶠ i in l, ∀ z ∈ K,
      ‖T i (e i) z‖ ≤ C i * ‖e i‖ := by
    simpa [e] using hevaluation
  simpa [e] using
    (tendstoUniformlyOn_zero_of_evaluation_rate
      T e K C hrate hevaluation')

#print axioms tendstoUniformlyOn_zero_of_weighted_projective_defect

end Q3.RouteB
