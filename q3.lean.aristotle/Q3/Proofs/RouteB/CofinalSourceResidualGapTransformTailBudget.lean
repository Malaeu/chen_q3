import Q3.Proofs.RouteB.CompactEvaluationRateTransfer
import Q3.Proofs.RouteB.PhaseAlignmentRateTransfer

set_option linter.mathlibStandardSet false

open Complex Filter Topology
open scoped Topology

noncomputable section
namespace Q3.RouteB

/-!
# Cofinal source residual/gap transform-tail budget

This file removes the free-error loophole left by the generic same-family
composition core.

The finite trial is computed by a named projection, its residual is computed
from a named source operator and its exact Rayleigh scalar, the coefficient-to-
function map is a named continuous linear evaluation operator, and the
normalization is an explicit scalar family.  The only tail premise is the
literal difference between the normalized projected-source transform and the
named trial target.

The theorem is still conditional.  It does not prove the projective
residual/gap inequality, the compact evaluation envelope, the cofinal decay
rate, or the transform tail.  It proves that these source-facing suppliers
compose without an arbitrary error function or an assumed decomposition
identity.
-/

/-- Exact Rayleigh residual of a unit vector for a named linear operator.  The
Rayleigh scalar is computed from the same operator and the same vector; it is
not a free parameter. -/
def sourceUnitRayleighResidual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (A : H →ₗ[ℂ] H) (q : H) : H :=
  A q - inner ℂ q (A q) • q

/-- A cofinal residual/gap budget plus the literal normalized transform tail
forces the phase-aligned ground transforms to track the named trial target
locally uniformly.

No error family and no decomposition identity occur as arguments.  The
tracking error is computed from `ground`, `finiteProjection`, `sourceTrial`,
`normalizer`, and `evaluation`; the residual is computed by
`sourceUnitRayleighResidual`; the tail is the literal displayed difference in
`htail`. -/
theorem cofinalSourceResidualGapTransformTailBudget
    {ι α E H : Type*}
    [TopologicalSpace α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {l : Filter ι} [NeBot l]
    (sourceOperator finiteProjection : ι → H →ₗ[ℂ] H)
    (ground sourceTrial : ι → H)
    (gap : ι → ℝ)
    (normalizer : ι → ℂ)
    (hnormalizerNonzero : ∀ i, normalizer i ≠ 0)
    (evaluation : ι → α → H →L[ℂ] E)
    (trialTarget : ι → α → E)
    (U : Set α) (hU : IsOpen U)
    (hgroundUnit : ∀ᶠ i in l, ‖ground i‖ = 1)
    (hprojectedUnit :
      ∀ᶠ i in l, ‖finiteProjection i (sourceTrial i)‖ = 1)
    (hgapPositive : ∀ᶠ i in l, 0 < gap i)
    (hprojectiveResidualGap :
      ∀ᶠ i in l,
        1 - ‖inner ℂ (ground i)
              (finiteProjection i (sourceTrial i))‖ ^ 2 ≤
          ‖sourceUnitRayleighResidual
              (sourceOperator i)
              (finiteProjection i (sourceTrial i))‖ ^ 2 /
            gap i ^ 2)
    (hcompactBudget :
      ∀ K ⊆ U, IsCompact K →
        ∃ C : ι → ℝ,
          Tendsto
              (fun i =>
                C i * √(2 *
                  (‖sourceUnitRayleighResidual
                      (sourceOperator i)
                      (finiteProjection i (sourceTrial i))‖ ^ 2 /
                    gap i ^ 2)))
              l (𝓝 0) ∧
            ∀ᶠ i in l,
              0 ≤ C i ∧
                ∀ z ∈ K, ∀ x : H,
                  ‖evaluation i z (normalizer i • x)‖ ≤ C i * ‖x‖)
    (htail :
      TendstoLocallyUniformlyOn
        (fun i z =>
          evaluation i z
              (normalizer i • finiteProjection i (sourceTrial i)) -
            trialTarget i z)
        (fun _ => 0) l U) :
    TendstoLocallyUniformlyOn
      (fun i z =>
        evaluation i z
            (normalizer i •
              (alignmentPhase
                  (inner ℂ (ground i)
                    (finiteProjection i (sourceTrial i))) •
                ground i)) -
          trialTarget i z)
      (fun _ => 0) l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at htail ⊢
  intro K hKU hK
  obtain ⟨C, hbudget, hCbound⟩ := hcompactBudget K hKU hK
  let q : ι → H := fun i => finiteProjection i (sourceTrial i)
  let r : ι → H := fun i => sourceUnitRayleighResidual (sourceOperator i) (q i)
  let e : ι → H := fun i =>
    alignmentPhase (inner ℂ (ground i) (q i)) • ground i - q i
  have hnonneg : ∀ᶠ i in l, 0 ≤ C i * ‖e i‖ := by
    filter_upwards [hCbound] with i hCi
    exact mul_nonneg hCi.1 (norm_nonneg _)
  have hupper : ∀ᶠ i in l,
      C i * ‖e i‖ ≤
        C i * √(2 * (‖r i‖ ^ 2 / gap i ^ 2)) := by
    filter_upwards [hgroundUnit, hprojectedUnit, hgapPositive,
      hprojectiveResidualGap, hCbound] with
      i hground hq hgap hdefect hCi
    have hphase :
        ‖e i‖ ≤
          √(2 * (1 - ‖inner ℂ (ground i) (q i)‖ ^ 2)) := by
      simpa [e, q] using
        phase_alignment_norm_le_sqrt_two_projective_defect
          (ground i) (q i) hground (by simpa [q] using hq)
    have hdefect' :
        1 - ‖inner ℂ (ground i) (q i)‖ ^ 2 ≤
          ‖r i‖ ^ 2 / gap i ^ 2 := by
      simpa [q, r] using hdefect
    have hgapSq : 0 < gap i ^ 2 := pow_pos hgap 2
    have hratioNonneg : 0 ≤ ‖r i‖ ^ 2 / gap i ^ 2 :=
      div_nonneg (sq_nonneg _) hgapSq.le
    have hsqrt :
        √(2 * (1 - ‖inner ℂ (ground i) (q i)‖ ^ 2)) ≤
          √(2 * (‖r i‖ ^ 2 / gap i ^ 2)) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    exact mul_le_mul_of_nonneg_left (hphase.trans hsqrt) hCi.1
  have hbudget' :
      Tendsto
        (fun i => C i * √(2 * (‖r i‖ ^ 2 / gap i ^ 2)))
        l (𝓝 0) := by
    simpa [q, r] using hbudget
  have hrate :
      Tendsto (fun i => C i * ‖e i‖) l (𝓝 0) :=
    squeeze_zero' hnonneg hupper hbudget'
  have hevaluation :
      ∀ᶠ i in l, ∀ z ∈ K,
        ‖evaluation i z (normalizer i • e i)‖ ≤ C i * ‖e i‖ := by
    filter_upwards [hCbound] with i hCi
    intro z hz
    exact hCi.2 z hz (e i)
  have htrackingRaw :
      TendstoUniformlyOn
        (fun i z => evaluation i z (normalizer i • e i))
        (fun _ => 0) l K :=
    tendstoUniformlyOn_zero_of_evaluation_rate
      (fun i x z => evaluation i z (normalizer i • x))
      e K C hrate hevaluation
  have htracking :
      TendstoUniformlyOn
        (fun i z =>
          evaluation i z
              (normalizer i •
                (alignmentPhase (inner ℂ (ground i) (q i)) • ground i)) -
            evaluation i z (normalizer i • q i))
        (fun _ => 0) l K := by
    convert htrackingRaw using 1
    ext i z
    simp [e, smul_sub]
  have hsum := htracking.add (htail K hKU hK)
  convert hsum using 1
  · ext i z
    simp [q]
  · ext z
    simp

/- A zero residual budget does not make a nonvanishing transform tail disappear.
The direct tail premise above is therefore load-bearing. -/
example :
    ¬ TendstoUniformlyOn
      (fun _ : ℕ => fun _ : Unit => (1 : ℝ))
      (fun _ => (0 : ℝ)) atTop ({()} : Set Unit) :=
  fixed_bound_without_vanishing_rate_not_uniform_zero.2

#print axioms cofinalSourceResidualGapTransformTailBudget

end Q3.RouteB
