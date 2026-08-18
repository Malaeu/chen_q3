import Q3.Proofs.RouteB.WeightedProjectiveEvaluationTransfer
import Q3.Proofs.RouteB.UniformDifferenceReferenceTransfer

set_option linter.mathlibStandardSet false

open Filter Topology
open scoped Topology

noncomputable section
namespace Q3.RouteB

/-!
# Same-family ground-to-trial cofinal composition core

This file closes only the generic composition layer of the Goal 058
same-family span.  It works with one index type, one filter, one domain, one
finite-ground family, and one CCM-trial family.  An exact additive identity
splits their difference into three independently supplied errors:

* phase-aligned/projective tracking error;
* finite-projection tail error;
* normalization error.

If all three errors vanish locally uniformly along the same filter, then the
literal difference of the two named families vanishes locally uniformly.

The theorem deliberately does not prove any source-specific residual bound,
true complement floor, compact evaluation envelope, projection-tail decay,
normalizer nondegeneracy, cofinal schedule, trial-to-`Xi` limit, or RH claim.
Those remain explicit suppliers.  In particular, no error term may be defined
as the desired conclusion under a new name.
-/

/-- The exact additive compact-error ledger for one ground family and one trial
family composes to locally uniform convergence of their difference to zero.
All three suppliers use the same index type, filter, domain, and pair of named
families; changing a family, normalization, or cofinal schedule between the
premises is therefore outside this theorem's type. -/
theorem sameFamilyGroundTrialCompositionCore
    {ι α E : Type*}
    [TopologicalSpace α] [LocallyCompactSpace α]
    [NormedAddCommGroup E]
    {l : Filter ι} [NeBot l]
    (finiteGroundTransform ccmTrialTransform : ι → α → E)
    (trackingError projectionTail normalizationError : ι → α → E)
    (U : Set α) (hU : IsOpen U)
    (hdecomp : ∀ i z,
      finiteGroundTransform i z - ccmTrialTransform i z =
        trackingError i z + projectionTail i z + normalizationError i z)
    (htracking : TendstoLocallyUniformlyOn
      trackingError (fun _ => 0) l U)
    (htail : TendstoLocallyUniformlyOn
      projectionTail (fun _ => 0) l U)
    (hnormalization : TendstoLocallyUniformlyOn
      normalizationError (fun _ => 0) l U) :
    TendstoLocallyUniformlyOn
      (fun i z => finiteGroundTransform i z - ccmTrialTransform i z)
      (fun _ => 0) l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU] at
    htracking htail hnormalization ⊢
  intro K hKU hK
  have hsum :=
    ((htracking K hKU hK).add (htail K hKU hK)).add
      (hnormalization K hKU hK)
  convert hsum using 1
  · ext i z
    exact hdecomp i z
  · ext z
    simp

/- A fixed bound without a vanishing rate remains rejected by the imported
compact-envelope plant.  This guards the composer against replacing any of the
three convergence premises by mere boundedness. -/
example :
    ¬ TendstoUniformlyOn
      (fun _ : ℕ => fun _ : Unit => (1 : ℝ))
      (fun _ => (0 : ℝ)) atTop ({()} : Set Unit) :=
  fixed_bound_without_vanishing_rate_not_uniform_zero.2

#print axioms sameFamilyGroundTrialCompositionCore

end Q3.RouteB
