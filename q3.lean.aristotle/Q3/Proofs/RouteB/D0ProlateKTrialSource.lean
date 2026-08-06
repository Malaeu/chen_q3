import Q3.Proofs.RouteB.D0KTrialStage3
import Q3.Proofs.RouteB.ProlateLayer

set_option linter.mathlibStandardSet false

open Complex MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

namespace Q3.RouteB.D0Pstar

open CanonicalRHRoute

/-!
# Source-faithful prolate-to-kTrial contract

This module closes only the XW.8 type-level provenance seam.  It packages the
existing exact construction

`prolateCombination -> E_star -> gTrial_m -> gTrial_m_N -> kTrial_m_N -> c_n`

as the `CoefficientFamily` consumed by `centeredPstarFamily`.  Every analytic
supplier and the cofinal schedule remain explicit data.  In particular, this
module proves no existence theorem for prolate modes, no ground-state
identification, no convergence theorem, and no `SlotS2` statement.
-/

/-- Exact source data needed to construct the D0 coefficient row from the
canonical two-mode prolate packet.  The consumed source trial is determined
by `m`; `N` enters only through the finite projection and its certificates.

The equality `lambda_eq` prevents the free bandwidth stored in `ProlatePair`
from drifting away from the production convention `lambda_m i = sqrt i.m`.
The remaining fields are precisely the existing carrier and nonzero
certificates required by `c_n`; they are not synthesized here.  This contract
proves no projection-tail or regularity theorem.
-/
structure ProlateKTrialSourceData where
  pair : PairIndex → ProlatePair
  prolateCombination_eq_of_same_m :
    ∀ i j : PairIndex, i.m = j.m →
      prolateCombination (pair i) =
        prolateCombination (pair j)
  lambda_eq : ∀ i, (pair i).pw.lambda = lambda_m i
  eStar_memLp :
    ∀ i,
      MemLp (E_star (prolateCombination (pair i))) 2
        (dStar.restrict (I_m i))
  trialNonzero :
    ∀ i,
      TrialNonzero i (prolateCombination (pair i)) (eStar_memLp i)

/-- Applying `E_star` preserves the exact same-`m` source identity.  The
projection certificates remain allowed to depend on the full pair index.
-/
@[simp] theorem ProlateKTrialSourceData.E_star_eq_of_same_m
    (S : ProlateKTrialSourceData)
    (i j : PairIndex)
    (hm : i.m = j.m) :
    E_star (prolateCombination (S.pair i)) =
      E_star (prolateCombination (S.pair j)) := by
  rw [S.prolateCombination_eq_of_same_m i j hm]

namespace ProlateKTrialSourceData

/-- The production coefficient family whose row is definitionally the Fourier
coefficient of the normalized projected starred sum of the same
`prolateCombination` stored in `S`.
-/
def coefficientFamily (S : ProlateKTrialSourceData) : CoefficientFamily where
  kTrial := fun i n =>
    c_n i (prolateCombination (S.pair i))
      (S.eStar_memLp i) (S.trialNonzero i) n

/-- XW.8's exact finite-row provenance is definitional; there is no
independently supplied coefficient selector.
-/
@[simp] theorem coefficientFamily_kTrial
    (S : ProlateKTrialSourceData) (i : PairIndex) (n : ℤ) :
    S.coefficientFamily.kTrial i n =
      c_n i (prolateCombination (S.pair i))
        (S.eStar_memLp i) (S.trialNonzero i) n :=
  rfl

end ProlateKTrialSourceData

/-- A production `CanonicalData` together with the exact proof that its
coefficient family is the prolate-derived family above.

Keeping the already-dependent `CanonicalData` as one field avoids duplicating
its `CentralIndex` dependency in this wrapper.  Its `parent` and `extract`
therefore remain literally the production suppliers, while `kTrial_eq` rules
out an independent coefficient family.
-/
structure ProlateCanonicalSourceData where
  source : ProlateKTrialSourceData
  canonical : CanonicalData
  kTrial_eq : canonical.kTrial = source.coefficientFamily

namespace ProlateCanonicalSourceData

/-- The coefficient row stored in the production `CanonicalData` is exactly
the Fourier coefficient of the normalized projected starred sum of the same
source packet.
-/
@[simp] theorem canonical_kTrial
    (S : ProlateCanonicalSourceData) (i : PairIndex) (n : ℤ) :
    S.canonical.kTrial.kTrial i n =
      c_n i (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i) (S.source.trialNonzero i) n := by
  rw [S.kTrial_eq]
  rfl

/-- The exact selected-family expansion on the same `parent ∘ extract`
sequence.  Combined with `coefficientFamily_kTrial`, this exposes the complete
type-level path from the source packet to the production family.
-/
@[simp] theorem selectedFamily_apply
    (S : ProlateCanonicalSourceData) (k : ℕ) :
    selectedFamily (canonicalApproximation S.canonical) k =
      centeredPstarFamily S.canonical.kTrial
        (S.canonical.parent (S.canonical.extract k)) :=
  rfl

end ProlateCanonicalSourceData

#print axioms ProlateKTrialSourceData.coefficientFamily_kTrial
#print axioms ProlateKTrialSourceData.E_star_eq_of_same_m
#print axioms ProlateCanonicalSourceData.canonical_kTrial
#print axioms ProlateCanonicalSourceData.selectedFamily_apply

end Q3.RouteB.D0Pstar
