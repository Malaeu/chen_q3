import Q3.Proofs.RouteB.D0PstarSourceWeilOddTargetFloorSchurReceiver
import Q3.Proofs.RouteB.D0PstarSourceWeilOddFormPullback13

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 3000000

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-!
# Canonical `m = 13` matrix receiver for the target-floor Schur sign

B3.0AO fixed the honest all-auxiliary-`N` target but deliberately exported
only three cheap `N`-independence facts.  Here Lean checks the stronger fact:
at fixed source cell `m = 13`, the graph carrier, target-floor operator and
exact Schur complement are definitionally independent of `PairIndex.N`.
Consequently the universal target is equivalent to one canonical `N = 0`
representative without weakening the source statement.

The literal odd graph head is also definitionally the existing B3.0AF odd
CCM synthesis.  This gives an exact pairing formula for the Schur complement
as the source matrix form, minus the target-floor scalar form, minus the
actual inverse-weighted infinite-tail correction.

No sign is proved.  The symbolic analytic cutoff and actual tail inverse are
preserved, and no finite `N = 480/960` surrogate is introduced.
-/

/-- Canonical auxiliary representative of the source cell `m = 13`. -/
def sourceWeilOddCanonicalIndex13 : PairIndex :=
  PairIndex.mk 13 0 (by norm_num)

/-- The large source graph carrier at fixed `m = 13` is definitionally
independent of the auxiliary Galerkin coordinate. -/
theorem sourceWeilGraphCarrier_13_N_irrelevant
    (N M : ℕ) :
    SourceWeilGraphCarrier (PairIndex.mk 13 N (by norm_num)) =
      SourceWeilGraphCarrier (PairIndex.mk 13 M (by norm_num)) := by
  rfl

/-- The exact target-floor graph operator at fixed `m = 13` is independent of
the auxiliary Galerkin coordinate. -/
theorem sourceWeilC0ShiftedGraphOperator_13_N_irrelevant
    (N M : ℕ) :
    sourceWeilC0ShiftedGraphOperator
        (PairIndex.mk 13 N (by norm_num)) sourceWeilOddTargetFloor =
      sourceWeilC0ShiftedGraphOperator
        (PairIndex.mk 13 M (by norm_num)) sourceWeilOddTargetFloor := by
  rfl

/-- The exact target-floor Schur operator at fixed `m = 13` is definitionally
the same operator for every auxiliary `PairIndex.N`. -/
theorem sourceWeilOddTargetFloorSchurComplement_13_N_irrelevant
    (N M : ℕ) :
    sourceWeilOddTargetFloorSchurComplement
        (PairIndex.mk 13 N (by norm_num)) =
      sourceWeilOddTargetFloorSchurComplement
        (PairIndex.mk 13 M (by norm_num)) := by
  rfl

/-- The scalar Schur energy at fixed `m = 13` is likewise independent of the
auxiliary coordinate. -/
theorem sourceWeilOddTargetFloorSchurEnergy_13_N_irrelevant
    (N M : ℕ) :
    sourceWeilOddTargetFloorSchurEnergy
        (PairIndex.mk 13 N (by norm_num)) =
      sourceWeilOddTargetFloorSchurEnergy
        (PairIndex.mk 13 M (by norm_num)) := by
  rfl

/-- The all-`N` target is exactly one canonical source-cell statement, not a
weaker fixed-`N` surrogate. -/
theorem sourceWeilOddTargetFloorSchurPositive13_iff_canonical :
    SourceWeilOddTargetFloorSchurPositive13 ↔
      (sourceWeilOddTargetFloorSchurComplement
        sourceWeilOddCanonicalIndex13).IsPositive := by
  constructor
  · intro h
    exact h 0
  · intro h N
    simpa [sourceWeilOddCanonicalIndex13] using h

/-- The literal graph-head synthesis is definitionally the already verified
normalized odd CCM synthesis at the same head size. -/
theorem sourceWeilGraphOddHeadSynthesis13_eq_sourceWeilOddSynthesis13
    (R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    sourceWeilGraphDomain sourceWeilOddCanonicalIndex13
        (sourceWeilGraphOddHeadSynthesis
          sourceWeilOddCanonicalIndex13 R q) =
      sourceWeilOddSynthesis13 R q := by
  rfl

/-- Exact source-matrix formula for the canonical target-floor head pairing. -/
theorem inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm
    (q r : SourceWeilOddHeadCoefficients sourceWeilOddCanonicalIndex13) :
    inner ℂ
        (sourceWeilOddTargetFloorHeadOperator
          sourceWeilOddCanonicalIndex13 q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) q) j) *
            (Q3.RouteB.ccmWeilMatFinite 13
              (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13)
              j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r := by
  rw [inner_sourceWeilOddTargetFloorHeadOperator]
  rw [inner_sourceWeilC0ShiftedGraphOperator]
  change sourceWeilSesquilinearForm sourceWeilOddCanonicalIndex13
      (sourceWeilOddSynthesis13
        (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) q)
      (sourceWeilOddSynthesis13
        (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) r) -
      (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r = _
  rw [sourceWeilOddFormPullback13]

/-- Exact corrected finite-matrix formula for the canonical Schur pairing.
The last term is the actual infinite-tail inverse-weighted correction. -/
theorem inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm
    (q r : SourceWeilOddHeadCoefficients sourceWeilOddCanonicalIndex13) :
    inner ℂ
        (sourceWeilOddTargetFloorSchurComplement
          sourceWeilOddCanonicalIndex13 q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) q) j) *
            (Q3.RouteB.ccmWeilMatFinite 13
              (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13)
              j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r -
        inner ℂ
          (oddTailInverseWeightedCorrection
            (sourceWeilOddTargetFloorInverseWeightedData
              sourceWeilOddCanonicalIndex13) q) r := by
  unfold sourceWeilOddTargetFloorSchurComplement
  unfold oddTailSchurComplement
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  rw [inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm]

/-- Final kernel receiver: the exact all-`N`, `m = 13` target is equivalent
to nonnegativity of one canonical corrected CCM energy at the symbolic source
cutoff.  This theorem exposes but does not prove the missing finite sign. -/
theorem sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy :
    SourceWeilOddTargetFloorSchurPositive13 ↔
      ∀ q : SourceWeilOddHeadCoefficients sourceWeilOddCanonicalIndex13,
        0 ≤ ((∑ j, ∑ k,
            star ((ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) q) j) *
              (Q3.RouteB.ccmWeilMatFinite 13
                (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13)
                j k : ℂ) *
              (ccmOddCoefficientIsometry
                (sourceWeilOddTailCutoff sourceWeilOddCanonicalIndex13) q) k) -
          (sourceWeilOddTargetFloor : ℂ) * inner ℂ q q -
          inner ℂ
            (oddTailInverseWeightedCorrection
              (sourceWeilOddTargetFloorInverseWeightedData
                sourceWeilOddCanonicalIndex13) q) q).re := by
  rw [sourceWeilOddTargetFloorSchurPositive13_iff_canonical]
  rw [sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy]
  simp only [sourceWeilOddTargetFloorSchurEnergy]
  constructor
  · intro h q
    rw [inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm] at h
    exact h q
  · intro h q
    rw [inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm]
    exact h q

#print axioms sourceWeilGraphCarrier_13_N_irrelevant
#print axioms sourceWeilC0ShiftedGraphOperator_13_N_irrelevant
#print axioms sourceWeilOddTargetFloorSchurComplement_13_N_irrelevant
#print axioms sourceWeilOddTargetFloorSchurEnergy_13_N_irrelevant
#print axioms sourceWeilOddTargetFloorSchurPositive13_iff_canonical
#print axioms sourceWeilGraphOddHeadSynthesis13_eq_sourceWeilOddSynthesis13
#print axioms inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm
#print axioms inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm
#print axioms sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy

end Q3.RouteB.D0Pstar
