import Q3.Proofs.RouteB.D0PstarSourceWeilOddTargetFloorSchurReduction

set_option linter.mathlibStandardSet false

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Exact receiver for the `m = 13` target-floor Schur certificate

This file fixes the kernel-facing target left open by B3.0AN.  It proves that
the exact finite Schur operator is symmetric, identifies positivity with the
scalar Schur energy and with the full head--tail block energy, and packages the
honest `m = 13` target with a universal quantifier over the auxiliary
`PairIndex.N` coordinate.

The symbolic analytic cutoff, its lower-bound constant, and the literal head
synthesis are definitionally independent of that auxiliary coordinate at
`m = 13`.  No equality of the large graph-carrier objects is asserted merely
from this fact.

The file does **not** prove `SourceWeilOddTargetFloorSchurPositive13`.  The
remaining obligation is still an exact positivity certificate for the finite
Schur energy.  No finite numerical section, form-core bridge, whole odd-space
floor, Route B promotion, or RH claim is introduced here.
-/

/-- The exact target-floor head compression is symmetric. -/
theorem sourceWeilOddTargetFloorHeadOperator_isSymmetric
    (i : PairIndex) :
    (sourceWeilOddTargetFloorHeadOperator i).IsSymmetric := by
  let S := sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i)
  let A := sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor
  have hA : A.IsSymmetric :=
    sourceWeilC0ShiftedGraphOperator_isSymmetric i sourceWeilOddTargetFloor
  have h := hA.isSelfAdjoint.adjoint_conj S
  simpa [sourceWeilOddTargetFloorHeadOperator, S, A,
    ContinuousLinearMap.comp_assoc] using h.isSymmetric

/-- Subtracting the positive inverse-weighted correction preserves symmetry. -/
theorem sourceWeilOddTargetFloorSchurComplement_isSymmetric
    (i : PairIndex) :
    (sourceWeilOddTargetFloorSchurComplement i).IsSymmetric := by
  exact (sourceWeilOddTargetFloorHeadOperator_isSymmetric i).sub
    (oddTailInverseWeightedCorrection_isPositive
      (sourceWeilOddTargetFloorInverseWeightedData i)).isSymmetric

/-- The missing operator sign is exactly nonnegativity of its real quadratic
energy; symmetry is already discharged. -/
theorem sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy
    (i : PairIndex) :
    (sourceWeilOddTargetFloorSchurComplement i).IsPositive ↔
      ∀ q : SourceWeilOddHeadCoefficients i,
        0 ≤ sourceWeilOddTargetFloorSchurEnergy i q := by
  constructor
  · intro h q
    exact h.re_inner_nonneg_left q
  · intro h
    refine ⟨sourceWeilOddTargetFloorSchurComplement_isSymmetric i, ?_⟩
    intro q
    exact h q

/-- The completed tail term in B3.0AN is always nonnegative. -/
theorem sourceWeilOddTargetFloorCompletedTailEnergy_nonneg
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) :
    0 ≤ sourceWeilOddTargetFloorCompletedTailEnergy i q y := by
  exact (sourceWeilOddTargetFloorTail_isPositive i).re_inner_nonneg_left
    (y + sourceWeilOddTargetFloorCorrector i q)

set_option maxHeartbeats 3000000 in
/-- Evaluating the block at the exact inverse-weighted corrector recovers the
finite Schur energy with no residual tail term. -/
theorem sourceWeilOddTargetFloorSchurEnergy_eq_blockEnergy_corrected
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i) :
    sourceWeilOddTargetFloorSchurEnergy i q =
      sourceWeilOddTargetFloorBlockEnergy i q
        (-sourceWeilOddTargetFloorCorrector i q) := by
  let v := sourceWeilOddTargetFloorCorrector i q
  have hv : -v + v = 0 := neg_add_cancel v
  have hzero :
      sourceWeilOddTargetFloorCompletedTailEnergy i q (-v) = 0 := by
    unfold sourceWeilOddTargetFloorCompletedTailEnergy
    rw [hv]
    rw [ContinuousLinearMap.map_zero]
    rw [inner_zero_left]
    exact Complex.zero_re
  have h := sourceWeilOddTargetFloor_block_completion i q
    (-sourceWeilOddTargetFloorCorrector i q)
  change sourceWeilOddTargetFloorSchurEnergy i q =
    sourceWeilOddTargetFloorBlockEnergy i q (-v)
  change sourceWeilOddTargetFloorBlockEnergy i q (-v) =
    sourceWeilOddTargetFloorSchurEnergy i q +
      sourceWeilOddTargetFloorCompletedTailEnergy i q (-v) at h
  rw [hzero, add_zero] at h
  exact h.symm

/-- Exact Schur positivity is equivalent to nonnegativity of the complete
literal head--tail block. -/
theorem sourceWeilOddTargetFloorSchurComplement_isPositive_iff_block
    (i : PairIndex) :
    (sourceWeilOddTargetFloorSchurComplement i).IsPositive ↔
      ∀ (q : SourceWeilOddHeadCoefficients i)
        (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)),
        0 ≤ sourceWeilOddTargetFloorBlockEnergy i q y := by
  rw [sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy]
  constructor
  · intro h q y
    rw [sourceWeilOddTargetFloor_block_completion]
    exact add_nonneg (h q)
      (sourceWeilOddTargetFloorCompletedTailEnergy_nonneg i q y)
  · intro h q
    rw [sourceWeilOddTargetFloorSchurEnergy_eq_blockEnergy_corrected]
    exact h q (-sourceWeilOddTargetFloorCorrector i q)

/-- At fixed source cell `m = 13`, the analytic tail cutoff does not depend on
the auxiliary finite coordinate carried by `PairIndex`. -/
theorem sourceWeilOddTailCutoff_13_N_irrelevant
    (N M : ℕ) :
    sourceWeilOddTailCutoff (PairIndex.mk 13 N (by norm_num)) =
      sourceWeilOddTailCutoff (PairIndex.mk 13 M (by norm_num)) := by
  rfl

/-- The global lower-bound constant used in the cutoff is likewise independent
of the auxiliary coordinate at `m = 13`. -/
theorem sourceWeilLowerBoundConstant_13_N_irrelevant
    (N M : ℕ) :
    sourceWeilLowerBoundConstant (PairIndex.mk 13 N (by norm_num)) =
      sourceWeilLowerBoundConstant (PairIndex.mk 13 M (by norm_num)) := by
  rfl

set_option maxHeartbeats 3000000 in
/-- The literal normalized odd head synthesis at a fixed cutoff depends on the
source cell `m = 13`, not on the auxiliary `PairIndex.N` coordinate. -/
theorem sourceWeilGraphOddHeadSynthesis_13_N_irrelevant
    (N M R : ℕ) :
    sourceWeilGraphOddHeadSynthesis
        (PairIndex.mk 13 N (by norm_num)) R =
      sourceWeilGraphOddHeadSynthesis
        (PairIndex.mk 13 M (by norm_num)) R := by
  rfl

/-- Honest kernel-facing target for the `m = 13` certificate.  Universal
quantification prevents a proof for one arbitrary auxiliary `N` from being
mistaken for a property of the source cell. -/
def SourceWeilOddTargetFloorSchurPositive13 : Prop :=
  ∀ N : ℕ,
    (sourceWeilOddTargetFloorSchurComplement
      (PairIndex.mk 13 N (by norm_num))).IsPositive

/-- Scalar-energy receiver for the exact `m = 13`, all-`N` target. -/
theorem sourceWeilOddTargetFloorSchurPositive13_iff_energy :
    SourceWeilOddTargetFloorSchurPositive13 ↔
      ∀ (N : ℕ)
        (q : SourceWeilOddHeadCoefficients
          (PairIndex.mk 13 N (by norm_num))),
        0 ≤ sourceWeilOddTargetFloorSchurEnergy
          (PairIndex.mk 13 N (by norm_num)) q := by
  constructor
  · intro h N
    exact (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy
      (PairIndex.mk 13 N (by norm_num))).mp (h N)
  · intro h N
    exact (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy
      (PairIndex.mk 13 N (by norm_num))).mpr (h N)

/-- Full block-energy receiver for the exact `m = 13`, all-`N` target. -/
theorem sourceWeilOddTargetFloorSchurPositive13_iff_block :
    SourceWeilOddTargetFloorSchurPositive13 ↔
      ∀ (N : ℕ)
        (q : SourceWeilOddHeadCoefficients
          (PairIndex.mk 13 N (by norm_num)))
        (y : SourceWeilGraphOddTailCarrier
          (PairIndex.mk 13 N (by norm_num))
          (sourceWeilOddTailCutoff
            (PairIndex.mk 13 N (by norm_num)))),
        0 ≤ sourceWeilOddTargetFloorBlockEnergy
          (PairIndex.mk 13 N (by norm_num)) q y := by
  constructor
  · intro h N
    exact (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_block
      (PairIndex.mk 13 N (by norm_num))).mp (h N)
  · intro h N
    exact (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_block
      (PairIndex.mk 13 N (by norm_num))).mpr (h N)

#print axioms sourceWeilOddTargetFloorHeadOperator_isSymmetric
#print axioms sourceWeilOddTargetFloorSchurComplement_isSymmetric
#print axioms sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy
#print axioms sourceWeilOddTargetFloorSchurComplement_isPositive_iff_block
#print axioms sourceWeilOddTailCutoff_13_N_irrelevant
#print axioms sourceWeilLowerBoundConstant_13_N_irrelevant
#print axioms sourceWeilGraphOddHeadSynthesis_13_N_irrelevant
#print axioms sourceWeilOddTargetFloorSchurPositive13_iff_energy
#print axioms sourceWeilOddTargetFloorSchurPositive13_iff_block

end Q3.RouteB.D0Pstar
