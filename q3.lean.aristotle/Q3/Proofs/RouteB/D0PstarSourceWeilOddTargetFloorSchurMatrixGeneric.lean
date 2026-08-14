import Q3.Proofs.RouteB.D0PstarSourceWeilOddTargetFloorSchurMatrixReceiver

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-!
# Exact arbitrary-cell matrix receiver for the source-Weil odd Schur head

The predecessor matrix receiver was restricted to `m = 13`.  This file keeps
the literal production `PairIndex` and proves the same exact pullback for every
cell.  It removes only the fixed-cell adapter restriction: the corrected
finite-head sign remains an explicit arithmetic obligation, and no uniform
floor, cofinal connector, G1, Route B promotion, or RH claim is made.
-/

/-- The ambient component of a literal odd graph head is the normalized odd
CCM synthesis at the same `m` and head radius. -/
theorem sourceWeilGraphAmbient_oddHeadSynthesis_eq_coe_sourceWeilOddSynthesis
    (i : PairIndex) (R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    sourceWeilGraphAmbient i
        (sourceWeilGraphOddHeadSynthesis i R q) =
      (sourceWeilOddSynthesis (PairIndex.mk i.m R i.hm) q :
        H_m (PairIndex.mk i.m R i.hm)) := by
  rw [sourceWeilOddSynthesis_eq_normalized_mode_sum]
  change sourceWeilGraphAmbient i
      (∑ k : Fin R, q k • sourceWeilGraphOddMode i k) = _
  rw [map_sum]
  simp only [sourceArchimedeanModeInShiftedFormDomain]
  change _ =
    (sourceArchimedeanShiftedFormDomain
      (PairIndex.mk i.m R i.hm)).subtype _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_smul, sourceWeilGraphAmbient_oddMode]
  rfl

/-- One normalized antisymmetric source mode in the exact shifted form domain
of an arbitrary production cell. -/
noncomputable def sourceWeilOddModeInShiftedFormDomain
    (i : PairIndex) (k : ℕ) :
    sourceArchimedeanShiftedFormDomain i :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (sourceArchimedeanModeInShiftedFormDomain i (k + 1 : ℕ) -
      sourceArchimedeanModeInShiftedFormDomain i
        (-((k + 1 : ℕ) : ℤ)))

/-- Domain-valued graph-head expansion on an arbitrary production cell. -/
theorem sourceWeilGraphDomain_oddHeadSynthesis_eq_mode_sum
    (i : PairIndex) (R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    sourceWeilGraphDomain i
        (sourceWeilGraphOddHeadSynthesis i R q) =
      ∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain i k := by
  apply Subtype.ext
  change sourceWeilGraphAmbient i
      (∑ k : Fin R, q k • sourceWeilGraphOddMode i k) = _
  rw [map_sum]
  change _ = (sourceArchimedeanShiftedFormDomain i).subtype _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_smul, sourceWeilGraphAmbient_oddMode]
  rfl

/-- A finite normalized odd-mode sum depends on the production cell only
through `m`; changing the auxiliary `N` to the head radius leaves the exact
source form unchanged. -/
theorem sourceWeilOddModeSum_form_N_irrelevant
    (i : PairIndex) (R : ℕ)
    (q r : EuclideanSpace ℂ (Fin R)) :
    sourceWeilSesquilinearForm i
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain i k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain i k) =
      sourceWeilSesquilinearForm (PairIndex.mk i.m R i.hm)
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain
          (PairIndex.mk i.m R i.hm) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain
          (PairIndex.mk i.m R i.hm) k) := by
  classical
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1

/-- The arbitrary-cell graph-head expansion lands on the generic normalized
odd CCM synthesis at the same `m` and head radius. -/
theorem sourceWeilOddModeSum_form_eq_sourceWeilOddSynthesis
    (i : PairIndex) (R : ℕ)
    (q r : EuclideanSpace ℂ (Fin R)) :
    sourceWeilSesquilinearForm i
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain i k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain i k) =
      sourceWeilSesquilinearForm (PairIndex.mk i.m R i.hm)
        (sourceWeilOddSynthesis (PairIndex.mk i.m R i.hm) q)
        (sourceWeilOddSynthesis (PairIndex.mk i.m R i.hm) r) := by
  rw [sourceWeilOddSynthesis_eq_normalized_mode_sum,
    sourceWeilOddSynthesis_eq_normalized_mode_sum]
  exact sourceWeilOddModeSum_form_N_irrelevant i R q r

/-- The generic normalized odd synthesis preserves the ambient inner
product. -/
theorem inner_coe_sourceWeilOddSynthesis
    (i : PairIndex) (q r : EuclideanSpace ℂ (Fin i.N)) :
    inner ℂ
        ((sourceWeilOddSynthesis i q :
          sourceArchimedeanShiftedFormDomain i) : H_m i)
        ((sourceWeilOddSynthesis i r :
          sourceArchimedeanShiftedFormDomain i) : H_m i) =
      inner ℂ q r := by
  change inner ℂ (sourceWeilOddSynthesis i q)
      (sourceWeilOddSynthesis i r) = inner ℂ q r
  exact (sourceWeilOddSynthesis i).inner_map_map q r

/-- Exact source-matrix formula for the target-floor head pairing on every
production cell. -/
theorem inner_sourceWeilOddTargetFloorHeadOperator_eq_ccm
    (i : PairIndex) (q r : SourceWeilOddHeadCoefficients i) :
    inner ℂ (sourceWeilOddTargetFloorHeadOperator i q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff i) q) j) *
            (Q3.RouteB.ccmWeilMatFinite i.m
              (sourceWeilOddTailCutoff i) j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff i) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r := by
  rw [inner_sourceWeilOddTargetFloorHeadOperator]
  rw [inner_sourceWeilC0ShiftedGraphOperator]
  rw [sourceWeilGraphDomain_oddHeadSynthesis_eq_mode_sum,
    sourceWeilGraphDomain_oddHeadSynthesis_eq_mode_sum]
  rw [sourceWeilGraphAmbient_oddHeadSynthesis_eq_coe_sourceWeilOddSynthesis,
    sourceWeilGraphAmbient_oddHeadSynthesis_eq_coe_sourceWeilOddSynthesis]
  rw [sourceWeilOddModeSum_form_eq_sourceWeilOddSynthesis]
  rw [sourceWeilOddFormPullback]
  rw [inner_coe_sourceWeilOddSynthesis]

/-- Exact corrected finite-matrix formula for the Schur pairing on every
production cell.  The last term remains the actual inverse-weighted infinite
tail correction. -/
theorem inner_sourceWeilOddTargetFloorSchurComplement_eq_ccm
    (i : PairIndex) (q r : SourceWeilOddHeadCoefficients i) :
    inner ℂ (sourceWeilOddTargetFloorSchurComplement i q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff i) q) j) *
            (Q3.RouteB.ccmWeilMatFinite i.m
              (sourceWeilOddTailCutoff i) j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff i) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r -
        inner ℂ
          (oddTailInverseWeightedCorrection
            (sourceWeilOddTargetFloorInverseWeightedData i) q) r := by
  unfold sourceWeilOddTargetFloorSchurComplement
  unfold oddTailSchurComplement
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  rw [inner_sourceWeilOddTargetFloorHeadOperator_eq_ccm]

/-- The arbitrary-cell Schur sign is exactly the corrected finite CCM energy
sign.  This is a receiver equivalence, not a proof of that sign. -/
theorem sourceWeilOddTargetFloorSchurComplement_isPositive_iff_ccm_corrected_energy
    (i : PairIndex) :
    (sourceWeilOddTargetFloorSchurComplement i).IsPositive ↔
      ∀ q : SourceWeilOddHeadCoefficients i,
        0 ≤ ((∑ j, ∑ k,
            star ((ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff i) q) j) *
              (Q3.RouteB.ccmWeilMatFinite i.m
                (sourceWeilOddTailCutoff i) j k : ℂ) *
              (ccmOddCoefficientIsometry
                (sourceWeilOddTailCutoff i) q) k) -
          (sourceWeilOddTargetFloor : ℂ) * inner ℂ q q -
          inner ℂ
            (oddTailInverseWeightedCorrection
              (sourceWeilOddTargetFloorInverseWeightedData i) q) q).re := by
  constructor
  · intro h q
    have hq :=
      (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy i).mp h q
    unfold sourceWeilOddTargetFloorSchurEnergy at hq
    rw [inner_sourceWeilOddTargetFloorSchurComplement_eq_ccm] at hq
    exact hq
  · intro h
    apply (sourceWeilOddTargetFloorSchurComplement_isPositive_iff_energy i).mpr
    intro q
    unfold sourceWeilOddTargetFloorSchurEnergy
    rw [inner_sourceWeilOddTargetFloorSchurComplement_eq_ccm]
    exact h q

#print axioms sourceWeilGraphAmbient_oddHeadSynthesis_eq_coe_sourceWeilOddSynthesis
#print axioms sourceWeilOddModeInShiftedFormDomain
#print axioms sourceWeilGraphDomain_oddHeadSynthesis_eq_mode_sum
#print axioms sourceWeilOddModeSum_form_N_irrelevant
#print axioms sourceWeilOddModeSum_form_eq_sourceWeilOddSynthesis
#print axioms inner_coe_sourceWeilOddSynthesis
#print axioms inner_sourceWeilOddTargetFloorHeadOperator_eq_ccm
#print axioms inner_sourceWeilOddTargetFloorSchurComplement_eq_ccm
#print axioms sourceWeilOddTargetFloorSchurComplement_isPositive_iff_ccm_corrected_energy

end Q3.RouteB.D0Pstar
