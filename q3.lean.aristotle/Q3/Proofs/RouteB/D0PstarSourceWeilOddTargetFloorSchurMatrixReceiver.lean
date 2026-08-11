import Q3.Proofs.RouteB.D0PstarSourceWeilOddTargetFloorSchurReceiver
import Q3.Proofs.RouteB.D0PstarSourceWeilOddFormPullback13

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

noncomputable section

open Complex
open scoped BigOperators ComplexConjugate

namespace Q3.RouteB.D0Pstar

/-!
# Exact all-`N`, `m = 13` matrix receiver for the target-floor Schur sign

This file keeps the universal auxiliary-`N` target from B3.0AO literally
intact.  It does not reduce the large graph operators to a canonical `N = 0`
representative: a clean source rebuild showed that such a reduction is not a
cheap definitional equality and must not be advertised.

Instead, the literal odd graph head is expanded mode by mode and crossed to
the existing B3.0AF normalized odd CCM synthesis for every auxiliary `N` and
every head size.  This yields an exact all-`N` pairing formula for the Schur
complement as the source matrix form, minus the target-floor scalar form,
minus the actual inverse-weighted infinite-tail correction.

No sign is proved.  The symbolic analytic cutoff and actual tail inverse are
preserved, and no finite `N = 480/960` surrogate is introduced.
-/

/-- The ambient component of the literal graph-head synthesis is the existing
normalized odd CCM synthesis, for every auxiliary graph coordinate `N` and
every literal head size `R`.  The proof is an explicit finite mode expansion,
not a large-operator definitional reduction. -/
theorem sourceWeilGraphAmbient_oddHeadSynthesis13_eq_coe_sourceWeilOddSynthesis13
    (N R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    sourceWeilGraphAmbient (PairIndex.mk 13 N (by norm_num))
        (sourceWeilGraphOddHeadSynthesis
          (PairIndex.mk 13 N (by norm_num)) R q) =
      (sourceWeilOddSynthesis13 R q :
        H_m (PairIndex.mk 13 R (by norm_num))) := by
  rw [sourceWeilOddSynthesis13_eq_normalized_mode_sum]
  change sourceWeilGraphAmbient (PairIndex.mk 13 N (by norm_num))
      (∑ k : Fin R, q k • sourceWeilGraphOddMode
        (PairIndex.mk 13 N (by norm_num)) k) = _
  rw [map_sum]
  simp only [sourceArchimedeanModeInShiftedFormDomain]
  change _ =
    (sourceArchimedeanShiftedFormDomain
      (PairIndex.mk 13 R (by norm_num))).subtype _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_smul, sourceWeilGraphAmbient_oddMode]
  rfl

/-- One normalized antisymmetric source mode in the exact shifted form
domain.  Its index is the physical pair `±(k+1)`. -/
noncomputable def sourceWeilOddModeInShiftedFormDomain13
    (i : PairIndex) (k : ℕ) :
    sourceArchimedeanShiftedFormDomain i :=
  (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) •
    (sourceArchimedeanModeInShiftedFormDomain i (k + 1 : ℕ) -
      sourceArchimedeanModeInShiftedFormDomain i (-((k + 1 : ℕ) : ℤ)))

/-- Domain-valued graph-head expansion at the original auxiliary coordinate.
Unlike the ambient crosswalk above, this statement never changes the carrier
before the source form is evaluated. -/
theorem sourceWeilGraphDomain_oddHeadSynthesis13_eq_mode_sum
    (N R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    sourceWeilGraphDomain (PairIndex.mk 13 N (by norm_num))
        (sourceWeilGraphOddHeadSynthesis
          (PairIndex.mk 13 N (by norm_num)) R q) =
      ∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
        (PairIndex.mk 13 N (by norm_num)) k := by
  apply Subtype.ext
  change sourceWeilGraphAmbient (PairIndex.mk 13 N (by norm_num))
      (∑ k : Fin R, q k • sourceWeilGraphOddMode
        (PairIndex.mk 13 N (by norm_num)) k) = _
  rw [map_sum]
  change _ =
    (sourceArchimedeanShiftedFormDomain
      (PairIndex.mk 13 N (by norm_num))).subtype _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro k _hk
  rw [map_smul, sourceWeilGraphAmbient_oddMode]
  rfl

/-- On a literal finite odd-mode sum, the exact source-Weil form at fixed
`m = 13` is independent of the auxiliary `PairIndex.N`.  This is proved only
after finite sesquilinear expansion; no equality of the large operators is
claimed. -/
theorem sourceWeilOddModeSum13_form_N_irrelevant
    (N R : ℕ) (q r : EuclideanSpace ℂ (Fin R)) :
    sourceWeilSesquilinearForm (PairIndex.mk 13 N (by norm_num))
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k) =
      sourceWeilSesquilinearForm (PairIndex.mk 13 R (by norm_num))
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 R (by norm_num)) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 R (by norm_num)) k) := by
  classical
  simp_rw [map_sum, map_smul, map_smulₛₗ]
  apply Finset.sum_congr rfl
  intro k _hk
  congr 1

/-- The preceding finite expansion lands exactly on the existing normalized
odd CCM synthesis at head size `R`. -/
theorem sourceWeilOddModeSum13_form_eq_sourceWeilOddSynthesis13
    (N R : ℕ) (q r : EuclideanSpace ℂ (Fin R)) :
    sourceWeilSesquilinearForm (PairIndex.mk 13 N (by norm_num))
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k) =
      sourceWeilSesquilinearForm (PairIndex.mk 13 R (by norm_num))
        (sourceWeilOddSynthesis13 R q)
        (sourceWeilOddSynthesis13 R r) := by
  rw [sourceWeilOddSynthesis13_eq_normalized_mode_sum,
    sourceWeilOddSynthesis13_eq_normalized_mode_sum]
  change sourceWeilSesquilinearForm (PairIndex.mk 13 N (by norm_num))
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 N (by norm_num)) k) =
      sourceWeilSesquilinearForm (PairIndex.mk 13 R (by norm_num))
        (∑ k : Fin R, q k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 R (by norm_num)) k)
        (∑ k : Fin R, r k • sourceWeilOddModeInShiftedFormDomain13
          (PairIndex.mk 13 R (by norm_num)) k)
  exact sourceWeilOddModeSum13_form_N_irrelevant N R q r

/-- The normalized odd synthesis preserves the ambient inner product. -/
theorem inner_coe_sourceWeilOddSynthesis13
    (R : ℕ) (q r : EuclideanSpace ℂ (Fin R)) :
    inner ℂ
        ((sourceWeilOddSynthesis13 R q :
          sourceArchimedeanShiftedFormDomain
            (PairIndex.mk 13 R (by norm_num))) :
          H_m (PairIndex.mk 13 R (by norm_num)))
        ((sourceWeilOddSynthesis13 R r :
          sourceArchimedeanShiftedFormDomain
            (PairIndex.mk 13 R (by norm_num))) :
          H_m (PairIndex.mk 13 R (by norm_num))) =
      inner ℂ q r := by
  change inner ℂ (sourceWeilOddSynthesis13 R q)
      (sourceWeilOddSynthesis13 R r) = inner ℂ q r
  exact (sourceWeilOddSynthesis13 R).inner_map_map q r

/-- Exact source-matrix formula for every auxiliary-`N` target-floor head
pairing. -/
theorem inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm
    (N : ℕ)
    (q r : SourceWeilOddHeadCoefficients
      (PairIndex.mk 13 N (by norm_num))) :
    inner ℂ
        (sourceWeilOddTargetFloorHeadOperator
          (PairIndex.mk 13 N (by norm_num)) q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff
              (PairIndex.mk 13 N (by norm_num))) q) j) *
            (Q3.RouteB.ccmWeilMatFinite 13
              (sourceWeilOddTailCutoff
                (PairIndex.mk 13 N (by norm_num)))
              j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff
                (PairIndex.mk 13 N (by norm_num))) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r := by
  rw [inner_sourceWeilOddTargetFloorHeadOperator]
  rw [inner_sourceWeilC0ShiftedGraphOperator]
  rw [sourceWeilGraphDomain_oddHeadSynthesis13_eq_mode_sum,
    sourceWeilGraphDomain_oddHeadSynthesis13_eq_mode_sum]
  rw [sourceWeilGraphAmbient_oddHeadSynthesis13_eq_coe_sourceWeilOddSynthesis13,
    sourceWeilGraphAmbient_oddHeadSynthesis13_eq_coe_sourceWeilOddSynthesis13]
  rw [sourceWeilOddModeSum13_form_eq_sourceWeilOddSynthesis13]
  rw [sourceWeilOddFormPullback13]
  rw [inner_coe_sourceWeilOddSynthesis13]

/-- Exact corrected finite-matrix formula for every auxiliary-`N` Schur pairing.
The last term is the actual infinite-tail inverse-weighted correction. -/
theorem inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm
    (N : ℕ)
    (q r : SourceWeilOddHeadCoefficients
      (PairIndex.mk 13 N (by norm_num))) :
    inner ℂ
        (sourceWeilOddTargetFloorSchurComplement
          (PairIndex.mk 13 N (by norm_num)) q) r =
      (∑ j, ∑ k,
          star ((ccmOddCoefficientIsometry
            (sourceWeilOddTailCutoff
              (PairIndex.mk 13 N (by norm_num))) q) j) *
            (Q3.RouteB.ccmWeilMatFinite 13
              (sourceWeilOddTailCutoff
                (PairIndex.mk 13 N (by norm_num)))
              j k : ℂ) *
            (ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff
                (PairIndex.mk 13 N (by norm_num))) r) k) -
        (sourceWeilOddTargetFloor : ℂ) * inner ℂ q r -
        inner ℂ
          (oddTailInverseWeightedCorrection
            (sourceWeilOddTargetFloorInverseWeightedData
              (PairIndex.mk 13 N (by norm_num))) q) r := by
  unfold sourceWeilOddTargetFloorSchurComplement
  unfold oddTailSchurComplement
  rw [ContinuousLinearMap.sub_apply, inner_sub_left]
  rw [inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm N]

/-- Final kernel receiver: the exact all-`N`, `m = 13` target is equivalent
to nonnegativity of the corresponding corrected CCM energy for every
auxiliary `N`.  This theorem exposes but does not prove the missing sign. -/
theorem sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy :
    SourceWeilOddTargetFloorSchurPositive13 ↔
      ∀ (N : ℕ)
        (q : SourceWeilOddHeadCoefficients
          (PairIndex.mk 13 N (by norm_num))),
        0 ≤ ((∑ j, ∑ k,
            star ((ccmOddCoefficientIsometry
              (sourceWeilOddTailCutoff
                (PairIndex.mk 13 N (by norm_num))) q) j) *
              (Q3.RouteB.ccmWeilMatFinite 13
                (sourceWeilOddTailCutoff
                  (PairIndex.mk 13 N (by norm_num)))
                j k : ℂ) *
              (ccmOddCoefficientIsometry
                (sourceWeilOddTailCutoff
                  (PairIndex.mk 13 N (by norm_num))) q) k) -
          (sourceWeilOddTargetFloor : ℂ) * inner ℂ q q -
          inner ℂ
            (oddTailInverseWeightedCorrection
              (sourceWeilOddTargetFloorInverseWeightedData
                (PairIndex.mk 13 N (by norm_num))) q) q).re := by
  constructor
  · intro h N q
    have hq :=
      (sourceWeilOddTargetFloorSchurPositive13_iff_energy.mp h) N q
    unfold sourceWeilOddTargetFloorSchurEnergy at hq
    rw [inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm N] at hq
    exact hq
  · intro h
    apply sourceWeilOddTargetFloorSchurPositive13_iff_energy.mpr
    intro N q
    unfold sourceWeilOddTargetFloorSchurEnergy
    rw [inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm N]
    exact h N q

#print axioms sourceWeilGraphAmbient_oddHeadSynthesis13_eq_coe_sourceWeilOddSynthesis13
#print axioms sourceWeilOddModeInShiftedFormDomain13
#print axioms sourceWeilGraphDomain_oddHeadSynthesis13_eq_mode_sum
#print axioms sourceWeilOddModeSum13_form_N_irrelevant
#print axioms sourceWeilOddModeSum13_form_eq_sourceWeilOddSynthesis13
#print axioms inner_coe_sourceWeilOddSynthesis13
#print axioms inner_sourceWeilOddTargetFloorHeadOperator13_eq_ccm
#print axioms inner_sourceWeilOddTargetFloorSchurComplement13_eq_ccm
#print axioms sourceWeilOddTargetFloorSchurPositive13_iff_ccm_corrected_energy

end Q3.RouteB.D0Pstar
