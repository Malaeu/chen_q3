import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailResidual

set_option linter.mathlibStandardSet false

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Exact shifted source-Weil odd-head Schur complement

This file compresses the actual shifted source-Weil graph operator to the
literal low odd head and eliminates the closed infinite odd tail through the
actual B3.0AK outer inverse.  It proves positivity of the exact Schur
complement

`S† A S - R† C⁻¹ R`.

The conclusion is deliberately structural and shifted.  It is not the
cancellation-sensitive quantitative theorem `OddTailGradedResolventBound13`,
does not produce a positive `c₀` floor for the unshifted source form, and does
not use the finite `N = 480/960` diagnostics.
-/

private theorem re_inner_map_sub_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x y : E) :
    (inner ℂ (A (x - y)) (x - y)).re =
      (inner ℂ (A x) x).re - (inner ℂ (A x) y).re -
        (inner ℂ (A y) x).re + (inner ℂ (A y) y).re := by
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  simp only [sub_re]
  ring

/-- Literal shifted source-Weil compression to the low odd head. -/
noncomputable def sourceWeilShiftedOddHeadOperator
    (i : PairIndex) (R : ℕ) :
    EuclideanSpace ℂ (Fin R) →L[ℂ] EuclideanSpace ℂ (Fin R) :=
  (sourceWeilGraphOddHeadSynthesis i R).adjoint.comp
    ((sourceWeilShiftedGraphOperator i).comp
      (sourceWeilGraphOddHeadSynthesis i R))

theorem inner_sourceWeilShiftedOddHeadOperator
    (i : PairIndex) (R : ℕ)
    (q r : EuclideanSpace ℂ (Fin R)) :
    inner ℂ (sourceWeilShiftedOddHeadOperator i R q) r =
      inner ℂ
        (sourceWeilShiftedGraphOperator i
          (sourceWeilGraphOddHeadSynthesis i R q))
        (sourceWeilGraphOddHeadSynthesis i R r) := by
  rw [sourceWeilShiftedOddHeadOperator]
  simp only [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

/-- The literal shifted head compression is positive. -/
theorem sourceWeilShiftedOddHeadOperator_isPositive
    (i : PairIndex) (R : ℕ) :
    (sourceWeilShiftedOddHeadOperator i R).IsPositive := by
  simpa [sourceWeilShiftedOddHeadOperator] using
    (sourceWeilShiftedGraphOperator_isPositive i).adjoint_conj
      (sourceWeilGraphOddHeadSynthesis i R)

private theorem inverseWeightedCorrection_le_compression_of_block
    {Head Tail Ambient : Type*}
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
    [NormedAddCommGroup Tail] [InnerProductSpace ℂ Tail] [CompleteSpace Tail]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℂ Ambient]
    (A : Ambient →L[ℂ] Ambient)
    (S : Head →L[ℂ] Ambient) (U : Tail →L[ℂ] Ambient)
    (D : OddTailInverseWeightedData Head Tail)
    (hA : A.IsPositive)
    (hres : ∀ x y, inner ℂ (D.residual x) y = inner ℂ (A (S x)) (U y))
    (htail : ∀ y, inner ℂ (A (U y)) (U y) = inner ℂ (D.outerBlock y) y)
    (x : Head) :
    (inner ℂ (oddTailInverseWeightedCorrection D x) x).re ≤
      (inner ℂ (A (S x)) (S x)).re := by
  let v := D.outerBlock.inverse (D.residual x)
  have hinv : D.outerBlock v = D.residual x :=
    outerBlock_apply_inverse_residual D x
  have hcross :
      (inner ℂ (A (U v)) (S x)).re =
        (inner ℂ (A (S x)) (U v)).re := by
    calc
      (inner ℂ (A (U v)) (S x)).re =
          (inner ℂ (U v) (A (S x))).re :=
        congrArg Complex.re (hA.isSymmetric (U v) (S x))
      _ = (inner ℂ (A (S x)) (U v)).re := by
        change RCLike.re (inner ℂ (U v) (A (S x))) =
          RCLike.re (inner ℂ (A (S x)) (U v))
        exact inner_re_symm (𝕜 := ℂ) (E := Ambient) _ _
  have hcorr :
      (inner ℂ (oddTailInverseWeightedCorrection D x) x).re =
        (inner ℂ (D.residual x) v).re := by
    rw [inner_oddTailInverseWeightedCorrection]
    change RCLike.re (inner ℂ v (D.residual x)) =
      RCLike.re (inner ℂ (D.residual x) v)
    exact inner_re_symm (𝕜 := ℂ) (E := Tail) _ _
  have hpos : 0 ≤ (inner ℂ (A (S x - U v)) (S x - U v)).re :=
    hA.re_inner_nonneg_left _
  have hfull :
      (inner ℂ (A (S x - U v)) (S x - U v)).re =
        (inner ℂ (A (S x)) (S x)).re -
          (inner ℂ (D.residual x) v).re := by
    rw [re_inner_map_sub_self A (S x) (U v)]
    rw [hres x v, hcross, htail v, hinv]
    rw [hres x v]
    ring
  rw [hcorr]
  rw [hfull] at hpos
  linarith

set_option maxHeartbeats 400000 in
theorem sourceWeilOddTailExplicitCorrection_le_shiftedHead
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i) :
    (inner ℂ (sourceWeilOddTailExplicitCorrection i q) q).re ≤
      (inner ℂ
        (sourceWeilShiftedOddHeadOperator i (sourceWeilOddTailCutoff i) q)
        q).re := by
  change
    (inner ℂ
      (oddTailInverseWeightedCorrection
        (sourceWeilOddTailExplicitInverseWeightedData i) q) q).re ≤ _
  rw [inner_sourceWeilShiftedOddHeadOperator]
  have hres : ∀ x y,
      inner ℂ
          ((sourceWeilOddTailExplicitInverseWeightedData i).residual x) y =
        inner ℂ
          (sourceWeilShiftedGraphOperator i
            (sourceWeilGraphOddHeadSynthesis i
              (sourceWeilOddTailCutoff i) x))
          ((sourceWeilGraphOddTail i
            (sourceWeilOddTailCutoff i)).subtypeL y) := by
    intro x y
    change inner ℂ
        (sourceWeilOddTailResidual i (sourceWeilOddTailCutoff i) x) y = _
    exact inner_sourceWeilOddTailResidual i
      (sourceWeilOddTailCutoff i) x y
  have htail : ∀ y,
      inner ℂ
          (sourceWeilShiftedGraphOperator i
            ((sourceWeilGraphOddTail i
              (sourceWeilOddTailCutoff i)).subtypeL y))
          ((sourceWeilGraphOddTail i
            (sourceWeilOddTailCutoff i)).subtypeL y) =
        inner ℂ
          ((sourceWeilOddTailExplicitInverseWeightedData i).outerBlock y) y := by
    intro y
    change inner ℂ
        (sourceWeilShiftedGraphOperator i
          ((sourceWeilGraphOddTail i
            (sourceWeilOddTailCutoff i)).subtypeL y))
        ((sourceWeilGraphOddTail i
          (sourceWeilOddTailCutoff i)).subtypeL y) =
      inner ℂ
        (sourceWeilShiftedOddTailOperator i
          (sourceWeilOddTailCutoff i) y) y
    exact (inner_sourceWeilShiftedOddTailOperator i
      (sourceWeilOddTailCutoff i) y y).symm
  exact inverseWeightedCorrection_le_compression_of_block
    (Head := SourceWeilOddHeadCoefficients i)
    (Tail := SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i))
    (Ambient := SourceWeilGraphCarrier i)
    (sourceWeilShiftedGraphOperator i)
    (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i))
    (sourceWeilGraphOddTail i (sourceWeilOddTailCutoff i)).subtypeL
    (sourceWeilOddTailExplicitInverseWeightedData i)
    (sourceWeilShiftedGraphOperator_isPositive i)
    hres htail
    q

/-- Exact Schur complement of the literal shifted low head by the actual
infinite odd-tail outer block. -/
noncomputable def sourceWeilShiftedOddHeadSchurComplement
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilOddHeadCoefficients i :=
  oddTailSchurComplement
    (sourceWeilShiftedOddHeadOperator i (sourceWeilOddTailCutoff i))
    (sourceWeilOddTailExplicitInverseWeightedData i)

/-- The exact shifted Schur complement is positive.  This is the structural
Schur fact for the already-shifted source operator; it is not a quantitative
lower bound for the unshifted source form. -/
theorem sourceWeilShiftedOddHeadSchurComplement_isPositive
    (i : PairIndex) :
    (sourceWeilShiftedOddHeadSchurComplement i).IsPositive := by
  refine ⟨?_, ?_⟩
  · exact
      (sourceWeilShiftedOddHeadOperator_isPositive i
        (sourceWeilOddTailCutoff i)).isSymmetric.sub
        (sourceWeilOddTailExplicitCorrection_isPositive i).isSymmetric
  · intro q
    change 0 ≤
      (inner ℂ
        ((sourceWeilShiftedOddHeadOperator i (sourceWeilOddTailCutoff i) -
          sourceWeilOddTailExplicitCorrection i) q) q).re
    simp only [ContinuousLinearMap.sub_apply, inner_sub_left, sub_re]
    exact sub_nonneg.mpr
      (sourceWeilOddTailExplicitCorrection_le_shiftedHead i q)

/-- Exact operator decomposition of the shifted head compression into its
positive Schur complement and the actual inverse-weighted correction. -/
theorem sourceWeilShiftedOddHeadOperator_eq_schur_add_correction
    (i : PairIndex) :
    sourceWeilShiftedOddHeadOperator i (sourceWeilOddTailCutoff i) =
      sourceWeilShiftedOddHeadSchurComplement i +
        sourceWeilOddTailExplicitCorrection i := by
  exact operator_eq_oddTailSchurComplement_add_correction
    (sourceWeilShiftedOddHeadOperator i (sourceWeilOddTailCutoff i))
    (sourceWeilOddTailExplicitInverseWeightedData i)

#print axioms sourceWeilShiftedOddHeadOperator
#print axioms inner_sourceWeilShiftedOddHeadOperator
#print axioms sourceWeilShiftedOddHeadOperator_isPositive
#print axioms sourceWeilOddTailExplicitCorrection_le_shiftedHead
#print axioms sourceWeilShiftedOddHeadSchurComplement
#print axioms sourceWeilShiftedOddHeadSchurComplement_isPositive
#print axioms sourceWeilShiftedOddHeadOperator_eq_schur_add_correction

end Q3.RouteB.D0Pstar
