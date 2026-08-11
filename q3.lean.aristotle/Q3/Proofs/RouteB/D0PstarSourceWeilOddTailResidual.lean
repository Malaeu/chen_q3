import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailExplicitCoercivity

set_option linter.mathlibStandardSet false

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Literal source-Weil odd-tail residual

This file constructs the exact low-head to infinite-tail cross-block of the
shifted source-Weil graph operator.  The head is the Euclidean coefficient
space of the literal normalized odd graph modes below the cutoff; the tail is
the B3.0AJ closed odd graph tail.  Orthogonal projection of the actual source
operator gives a bounded residual into that exact tail.

At the explicit B3.0AK cutoff, this residual and the proved continuously
invertible outer block instantiate the actual B3.0AI `R† C⁻¹ R` correction.
No scalar inverse, finite-section matrix, or raw residual norm is substituted.
This file does not yet prove the cancellation-sensitive quantitative theorem
`OddTailGradedResolventBound13`.
-/

/-- Synthesis of the literal low odd graph modes below the tail cutoff. -/
noncomputable def sourceWeilGraphOddHeadSynthesisLinear
    (i : PairIndex) (R : ℕ) :
    EuclideanSpace ℂ (Fin R) →ₗ[ℂ] SourceWeilGraphCarrier i where
  toFun q := ∑ k, q k • sourceWeilGraphOddMode i k
  map_add' := by
    intro q r
    simp only [WithLp.ofLp_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
  map_smul' := by
    intro c q
    simp only [RingHom.id_apply, WithLp.ofLp_smul, Pi.smul_apply,
      smul_eq_mul, smul_smul, Finset.smul_sum]

/-- The finite literal head synthesis is continuous. -/
noncomputable def sourceWeilGraphOddHeadSynthesis
    (i : PairIndex) (R : ℕ) :
    EuclideanSpace ℂ (Fin R) →L[ℂ] SourceWeilGraphCarrier i :=
  (sourceWeilGraphOddHeadSynthesisLinear i R).toContinuousLinearMap

/-- Literal source cross-block from low odd coefficients into the closed odd
tail.  This is the actual shifted source-Weil operator followed by the exact
tail projection. -/
noncomputable def sourceWeilOddTailResidual
    (i : PairIndex) (R : ℕ) :
    EuclideanSpace ℂ (Fin R) →L[ℂ] SourceWeilGraphOddTailCarrier i R :=
  (sourceWeilGraphOddTail i R).orthogonalProjection.comp
    ((sourceWeilShiftedGraphOperator i).comp
      (sourceWeilGraphOddHeadSynthesis i R))

/-- The residual is bounded in the exact graph Hilbert norms. -/
theorem norm_sourceWeilOddTailResidual_le
    (i : PairIndex) (R : ℕ) (q : EuclideanSpace ℂ (Fin R)) :
    ‖sourceWeilOddTailResidual i R q‖ ≤
      ‖sourceWeilOddTailResidual i R‖ * ‖q‖ := by
  exact ContinuousLinearMap.le_opNorm _ _

/-- Exact source pairing of the literal cross-block; projection does not alter
pairing against a vector already in the tail. -/
theorem inner_sourceWeilOddTailResidual
    (i : PairIndex) (R : ℕ) (q : EuclideanSpace ℂ (Fin R))
    (y : SourceWeilGraphOddTailCarrier i R) :
    inner ℂ (sourceWeilOddTailResidual i R q) y =
      inner ℂ
        (sourceWeilShiftedGraphOperator i
          (sourceWeilGraphOddHeadSynthesis i R q))
        (y : SourceWeilGraphCarrier i) := by
  exact (sourceWeilGraphOddTail i R).inner_orthogonalProjection_eq_of_mem_right
    y (sourceWeilShiftedGraphOperator i
      (sourceWeilGraphOddHeadSynthesis i R q))

abbrev SourceWeilOddHeadCoefficients (i : PairIndex) :=
  EuclideanSpace ℂ (Fin (sourceWeilOddTailCutoff i))

/-- The explicit B3.0AK-cutoff residual. -/
noncomputable def sourceWeilOddTailExplicitResidual
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i) :=
  sourceWeilOddTailResidual i (sourceWeilOddTailCutoff i)

/-- Exact source data with both the actual outer block and actual cross-block. -/
noncomputable def sourceWeilOddTailExplicitInverseWeightedData
    (i : PairIndex) :
    OddTailInverseWeightedData
      (SourceWeilOddHeadCoefficients i)
      (SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) :=
  sourceWeilOddTailInverseWeightedData i (sourceWeilOddTailCutoff i)
    (1 / 2) (sourceWeilOddTailAmbientCoercive_explicit i)
    (sourceWeilOddTailExplicitResidual i)

@[simp] theorem sourceWeilOddTailExplicitInverseWeightedData_outerBlock
    (i : PairIndex) :
    (sourceWeilOddTailExplicitInverseWeightedData i).outerBlock =
      sourceWeilShiftedOddTailOperator i (sourceWeilOddTailCutoff i) := by
  rfl

@[simp] theorem sourceWeilOddTailExplicitInverseWeightedData_residual
    (i : PairIndex) :
    (sourceWeilOddTailExplicitInverseWeightedData i).residual =
      sourceWeilOddTailExplicitResidual i := by
  rfl

/-- The actual inverse-weighted source correction at the explicit cutoff. -/
noncomputable def sourceWeilOddTailExplicitCorrection
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilOddHeadCoefficients i :=
  oddTailInverseWeightedCorrection
    (sourceWeilOddTailExplicitInverseWeightedData i)

theorem sourceWeilOddTailExplicitCorrection_isPositive
    (i : PairIndex) :
    (sourceWeilOddTailExplicitCorrection i).IsPositive := by
  exact oddTailInverseWeightedCorrection_isPositive
    (sourceWeilOddTailExplicitInverseWeightedData i)

/-- Exact quadratic pairing through the actual outer inverse. -/
theorem inner_sourceWeilOddTailExplicitCorrection
    (i : PairIndex) (q r : SourceWeilOddHeadCoefficients i) :
    inner ℂ (sourceWeilOddTailExplicitCorrection i q) r =
      inner ℂ
        ((sourceWeilShiftedOddTailOperator i
            (sourceWeilOddTailCutoff i)).inverse
          (sourceWeilOddTailExplicitResidual i q))
        (sourceWeilOddTailExplicitResidual i r) := by
  exact inner_oddTailInverseWeightedCorrection
    (sourceWeilOddTailExplicitInverseWeightedData i) q r

#print axioms sourceWeilGraphOddHeadSynthesis
#print axioms sourceWeilOddTailResidual
#print axioms norm_sourceWeilOddTailResidual_le
#print axioms inner_sourceWeilOddTailResidual
#print axioms sourceWeilOddTailExplicitInverseWeightedData
#print axioms sourceWeilOddTailExplicitCorrection_isPositive
#print axioms inner_sourceWeilOddTailExplicitCorrection

end Q3.RouteB.D0Pstar
