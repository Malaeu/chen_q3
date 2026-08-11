import Q3.Proofs.RouteB.D0PstarSourceWeilShiftedOddHeadSchur

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

open Complex

namespace Q3.RouteB.D0Pstar

/-!
# Exact target-floor reduction for the source-Weil odd block

This file removes the large auxiliary lower-bound shift from the actual graph
operator and replaces it by the pre-registered target floor `10⁻⁵⁸`.  The
explicit B3.0AK tail estimate and the independent weighted-energy lower bound
combine to control the full graph norm, so the actual `c₀`-shifted infinite
tail is positive and continuously invertible.

The file then constructs the literal `c₀` residual, actual inverse-weighted
correction and exact finite Schur complement, and proves completion of the
square.  It does not assert that the finite Schur complement is positive; that
remaining sign is exactly the next quantitative certificate obligation.
-/

noncomputable def sourceWeilC0ShiftedGraphOperator
    (i : PairIndex) (c0 : ℝ) :
    SourceWeilGraphCarrier i →L[ℂ] SourceWeilGraphCarrier i :=
  sourceWeilShiftedGraphOperator i -
    (((sourceWeilLowerBoundConstant i + c0 : ℝ) : ℂ) •
      ((sourceWeilGraphAmbient i).adjoint.comp
        (sourceWeilGraphAmbient i)))

theorem inner_sourceWeilC0ShiftedGraphOperator
    (i : PairIndex) (c0 : ℝ) (x y : SourceWeilGraphCarrier i) :
    inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 x) y =
      sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i y) -
        (c0 : ℂ) * inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i y) := by
  rw [sourceWeilC0ShiftedGraphOperator,
    ContinuousLinearMap.sub_apply, inner_sub_left]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.comp_apply, inner_smul_left, Complex.conj_ofReal]
  rw [ContinuousLinearMap.adjoint_inner_left]
  rw [inner_sourceWeilShiftedGraphOperator_eq_source]
  push_cast
  ring

theorem inner_sourceWeilC0ShiftedGraphOperator_self
    (i : PairIndex) (c0 : ℝ) (x : SourceWeilGraphCarrier i) :
    (inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 x) x).re =
      (sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i x)).re -
        c0 * ‖sourceWeilGraphAmbient i x‖ ^ 2 := by
  rw [inner_sourceWeilC0ShiftedGraphOperator]
  have hinner :
      (inner ℂ (sourceWeilGraphAmbient i x)
        (sourceWeilGraphAmbient i x)).re =
          ‖sourceWeilGraphAmbient i x‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (sourceWeilGraphAmbient i x))
  simp only [sub_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hinner]

theorem sourceWeilC0ShiftedGraphOperator_isSymmetric
    (i : PairIndex) (c0 : ℝ) :
    (sourceWeilC0ShiftedGraphOperator i c0).IsSymmetric := by
  intro x y
  change inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 x) y =
    inner ℂ x (sourceWeilC0ShiftedGraphOperator i c0 y)
  calc
    inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 x) y =
        sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i y) -
          (c0 : ℂ) * inner ℂ (sourceWeilGraphAmbient i x)
            (sourceWeilGraphAmbient i y) :=
      inner_sourceWeilC0ShiftedGraphOperator i c0 x y
    _ = star
        (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i y) (sourceWeilGraphDomain i x) -
          (c0 : ℂ) * inner ℂ (sourceWeilGraphAmbient i y)
            (sourceWeilGraphAmbient i x)) := by
      change _ = (starRingEnd ℂ)
        (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i y) (sourceWeilGraphDomain i x) -
          (c0 : ℂ) * inner ℂ (sourceWeilGraphAmbient i y)
            (sourceWeilGraphAmbient i x))
      rw [map_sub, map_mul, Complex.conj_ofReal, inner_conj_symm]
      rw [sourceWeilSesquilinearForm_conj_symm]
      rfl
    _ = star (inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 y) x) := by
      rw [inner_sourceWeilC0ShiftedGraphOperator]
    _ = inner ℂ x (sourceWeilC0ShiftedGraphOperator i c0 y) := by
      change (starRingEnd ℂ)
        (inner ℂ (sourceWeilC0ShiftedGraphOperator i c0 y) x) = _
      rw [inner_conj_symm]

noncomputable def sourceWeilC0ShiftedOddTailOperator
    (i : PairIndex) (R : ℕ) (c0 : ℝ) :
    SourceWeilGraphOddTailCarrier i R →L[ℂ]
      SourceWeilGraphOddTailCarrier i R :=
  (sourceWeilGraphOddTail i R).orthogonalProjection.comp
    ((sourceWeilC0ShiftedGraphOperator i c0).comp
      (sourceWeilGraphOddTail i R).subtypeL)

theorem inner_sourceWeilC0ShiftedOddTailOperator
    (i : PairIndex) (R : ℕ) (c0 : ℝ)
    (x y : SourceWeilGraphOddTailCarrier i R) :
    inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) y =
      inner ℂ
        (sourceWeilC0ShiftedGraphOperator i c0
          (x : SourceWeilGraphCarrier i))
        (y : SourceWeilGraphCarrier i) := by
  exact (sourceWeilGraphOddTail i R).inner_orthogonalProjection_eq_of_mem_right
    y (sourceWeilC0ShiftedGraphOperator i c0
      (x : SourceWeilGraphCarrier i))

theorem sourceWeilC0ShiftedOddTailOperator_graph_lower
    (i : PairIndex) (R : ℕ) (mu c0 : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (hc0_nonneg : 0 ≤ c0)
    (hc0 : c0 < mu)
    (x : SourceWeilGraphOddTailCarrier i R) :
    ((mu - c0) / (sourceWeilLowerBoundConstant i + mu + 1)) * ‖x‖ ^ 2 ≤
      (inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) x).re := by
  let a := ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖ ^ 2
  let b := ‖sourceWeilGraphWeighted i (x : SourceWeilGraphCarrier i)‖ ^ 2
  let e := (inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) x).re
  let L := sourceWeilLowerBoundConstant i
  have hmu : 0 < mu := hcoercive.1
  have hL : 0 ≤ L := sourceWeilLowerBoundConstant_nonneg i
  have hden : 0 < L + mu + 1 := by linarith
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hc : 0 < (mu - c0) / (L + mu + 1) := div_pos (sub_pos.mpr hc0) hden
  have hambient : (mu - c0) * a ≤ e := by
    dsimp only [e]
    rw [inner_sourceWeilC0ShiftedOddTailOperator,
      inner_sourceWeilC0ShiftedGraphOperator_self]
    have h := hcoercive.2 x
    dsimp only [a, e]
    nlinarith
  have hweighted : b - (L + c0) * a ≤ e := by
    dsimp only [e]
    rw [inner_sourceWeilC0ShiftedOddTailOperator,
      inner_sourceWeilC0ShiftedGraphOperator_self]
    have hshift := sourceWeilShiftedOddTailOperator_weighted_lower i R x
    rw [inner_sourceWeilShiftedOddTailOperator] at hshift
    have hraw :=
      sourceWeilSesquilinearForm_self_re_eq_graph_diagonal_sub_shift
        i (x : SourceWeilGraphCarrier i)
    dsimp only [a, b, e, L] at hshift hraw ⊢
    nlinarith
  have hnorm : ‖x‖ ^ 2 = a + b := by
    simpa [a, b] using
      (sourceWeilGraph_norm_sq i (x : SourceWeilGraphCarrier i))
  rw [hnorm]
  have hconv :
      ((L + c0 + 1) / (L + mu + 1)) * ((mu - c0) * a) +
          ((mu - c0) / (L + mu + 1)) * (b - (L + c0) * a) ≤ e := by
    have hleft : 0 ≤ (L + c0 + 1) / (L + mu + 1) := by
      exact div_nonneg (by linarith) hden.le
    have hright : 0 ≤ (mu - c0) / (L + mu + 1) := hc.le
    have hsum :
        (L + c0 + 1) / (L + mu + 1) +
          (mu - c0) / (L + mu + 1) = 1 := by
      field_simp [hden.ne']
      ring
    have h1 := mul_le_mul_of_nonneg_left hambient hleft
    have h2 := mul_le_mul_of_nonneg_left hweighted hright
    calc
      ((L + c0 + 1) / (L + mu + 1)) * ((mu - c0) * a) +
          ((mu - c0) / (L + mu + 1)) * (b - (L + c0) * a) ≤
          ((L + c0 + 1) / (L + mu + 1)) * e +
            ((mu - c0) / (L + mu + 1)) * e := add_le_add h1 h2
      _ = e := by rw [← add_mul, hsum, one_mul]
  have halg :
      ((L + c0 + 1) / (L + mu + 1)) * ((mu - c0) * a) +
          ((mu - c0) / (L + mu + 1)) * (b - (L + c0) * a) =
        ((mu - c0) / (L + mu + 1)) * (a + b) := by
    field_simp [hden.ne']
    ring
  rw [halg] at hconv
  exact hconv

theorem sourceWeilC0ShiftedOddTailOperator_isPositive
    (i : PairIndex) (R : ℕ) (mu c0 : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (hc0_nonneg : 0 ≤ c0) (hc0 : c0 < mu) :
    (sourceWeilC0ShiftedOddTailOperator i R c0).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  constructor
  · rw [inner_sourceWeilC0ShiftedOddTailOperator,
      inner_sourceWeilC0ShiftedGraphOperator]
    apply Complex.ext
    · rfl
    · change 0 =
        (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
            (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i)) -
          (c0 : ℂ) *
            inner ℂ
              (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))
              (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))).im
      have him :
          (inner ℂ
            (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))
            (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))).im = 0 := by
        exact inner_self_im (𝕜 := ℂ) _
      rw [sub_im, mul_im, Complex.ofReal_re, Complex.ofReal_im,
        sourceWeilSesquilinearForm_im_self_eq_zero, him]
      ring
  · exact (sourceWeilC0ShiftedOddTailOperator_graph_lower
      i R mu c0 hcoercive hc0_nonneg hc0 x).trans'
        (mul_nonneg
          (div_nonneg (sub_nonneg.mpr hc0.le)
            (by have := sourceWeilLowerBoundConstant_nonneg i; linarith))
          (sq_nonneg ‖x‖))

set_option maxHeartbeats 1200000 in
theorem sourceWeilC0ShiftedOddTailOperator_isUnit
    (i : PairIndex) (R : ℕ) (mu c0 : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (hc0_nonneg : 0 ≤ c0) (hc0 : c0 < mu) :
    IsUnit (sourceWeilC0ShiftedOddTailOperator i R c0) := by
  let c : NNReal :=
    ⟨(mu - c0) / (sourceWeilLowerBoundConstant i + mu + 1),
      div_nonneg (sub_nonneg.mpr hc0.le)
        (by have := sourceWeilLowerBoundConstant_nonneg i; linarith)⟩
  have hcReal :
      0 < (mu - c0) / (sourceWeilLowerBoundConstant i + mu + 1) := by
    apply div_pos (sub_pos.mpr hc0)
    have := sourceWeilLowerBoundConstant_nonneg i
    linarith [hcoercive.1]
  have hc : 0 < c := by exact_mod_cast hcReal
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (sourceWeilC0ShiftedOddTailOperator i R c0) hc
  intro x
  have hgraph := sourceWeilC0ShiftedOddTailOperator_graph_lower
    i R mu c0 hcoercive hc0_nonneg hc0 x
  change ‖x‖ ^ 2 * (c : ℝ) ≤
    ‖inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) x‖
  calc
    ‖x‖ ^ 2 * (c : ℝ) =
        ((mu - c0) / (sourceWeilLowerBoundConstant i + mu + 1)) *
          ‖x‖ ^ 2 := by
      dsimp only [c]
      push_cast
      ring
    _ ≤ (inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) x).re :=
      hgraph
    _ ≤ ‖inner ℂ (sourceWeilC0ShiftedOddTailOperator i R c0 x) x‖ :=
      Complex.re_le_norm _

theorem sourceWeilC0ShiftedOddTailOperator_isInvertible
    (i : PairIndex) (R : ℕ) (mu c0 : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (hc0_nonneg : 0 ≤ c0) (hc0 : c0 < mu) :
    (sourceWeilC0ShiftedOddTailOperator i R c0).IsInvertible := by
  obtain ⟨u, hu⟩ := sourceWeilC0ShiftedOddTailOperator_isUnit
    i R mu c0 hcoercive hc0_nonneg hc0
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

/-- The pre-registered G-LOWER target floor. -/
noncomputable def sourceWeilOddTargetFloor : ℝ := 1 / (10 : ℝ) ^ 58

theorem sourceWeilOddTargetFloor_nonneg : 0 ≤ sourceWeilOddTargetFloor := by
  norm_num [sourceWeilOddTargetFloor]

theorem sourceWeilOddTargetFloor_lt_half :
    sourceWeilOddTargetFloor < (1 / 2 : ℝ) := by
  norm_num [sourceWeilOddTargetFloor]

theorem sourceWeilOddTargetFloorTail_isInvertible (i : PairIndex) :
    (sourceWeilC0ShiftedOddTailOperator i (sourceWeilOddTailCutoff i)
      sourceWeilOddTargetFloor).IsInvertible := by
  exact sourceWeilC0ShiftedOddTailOperator_isInvertible i
    (sourceWeilOddTailCutoff i) (1 / 2) sourceWeilOddTargetFloor
    (sourceWeilOddTailAmbientCoercive_explicit i)
    sourceWeilOddTargetFloor_nonneg sourceWeilOddTargetFloor_lt_half

theorem sourceWeilOddTargetFloorTail_isPositive (i : PairIndex) :
    (sourceWeilC0ShiftedOddTailOperator i (sourceWeilOddTailCutoff i)
      sourceWeilOddTargetFloor).IsPositive := by
  exact sourceWeilC0ShiftedOddTailOperator_isPositive i
    (sourceWeilOddTailCutoff i) (1 / 2) sourceWeilOddTargetFloor
    (sourceWeilOddTailAmbientCoercive_explicit i)
    sourceWeilOddTargetFloor_nonneg sourceWeilOddTargetFloor_lt_half

noncomputable def sourceWeilOddTargetFloorResidual
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i) :=
  (sourceWeilGraphOddTail i (sourceWeilOddTailCutoff i)).orthogonalProjection.comp
    ((sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor).comp
      (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i)))

theorem inner_sourceWeilOddTargetFloorResidual
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) :
    inner ℂ (sourceWeilOddTargetFloorResidual i q) y =
      inner ℂ
        (sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor
          (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i) q))
        (y : SourceWeilGraphCarrier i) := by
  exact (sourceWeilGraphOddTail i
    (sourceWeilOddTailCutoff i)).inner_orthogonalProjection_eq_of_mem_right
      y (sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor
        (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i) q))

noncomputable def sourceWeilOddTargetFloorInverseWeightedData
    (i : PairIndex) :
    OddTailInverseWeightedData
      (SourceWeilOddHeadCoefficients i)
      (SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) where
  outerBlock := sourceWeilC0ShiftedOddTailOperator i
    (sourceWeilOddTailCutoff i) sourceWeilOddTargetFloor
  residual := sourceWeilOddTargetFloorResidual i
  outerBlock_positive := sourceWeilOddTargetFloorTail_isPositive i
  outerBlock_invertible := sourceWeilOddTargetFloorTail_isInvertible i

noncomputable def sourceWeilOddTargetFloorHeadOperator
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilOddHeadCoefficients i :=
  (sourceWeilGraphOddHeadSynthesis i
      (sourceWeilOddTailCutoff i)).adjoint.comp
    ((sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor).comp
      (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i)))

theorem inner_sourceWeilOddTargetFloorHeadOperator
    (i : PairIndex) (q r : SourceWeilOddHeadCoefficients i) :
    inner ℂ (sourceWeilOddTargetFloorHeadOperator i q) r =
      inner ℂ
        (sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor
          (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i) q))
        (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i) r) := by
  rw [sourceWeilOddTargetFloorHeadOperator]
  simp only [ContinuousLinearMap.comp_apply]
  exact ContinuousLinearMap.adjoint_inner_left _ _ _

noncomputable def sourceWeilOddTargetFloorSchurComplement
    (i : PairIndex) :
    SourceWeilOddHeadCoefficients i →L[ℂ]
      SourceWeilOddHeadCoefficients i :=
  oddTailSchurComplement
    (sourceWeilOddTargetFloorHeadOperator i)
    (sourceWeilOddTargetFloorInverseWeightedData i)

theorem sourceWeilOddTargetFloorHeadOperator_eq_schur_add_correction
    (i : PairIndex) :
    sourceWeilOddTargetFloorHeadOperator i =
      sourceWeilOddTargetFloorSchurComplement i +
        oddTailInverseWeightedCorrection
          (sourceWeilOddTargetFloorInverseWeightedData i) := by
  exact operator_eq_oddTailSchurComplement_add_correction
    (sourceWeilOddTargetFloorHeadOperator i)
    (sourceWeilOddTargetFloorInverseWeightedData i)

private theorem re_inner_map_add_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (x y : E) :
    (inner ℂ (A (x + y)) (x + y)).re =
      (inner ℂ (A x) x).re + (inner ℂ (A x) y).re +
        (inner ℂ (A y) x).re + (inner ℂ (A y) y).re := by
  rw [map_add, inner_add_left, inner_add_right, inner_add_right]
  simp only [add_re]
  ring

noncomputable def sourceWeilOddTargetFloorCorrector
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i) :
    SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i) :=
  (sourceWeilC0ShiftedOddTailOperator i (sourceWeilOddTailCutoff i)
      sourceWeilOddTargetFloor).inverse
    (sourceWeilOddTargetFloorResidual i q)

noncomputable def sourceWeilOddTargetFloorBlockVector
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) :
    SourceWeilGraphCarrier i :=
  sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i) q +
    (sourceWeilGraphOddTail i (sourceWeilOddTailCutoff i)).subtypeL y

private theorem re_inner_block_completion
    {Head Tail Ambient : Type*}
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
    [NormedAddCommGroup Tail] [InnerProductSpace ℂ Tail] [CompleteSpace Tail]
    [NormedAddCommGroup Ambient] [InnerProductSpace ℂ Ambient]
    (A : Ambient →L[ℂ] Ambient) (S : Head →L[ℂ] Ambient)
    (U : Tail →L[ℂ] Ambient) (H : Head →L[ℂ] Head)
    (D : OddTailInverseWeightedData Head Tail)
    (hA : A.IsSymmetric)
    (hhead : ∀ q, inner ℂ (H q) q = inner ℂ (A (S q)) (S q))
    (hres : ∀ q y, inner ℂ (D.residual q) y = inner ℂ (A (S q)) (U y))
    (htail : ∀ y, inner ℂ (A (U y)) (U y) = inner ℂ (D.outerBlock y) y)
    (q : Head) (y : Tail) :
    let v := D.outerBlock.inverse (D.residual q)
    (inner ℂ (A (S q + U y)) (S q + U y)).re =
      (inner ℂ
        (oddTailSchurComplement H D q) q).re +
      (inner ℂ (D.outerBlock (y + v)) (y + v)).re := by
  dsimp only
  let C := D.outerBlock
  let R := D.residual
  let v := C.inverse (R q)
  have hinv : C v = R q := outerBlock_apply_inverse_residual D q
  have hhead :
      (inner ℂ (A (S q)) (S q)).re =
        (inner ℂ (H q) q).re := congrArg Complex.re (hhead q).symm
  have hres' :
      (inner ℂ (A (S q)) (U y)).re = (inner ℂ (R q) y).re :=
    congrArg Complex.re (hres q y).symm
  have hresSymm :
      (inner ℂ (A (U y)) (S q)).re = (inner ℂ (R q) y).re := by
    calc
      (inner ℂ (A (U y)) (S q)).re = (inner ℂ (U y) (A (S q))).re :=
        congrArg Complex.re (hA (U y) (S q))
      _ = (inner ℂ (A (S q)) (U y)).re :=
        inner_re_symm (𝕜 := ℂ) (E := Ambient) _ _
      _ = (inner ℂ (R q) y).re := hres'
  have htail' :
      (inner ℂ (A (U y)) (U y)).re = (inner ℂ (C y) y).re :=
    congrArg Complex.re (htail y)
  have hcorr :
      (inner ℂ (oddTailInverseWeightedCorrection D q) q).re =
        (inner ℂ (C v) v).re := by
    calc
      (inner ℂ (oddTailInverseWeightedCorrection D q) q).re =
          (inner ℂ v (R q)).re :=
        congrArg Complex.re (inner_oddTailInverseWeightedCorrection D q q)
      _ = (inner ℂ v (C v)).re := by rw [hinv]
      _ = (inner ℂ (C v) v).re :=
        inner_re_symm (𝕜 := ℂ) (E := Tail) _ _
  have hCv : (inner ℂ (C v) y).re = (inner ℂ (R q) y).re :=
    congrArg (fun z => (inner ℂ z y).re) hinv
  have hCy : (inner ℂ (C y) v).re = (inner ℂ (R q) y).re := by
    calc
      (inner ℂ (C y) v).re = (inner ℂ y (C v)).re :=
        congrArg Complex.re (D.outerBlock_positive.isSymmetric y v)
      _ = (inner ℂ (C v) y).re :=
        inner_re_symm (𝕜 := ℂ) (E := Tail) _ _
      _ = (inner ℂ (R q) y).re := hCv
  rw [re_inner_map_add_self A (S q) (U y)]
  rw [re_inner_map_add_self C y v]
  rw [hhead, hres', hresSymm, htail', hCy, hCv]
  simp only [oddTailSchurComplement, ContinuousLinearMap.sub_apply,
    inner_sub_left, sub_re]
  rw [hcorr]
  ring

noncomputable def sourceWeilOddTargetFloorBlockEnergy
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) : ℝ :=
  (inner ℂ
    (sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor
      (sourceWeilOddTargetFloorBlockVector i q y))
    (sourceWeilOddTargetFloorBlockVector i q y)).re

noncomputable def sourceWeilOddTargetFloorSchurEnergy
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i) : ℝ :=
  (inner ℂ (sourceWeilOddTargetFloorSchurComplement i q) q).re

noncomputable def sourceWeilOddTargetFloorCompletedTailEnergy
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) : ℝ :=
  (inner ℂ
    (sourceWeilC0ShiftedOddTailOperator i (sourceWeilOddTailCutoff i)
      sourceWeilOddTargetFloor (y + sourceWeilOddTargetFloorCorrector i q))
    (y + sourceWeilOddTargetFloorCorrector i q)).re

set_option maxHeartbeats 3000000 in
/-- Exact completion of the square for the target-floor source block.  The
only remaining sign is the finite exact Schur complement. -/
theorem sourceWeilOddTargetFloor_block_completion
    (i : PairIndex) (q : SourceWeilOddHeadCoefficients i)
    (y : SourceWeilGraphOddTailCarrier i (sourceWeilOddTailCutoff i)) :
    sourceWeilOddTargetFloorBlockEnergy i q y =
      sourceWeilOddTargetFloorSchurEnergy i q +
        sourceWeilOddTargetFloorCompletedTailEnergy i q y := by
  unfold sourceWeilOddTargetFloorBlockEnergy
  unfold sourceWeilOddTargetFloorSchurEnergy
  unfold sourceWeilOddTargetFloorCompletedTailEnergy
  unfold sourceWeilOddTargetFloorBlockVector
  unfold sourceWeilOddTargetFloorCorrector
  unfold sourceWeilOddTargetFloorSchurComplement
  apply re_inner_block_completion
    (sourceWeilC0ShiftedGraphOperator i sourceWeilOddTargetFloor)
    (sourceWeilGraphOddHeadSynthesis i (sourceWeilOddTailCutoff i))
    (sourceWeilGraphOddTail i (sourceWeilOddTailCutoff i)).subtypeL
    (sourceWeilOddTargetFloorHeadOperator i)
    (sourceWeilOddTargetFloorInverseWeightedData i)
    (sourceWeilC0ShiftedGraphOperator_isSymmetric i sourceWeilOddTargetFloor)
  · intro q'
    exact inner_sourceWeilOddTargetFloorHeadOperator i q' q'
  · intro q' y'
    exact inner_sourceWeilOddTargetFloorResidual i q' y'
  · intro y'
    exact (inner_sourceWeilC0ShiftedOddTailOperator i
      (sourceWeilOddTailCutoff i) sourceWeilOddTargetFloor y' y').symm

#print axioms sourceWeilC0ShiftedGraphOperator
#print axioms inner_sourceWeilC0ShiftedGraphOperator
#print axioms sourceWeilC0ShiftedOddTailOperator_graph_lower
#print axioms sourceWeilC0ShiftedOddTailOperator_isPositive
#print axioms sourceWeilC0ShiftedOddTailOperator_isInvertible
#print axioms sourceWeilOddTargetFloorTail_isInvertible
#print axioms sourceWeilOddTargetFloorResidual
#print axioms sourceWeilOddTargetFloorInverseWeightedData
#print axioms sourceWeilOddTargetFloorSchurComplement
#print axioms sourceWeilOddTargetFloor_block_completion

end Q3.RouteB.D0Pstar
