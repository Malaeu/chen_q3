import Q3.Proofs.RouteB.D0PstarSourceWeilFormCoreTopology
import Q3.Proofs.RouteB.D0PstarOddTailInverseWeightedCorrection
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.ProdL2

set_option linter.mathlibStandardSet false

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate NNReal

namespace Q3.RouteB.D0Pstar

/-!
# Literal source-Weil odd-tail graph operator

This file transports the exact closed graph of the shifted square-root-weight
map to the Hilbert `L²` product, constructs the literal closed span of the
normalized infinite odd tail, and compresses the complete shifted source-Weil
Riesz operator to that tail.

The unshifted source-Weil tail coercivity remains an explicit source theorem.
From that exact Yoshida-style ambient estimate, the file proves a graph-norm
lower bound and continuous invertibility of the compressed outer block, then
instantiates the B3.0AI `R† C⁻¹ R` interface for any separately supplied
bounded residual. No finite-section floor is promoted to an infinite result.
-/

/-- The exact closed graph transported to the Hilbert `L²` product rather
than the max-norm plain product used by `LinearPMap.graph`. -/
noncomputable def sourceWeilGraphSubmodule (i : PairIndex) :
    Submodule ℂ
      (WithLp 2
        (H_m i × MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))) :=
  (sourceArchimedeanShiftedWeightedLpPMap i).graph.comap
    (WithLp.prodContinuousLinearEquiv 2 ℂ (H_m i)
      (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))).toLinearMap

abbrev SourceWeilGraphCarrier (i : PairIndex) :=
  sourceWeilGraphSubmodule i

theorem sourceWeilGraphSubmodule_isClosed (i : PairIndex) :
    IsClosed (sourceWeilGraphSubmodule i : Set
      (WithLp 2
        (H_m i × MeasureTheory.Lp ℂ 2 (volume : Measure ℝ)))) := by
  exact (sourceArchimedeanShiftedWeightedLpPMap_isClosed i).preimage
    (WithLp.prodContinuousLinearEquiv 2 ℂ (H_m i)
      (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))).continuous

noncomputable instance sourceWeilGraphCarrierCompleteSpace (i : PairIndex) :
    CompleteSpace (SourceWeilGraphCarrier i) :=
  (sourceWeilGraphSubmodule_isClosed i).completeSpace_coe

noncomputable def sourceWeilGraphAmbient
    (i : PairIndex) : SourceWeilGraphCarrier i →L[ℂ] H_m i :=
  (WithLp.fstL (p := 2) (𝕜 := ℂ) (H_m i)
    (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))).comp
    ((sourceWeilGraphSubmodule i).subtypeL)

noncomputable def sourceWeilGraphWeighted
    (i : PairIndex) : SourceWeilGraphCarrier i →L[ℂ]
      MeasureTheory.Lp ℂ 2 (volume : Measure ℝ) :=
  (WithLp.sndL (p := 2) (𝕜 := ℂ) (H_m i)
    (MeasureTheory.Lp ℂ 2 (volume : Measure ℝ))).comp
    ((sourceWeilGraphSubmodule i).subtypeL)

@[simp] theorem sourceWeilGraphAmbient_apply
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    sourceWeilGraphAmbient i x = x.1.fst := by
  rfl

@[simp] theorem sourceWeilGraphWeighted_apply
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    sourceWeilGraphWeighted i x = x.1.snd := by
  rfl

theorem sourceWeilGraph_pair_mem
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    (sourceWeilGraphAmbient i x, sourceWeilGraphWeighted i x) ∈
      (sourceArchimedeanShiftedWeightedLpPMap i).graph := by
  exact x.2

theorem sourceWeilGraphAmbient_mem_domain
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    sourceWeilGraphAmbient i x ∈
      (sourceArchimedeanShiftedWeightedLpPMap i).domain := by
  obtain ⟨y, hy, _⟩ :=
    (LinearPMap.mem_graph_iff
      (sourceArchimedeanShiftedWeightedLpPMap i)).mp
      (sourceWeilGraph_pair_mem i x)
  have hy' : (y : H_m i) = sourceWeilGraphAmbient i x := by
    simpa only [Prod.fst] using hy
  rw [← hy']
  exact y.2

noncomputable def sourceWeilGraphDomain
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    sourceArchimedeanShiftedFormDomain i :=
  ⟨sourceWeilGraphAmbient i x, sourceWeilGraphAmbient_mem_domain i x⟩

@[simp] theorem sourceWeilGraphDomain_coe
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    (sourceWeilGraphDomain i x : H_m i) = sourceWeilGraphAmbient i x := rfl

theorem sourceWeilGraphWeighted_eq
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    sourceWeilGraphWeighted i x =
      sourceArchimedeanShiftedWeightedLpLinearMap i
        (sourceWeilGraphDomain i x) := by
  obtain ⟨y, hy, hout⟩ :=
    (LinearPMap.mem_graph_iff
      (sourceArchimedeanShiftedWeightedLpPMap i)).mp
      (sourceWeilGraph_pair_mem i x)
  have hy' : (y : H_m i) = sourceWeilGraphAmbient i x := by
    simpa only [Prod.fst] using hy
  have hout' : sourceArchimedeanShiftedWeightedLpPMap i y =
      sourceWeilGraphWeighted i x := by
    simpa only [Prod.snd] using hout
  rw [← hout', sourceArchimedeanShiftedWeightedLpPMap_apply]
  apply congrArg (sourceArchimedeanShiftedWeightedLpLinearMap i)
  exact Subtype.ext hy'

noncomputable def sourceW02AmbientRieszOperator
    (i : PairIndex) : H_m i →L[ℂ] H_m i :=
  InnerProductSpace.continuousLinearMapOfBilin
    (sourceW02AmbientContinuousSesquilinearForm i)

noncomputable def sourcePrimeAmbientRieszOperator
    (i : PairIndex) : H_m i →L[ℂ] H_m i :=
  InnerProductSpace.continuousLinearMapOfBilin
    (sourcePrimeContinuousSesquilinearForm i)

noncomputable def sourceWeilBoundedShiftRieszOperator
    (i : PairIndex) : H_m i →L[ℂ] H_m i :=
  sourceW02AmbientRieszOperator i - sourcePrimeAmbientRieszOperator i +
    ((‖sourceW02AmbientContinuousSesquilinearForm i‖ +
        ‖sourcePrimeContinuousSesquilinearForm i‖ : ℝ) : ℂ) •
      ContinuousLinearMap.id ℂ (H_m i)

/-- The exact bounded Riesz operator of the shifted source-Weil form on the
closed graph Hilbert carrier. -/
noncomputable def sourceWeilShiftedGraphOperator
    (i : PairIndex) :
    SourceWeilGraphCarrier i →L[ℂ] SourceWeilGraphCarrier i :=
  (sourceWeilGraphWeighted i).adjoint.comp (sourceWeilGraphWeighted i) +
    (sourceWeilGraphAmbient i).adjoint.comp
      ((sourceWeilBoundedShiftRieszOperator i).comp
        (sourceWeilGraphAmbient i))

set_option maxHeartbeats 800000 in
theorem inner_sourceWeilShiftedGraphOperator
    (i : PairIndex) (x y : SourceWeilGraphCarrier i) :
    inner ℂ (sourceWeilShiftedGraphOperator i x) y =
      inner ℂ (sourceWeilGraphWeighted i x)
        (sourceWeilGraphWeighted i y) +
      sourceW02AmbientContinuousSesquilinearForm i
        (sourceWeilGraphAmbient i x) (sourceWeilGraphAmbient i y) -
      sourcePrimeContinuousSesquilinearForm i
        (sourceWeilGraphAmbient i x) (sourceWeilGraphAmbient i y) +
      ((‖sourceW02AmbientContinuousSesquilinearForm i‖ +
          ‖sourcePrimeContinuousSesquilinearForm i‖ : ℝ) : ℂ) *
        inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i y) := by
  rw [sourceWeilShiftedGraphOperator, ContinuousLinearMap.add_apply,
    inner_add_left]
  simp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_left,
    ContinuousLinearMap.adjoint_inner_left]
  rw [sourceWeilBoundedShiftRieszOperator,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    inner_add_left, inner_sub_left]
  simp only [sourceW02AmbientRieszOperator,
    sourcePrimeAmbientRieszOperator,
    InnerProductSpace.continuousLinearMapOfBilin_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.id_apply, inner_smul_left,
    Complex.conj_ofReal]
  ring

set_option maxHeartbeats 800000 in
theorem inner_sourceWeilShiftedGraphOperator_eq_source
    (i : PairIndex) (x y : SourceWeilGraphCarrier i) :
    inner ℂ (sourceWeilShiftedGraphOperator i x) y =
      sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i y) +
      (sourceWeilLowerBoundConstant i : ℂ) *
        inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i y) := by
  rw [inner_sourceWeilShiftedGraphOperator]
  rw [sourceWeilSesquilinearForm_apply,
    sourceArchPrimeSesquilinearForm_apply,
    sourceArchimedeanSesquilinearForm_apply,
    sourceArchimedeanShiftedSesquilinearForm_apply,
    sourcePrimeContinuousSesquilinearForm_apply]
  rw [← sourceWeilGraphWeighted_eq i x,
    ← sourceWeilGraphWeighted_eq i y]
  have hinnerDomain :
      inner ℂ (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i y) =
        inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i y) := rfl
  rw [hinnerDomain]
  simp only [sourceWeilGraphDomain_coe, coe_innerₛₗ_apply]
  dsimp only [sourceWeilLowerBoundConstant]
  push_cast
  ring

theorem inner_sourceWeilShiftedGraphOperator_self_eq_energy
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    inner ℂ (sourceWeilShiftedGraphOperator i x) x =
      ((sourceWeilShiftedExtendedQuadraticForm i
        (sourceWeilGraphAmbient i x)).toReal : ℂ) := by
  have henergy :=
    sourceWeilShiftedExtendedQuadraticForm_toReal_eq_re_add_shift
      i (sourceWeilGraphDomain i x)
  rw [inner_sourceWeilShiftedGraphOperator_eq_source]
  apply Complex.ext
  · have hinnerRe :
        (inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i x)).re =
            ‖sourceWeilGraphAmbient i x‖ ^ 2 :=
      by simpa using
        (inner_self_eq_norm_sq (𝕜 := ℂ) (sourceWeilGraphAmbient i x))
    simpa only [add_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, sourceWeilGraphDomain_coe, hinnerRe] using henergy.symm
  · simp only [add_im, mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.ofReal_im]
    rw [sourceWeilSesquilinearForm_im_self_eq_zero]
    have him :
        (inner ℂ (sourceWeilGraphAmbient i x)
          (sourceWeilGraphAmbient i x)).im = 0 := by
      exact inner_self_im (𝕜 := ℂ) (sourceWeilGraphAmbient i x)
    rw [him]
    ring

theorem sourceWeilShiftedGraphOperator_isPositive
    (i : PairIndex) :
    (sourceWeilShiftedGraphOperator i).IsPositive := by
  rw [ContinuousLinearMap.isPositive_iff_complex]
  intro x
  rw [inner_sourceWeilShiftedGraphOperator_self_eq_energy]
  constructor
  · simp
  · exact ENNReal.toReal_nonneg

/-- The exact graph lift of a vector in the maximal shifted source domain. -/
noncomputable def sourceWeilGraphLift
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    SourceWeilGraphCarrier i :=
  ⟨WithLp.toLp 2
      ((x : H_m i), sourceArchimedeanShiftedWeightedLpLinearMap i x),
    (sourceArchimedeanShiftedWeightedLpPMap i).mem_graph x⟩

@[simp] theorem sourceWeilGraphAmbient_lift
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    sourceWeilGraphAmbient i (sourceWeilGraphLift i x) = x := by
  rfl

@[simp] theorem sourceWeilGraphWeighted_lift
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    sourceWeilGraphWeighted i (sourceWeilGraphLift i x) =
      sourceArchimedeanShiftedWeightedLpLinearMap i x := by
  rfl

/-- A literal normalized odd graph mode.  The public index `n : ℕ` denotes
the physical pair `±(n+1)`, so the zero mode is absent by construction. -/
noncomputable def sourceWeilGraphOddMode
    (i : PairIndex) (n : ℕ) : SourceWeilGraphCarrier i :=
  ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
    (sourceWeilGraphLift i
        (sourceArchimedeanModeInShiftedFormDomain i (n + 1 : ℕ)) -
      sourceWeilGraphLift i
        (sourceArchimedeanModeInShiftedFormDomain i (-((n + 1 : ℕ) : ℤ))))

/-- The literal infinite source odd tail after cutoff `R`: the closed span of
physical odd pairs `±(R+1), ±(R+2), ...` inside the exact graph Hilbert carrier. -/
noncomputable def sourceWeilGraphOddTail
    (i : PairIndex) (R : ℕ) : Submodule ℂ (SourceWeilGraphCarrier i) :=
  (Submodule.span ℂ
    (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k)))).topologicalClosure

abbrev SourceWeilGraphOddTailCarrier (i : PairIndex) (R : ℕ) :=
  sourceWeilGraphOddTail i R

noncomputable instance sourceWeilGraphOddTailCompleteSpace
    (i : PairIndex) (R : ℕ) :
    CompleteSpace (SourceWeilGraphOddTailCarrier i R) :=
  (Submodule.isClosed_topologicalClosure
    (Submodule.span ℂ
      (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k))))).completeSpace_coe

instance sourceWeilGraphOddTailInnerProductSpace
    (i : PairIndex) (R : ℕ) :
    InnerProductSpace ℂ (SourceWeilGraphOddTailCarrier i R) :=
  Submodule.innerProductSpace (sourceWeilGraphOddTail i R)

noncomputable instance sourceWeilGraphOddTailHasOrthogonalProjection
    (i : PairIndex) (R : ℕ) :
    (sourceWeilGraphOddTail i R).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace
    (sourceWeilGraphOddTail i R)

/-- The exact source-Weil shifted outer block compressed to the literal closed
odd tail. -/
noncomputable def sourceWeilShiftedOddTailOperator
    (i : PairIndex) (R : ℕ) :
    SourceWeilGraphOddTailCarrier i R →L[ℂ]
      SourceWeilGraphOddTailCarrier i R :=
  (sourceWeilGraphOddTail i R).orthogonalProjection.comp
    ((sourceWeilShiftedGraphOperator i).comp
      (sourceWeilGraphOddTail i R).subtypeL)

set_option synthInstance.maxHeartbeats 200000 in
theorem inner_sourceWeilShiftedOddTailOperator
    (i : PairIndex) (R : ℕ)
    (x y : SourceWeilGraphOddTailCarrier i R) :
    inner ℂ (sourceWeilShiftedOddTailOperator i R x) y =
      inner ℂ (sourceWeilShiftedGraphOperator i (x : SourceWeilGraphCarrier i))
        (y : SourceWeilGraphCarrier i) := by
  exact (sourceWeilGraphOddTail i R).inner_orthogonalProjection_eq_of_mem_right
    y (sourceWeilShiftedGraphOperator i (x : SourceWeilGraphCarrier i))

set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_isPositive
    (i : PairIndex) (R : ℕ) :
    ContinuousLinearMap.IsPositive (𝕜 := ℂ)
      (sourceWeilShiftedOddTailOperator i R) := by
  exact (sourceWeilShiftedGraphOperator_isPositive i).orthogonalProjection_comp
    (sourceWeilGraphOddTail i R)

/-- The exact source input still missing from the project: a uniform positive
lower bound for the unshifted source-Weil form on the literal infinite odd
tail.  This is the Yoshida-style ambient `L²` estimate, not a graph-norm
restatement and not a finite-section floor. -/
def SourceWeilOddTailAmbientCoercive
    (i : PairIndex) (R : ℕ) (mu : ℝ) : Prop :=
  0 < mu ∧
    ∀ x : SourceWeilGraphOddTailCarrier i R,
      mu * ‖sourceWeilGraphAmbient i
          (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
        (sourceWeilSesquilinearForm i
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))).re

theorem sourceWeilGraph_norm_sq
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    ‖x‖ ^ 2 =
      ‖sourceWeilGraphAmbient i x‖ ^ 2 +
        ‖sourceWeilGraphWeighted i x‖ ^ 2 := by
  exact WithLp.prod_norm_sq_eq_of_L2 x.1

set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_ambient_lower
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (x : SourceWeilGraphOddTailCarrier i R) :
    mu * ‖sourceWeilGraphAmbient i
        (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
      (inner ℂ (sourceWeilShiftedOddTailOperator i R x) x).re := by
  rw [inner_sourceWeilShiftedOddTailOperator,
    inner_sourceWeilShiftedGraphOperator_eq_source]
  have hinner :
      (inner ℂ (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))
        (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))).re =
          ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ)
        (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)))
  simp only [add_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  rw [hinner]
  exact (hcoercive.2 x).trans
    (le_add_of_nonneg_right
      (mul_nonneg (sourceWeilLowerBoundConstant_nonneg i)
        (sq_nonneg ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖)))

set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_weighted_lower
    (i : PairIndex) (R : ℕ)
    (x : SourceWeilGraphOddTailCarrier i R) :
    ‖sourceWeilGraphWeighted i (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
      (inner ℂ (sourceWeilShiftedOddTailOperator i R x) x).re := by
  rw [inner_sourceWeilShiftedOddTailOperator,
    inner_sourceWeilShiftedGraphOperator_self_eq_energy]
  simp only [Complex.ofReal_re]
  have hdecomp :=
    sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add
      i (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
  rw [← sourceWeilGraphWeighted_eq i (x : SourceWeilGraphCarrier i)] at hdecomp
  calc
    ‖sourceWeilGraphWeighted i (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
        ‖sourceWeilGraphWeighted i (x : SourceWeilGraphCarrier i)‖ ^ 2 +
          sourceWeilBoundedShiftedDiagonal i
            (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)) :=
      le_add_of_nonneg_right
        (sourceWeilBoundedShiftedDiagonal_nonneg i
          (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)))
    _ = (sourceWeilShiftedExtendedQuadraticForm i
        (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i))).toReal := by
      simpa only [sourceWeilGraphDomain_coe] using hdecomp.symm

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_graph_lower
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (x : SourceWeilGraphOddTailCarrier i R) :
    (min mu 1 / 2) * ‖x‖ ^ 2 ≤
      (inner ℂ (sourceWeilShiftedOddTailOperator i R x) x).re := by
  let a := ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖ ^ 2
  let b := ‖sourceWeilGraphWeighted i (x : SourceWeilGraphCarrier i)‖ ^ 2
  let e := (inner ℂ (sourceWeilShiftedOddTailOperator i R x) x).re
  have hambient : mu * a ≤ e := by
    exact sourceWeilShiftedOddTailOperator_ambient_lower i R mu hcoercive x
  have hweighted : b ≤ e := by
    exact sourceWeilShiftedOddTailOperator_weighted_lower i R x
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  have hmin_nonneg : 0 ≤ min mu 1 :=
    le_min hcoercive.1.le (by norm_num)
  have hmin_mu : min mu 1 ≤ mu := min_le_left _ _
  have hmin_one : min mu 1 ≤ 1 := min_le_right _ _
  have hma : min mu 1 * a ≤ mu * a :=
    mul_le_mul_of_nonneg_right hmin_mu ha
  have hmb : min mu 1 * b ≤ b := by
    have := mul_le_mul_of_nonneg_right hmin_one hb
    simpa using this
  have hnorm : ‖x‖ ^ 2 = a + b := by
    simpa [a, b] using
      (sourceWeilGraph_norm_sq i (x : SourceWeilGraphCarrier i))
  rw [hnorm]
  nlinarith

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_isUnit
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu) :
    IsUnit (sourceWeilShiftedOddTailOperator i R) := by
  let c : ℝ≥0 :=
    ⟨min mu 1 / 2,
      div_nonneg (le_min hcoercive.1.le (by norm_num)) (by norm_num)⟩
  have hcReal : 0 < min mu 1 / 2 := by
    exact div_pos (lt_min hcoercive.1 (by norm_num)) (by norm_num)
  have hc : 0 < c := by
    exact_mod_cast hcReal
  apply ContinuousLinearMap.isUnit_of_forall_le_norm_inner_map
    (sourceWeilShiftedOddTailOperator i R) hc
  intro x
  have hgraph :=
    sourceWeilShiftedOddTailOperator_graph_lower i R mu hcoercive x
  change ‖x‖ ^ 2 * (c : ℝ) ≤
    ‖inner ℂ (sourceWeilShiftedOddTailOperator i R x) x‖
  calc
    ‖x‖ ^ 2 * (c : ℝ) = (min mu 1 / 2) * ‖x‖ ^ 2 := by
      change ‖x‖ ^ 2 * (min mu 1 / 2) = (min mu 1 / 2) * ‖x‖ ^ 2
      ring
    _ ≤ (inner ℂ (sourceWeilShiftedOddTailOperator i R x) x).re := hgraph
    _ ≤ ‖inner ℂ (sourceWeilShiftedOddTailOperator i R x) x‖ :=
      Complex.re_le_norm _

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem sourceWeilShiftedOddTailOperator_isInvertible
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu) :
    (sourceWeilShiftedOddTailOperator i R).IsInvertible := by
  obtain ⟨u, hu⟩ :=
    sourceWeilShiftedOddTailOperator_isUnit i R mu hcoercive
  exact ⟨ContinuousLinearEquiv.ofUnit u, hu⟩

/-- The literal source outer block now instantiates the exact B3.0AI
`R† C⁻¹ R` interface.  The residual remains an explicit independent source
supplier; it is not manufactured from finite sections or a beta envelope. -/
noncomputable def sourceWeilOddTailInverseWeightedData
    {Head : Type*}
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (residual : Head →L[ℂ] SourceWeilGraphOddTailCarrier i R) :
    OddTailInverseWeightedData Head (SourceWeilGraphOddTailCarrier i R) where
  outerBlock := sourceWeilShiftedOddTailOperator i R
  residual := residual
  outerBlock_positive := sourceWeilShiftedOddTailOperator_isPositive i R
  outerBlock_invertible :=
    sourceWeilShiftedOddTailOperator_isInvertible i R mu hcoercive

@[simp] theorem sourceWeilOddTailInverseWeightedData_outerBlock
    {Head : Type*}
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (residual : Head →L[ℂ] SourceWeilGraphOddTailCarrier i R) :
    (sourceWeilOddTailInverseWeightedData i R mu hcoercive residual).outerBlock =
      sourceWeilShiftedOddTailOperator i R := rfl

@[simp] theorem sourceWeilOddTailInverseWeightedData_residual
    {Head : Type*}
    [NormedAddCommGroup Head] [InnerProductSpace ℂ Head] [CompleteSpace Head]
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (hcoercive : SourceWeilOddTailAmbientCoercive i R mu)
    (residual : Head →L[ℂ] SourceWeilGraphOddTailCarrier i R) :
    (sourceWeilOddTailInverseWeightedData i R mu hcoercive residual).residual =
      residual := rfl

#print axioms sourceWeilGraphSubmodule_isClosed
#print axioms sourceWeilShiftedGraphOperator_isPositive
#print axioms sourceWeilShiftedOddTailOperator_isPositive
#print axioms sourceWeilShiftedOddTailOperator_graph_lower
#print axioms sourceWeilShiftedOddTailOperator_isInvertible
#print axioms sourceWeilOddTailInverseWeightedData
#print axioms sourceWeilOddTailInverseWeightedData_outerBlock

end Q3.RouteB.D0Pstar
