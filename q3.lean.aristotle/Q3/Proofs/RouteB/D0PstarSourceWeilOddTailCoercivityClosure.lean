import Q3.Proofs.RouteB.D0PstarSourceWeilOddTailGraphOperator

set_option linter.mathlibStandardSet false

noncomputable section

open Complex MeasureTheory
open scoped ComplexConjugate NNReal

namespace Q3.RouteB.D0Pstar

/-!
# Source-Weil odd-tail coercivity: algebraic span to graph closure

The literal tail in B3.0AJ is a topological closure in the shifted source-Weil
graph norm.  This file proves the exact closure-transport seam: it is enough to
establish the unshifted ambient coercivity estimate on the algebraic span of
the high odd graph modes.  The transport is legal because the raw source-Weil
diagonal is the difference of two continuous graph-topology quadratic maps,
using the already constructed bounded shifted graph operator.

No cutoff or positive constant is manufactured here.  Those remain the
source-locked Yoshida/Suzuki input.
-/

/-- The source theorem reduced to finite linear combinations of the literal
high odd graph modes.  This is still an explicit source input: in particular,
the definition does not choose `R` or `mu`. -/
def SourceWeilOddTailAlgebraicCoercive
    (i : PairIndex) (R : ℕ) (mu : ℝ) : Prop :=
  0 < mu ∧
    ∀ x : SourceWeilGraphCarrier i,
      x ∈ Submodule.span ℂ
          (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k))) →
        mu * ‖sourceWeilGraphAmbient i x‖ ^ 2 ≤
          (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i x)).re

/-- The ambient component of a literal odd graph mode is exactly the
normalized antisymmetric pair of the pre-existing source Fourier modes. -/
@[simp]
theorem sourceWeilGraphAmbient_oddMode
    (i : PairIndex) (n : ℕ) :
    sourceWeilGraphAmbient i (sourceWeilGraphOddMode i n) =
      ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ •
        (V_n_m i (n + 1 : ℕ) - V_n_m i (-((n + 1 : ℕ) : ℤ))) := by
  rw [sourceWeilGraphOddMode, map_smul, map_sub,
    sourceWeilGraphAmbient_lift, sourceWeilGraphAmbient_lift]
  rfl

/-- Every algebraic high-odd combination has zero production Fourier
coefficient in every mode with `|n| ≤ R`.  This is the exact coefficient-side
condition needed before importing Yoshida's centered-window `K_N(a)` theorem;
the centered/un-centered phase crosswalk remains a separate source step. -/
theorem sourceWeilGraphOddTailAlgebraic_low_fourier_vanish
    (i : PairIndex) (R : ℕ) (x : SourceWeilGraphCarrier i)
    (hx : x ∈ Submodule.span ℂ
      (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k))))
    (n : ℤ) (hn : n.natAbs ≤ R) :
    inner ℂ (V_n_m i n) (sourceWeilGraphAmbient i x) = 0 := by
  refine Submodule.span_induction
    (p := fun y _ => inner ℂ (V_n_m i n) (sourceWeilGraphAmbient i y) = 0)
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    rcases hy with ⟨k, rfl⟩
    have hpos : n ≠ (((R + k + 1 : ℕ) : ℤ)) := by
      intro hEq
      have habs : n.natAbs = R + k + 1 :=
        (congrArg Int.natAbs hEq).trans
          (Int.natAbs_natCast (R + k + 1))
      omega
    have hneg : n ≠ -(((R + k + 1 : ℕ) : ℤ)) := by
      intro hEq
      have habs : n.natAbs = R + k + 1 :=
        (congrArg Int.natAbs hEq).trans
          ((Int.natAbs_neg (((R + k + 1 : ℕ) : ℤ))).trans
            (Int.natAbs_natCast (R + k + 1)))
      omega
    rw [sourceWeilGraphAmbient_oddMode, inner_smul_right, inner_sub_right,
      (V_n_m_orthonormal i).inner_eq_zero hpos,
      (V_n_m_orthonormal i).inner_eq_zero hneg]
    simp
  · simp
  · intro y z _hy _hz hy hz
    rw [map_add, inner_add_right, hy, hz, add_zero]
  · intro a y _hy hy
    rw [map_smul, inner_smul_right, hy, mul_zero]

/-- The same low-frequency cancellation holds on the literal closed graph
tail.  Unlike coercivity, a Fourier coefficient is linear and continuous, so
its zero set is closed directly. -/
theorem sourceWeilGraphOddTail_low_fourier_vanish
    (i : PairIndex) (R : ℕ) (x : SourceWeilGraphOddTailCarrier i R)
    (n : ℤ) (hn : n.natAbs ≤ R) :
    inner ℂ (V_n_m i n)
      (sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)) = 0 := by
  let algebraic : Submodule ℂ (SourceWeilGraphCarrier i) :=
    Submodule.span ℂ
      (Set.range (fun k : ℕ => sourceWeilGraphOddMode i (R + k)))
  let coefficient : SourceWeilGraphCarrier i → ℂ := fun y =>
    inner ℂ (V_n_m i n) (sourceWeilGraphAmbient i y)
  have hcontinuous : Continuous coefficient := by
    dsimp [coefficient]
    fun_prop
  have hclosed : IsClosed {y : SourceWeilGraphCarrier i | coefficient y = 0} :=
    isClosed_eq hcontinuous continuous_const
  have hsubset :
      (algebraic : Set (SourceWeilGraphCarrier i)) ⊆
        {y : SourceWeilGraphCarrier i | coefficient y = 0} := by
    intro y hy
    exact sourceWeilGraphOddTailAlgebraic_low_fourier_vanish i R y
      (by simpa [algebraic] using hy) n hn
  have hxclosure :
      (x : SourceWeilGraphCarrier i) ∈
        closure (algebraic : Set (SourceWeilGraphCarrier i)) := by
    change (x : SourceWeilGraphCarrier i) ∈ algebraic.topologicalClosure
    have hxprop := x.property
    change (x : SourceWeilGraphCarrier i) ∈ algebraic.topologicalClosure at hxprop
    exact hxprop
  exact (closure_minimal hsubset hclosed) hxclosure

/-- The exact project-side theorem head to be supplied by a formalized
Yoshida high-mode estimate.  It speaks about the existing source-Weil form,
the existing maximal shifted form domain, the existing orthonormal modes, and
the ambient `H_m` norm; it is not a paper citation or a new axiom. -/
def SourceWeilHighModeAmbientCoercive
    (i : PairIndex) (R : ℕ) (mu : ℝ) : Prop :=
  0 < mu ∧
    ∀ x : sourceArchimedeanShiftedFormDomain i,
      (∀ n : ℤ, n.natAbs ≤ R → inner ℂ (V_n_m i n) (x : H_m i) = 0) →
        mu * ‖(x : H_m i)‖ ^ 2 ≤
          (sourceWeilSesquilinearForm i x x).re

/-- The source-facing high-mode theorem head spends directly on the literal
closed odd tail because the exact low production coefficients vanish there. -/
theorem sourceWeilOddTailAmbientCoercive_of_highMode
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (h : SourceWeilHighModeAmbientCoercive i R mu) :
    SourceWeilOddTailAmbientCoercive i R mu := by
  refine ⟨h.1, ?_⟩
  intro x
  apply h.2 (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
  intro n hn
  simpa only [sourceWeilGraphDomain_coe] using
    (sourceWeilGraphOddTail_low_fourier_vanish i R x n hn)

/-- On the exact graph carrier, the raw source-Weil diagonal is a continuous
quadratic expression obtained by subtracting the explicit lower-bound shift
from the bounded shifted graph-operator diagonal. -/
theorem sourceWeilSesquilinearForm_self_re_eq_graph_diagonal_sub_shift
    (i : PairIndex) (x : SourceWeilGraphCarrier i) :
    (sourceWeilSesquilinearForm i
        (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i x)).re =
      (inner ℂ (sourceWeilShiftedGraphOperator i x) x).re -
        sourceWeilLowerBoundConstant i * ‖sourceWeilGraphAmbient i x‖ ^ 2 := by
  rw [inner_sourceWeilShiftedGraphOperator_eq_source]
  have hinner :
      (inner ℂ (sourceWeilGraphAmbient i x)
        (sourceWeilGraphAmbient i x)).re =
          ‖sourceWeilGraphAmbient i x‖ ^ 2 := by
    simpa using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (sourceWeilGraphAmbient i x))
  simp only [add_re, mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, hinner]
  ring

/-- Generic graph-topology closure transport for a tail generated by an
arbitrary source-Weil graph family.  The generator is explicit so this lemma
does not manufacture a cutoff, a parity sector, or a coercivity constant. -/
theorem sourceWeilGraphTailAmbientCoercive_of_algebraic
    (i : PairIndex) (generator : ℕ → SourceWeilGraphCarrier i)
    (mu : ℝ)
    (h : ∀ x : SourceWeilGraphCarrier i,
      x ∈ Submodule.span ℂ (Set.range generator) →
        mu * ‖sourceWeilGraphAmbient i x‖ ^ 2 ≤
          (sourceWeilSesquilinearForm i
            (sourceWeilGraphDomain i x) (sourceWeilGraphDomain i x)).re) :
    ∀ x : (Submodule.span ℂ (Set.range generator)).topologicalClosure,
      mu * ‖sourceWeilGraphAmbient i (x : SourceWeilGraphCarrier i)‖ ^ 2 ≤
        (sourceWeilSesquilinearForm i
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
          (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))).re := by
  intro x
  let algebraic : Submodule ℂ (SourceWeilGraphCarrier i) :=
    Submodule.span ℂ (Set.range generator)
  let lhs : SourceWeilGraphCarrier i → ℝ := fun y =>
    mu * ‖sourceWeilGraphAmbient i y‖ ^ 2
  let rhs : SourceWeilGraphCarrier i → ℝ := fun y =>
    (inner ℂ (sourceWeilShiftedGraphOperator i y) y).re -
      sourceWeilLowerBoundConstant i * ‖sourceWeilGraphAmbient i y‖ ^ 2
  have hlhs : Continuous lhs := by
    dsimp [lhs]
    fun_prop
  have hrhs : Continuous rhs := by
    dsimp [rhs]
    fun_prop
  have hclosed : IsClosed {y : SourceWeilGraphCarrier i | lhs y ≤ rhs y} :=
    isClosed_le hlhs hrhs
  have hsubset :
      (algebraic : Set (SourceWeilGraphCarrier i)) ⊆
        {y : SourceWeilGraphCarrier i | lhs y ≤ rhs y} := by
    intro y hy
    change lhs y ≤ rhs y
    rw [show rhs y =
        (sourceWeilSesquilinearForm i
          (sourceWeilGraphDomain i y) (sourceWeilGraphDomain i y)).re by
      exact (sourceWeilSesquilinearForm_self_re_eq_graph_diagonal_sub_shift
        i y).symm]
    exact h y (by simpa [algebraic] using hy)
  have hxclosure :
      (x : SourceWeilGraphCarrier i) ∈
        closure (algebraic : Set (SourceWeilGraphCarrier i)) := by
    change (x : SourceWeilGraphCarrier i) ∈ algebraic.topologicalClosure
    have hxprop := x.property
    change (x : SourceWeilGraphCarrier i) ∈ algebraic.topologicalClosure at hxprop
    exact hxprop
  have hxineq : lhs (x : SourceWeilGraphCarrier i) ≤
      rhs (x : SourceWeilGraphCarrier i) :=
    (closure_minimal hsubset hclosed) hxclosure
  change lhs (x : SourceWeilGraphCarrier i) ≤
    (sourceWeilSesquilinearForm i
      (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))
      (sourceWeilGraphDomain i (x : SourceWeilGraphCarrier i))).re
  rw [sourceWeilSesquilinearForm_self_re_eq_graph_diagonal_sub_shift]
  exact hxineq

/-- A coercive source estimate on every finite high-odd combination extends
to the literal closed graph tail, with the same cutoff and the same constant.
This is graph-topology closure transport, not Hilbert-norm density. -/
theorem sourceWeilOddTailAmbientCoercive_of_algebraic
    (i : PairIndex) (R : ℕ) (mu : ℝ)
    (h : SourceWeilOddTailAlgebraicCoercive i R mu) :
    SourceWeilOddTailAmbientCoercive i R mu := by
  refine ⟨h.1, ?_⟩
  exact sourceWeilGraphTailAmbientCoercive_of_algebraic i
    (fun k : ℕ => sourceWeilGraphOddMode i (R + k)) mu h.2

#print axioms sourceWeilSesquilinearForm_self_re_eq_graph_diagonal_sub_shift
#print axioms sourceWeilGraphTailAmbientCoercive_of_algebraic
#print axioms sourceWeilGraphOddTailAlgebraic_low_fourier_vanish
#print axioms sourceWeilGraphOddTail_low_fourier_vanish
#print axioms sourceWeilOddTailAmbientCoercive_of_highMode
#print axioms sourceWeilOddTailAmbientCoercive_of_algebraic

end Q3.RouteB.D0Pstar
