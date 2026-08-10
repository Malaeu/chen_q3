import Q3.Proofs.RouteB.D0PstarSourceWeilClosedForm

noncomputable section

open Complex Filter MeasureTheory Topology
open scoped ENNReal

namespace Q3.RouteB.D0Pstar

/-!
# Source-Weil form-core topology

This file isolates the topology that the remaining source form-core theorem
must use.  The complete shifted source-Weil energy differs from the graph
energy of the closed square-root-weight map only by the already-proved
continuous nonnegative bounded diagonal.  Consequently, on sequences that
converge in the ambient Hilbert norm, convergence of either energy to zero is
equivalent to convergence of the other.

This is a topology reduction only.  It does not assert that the literal mode
span is a form core, does not prove a Yoshida tail estimate, and does not make
an associated-operator or RH claim.
-/

/-- Exact decomposition of the complete shifted source-Weil energy on its
form domain into the squared graph-output norm and the continuous bounded
diagonal. -/
theorem sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add
    (i : PairIndex) (x : sourceArchimedeanShiftedFormDomain i) :
    (sourceWeilShiftedExtendedQuadraticForm i x.1).toReal =
      ‖sourceArchimedeanShiftedWeightedLpLinearMap i x‖ ^ 2 +
        sourceWeilBoundedShiftedDiagonal i x.1 := by
  have hArchLt :
      sourceArchimedeanShiftedExtendedQuadraticForm i x.1 < ∞ :=
    (mem_sourceArchimedeanShiftedFormDomain_iff_extendedQuadraticForm_lt_top
      i x.1).mp x.2
  rw [sourceWeilShiftedExtendedQuadraticForm,
    ENNReal.toReal_add (ne_of_lt hArchLt)
      (ne_of_lt ENNReal.ofReal_lt_top),
    ENNReal.toReal_ofReal (sourceWeilBoundedShiftedDiagonal_nonneg i x.1),
    sourceArchimedeanShiftedExtendedQuadraticForm_toReal_eq_re,
    sourceArchimedeanShiftedSesquilinearForm_apply]
  simpa using
    (inner_self_eq_norm_sq (𝕜 := ℂ)
      (sourceArchimedeanShiftedWeightedLpLinearMap i x))

/-- Along an ambient-null sequence in the exact form domain, the complete
shifted source-Weil energy tends to zero exactly when the output of the
closed square-root-weight map tends to zero.  This is the precise reduction
needed before importing the Connes--Consani Laurent-polynomial core proof. -/
theorem tendsto_sourceWeilShifted_energy_zero_iff_weighted_graph_zero
    (i : PairIndex)
    (x : ℕ → sourceArchimedeanShiftedFormDomain i)
    (hx : Tendsto (fun n => ((x n : sourceArchimedeanShiftedFormDomain i) : H_m i))
      atTop (𝓝 0)) :
    Tendsto
        (fun n =>
          (sourceWeilShiftedExtendedQuadraticForm i (x n).1).toReal)
        atTop (𝓝 0) ↔
      Tendsto
        (fun n => ‖sourceArchimedeanShiftedWeightedLpLinearMap i (x n)‖)
        atTop (𝓝 0) := by
  have hbounded :
      Tendsto
        (fun n => sourceWeilBoundedShiftedDiagonal i (x n).1)
        atTop (𝓝 0) := by
    have h :=
      (sourceWeilBoundedShiftedDiagonal_continuous i).continuousAt.tendsto.comp hx
    have hzero : sourceWeilBoundedShiftedDiagonal i 0 = 0 := by
      simp [sourceWeilBoundedShiftedDiagonal]
    simpa only [Function.comp_apply, hzero] using h
  constructor
  · intro henergy
    have hsum :
        Tendsto
          (fun n =>
            ‖sourceArchimedeanShiftedWeightedLpLinearMap i (x n)‖ ^ 2 +
              sourceWeilBoundedShiftedDiagonal i (x n).1)
          atTop (𝓝 0) := by
      simpa only [sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add]
        using henergy
    have hsquare :
        Tendsto
          (fun n =>
            ‖sourceArchimedeanShiftedWeightedLpLinearMap i (x n)‖ ^ 2)
          atTop (𝓝 0) := by
      have := hsum.sub hbounded
      simpa using this
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsquare
    convert hsqrt using 1
    · ext n
      simp [Function.comp_apply, Real.sqrt_sq (norm_nonneg _)]
    · simp
  · intro hweighted
    have hsquare :
        Tendsto
          (fun n =>
            ‖sourceArchimedeanShiftedWeightedLpLinearMap i (x n)‖ ^ 2)
          atTop (𝓝 0) := by
      simpa using hweighted.pow 2
    have hsum := hsquare.add hbounded
    simpa only [sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add,
      zero_add]
      using hsum

/-- A submodule of the exact shifted form domain is a source-Weil form core
when every domain vector admits an ambient-convergent sequence whose complete
shifted source-Weil energy error tends to zero. -/
def IsSourceWeilFormCore
    (i : PairIndex)
    (S : Submodule ℂ (sourceArchimedeanShiftedFormDomain i)) : Prop :=
  ∀ x : sourceArchimedeanShiftedFormDomain i,
    ∃ a : ℕ → S,
      Tendsto
          (fun n => (((a n).1 : sourceArchimedeanShiftedFormDomain i) : H_m i))
          atTop (𝓝 (x : H_m i)) ∧
        Tendsto
          (fun n =>
            (sourceWeilShiftedExtendedQuadraticForm i
              (((a n).1 : sourceArchimedeanShiftedFormDomain i) - x).1).toReal)
          atTop (𝓝 0)

/-- The corresponding graph-core predicate for the closed shifted
square-root-weight map. -/
def IsSourceArchimedeanShiftedWeightedGraphCore
    (i : PairIndex)
    (S : Submodule ℂ (sourceArchimedeanShiftedFormDomain i)) : Prop :=
  ∀ x : sourceArchimedeanShiftedFormDomain i,
    ∃ a : ℕ → S,
      Tendsto
          (fun n => (((a n).1 : sourceArchimedeanShiftedFormDomain i) : H_m i))
          atTop (𝓝 (x : H_m i)) ∧
        Tendsto
          (fun n =>
            ‖sourceArchimedeanShiftedWeightedLpLinearMap i
              ((a n).1 - x)‖)
          atTop (𝓝 0)

/-- The complete shifted source-Weil core condition is exactly the graph-core
condition for the closed square-root-weight map.  The bounded W02 and prime
terms introduce no additional core obstruction. -/
theorem isSourceWeilFormCore_iff_isShiftedWeightedGraphCore
    (i : PairIndex)
    (S : Submodule ℂ (sourceArchimedeanShiftedFormDomain i)) :
    IsSourceWeilFormCore i S ↔
      IsSourceArchimedeanShiftedWeightedGraphCore i S := by
  constructor
  · intro hcore x
    obtain ⟨a, ha, henergy⟩ := hcore x
    refine ⟨a, ha, ?_⟩
    have hdiff :
        Tendsto
          (fun n =>
            ((((a n).1 : sourceArchimedeanShiftedFormDomain i) - x :
                sourceArchimedeanShiftedFormDomain i) : H_m i))
          atTop (𝓝 0) := by
      simpa using ha.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (x : H_m i)) atTop (𝓝 (x : H_m i)))
    exact
      (tendsto_sourceWeilShifted_energy_zero_iff_weighted_graph_zero i
        (fun n => (a n).1 - x) hdiff).mp henergy
  · intro hcore x
    obtain ⟨a, ha, hweighted⟩ := hcore x
    refine ⟨a, ha, ?_⟩
    have hdiff :
        Tendsto
          (fun n =>
            ((((a n).1 : sourceArchimedeanShiftedFormDomain i) - x :
                sourceArchimedeanShiftedFormDomain i) : H_m i))
          atTop (𝓝 0) := by
      simpa using ha.sub
        (tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (x : H_m i)) atTop (𝓝 (x : H_m i)))
    exact
      (tendsto_sourceWeilShifted_energy_zero_iff_weighted_graph_zero i
        (fun n => (a n).1 - x) hdiff).mpr hweighted

#print axioms sourceWeilShiftedExtendedQuadraticForm_toReal_eq_weighted_norm_sq_add
#print axioms tendsto_sourceWeilShifted_energy_zero_iff_weighted_graph_zero
#print axioms IsSourceWeilFormCore
#print axioms IsSourceArchimedeanShiftedWeightedGraphCore
#print axioms isSourceWeilFormCore_iff_isShiftedWeightedGraphCore

end Q3.RouteB.D0Pstar
