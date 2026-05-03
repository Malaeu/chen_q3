import Q3.Proofs.PSD_BoundaryNullConvergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

open Filter
open scoped Topology

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
Boundary-null sequential exhaustion.

Step 28 supplied the algebraic correction mechanism and Step 29 proved that
the correction is asymptotically harmless.  This file packages the consequence
needed by the certificate-family lane:

ordinary sequential density + closure under boundary correction
implies sequential density inside the boundary-null subspace.

This remains an abstract analytic shell.  The concrete smooth finite spaces
and their closure-under-correction proof are supplied by the later exhaustion
layer.
-/

/-- A sequentially exhaustive approximation family in an ambient normed
space. -/
structure OrdinarySequentialExhaustive
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] where
  member : V → Prop
  dense :
    ∀ h : V,
      ∃ g : ℕ → V,
        (∀ n, member (g n)) ∧ Tendsto g atTop (nhds h)

/-- A sequentially exhaustive approximation family inside the boundary-null
subspace for a boundary pair `E`. -/
structure BoundaryNullSequentialExhaustive
    (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : BoundaryPair V) where
  member : V → Prop
  dense_boundary :
    ∀ h : V,
      E.evalPlus h = 0 →
      E.evalMinus h = 0 →
        ∃ g : ℕ → V,
          (∀ n, member (g n)) ∧
          Tendsto g atTop (nhds h) ∧
          (∀ n, E.evalPlus (g n) = 0 ∧ E.evalMinus (g n) = 0)

/-- The explicit correction kills the plus boundary functional. -/
theorem boundaryCorrected_evalPlus_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V)
    (hdet : boundaryDet E bPlus bMinus ≠ 0) :
    E.evalPlus (boundaryCorrected E bPlus bMinus g) = 0 := by
  have hdet' :
      E.evalMinus bMinus * E.evalPlus bPlus
          - E.evalPlus bMinus * E.evalMinus bPlus ≠ 0 := by
    simpa [boundaryDet, mul_comm] using hdet
  simp [boundaryCorrected, boundaryCoeffPlus, boundaryCoeffMinus, boundaryDet]
  field_simp [hdet']
  ring_nf

/-- The explicit correction kills the minus boundary functional. -/
theorem boundaryCorrected_evalMinus_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V)
    (hdet : boundaryDet E bPlus bMinus ≠ 0) :
    E.evalMinus (boundaryCorrected E bPlus bMinus g) = 0 := by
  have hdet' :
      E.evalMinus bMinus * E.evalPlus bPlus
          - E.evalPlus bMinus * E.evalMinus bPlus ≠ 0 := by
    simpa [boundaryDet, mul_comm] using hdet
  simp [boundaryCorrected, boundaryCoeffPlus, boundaryCoeffMinus, boundaryDet]
  field_simp [hdet']
  ring_nf

/--
Convert ordinary sequential density into boundary-null sequential density.

The only family-specific analytic assumption is `hclosed`: after applying the
fixed boundary correction to a family approximant, the result still belongs to
the family.  In the directed finite-certificate lane this closure may be proved
after passing to a common refinement.
-/
def boundaryNullSequentialExhaustiveOfOrdinary
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : OrdinarySequentialExhaustive V)
    (E : BoundaryPair V) (bPlus bMinus : V)
    (hdet : boundaryDet E bPlus bMinus ≠ 0)
    (hEvalPlus_cont : Continuous E.evalPlus)
    (hEvalMinus_cont : Continuous E.evalMinus)
    (hclosed :
      ∀ g : V,
        F.member g →
          F.member (boundaryCorrected E bPlus bMinus g)) :
    BoundaryNullSequentialExhaustive V E where
  member := F.member
  dense_boundary := by
    intro h hPlus_h hMinus_h
    rcases F.dense h with ⟨g, hg_mem, hg_tendsto⟩
    refine ⟨fun n => boundaryCorrected E bPlus bMinus (g n), ?_, ?_, ?_⟩
    · intro n
      exact hclosed (g n) (hg_mem n)
    · exact
        boundaryCorrected_tendsto_of_continuous_boundary
          E bPlus bMinus h g hEvalPlus_cont hEvalMinus_cont
          hg_tendsto hPlus_h hMinus_h
    · intro n
      exact
        ⟨boundaryCorrected_evalPlus_zero E bPlus bMinus (g n) hdet,
          boundaryCorrected_evalMinus_zero E bPlus bMinus (g n) hdet⟩

/-- Proposition-level theorem wrapper around
`boundaryNullSequentialExhaustiveOfOrdinary`. -/
theorem boundaryNullSequentialExhaustive_exists_of_ordinary
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (F : OrdinarySequentialExhaustive V)
    (E : BoundaryPair V) (bPlus bMinus : V)
    (hdet : boundaryDet E bPlus bMinus ≠ 0)
    (hEvalPlus_cont : Continuous E.evalPlus)
    (hEvalMinus_cont : Continuous E.evalMinus)
    (hclosed :
      ∀ g : V,
        F.member g →
          F.member (boundaryCorrected E bPlus bMinus g)) :
    ∃ F0 : BoundaryNullSequentialExhaustive V E, F0.member = F.member := by
  refine ⟨boundaryNullSequentialExhaustiveOfOrdinary
      F E bPlus bMinus hdet hEvalPlus_cont hEvalMinus_cont hclosed, ?_⟩
  simp [boundaryNullSequentialExhaustiveOfOrdinary]

end PSDpd
end Q3
