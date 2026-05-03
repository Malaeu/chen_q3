import Q3.Proofs.PSD_BoundaryNullCorrection
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Topology.Algebra.Module.Basic

noncomputable section

open Filter
open scoped Topology

set_option linter.mathlibStandardSet false

namespace Q3
namespace PSDpd

/-!
Small-coefficient convergence for boundary-null correction.

Step 28 proves the algebraic correction core: if two correctors have an
invertible boundary evaluation matrix, every vector can be shifted into the
intersection of the two boundary kernels.  This file records the asymptotic
part needed by the exhaustion layer: when the raw approximants already converge
to a boundary-null limit, the explicit correction coefficients tend to zero, so
the corrected approximants still converge to the same limit.
-/

/-- Explicit coefficient correcting the `evalPlus` boundary value. -/
def boundaryCoeffPlus
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V) : ℝ :=
  (E.evalPlus g * E.evalMinus bMinus
      - E.evalPlus bMinus * E.evalMinus g)
    / boundaryDet E bPlus bMinus

/-- Explicit coefficient correcting the `evalMinus` boundary value. -/
def boundaryCoeffMinus
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V) : ℝ :=
  (E.evalPlus bPlus * E.evalMinus g
      - E.evalPlus g * E.evalMinus bPlus)
    / boundaryDet E bPlus bMinus

/-- The explicitly corrected vector. -/
def boundaryCorrected
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus g : V) : V :=
  g
    - boundaryCoeffPlus E bPlus bMinus g • bPlus
    - boundaryCoeffMinus E bPlus bMinus g • bMinus

/--
If both boundary values of `g n` tend to zero, then the plus correction
coefficient tends to zero.
-/
theorem boundaryCoeffPlus_tendsto_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus : V) (g : ℕ → V)
    (hPlus : Tendsto (fun n => E.evalPlus (g n)) atTop (nhds 0))
    (hMinus : Tendsto (fun n => E.evalMinus (g n)) atTop (nhds 0)) :
    Tendsto
      (fun n => boundaryCoeffPlus E bPlus bMinus (g n))
      atTop
      (nhds 0) := by
  have hD :
      Tendsto
        (fun n => E.evalPlus (g n) * E.evalMinus bMinus)
        atTop
        (nhds 0) := by
    simpa using hPlus.mul (tendsto_const_nhds (x := E.evalMinus bMinus))
  have hB :
      Tendsto
        (fun n => E.evalPlus bMinus * E.evalMinus (g n))
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds (x := E.evalPlus bMinus)).mul hMinus
  have hnum :
      Tendsto
        (fun n =>
          E.evalPlus (g n) * E.evalMinus bMinus
            - E.evalPlus bMinus * E.evalMinus (g n))
        atTop
        (nhds 0) := by
    simpa using hD.sub hB
  simpa [boundaryCoeffPlus] using
    hnum.div_const (boundaryDet E bPlus bMinus)

/--
If both boundary values of `g n` tend to zero, then the minus correction
coefficient tends to zero.
-/
theorem boundaryCoeffMinus_tendsto_zero
    {V : Type*} [AddCommGroup V] [Module ℝ V]
    (E : BoundaryPair V) (bPlus bMinus : V) (g : ℕ → V)
    (hPlus : Tendsto (fun n => E.evalPlus (g n)) atTop (nhds 0))
    (hMinus : Tendsto (fun n => E.evalMinus (g n)) atTop (nhds 0)) :
    Tendsto
      (fun n => boundaryCoeffMinus E bPlus bMinus (g n))
      atTop
      (nhds 0) := by
  have hA :
      Tendsto
        (fun n => E.evalPlus bPlus * E.evalMinus (g n))
        atTop
        (nhds 0) := by
    simpa using (tendsto_const_nhds (x := E.evalPlus bPlus)).mul hMinus
  have hC :
      Tendsto
        (fun n => E.evalPlus (g n) * E.evalMinus bPlus)
        atTop
        (nhds 0) := by
    simpa using hPlus.mul (tendsto_const_nhds (x := E.evalMinus bPlus))
  have hnum :
      Tendsto
        (fun n =>
          E.evalPlus bPlus * E.evalMinus (g n)
            - E.evalPlus (g n) * E.evalMinus bPlus)
        atTop
        (nhds 0) := by
    simpa using hA.sub hC
  simpa [boundaryCoeffMinus] using
    hnum.div_const (boundaryDet E bPlus bMinus)

/--
If `g n → h` and the boundary values of `g n` tend to zero, then the explicitly
corrected approximants still converge to `h`.
-/
theorem boundaryCorrected_tendsto
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : BoundaryPair V) (bPlus bMinus h : V) (g : ℕ → V)
    (hg : Tendsto g atTop (nhds h))
    (hPlus : Tendsto (fun n => E.evalPlus (g n)) atTop (nhds 0))
    (hMinus : Tendsto (fun n => E.evalMinus (g n)) atTop (nhds 0)) :
    Tendsto
      (fun n => boundaryCorrected E bPlus bMinus (g n))
      atTop
      (nhds h) := by
  have haPlus :
      Tendsto
        (fun n => boundaryCoeffPlus E bPlus bMinus (g n))
        atTop
        (nhds 0) :=
    boundaryCoeffPlus_tendsto_zero E bPlus bMinus g hPlus hMinus
  have haMinus :
      Tendsto
        (fun n => boundaryCoeffMinus E bPlus bMinus (g n))
        atTop
        (nhds 0) :=
    boundaryCoeffMinus_tendsto_zero E bPlus bMinus g hPlus hMinus
  have hPlusVec :
      Tendsto
        (fun n => boundaryCoeffPlus E bPlus bMinus (g n) • bPlus)
        atTop
        (nhds 0) := by
    simpa using haPlus.smul (tendsto_const_nhds (x := bPlus))
  have hMinusVec :
      Tendsto
        (fun n => boundaryCoeffMinus E bPlus bMinus (g n) • bMinus)
        atTop
        (nhds 0) := by
    simpa using haMinus.smul (tendsto_const_nhds (x := bMinus))
  have hsub :
      Tendsto
        (fun n =>
          g n
            - boundaryCoeffPlus E bPlus bMinus (g n) • bPlus
            - boundaryCoeffMinus E bPlus bMinus (g n) • bMinus)
        atTop
        (nhds h) := by
    simpa using (hg.sub hPlusVec).sub hMinusVec
  simpa [boundaryCorrected] using hsub

/--
If the boundary functionals are continuous and `g n → h` with `h`
boundary-null, then the corrected approximants converge to `h`.
-/
theorem boundaryCorrected_tendsto_of_continuous_boundary
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (E : BoundaryPair V) (bPlus bMinus h : V) (g : ℕ → V)
    (hEvalPlus_cont : Continuous E.evalPlus)
    (hEvalMinus_cont : Continuous E.evalMinus)
    (hg : Tendsto g atTop (nhds h))
    (hPlus_h : E.evalPlus h = 0)
    (hMinus_h : E.evalMinus h = 0) :
    Tendsto
      (fun n => boundaryCorrected E bPlus bMinus (g n))
      atTop
      (nhds h) := by
  have hPlus :
      Tendsto (fun n => E.evalPlus (g n)) atTop (nhds 0) := by
    have htmp := (hEvalPlus_cont.tendsto h).comp hg
    simpa [hPlus_h] using htmp
  have hMinus :
      Tendsto (fun n => E.evalMinus (g n)) atTop (nhds 0) := by
    have htmp := (hEvalMinus_cont.tendsto h).comp hg
    simpa [hMinus_h] using htmp
  exact boundaryCorrected_tendsto E bPlus bMinus h g hg hPlus hMinus

end PSDpd
end Q3
