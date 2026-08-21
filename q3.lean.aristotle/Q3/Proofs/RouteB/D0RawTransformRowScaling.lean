import Q3.Proofs.RouteB.D0CanonicalApproximation
import Q3.Proofs.RouteB.Proposition59GroundLagrangeZeroSetBridge

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Finset

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Row scaling of the raw transform, and the value crosswalk it reduces

`G3_CVS_PORT:1` asks for the exact equality of the selected function with a
nonzero multiple of the `proposition59CCMTransform` ground row. Both sides are
instances of the same `proposition59RawTransform`, differing only in their
coefficient rows, and the transform is linear in that row. So the value-level
equality is exactly a row-level proportionality, and this file performs the
reduction.

What this does **not** do: it does not prove the rows are proportional. Whether
the trial coefficient row of the canonical family really is a nonzero multiple
of the CCM ground row on the shared mode set is the source content of the CvS
port and remains the open obligation. Proving the value identity from an
assumed row identity is bookkeeping; asserting the row identity is the work.

LEDGER:
  CLOSES: []
  OPENS:  []
-/

/-- **Row scaling.**  The raw transform is homogeneous in its coefficient row:
a row that is pointwise `c` times another on the summation set produces `c`
times the transform, at every argument. -/
theorem proposition59RawTransform_row_smul
    (L : ℝ) (S : Finset ℤ) (xi eta : ℤ → ℂ) (c : ℂ)
    (hrow : ∀ k ∈ S, xi k = c * eta k) (z : ℂ) :
    proposition59RawTransform L S xi z =
      c * proposition59RawTransform L S eta z := by
  unfold proposition59RawTransform
  have hsum :
      (∑ k ∈ S, xi k * proposition59PoleKernel L k z) =
        c * ∑ k ∈ S, eta k * proposition59PoleKernel L k z := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    rw [hrow k hk]
    ring
  rw [hsum]
  ring

/-- **The reduced crosswalk.**  If the trial coefficient row of the canonical
family is `c` times the CCM ground coefficient row on the mode set, then the raw
selected function is exactly `c` times the ground transform, at every point.

The set equality `modeSet i = Icc (−N) N` is a hypothesis rather than a
computation because the index bound of the family and the ground row need not
agree a priori; when they do, `rfl` discharges it. -/
theorem rawFplus_eq_smul_ccmTransform_of_row
    (D : CoefficientFamily) (i : PairIndex) (N : ℕ)
    (xi : CCMModeFinite N → ℝ) (c : ℂ)
    (hset : modeSet i = Finset.Icc (-(N : ℤ)) (N : ℤ))
    (hrow : ∀ k ∈ modeSet i,
      D.kTrial i k = c * proposition59CCMCoefficient N xi k) :
    ∀ z : ℂ,
      rawFplus D i z =
        c * proposition59CCMTransform (logLength i) N xi (-z) := by
  intro z
  unfold rawFplus proposition59CCMTransform
  rw [← hset]
  exact proposition59RawTransform_row_smul (logLength i) (modeSet i)
    (D.kTrial i) (proposition59CCMCoefficient N xi) c hrow (-z)

#print axioms proposition59RawTransform_row_smul
#print axioms rawFplus_eq_smul_ccmTransform_of_row

end Q3.RouteB.D0Pstar
