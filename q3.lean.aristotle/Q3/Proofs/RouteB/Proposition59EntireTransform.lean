import Mathlib

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The apparent pole `2*pi*k/L` in Proposition 5.9. -/
def proposition59Pole (L : ℝ) (k : ℤ) : ℂ :=
  (2 * (k : ℂ) * (Real.pi : ℂ)) / (L : ℂ)

/-- The common sine numerator in Proposition 5.9. -/
def proposition59Numerator (L : ℝ) (z : ℂ) : ℂ :=
  2 * Complex.sin (z * (L : ℂ) / 2)

theorem proposition59Numerator_at_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    proposition59Numerator L (proposition59Pole L k) = 0 := by
  have harg : proposition59Pole L k * (L : ℂ) / 2 = (k : ℂ) * (Real.pi : ℂ) := by
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    unfold proposition59Pole
    field_simp [hLC]
  unfold proposition59Numerator
  rw [harg, Complex.sin_int_mul_pi]
  simp

/-- The removable-pole kernel in Proposition 5.9.  Using `dslope` makes the
value at the apparent pole part of the definition instead of a side condition. -/
def proposition59PoleKernel (L : ℝ) (k : ℤ) : ℂ → ℂ :=
  dslope (proposition59Numerator L) (proposition59Pole L k)

theorem hasDerivAt_proposition59Numerator (L : ℝ) (z : ℂ) :
    HasDerivAt (proposition59Numerator L)
      ((L : ℂ) * Complex.cos (z * (L : ℂ) / 2)) z := by
  have hlinear : HasDerivAt (fun w : ℂ => w * (L : ℂ) / 2) ((L : ℂ) / 2) z := by
    exact (hasDerivAt_mul_const (L : ℂ)).div_const 2
  have hsin := (Complex.hasDerivAt_sin (z * (L : ℂ) / 2)).comp z hlinear
  have hscaled := hsin.const_mul 2
  convert hscaled using 1
  ring

/-- At its own lattice point the removable kernel has the finite derivative
value `L*cos(pi*k)`, rather than a pole. -/
theorem proposition59PoleKernel_at_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L k) =
      (L : ℂ) * Complex.cos ((k : ℂ) * (Real.pi : ℂ)) := by
  have harg : proposition59Pole L k * (L : ℂ) / 2 = (k : ℂ) * (Real.pi : ℂ) := by
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
    unfold proposition59Pole
    field_simp [hLC]
  rw [proposition59PoleKernel, dslope_same,
    (hasDerivAt_proposition59Numerator L (proposition59Pole L k)).deriv, harg]

/-- Away from the removable point, the kernel is exactly the quotient printed
in Proposition 5.9. -/
theorem proposition59PoleKernel_eq_quotient
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) {z : ℂ}
    (hz : z ≠ proposition59Pole L k) :
    proposition59PoleKernel L k z =
      proposition59Numerator L z / (z - proposition59Pole L k) := by
  rw [proposition59PoleKernel, dslope_of_ne _ hz]
  simp [slope, proposition59Numerator_at_pole hL, div_eq_inv_mul, mul_comm]

/-- Each apparent-pole summand in Proposition 5.9 is globally entire after
the canonical removable extension. -/
theorem differentiable_proposition59PoleKernel (L : ℝ) (k : ℤ) :
    Differentiable ℂ (proposition59PoleKernel L k) := by
  have hnum : Differentiable ℂ (proposition59Numerator L) := by
    unfold proposition59Numerator
    fun_prop
  have hds : DifferentiableOn ℂ
      (dslope (proposition59Numerator L) (proposition59Pole L k)) Set.univ :=
    (Complex.differentiableOn_dslope (s := Set.univ)
      (c := proposition59Pole L k) univ_mem).2 hnum.differentiableOn
  exact differentiableOn_univ.mp hds

/-- The source-locked finite raw transform in Proposition 5.9.  The factor
`L^(-1/2)` is constant in the spectral variable and is kept exactly. -/
def proposition59RawTransform
    (L : ℝ) (S : Finset ℤ) (xi : ℤ → ℂ) (z : ℂ) : ℂ :=
  ((Real.sqrt L : ℂ)⁻¹) *
    ∑ k ∈ S, xi k * proposition59PoleKernel L k z

/-- Proposition 5.9's finite raw transform is entire, with no excluded lattice
points and no pole-cancellation assumption. -/
theorem differentiable_proposition59RawTransform
    (L : ℝ) (S : Finset ℤ) (xi : ℤ → ℂ) :
    Differentiable ℂ (proposition59RawTransform L S xi) := by
  unfold proposition59RawTransform
  apply Differentiable.const_mul
  apply Differentiable.fun_sum
  intro k hk
  exact (differentiable_proposition59PoleKernel L k).const_mul (xi k)

/-- On points avoiding the finite pole lattice, the removable definition is
definitionally the quotient formula from Proposition 5.9. -/
theorem proposition59RawTransform_eq_quotient_sum
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (xi : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    proposition59RawTransform L S xi z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ k ∈ S,
          xi k * (proposition59Numerator L z /
            (z - proposition59Pole L k)) := by
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [proposition59PoleKernel_eq_quotient hL k (hz k hk)]

/-- This is the printed Proposition-5.9 shape: one common sine numerator
times the finite Cauchy sum.  It is asserted only off the finite lattice;
`proposition59RawTransform` itself is defined and entire on all of `ℂ`. -/
theorem proposition59RawTransform_eq_paper_formula
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (xi : ℤ → ℂ) {z : ℂ}
    (hz : ∀ k ∈ S, z ≠ proposition59Pole L k) :
    proposition59RawTransform L S xi z =
      ((Real.sqrt L : ℂ)⁻¹) * proposition59Numerator L z *
        ∑ k ∈ S, xi k / (z - proposition59Pole L k) := by
  rw [proposition59RawTransform_eq_quotient_sum hL S xi hz, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

#print axioms proposition59Numerator_at_pole
#print axioms proposition59PoleKernel_at_pole
#print axioms proposition59PoleKernel_eq_quotient
#print axioms differentiable_proposition59PoleKernel
#print axioms differentiable_proposition59RawTransform
#print axioms proposition59RawTransform_eq_quotient_sum
#print axioms proposition59RawTransform_eq_paper_formula

end Q3.RouteB
