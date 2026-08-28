import Mathlib

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The apparent pole `2*pi*k/L` in Proposition 5.9. -/
def proposition59Pole (L : ℝ) (k : ℤ) : ℂ :=
  (2 * (k : ℂ) * (Real.pi : ℂ)) / (L : ℂ)

/-- Distinct integer modes give distinct Proposition-5.9 lattice points when
the log length is nonzero. -/
theorem proposition59Pole_ne
    {L : ℝ} (hL : L ≠ 0) {j k : ℤ} (hjk : j ≠ k) :
    proposition59Pole L j ≠ proposition59Pole L k := by
  intro h
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  unfold proposition59Pole at h
  field_simp [hLC] at h
  have : (j : ℂ) = (k : ℂ) := by
    apply (mul_left_cancel₀ hpi)
    apply (mul_left_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
    simpa [mul_assoc] using h
  apply hjk
  exact_mod_cast this

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

/-- The full Proposition-5.9 pole row: the removable diagonal entry is the
derivative value and every off-diagonal lattice entry vanishes. -/
theorem proposition59PoleKernel_at_lattice
    {L : ℝ} (hL : L ≠ 0) (k j : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L j) =
      if k = j then
        (L : ℂ) * Complex.cos ((j : ℂ) * (Real.pi : ℂ))
      else 0 := by
  by_cases hkj : k = j
  · subst k
    simp [proposition59PoleKernel_at_pole hL]
  · rw [if_neg hkj, proposition59PoleKernel_eq_quotient hL k]
    · rw [proposition59Numerator_at_pole hL j]
      simp
    · exact proposition59Pole_ne hL (Ne.symm hkj)

/-- The same pole row with its alternating sign made explicit. -/
theorem proposition59PoleKernel_at_lattice_sign
    {L : ℝ} (hL : L ≠ 0) (k j : ℤ) :
    proposition59PoleKernel L k (proposition59Pole L j) =
      if k = j then (L : ℂ) * (j.negOnePow : ℂ) else 0 := by
  rw [proposition59PoleKernel_at_lattice hL]
  congr 1
  rw [show Complex.cos ((j : ℂ) * (Real.pi : ℂ)) = (j.negOnePow : ℂ) by
    have harg : (j : ℂ) * (Real.pi : ℂ) = ((j : ℝ) * Real.pi : ℝ) := by norm_num
    rw [harg, ← Complex.ofReal_cos, Real.cos_int_mul_pi]
    exact_mod_cast (Int.cast_negOnePow ℝ j).symm]

/-- A finite unnormalised kernel sum samples exactly one coefficient at each
lattice point in its carrier. -/
theorem proposition59PoleKernel_sum_at_lattice
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) {j : ℤ} (hj : j ∈ S) :
    ∑ k ∈ S, v k * proposition59PoleKernel L k (proposition59Pole L j) =
      v j * ((L : ℂ) * (j.negOnePow : ℂ)) := by
  rw [Finset.sum_eq_single j]
  · rw [proposition59PoleKernel_at_lattice_sign hL]
    simp
  · intro k hk hkj
    rw [proposition59PoleKernel_at_lattice_sign hL, if_neg hkj]
    simp
  · simp [hj]

/-- At the central lattice point the unnormalised finite kernel sum is
`L * v 0`.  This deliberately does not include the raw transform's
`L^(-1/2)` normalisation. -/
theorem proposition59PoleKernel_sum_at_zero
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    ∑ k ∈ S, v k * proposition59PoleKernel L k 0 = (L : ℂ) * v 0 := by
  have hpole0 : proposition59Pole L 0 = 0 := by
    simp [proposition59Pole]
  rw [← hpole0, proposition59PoleKernel_sum_at_lattice hL S v h0]
  simp [mul_comm]

/-- At every lattice point the full pole row has squared `ℓ²` norm exactly
`L²`: its only nonzero entry is the removable diagonal value. -/
theorem proposition59PoleKernel_normSq_hasSum_at_lattice
    {L : ℝ} (hL : L ≠ 0) (j : ℤ) :
    HasSum
      (fun k : ℤ =>
        ‖proposition59PoleKernel L k (proposition59Pole L j)‖ ^ 2)
      (L ^ 2) := by
  have hrow :
      (fun k : ℤ =>
        ‖proposition59PoleKernel L k (proposition59Pole L j)‖ ^ 2) =
      fun k : ℤ => if k = j then L ^ 2 else 0 := by
    funext k
    rw [proposition59PoleKernel_at_lattice_sign hL]
    by_cases hkj : k = j
    · subst k
      simp [Int.cast_negOnePow, sq_abs]
    · simp [hkj]
  rw [hrow]
  exact hasSum_ite_eq j (L ^ 2)

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

/-- The exact central value of the source-locked raw transform, retaining its
explicit `L^(-1/2)` normalisation. -/
theorem proposition59RawTransform_at_zero
    {L : ℝ} (hL : L ≠ 0)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    proposition59RawTransform L S v 0 =
      (Real.sqrt L : ℂ)⁻¹ * ((L : ℂ) * v 0) := by
  unfold proposition59RawTransform
  rw [proposition59PoleKernel_sum_at_zero hL S v h0]

/-- For positive log length the normalised central value is `sqrt L * v 0`,
not the unnormalised value `L * v 0`. -/
theorem proposition59RawTransform_at_zero_eq_sqrt
    {L : ℝ} (hL : 0 < L)
    (S : Finset ℤ) (v : ℤ → ℂ) (h0 : 0 ∈ S) :
    proposition59RawTransform L S v 0 = (Real.sqrt L : ℂ) * v 0 := by
  rw [proposition59RawTransform_at_zero hL.ne' S v h0]
  have hsqrt : Real.sqrt L ≠ 0 := Real.sqrt_ne_zero'.mpr hL
  have hsq : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL.le
  have hsqC : (Real.sqrt L : ℂ) * (Real.sqrt L : ℂ) = (L : ℂ) := by
    exact_mod_cast hsq
  rw [← hsqC]
  field_simp

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
#print axioms proposition59Pole_ne
#print axioms proposition59PoleKernel_at_pole
#print axioms proposition59PoleKernel_eq_quotient
#print axioms proposition59PoleKernel_at_lattice
#print axioms proposition59PoleKernel_at_lattice_sign
#print axioms proposition59PoleKernel_sum_at_lattice
#print axioms proposition59PoleKernel_sum_at_zero
#print axioms proposition59PoleKernel_normSq_hasSum_at_lattice
#print axioms differentiable_proposition59PoleKernel
#print axioms proposition59RawTransform_at_zero
#print axioms proposition59RawTransform_at_zero_eq_sqrt
#print axioms differentiable_proposition59RawTransform
#print axioms proposition59RawTransform_eq_quotient_sum
#print axioms proposition59RawTransform_eq_paper_formula

end Q3.RouteB
