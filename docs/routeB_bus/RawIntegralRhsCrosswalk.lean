import Q3.Proofs.RouteB.FplusConstantMode
import Q3.Proofs.RouteB.Proposition59EntireTransform

/-!
# Exact raw-integral / Proposition-5.9 crosswalk

This file closes the source-raw identity at every complex point, including
the removable source lattice.  It also records the finite centered-integral
representative of the owner `Fplus` reflection at `-z`, so the two transform
conventions cannot be silently conflated.
-/

set_option linter.mathlibStandardSet false

open scoped BigOperators
open MeasureTheory

noncomputable section

namespace Q3.RouteB

/-- The phase-centered raw integral for one finite Fourier trial. -/
def finiteRawCenteredIntegral
    (L : ℝ) (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (L : ℂ) / 2) *
    ∫ x : ℝ in 0..L,
      finiteLogFourierTrial L S c x *
        Complex.exp (-Complex.I * z * (x : ℂ))

def rawModeCenteredIntegral (L : ℝ) (k : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * z * (L : ℂ) / 2) *
    ∫ x : ℝ in 0..L,
      Complex.exp
        ((((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) -
          Complex.I * z) * (x : ℂ))

theorem centered_exp_difference_eq_sin (L : ℝ) (z : ℂ) :
    Complex.exp (Complex.I * z * (L : ℂ) / 2) *
        (Complex.exp (-Complex.I * z * (L : ℂ)) - 1) =
      -2 * Complex.I * Complex.sin (z * (L : ℂ) / 2) := by
  have hleft :
      Complex.exp (Complex.I * z * (L : ℂ) / 2) *
          Complex.exp (-Complex.I * z * (L : ℂ)) =
        Complex.exp (-(z * (L : ℂ) / 2) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hright :
      Complex.exp (Complex.I * z * (L : ℂ) / 2) =
        Complex.exp ((z * (L : ℂ) / 2) * Complex.I) := by
    congr 1
    ring
  rw [mul_sub, mul_one, hleft, hright]
  change _ = -2 * Complex.I *
    ((Complex.exp (-(z * (L : ℂ) / 2) * Complex.I) -
      Complex.exp ((z * (L : ℂ) / 2) * Complex.I)) * Complex.I / 2)
  ring_nf
  rw [Complex.I_sq]
  ring

theorem rawModeCenteredIntegral_at_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) :
    rawModeCenteredIntegral L k (proposition59Pole L k) =
      proposition59PoleKernel L k (proposition59Pole L k) := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  have hcoeff :
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ) -
          Complex.I * proposition59Pole L k = 0 := by
    unfold proposition59Pole
    field_simp [hLC]
    ring_nf
  have hphaseArg :
      Complex.I * proposition59Pole L k * (L : ℂ) / 2 =
        (k : ℂ) * (Real.pi : ℂ) * Complex.I := by
    unfold proposition59Pole
    field_simp [hLC]
  rw [rawModeCenteredIntegral, hcoeff]
  simp only [zero_mul, Complex.exp_zero]
  simp only [intervalIntegral.integral_const, sub_zero, Complex.real_smul]
  rw [hphaseArg, proposition59PoleKernel_at_pole hL k]
  rw [← Complex.cos_add_sin_I]
  simp [Complex.sin_int_mul_pi]
  ring

theorem rawModeCenteredIntegral_off_pole
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) {z : ℂ}
    (hz : z ≠ proposition59Pole L k) :
    rawModeCenteredIntegral L k z = proposition59PoleKernel L k z := by
  have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL
  let a : ℂ :=
    (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ) - Complex.I * z
  have ha : a = -Complex.I * (z - proposition59Pole L k) := by
    dsimp [a]
    unfold proposition59Pole
    field_simp [hLC]
    ring
  have ha0 : a ≠ 0 := by
    rw [ha]
    exact mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) (sub_ne_zero.mpr hz)
  have haL : a * (L : ℂ) =
      (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        (-Complex.I * z * (L : ℂ)) := by
    dsimp [a]
    field_simp [hLC]
    ring
  have hexp : Complex.exp (a * (L : ℂ)) =
      Complex.exp (-Complex.I * z * (L : ℂ)) := by
    rw [haL, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
    simp
  rw [rawModeCenteredIntegral]
  change Complex.exp (Complex.I * z * (L : ℂ) / 2) *
      (∫ x : ℝ in 0..L, Complex.exp (a * (x : ℂ))) = _
  rw [integral_exp_mul_complex ha0]
  rw [hexp, proposition59PoleKernel_eq_quotient hL k hz, ha]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp [Complex.I_ne_zero, sub_ne_zero.mpr hz]
  rw [show -(Complex.I * z * (L : ℂ)) = -Complex.I * z * (L : ℂ) by ring]
  rw [centered_exp_difference_eq_sin]
  unfold proposition59Numerator
  rw [neg_mul, neg_mul, neg_neg]
  ring_nf

theorem rawModeCenteredIntegral_eq_kernel
    {L : ℝ} (hL : L ≠ 0) (k : ℤ) (z : ℂ) :
    rawModeCenteredIntegral L k z = proposition59PoleKernel L k z := by
  by_cases hz : z = proposition59Pole L k
  · subst z
    exact rawModeCenteredIntegral_at_pole hL k
  · exact rawModeCenteredIntegral_off_pole hL k hz

theorem finiteRawCenteredIntegral_eq_mode_sum
    {L : ℝ} (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) :
    finiteRawCenteredIntegral L S c z =
      ((Real.sqrt L : ℂ)⁻¹) *
        ∑ k ∈ S, c k * rawModeCenteredIntegral L k z := by
  have hpoint : ∀ x : ℝ,
      finiteLogFourierTrial L S c x *
          Complex.exp (-Complex.I * z * (x : ℂ)) =
        ((Real.sqrt L : ℂ)⁻¹) *
          ∑ k ∈ S, c k *
            Complex.exp
              ((((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) -
                Complex.I * z) * (x : ℂ)) := by
    intro x
    unfold finiteLogFourierTrial
    rw [mul_assoc]
    congr 1
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  unfold finiteRawCenteredIntegral
  rw [intervalIntegral.integral_congr (fun x _hx => hpoint x)]
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finset_sum]
  · simp_rw [intervalIntegral.integral_const_mul]
    unfold rawModeCenteredIntegral
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · intro k hk
    have hcont : Continuous (fun x : ℝ =>
        c k * Complex.exp
          ((((k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) / (L : ℂ)) -
            Complex.I * z) * (x : ℂ))) := by
      fun_prop
    exact hcont.intervalIntegrable 0 L

theorem finiteRawCenteredIntegral_eq_proposition59RawTransform
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) :
    finiteRawCenteredIntegral L S c z =
      proposition59RawTransform L S c z := by
  rw [finiteRawCenteredIntegral_eq_mode_sum]
  unfold proposition59RawTransform
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [rawModeCenteredIntegral_eq_kernel hL]

/-- The positive-exponent centered integral selected by the source-locked
owner convention `Fplus(z)=T(k)(-z)`, written in finite-log coordinates. -/
def finiteFplusCenteredIntegral
    (L : ℝ) (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) : ℂ :=
  Complex.exp (-Complex.I * z * (L : ℂ) / 2) *
    ∫ x : ℝ in 0..L,
      finiteLogFourierTrial L S c x *
        Complex.exp (Complex.I * z * (x : ℂ))

theorem finiteFplusCenteredIntegral_eq_raw_neg
    (L : ℝ) (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) :
    finiteFplusCenteredIntegral L S c z =
      finiteRawCenteredIntegral L S c (-z) := by
  unfold finiteFplusCenteredIntegral finiteRawCenteredIntegral
  ring_nf

/-- The positive-exponent centered integral is the Proposition-5.9 raw
transform at `-z`; no coefficient-evenness is silently assumed. -/
theorem finiteFplusCenteredIntegral_eq_proposition59RawTransform_neg
    {L : ℝ} (hL : L ≠ 0) (S : Finset ℤ) (c : ℤ → ℂ) (z : ℂ) :
    finiteFplusCenteredIntegral L S c z =
      proposition59RawTransform L S c (-z) := by
  rw [finiteFplusCenteredIntegral_eq_raw_neg]
  exact finiteRawCenteredIntegral_eq_proposition59RawTransform hL S c (-z)

#print axioms centered_exp_difference_eq_sin
#print axioms rawModeCenteredIntegral_at_pole
#print axioms rawModeCenteredIntegral_off_pole
#print axioms rawModeCenteredIntegral_eq_kernel
#print axioms finiteRawCenteredIntegral_eq_mode_sum
#print axioms finiteRawCenteredIntegral_eq_proposition59RawTransform
#print axioms finiteFplusCenteredIntegral_eq_raw_neg
#print axioms finiteFplusCenteredIntegral_eq_proposition59RawTransform_neg

end Q3.RouteB
