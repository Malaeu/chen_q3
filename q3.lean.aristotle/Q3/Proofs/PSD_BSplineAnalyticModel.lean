import Q3.Proofs.PSD_BSplineMatrixIdentificationInstance
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Tactic

set_option linter.mathlibStandardSet false
set_option linter.unusedSimpArgs false

open MeasureTheory
open scoped BigOperators

noncomputable section

namespace Q3
namespace PSDpd

/-!
Concrete analytic packet identities for Step 32F.

This file is deliberately not another matrix-identification receiver.  It proves
the generic analytic identities that the B-spline packet model needs:

* transform of a translated/scaled bump;
* boundary-row specializations at `z = ±1/2`;
* correlation of two translated/scaled bumps against a shift.

The remaining centered-cardinal B-spline specialization is now localized to the
closed-form facts for the concrete bump:

* the `sinh`/sinc-power transform profile;
* the autocorrelation identity `r_k(x)=b_{2k+1}(s_k x)/c_k`.
-/

/-- Real Laplace transform used for boundary rows. -/
def realBumpLaplace (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ u : ℝ, f u * Real.exp (z * u)

/-- Complex Laplace/Fourier-side transform used for packet formulas. -/
def complexBumpLaplace (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ u : ℝ, f u * Complex.exp (z * (u : ℂ))

/-- L2-normalized translated/scaled real bump. -/
def realScaledTranslatedBump (eta : ℝ → ℝ) (ell center : ℝ) : ℝ → ℝ :=
  fun u => (Real.sqrt ell)⁻¹ * eta ((u - center) / ell)

/-- L2-normalized translated/scaled complex bump. -/
def complexScaledTranslatedBump (eta : ℝ → ℂ) (ell center : ℝ) : ℝ → ℂ :=
  fun u => ((Real.sqrt ell : ℂ)⁻¹) * eta ((u - center) / ell)

/-- Common real transform profile for the scaled packet. -/
def realBumpTransformProfile (eta : ℝ → ℝ) (ell : ℝ) (z : ℝ) : ℝ :=
  ∫ x : ℝ, eta x * Real.exp (z * (ell * x))

/-- Common complex transform profile for the scaled packet. -/
def complexBumpTransformProfile (eta : ℝ → ℂ) (ell : ℝ) (z : ℂ) : ℂ :=
  ∫ x : ℝ, eta x * Complex.exp (z * (ell * x : ℂ))

/-- Shift convention `(S_a f)(u)=f(u-a)`. -/
def realShift (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun u => f (u - a)

/-- Generic real bump correlation profile. -/
def realBumpCorrelationProfile (eta : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∫ y : ℝ, eta y * eta (y + x)

/--
Transform identity for a translated/scaled real bump.

This is the generic packet identity

\[
H_j(z)=\sqrt{\ell}\,e^{z u_j}E_\ell(z).
\]
-/
theorem realBumpLaplace_scaledTranslated
    (eta : ℝ → ℝ) (ell center : ℝ) (z : ℝ)
    (hell : 0 < ell) :
    realBumpLaplace (realScaledTranslatedBump eta ell center) z =
      Real.sqrt ell * Real.exp (z * center) *
        realBumpTransformProfile eta ell z := by
  unfold realBumpLaplace realScaledTranslatedBump realBumpTransformProfile
  let F : ℝ → ℝ :=
    fun u => (Real.sqrt ell)⁻¹ * eta ((u - center) / ell) * Real.exp (z * u)
  let G : ℝ → ℝ :=
    fun y => (Real.sqrt ell)⁻¹ * eta y * Real.exp (z * (ell * y + center))
  have hshift :
      (∫ u : ℝ, (Real.sqrt ell)⁻¹ * eta ((u - center) / ell) *
          Real.exp (z * u)) =
        ∫ x : ℝ, (Real.sqrt ell)⁻¹ * eta (x / ell) *
          Real.exp (z * (x + center)) := by
    calc
      (∫ u : ℝ, (Real.sqrt ell)⁻¹ * eta ((u - center) / ell) *
          Real.exp (z * u))
          = ∫ x : ℝ, F (x + center) := by
              rw [MeasureTheory.integral_add_right_eq_self F center]
      _ = ∫ x : ℝ, (Real.sqrt ell)⁻¹ * eta (x / ell) *
            Real.exp (z * (x + center)) := by
              simp [F, add_sub_cancel_right]
  have hscale :
      (∫ x : ℝ, (Real.sqrt ell)⁻¹ * eta (x / ell) *
          Real.exp (z * (x + center))) =
        ell • (∫ y : ℝ, (Real.sqrt ell)⁻¹ * eta y *
          Real.exp (z * (ell * y + center))) := by
    calc
      (∫ x : ℝ, (Real.sqrt ell)⁻¹ * eta (x / ell) *
          Real.exp (z * (x + center)))
          = ∫ x : ℝ, G (x / ell) := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [G, div_eq_mul_inv]
              have hx : ell * (x * ell⁻¹) + center = x + center := by
                field_simp [hell.ne']
              rw [hx]
      _ = |ell| • (∫ y : ℝ, G y) := by
              exact MeasureTheory.Measure.integral_comp_div G ell
      _ = ell • (∫ y : ℝ, (Real.sqrt ell)⁻¹ * eta y *
            Real.exp (z * (ell * y + center))) := by
              simp [G, abs_of_pos hell]
  rw [hshift, hscale]
  have hfun :
      (fun y : ℝ => (Real.sqrt ell)⁻¹ * eta y *
          Real.exp (z * (ell * y + center))) =
        fun y : ℝ => ((Real.sqrt ell)⁻¹ * Real.exp (z * center)) *
          (eta y * Real.exp (z * (ell * y))) := by
    funext y
    have hzarg : z * (ell * y + center) = z * (ell * y) + z * center := by
      ring_nf
    rw [hzarg, Real.exp_add]
    ring_nf
  rw [hfun]
  rw [MeasureTheory.integral_const_mul]
  have hcoeff : ell * (Real.sqrt ell)⁻¹ = Real.sqrt ell := by
    have hs : Real.sqrt ell ≠ 0 := (Real.sqrt_ne_zero hell.le).mpr hell.ne'
    field_simp [hs]
    exact (Real.sq_sqrt hell.le).symm
  change ell * (((Real.sqrt ell)⁻¹ * Real.exp (z * center)) *
        ∫ a : ℝ, eta a * Real.exp (z * (ell * a))) =
      Real.sqrt ell * Real.exp (z * center) *
        ∫ x : ℝ, eta x * Real.exp (z * (ell * x))
  calc
    ell * (((Real.sqrt ell)⁻¹ * Real.exp (z * center)) *
        ∫ a : ℝ, eta a * Real.exp (z * (ell * a)))
        = (ell * (Real.sqrt ell)⁻¹) *
            (Real.exp (z * center) *
              ∫ a : ℝ, eta a * Real.exp (z * (ell * a))) := by
            ring_nf
    _ = Real.sqrt ell *
            (Real.exp (z * center) *
              ∫ a : ℝ, eta a * Real.exp (z * (ell * a))) := by
            rw [hcoeff]
    _ = Real.sqrt ell * Real.exp (z * center) *
          ∫ x : ℝ, eta x * Real.exp (z * (ell * x)) := by
            ring_nf

/-- Plus-boundary row identity at `z = 1/2`. -/
theorem realBumpLaplace_scaledTranslated_plus
    (eta : ℝ → ℝ) (ell center : ℝ) (hell : 0 < ell) :
    realBumpLaplace (realScaledTranslatedBump eta ell center) (1 / 2) =
      (Real.sqrt ell * realBumpTransformProfile eta ell (1 / 2)) *
        Real.exp (center / 2) := by
  rw [realBumpLaplace_scaledTranslated eta ell center (1 / 2) hell]
  ring_nf

/-- Minus-boundary row identity at `z = -1/2`. -/
theorem realBumpLaplace_scaledTranslated_minus
    (eta : ℝ → ℝ) (ell center : ℝ) (hell : 0 < ell) :
    realBumpLaplace (realScaledTranslatedBump eta ell center) (-(1 / 2)) =
      (Real.sqrt ell * realBumpTransformProfile eta ell (-(1 / 2))) *
        Real.exp (-(center) / 2) := by
  rw [realBumpLaplace_scaledTranslated eta ell center (-(1 / 2)) hell]
  ring_nf

/--
Transform identity for a translated/scaled complex bump.

This is the same packet identity on the complex Fourier/Laplace side.
-/
theorem complexBumpLaplace_scaledTranslated
    (eta : ℝ → ℂ) (ell center : ℝ) (z : ℂ)
    (hell : 0 < ell) :
    complexBumpLaplace (complexScaledTranslatedBump eta ell center) z =
      (Real.sqrt ell : ℂ) * Complex.exp (z * (center : ℂ)) *
        complexBumpTransformProfile eta ell z := by
  unfold complexBumpLaplace complexScaledTranslatedBump complexBumpTransformProfile
  let F : ℝ → ℂ :=
    fun u => ((Real.sqrt ell : ℂ)⁻¹) * eta ((u - center) / ell) *
      Complex.exp (z * (u : ℂ))
  let G : ℝ → ℂ :=
    fun y => ((Real.sqrt ell : ℂ)⁻¹) * eta y *
      Complex.exp (z * ((ell * y + center : ℝ) : ℂ))
  have hshift :
      (∫ u : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta ((u - center) / ell) *
          Complex.exp (z * (u : ℂ))) =
        ∫ x : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta (x / ell) *
          Complex.exp (z * ((x + center : ℝ) : ℂ)) := by
    calc
      (∫ u : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta ((u - center) / ell) *
          Complex.exp (z * (u : ℂ)))
          = ∫ x : ℝ, F (x + center) := by
              rw [MeasureTheory.integral_add_right_eq_self F center]
      _ = ∫ x : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta (x / ell) *
            Complex.exp (z * ((x + center : ℝ) : ℂ)) := by
              simp [F, add_sub_cancel_right]
  have hscale :
      (∫ x : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta (x / ell) *
          Complex.exp (z * ((x + center : ℝ) : ℂ))) =
        ell • (∫ y : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta y *
          Complex.exp (z * ((ell * y + center : ℝ) : ℂ))) := by
    calc
      (∫ x : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta (x / ell) *
          Complex.exp (z * ((x + center : ℝ) : ℂ)))
          = ∫ x : ℝ, G (x / ell) := by
              apply integral_congr_ae
              filter_upwards with x
              simp only [G, div_eq_mul_inv, Complex.ofReal_add, Complex.ofReal_mul,
                Complex.ofReal_inv]
              have hx :
                  (↑ell * (↑x * (↑ell)⁻¹) + ↑center : ℂ) =
                    ↑x + ↑center := by
                field_simp [Complex.ofReal_ne_zero.mpr hell.ne']
              rw [← hx]
      _ = |ell| • (∫ y : ℝ, G y) := by
              exact MeasureTheory.Measure.integral_comp_div G ell
      _ = ell • (∫ y : ℝ, ((Real.sqrt ell : ℂ)⁻¹) * eta y *
            Complex.exp (z * ((ell * y + center : ℝ) : ℂ))) := by
              simp [G, abs_of_pos hell]
  rw [hshift, hscale]
  have hfun :
      (fun y : ℝ => ((Real.sqrt ell : ℂ)⁻¹) * eta y *
          Complex.exp (z * ((ell * y + center : ℝ) : ℂ))) =
        fun y : ℝ => (((Real.sqrt ell : ℂ)⁻¹) * Complex.exp (z * (center : ℂ))) *
          (eta y * Complex.exp (z * (ell * y : ℂ))) := by
    funext y
    rw [Complex.ofReal_add, Complex.ofReal_mul]
    have hzarg : z * (↑ell * ↑y + ↑center) =
        z * (↑ell * ↑y) + z * ↑center := by
      ring_nf
    rw [hzarg, Complex.exp_add]
    ring_nf
  rw [hfun]
  rw [MeasureTheory.integral_const_mul]
  have hcoeff : (ell : ℂ) * (Real.sqrt ell : ℂ)⁻¹ =
      (Real.sqrt ell : ℂ) := by
    have hs : (Real.sqrt ell : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr ((Real.sqrt_ne_zero hell.le).mpr hell.ne')
    field_simp [hs]
    exact_mod_cast (Real.sq_sqrt hell.le).symm
  calc
    ell • ((((Real.sqrt ell : ℂ)⁻¹) * Complex.exp (z * ↑center)) *
        ∫ a : ℝ, eta a * Complex.exp (z * (↑ell * ↑a)))
        = ((ell : ℂ) * (Real.sqrt ell : ℂ)⁻¹) *
            (Complex.exp (z * ↑center) *
              ∫ a : ℝ, eta a * Complex.exp (z * (↑ell * ↑a))) := by
            simp
            ring_nf
    _ = (Real.sqrt ell : ℂ) *
            (Complex.exp (z * ↑center) *
              ∫ a : ℝ, eta a * Complex.exp (z * (↑ell * ↑a))) := by
            rw [hcoeff]
    _ = ↑√ell * Complex.exp (z * ↑center) *
          ∫ x : ℝ, eta x * Complex.exp (z * (↑ell * ↑x)) := by
            ring_nf

/--
Correlation identity for translated/scaled real bumps against the shift
`(S_a f)(u)=f(u-a)`.

This is the generic source of the prime-side packet entries.
-/
theorem realBumpCorrelation_scaledTranslated_shift
    (eta : ℝ → ℝ) (ell ui uj a : ℝ) (hell : 0 < ell) :
    (∫ u : ℝ,
        realScaledTranslatedBump eta ell uj u *
          realShift a (realScaledTranslatedBump eta ell ui) u) =
      realBumpCorrelationProfile eta ((uj - ui - a) / ell) := by
  unfold realScaledTranslatedBump realShift realBumpCorrelationProfile
  let F : ℝ → ℝ :=
    fun u => (√ell)⁻¹ * eta ((u - uj) / ell) *
      ((√ell)⁻¹ * eta (((u - a) - ui) / ell))
  let G : ℝ → ℝ :=
    fun y => (√ell)⁻¹ * eta y *
      ((√ell)⁻¹ * eta (y + ((uj - ui - a) / ell)))
  have hshift :
      (∫ u : ℝ,
        (√ell)⁻¹ * eta ((u - uj) / ell) *
          ((√ell)⁻¹ * eta (((u - a) - ui) / ell))) =
        ∫ x : ℝ,
          (√ell)⁻¹ * eta (x / ell) *
            ((√ell)⁻¹ * eta ((x + (uj - ui - a)) / ell)) := by
    calc
      (∫ u : ℝ,
        (√ell)⁻¹ * eta ((u - uj) / ell) *
          ((√ell)⁻¹ * eta (((u - a) - ui) / ell)))
          = ∫ x : ℝ, F (x + uj) := by
              rw [MeasureTheory.integral_add_right_eq_self F uj]
      _ = ∫ x : ℝ,
            (√ell)⁻¹ * eta (x / ell) *
              ((√ell)⁻¹ * eta ((x + (uj - ui - a)) / ell)) := by
              apply integral_congr_ae
              filter_upwards with x
              have h1 : ((x + uj - uj) / ell) = x / ell := by
                ring_nf
              have h2 : (((x + uj - a) - ui) / ell) =
                  (x + (uj - ui - a)) / ell := by
                ring_nf
              simp [F, h1, h2]
  have hscale :
      (∫ x : ℝ,
        (√ell)⁻¹ * eta (x / ell) *
          ((√ell)⁻¹ * eta ((x + (uj - ui - a)) / ell))) =
        ell • (∫ y : ℝ,
          (√ell)⁻¹ * eta y *
            ((√ell)⁻¹ * eta (y + ((uj - ui - a) / ell)))) := by
    calc
      (∫ x : ℝ,
        (√ell)⁻¹ * eta (x / ell) *
          ((√ell)⁻¹ * eta ((x + (uj - ui - a)) / ell)))
          = ∫ x : ℝ, G (x / ell) := by
              apply integral_congr_ae
              filter_upwards with x
              have hx : x / ell + (uj - ui - a) / ell =
                  (x + (uj - ui - a)) / ell := by
                field_simp [hell.ne']
              simp [G, hx]
      _ = |ell| • (∫ y : ℝ, G y) := by
              exact MeasureTheory.Measure.integral_comp_div G ell
      _ = ell • (∫ y : ℝ,
            (√ell)⁻¹ * eta y *
              ((√ell)⁻¹ * eta (y + ((uj - ui - a) / ell)))) := by
              simp [G, abs_of_pos hell]
  rw [hshift, hscale]
  have hcoeff : ell * (√ell)⁻¹ * (√ell)⁻¹ = 1 := by
    have hs : √ell ≠ 0 := (Real.sqrt_ne_zero hell.le).mpr hell.ne'
    field_simp [hs]
    exact (Real.sq_sqrt hell.le).symm
  calc
    ell • (∫ y : ℝ,
      (√ell)⁻¹ * eta y *
        ((√ell)⁻¹ * eta (y + ((uj - ui - a) / ell))))
        = ∫ y : ℝ, eta y * eta (y + ((uj - ui - a) / ell)) := by
          rw [← MeasureTheory.integral_smul]
          apply integral_congr_ae
          filter_upwards with y
          calc
            ell * ((√ell)⁻¹ * eta y *
                ((√ell)⁻¹ * eta (y + (uj - ui - a) / ell)))
                = (ell * (√ell)⁻¹ * (√ell)⁻¹) *
                    (eta y * eta (y + (uj - ui - a) / ell)) := by
                    ring_nf
            _ = eta y * eta (y + (uj - ui - a) / ell) := by
                    simp [hcoeff]

end PSDpd
end Q3
