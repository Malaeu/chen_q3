import Q3.Proofs.PSD_ExpInterval
import Q3.Proofs.PSD_CenteredCoeffAnalyticP0Import

set_option linter.mathlibStandardSet false

/-!
Affine-window bridge for the Step21 `P0` piecewise-polynomial backend.

The Step21 generator decomposes the `P0` profile into two compact-support
windows after the changes of variables `x=(d-a)/ell` and `x=(d+a)/ell`.
This file proves the shared calculus bridge used by those generated segments.
-/

noncomputable section

open MeasureTheory

namespace Q3
namespace PSDpd

lemma intervalIntegral_exp_mul_comp_sub_div
    (r : Real -> Real) (ell L d : Real) (hell : ell ≠ 0) :
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d - a) / ell) =
      ell * ∫ x in (d - 2 * L) / ell..d / ell,
        Real.exp ((d - ell * x) / 2) * r x := by
  have hsubst := intervalIntegral.integral_comp_sub_div
    (f := fun x : Real => Real.exp ((d - ell * x) / 2) * r x)
    (a := (0 : Real)) (b := 2 * L) (c := ell) (d := d / ell) hell
  calc
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d - a) / ell)
        = ∫ a in (0 : Real)..(2 * L),
            Real.exp ((d - ell * (d / ell - a / ell)) / 2) *
              r (d / ell - a / ell) := by
            apply intervalIntegral.integral_congr
            intro a _ha
            have harg : d / ell - a / ell = (d - a) / ell := by ring
            have hlin : (d - ell * ((d - a) / ell)) / 2 = a / 2 := by
              field_simp [hell]
              ring
            simp [harg, hlin, mul_comm]
    _ = ell * ∫ x in (d - 2 * L) / ell..d / ell,
        Real.exp ((d - ell * x) / 2) * r x := by
          have hb0 : d / ell - 0 / ell = d / ell := by ring
          have hb1 : d / ell - 2 * L / ell = (d - 2 * L) / ell := by ring
          rw [hb0, hb1] at hsubst
          simpa [mul_comm] using hsubst

lemma intervalIntegral_exp_mul_comp_sub_div_factored
    (r : Real -> Real) (ell L d : Real) (hell : ell ≠ 0) :
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d - a) / ell) =
      ell * Real.exp (d / 2) *
        ∫ x in (d - 2 * L) / ell..d / ell,
          Real.exp (-(ell / 2) * x) * r x := by
  rw [intervalIntegral_exp_mul_comp_sub_div r ell L d hell]
  have hfac :
      ∫ x in (d - 2 * L) / ell..d / ell,
        Real.exp ((d - ell * x) / 2) * r x =
      Real.exp (d / 2) *
        ∫ x in (d - 2 * L) / ell..d / ell,
          Real.exp (-(ell / 2) * x) * r x := by
    calc
      ∫ x in (d - 2 * L) / ell..d / ell,
        Real.exp ((d - ell * x) / 2) * r x
          = ∫ x in (d - 2 * L) / ell..d / ell,
              Real.exp (d / 2) * (Real.exp (-(ell / 2) * x) * r x) := by
              apply intervalIntegral.integral_congr
              intro x _hx
              change Real.exp ((d - ell * x) / 2) * r x =
                Real.exp (d / 2) * (Real.exp (-(ell / 2) * x) * r x)
              have hlin :
                  (d - ell * x) / 2 = d / 2 + (-(ell / 2) * x) := by
                ring
              rw [hlin, Real.exp_add]
              ring
      _ = Real.exp (d / 2) *
        ∫ x in (d - 2 * L) / ell..d / ell,
          Real.exp (-(ell / 2) * x) * r x := by
          rw [intervalIntegral.integral_const_mul]
  rw [hfac]
  ring

lemma intervalIntegral_exp_mul_comp_add_div
    (r : Real -> Real) (ell L d : Real) (hell : ell ≠ 0) :
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d + a) / ell) =
      ell * ∫ x in d / ell..(d + 2 * L) / ell,
        Real.exp ((ell * x - d) / 2) * r x := by
  have hsubst := intervalIntegral.integral_comp_add_div
    (f := fun x : Real => Real.exp ((ell * x - d) / 2) * r x)
    (a := (0 : Real)) (b := 2 * L) (c := ell) (d := d / ell) hell
  calc
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d + a) / ell)
        = ∫ a in (0 : Real)..(2 * L),
            Real.exp ((ell * (d / ell + a / ell) - d) / 2) *
              r (d / ell + a / ell) := by
            apply intervalIntegral.integral_congr
            intro a _ha
            have harg : d / ell + a / ell = (d + a) / ell := by ring
            have hlin : (ell * ((d + a) / ell) - d) / 2 = a / 2 := by
              field_simp [hell]
              ring
            simp [harg, hlin, mul_comm]
    _ = ell * ∫ x in d / ell..(d + 2 * L) / ell,
        Real.exp ((ell * x - d) / 2) * r x := by
          have hb0 : d / ell + 0 / ell = d / ell := by ring
          have hb1 : d / ell + 2 * L / ell = (d + 2 * L) / ell := by ring
          rw [hb0, hb1] at hsubst
          simpa [mul_comm] using hsubst

lemma intervalIntegral_exp_mul_comp_add_div_factored
    (r : Real -> Real) (ell L d : Real) (hell : ell ≠ 0) :
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) * r ((d + a) / ell) =
      ell * Real.exp (-(d / 2)) *
        ∫ x in d / ell..(d + 2 * L) / ell,
          Real.exp ((ell / 2) * x) * r x := by
  rw [intervalIntegral_exp_mul_comp_add_div r ell L d hell]
  have hfac :
      ∫ x in d / ell..(d + 2 * L) / ell,
        Real.exp ((ell * x - d) / 2) * r x =
      Real.exp (-(d / 2)) *
        ∫ x in d / ell..(d + 2 * L) / ell,
          Real.exp ((ell / 2) * x) * r x := by
    calc
      ∫ x in d / ell..(d + 2 * L) / ell,
        Real.exp ((ell * x - d) / 2) * r x
          = ∫ x in d / ell..(d + 2 * L) / ell,
              Real.exp (-(d / 2)) * (Real.exp ((ell / 2) * x) * r x) := by
              apply intervalIntegral.integral_congr
              intro x _hx
              change Real.exp ((ell * x - d) / 2) * r x =
                Real.exp (-(d / 2)) * (Real.exp ((ell / 2) * x) * r x)
              have hlin :
                  (ell * x - d) / 2 = -(d / 2) + ((ell / 2) * x) := by
                ring
              rw [hlin, Real.exp_add]
              ring
      _ = Real.exp (-(d / 2)) *
        ∫ x in d / ell..(d + 2 * L) / ell,
          Real.exp ((ell / 2) * x) * r x := by
          rw [intervalIntegral.integral_const_mul]
  rw [hfac]
  ring

theorem centeredBSplineR_continuous (k : Nat) :
    Continuous (centeredBSplineR k) := by
  unfold centeredBSplineR
  exact ((centeredCardinalBSpline_continuous_of_pos
    (bsplineAutocorrDegree k) (by unfold bsplineAutocorrDegree; omega)).comp
      (continuous_const.mul continuous_id)).div_const (bsplineAutocorrNorm k)

theorem bsplineAutocorrNorm_11_exact :
    bsplineAutocorrNorm 11 =
      ((75489558096433522049 : Real) / (269291841030051840000 : Real)) := by
  norm_num [bsplineAutocorrNorm, bsplineAutocorrDegree,
    centeredCardinalBSpline, positivePartPower, Finset.sum_range_succ, Nat.choose]

theorem bsplineAutocorrNorm_9_exact :
    bsplineAutocorrNorm 9 =
      ((37307713155613 : Real) / (121645100408832 : Real)) := by
  norm_num [bsplineAutocorrNorm, bsplineAutocorrDegree,
    centeredCardinalBSpline, positivePartPower, Finset.sum_range_succ, Nat.choose]

namespace CenteredCoeffAnalyticP0Import

theorem centeredBSplineP0KernelProfile_eq_transformed_integrals
    (k : Nat) (ell L d : Real) (hell : ell ≠ 0) :
    centeredBSplineP0KernelProfile k ell L d =
      ell * Real.exp (d / 2) *
        (∫ x in (d - 2 * L) / ell..d / ell,
          Real.exp (-(ell / 2) * x) * centeredBSplineR k x) +
      ell * Real.exp (-(d / 2)) *
        (∫ x in d / ell..(d + 2 * L) / ell,
          Real.exp ((ell / 2) * x) * centeredBSplineR k x) := by
  have hr : Continuous (centeredBSplineR k) := centeredBSplineR_continuous k
  have hsubInt : IntervalIntegrable
      (fun a : Real => Real.exp (a / 2) * centeredBSplineR k ((d - a) / ell))
      volume (0 : Real) (2 * L) := by
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (hr.comp (by continuity))).intervalIntegrable _ _
  have haddInt : IntervalIntegrable
      (fun a : Real => Real.exp (a / 2) * centeredBSplineR k ((d + a) / ell))
      volume (0 : Real) (2 * L) := by
    exact ((Real.continuous_exp.comp (by continuity)).mul
      (hr.comp (by continuity))).intervalIntegrable _ _
  unfold centeredBSplineP0KernelProfile
  calc
    ∫ a in (0 : Real)..(2 * L),
      Real.exp (a / 2) *
        (centeredBSplineR k ((d - a) / ell) + centeredBSplineR k ((d + a) / ell))
      = ∫ a in (0 : Real)..(2 * L),
          Real.exp (a / 2) * centeredBSplineR k ((d - a) / ell) +
            Real.exp (a / 2) * centeredBSplineR k ((d + a) / ell) := by
          apply intervalIntegral.integral_congr
          intro a _ha
          ring
    _ = (∫ a in (0 : Real)..(2 * L),
          Real.exp (a / 2) * centeredBSplineR k ((d - a) / ell)) +
        (∫ a in (0 : Real)..(2 * L),
          Real.exp (a / 2) * centeredBSplineR k ((d + a) / ell)) := by
          rw [intervalIntegral.integral_add hsubInt haddInt]
    _ = ell * Real.exp (d / 2) *
        (∫ x in (d - 2 * L) / ell..d / ell,
          Real.exp (-(ell / 2) * x) * centeredBSplineR k x) +
      ell * Real.exp (-(d / 2)) *
        (∫ x in d / ell..(d + 2 * L) / ell,
          Real.exp ((ell / 2) * x) * centeredBSplineR k x) := by
        rw [intervalIntegral_exp_mul_comp_sub_div_factored
          (centeredBSplineR k) ell L d hell]
        rw [intervalIntegral_exp_mul_comp_add_div_factored
          (centeredBSplineR k) ell L d hell]

end CenteredCoeffAnalyticP0Import
end PSDpd
end Q3
