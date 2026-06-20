import Mathlib.Analysis.Calculus.Taylor
import Q3.DigammaSeries
import Q3.DigammaRemainder
import Q3.Proofs.PSD_CenteredCoeffRawOmegaAChunkTaylorChecker
import Q3.Proofs.PSD_CenteredCoeffAnalyticABoundsBackend

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Typed landing surface for the first Step33A.1-A high-order shifted-digamma
endpoint.  This file fixes the exact point, generated center, and Bernoulli
m=6 main expression; it does not assert any numerical special-function bound.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open MeasureTheory
open scoped BigOperators

def step33Shift16DigammaPoint : Complex :=
  ((129 : Real) / (4 : Real) : Complex) +
    Complex.I * (((1 : Real) / (40 : Real) : Complex))

def step33Shift16DigammaFixedRe : Real :=
  (3457934361506642309616650171583002119 : Real) /
    (1000000000000000000000000000000000000 : Real)

def step33Shift16DigammaFixedIm : Real :=
  (393668171371225061774807882120813 : Real) /
    (500000000000000000000000000000000000 : Real)

def step33Shift16DigammaFixedCenter : Complex :=
  ((step33Shift16DigammaFixedRe : Real) : Complex) +
    Complex.I * (((step33Shift16DigammaFixedIm : Real) : Complex))

def step33Shift16DigammaTargetRadius : Real :=
  (1 : Real) / (2000000000000000000000 : Real)

def step33Shift16DigammaComponentRadius : Real :=
  (1 : Real) / (4000000000000000000000 : Real)

def step33Shift16DigammaM6MainComponentRadius : Real :=
  (1 : Real) / (10000000000000000000000 : Real)

def step33Shift16DigammaM6CenterReRadius : Real :=
  (1 : Real) / (10000000000000000000000 : Real)

def step33Shift16DigammaM6CenterImRadius : Real :=
  (1 : Real) / (100000000000000000000000 : Real)

def step33Shift16DigammaLogReCenter : Real :=
  (3473518343704403795597289462563 : Real) /
    (1000000000000000000000000000000 : Real)

def step33Shift16DigammaArgCenter : Real :=
  (775193643171780752451850408 : Real) /
    (1000000000000000000000000000000 : Real)

def step33Shift16DigammaLogReRadius : Real :=
  (1 : Real) / (1000000000000000000000000000000 : Real)

def step33Shift16DigammaArgRadius : Real :=
  (1 : Real) / (1000000000000000000000000000000 : Real)

private def step33Shift16DigammaLogReLower : Real :=
  (3473518343704403795597289462562 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16DigammaLogReUpper : Real :=
  (3473518343704403795597289462564 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16DigammaLogReExpQuarterUpper : Real :=
  (23830462015979011196396542615169812279827 : Real) /
    (10000000000000000000000000000000000000000 : Real)

private def step33Shift16DigammaLogReExpQuarterLower : Real :=
  (23830462015979011196396542615181727510834 : Real) /
    (10000000000000000000000000000000000000000 : Real)

theorem step33ComplexIPowFive : Complex.I ^ 5 = Complex.I := by
  rw [Complex.I_pow_eq_pow_mod 5]
  norm_num

theorem step33ComplexIPowSix : Complex.I ^ 6 = -1 := by
  rw [Complex.I_pow_eq_pow_mod 6]
  norm_num [Complex.I_sq]

theorem step33ComplexIPowSeven : Complex.I ^ 7 = -Complex.I := by
  rw [Complex.I_pow_eq_pow_mod 7]
  norm_num [Complex.I_pow_three]

theorem step33ComplexIPowEight : Complex.I ^ 8 = 1 := by
  rw [Complex.I_pow_eq_pow_mod 8]
  norm_num

theorem step33ComplexIPowNine : Complex.I ^ 9 = Complex.I := by
  rw [Complex.I_pow_eq_pow_mod 9]
  norm_num

theorem step33ComplexIPowTen : Complex.I ^ 10 = -1 := by
  rw [Complex.I_pow_eq_pow_mod 10]
  norm_num [Complex.I_sq]

theorem step33ComplexIPowEleven : Complex.I ^ 11 = -Complex.I := by
  rw [Complex.I_pow_eq_pow_mod 11]
  norm_num [Complex.I_pow_three]

theorem step33ComplexIPowTwelve : Complex.I ^ 12 = 1 := by
  rw [Complex.I_pow_eq_pow_mod 12]
  norm_num

theorem step33Shift16DigammaPoint_re_pos :
    0 < step33Shift16DigammaPoint.re := by
  norm_num [step33Shift16DigammaPoint]

theorem step33Shift16DigammaPoint_re_eq :
    step33Shift16DigammaPoint.re = (129 : Real) / (4 : Real) := by
  norm_num [step33Shift16DigammaPoint]

theorem step33Shift16DigammaPoint_eq_generated :
    step33Shift16DigammaPoint =
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
        ((1 : Real) / (20 : Real)) 16 + (16 : Complex) := by
  apply Complex.ext
  · norm_num [step33Shift16DigammaPoint,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]
  · norm_num [step33Shift16DigammaPoint,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]

theorem step33Shift16DigammaPoint_add_16_eq_generated_shift48 :
    step33Shift16DigammaPoint + (16 : Complex) =
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
        ((1 : Real) / (20 : Real)) 48 := by
  apply Complex.ext
  · norm_num [step33Shift16DigammaPoint,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]
  · norm_num [step33Shift16DigammaPoint,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg,
      CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightDigammaArg]

theorem step33Shift16DigammaPoint_ne_zero :
    step33Shift16DigammaPoint ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num [step33Shift16DigammaPoint] at hre

theorem step33Shift16DigammaLog_re_eq :
    (Complex.log step33Shift16DigammaPoint).re =
      Real.log ‖step33Shift16DigammaPoint‖ := by
  simp [Complex.log_re]

theorem step33Shift16DigammaPoint_normSq_eq :
    Complex.normSq step33Shift16DigammaPoint =
      (1664101 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_norm_eq_sqrt :
    ‖step33Shift16DigammaPoint‖ =
      Real.sqrt ((1664101 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_normSq_eq]

theorem step33Shift16DigammaPoint_add_one_normSq_eq :
    Complex.normSq (step33Shift16DigammaPoint + 1) =
      (1768901 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_one_norm_eq_sqrt :
    ‖step33Shift16DigammaPoint + 1‖ =
      Real.sqrt ((1768901 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_one_normSq_eq]

theorem step33Shift16DigammaPoint_add_one_add_one_normSq_eq :
    Complex.normSq ((step33Shift16DigammaPoint + (1 : Complex)) + 1) =
      (1876901 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_one_add_one_norm_eq_sqrt :
    ‖(step33Shift16DigammaPoint + (1 : Complex)) + 1‖ =
      Real.sqrt ((1876901 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_one_add_one_normSq_eq]

theorem step33Shift16DigammaPoint_add_two_normSq_eq :
    Complex.normSq (step33Shift16DigammaPoint + (2 : Complex)) =
      (1876901 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_two_norm_eq_sqrt :
    ‖step33Shift16DigammaPoint + (2 : Complex)‖ =
      Real.sqrt ((1876901 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_two_normSq_eq]

theorem step33Shift16DigammaPoint_add_two_add_one_normSq_eq :
    Complex.normSq ((step33Shift16DigammaPoint + (2 : Complex)) + 1) =
      (1988101 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_two_add_one_norm_eq_sqrt :
    ‖(step33Shift16DigammaPoint + (2 : Complex)) + 1‖ =
      Real.sqrt ((1988101 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_two_add_one_normSq_eq]

theorem step33Shift16DigammaPoint_add_three_normSq_eq :
    Complex.normSq (step33Shift16DigammaPoint + (3 : Complex)) =
      (1988101 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_three_norm_eq_sqrt :
    ‖step33Shift16DigammaPoint + (3 : Complex)‖ =
      Real.sqrt ((1988101 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_three_normSq_eq]

theorem step33Shift16DigammaPoint_add_three_add_one_normSq_eq :
    Complex.normSq ((step33Shift16DigammaPoint + (3 : Complex)) + 1) =
      (2102501 : Real) / (1600 : Real) := by
  norm_num [step33Shift16DigammaPoint, Complex.normSq_apply]

theorem step33Shift16DigammaPoint_add_three_add_one_norm_eq_sqrt :
    ‖(step33Shift16DigammaPoint + (3 : Complex)) + 1‖ =
      Real.sqrt ((2102501 : Real) / (1600 : Real)) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_three_add_one_normSq_eq]

theorem step33Shift16DigammaPoint_add_nat_normSq_eq (n : Nat) :
    Complex.normSq (step33Shift16DigammaPoint + (n : Complex)) =
      (((1290 : Real) + 40 * (n : Real)) ^ 2 + 1) / 1600 := by
  rw [step33Shift16DigammaPoint]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem step33Shift16DigammaPoint_add_nat_add_real_normSq_eq
    (n : Nat) (t : Real) :
    Complex.normSq (step33Shift16DigammaPoint + (((n : Real) + t) : Complex)) =
      (((1290 : Real) + 40 * (n : Real) + 40 * t) ^ 2 + 1) / 1600 := by
  rw [step33Shift16DigammaPoint]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  ring

theorem step33Shift16DigammaPoint_half_cell_normSq_le_reflect
    (n : Nat) {t : Real} (ht0 : 0 <= t) (hth : t <= 1 / 2) :
    Complex.normSq (step33Shift16DigammaPoint + (((n : Real) + t) : Complex)) <=
      Complex.normSq
        (step33Shift16DigammaPoint + (((n : Real) + (1 - t)) : Complex)) := by
  rw [step33Shift16DigammaPoint]
  simp [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  have hn0 : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have ht0' : 0 <= t := ht0
  nlinarith [ht0', hth, hn0]

theorem step33Shift16Bernoulli14Diff_nat_add_real_eq
    (n : Nat) {t : Real} (ht0 : 0 <= t) (ht1 : t <= 1) :
    Q3.bernoulli14Diff ((n : Real) + t) = Q3.bernoulli14 t := by
  have hx : ((n : Real) + t) ∈ Set.Icc (n : Real) (n + 1 : Real) := by
    constructor <;> nlinarith [ht0, ht1]
  have hcell := Q3.bernoulli14Diff_eq_cell_on_Icc n hx
  rw [hcell]
  unfold Q3.bernoulli14
  ring_nf

theorem step33Shift16Bernoulli14Diff_nat_add_one_sub_real_eq
    (n : Nat) {t : Real} (ht0 : 0 <= t) (ht1 : t <= 1) :
    Q3.bernoulli14Diff ((n : Real) + 1 - t) = Q3.bernoulli14 t := by
  have h :=
    step33Shift16Bernoulli14Diff_nat_add_real_eq n
      (t := 1 - t) (by nlinarith [ht1]) (by nlinarith [ht0])
  calc
    Q3.bernoulli14Diff ((n : Real) + 1 - t)
        = Q3.bernoulli14Diff ((n : Real) + (1 - t)) := by ring_nf
    _ = Q3.bernoulli14 (1 - t) := h
    _ = Q3.bernoulli14 t := Q3.bernoulli14_one_sub t

def step33Shift16Z0KernelSq (x : Real) : Real :=
  (x + (129 : Real) / 4) ^ 2 + ((1 : Real) / 40) ^ 2

def step33Shift16Z0KernelPow15 (x : Real) : Real :=
  step33Shift16Z0KernelSq x ^ (-(15 : Real) / 2)

theorem step33Shift16Z0KernelSq_pos (x : Real) :
    0 < step33Shift16Z0KernelSq x := by
  unfold step33Shift16Z0KernelSq
  nlinarith [sq_nonneg (x + (129 : Real) / 4), sq_nonneg ((1 : Real) / 40)]

theorem step33Shift16Z0KernelSq_eq_normSq (x : Real) :
    step33Shift16Z0KernelSq x =
      Complex.normSq ((x : Complex) + step33Shift16DigammaPoint) := by
  rw [step33Shift16DigammaPoint]
  simp [step33Shift16Z0KernelSq, Complex.normSq_apply, Complex.add_re,
    Complex.add_im]
  ring

theorem step33Shift16Z0KernelPow15_eq_inv_norm_pow15 (x : Real) :
    step33Shift16Z0KernelPow15 x =
      1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
  have hnorm_sq :
      ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2 =
        step33Shift16Z0KernelSq x := by
    calc
      ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2
          = Complex.normSq ((x : Complex) + step33Shift16DigammaPoint) := by
            simpa using (Complex.sq_norm ((x : Complex) + step33Shift16DigammaPoint))
      _ = step33Shift16Z0KernelSq x := by
            rw [← step33Shift16Z0KernelSq_eq_normSq x]
  have hpow :
      (‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2) ^ ((15 : Real) / 2) =
        ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
    have hbase :
        0 <= ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2 := by
      positivity
    calc
      (‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2) ^ ((15 : Real) / 2)
          = (‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2) ^
              ((1 / 2 : Real) * (15 : Real)) := by ring_nf
      _ = ((‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2) ^ (1 / 2 : Real)) ^
            (15 : Real) := by
            simpa using
              (Real.rpow_mul
                (x := ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2)
                hbase (1 / 2 : Real) (15 : Real))
      _ = (Real.sqrt (‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2)) ^
            (15 : Real) := by
            simp [Real.sqrt_eq_rpow]
      _ = ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ (15 : Real) := by
            simp
      _ = ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
            simp
  calc
    step33Shift16Z0KernelPow15 x
        = step33Shift16Z0KernelSq x ^ (-(15 : Real) / 2) := rfl
    _ = step33Shift16Z0KernelSq x ^ (-((15 : Real) / 2)) := by ring_nf
    _ = 1 / step33Shift16Z0KernelSq x ^ ((15 : Real) / 2) := by
          simpa [one_div] using
            (Real.rpow_neg (le_of_lt (step33Shift16Z0KernelSq_pos x))
              ((15 : Real) / 2))
    _ = 1 / (‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 2) ^ ((15 : Real) / 2) := by
          rw [hnorm_sq]
    _ = 1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
          rw [hpow]

theorem step33Shift16Z0KernelSq_hasDerivAt (x : Real) :
    HasDerivAt step33Shift16Z0KernelSq (2 * (x + (129 : Real) / 4)) x := by
  unfold step33Shift16Z0KernelSq
  have hlin : HasDerivAt (fun y : Real => y + (129 : Real) / 4) 1 x := by
    simpa [id_eq] using (hasDerivAt_id x).add_const ((129 : Real) / 4)
  have hsq := hlin.pow 2
  have hc : HasDerivAt (fun _ : Real => ((1 : Real) / 40) ^ 2) 0 x :=
    hasDerivAt_const x (((1 : Real) / 40) ^ 2)
  have h := hsq.add hc
  convert h using 1
  ring

theorem step33Shift16Z0KernelPow15_hasDerivAt (x : Real) :
    HasDerivAt step33Shift16Z0KernelPow15
      (-15 * (x + (129 : Real) / 4) *
        step33Shift16Z0KernelSq x ^ (-(17 : Real) / 2)) x := by
  unfold step33Shift16Z0KernelPow15
  have hs_deriv := step33Shift16Z0KernelSq_hasDerivAt x
  have hs_ne : step33Shift16Z0KernelSq x ≠ 0 :=
    ne_of_gt (step33Shift16Z0KernelSq_pos x)
  have hrpow :=
    (Real.hasDerivAt_rpow_const
      (x := step33Shift16Z0KernelSq x) (p := (-(15 : Real) / 2))
      (Or.inl hs_ne)).comp x hs_deriv
  convert hrpow using 1
  ring_nf

theorem step33Shift16Z0KernelPow17_hasDerivAt (x : Real) :
    HasDerivAt (fun y : Real => step33Shift16Z0KernelSq y ^ (-(17 : Real) / 2))
      (-17 * (x + (129 : Real) / 4) *
        step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2)) x := by
  have hs_deriv := step33Shift16Z0KernelSq_hasDerivAt x
  have hs_ne : step33Shift16Z0KernelSq x ≠ 0 :=
    ne_of_gt (step33Shift16Z0KernelSq_pos x)
  have hrpow :=
    (Real.hasDerivAt_rpow_const
      (x := step33Shift16Z0KernelSq x) (p := (-(17 : Real) / 2))
      (Or.inl hs_ne)).comp x hs_deriv
  convert hrpow using 1
  ring_nf

theorem step33Shift16Z0KernelPow15_deriv_hasDerivAt (x : Real) :
    HasDerivAt
      (fun y : Real =>
        -15 * (y + (129 : Real) / 4) *
          step33Shift16Z0KernelSq y ^ (-(17 : Real) / 2))
      (15 *
        (16 * (x + (129 : Real) / 4) ^ 2 - ((1 : Real) / 40) ^ 2) *
          step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2)) x := by
  have hlin :
      HasDerivAt (fun y : Real => -15 * (y + (129 : Real) / 4)) (-15) x := by
    have h0 : HasDerivAt (fun y : Real => y + (129 : Real) / 4) 1 x := by
      simpa [id_eq] using (hasDerivAt_id x).add_const ((129 : Real) / 4)
    simpa using h0.const_mul (-15 : Real)
  have hp := step33Shift16Z0KernelPow17_hasDerivAt x
  have h := hlin.mul hp
  convert h using 1
  have hpow :
      step33Shift16Z0KernelSq x ^ (-(17 : Real) / 2) =
        step33Shift16Z0KernelSq x *
          step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2) := by
    calc
      step33Shift16Z0KernelSq x ^ (-(17 : Real) / 2)
          = step33Shift16Z0KernelSq x ^ (1 + (-(19 : Real) / 2)) := by
            ring_nf
      _ = step33Shift16Z0KernelSq x ^ (1 : Real) *
            step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2) := by
            rw [Real.rpow_add (step33Shift16Z0KernelSq_pos x)]
      _ = step33Shift16Z0KernelSq x *
            step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2) := by
            simp
  rw [hpow]
  unfold step33Shift16Z0KernelSq
  ring_nf

theorem step33Shift16Z0KernelConvexNumerator_nonneg
    {x : Real} (hx : 0 <= x) :
    0 <= 16 * (x + (129 : Real) / 4) ^ 2 - ((1 : Real) / 40) ^ 2 := by
  nlinarith [sq_nonneg (x + (129 : Real) / 4), hx]

theorem step33Shift16Z0KernelPow15_second_deriv_nonneg_of_nonneg
    {x : Real} (hx : 0 <= x) :
    0 <=
      15 * (16 * (x + (129 : Real) / 4) ^ 2 - ((1 : Real) / 40) ^ 2) *
        step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2) := by
  have hnum := step33Shift16Z0KernelConvexNumerator_nonneg hx
  have hrpow : 0 <= step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2) :=
    Real.rpow_nonneg (le_of_lt (step33Shift16Z0KernelSq_pos x)) _
  exact mul_nonneg (mul_nonneg (by norm_num) hnum) hrpow

def step33Shift16Z0KernelPow15Deriv (x : Real) : Real :=
  -(15 * ((x + (129 : Real) / 4) *
    step33Shift16Z0KernelSq x ^ (-(17 : Real) / 2)))

theorem step33Shift16Z0KernelPow15Deriv_hasDerivAt (x : Real) :
    HasDerivAt step33Shift16Z0KernelPow15Deriv
      (15 * ((16 * (x + (129 : Real) / 4) ^ 2 - ((1 : Real) / 40) ^ 2) *
        step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2))) x := by
  change HasDerivAt
    (fun y : Real => -(15 * ((y + (129 : Real) / 4) *
      step33Shift16Z0KernelSq y ^ (-(17 : Real) / 2))))
    (15 * ((16 * (x + (129 : Real) / 4) ^ 2 - ((1 : Real) / 40) ^ 2) *
      step33Shift16Z0KernelSq x ^ (-(19 : Real) / 2))) x
  simpa [mul_assoc] using step33Shift16Z0KernelPow15_deriv_hasDerivAt x

theorem step33Shift16Z0KernelPow15Deriv_deriv_nonneg_of_nonneg
    {x : Real} (hx : 0 <= x) :
    0 <= deriv step33Shift16Z0KernelPow15Deriv x := by
  rw [(step33Shift16Z0KernelPow15Deriv_hasDerivAt x).deriv]
  simpa [mul_assoc] using
    step33Shift16Z0KernelPow15_second_deriv_nonneg_of_nonneg hx

theorem step33Shift16Z0KernelPow15Deriv_monotoneOn_Ici_zero :
    MonotoneOn step33Shift16Z0KernelPow15Deriv (Set.Ici (0 : Real)) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0 : Real)) ?hcont ?hdiff ?hderiv
  · intro x _hx
    exact ((step33Shift16Z0KernelPow15Deriv_hasDerivAt x).differentiableAt.continuousAt).continuousWithinAt
  · intro x _hx
    exact ((step33Shift16Z0KernelPow15Deriv_hasDerivAt x).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact step33Shift16Z0KernelPow15Deriv_deriv_nonneg_of_nonneg (le_of_lt hx)

def step33Shift16Z0KernelPow15Pair (n : Nat) (t : Real) : Real :=
  step33Shift16Z0KernelPow15 ((n : Real) + t) +
    step33Shift16Z0KernelPow15 ((n : Real) + 1 - t)

theorem step33Shift16Z0KernelPow15Pair_hasDerivAt
    (n : Nat) (t : Real) :
    HasDerivAt (step33Shift16Z0KernelPow15Pair n)
      (step33Shift16Z0KernelPow15Deriv ((n : Real) + t) -
        step33Shift16Z0KernelPow15Deriv ((n : Real) + 1 - t)) t := by
  have hleft_inner : HasDerivAt (fun u : Real => (n : Real) + u) 1 t := by
    simpa [add_comm] using (hasDerivAt_id t).const_add (n : Real)
  have hleft :=
    (step33Shift16Z0KernelPow15_hasDerivAt ((n : Real) + t)).comp t hleft_inner
  have hright_inner :
      HasDerivAt (fun u : Real => (n : Real) + 1 - u) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub ((n : Real) + 1)
  have hright :=
    (step33Shift16Z0KernelPow15_hasDerivAt ((n : Real) + 1 - t)).comp t
      hright_inner
  have h := hleft.add hright
  simpa [step33Shift16Z0KernelPow15Pair, step33Shift16Z0KernelPow15Deriv,
    sub_eq_add_neg, mul_assoc] using h

theorem step33Shift16Z0KernelPow15Pair_deriv_nonpos_on_Icc_zero_half
    (n : Nat) {t : Real} (ht0 : 0 <= t) (hth : t <= 1 / 2) :
    deriv (step33Shift16Z0KernelPow15Pair n) t <= 0 := by
  rw [(step33Shift16Z0KernelPow15Pair_hasDerivAt n t).deriv]
  have hn0 : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hleft_mem : (n : Real) + t ∈ Set.Ici (0 : Real) := by
    exact add_nonneg hn0 ht0
  have hone_sub : 0 <= (1 : Real) - t := by
    nlinarith [hth]
  have hright_mem : (n : Real) + 1 - t ∈ Set.Ici (0 : Real) := by
    have hbase : 0 <= (n : Real) + ((1 : Real) - t) :=
      add_nonneg hn0 hone_sub
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hbase
  have hle : (n : Real) + t <= (n : Real) + 1 - t := by
    nlinarith [hth]
  have hmono :=
    step33Shift16Z0KernelPow15Deriv_monotoneOn_Ici_zero hleft_mem hright_mem hle
  exact sub_nonpos.mpr hmono

theorem step33Shift16Z0KernelPow15Pair_antitoneOn_Icc_zero_half
    (n : Nat) :
    AntitoneOn (step33Shift16Z0KernelPow15Pair n)
      (Set.Icc (0 : Real) (1 / 2)) := by
  refine antitoneOn_of_deriv_nonpos (convex_Icc (0 : Real) (1 / 2)) ?hcont ?hdiff ?hderiv
  · intro x _hx
    exact ((step33Shift16Z0KernelPow15Pair_hasDerivAt n x).differentiableAt.continuousAt).continuousWithinAt
  · intro x _hx
    exact ((step33Shift16Z0KernelPow15Pair_hasDerivAt n x).differentiableAt).differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact step33Shift16Z0KernelPow15Pair_deriv_nonpos_on_Icc_zero_half n
      (le_of_lt hx.1) (le_of_lt hx.2)

theorem step33Shift16B14HalfCellPairIntegral_nonneg (n : Nat) :
    0 <= ∫ t in (0 : Real)..(1 / 2 : Real),
      Q3.bernoulli14 t * step33Shift16Z0KernelPow15Pair n t := by
  let u : Real → Real := Q3.bernoulli14Primitive
  let u' : Real → Real := Q3.bernoulli14
  let v : Real → Real := step33Shift16Z0KernelPow15Pair n
  let v' : Real → Real := fun t =>
    step33Shift16Z0KernelPow15Deriv ((n : Real) + t) -
      step33Shift16Z0KernelPow15Deriv ((n : Real) + 1 - t)
  have hu : ∀ x ∈ Set.uIcc (0 : Real) (1 / 2 : Real), HasDerivAt u (u' x) x := by
    intro x _hx
    simpa [u, u'] using Q3.bernoulli14Primitive_hasDerivAt x
  have hv : ∀ x ∈ Set.uIcc (0 : Real) (1 / 2 : Real), HasDerivAt v (v' x) x := by
    intro x _hx
    simpa [v, v'] using step33Shift16Z0KernelPow15Pair_hasDerivAt n x
  have hcont_u : Continuous u := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (Q3.bernoulli14Primitive_hasDerivAt x).continuousAt
  have hcont_u' : Continuous u' := by
    dsimp [u']
    unfold Q3.bernoulli14
    fun_prop
  have hcont_deriv : Continuous step33Shift16Z0KernelPow15Deriv := by
    refine continuous_iff_continuousAt.mpr ?_
    intro x
    exact (step33Shift16Z0KernelPow15Deriv_hasDerivAt x).continuousAt
  have hcont_v' : Continuous v' := by
    have hleft : Continuous fun x : Real =>
        step33Shift16Z0KernelPow15Deriv ((n : Real) + x) := by
      exact hcont_deriv.comp (by fun_prop)
    have hright : Continuous fun x : Real =>
        step33Shift16Z0KernelPow15Deriv ((n : Real) + 1 - x) := by
      exact hcont_deriv.comp (by fun_prop)
    simpa [v'] using hleft.sub hright
  have hu'_int : IntervalIntegrable u' volume (0 : Real) (1 / 2 : Real) := by
    exact hcont_u'.intervalIntegrable _ _
  have hv'_int : IntervalIntegrable v' volume (0 : Real) (1 / 2 : Real) := by
    exact hcont_v'.intervalIntegrable _ _
  have hparts :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul
      (a := (0 : Real)) (b := (1 / 2 : Real))
      (u := u) (u' := u') (v := v) (v' := v') hu hv hu'_int hv'_int
  have hsum_parts :
      (∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x) +
        ∫ x in (0 : Real)..(1 / 2 : Real), u' x * v x =
          u (1 / 2 : Real) * v (1 / 2 : Real) - u (0 : Real) * v (0 : Real) := by
    have hparts' := (eq_sub_iff_add_eq).1 hparts
    simpa [add_comm, add_left_comm, add_assoc] using hparts'
  have hparts_rev :
      ∫ x in (0 : Real)..(1 / 2 : Real), u' x * v x =
        u (1 / 2 : Real) * v (1 / 2 : Real) - u (0 : Real) * v (0 : Real) -
          ∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x := by
    refine (eq_sub_iff_add_eq).2 ?_
    simpa [add_comm, add_left_comm, add_assoc] using hsum_parts
  have hboundary :
      u (1 / 2 : Real) * v (1 / 2 : Real) - u (0 : Real) * v (0 : Real) = 0 := by
    have hu_half : u (1 / 2 : Real) = 0 := by
      simpa [u] using Q3.bernoulli14Primitive_half
    have hu_zero : u (0 : Real) = 0 := by
      simpa [u] using Q3.bernoulli14Primitive_zero
    rw [hu_half, hu_zero]
    ring
  have hmain_eq :
      ∫ x in (0 : Real)..(1 / 2 : Real), u' x * v x =
        -∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x := by
    calc
      ∫ x in (0 : Real)..(1 / 2 : Real), u' x * v x =
          u (1 / 2 : Real) * v (1 / 2 : Real) - u (0 : Real) * v (0 : Real) -
            ∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x := hparts_rev
      _ = -∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x := by
          rw [hboundary]
          ring
  have huv'_int : IntervalIntegrable (fun x : Real => u x * v' x) volume
      (0 : Real) (1 / 2 : Real) := by
    exact (hcont_u.mul hcont_v').intervalIntegrable _ _
  have hzero_int : IntervalIntegrable (fun _ : Real => (0 : Real)) volume
      (0 : Real) (1 / 2 : Real) := by
    exact intervalIntegrable_const (μ := volume) (a := (0 : Real))
      (b := (1 / 2 : Real)) (c := (0 : Real))
  have hpoint_nonpos :
      ∀ x ∈ Set.Icc (0 : Real) (1 / 2 : Real), u x * v' x <= 0 := by
    intro x hx
    have hu_nonneg : 0 <= u x := by
      simpa [u] using Q3.bernoulli14Primitive_nonneg_on_Icc_zero_half hx.1 hx.2
    have hv_nonpos : v' x <= 0 := by
      have hderiv := step33Shift16Z0KernelPow15Pair_deriv_nonpos_on_Icc_zero_half n
        hx.1 hx.2
      rw [(step33Shift16Z0KernelPow15Pair_hasDerivAt n x).deriv] at hderiv
      simpa [v'] using hderiv
    exact mul_nonpos_of_nonneg_of_nonpos hu_nonneg hv_nonpos
  have h_uv'_le_zero_int :
      (∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x) <=
        ∫ x in (0 : Real)..(1 / 2 : Real), (0 : Real) := by
    exact intervalIntegral.integral_mono_on
      (a := (0 : Real)) (b := (1 / 2 : Real)) (μ := volume)
      (f := fun x : Real => u x * v' x) (g := fun _ : Real => (0 : Real))
      (hab := by norm_num) (hf := huv'_int) (hg := hzero_int) hpoint_nonpos
  have h_uv'_nonpos :
      (∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x) <= 0 := by
    simpa using h_uv'_le_zero_int
  have h_nonneg_neg :
      0 <= -∫ x in (0 : Real)..(1 / 2 : Real), u x * v' x := by
    linarith
  change 0 <= ∫ t in (0 : Real)..(1 / 2 : Real), u' t * v t
  rw [hmain_eq]
  exact h_nonneg_neg

theorem step33Shift16B14KernelCellIntegral_eq_halfCellPair (n : Nat) :
    (∫ t in (0 : Real)..1,
      Q3.bernoulli14Diff ((n : Real) + t) *
        step33Shift16Z0KernelPow15 ((n : Real) + t)) =
    ∫ t in (0 : Real)..(1 / 2 : Real),
      Q3.bernoulli14 t * step33Shift16Z0KernelPow15Pair n t := by
  let A : Real → Real := fun t =>
    Q3.bernoulli14 t * step33Shift16Z0KernelPow15 ((n : Real) + t)
  have hcont_kernel : Continuous fun t : Real =>
      step33Shift16Z0KernelPow15 ((n : Real) + t) := by
    have hcont_global : Continuous step33Shift16Z0KernelPow15 := by
      refine continuous_iff_continuousAt.mpr ?_
      intro x
      exact (step33Shift16Z0KernelPow15_hasDerivAt x).continuousAt
    exact hcont_global.comp (by fun_prop)
  have hcont_b14 : Continuous Q3.bernoulli14 := by
    unfold Q3.bernoulli14
    fun_prop
  have hcont_A : Continuous A := by
    simpa [A] using hcont_b14.mul hcont_kernel
  have hleft_to_A :
      (∫ t in (0 : Real)..1,
        Q3.bernoulli14Diff ((n : Real) + t) *
          step33Shift16Z0KernelPow15 ((n : Real) + t)) =
        ∫ t in (0 : Real)..1, A t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Set.Icc (0 : Real) 1 := by
      simpa using ht
    have hb := step33Shift16Bernoulli14Diff_nat_add_real_eq n htIcc.1 htIcc.2
    simp [A, hb]
  have hsplit :
      (∫ t in (0 : Real)..1, A t) =
        (∫ t in (0 : Real)..(1 / 2 : Real), A t) +
          ∫ t in (1 / 2 : Real)..1, A t := by
    have h01 : IntervalIntegrable A volume (0 : Real) (1 / 2 : Real) :=
      hcont_A.intervalIntegrable _ _
    have h12 : IntervalIntegrable A volume (1 / 2 : Real) 1 :=
      hcont_A.intervalIntegrable _ _
    rw [← intervalIntegral.integral_add_adjacent_intervals h01 h12]
  have hreflect :
      (∫ t in (1 / 2 : Real)..1, A t) =
        ∫ t in (0 : Real)..(1 / 2 : Real), A (1 - t) := by
    have hcomp := intervalIntegral.integral_comp_sub_left (f := A)
      (d := (1 : Real)) (a := (0 : Real)) (b := (1 / 2 : Real))
    convert hcomp.symm using 1
    ring_nf
  have hadd :
      (∫ t in (0 : Real)..(1 / 2 : Real), A t) +
        (∫ t in (0 : Real)..(1 / 2 : Real), A (1 - t)) =
          ∫ t in (0 : Real)..(1 / 2 : Real), A t + A (1 - t) := by
    have hA : IntervalIntegrable A volume (0 : Real) (1 / 2 : Real) :=
      hcont_A.intervalIntegrable _ _
    have hA_reflect :
        IntervalIntegrable (fun t : Real => A (1 - t)) volume
          (0 : Real) (1 / 2 : Real) := by
      exact (hcont_A.comp (by fun_prop)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_add hA hA_reflect]
  have hpair :
      (∫ t in (0 : Real)..(1 / 2 : Real), A t + A (1 - t)) =
        ∫ t in (0 : Real)..(1 / 2 : Real),
          Q3.bernoulli14 t * step33Shift16Z0KernelPow15Pair n t := by
    refine intervalIntegral.integral_congr ?_
    intro t _ht
    have hb : Q3.bernoulli14 (1 - t) = Q3.bernoulli14 t :=
      Q3.bernoulli14_one_sub t
    dsimp [A, step33Shift16Z0KernelPow15Pair]
    rw [hb]
    ring_nf
  calc
    (∫ t in (0 : Real)..1,
      Q3.bernoulli14Diff ((n : Real) + t) *
        step33Shift16Z0KernelPow15 ((n : Real) + t))
        = ∫ t in (0 : Real)..1, A t := hleft_to_A
    _ = (∫ t in (0 : Real)..(1 / 2 : Real), A t) +
          ∫ t in (1 / 2 : Real)..1, A t := hsplit
    _ = (∫ t in (0 : Real)..(1 / 2 : Real), A t) +
          ∫ t in (0 : Real)..(1 / 2 : Real), A (1 - t) := by
          rw [hreflect]
    _ = ∫ t in (0 : Real)..(1 / 2 : Real), A t + A (1 - t) := hadd
    _ = ∫ t in (0 : Real)..(1 / 2 : Real),
          Q3.bernoulli14 t * step33Shift16Z0KernelPow15Pair n t := hpair

theorem step33Shift16B14KernelCellIntegral_nonneg (n : Nat) :
    0 <= ∫ t in (0 : Real)..1,
      Q3.bernoulli14Diff ((n : Real) + t) *
        step33Shift16Z0KernelPow15 ((n : Real) + t) := by
  rw [step33Shift16B14KernelCellIntegral_eq_halfCellPair n]
  exact step33Shift16B14HalfCellPairIntegral_nonneg n

theorem step33Shift16B14NormKernelParamCellIntegral_nonneg (n : Nat) :
    0 <= ∫ t in (0 : Real)..1,
      Q3.bernoulli14Diff ((n : Real) + t) /
        ‖((((n : Real) + t : Real) : Complex) + step33Shift16DigammaPoint)‖ ^ 15 := by
  have h := step33Shift16B14KernelCellIntegral_nonneg n
  convert h using 1
  refine intervalIntegral.integral_congr ?_
  intro t _ht
  dsimp
  rw [step33Shift16Z0KernelPow15_eq_inv_norm_pow15 ((n : Real) + t)]
  ring_nf

theorem step33Shift16B14NormKernelCellIntegral_nonneg (n : Nat) :
    0 <= ∫ x in (n : Real)..(n + 1 : Real),
      Q3.bernoulli14Diff x /
        ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
  have h := step33Shift16B14NormKernelParamCellIntegral_nonneg n
  let F : Real → Real := fun x =>
    Q3.bernoulli14Diff x /
      ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15
  have hcomp :=
    intervalIntegral.integral_comp_add_left (f := F) (d := (n : Real))
      (a := (0 : Real)) (b := (1 : Real))
  have hcell :
      (∫ t in (0 : Real)..1,
        Q3.bernoulli14Diff ((n : Real) + t) /
          ‖((((n : Real) + t : Real) : Complex) + step33Shift16DigammaPoint)‖ ^ 15) =
        ∫ x in (n : Real)..(n + 1 : Real), F x := by
    calc
      (∫ t in (0 : Real)..1,
        Q3.bernoulli14Diff ((n : Real) + t) /
          ‖((((n : Real) + t : Real) : Complex) + step33Shift16DigammaPoint)‖ ^ 15)
          = ∫ t in (0 : Real)..1, F ((n : Real) + t) := by
              rfl
      _ = ∫ x in (n : Real) + (0 : Real)..(n : Real) + (1 : Real), F x := by
              exact hcomp
      _ = ∫ x in (n : Real)..(n + 1 : Real), F x := by
              convert rfl using 1
              ring_nf
  rw [← hcell]
  exact h

theorem step33Shift16B14NormKernelFinitePrefix_nonneg (N : Nat) :
    0 <= ∫ x in (0 : Real)..(N : Real),
      Q3.bernoulli14Diff x /
        ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
  let F : Real → Real := fun x =>
    Q3.bernoulli14Diff x /
      ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15
  have hIoiInt : IntegrableOn F (Set.Ioi (0 : Real)) volume := by
    simpa [F, IntegrableOn] using
      Q3.integrable_bernoulli14Diff_kernel_norm_pow15 step33Shift16DigammaPoint
        step33Shift16DigammaPoint_re_pos
  have hsum :=
    intervalIntegral.sum_integral_adjacent_intervals
      (f := F) (μ := volume) (a := fun k : Nat => (k : Real)) (n := N)
      (by
        intro k _hk
        have hle : (k : Real) <= ((k + 1 : Nat) : Real) := by
          exact_mod_cast Nat.le_succ k
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
        exact hIoiInt.mono_set (by
          intro x hx
          exact lt_of_le_of_lt (Nat.cast_nonneg k) hx.1))
  have hsum' :
      (∑ k ∈ Finset.range N,
        ∫ x in (k : Real)..((k + 1 : Nat) : Real), F x) =
        ∫ x in (0 : Real)..(N : Real), F x := by
    simpa using hsum
  change 0 <= ∫ x in (0 : Real)..(N : Real), F x
  rw [← hsum']
  refine Finset.sum_nonneg ?_
  intro k _hk
  simpa [F, Nat.cast_add, Nat.cast_one] using
    step33Shift16B14NormKernelCellIntegral_nonneg k

theorem step33Shift16B14NormKernelWeightedIoi_nonneg :
    0 <= ∫ x in Set.Ioi (0 : Real),
      Q3.bernoulli14Diff x /
        ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
  let F : Real → Real := fun x =>
    Q3.bernoulli14Diff x /
      ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15
  have hIoiInt : IntegrableOn F (Set.Ioi (0 : Real)) volume := by
    simpa [F, IntegrableOn] using
      Q3.integrable_bernoulli14Diff_kernel_norm_pow15 step33Shift16DigammaPoint
        step33Shift16DigammaPoint_re_pos
  have hlim :
      Filter.Tendsto
        (fun N : Nat => ∫ x in (0 : Real)..(N : Real), F x)
        Filter.atTop
        (nhds (∫ x in Set.Ioi (0 : Real), F x)) := by
    simpa using
      (intervalIntegral_tendsto_integral_Ioi (a := (0 : Real))
        (f := F) (μ := volume) (b := fun N : Nat => (N : Real)) (l := Filter.atTop)
        hIoiInt tendsto_natCast_atTop_atTop)
  have hnonneg :
      ∀ N : Nat, 0 <= ∫ x in (0 : Real)..(N : Real), F x := by
    intro N
    simpa [F] using step33Shift16B14NormKernelFinitePrefix_nonneg N
  have hmain : 0 <= ∫ x in Set.Ioi (0 : Real), F x :=
    ge_of_tendsto' hlim hnonneg
  simpa [F] using hmain

theorem step33Shift16B14ShiftedIoiNorm_le :
    ‖∫ x in Set.Ioi (0 : Real),
        ((Q3.bernoulli14Diff x : Complex) - (7 / 6 : Complex)) /
          ((x : Complex) + step33Shift16DigammaPoint) ^ 15‖ <=
      ((7 : Real) / (6 : Real)) *
        ∫ x in Set.Ioi (0 : Real),
          1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 := by
  exact
    Q3.shiftedB14Diff_Ioi_norm_le_of_weighted_nonneg
      step33Shift16DigammaPoint step33Shift16DigammaPoint_re_pos
      step33Shift16B14NormKernelWeightedIoi_nonneg

theorem step33_shift16_digamma_m6_integral_remainder_bound :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint := by
  exact
    Q3.digammaM6IntegralRemainderBound_of_shiftedB14Diff_norm_bound
      step33Shift16DigammaPoint step33Shift16DigammaPoint_re_pos
      step33Shift16B14ShiftedIoiNorm_le

theorem step33Shift16DigammaPoint_add_nat_norm_eq_sqrt (n : Nat) :
    ‖step33Shift16DigammaPoint + (n : Complex)‖ =
      Real.sqrt ((((1290 : Real) + 40 * (n : Real)) ^ 2 + 1) / 1600) := by
  rw [Complex.norm_def, step33Shift16DigammaPoint_add_nat_normSq_eq]

theorem step33Shift16DigammaPoint_norm_ge_32 :
    (32 : Real) <= ‖step33Shift16DigammaPoint‖ := by
  rw [step33Shift16DigammaPoint_norm_eq_sqrt]
  exact (Real.le_sqrt
    (x := (32 : Real)) (y := ((1664101 : Real) / (1600 : Real)))
    (by norm_num) (by norm_num)).2 (by norm_num)

theorem step33Shift16DigammaLog_re_eq_log_sqrt :
    (Complex.log step33Shift16DigammaPoint).re =
      Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) := by
  rw [step33Shift16DigammaLog_re_eq, step33Shift16DigammaPoint_norm_eq_sqrt]

theorem step33Shift16DigammaLog_im_eq_arg :
    (Complex.log step33Shift16DigammaPoint).im =
      Complex.arg step33Shift16DigammaPoint := by
  simp [Complex.log_im]

private theorem step33Shift16DigammaLogRe_expLowerQuarter_le :
    Real.exp (step33Shift16DigammaLogReLower / 4) <=
      step33Shift16DigammaLogReExpQuarterUpper := by
  have hx0 : (0 : Real) <= step33Shift16DigammaLogReLower / 4 := by
    norm_num [step33Shift16DigammaLogReLower]
  have hx1 : step33Shift16DigammaLogReLower / 4 <= 1 := by
    norm_num [step33Shift16DigammaLogReLower]
  have hTaylor :
      (∑ m ∈ Finset.range 40,
          (step33Shift16DigammaLogReLower / 4) ^ m / (Nat.factorial m)) +
        (step33Shift16DigammaLogReLower / 4) ^ 40 * (40 + 1) /
          (Nat.factorial 40 * 40) <=
        step33Shift16DigammaLogReExpQuarterUpper := by
    norm_num [step33Shift16DigammaLogReLower,
      step33Shift16DigammaLogReExpQuarterUpper]
  exact Q3.Proofs.PrimeCert.exp_le_of_taylor_bound
    (x := step33Shift16DigammaLogReLower / 4)
    (b := step33Shift16DigammaLogReExpQuarterUpper)
    hx0 hx1 (n := 40) (by decide) hTaylor

private theorem step33Shift16DigammaLogRe_expQuarterLower_le :
    step33Shift16DigammaLogReExpQuarterLower <=
      Real.exp (step33Shift16DigammaLogReUpper / 4) := by
  have hx0 : (0 : Real) <= step33Shift16DigammaLogReUpper / 4 := by
    norm_num [step33Shift16DigammaLogReUpper]
  have hsum :
      step33Shift16DigammaLogReExpQuarterLower <=
        ∑ m ∈ Finset.range 41,
          (step33Shift16DigammaLogReUpper / 4) ^ m / (Nat.factorial m) := by
    norm_num [step33Shift16DigammaLogReUpper,
      step33Shift16DigammaLogReExpQuarterLower]
  have hle :
      (∑ m ∈ Finset.range 41,
          (step33Shift16DigammaLogReUpper / 4) ^ m / (Nat.factorial m)) <=
        Real.exp (step33Shift16DigammaLogReUpper / 4) := by
    simpa using
      (Real.sum_le_exp_of_nonneg hx0 41)
  exact hsum.trans hle

private theorem step33Shift16DigammaLogRe_expLowerSq_le_normSq :
    (Real.exp step33Shift16DigammaLogReLower) ^ 2 <=
      ((1664101 : Real) / (1600 : Real)) := by
  have hpow :
      Real.exp step33Shift16DigammaLogReLower <=
        step33Shift16DigammaLogReExpQuarterUpper ^ 4 := by
    exact Q3.Proofs.PrimeCert.exp_le_pow_of_div_le
      (x := step33Shift16DigammaLogReLower)
      (b := step33Shift16DigammaLogReExpQuarterUpper)
      (n := 4) (by decide)
      step33Shift16DigammaLogRe_expLowerQuarter_le
  have hpow2a :
      (Real.exp step33Shift16DigammaLogReLower) ^ 2 <=
        (step33Shift16DigammaLogReExpQuarterUpper ^ 4) ^ 2 := by
    exact pow_le_pow_left₀
      (Real.exp_nonneg step33Shift16DigammaLogReLower) hpow 2
  have hpow2 :
      (Real.exp step33Shift16DigammaLogReLower) ^ 2 <=
        step33Shift16DigammaLogReExpQuarterUpper ^ 8 := by
    convert hpow2a using 1
    ring
  have hb :
      step33Shift16DigammaLogReExpQuarterUpper ^ 8 <=
        ((1664101 : Real) / (1600 : Real)) := by
    norm_num [step33Shift16DigammaLogReExpQuarterUpper]
  exact hpow2.trans hb

private theorem step33Shift16DigammaLogRe_normSq_le_expUpperSq :
    ((1664101 : Real) / (1600 : Real)) <=
      (Real.exp step33Shift16DigammaLogReUpper) ^ 2 := by
  have hpow :
      step33Shift16DigammaLogReExpQuarterLower ^ 4 <=
        Real.exp step33Shift16DigammaLogReUpper := by
    exact Q3.Proofs.PrimeCert.pow_le_exp_of_le_div
      (x := step33Shift16DigammaLogReUpper)
      (a := step33Shift16DigammaLogReExpQuarterLower)
      (n := 4) (by decide)
      (by norm_num [step33Shift16DigammaLogReExpQuarterLower])
      step33Shift16DigammaLogRe_expQuarterLower_le
  have hpow2a :
      (step33Shift16DigammaLogReExpQuarterLower ^ 4) ^ 2 <=
        (Real.exp step33Shift16DigammaLogReUpper) ^ 2 := by
    exact pow_le_pow_left₀
      (by positivity :
        (0 : Real) <= step33Shift16DigammaLogReExpQuarterLower ^ 4)
      hpow 2
  have hpow2 :
      step33Shift16DigammaLogReExpQuarterLower ^ 8 <=
        (Real.exp step33Shift16DigammaLogReUpper) ^ 2 := by
    convert hpow2a using 1
    ring
  have hb :
      ((1664101 : Real) / (1600 : Real)) <=
        step33Shift16DigammaLogReExpQuarterLower ^ 8 := by
    norm_num [step33Shift16DigammaLogReExpQuarterLower]
  exact hb.trans hpow2

theorem step33Shift16DigammaLogReInterval :
    step33Shift16DigammaLogReLower <=
        Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) ∧
      Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) <=
        step33Shift16DigammaLogReUpper := by
  have hsqrt_pos :
      0 < Real.sqrt ((1664101 : Real) / (1600 : Real)) := by
    exact Real.sqrt_pos.mpr (by norm_num)
  constructor
  · exact Q3.Proofs.PrimeCert.le_log_of_exp_le
      (y := Real.sqrt ((1664101 : Real) / (1600 : Real)))
      hsqrt_pos
      ((Real.le_sqrt
          (Real.exp_nonneg step33Shift16DigammaLogReLower)
          (by norm_num)).2
        step33Shift16DigammaLogRe_expLowerSq_le_normSq)
  · exact Q3.Proofs.PrimeCert.log_le_of_le_exp
      (x := Real.sqrt ((1664101 : Real) / (1600 : Real)))
      hsqrt_pos
      ((Real.sqrt_le_iff).2
        ⟨Real.exp_nonneg step33Shift16DigammaLogReUpper,
          step33Shift16DigammaLogRe_normSq_le_expUpperSq⟩)

theorem step33Shift16DigammaLogRe_abs :
    |Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) -
        step33Shift16DigammaLogReCenter| <=
      step33Shift16DigammaLogReRadius := by
  have h := step33Shift16DigammaLogReInterval
  have hmid :
      step33Shift16DigammaLogReLower =
        step33Shift16DigammaLogReCenter -
          step33Shift16DigammaLogReRadius := by
    norm_num [step33Shift16DigammaLogReLower,
      step33Shift16DigammaLogReCenter, step33Shift16DigammaLogReRadius]
  have hhi :
      step33Shift16DigammaLogReUpper =
        step33Shift16DigammaLogReCenter +
          step33Shift16DigammaLogReRadius := by
    norm_num [step33Shift16DigammaLogReUpper,
      step33Shift16DigammaLogReCenter, step33Shift16DigammaLogReRadius]
  rw [abs_sub_le_iff]
  constructor
  · rw [hhi] at h
    linarith [h.2]
  · rw [hmid] at h
    linarith [h.1]

private def step33Shift16DigammaArgRatio : Real :=
  (1 : Real) / (1290 : Real)

private def step33Shift16DigammaPointAddOneArgRatio : Real :=
  (1 : Real) / (1330 : Real)

private def step33Shift16DigammaPointAddTwoArgRatio : Real :=
  (1 : Real) / (1370 : Real)

private def step33Shift16DigammaPointAddThreeArgRatio : Real :=
  (1 : Real) / (1410 : Real)

private def step33Shift16DigammaPointAddFourArgRatio : Real :=
  (1 : Real) / (1450 : Real)

private theorem step33Shift16DigammaArg_eq_arctan :
    Complex.arg step33Shift16DigammaPoint =
      Real.arctan step33Shift16DigammaArgRatio := by
  have hre : 0 < step33Shift16DigammaPoint.re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg step33Shift16DigammaPoint ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg step33Shift16DigammaPoint
  have hratio :
      step33Shift16DigammaPoint.im / step33Shift16DigammaPoint.re =
        step33Shift16DigammaArgRatio := by
    norm_num [step33Shift16DigammaPoint, step33Shift16DigammaArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg step33Shift16DigammaPoint)
      (y := step33Shift16DigammaArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_one_arg_eq_arctan :
    Complex.arg (step33Shift16DigammaPoint + 1) =
      Real.arctan step33Shift16DigammaPointAddOneArgRatio := by
  have hre : 0 < (step33Shift16DigammaPoint + 1).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg (step33Shift16DigammaPoint + 1) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg (step33Shift16DigammaPoint + 1)
  have hratio :
      (step33Shift16DigammaPoint + 1).im /
          (step33Shift16DigammaPoint + 1).re =
        step33Shift16DigammaPointAddOneArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddOneArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg (step33Shift16DigammaPoint + 1))
      (y := step33Shift16DigammaPointAddOneArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_one_add_one_arg_eq_arctan :
    Complex.arg ((step33Shift16DigammaPoint + (1 : Complex)) + 1) =
      Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
  have hre : 0 < ((step33Shift16DigammaPoint + (1 : Complex)) + 1).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg ((step33Shift16DigammaPoint + (1 : Complex)) + 1) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg
    ((step33Shift16DigammaPoint + (1 : Complex)) + 1)
  have hratio :
      ((step33Shift16DigammaPoint + (1 : Complex)) + 1).im /
          ((step33Shift16DigammaPoint + (1 : Complex)) + 1).re =
        step33Shift16DigammaPointAddTwoArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddTwoArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg ((step33Shift16DigammaPoint + (1 : Complex)) + 1))
      (y := step33Shift16DigammaPointAddTwoArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_two_arg_eq_arctan :
    Complex.arg (step33Shift16DigammaPoint + (2 : Complex)) =
      Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
  have hre : 0 < (step33Shift16DigammaPoint + (2 : Complex)).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg (step33Shift16DigammaPoint + (2 : Complex)) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg (step33Shift16DigammaPoint + (2 : Complex))
  have hratio :
      (step33Shift16DigammaPoint + (2 : Complex)).im /
          (step33Shift16DigammaPoint + (2 : Complex)).re =
        step33Shift16DigammaPointAddTwoArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddTwoArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg (step33Shift16DigammaPoint + (2 : Complex)))
      (y := step33Shift16DigammaPointAddTwoArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_two_add_one_arg_eq_arctan :
    Complex.arg ((step33Shift16DigammaPoint + (2 : Complex)) + 1) =
      Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
  have hre : 0 < ((step33Shift16DigammaPoint + (2 : Complex)) + 1).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg ((step33Shift16DigammaPoint + (2 : Complex)) + 1) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg
    ((step33Shift16DigammaPoint + (2 : Complex)) + 1)
  have hratio :
      ((step33Shift16DigammaPoint + (2 : Complex)) + 1).im /
          ((step33Shift16DigammaPoint + (2 : Complex)) + 1).re =
        step33Shift16DigammaPointAddThreeArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddThreeArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg ((step33Shift16DigammaPoint + (2 : Complex)) + 1))
      (y := step33Shift16DigammaPointAddThreeArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_three_arg_eq_arctan :
    Complex.arg (step33Shift16DigammaPoint + (3 : Complex)) =
      Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
  have hre : 0 < (step33Shift16DigammaPoint + (3 : Complex)).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg (step33Shift16DigammaPoint + (3 : Complex)) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg (step33Shift16DigammaPoint + (3 : Complex))
  have hratio :
      (step33Shift16DigammaPoint + (3 : Complex)).im /
          (step33Shift16DigammaPoint + (3 : Complex)).re =
        step33Shift16DigammaPointAddThreeArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddThreeArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg (step33Shift16DigammaPoint + (3 : Complex)))
      (y := step33Shift16DigammaPointAddThreeArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaPoint_add_three_add_one_arg_eq_arctan :
    Complex.arg ((step33Shift16DigammaPoint + (3 : Complex)) + 1) =
      Real.arctan step33Shift16DigammaPointAddFourArgRatio := by
  have hre : 0 < ((step33Shift16DigammaPoint + (3 : Complex)) + 1).re := by
    norm_num [step33Shift16DigammaPoint]
  have hmem :
      Complex.arg ((step33Shift16DigammaPoint + (3 : Complex)) + 1) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg
    ((step33Shift16DigammaPoint + (3 : Complex)) + 1)
  have hratio :
      ((step33Shift16DigammaPoint + (3 : Complex)) + 1).im /
          ((step33Shift16DigammaPoint + (3 : Complex)) + 1).re =
        step33Shift16DigammaPointAddFourArgRatio := by
    norm_num [step33Shift16DigammaPoint,
      step33Shift16DigammaPointAddFourArgRatio]
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg ((step33Shift16DigammaPoint + (3 : Complex)) + 1))
      (y := step33Shift16DigammaPointAddFourArgRatio)
      (by rw [htan, hratio]) hmem
  exact h.symm

theorem step33Shift16DigammaPoint_add_nat_arg_eq_arctan (n : Nat) :
    Complex.arg (step33Shift16DigammaPoint + (n : Complex)) =
      Real.arctan ((1 : Real) / ((1290 : Real) + 40 * (n : Real))) := by
  have hre : 0 < (step33Shift16DigammaPoint + (n : Complex)).re := by
    have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
    have hpos : 0 < (129 : Real) / 4 + (n : Real) := by
      nlinarith
    simpa [step33Shift16DigammaPoint] using hpos
  have hmem :
      Complex.arg (step33Shift16DigammaPoint + (n : Complex)) ∈
        Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · exact (Complex.neg_pi_div_two_lt_arg_iff).2 (Or.inl hre)
    · exact (Complex.arg_lt_pi_div_two_iff).2 (Or.inl hre)
  have htan := Complex.tan_arg (step33Shift16DigammaPoint + (n : Complex))
  have hratio :
      (step33Shift16DigammaPoint + (n : Complex)).im /
          (step33Shift16DigammaPoint + (n : Complex)).re =
        (1 : Real) / ((1290 : Real) + 40 * (n : Real)) := by
    have hden : (1290 : Real) + 40 * (n : Real) ≠ 0 := by
      have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
      nlinarith
    rw [step33Shift16DigammaPoint]
    simp [Complex.add_re, Complex.add_im]
    field_simp [hden]
    ring
  have h :=
    Real.arctan_eq_of_tan_eq
      (x := Complex.arg (step33Shift16DigammaPoint + (n : Complex)))
      (y := (1 : Real) / ((1290 : Real) + 40 * (n : Real)))
      (by rw [htan, hratio]) hmem
  exact h.symm

private theorem step33Shift16DigammaArctanTerm_antitone :
    Antitone (fun n : Nat =>
      step33Shift16DigammaArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  intro m n hmn
  have hx0 : 0 <= step33Shift16DigammaArgRatio := by
    norm_num [step33Shift16DigammaArgRatio]
  have hx1 : step33Shift16DigammaArgRatio <= 1 := by
    norm_num [step33Shift16DigammaArgRatio]
  have hpow :
      step33Shift16DigammaArgRatio ^ (2 * n + 1) <=
        step33Shift16DigammaArgRatio ^ (2 * m + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1
      (by omega : 2 * m + 1 <= 2 * n + 1)
  have hden0n : 0 < (((2 * n + 1 : Nat) : Real)) := by
    positivity
  have hden0m : 0 < (((2 * m + 1 : Nat) : Real)) := by
    positivity
  have hden :
      (((2 * m + 1 : Nat) : Real)) <=
        (((2 * n + 1 : Nat) : Real)) := by
    exact_mod_cast (by omega : 2 * m + 1 <= 2 * n + 1)
  calc
    step33Shift16DigammaArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))
        <= step33Shift16DigammaArgRatio ^ (2 * m + 1) /
          (((2 * n + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_right hpow hden0n.le
    _ <= step33Shift16DigammaArgRatio ^ (2 * m + 1) /
        (((2 * m + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0 _) hden0m hden

private theorem step33Shift16DigammaArctanTerm_summable :
    Summable (fun n : Nat =>
      step33Shift16DigammaArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  have hgeom :
      Summable (fun n : Nat =>
        step33Shift16DigammaArgRatio *
          (step33Shift16DigammaArgRatio ^ 2) ^ n) := by
    exact Summable.mul_left step33Shift16DigammaArgRatio
      (summable_geometric_of_lt_one
        (by positivity)
        (by norm_num [step33Shift16DigammaArgRatio]))
  refine hgeom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · have hx0 : 0 <= step33Shift16DigammaArgRatio := by
      norm_num [step33Shift16DigammaArgRatio]
    exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  · have hx0 : 0 <= step33Shift16DigammaArgRatio := by
      norm_num [step33Shift16DigammaArgRatio]
    have hden1 : (1 : Real) <= (((2 * n + 1 : Nat) : Real)) := by
      exact_mod_cast (by omega : 1 <= 2 * n + 1)
    have hpow_nonneg :
        0 <= step33Shift16DigammaArgRatio ^ (2 * n + 1) :=
      pow_nonneg hx0 _
    have hdiv :
        step33Shift16DigammaArgRatio ^ (2 * n + 1) /
            (((2 * n + 1 : Nat) : Real)) <=
          step33Shift16DigammaArgRatio ^ (2 * n + 1) / 1 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (by norm_num) hden1
    have hpoweq :
        step33Shift16DigammaArgRatio ^ (2 * n + 1) / 1 =
          step33Shift16DigammaArgRatio *
            (step33Shift16DigammaArgRatio ^ 2) ^ n := by
      field_simp
      ring_nf
    exact hdiv.trans_eq hpoweq

private theorem step33Shift16DigammaArctan_error_bound :
    |Real.arctan step33Shift16DigammaArgRatio -
        (∑ i ∈ Finset.range 9,
          (-1 : Real) ^ i *
            (step33Shift16DigammaArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real))))| <=
      step33Shift16DigammaArgRatio ^ (2 * 9 + 1) /
        (((2 * 9 + 1 : Nat) : Real)) := by
  have hsum0 :=
    (Real.hasSum_arctan
      (x := step33Shift16DigammaArgRatio)
      (by norm_num [step33Shift16DigammaArgRatio])).tsum_eq
  have hsum :
      (∑' i : Nat,
          (-1 : Real) ^ i *
            (step33Shift16DigammaArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real)))) =
        Real.arctan step33Shift16DigammaArgRatio := by
    convert hsum0 using 1
    ring_nf
  have herr := alternating_series_error_bound
    (fun n : Nat =>
      step33Shift16DigammaArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real)))
    step33Shift16DigammaArctanTerm_antitone
    step33Shift16DigammaArctanTerm_summable 9
  rw [hsum] at herr
  simpa using herr

private theorem step33Shift16DigammaAddOneArctanTerm_antitone :
    Antitone (fun n : Nat =>
      step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  intro m n hmn
  have hx0 : 0 <= step33Shift16DigammaPointAddOneArgRatio := by
    norm_num [step33Shift16DigammaPointAddOneArgRatio]
  have hx1 : step33Shift16DigammaPointAddOneArgRatio <= 1 := by
    norm_num [step33Shift16DigammaPointAddOneArgRatio]
  have hpow :
      step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) <=
        step33Shift16DigammaPointAddOneArgRatio ^ (2 * m + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1
      (by omega : 2 * m + 1 <= 2 * n + 1)
  have hden0n : 0 < (((2 * n + 1 : Nat) : Real)) := by
    positivity
  have hden0m : 0 < (((2 * m + 1 : Nat) : Real)) := by
    positivity
  have hden :
      (((2 * m + 1 : Nat) : Real)) <=
        (((2 * n + 1 : Nat) : Real)) := by
    exact_mod_cast (by omega : 2 * m + 1 <= 2 * n + 1)
  calc
    step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))
        <= step33Shift16DigammaPointAddOneArgRatio ^ (2 * m + 1) /
          (((2 * n + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_right hpow hden0n.le
    _ <= step33Shift16DigammaPointAddOneArgRatio ^ (2 * m + 1) /
        (((2 * m + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0 _) hden0m hden

private theorem step33Shift16DigammaAddOneArctanTerm_summable :
    Summable (fun n : Nat =>
      step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  have hgeom :
      Summable (fun n : Nat =>
        step33Shift16DigammaPointAddOneArgRatio *
          (step33Shift16DigammaPointAddOneArgRatio ^ 2) ^ n) := by
    exact Summable.mul_left step33Shift16DigammaPointAddOneArgRatio
      (summable_geometric_of_lt_one
        (by positivity)
        (by norm_num [step33Shift16DigammaPointAddOneArgRatio]))
  refine hgeom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · have hx0 : 0 <= step33Shift16DigammaPointAddOneArgRatio := by
      norm_num [step33Shift16DigammaPointAddOneArgRatio]
    exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  · have hx0 : 0 <= step33Shift16DigammaPointAddOneArgRatio := by
      norm_num [step33Shift16DigammaPointAddOneArgRatio]
    have hden1 : (1 : Real) <= (((2 * n + 1 : Nat) : Real)) := by
      exact_mod_cast (by omega : 1 <= 2 * n + 1)
    have hpow_nonneg :
        0 <= step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) :=
      pow_nonneg hx0 _
    have hdiv :
        step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) /
            (((2 * n + 1 : Nat) : Real)) <=
          step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) / 1 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (by norm_num) hden1
    have hpoweq :
        step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) / 1 =
          step33Shift16DigammaPointAddOneArgRatio *
            (step33Shift16DigammaPointAddOneArgRatio ^ 2) ^ n := by
      field_simp
      ring_nf
    exact hdiv.trans_eq hpoweq

private theorem step33Shift16DigammaAddOneArctan_error_bound :
    |Real.arctan step33Shift16DigammaPointAddOneArgRatio -
        (∑ i ∈ Finset.range 9,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddOneArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real))))| <=
      step33Shift16DigammaPointAddOneArgRatio ^ (2 * 9 + 1) /
        (((2 * 9 + 1 : Nat) : Real)) := by
  have hsum0 :=
    (Real.hasSum_arctan
      (x := step33Shift16DigammaPointAddOneArgRatio)
      (by norm_num [step33Shift16DigammaPointAddOneArgRatio])).tsum_eq
  have hsum :
      (∑' i : Nat,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddOneArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real)))) =
        Real.arctan step33Shift16DigammaPointAddOneArgRatio := by
    convert hsum0 using 1
    ring_nf
  have herr := alternating_series_error_bound
    (fun n : Nat =>
      step33Shift16DigammaPointAddOneArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real)))
    step33Shift16DigammaAddOneArctanTerm_antitone
    step33Shift16DigammaAddOneArctanTerm_summable 9
  rw [hsum] at herr
  simpa using herr

private theorem step33Shift16DigammaAddTwoArctanTerm_antitone :
    Antitone (fun n : Nat =>
      step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  intro m n hmn
  have hx0 : 0 <= step33Shift16DigammaPointAddTwoArgRatio := by
    norm_num [step33Shift16DigammaPointAddTwoArgRatio]
  have hx1 : step33Shift16DigammaPointAddTwoArgRatio <= 1 := by
    norm_num [step33Shift16DigammaPointAddTwoArgRatio]
  have hpow :
      step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) <=
        step33Shift16DigammaPointAddTwoArgRatio ^ (2 * m + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1
      (by omega : 2 * m + 1 <= 2 * n + 1)
  have hden0n : 0 < (((2 * n + 1 : Nat) : Real)) := by
    positivity
  have hden0m : 0 < (((2 * m + 1 : Nat) : Real)) := by
    positivity
  have hden :
      (((2 * m + 1 : Nat) : Real)) <=
        (((2 * n + 1 : Nat) : Real)) := by
    exact_mod_cast (by omega : 2 * m + 1 <= 2 * n + 1)
  calc
    step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))
        <= step33Shift16DigammaPointAddTwoArgRatio ^ (2 * m + 1) /
          (((2 * n + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_right hpow hden0n.le
    _ <= step33Shift16DigammaPointAddTwoArgRatio ^ (2 * m + 1) /
        (((2 * m + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0 _) hden0m hden

private theorem step33Shift16DigammaAddTwoArctanTerm_summable :
    Summable (fun n : Nat =>
      step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  have hgeom :
      Summable (fun n : Nat =>
        step33Shift16DigammaPointAddTwoArgRatio *
          (step33Shift16DigammaPointAddTwoArgRatio ^ 2) ^ n) := by
    exact Summable.mul_left step33Shift16DigammaPointAddTwoArgRatio
      (summable_geometric_of_lt_one
        (by positivity)
        (by norm_num [step33Shift16DigammaPointAddTwoArgRatio]))
  refine hgeom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · have hx0 : 0 <= step33Shift16DigammaPointAddTwoArgRatio := by
      norm_num [step33Shift16DigammaPointAddTwoArgRatio]
    exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  · have hx0 : 0 <= step33Shift16DigammaPointAddTwoArgRatio := by
      norm_num [step33Shift16DigammaPointAddTwoArgRatio]
    have hden1 : (1 : Real) <= (((2 * n + 1 : Nat) : Real)) := by
      exact_mod_cast (by omega : 1 <= 2 * n + 1)
    have hpow_nonneg :
        0 <= step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) :=
      pow_nonneg hx0 _
    have hdiv :
        step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) /
            (((2 * n + 1 : Nat) : Real)) <=
          step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) / 1 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (by norm_num) hden1
    have hpoweq :
        step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) / 1 =
          step33Shift16DigammaPointAddTwoArgRatio *
            (step33Shift16DigammaPointAddTwoArgRatio ^ 2) ^ n := by
      field_simp
      ring_nf
    exact hdiv.trans_eq hpoweq

private theorem step33Shift16DigammaAddTwoArctan_error_bound :
    |Real.arctan step33Shift16DigammaPointAddTwoArgRatio -
        (∑ i ∈ Finset.range 9,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddTwoArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real))))| <=
      step33Shift16DigammaPointAddTwoArgRatio ^ (2 * 9 + 1) /
        (((2 * 9 + 1 : Nat) : Real)) := by
  have hsum0 :=
    (Real.hasSum_arctan
      (x := step33Shift16DigammaPointAddTwoArgRatio)
      (by norm_num [step33Shift16DigammaPointAddTwoArgRatio])).tsum_eq
  have hsum :
      (∑' i : Nat,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddTwoArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real)))) =
        Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
    convert hsum0 using 1
    ring_nf
  have herr := alternating_series_error_bound
    (fun n : Nat =>
      step33Shift16DigammaPointAddTwoArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real)))
    step33Shift16DigammaAddTwoArctanTerm_antitone
    step33Shift16DigammaAddTwoArctanTerm_summable 9
  rw [hsum] at herr
  simpa using herr

private theorem step33Shift16DigammaAddThreeArctanTerm_antitone :
    Antitone (fun n : Nat =>
      step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  intro m n hmn
  have hx0 : 0 <= step33Shift16DigammaPointAddThreeArgRatio := by
    norm_num [step33Shift16DigammaPointAddThreeArgRatio]
  have hx1 : step33Shift16DigammaPointAddThreeArgRatio <= 1 := by
    norm_num [step33Shift16DigammaPointAddThreeArgRatio]
  have hpow :
      step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) <=
        step33Shift16DigammaPointAddThreeArgRatio ^ (2 * m + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1
      (by omega : 2 * m + 1 <= 2 * n + 1)
  have hden0n : 0 < (((2 * n + 1 : Nat) : Real)) := by
    positivity
  have hden0m : 0 < (((2 * m + 1 : Nat) : Real)) := by
    positivity
  have hden :
      (((2 * m + 1 : Nat) : Real)) <=
        (((2 * n + 1 : Nat) : Real)) := by
    exact_mod_cast (by omega : 2 * m + 1 <= 2 * n + 1)
  calc
    step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))
        <= step33Shift16DigammaPointAddThreeArgRatio ^ (2 * m + 1) /
          (((2 * n + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_right hpow hden0n.le
    _ <= step33Shift16DigammaPointAddThreeArgRatio ^ (2 * m + 1) /
        (((2 * m + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0 _) hden0m hden

private theorem step33Shift16DigammaAddThreeArctanTerm_summable :
    Summable (fun n : Nat =>
      step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real))) := by
  have hgeom :
      Summable (fun n : Nat =>
        step33Shift16DigammaPointAddThreeArgRatio *
          (step33Shift16DigammaPointAddThreeArgRatio ^ 2) ^ n) := by
    exact Summable.mul_left step33Shift16DigammaPointAddThreeArgRatio
      (summable_geometric_of_lt_one
        (by positivity)
        (by norm_num [step33Shift16DigammaPointAddThreeArgRatio]))
  refine hgeom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · have hx0 : 0 <= step33Shift16DigammaPointAddThreeArgRatio := by
      norm_num [step33Shift16DigammaPointAddThreeArgRatio]
    exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  · have hx0 : 0 <= step33Shift16DigammaPointAddThreeArgRatio := by
      norm_num [step33Shift16DigammaPointAddThreeArgRatio]
    have hden1 : (1 : Real) <= (((2 * n + 1 : Nat) : Real)) := by
      exact_mod_cast (by omega : 1 <= 2 * n + 1)
    have hpow_nonneg :
        0 <= step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) :=
      pow_nonneg hx0 _
    have hdiv :
        step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) /
            (((2 * n + 1 : Nat) : Real)) <=
          step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) / 1 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (by norm_num) hden1
    have hpoweq :
        step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) / 1 =
          step33Shift16DigammaPointAddThreeArgRatio *
            (step33Shift16DigammaPointAddThreeArgRatio ^ 2) ^ n := by
      field_simp
      ring_nf
    exact hdiv.trans_eq hpoweq

private theorem step33Shift16DigammaAddThreeArctan_error_bound :
    |Real.arctan step33Shift16DigammaPointAddThreeArgRatio -
        (∑ i ∈ Finset.range 9,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddThreeArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real))))| <=
      step33Shift16DigammaPointAddThreeArgRatio ^ (2 * 9 + 1) /
        (((2 * 9 + 1 : Nat) : Real)) := by
  have hsum0 :=
    (Real.hasSum_arctan
      (x := step33Shift16DigammaPointAddThreeArgRatio)
      (by norm_num [step33Shift16DigammaPointAddThreeArgRatio])).tsum_eq
  have hsum :
      (∑' i : Nat,
          (-1 : Real) ^ i *
            (step33Shift16DigammaPointAddThreeArgRatio ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real)))) =
        Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
    convert hsum0 using 1
    ring_nf
  have herr := alternating_series_error_bound
    (fun n : Nat =>
      step33Shift16DigammaPointAddThreeArgRatio ^ (2 * n + 1) /
        (((2 * n + 1 : Nat) : Real)))
    step33Shift16DigammaAddThreeArctanTerm_antitone
    step33Shift16DigammaAddThreeArctanTerm_summable 9
  rw [hsum] at herr
  simpa using herr

private theorem step33Shift16ArctanTerm_antitone_of_nonneg_le_one
    (x : Real) (hx0 : 0 <= x) (hx1 : x <= 1) :
    Antitone (fun n : Nat =>
      x ^ (2 * n + 1) / (((2 * n + 1 : Nat) : Real))) := by
  intro m n hmn
  have hpow : x ^ (2 * n + 1) <= x ^ (2 * m + 1) := by
    exact pow_le_pow_of_le_one hx0 hx1
      (by omega : 2 * m + 1 <= 2 * n + 1)
  have hden0n : 0 < (((2 * n + 1 : Nat) : Real)) := by
    positivity
  have hden0m : 0 < (((2 * m + 1 : Nat) : Real)) := by
    positivity
  have hden :
      (((2 * m + 1 : Nat) : Real)) <=
        (((2 * n + 1 : Nat) : Real)) := by
    exact_mod_cast (by omega : 2 * m + 1 <= 2 * n + 1)
  calc
    x ^ (2 * n + 1) / (((2 * n + 1 : Nat) : Real))
        <= x ^ (2 * m + 1) / (((2 * n + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_right hpow hden0n.le
    _ <= x ^ (2 * m + 1) / (((2 * m + 1 : Nat) : Real)) := by
      exact div_le_div_of_nonneg_left (pow_nonneg hx0 _) hden0m hden

private theorem step33Shift16ArctanTerm_summable_of_nonneg_sq_lt_one
    (x : Real) (hx0 : 0 <= x) (hxsq : x ^ 2 < 1) :
    Summable (fun n : Nat =>
      x ^ (2 * n + 1) / (((2 * n + 1 : Nat) : Real))) := by
  have hgeom :
      Summable (fun n : Nat => x * (x ^ 2) ^ n) := by
    exact Summable.mul_left x
      (summable_geometric_of_lt_one (by positivity) hxsq)
  refine hgeom.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact div_nonneg (pow_nonneg hx0 _) (by positivity)
  · have hden1 : (1 : Real) <= (((2 * n + 1 : Nat) : Real)) := by
      exact_mod_cast (by omega : 1 <= 2 * n + 1)
    have hpow_nonneg : 0 <= x ^ (2 * n + 1) := pow_nonneg hx0 _
    have hdiv :
        x ^ (2 * n + 1) / (((2 * n + 1 : Nat) : Real)) <=
          x ^ (2 * n + 1) / 1 := by
      exact div_le_div_of_nonneg_left hpow_nonneg (by norm_num) hden1
    have hpoweq :
        x ^ (2 * n + 1) / 1 = x * (x ^ 2) ^ n := by
      field_simp
      ring_nf
    exact hdiv.trans_eq hpoweq

private theorem step33Shift16Arctan_error_bound_of_nonneg_le_one
    (x : Real) (hx0 : 0 <= x) (hx1 : x <= 1) (hxsq : x ^ 2 < 1)
    (hxnorm : ‖x‖ < 1) :
    |Real.arctan x -
        (∑ i ∈ Finset.range 9,
          (-1 : Real) ^ i *
            (x ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real))))| <=
      x ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real)) := by
  have hsum0 := (Real.hasSum_arctan (x := x) hxnorm).tsum_eq
  have hsum :
      (∑' i : Nat,
          (-1 : Real) ^ i *
            (x ^ (2 * i + 1) /
              (((2 * i + 1 : Nat) : Real)))) =
        Real.arctan x := by
    convert hsum0 using 1
    ring_nf
  have herr := alternating_series_error_bound
    (fun n : Nat =>
      x ^ (2 * n + 1) / (((2 * n + 1 : Nat) : Real)))
    (step33Shift16ArctanTerm_antitone_of_nonneg_le_one x hx0 hx1)
    (step33Shift16ArctanTerm_summable_of_nonneg_sq_lt_one x hx0 hxsq) 9
  rw [hsum] at herr
  simpa using herr

private theorem step33Shift16DigammaArctan_abs :
    |Real.arctan step33Shift16DigammaArgRatio -
        step33Shift16DigammaArgCenter| <=
      step33Shift16DigammaArgRadius := by
  have herr := step33Shift16DigammaArctan_error_bound
  rw [abs_sub_le_iff] at herr ⊢
  constructor
  · have h1 := herr.1
    norm_num [step33Shift16DigammaArgRatio,
      step33Shift16DigammaArgCenter, step33Shift16DigammaArgRadius] at h1 ⊢
    linarith [h1]
  · have h2 := herr.2
    norm_num [step33Shift16DigammaArgRatio,
      step33Shift16DigammaArgCenter, step33Shift16DigammaArgRadius] at h2 ⊢
    linarith [h2]

theorem step33Shift16DigammaArg_abs :
    |Complex.arg step33Shift16DigammaPoint -
        step33Shift16DigammaArgCenter| <=
      step33Shift16DigammaArgRadius := by
  simpa [step33Shift16DigammaArg_eq_arctan] using
    step33Shift16DigammaArctan_abs

/-- The Bernoulli m=6 asymptotic main selected for the first shifted-digamma
endpoint at `129/4 + I/40`. -/
def step33Shift16DigammaM6Main : Complex :=
  let z : Complex := step33Shift16DigammaPoint
  Complex.log z
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)

theorem step33Shift16DigammaM6Main_eq_digammaM6AsymptoticMain :
    step33Shift16DigammaM6Main =
      Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint := by
  rfl

theorem step33_shift16_digamma_m6_main_component_abs_of_asymptotic_main_component_abs
    (hMainRe :
      |(Q3.digamma step33Shift16DigammaPoint -
          Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).re| <=
        step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma step33Shift16DigammaPoint -
          Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).im| <=
        step33Shift16DigammaM6MainComponentRadius) :
    |(Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main).re| <=
        step33Shift16DigammaM6MainComponentRadius ∧
      |(Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main).im| <=
        step33Shift16DigammaM6MainComponentRadius := by
  constructor
  · simpa [step33Shift16DigammaM6Main_eq_digammaM6AsymptoticMain] using
      hMainRe
  · simpa [step33Shift16DigammaM6Main_eq_digammaM6AsymptoticMain] using
      hMainIm

def step33Shift16DigammaM6AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint
  (0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)

theorem step33Shift16DigammaM6AlgebraicPart_re_eq :
    step33Shift16DigammaM6AlgebraicPart.re =
      (-63315670345553756061002593643336591490616904934440296647744506790486014579000 : Real) /
        (4062868498056199278319006262168713067039941698943618608439364197857288035671809 : Real) := by
  norm_num [step33Shift16DigammaM6AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16DigammaM6AlgebraicPart_im_eq :
    step33Shift16DigammaM6AlgebraicPart.im =
      (421659756983189090226699488552166141840392324405768671465646255039503540 : Real) /
        (34725371778258113489906036428792419376409758110629218875550121349207590048477 : Real) := by
  norm_num [step33Shift16DigammaM6AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

/-- Rational cancellation table for the m=6 Bernoulli step-defect expansion.

These identities are the hole-free algebraic part extracted from the Aristotle
draft for the shifted-digamma M6 blocker.  They do not assert the analytic
Euler-Maclaurin remainder theorem; they only record the rational coefficient
cancellations that a future local M6 remainder proof will consume. -/
theorem step33Shift16DigammaM6CancelD2 :
    (0 : Rat) = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD3 :
    (1 : Rat) / 6 - 1 / 6 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD4 :
    -(1 : Rat) / 4 + 1 / 4 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD5 :
    (3 : Rat) / 10 - 1 / 3 + 1 / 30 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD6 :
    -(1 : Rat) / 3 + 5 / 12 - 1 / 12 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD7 :
    (5 : Rat) / 14 - 1 / 2 + 1 / 6 - 1 / 42 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD8 :
    -(3 : Rat) / 8 + 7 / 12 - 7 / 24 + 1 / 12 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD9 :
    (7 : Rat) / 18 - 2 / 3 + 7 / 15 - 2 / 9 + 1 / 30 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD10 :
    -(2 : Rat) / 5 + 3 / 4 - 7 / 10 + 1 / 2 - 3 / 20 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD11 :
    (9 : Rat) / 22 - 5 / 6 + 1 - 1 + 1 / 2 - 5 / 66 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD12 :
    -(5 : Rat) / 12 + 11 / 12 - 11 / 8 + 11 / 6 - 11 / 8 + 5 / 12 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD13 :
    (11 : Rat) / 26 - 1 + 11 / 6 - 22 / 7 + 33 / 10 - 5 / 3 +
      691 / 2730 = 0 := by
  norm_num

theorem step33Shift16DigammaM6CancelD14 :
    -(3 : Rat) / 7 + 13 / 12 - 143 / 60 + 143 / 28 - 143 / 20 +
      65 / 12 - 53898 / 32760 = 0 := by
  norm_num

theorem step33Shift16DigammaM6LeadingD15 :
    (7 : Rat) / 30 + 11 / 15 = 29 / 30 := by
  norm_num

theorem step33Shift16DigammaM6Main_eq_log_add_algebraicPart :
    step33Shift16DigammaM6Main =
      Complex.log step33Shift16DigammaPoint +
        step33Shift16DigammaM6AlgebraicPart := by
  simp [step33Shift16DigammaM6Main, step33Shift16DigammaM6AlgebraicPart]
  ring_nf

def step33Shift16M6StepDefectN0LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + 1) -
    Complex.log step33Shift16DigammaPoint

def step33Shift16M6StepDefectN0AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN0LogReLower : Real :=
  (30536706058920523887855509174 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN0LogReUpper : Real :=
  (30536706058920523887855509175 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN0LogImLower : Real :=
  (-233140856085953858876761496505 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN0LogImUpper : Real :=
  (-233140856085953858876761496504 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN0LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN0LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((1768901 : Real) / (1664101 : Real)) := by
  rw [step33Shift16M6StepDefectN0LogStep]
  simp [Complex.log_re, step33Shift16DigammaPoint_add_one_norm_eq_sqrt,
    step33Shift16DigammaPoint_norm_eq_sqrt]
  have h176 : (0 : Real) <= 1768901 := by
    norm_num
  have h166 : (0 : Real) <= 1664101 := by
    norm_num
  have hs1600_ne : Real.sqrt (1600 : Real) ≠ 0 := by
    positivity
  have hs176_ne : Real.sqrt (1768901 : Real) ≠ 0 := by
    positivity
  have hs166_ne : Real.sqrt (1664101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs176_ne hs1600_ne,
    Real.log_div hs166_ne hs1600_ne]
  rw [Real.log_sqrt h176, Real.log_sqrt h166]
  have hratio :
      Real.log ((1768901 : Real) / (1664101 : Real)) =
        Real.log (1768901 : Real) - Real.log (1664101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN0LogStep_re_bounds :
    step33Shift16M6StepDefectN0LogReLower <=
        step33Shift16M6StepDefectN0LogStep.re ∧
      step33Shift16M6StepDefectN0LogStep.re <=
        step33Shift16M6StepDefectN0LogReUpper := by
  let a : Real := (104800 : Real) / (1664101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((1768901 : Real) / (1664101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN0LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN0LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN0LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN0LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN0LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN0LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN0LogReUpper := by
      norm_num [step33Shift16M6StepDefectN0LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN0LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN0LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN0LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN0LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN0LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + 1) -
        Complex.arg step33Shift16DigammaPoint := by
  rw [step33Shift16M6StepDefectN0LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN0LogStep_im_bounds :
    step33Shift16M6StepDefectN0LogImLower <=
        step33Shift16M6StepDefectN0LogStep.im ∧
      step33Shift16M6StepDefectN0LogStep.im <=
        step33Shift16M6StepDefectN0LogImUpper := by
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E0 : Real :=
    step33Shift16DigammaArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddOneArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E1 : Real :=
    step33Shift16DigammaPointAddOneArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16DigammaArctan_error_bound
  have h1 := step33Shift16DigammaAddOneArctan_error_bound
  have h0Lower : S0 - E0 <= Real.arctan step33Shift16DigammaArgRatio := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan step33Shift16DigammaArgRatio <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower :
      S1 - E1 <= Real.arctan step33Shift16DigammaPointAddOneArgRatio := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper :
      Real.arctan step33Shift16DigammaPointAddOneArgRatio <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN0LogStep.im =
        Real.arctan step33Shift16DigammaPointAddOneArgRatio -
          Real.arctan step33Shift16DigammaArgRatio := by
    rw [step33Shift16M6StepDefectN0LogStep_im_eq_arg_sub,
      step33Shift16DigammaPoint_add_one_arg_eq_arctan,
      step33Shift16DigammaArg_eq_arctan]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN0LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN0LogImLower, S0, E0, S1, E1,
        step33Shift16DigammaArgRatio,
        step33Shift16DigammaPointAddOneArgRatio]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN0LogImUpper := by
      norm_num [step33Shift16M6StepDefectN0LogImUpper, S0, E0, S1, E1,
        step33Shift16DigammaArgRatio,
        step33Shift16DigammaPointAddOneArgRatio]
    linarith

theorem step33Shift16M6StepDefectN0_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect step33Shift16DigammaPoint =
      step33Shift16M6StepDefectN0LogStep +
        step33Shift16M6StepDefectN0AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN0LogStep,
    step33Shift16M6StepDefectN0AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN0AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN0AlgebraicPart.re =
      (-2985607251472893161683489085800494160815831985345926757653362318531970198954897367155822945385857996217473193315344869483077103347806023475451691904400 : Real) /
        (97771097043412897998661009338848079780589869546549426272177778248339881392715430054211327602507209885949821825315784726237185335010618616209155680556231 : Real) := by
  norm_num [step33Shift16M6StepDefectN0AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN0AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN0AlgebraicPart.im =
      (6838331179549246583576826723582952093154781452760714073531897752140910835099238253493753247757252310258462079429375017554074797288064118184746599720 : Real) /
        (293313291130238693995983028016544239341769608639648278816533334745019644178146290162633982807521629657849465475947354178711556005031855848627467041668693 : Real) := by
  norm_num [step33Shift16M6StepDefectN0AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n0_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN0LogReLower <=
        step33Shift16M6StepDefectN0LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN0LogStep.re <=
        step33Shift16M6StepDefectN0LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN0LogImLower <=
        step33Shift16M6StepDefectN0LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN0LogStep.im <=
        step33Shift16M6StepDefectN0LogImUpper) :
    (((-219 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect step33Shift16DigammaPoint).re ∧
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).re <=
        (-218 : Real) / ((10 : Real) ^ 25)) ∧
     ((250 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect step33Shift16DigammaPoint).im ∧
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).im <=
        (251 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).re =
        step33Shift16M6StepDefectN0LogStep.re +
          step33Shift16M6StepDefectN0AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN0_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).im =
        step33Shift16M6StepDefectN0LogStep.im +
          step33Shift16M6StepDefectN0AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN0_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN0AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN0LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN0AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN0LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN0AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN0LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN0AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN0LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n0_component_interval :
    (((-219 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect step33Shift16DigammaPoint).re ∧
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).re <=
        (-218 : Real) / ((10 : Real) ^ 25)) ∧
     ((250 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect step33Shift16DigammaPoint).im ∧
      (Q3.digammaM6StepDefect step33Shift16DigammaPoint).im <=
        (251 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n0_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN0LogStep_re_bounds.1
    step33Shift16M6StepDefectN0LogStep_re_bounds.2
    step33Shift16M6StepDefectN0LogStep_im_bounds.1
    step33Shift16M6StepDefectN0LogStep_im_bounds.2

def step33Shift16M6StepDefectN1LogStep : Complex :=
  Complex.log ((step33Shift16DigammaPoint + (1 : Complex)) + 1) -
    Complex.log (step33Shift16DigammaPoint + (1 : Complex))

def step33Shift16M6StepDefectN1AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (1 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN1LogReLower : Real :=
  (29631781341557002243764214602 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN1LogReUpper : Real :=
  (29631781341557002243764214603 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN1LogImLower : Real :=
  (-219526798973132652566871240756 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN1LogImUpper : Real :=
  (-219526798973132652566871240755 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN1LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN1LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((1876901 : Real) / (1768901 : Real)) := by
  rw [step33Shift16M6StepDefectN1LogStep]
  simp [Complex.log_re,
    step33Shift16DigammaPoint_add_one_add_one_norm_eq_sqrt,
    step33Shift16DigammaPoint_add_one_norm_eq_sqrt]
  have h187 : (0 : Real) <= 1876901 := by
    norm_num
  have h176 : (0 : Real) <= 1768901 := by
    norm_num
  have hs1600_ne : Real.sqrt (1600 : Real) ≠ 0 := by
    positivity
  have hs187_ne : Real.sqrt (1876901 : Real) ≠ 0 := by
    positivity
  have hs176_ne : Real.sqrt (1768901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs187_ne hs1600_ne,
    Real.log_div hs176_ne hs1600_ne]
  rw [Real.log_sqrt h187, Real.log_sqrt h176]
  have hratio :
      Real.log ((1876901 : Real) / (1768901 : Real)) =
        Real.log (1876901 : Real) - Real.log (1768901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN1LogStep_re_bounds :
    step33Shift16M6StepDefectN1LogReLower <=
        step33Shift16M6StepDefectN1LogStep.re ∧
      step33Shift16M6StepDefectN1LogStep.re <=
        step33Shift16M6StepDefectN1LogReUpper := by
  let a : Real := (108000 : Real) / (1768901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((1876901 : Real) / (1768901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN1LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN1LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN1LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN1LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN1LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN1LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN1LogReUpper := by
      norm_num [step33Shift16M6StepDefectN1LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN1LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN1LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN1LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN1LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN1LogStep.im =
      Complex.arg ((step33Shift16DigammaPoint + (1 : Complex)) + 1) -
        Complex.arg (step33Shift16DigammaPoint + (1 : Complex)) := by
  rw [step33Shift16M6StepDefectN1LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN1LogStep_im_bounds :
    step33Shift16M6StepDefectN1LogImLower <=
        step33Shift16M6StepDefectN1LogStep.im ∧
      step33Shift16M6StepDefectN1LogStep.im <=
        step33Shift16M6StepDefectN1LogImUpper := by
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddOneArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E0 : Real :=
    step33Shift16DigammaPointAddOneArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddTwoArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E1 : Real :=
    step33Shift16DigammaPointAddTwoArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16DigammaAddOneArctan_error_bound
  have h1 := step33Shift16DigammaAddTwoArctan_error_bound
  have h0Lower :
      S0 - E0 <= Real.arctan step33Shift16DigammaPointAddOneArgRatio := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper :
      Real.arctan step33Shift16DigammaPointAddOneArgRatio <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower :
      S1 - E1 <= Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper :
      Real.arctan step33Shift16DigammaPointAddTwoArgRatio <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN1LogStep.im =
        Real.arctan step33Shift16DigammaPointAddTwoArgRatio -
          Real.arctan step33Shift16DigammaPointAddOneArgRatio := by
    rw [step33Shift16M6StepDefectN1LogStep_im_eq_arg_sub,
      step33Shift16DigammaPoint_add_one_add_one_arg_eq_arctan,
      step33Shift16DigammaPoint_add_one_arg_eq_arctan]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN1LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN1LogImLower, S0, E0, S1, E1,
        step33Shift16DigammaPointAddOneArgRatio,
        step33Shift16DigammaPointAddTwoArgRatio]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN1LogImUpper := by
      norm_num [step33Shift16M6StepDefectN1LogImUpper, S0, E0, S1, E1,
        step33Shift16DigammaPointAddOneArgRatio,
        step33Shift16DigammaPointAddTwoArgRatio]
    linarith

theorem step33Shift16M6StepDefectN1_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (1 : Complex)) =
      step33Shift16M6StepDefectN1LogStep +
        step33Shift16M6StepDefectN1AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN1LogStep,
    step33Shift16M6StepDefectN1AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN1AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN1AlgebraicPart.re =
      (-53202318106913686225087113749020606359097260251647508100494146617288325369159632562570382584272381826003134266963137203021024220549483783759441315854000 : Real) /
        (1795447850187131878105276370586234270592361829059762893671653960127112999208973465809403988353572096947772553916969872460362896717953329309273978874510601 : Real) := by
  norm_num [step33Shift16M6StepDefectN1AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN1AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN1AlgebraicPart.im =
      (354734027347296321904545306126993105091528907647174168843651115026471506617318469474991555531077733915839623197672657104482007375286787401884532388360 : Real) /
        (16159030651684186902947487335276108435331256461537866043044885641144016992880761192284635895182148872529952985252728852143266070461579963783465809870595409 : Real) := by
  norm_num [step33Shift16M6StepDefectN1AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n1_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN1LogReLower <=
        step33Shift16M6StepDefectN1LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN1LogStep.re <=
        step33Shift16M6StepDefectN1LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN1LogImLower <=
        step33Shift16M6StepDefectN1LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN1LogStep.im <=
        step33Shift16M6StepDefectN1LogImUpper) :
    (((-140 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).re <=
        (-139 : Real) / ((10 : Real) ^ 25)) ∧
     ((154 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).im <=
        (155 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).re =
        step33Shift16M6StepDefectN1LogStep.re +
          step33Shift16M6StepDefectN1AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN1_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).im =
        step33Shift16M6StepDefectN1LogStep.im +
          step33Shift16M6StepDefectN1AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN1_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN1AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN1LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN1AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN1LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN1AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN1LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN1AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN1LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n1_component_interval :
    (((-140 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).re <=
        (-139 : Real) / ((10 : Real) ^ 25)) ∧
     ((154 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (1 : Complex))).im <=
        (155 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n1_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN1LogStep_re_bounds.1
    step33Shift16M6StepDefectN1LogStep_re_bounds.2
    step33Shift16M6StepDefectN1LogStep_im_bounds.1
    step33Shift16M6StepDefectN1LogStep_im_bounds.2

def step33Shift16M6StepDefectN2LogStep : Complex :=
  Complex.log ((step33Shift16DigammaPoint + (2 : Complex)) + 1) -
    Complex.log (step33Shift16DigammaPoint + (2 : Complex))

def step33Shift16M6StepDefectN2AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (2 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN2LogReLower : Real :=
  (28778949649736688661507267200 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN2LogReUpper : Real :=
  (28778949649736688661507267201 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN2LogImLower : Real :=
  (-207071384206369717219267581062 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN2LogImUpper : Real :=
  (-207071384206369717219267581061 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN2LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN2LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((1988101 : Real) / (1876901 : Real)) := by
  rw [step33Shift16M6StepDefectN2LogStep]
  simp [Complex.log_re,
    step33Shift16DigammaPoint_add_two_add_one_norm_eq_sqrt,
    step33Shift16DigammaPoint_add_two_norm_eq_sqrt]
  have h198 : (0 : Real) <= 1988101 := by
    norm_num
  have h187 : (0 : Real) <= 1876901 := by
    norm_num
  have hs1600_ne : Real.sqrt (1600 : Real) ≠ 0 := by
    positivity
  have hs198_ne : Real.sqrt (1988101 : Real) ≠ 0 := by
    positivity
  have hs187_ne : Real.sqrt (1876901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs198_ne hs1600_ne,
    Real.log_div hs187_ne hs1600_ne]
  rw [Real.log_sqrt h198, Real.log_sqrt h187]
  have hratio :
      Real.log ((1988101 : Real) / (1876901 : Real)) =
        Real.log (1988101 : Real) - Real.log (1876901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN2LogStep_re_bounds :
    step33Shift16M6StepDefectN2LogReLower <=
        step33Shift16M6StepDefectN2LogStep.re ∧
      step33Shift16M6StepDefectN2LogStep.re <=
        step33Shift16M6StepDefectN2LogReUpper := by
  let a : Real := (111200 : Real) / (1876901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((1988101 : Real) / (1876901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN2LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN2LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN2LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN2LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN2LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN2LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN2LogReUpper := by
      norm_num [step33Shift16M6StepDefectN2LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN2LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN2LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN2LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN2LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN2LogStep.im =
      Complex.arg ((step33Shift16DigammaPoint + (2 : Complex)) + 1) -
        Complex.arg (step33Shift16DigammaPoint + (2 : Complex)) := by
  rw [step33Shift16M6StepDefectN2LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN2LogStep_im_bounds :
    step33Shift16M6StepDefectN2LogImLower <=
        step33Shift16M6StepDefectN2LogStep.im ∧
      step33Shift16M6StepDefectN2LogStep.im <=
        step33Shift16M6StepDefectN2LogImUpper := by
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddTwoArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E0 : Real :=
    step33Shift16DigammaPointAddTwoArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddThreeArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E1 : Real :=
    step33Shift16DigammaPointAddThreeArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16DigammaAddTwoArctan_error_bound
  have h1 := step33Shift16DigammaAddThreeArctan_error_bound
  have h0Lower :
      S0 - E0 <= Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper :
      Real.arctan step33Shift16DigammaPointAddTwoArgRatio <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower :
      S1 - E1 <= Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper :
      Real.arctan step33Shift16DigammaPointAddThreeArgRatio <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN2LogStep.im =
        Real.arctan step33Shift16DigammaPointAddThreeArgRatio -
          Real.arctan step33Shift16DigammaPointAddTwoArgRatio := by
    rw [step33Shift16M6StepDefectN2LogStep_im_eq_arg_sub,
      step33Shift16DigammaPoint_add_two_add_one_arg_eq_arctan,
      step33Shift16DigammaPoint_add_two_arg_eq_arctan]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN2LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN2LogImLower, S0, E0, S1, E1,
        step33Shift16DigammaPointAddTwoArgRatio,
        step33Shift16DigammaPointAddThreeArgRatio]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN2LogImUpper := by
      norm_num [step33Shift16M6StepDefectN2LogImUpper, S0, E0, S1, E1,
        step33Shift16DigammaPointAddTwoArgRatio,
        step33Shift16DigammaPointAddThreeArgRatio]
    linarith

theorem step33Shift16M6StepDefectN2_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (2 : Complex)) =
      step33Shift16M6StepDefectN2LogStep +
        step33Shift16M6StepDefectN2AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN2LogStep,
    step33Shift16M6StepDefectN2AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN2AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN2AlgebraicPart.re =
      (-629778724630838387065844672744462739426808849211159236357770150722435484040382772859945728722646336999753089052719287313386257243283940487216548949966800 : Real) /
        (21883311666887068310754332863190439236975231908636337335729275199162817417786428098034797838600395451170741387206024415871828253566736665191222163005183003 : Real) := by
  norm_num [step33Shift16M6StepDefectN2AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN2AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN2AlgebraicPart.im =
      (123583844669501046745862107615991527127081903714088363035953942158598832287766557311625534563348503840424592091532932567330971158594856628592422388760 : Real) /
        (5968175909151018630205727144506483428265972338719001091562529599771677477578116754009490319618289668501111287419824840692316796427291817779424226274140819 : Real) := by
  norm_num [step33Shift16M6StepDefectN2AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n2_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN2LogReLower <=
        step33Shift16M6StepDefectN2LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN2LogStep.re <=
        step33Shift16M6StepDefectN2LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN2LogImLower <=
        step33Shift16M6StepDefectN2LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN2LogStep.im <=
        step33Shift16M6StepDefectN2LogImUpper) :
    (((-90 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).re <=
        (-89 : Real) / ((10 : Real) ^ 25)) ∧
     ((97 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).im <=
        (98 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).re =
        step33Shift16M6StepDefectN2LogStep.re +
          step33Shift16M6StepDefectN2AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN2_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).im =
        step33Shift16M6StepDefectN2LogStep.im +
          step33Shift16M6StepDefectN2AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN2_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN2AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN2LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN2AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN2LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN2AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN2LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN2AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN2LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n2_component_interval :
    (((-90 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).re <=
        (-89 : Real) / ((10 : Real) ^ 25)) ∧
     ((97 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (2 : Complex))).im <=
        (98 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n2_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN2LogStep_re_bounds.1
    step33Shift16M6StepDefectN2LogStep_re_bounds.2
    step33Shift16M6StepDefectN2LogStep_im_bounds.1
    step33Shift16M6StepDefectN2LogStep_im_bounds.2

def step33Shift16M6StepDefectN3LogStep : Complex :=
  Complex.log ((step33Shift16DigammaPoint + (3 : Complex)) + 1) -
    Complex.log (step33Shift16DigammaPoint + (3 : Complex))

def step33Shift16M6StepDefectN3AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (3 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN3LogReLower : Real :=
  (27973838358137636518006214510 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN3LogReUpper : Real :=
  (27973838358137636518006214511 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN3LogImLower : Real :=
  (-195646761703204413291440640697 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN3LogImUpper : Real :=
  (-195646761703204413291440640696 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN3LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN3LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2102501 : Real) / (1988101 : Real)) := by
  rw [step33Shift16M6StepDefectN3LogStep]
  simp [Complex.log_re,
    step33Shift16DigammaPoint_add_three_add_one_norm_eq_sqrt,
    step33Shift16DigammaPoint_add_three_norm_eq_sqrt]
  have h210 : (0 : Real) <= 2102501 := by
    norm_num
  have h198 : (0 : Real) <= 1988101 := by
    norm_num
  have hs1600_ne : Real.sqrt (1600 : Real) ≠ 0 := by
    positivity
  have hs210_ne : Real.sqrt (2102501 : Real) ≠ 0 := by
    positivity
  have hs198_ne : Real.sqrt (1988101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs210_ne hs1600_ne,
    Real.log_div hs198_ne hs1600_ne]
  rw [Real.log_sqrt h210, Real.log_sqrt h198]
  have hratio :
      Real.log ((2102501 : Real) / (1988101 : Real)) =
        Real.log (2102501 : Real) - Real.log (1988101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN3LogStep_re_bounds :
    step33Shift16M6StepDefectN3LogReLower <=
        step33Shift16M6StepDefectN3LogStep.re ∧
      step33Shift16M6StepDefectN3LogStep.re <=
        step33Shift16M6StepDefectN3LogReUpper := by
  let a : Real := (114400 : Real) / (1988101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2102501 : Real) / (1988101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN3LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN3LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN3LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN3LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN3LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN3LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN3LogReUpper := by
      norm_num [step33Shift16M6StepDefectN3LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN3LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN3LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN3LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN3LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN3LogStep.im =
      Complex.arg ((step33Shift16DigammaPoint + (3 : Complex)) + 1) -
        Complex.arg (step33Shift16DigammaPoint + (3 : Complex)) := by
  rw [step33Shift16M6StepDefectN3LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN3LogStep_im_bounds :
    step33Shift16M6StepDefectN3LogImLower <=
        step33Shift16M6StepDefectN3LogStep.im ∧
      step33Shift16M6StepDefectN3LogStep.im <=
        step33Shift16M6StepDefectN3LogImUpper := by
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddThreeArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E0 : Real :=
    step33Shift16DigammaPointAddThreeArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (step33Shift16DigammaPointAddFourArgRatio ^ (2 * i + 1) /
          (((2 * i + 1 : Nat) : Real)))
  let E1 : Real :=
    step33Shift16DigammaPointAddFourArgRatio ^ (2 * 9 + 1) /
      (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    step33Shift16DigammaPointAddThreeArgRatio
    (by norm_num [step33Shift16DigammaPointAddThreeArgRatio])
    (by norm_num [step33Shift16DigammaPointAddThreeArgRatio])
    (by norm_num [step33Shift16DigammaPointAddThreeArgRatio])
    (by norm_num [step33Shift16DigammaPointAddThreeArgRatio])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    step33Shift16DigammaPointAddFourArgRatio
    (by norm_num [step33Shift16DigammaPointAddFourArgRatio])
    (by norm_num [step33Shift16DigammaPointAddFourArgRatio])
    (by norm_num [step33Shift16DigammaPointAddFourArgRatio])
    (by norm_num [step33Shift16DigammaPointAddFourArgRatio])
  have h0Lower :
      S0 - E0 <= Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper :
      Real.arctan step33Shift16DigammaPointAddThreeArgRatio <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower :
      S1 - E1 <= Real.arctan step33Shift16DigammaPointAddFourArgRatio := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper :
      Real.arctan step33Shift16DigammaPointAddFourArgRatio <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN3LogStep.im =
        Real.arctan step33Shift16DigammaPointAddFourArgRatio -
          Real.arctan step33Shift16DigammaPointAddThreeArgRatio := by
    rw [step33Shift16M6StepDefectN3LogStep_im_eq_arg_sub,
      step33Shift16DigammaPoint_add_three_add_one_arg_eq_arctan,
      step33Shift16DigammaPoint_add_three_arg_eq_arctan]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN3LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN3LogImLower, S0, E0, S1, E1,
        step33Shift16DigammaPointAddThreeArgRatio,
        step33Shift16DigammaPointAddFourArgRatio]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN3LogImUpper := by
      norm_num [step33Shift16M6StepDefectN3LogImUpper, S0, E0, S1, E1,
        step33Shift16DigammaPointAddThreeArgRatio,
        step33Shift16DigammaPointAddFourArgRatio]
    linarith

theorem step33Shift16M6StepDefectN3_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (3 : Complex)) =
      step33Shift16M6StepDefectN3LogStep +
        step33Shift16M6StepDefectN3AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN3LogStep,
    step33Shift16M6StepDefectN3AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN3AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN3AlgebraicPart.re =
      (-16713492593933127949989388303271012912650000158678510308465368562841515612337736117121359773594178588293597811208454320050842050961450768769855895481200 : Real) /
        (597468691280656696489955381075563198989444019863664964713381687956276426398364335616338792449655245716275802964641336508811867921759290198884026360791221 : Real) := by
  norm_num [step33Shift16M6StepDefectN3AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN3AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN3AlgebraicPart.im =
      (385746288404769748940904276849531448486537591506233509440062604202311931887918656070282494669650738872357851801638321319070033676600022320357697927720 : Real) /
        (19716466812261670984168527575493585566651652655500943835541595702557122071146023075339180150838623108637101497833164104790791641418056576563172869906110293 : Real) := by
  norm_num [step33Shift16M6StepDefectN3AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n3_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN3LogReLower <=
        step33Shift16M6StepDefectN3LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN3LogStep.re <=
        step33Shift16M6StepDefectN3LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN3LogImLower <=
        step33Shift16M6StepDefectN3LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN3LogStep.im <=
        step33Shift16M6StepDefectN3LogImUpper) :
    (((-59 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).re <=
        (-58 : Real) / ((10 : Real) ^ 25)) ∧
     ((61 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).im <=
        (62 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).re =
        step33Shift16M6StepDefectN3LogStep.re +
          step33Shift16M6StepDefectN3AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN3_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).im =
        step33Shift16M6StepDefectN3LogStep.im +
          step33Shift16M6StepDefectN3AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN3_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN3AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN3LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN3AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN3LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN3AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN3LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN3AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN3LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n3_component_interval :
    (((-59 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).re <=
        (-58 : Real) / ((10 : Real) ^ 25)) ∧
     ((61 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (3 : Complex))).im <=
        (62 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n3_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN3LogStep_re_bounds.1
    step33Shift16M6StepDefectN3LogStep_re_bounds.2
    step33Shift16M6StepDefectN3LogStep_im_bounds.1
    step33Shift16M6StepDefectN3LogStep_im_bounds.2

def step33Shift16M6StepDefectN4LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (5 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (4 : Complex))

def step33Shift16M6StepDefectN4AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (4 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN4LogReLower : Real :=
  (27212550927842555216035509303 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN4LogReUpper : Real :=
  (27212550927842555216035509304 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN4LogImLower : Real :=
  (-185142242449458003836457566038 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN4LogImUpper : Real :=
  (-185142242449458003836457566037 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN4LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN4LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2220101 : Real) / (2102501 : Real)) := by
  rw [step33Shift16M6StepDefectN4LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((5 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((4 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2220101 : Real) / (2102501 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 5,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 4]
  norm_num
  have h222 : (0 : Real) <= 2220101 := by
    norm_num
  have h210 : (0 : Real) <= 2102501 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hs222_ne : Real.sqrt (2220101 : Real) ≠ 0 := by
    positivity
  have hs210_ne : Real.sqrt (2102501 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs222_ne h40_ne,
    Real.log_div hs210_ne h40_ne]
  rw [Real.log_sqrt h222, Real.log_sqrt h210]
  have hratio :
      Real.log ((2220101 : Real) / (2102501 : Real)) =
        Real.log (2220101 : Real) - Real.log (2102501 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN4LogStep_re_bounds :
    step33Shift16M6StepDefectN4LogReLower <=
        step33Shift16M6StepDefectN4LogStep.re ∧
      step33Shift16M6StepDefectN4LogStep.re <=
        step33Shift16M6StepDefectN4LogReUpper := by
  let a : Real := (117600 : Real) / (2102501 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2220101 : Real) / (2102501 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN4LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN4LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN4LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN4LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN4LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN4LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN4LogReUpper := by
      norm_num [step33Shift16M6StepDefectN4LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN4LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN4LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN4LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN4LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN4LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (5 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (4 : Complex)) := by
  rw [step33Shift16M6StepDefectN4LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN4LogStep_im_bounds :
    step33Shift16M6StepDefectN4LogImLower <=
        step33Shift16M6StepDefectN4LogStep.im ∧
      step33Shift16M6StepDefectN4LogStep.im <=
        step33Shift16M6StepDefectN4LogImUpper := by
  let x0 : Real := (1 : Real) / (1450 : Real)
  let x1 : Real := (1 : Real) / (1490 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN4LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN4LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((5 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((4 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 5,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 4]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN4LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN4LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN4LogImUpper := by
      norm_num [step33Shift16M6StepDefectN4LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN4_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (4 : Complex)) =
      step33Shift16M6StepDefectN4LogStep +
        step33Shift16M6StepDefectN4AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN4LogStep,
    step33Shift16M6StepDefectN4AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN4AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN4AlgebraicPart.re =
      (-416305946124233870598422734799657691131686002514378471559411804145691648745933854873954160352756838836516456215651103648498360144605358724453137199568400 : Real) /
        (15298306550830922864530704373605108421403348815430644412793239695657548578788075374677654677322053425171467747424913246497788447852142294567953627599461743 : Real) := by
  norm_num [step33Shift16M6StepDefectN4AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN4AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN4AlgebraicPart.im =
      (1622171410650040289352797797698008234766995956706722469640390907370559408503484461593130839657602065168099279452781381442697119085291204255602719412760 : Real) /
        (87617573882031649133221306867011075504400997761102781636906736438765960042149886236790204061026305980527497098888139502669152019516814959798279867160553619 : Real) := by
  norm_num [step33Shift16M6StepDefectN4AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n4_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN4LogReLower <=
        step33Shift16M6StepDefectN4LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN4LogStep.re <=
        step33Shift16M6StepDefectN4LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN4LogImLower <=
        step33Shift16M6StepDefectN4LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN4LogStep.im <=
        step33Shift16M6StepDefectN4LogImUpper) :
    (((-39 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).re <=
        (-38 : Real) / ((10 : Real) ^ 25)) ∧
     ((39 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).im <=
        (40 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).re =
        step33Shift16M6StepDefectN4LogStep.re +
          step33Shift16M6StepDefectN4AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN4_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).im =
        step33Shift16M6StepDefectN4LogStep.im +
          step33Shift16M6StepDefectN4AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN4_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN4AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN4LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN4AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN4LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN4AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN4LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN4AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN4LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n4_component_interval :
    (((-39 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).re <=
        (-38 : Real) / ((10 : Real) ^ 25)) ∧
     ((39 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (4 : Complex))).im <=
        (40 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n4_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN4LogStep_re_bounds.1
    step33Shift16M6StepDefectN4LogStep_re_bounds.2
    step33Shift16M6StepDefectN4LogStep_im_bounds.1
    step33Shift16M6StepDefectN4LogStep_im_bounds.2

def step33Shift16M6StepDefectN5LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (6 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (5 : Complex))

def step33Shift16M6StepDefectN5AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (5 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN5LogReLower : Real :=
  (26491603824963517427835120267 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN5LogReUpper : Real :=
  (26491603824963517427835120268 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN5LogImLower : Real :=
  (-175461606569875157382063969100 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN5LogImUpper : Real :=
  (-175461606569875157382063969099 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN5LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN5LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2340901 : Real) / (2220101 : Real)) := by
  rw [step33Shift16M6StepDefectN5LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((6 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((5 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2340901 : Real) / (2220101 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 6,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 5]
  norm_num
  have h234 : (0 : Real) <= 2340901 := by
    norm_num
  have h222 : (0 : Real) <= 2220101 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hs234_ne : Real.sqrt (2340901 : Real) ≠ 0 := by
    positivity
  have hs222_ne : Real.sqrt (2220101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs234_ne h40_ne,
    Real.log_div hs222_ne h40_ne]
  rw [Real.log_sqrt h234, Real.log_sqrt h222]
  have hratio :
      Real.log ((2340901 : Real) / (2220101 : Real)) =
        Real.log (2340901 : Real) - Real.log (2220101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN5LogStep_re_bounds :
    step33Shift16M6StepDefectN5LogReLower <=
        step33Shift16M6StepDefectN5LogStep.re ∧
      step33Shift16M6StepDefectN5LogStep.re <=
        step33Shift16M6StepDefectN5LogReUpper := by
  let a : Real := (120800 : Real) / (2220101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2340901 : Real) / (2220101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN5LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN5LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN5LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN5LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN5LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN5LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN5LogReUpper := by
      norm_num [step33Shift16M6StepDefectN5LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN5LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN5LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN5LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN5LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN5LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (6 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (5 : Complex)) := by
  rw [step33Shift16M6StepDefectN5LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN5LogStep_im_bounds :
    step33Shift16M6StepDefectN5LogImLower <=
        step33Shift16M6StepDefectN5LogStep.im ∧
      step33Shift16M6StepDefectN5LogStep.im <=
        step33Shift16M6StepDefectN5LogImUpper := by
  let x0 : Real := (1 : Real) / (1490 : Real)
  let x1 : Real := (1 : Real) / (1530 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN5LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN5LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((6 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((5 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 6,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 5]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN5LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN5LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN5LogImUpper := by
      norm_num [step33Shift16M6StepDefectN5LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN5_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (5 : Complex)) =
      step33Shift16M6StepDefectN5LogStep +
        step33Shift16M6StepDefectN5AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN5LogStep,
    step33Shift16M6StepDefectN5AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN5AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN5AlgebraicPart.re =
      (-30883956999538153098127697482335646329398934559094927952342783158940659181349031169077256858152411891344579517507884408206799674735560755640267488853181200 : Real) /
        (1165801708480769361010337410052245572415793755785470927961924524121747197897102528814261895370287626835201086401686920175347577046338227390607396239353439003 : Real) := by
  norm_num [step33Shift16M6StepDefectN5AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN5AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN5AlgebraicPart.im =
      (61366032213582313288657764921865892864130250529570228161978854804449873707636526615665694626287914355601431513110123046981520353661726806644383143716360 : Real) /
        (3497405125442308083031012230156736717247381267356412783885773572365241593691307586442785686110862880505603259205060760526042731139014682171822188718060317009 : Real) := by
  norm_num [step33Shift16M6StepDefectN5AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n5_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN5LogReLower <=
        step33Shift16M6StepDefectN5LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN5LogStep.re <=
        step33Shift16M6StepDefectN5LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN5LogImLower <=
        step33Shift16M6StepDefectN5LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN5LogStep.im <=
        step33Shift16M6StepDefectN5LogImUpper) :
    (((-26 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).re <=
        (-25 : Real) / ((10 : Real) ^ 25)) ∧
     ((25 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).im <=
        (26 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).re =
        step33Shift16M6StepDefectN5LogStep.re +
          step33Shift16M6StepDefectN5AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN5_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).im =
        step33Shift16M6StepDefectN5LogStep.im +
          step33Shift16M6StepDefectN5AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN5_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN5AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN5LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN5AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN5LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN5AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN5LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN5AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN5LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n5_component_interval :
    (((-26 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).re <=
        (-25 : Real) / ((10 : Real) ^ 25)) ∧
     ((25 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (5 : Complex))).im <=
        (26 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n5_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN5LogStep_re_bounds.1
    step33Shift16M6StepDefectN5LogStep_re_bounds.2
    step33Shift16M6StepDefectN5LogStep_im_bounds.1
    step33Shift16M6StepDefectN5LogStep_im_bounds.2

def step33Shift16M6StepDefectN6LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (7 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (6 : Complex))

def step33Shift16M6StepDefectN6AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (6 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN6LogReLower : Real :=
  (25807873210800291245311444343 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN6LogReUpper : Real :=
  (25807873210800291245311444344 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN6LogImLower : Real :=
  (-166520891487505197989978446886 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN6LogImUpper : Real :=
  (-166520891487505197989978446885 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN6LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN6LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2464901 : Real) / (2340901 : Real)) := by
  rw [step33Shift16M6StepDefectN6LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((7 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((6 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2464901 : Real) / (2340901 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 7,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 6]
  norm_num
  have h246 : (0 : Real) <= 2464901 := by
    norm_num
  have h234 : (0 : Real) <= 2340901 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hs246_ne : Real.sqrt (2464901 : Real) ≠ 0 := by
    positivity
  have hs234_ne : Real.sqrt (2340901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs246_ne h40_ne,
    Real.log_div hs234_ne h40_ne]
  rw [Real.log_sqrt h246, Real.log_sqrt h234]
  have hratio :
      Real.log ((2464901 : Real) / (2340901 : Real)) =
        Real.log (2464901 : Real) - Real.log (2340901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN6LogStep_re_bounds :
    step33Shift16M6StepDefectN6LogReLower <=
        step33Shift16M6StepDefectN6LogStep.re ∧
      step33Shift16M6StepDefectN6LogStep.re <=
        step33Shift16M6StepDefectN6LogReUpper := by
  let a : Real := (124000 : Real) / (2340901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2464901 : Real) / (2340901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN6LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN6LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN6LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN6LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN6LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN6LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN6LogReUpper := by
      norm_num [step33Shift16M6StepDefectN6LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN6LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN6LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN6LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN6LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN6LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (7 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (6 : Complex)) := by
  rw [step33Shift16M6StepDefectN6LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN6LogStep_im_bounds :
    step33Shift16M6StepDefectN6LogImLower <=
        step33Shift16M6StepDefectN6LogStep.im ∧
      step33Shift16M6StepDefectN6LogStep.im <=
        step33Shift16M6StepDefectN6LogImUpper := by
  let x0 : Real := (1 : Real) / (1530 : Real)
  let x1 : Real := (1 : Real) / (1570 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN6LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN6LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((7 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((6 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 7,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 6]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN6LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN6LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN6LogImUpper := by
      norm_num [step33Shift16M6StepDefectN6LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN6_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (6 : Complex)) =
      step33Shift16M6StepDefectN6LogStep +
        step33Shift16M6StepDefectN6AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN6LogStep,
    step33Shift16M6StepDefectN6AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN6AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN6AlgebraicPart.re =
      (-8119972050490501360877372642783454666195236159545049590923322186470941630657696181586381243260827459585248589371773644566399663153438271688654556751722000 : Real) /
        (314631584872030005528893039353646650111345877132761039985776549247215649522415310151759423627097688333364616282686563972461208995208562139094811026277637831 : Real) := by
  norm_num [step33Shift16M6StepDefectN6AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN6AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN6AlgebraicPart.im =
      (15717819600905127172919793388920035136512396568624916006734706069793447469252236121262859719898149171512805440715974994122943879492813665354750354983720 : Real) /
        (943894754616090016586679118060939950334037631398283119957329647741646948567245930455278270881293065000093848848059691917383626985625686417284433078832913493 : Real) := by
  norm_num [step33Shift16M6StepDefectN6AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n6_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN6LogReLower <=
        step33Shift16M6StepDefectN6LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN6LogStep.re <=
        step33Shift16M6StepDefectN6LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN6LogImLower <=
        step33Shift16M6StepDefectN6LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN6LogStep.im <=
        step33Shift16M6StepDefectN6LogImUpper) :
    (((-18 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).re <=
        (-17 : Real) / ((10 : Real) ^ 25)) ∧
     ((16 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).im <=
        (17 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).re =
        step33Shift16M6StepDefectN6LogStep.re +
          step33Shift16M6StepDefectN6AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN6_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).im =
        step33Shift16M6StepDefectN6LogStep.im +
          step33Shift16M6StepDefectN6AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN6_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN6AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN6LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN6AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN6LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN6AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN6LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN6AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN6LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n6_component_interval :
    (((-18 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).re <=
        (-17 : Real) / ((10 : Real) ^ 25)) ∧
     ((16 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (6 : Complex))).im <=
        (17 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n6_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN6LogStep_re_bounds.1
    step33Shift16M6StepDefectN6LogStep_re_bounds.2
    step33Shift16M6StepDefectN6LogStep_im_bounds.1
    step33Shift16M6StepDefectN6LogStep_im_bounds.2

def step33Shift16M6StepDefectN7LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (8 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (7 : Complex))

def step33Shift16M6StepDefectN7AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (7 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN7LogReLower : Real :=
  (25158549681965836025982526296 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN7LogReUpper : Real :=
  (25158549681965836025982526297 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN7LogImLower : Real :=
  (-158246564750581931826178182202 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN7LogImUpper : Real :=
  (-158246564750581931826178182201 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN7LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN7LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2592101 : Real) / (2464901 : Real)) := by
  rw [step33Shift16M6StepDefectN7LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((8 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((7 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2592101 : Real) / (2464901 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 8,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 7]
  norm_num
  have h259 : (0 : Real) <= 2592101 := by
    norm_num
  have h246 : (0 : Real) <= 2464901 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hs259_ne : Real.sqrt (2592101 : Real) ≠ 0 := by
    positivity
  have hs246_ne : Real.sqrt (2464901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hs259_ne h40_ne,
    Real.log_div hs246_ne h40_ne]
  rw [Real.log_sqrt h259, Real.log_sqrt h246]
  have hratio :
      Real.log ((2592101 : Real) / (2464901 : Real)) =
        Real.log (2592101 : Real) - Real.log (2464901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN7LogStep_re_bounds :
    step33Shift16M6StepDefectN7LogReLower <=
        step33Shift16M6StepDefectN7LogStep.re ∧
      step33Shift16M6StepDefectN7LogStep.re <=
        step33Shift16M6StepDefectN7LogReUpper := by
  let a : Real := (127200 : Real) / (2464901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2592101 : Real) / (2464901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN7LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN7LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN7LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN7LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN7LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN7LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN7LogReUpper := by
      norm_num [step33Shift16M6StepDefectN7LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN7LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN7LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN7LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN7LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN7LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (8 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (7 : Complex)) := by
  rw [step33Shift16M6StepDefectN7LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN7LogStep_im_bounds :
    step33Shift16M6StepDefectN7LogImLower <=
        step33Shift16M6StepDefectN7LogStep.im ∧
      step33Shift16M6StepDefectN7LogStep.im <=
        step33Shift16M6StepDefectN7LogImUpper := by
  let x0 : Real := (1 : Real) / (1570 : Real)
  let x1 : Real := (1 : Real) / (1610 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN7LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN7LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((8 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((7 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 8,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 7]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN7LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN7LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN7LogImUpper := by
      norm_num [step33Shift16M6StepDefectN7LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN7_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (7 : Complex)) =
      step33Shift16M6StepDefectN7LogStep +
        step33Shift16M6StepDefectN7AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN7LogStep,
    step33Shift16M6StepDefectN7AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN7AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN7AlgebraicPart.re =
      (-8965884383463011133009806694759967059731212874049198639624796620286856193344902087284667503963153028790034959176014350431051657683647692609259735579497200 : Real) /
        (356375248048974015088227777465338959212224627842789019195003893325880038029905538838952100520409854023067757631944099476290602977421909916232185202186628077 : Real) := by
  norm_num [step33Shift16M6StepDefectN7AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN7AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN7AlgebraicPart.im =
      (50755642889297997373801920386066039585608377375665459998568076721763546318012848330697740701567516358852818233296091524604544660642295435619276173319720 : Real) /
        (3207377232440766135794049997188050632910021650585101172755035039932920342269149849550568904683688686207609818687496895286615426796797189246089666819679652693 : Real) := by
  norm_num [step33Shift16M6StepDefectN7AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n7_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN7LogReLower <=
        step33Shift16M6StepDefectN7LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN7LogStep.re <=
        step33Shift16M6StepDefectN7LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN7LogImLower <=
        step33Shift16M6StepDefectN7LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN7LogStep.im <=
        step33Shift16M6StepDefectN7LogImUpper) :
    (((-12 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).re <=
        (-11 : Real) / ((10 : Real) ^ 25)) ∧
     ((11 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).im <=
        (12 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).re =
        step33Shift16M6StepDefectN7LogStep.re +
          step33Shift16M6StepDefectN7AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN7_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).im =
        step33Shift16M6StepDefectN7LogStep.im +
          step33Shift16M6StepDefectN7AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN7_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN7AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN7LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN7AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN7LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN7AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN7LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN7AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN7LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n7_component_interval :
    (((-12 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).re <=
        (-11 : Real) / ((10 : Real) ^ 25)) ∧
     ((11 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (7 : Complex))).im <=
        (12 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n7_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN7LogStep_re_bounds.1
    step33Shift16M6StepDefectN7LogStep_re_bounds.2
    step33Shift16M6StepDefectN7LogStep_im_bounds.1
    step33Shift16M6StepDefectN7LogStep_im_bounds.2

def step33Shift16M6StepDefectN8LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (9 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (8 : Complex))

def step33Shift16M6StepDefectN8AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (8 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN8LogReLower : Real :=
  (24541099677057524623195588710 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN8LogReUpper : Real :=
  (24541099677057524623195588711 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN8LogImLower : Real :=
  (-150574006924811983100207868506 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN8LogImUpper : Real :=
  (-150574006924811983100207868505 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN8LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN8LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2722501 : Real) / (2592101 : Real)) := by
  rw [step33Shift16M6StepDefectN8LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((9 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((8 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2722501 : Real) / (2592101 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 9,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 8]
  norm_num
  have hNum : (0 : Real) <= 2722501 := by
    norm_num
  have hDen : (0 : Real) <= 2592101 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (2722501 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (2592101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((2722501 : Real) / (2592101 : Real)) =
        Real.log (2722501 : Real) - Real.log (2592101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN8LogStep_re_bounds :
    step33Shift16M6StepDefectN8LogReLower <=
        step33Shift16M6StepDefectN8LogStep.re ∧
      step33Shift16M6StepDefectN8LogStep.re <=
        step33Shift16M6StepDefectN8LogReUpper := by
  let a : Real := (130400 : Real) / (2592101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2722501 : Real) / (2592101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN8LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN8LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN8LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN8LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN8LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN8LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN8LogReUpper := by
      norm_num [step33Shift16M6StepDefectN8LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN8LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN8LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN8LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN8LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN8LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (9 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (8 : Complex)) := by
  rw [step33Shift16M6StepDefectN8LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN8LogStep_im_bounds :
    step33Shift16M6StepDefectN8LogImLower <=
        step33Shift16M6StepDefectN8LogStep.im ∧
      step33Shift16M6StepDefectN8LogStep.im <=
        step33Shift16M6StepDefectN8LogImUpper := by
  let x0 : Real := (1 : Real) / (1610 : Real)
  let x1 : Real := (1 : Real) / (1650 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN8LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN8LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((9 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((8 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 9,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 8]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN8LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN8LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN8LogImUpper := by
      norm_num [step33Shift16M6StepDefectN8LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN8_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (8 : Complex)) =
      step33Shift16M6StepDefectN8LogStep +
        step33Shift16M6StepDefectN8AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN8LogStep,
    step33Shift16M6StepDefectN8AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN8AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN8AlgebraicPart.re =
      (-86485959899542492389634694879377880391649505717362714705504899701537066128163436897100423887514620914234523770686966434659447756159950190447733145814541200 : Real) /
        (3524127322639689887817721983750621732165732965172087749721296760726289330684803991439107775228427392545159015472173531565993558062689300437788271446766431431 : Real) := by
  norm_num [step33Shift16M6StepDefectN8AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN8AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN8AlgebraicPart.im =
      (159192591564920333686413021701770540156094598565530382572636889861039283531784234924920696758542090096798154740945049460336612839587860215288089804647720 : Real) /
        (10572381967919069663453165951251865196497198895516263249163890282178867992054411974317323325685282177635477046416520594697980674188067901313364814340299294293 : Real) := by
  norm_num [step33Shift16M6StepDefectN8AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n8_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN8LogReLower <=
        step33Shift16M6StepDefectN8LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN8LogStep.re <=
        step33Shift16M6StepDefectN8LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN8LogImLower <=
        step33Shift16M6StepDefectN8LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN8LogStep.im <=
        step33Shift16M6StepDefectN8LogImUpper) :
    (((-9 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).re <=
        (-8 : Real) / ((10 : Real) ^ 25)) ∧
     ((7 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).im <=
        (8 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).re =
        step33Shift16M6StepDefectN8LogStep.re +
          step33Shift16M6StepDefectN8AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN8_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).im =
        step33Shift16M6StepDefectN8LogStep.im +
          step33Shift16M6StepDefectN8AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN8_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN8AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN8LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN8AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN8LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN8AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN8LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN8AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN8LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n8_component_interval :
    (((-9 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).re <=
        (-8 : Real) / ((10 : Real) ^ 25)) ∧
     ((7 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (8 : Complex))).im <=
        (8 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n8_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN8LogStep_re_bounds.1
    step33Shift16M6StepDefectN8LogStep_re_bounds.2
    step33Shift16M6StepDefectN8LogStep_im_bounds.1
    step33Shift16M6StepDefectN8LogStep_im_bounds.2

def step33Shift16M6StepDefectN9LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (10 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (9 : Complex))

def step33Shift16M6StepDefectN9AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (9 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN9LogReLower : Real :=
  (23953232431665157352239505417 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN9LogReUpper : Real :=
  (23953232431665157352239505418 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN9LogImLower : Real :=
  (-143446245840530174720623928556 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN9LogImUpper : Real :=
  (-143446245840530174720623928555 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN9LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN9LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2856101 : Real) / (2722501 : Real)) := by
  rw [step33Shift16M6StepDefectN9LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((10 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((9 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2856101 : Real) / (2722501 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 10,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 9]
  norm_num
  have hNum : (0 : Real) <= 2856101 := by
    norm_num
  have hDen : (0 : Real) <= 2722501 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (2856101 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (2722501 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((2856101 : Real) / (2722501 : Real)) =
        Real.log (2856101 : Real) - Real.log (2722501 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN9LogStep_re_bounds :
    step33Shift16M6StepDefectN9LogReLower <=
        step33Shift16M6StepDefectN9LogStep.re ∧
      step33Shift16M6StepDefectN9LogStep.re <=
        step33Shift16M6StepDefectN9LogReUpper := by
  let a : Real := (133600 : Real) / (2722501 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2856101 : Real) / (2722501 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN9LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN9LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN9LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN9LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN9LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN9LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN9LogReUpper := by
      norm_num [step33Shift16M6StepDefectN9LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN9LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN9LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN9LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN9LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN9LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (10 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (9 : Complex)) := by
  rw [step33Shift16M6StepDefectN9LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN9LogStep_im_bounds :
    step33Shift16M6StepDefectN9LogImLower <=
        step33Shift16M6StepDefectN9LogStep.im ∧
      step33Shift16M6StepDefectN9LogStep.im <=
        step33Shift16M6StepDefectN9LogImUpper := by
  let x0 : Real := (1 : Real) / (1650 : Real)
  let x1 : Real := (1 : Real) / (1690 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN9LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN9LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((10 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((9 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 10,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 9]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN9LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN9LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN9LogImUpper := by
      norm_num [step33Shift16M6StepDefectN9LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN9_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (9 : Complex)) =
      step33Shift16M6StepDefectN9LogStep +
        step33Shift16M6StepDefectN9AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN9LogStep,
    step33Shift16M6StepDefectN9AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN9AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN9AlgebraicPart.re =
      (-270318282487713508819910770038912373208712376574101112855365242624845456318090190987004188570129244406073512414290043765402647593151603787001539801251550800 : Real) /
        (11285252763228907857649527875282499781686626580983817315634368595537040469987521076758008178003182514443564763215358416625298598987231879506281175337159039431 : Real) := by
  norm_num [step33Shift16M6StepDefectN9AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN9AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN9AlgebraicPart.im =
      (485648142673996915342379424997802894301205403025491206176121438707352367382298056574561026046808790584037880113945577285487386308638651358405936362567720 : Real) /
        (33855758289686723572948583625847499345059879742951451946903105786611121409962563230274024534009547543330694289646075249875895796961695638518843526011477118293 : Real) := by
  norm_num [step33Shift16M6StepDefectN9AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n9_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN9LogReLower <=
        step33Shift16M6StepDefectN9LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN9LogStep.re <=
        step33Shift16M6StepDefectN9LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN9LogImLower <=
        step33Shift16M6StepDefectN9LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN9LogStep.im <=
        step33Shift16M6StepDefectN9LogImUpper) :
    (((-6 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).re <=
        (-5 : Real) / ((10 : Real) ^ 25)) ∧
     ((5 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).im <=
        (6 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).re =
        step33Shift16M6StepDefectN9LogStep.re +
          step33Shift16M6StepDefectN9AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN9_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).im =
        step33Shift16M6StepDefectN9LogStep.im +
          step33Shift16M6StepDefectN9AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN9_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN9AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN9LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN9AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN9LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN9AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN9LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN9AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN9LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n9_component_interval :
    (((-6 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).re <=
        (-5 : Real) / ((10 : Real) ^ 25)) ∧
     ((5 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (9 : Complex))).im <=
        (6 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n9_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN9LogStep_re_bounds.1
    step33Shift16M6StepDefectN9LogStep_re_bounds.2
    step33Shift16M6StepDefectN9LogStep_im_bounds.1
    step33Shift16M6StepDefectN9LogStep_im_bounds.2

def step33Shift16M6StepDefectN10LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (11 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (10 : Complex))

def step33Shift16M6StepDefectN10AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (10 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN10LogReLower : Real :=
  (23392871572856733776669996629 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN10LogReUpper : Real :=
  (23392871572856733776669996630 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN10LogImLower : Real :=
  (-136812895701387718999340281786 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN10LogImUpper : Real :=
  (-136812895701387718999340281785 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN10LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN10LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((2992901 : Real) / (2856101 : Real)) := by
  rw [step33Shift16M6StepDefectN10LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((11 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((10 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((2992901 : Real) / (2856101 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 11,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 10]
  norm_num
  have hNum : (0 : Real) <= 2992901 := by
    norm_num
  have hDen : (0 : Real) <= 2856101 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (2992901 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (2856101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((2992901 : Real) / (2856101 : Real)) =
        Real.log (2992901 : Real) - Real.log (2856101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN10LogStep_re_bounds :
    step33Shift16M6StepDefectN10LogReLower <=
        step33Shift16M6StepDefectN10LogStep.re ∧
      step33Shift16M6StepDefectN10LogStep.re <=
        step33Shift16M6StepDefectN10LogReUpper := by
  let a : Real := (136800 : Real) / (2856101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((2992901 : Real) / (2856101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN10LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN10LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN10LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN10LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN10LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN10LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN10LogReUpper := by
      norm_num [step33Shift16M6StepDefectN10LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN10LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN10LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN10LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN10LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN10LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (11 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (10 : Complex)) := by
  rw [step33Shift16M6StepDefectN10LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN10LogStep_im_bounds :
    step33Shift16M6StepDefectN10LogImLower <=
        step33Shift16M6StepDefectN10LogStep.im ∧
      step33Shift16M6StepDefectN10LogStep.im <=
        step33Shift16M6StepDefectN10LogImUpper := by
  let x0 : Real := (1 : Real) / (1690 : Real)
  let x1 : Real := (1 : Real) / (1730 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN10LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN10LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((11 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((10 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 11,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 10]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN10LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN10LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN10LogImUpper := by
      norm_num [step33Shift16M6StepDefectN10LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN10_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (10 : Complex)) =
      step33Shift16M6StepDefectN10LogStep +
        step33Shift16M6StepDefectN10AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN10LogStep,
    step33Shift16M6StepDefectN10AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN10AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN10AlgebraicPart.re =
      (-274135458395893086063962242754401073397141725896632929978671783945571602619160678591149796004749063785963158112662649530030603938615228925008870856747066800 : Real) /
        (11718760458377351201001193924437707598630857697391540815880561060144829459089748655387922960497518748652849579958965162115594505611295577264318206357168036077 : Real) := by
  norm_num [step33Shift16M6StepDefectN10AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN10AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN10AlgebraicPart.im =
      (1442949797107374378877860247487879016517739853519769622432458555576458123188508448191182319778160619249303590843296395146809246646724478102630078951079720 : Real) /
        (105468844125396160809010745319939368387677719276523867342925049541303465131807737898491306644477668737875646219630686459040350550501660195378863857214512324693 : Real) := by
  norm_num [step33Shift16M6StepDefectN10AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n10_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN10LogReLower <=
        step33Shift16M6StepDefectN10LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN10LogStep.re <=
        step33Shift16M6StepDefectN10LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN10LogImLower <=
        step33Shift16M6StepDefectN10LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN10LogStep.im <=
        step33Shift16M6StepDefectN10LogImUpper) :
    (((-5 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).re <=
        (-4 : Real) / ((10 : Real) ^ 25)) ∧
     ((3 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).im <=
        (4 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).re =
        step33Shift16M6StepDefectN10LogStep.re +
          step33Shift16M6StepDefectN10AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN10_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).im =
        step33Shift16M6StepDefectN10LogStep.im +
          step33Shift16M6StepDefectN10AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN10_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN10AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN10LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN10AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN10LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN10AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN10LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN10AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN10LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n10_component_interval :
    (((-5 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).re <=
        (-4 : Real) / ((10 : Real) ^ 25)) ∧
     ((3 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (10 : Complex))).im <=
        (4 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n10_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN10LogStep_re_bounds.1
    step33Shift16M6StepDefectN10LogStep_re_bounds.2
    step33Shift16M6StepDefectN10LogStep_im_bounds.1
    step33Shift16M6StepDefectN10LogStep_im_bounds.2

def step33Shift16M6StepDefectN11LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (12 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (11 : Complex))

def step33Shift16M6StepDefectN11AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (11 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN11LogReLower : Real :=
  (22858130610545736564944809297 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN11LogReUpper : Real :=
  (22858130610545736564944809298 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN11LogImLower : Real :=
  (-130629264017499094197982538238 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN11LogImUpper : Real :=
  (-130629264017499094197982538237 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN11LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN11LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((3132901 : Real) / (2992901 : Real)) := by
  rw [step33Shift16M6StepDefectN11LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((12 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((11 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((3132901 : Real) / (2992901 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 12,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 11]
  norm_num
  have hNum : (0 : Real) <= 3132901 := by
    norm_num
  have hDen : (0 : Real) <= 2992901 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (3132901 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (2992901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((3132901 : Real) / (2992901 : Real)) =
        Real.log (3132901 : Real) - Real.log (2992901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN11LogStep_re_bounds :
    step33Shift16M6StepDefectN11LogReLower <=
        step33Shift16M6StepDefectN11LogStep.re ∧
      step33Shift16M6StepDefectN11LogStep.re <=
        step33Shift16M6StepDefectN11LogReUpper := by
  let a : Real := (140000 : Real) / (2992901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((3132901 : Real) / (2992901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN11LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN11LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN11LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN11LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN11LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN11LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN11LogReUpper := by
      norm_num [step33Shift16M6StepDefectN11LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN11LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN11LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN11LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN11LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN11LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (12 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (11 : Complex)) := by
  rw [step33Shift16M6StepDefectN11LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN11LogStep_im_bounds :
    step33Shift16M6StepDefectN11LogImLower <=
        step33Shift16M6StepDefectN11LogStep.im ∧
      step33Shift16M6StepDefectN11LogStep.im <=
        step33Shift16M6StepDefectN11LogImUpper := by
  let x0 : Real := (1 : Real) / (1730 : Real)
  let x1 : Real := (1 : Real) / (1770 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN11LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN11LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((12 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((11 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 12,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 11]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN11LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN11LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN11LogImUpper := by
      norm_num [step33Shift16M6StepDefectN11LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN11_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (11 : Complex)) =
      step33Shift16M6StepDefectN11LogStep +
        step33Shift16M6StepDefectN11AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN11LogStep,
    step33Shift16M6StepDefectN11AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN11AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN11AlgebraicPart.re =
      (-348355701007937585149398611867363335998393920260637484115035572904097759521910814918684705918306002825944751874565913041290648512222923160424420318179310000 : Real) /
        (15239903338693041646385317170256945199349889817708917784558909653168762224870024141612152795123787045968556056773466874182549714256182482883264707225696096833 : Real) := by
  norm_num [step33Shift16M6StepDefectN11AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN11AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN11AlgebraicPart.im =
      (4180632449345728438190039748717160807837868635834581352452272695854988394282264321411028171329651461985146587506813222311385438899491866670778842664583720 : Real) /
        (320037970112553874574091660575395849186347686171887273475737102716544006722270506973855208697599527965339677192242804357833543999379832140548558851739618033493 : Real) := by
  norm_num [step33Shift16M6StepDefectN11AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n11_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN11LogReLower <=
        step33Shift16M6StepDefectN11LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN11LogStep.re <=
        step33Shift16M6StepDefectN11LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN11LogImLower <=
        step33Shift16M6StepDefectN11LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN11LogStep.im <=
        step33Shift16M6StepDefectN11LogImUpper) :
    (((-3 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).re <=
        (-2 : Real) / ((10 : Real) ^ 25)) ∧
     ((2 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).im <=
        (3 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).re =
        step33Shift16M6StepDefectN11LogStep.re +
          step33Shift16M6StepDefectN11AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN11_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).im =
        step33Shift16M6StepDefectN11LogStep.im +
          step33Shift16M6StepDefectN11AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN11_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN11AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN11LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN11AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN11LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN11AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN11LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN11AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN11LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n11_component_interval :
    (((-3 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).re <=
        (-2 : Real) / ((10 : Real) ^ 25)) ∧
     ((2 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (11 : Complex))).im <=
        (3 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n11_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN11LogStep_re_bounds.1
    step33Shift16M6StepDefectN11LogStep_re_bounds.2
    step33Shift16M6StepDefectN11LogStep_im_bounds.1
    step33Shift16M6StepDefectN11LogStep_im_bounds.2

def step33Shift16M6StepDefectN12LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (13 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (12 : Complex))

def step33Shift16M6StepDefectN12AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (12 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN12LogReLower : Real :=
  (22347291715952715771768880083 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN12LogReUpper : Real :=
  (22347291715952715771768880084 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN12LogImLower : Real :=
  (-124855596692454999171025015819 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN12LogImUpper : Real :=
  (-124855596692454999171025015818 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN12LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN12LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((3276101 : Real) / (3132901 : Real)) := by
  rw [step33Shift16M6StepDefectN12LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((13 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((12 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((3276101 : Real) / (3132901 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 13,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 12]
  norm_num
  have hNum : (0 : Real) <= 3276101 := by
    norm_num
  have hDen : (0 : Real) <= 3132901 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (3276101 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (3132901 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((3276101 : Real) / (3132901 : Real)) =
        Real.log (3276101 : Real) - Real.log (3132901 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN12LogStep_re_bounds :
    step33Shift16M6StepDefectN12LogReLower <=
        step33Shift16M6StepDefectN12LogStep.re ∧
      step33Shift16M6StepDefectN12LogStep.re <=
        step33Shift16M6StepDefectN12LogReUpper := by
  let a : Real := (143200 : Real) / (3132901 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((3276101 : Real) / (3132901 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN12LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN12LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN12LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN12LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN12LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN12LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN12LogReUpper := by
      norm_num [step33Shift16M6StepDefectN12LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN12LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN12LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN12LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN12LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN12LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (13 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (12 : Complex)) := by
  rw [step33Shift16M6StepDefectN12LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN12LogStep_im_bounds :
    step33Shift16M6StepDefectN12LogImLower <=
        step33Shift16M6StepDefectN12LogStep.im ∧
      step33Shift16M6StepDefectN12LogStep.im <=
        step33Shift16M6StepDefectN12LogImUpper := by
  let x0 : Real := (1 : Real) / (1770 : Real)
  let x1 : Real := (1 : Real) / (1810 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN12LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN12LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((13 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((12 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 13,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 12]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN12LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN12LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN12LogImUpper := by
      norm_num [step33Shift16M6StepDefectN12LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN12_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (12 : Complex)) =
      step33Shift16M6StepDefectN12LogStep +
        step33Shift16M6StepDefectN12AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN12LogStep,
    step33Shift16M6StepDefectN12AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN12AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN12AlgebraicPart.re =
      (-7054793756682310724453676406530744690256188903585680895252658232104628278383767700323659771731853507052432738264751633746981549162914765702294280043405139600 : Real) /
        (315688981302652174780228161419527951367363889734425767766918894049151734675323902424060360358678740743275142349429317138416490893948593918103618840182720428231 : Real) := by
  norm_num [step33Shift16M6StepDefectN12AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN12AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN12AlgebraicPart.im =
      (11824660838932772084734995419021273118930633644676694847067228527373985182060057577358189709285819913606680328961947761030801886299568998994120292987879720 : Real) /
        (947066943907956524340684484258583854102091669203277303300756682147455204025971707272181081076036222229825427048287951415249472681845781754310856520548161284693 : Real) := by
  norm_num [step33Shift16M6StepDefectN12AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n12_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN12LogReLower <=
        step33Shift16M6StepDefectN12LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN12LogStep.re <=
        step33Shift16M6StepDefectN12LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN12LogImLower <=
        step33Shift16M6StepDefectN12LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN12LogStep.im <=
        step33Shift16M6StepDefectN12LogImUpper) :
    (((-3 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).re <=
        (-2 : Real) / ((10 : Real) ^ 25)) ∧
     ((1 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).im <=
        (2 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).re =
        step33Shift16M6StepDefectN12LogStep.re +
          step33Shift16M6StepDefectN12AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN12_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).im =
        step33Shift16M6StepDefectN12LogStep.im +
          step33Shift16M6StepDefectN12AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN12_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN12AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN12LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN12AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN12LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN12AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN12LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN12AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN12LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n12_component_interval :
    (((-3 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).re <=
        (-2 : Real) / ((10 : Real) ^ 25)) ∧
     ((1 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (12 : Complex))).im <=
        (2 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n12_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN12LogStep_re_bounds.1
    step33Shift16M6StepDefectN12LogStep_re_bounds.2
    step33Shift16M6StepDefectN12LogStep_im_bounds.1
    step33Shift16M6StepDefectN12LogStep_im_bounds.2

def step33Shift16M6StepDefectN13LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (14 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (13 : Complex))

def step33Shift16M6StepDefectN13AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (13 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN13LogReLower : Real :=
  (21858787284045126272455602929 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN13LogReUpper : Real :=
  (21858787284045126272455602930 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN13LogImLower : Real :=
  (-119456437367339459087859374580 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN13LogImUpper : Real :=
  (-119456437367339459087859374579 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN13LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN13LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((3422501 : Real) / (3276101 : Real)) := by
  rw [step33Shift16M6StepDefectN13LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((14 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((13 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((3422501 : Real) / (3276101 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 14,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 13]
  norm_num
  have hNum : (0 : Real) <= 3422501 := by
    norm_num
  have hDen : (0 : Real) <= 3276101 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (3422501 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (3276101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((3422501 : Real) / (3276101 : Real)) =
        Real.log (3422501 : Real) - Real.log (3276101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN13LogStep_re_bounds :
    step33Shift16M6StepDefectN13LogReLower <=
        step33Shift16M6StepDefectN13LogStep.re ∧
      step33Shift16M6StepDefectN13LogStep.re <=
        step33Shift16M6StepDefectN13LogReUpper := by
  let a : Real := (146400 : Real) / (3276101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((3422501 : Real) / (3276101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN13LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN13LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN13LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN13LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN13LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN13LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN13LogReUpper := by
      norm_num [step33Shift16M6StepDefectN13LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN13LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN13LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN13LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN13LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN13LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (14 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (13 : Complex)) := by
  rw [step33Shift16M6StepDefectN13LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN13LogStep_im_bounds :
    step33Shift16M6StepDefectN13LogImLower <=
        step33Shift16M6StepDefectN13LogStep.im ∧
      step33Shift16M6StepDefectN13LogStep.im <=
        step33Shift16M6StepDefectN13LogImUpper := by
  let x0 : Real := (1 : Real) / (1810 : Real)
  let x1 : Real := (1 : Real) / (1850 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN13LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN13LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((14 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((13 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 14,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 13]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN13LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN13LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN13LogImUpper := by
      norm_num [step33Shift16M6StepDefectN13LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN13_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (13 : Complex)) =
      step33Shift16M6StepDefectN13LogStep +
        step33Shift16M6StepDefectN13AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN13LogStep,
    step33Shift16M6StepDefectN13AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN13AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN13AlgebraicPart.re =
      (-6645492634926121949124767520410023690703048528462731734047277851048558696533223439863843283792111474497730150952191395372838145263441590835286488387267596400 : Real) /
        (304019273739706093959818547796374927724285693059584246176613429524767851888166225119383440449311183893413320569274215351065272705701209663699215967732749226477 : Real) := by
  norm_num [step33Shift16M6StepDefectN13AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN13AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN13AlgebraicPart.im =
      (2971395763523282534682947734488285647142832033447809603236061124635952443208618030888677010291550456499203381546181783030261036440633146594913113508742520 : Real) /
        (248743042150668622330760630015215849956233748866932565053592805974810060635772366006768269458527332276429080465769812559962495850119171543026631246326794821663 : Real) := by
  norm_num [step33Shift16M6StepDefectN13AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n13_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN13LogReLower <=
        step33Shift16M6StepDefectN13LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN13LogStep.re <=
        step33Shift16M6StepDefectN13LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN13LogImLower <=
        step33Shift16M6StepDefectN13LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN13LogStep.im <=
        step33Shift16M6StepDefectN13LogImUpper) :
    (((-2 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).re <=
        (-1 : Real) / ((10 : Real) ^ 25)) ∧
     ((1 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).im <=
        (2 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).re =
        step33Shift16M6StepDefectN13LogStep.re +
          step33Shift16M6StepDefectN13AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN13_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).im =
        step33Shift16M6StepDefectN13LogStep.im +
          step33Shift16M6StepDefectN13AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN13_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN13AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN13LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN13AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN13LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN13AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN13LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN13AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN13LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n13_component_interval :
    (((-2 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).re <=
        (-1 : Real) / ((10 : Real) ^ 25)) ∧
     ((1 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (13 : Complex))).im <=
        (2 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n13_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN13LogStep_re_bounds.1
    step33Shift16M6StepDefectN13LogStep_re_bounds.2
    step33Shift16M6StepDefectN13LogStep_im_bounds.1
    step33Shift16M6StepDefectN13LogStep_im_bounds.2

def step33Shift16M6StepDefectN14LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (15 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (14 : Complex))

def step33Shift16M6StepDefectN14AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (14 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN14LogReLower : Real :=
  (21391183862966273872862231665 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN14LogReUpper : Real :=
  (21391183862966273872862231666 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN14LogImLower : Real :=
  (-114400081676667663401119226036 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN14LogImUpper : Real :=
  (-114400081676667663401119226035 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN14LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN14LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((3572101 : Real) / (3422501 : Real)) := by
  rw [step33Shift16M6StepDefectN14LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((15 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((14 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((3572101 : Real) / (3422501 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 15,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 14]
  norm_num
  have hNum : (0 : Real) <= 3572101 := by
    norm_num
  have hDen : (0 : Real) <= 3422501 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (3572101 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (3422501 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((3572101 : Real) / (3422501 : Real)) =
        Real.log (3572101 : Real) - Real.log (3422501 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN14LogStep_re_bounds :
    step33Shift16M6StepDefectN14LogReLower <=
        step33Shift16M6StepDefectN14LogStep.re ∧
      step33Shift16M6StepDefectN14LogStep.re <=
        step33Shift16M6StepDefectN14LogReUpper := by
  let a : Real := (149600 : Real) / (3422501 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((3572101 : Real) / (3422501 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN14LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN14LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN14LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN14LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN14LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN14LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN14LogReUpper := by
      norm_num [step33Shift16M6StepDefectN14LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN14LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN14LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN14LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN14LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN14LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (15 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (14 : Complex)) := by
  rw [step33Shift16M6StepDefectN14LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN14LogStep_im_bounds :
    step33Shift16M6StepDefectN14LogImLower <=
        step33Shift16M6StepDefectN14LogStep.im ∧
      step33Shift16M6StepDefectN14LogStep.im <=
        step33Shift16M6StepDefectN14LogImUpper := by
  let x0 : Real := (1 : Real) / (1850 : Real)
  let x1 : Real := (1 : Real) / (1890 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN14LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN14LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((15 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((14 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 15,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 14]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN14LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN14LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN14LogImUpper := by
      norm_num [step33Shift16M6StepDefectN14LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN14_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (14 : Complex)) =
      step33Shift16M6StepDefectN14LogStep +
        step33Shift16M6StepDefectN14AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN14LogStep,
    step33Shift16M6StepDefectN14AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN14AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN14AlgebraicPart.re =
      (-65103634025345966808045117347593960746716284573568415910461198820788768462659025457652473434683500730659027362575105519776282363025082971768243791822541580400 : Real) /
        (3043479708388527331673617128412280419278586237103045649177995963774702969609972387842840794590695663747849216851032154305688835251512732936129259562837410189873 : Real) := by
  norm_num [step33Shift16M6StepDefectN14AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN14AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN14AlgebraicPart.im =
      (1148975279829063090024013153156680955515559514366773062823927170952922411143803987044739121253548659824004819311819095245204367370750309228187116371215620360 : Real) /
        (100434830376821401945229365237605253836193345824400506422873866804565197997129088798813746221492956903679024156084061092087731563299920186892265565573634536265809 : Real) := by
  norm_num [step33Shift16M6StepDefectN14AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n14_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN14LogReLower <=
        step33Shift16M6StepDefectN14LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN14LogStep.re <=
        step33Shift16M6StepDefectN14LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN14LogImLower <=
        step33Shift16M6StepDefectN14LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN14LogStep.im <=
        step33Shift16M6StepDefectN14LogImUpper) :
    (((-2 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).re <=
        (-1 : Real) / ((10 : Real) ^ 25)) ∧
     ((0 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).im <=
        (1 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).re =
        step33Shift16M6StepDefectN14LogStep.re +
          step33Shift16M6StepDefectN14AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN14_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).im =
        step33Shift16M6StepDefectN14LogStep.im +
          step33Shift16M6StepDefectN14AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN14_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN14AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN14LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN14AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN14LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN14AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN14LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN14AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN14LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n14_component_interval :
    (((-2 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).re <=
        (-1 : Real) / ((10 : Real) ^ 25)) ∧
     ((0 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (14 : Complex))).im <=
        (1 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n14_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN14LogStep_re_bounds.1
    step33Shift16M6StepDefectN14LogStep_re_bounds.2
    step33Shift16M6StepDefectN14LogStep_im_bounds.1
    step33Shift16M6StepDefectN14LogStep_im_bounds.2

def step33Shift16M6StepDefectN15LogStep : Complex :=
  Complex.log (step33Shift16DigammaPoint + (16 : Complex)) -
    Complex.log (step33Shift16DigammaPoint + (15 : Complex))

def step33Shift16M6StepDefectN15AlgebraicPart : Complex :=
  let z : Complex := step33Shift16DigammaPoint + (15 : Complex)
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * (z + 1)⁻¹
    - ((1 : Complex) / (12 : Complex)) * ((z + 1) ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * ((z + 1) ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * ((z + 1) ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * ((z + 1) ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * ((z + 1) ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * ((z + 1) ^ 12)⁻¹)) -
  ((0 : Complex)
    - ((1 : Complex) / (2 : Complex)) * z⁻¹
    - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
    + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
    - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
    + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
    - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
    + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹)) -
  z⁻¹

private def step33Shift16M6StepDefectN15LogReLower : Real :=
  (20943168103351257280921501145 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN15LogReUpper : Real :=
  (20943168103351257280921501146 : Real) /
    (1000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN15LogImLower : Real :=
  (-109658110679566882907742515340 : Real) /
    (10000000000000000000000000000000000 : Real)

private def step33Shift16M6StepDefectN15LogImUpper : Real :=
  (-109658110679566882907742515339 : Real) /
    (10000000000000000000000000000000000 : Real)

theorem step33Shift16M6StepDefectN15LogStep_re_eq_half_log_ratio :
    step33Shift16M6StepDefectN15LogStep.re =
      (1 / (2 : Real)) *
        Real.log ((3724901 : Real) / (3572101 : Real)) := by
  rw [step33Shift16M6StepDefectN15LogStep]
  simp [Complex.log_re]
  change
    Real.log ‖step33Shift16DigammaPoint + (((16 : Nat) : Complex))‖ -
        Real.log ‖step33Shift16DigammaPoint + (((15 : Nat) : Complex))‖ =
      (2 : Real)⁻¹ * Real.log ((3724901 : Real) / (3572101 : Real))
  rw [step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 16,
    step33Shift16DigammaPoint_add_nat_norm_eq_sqrt 15]
  norm_num
  have hNum : (0 : Real) <= 3724901 := by
    norm_num
  have hDen : (0 : Real) <= 3572101 := by
    norm_num
  have h40_ne : (40 : Real) ≠ 0 := by
    norm_num
  have hsNum_ne : Real.sqrt (3724901 : Real) ≠ 0 := by
    positivity
  have hsDen_ne : Real.sqrt (3572101 : Real) ≠ 0 := by
    positivity
  rw [Real.log_div hsNum_ne h40_ne,
    Real.log_div hsDen_ne h40_ne]
  rw [Real.log_sqrt hNum, Real.log_sqrt hDen]
  have hratio :
      Real.log ((3724901 : Real) / (3572101 : Real)) =
        Real.log (3724901 : Real) - Real.log (3572101 : Real) := by
    exact Real.log_div (by norm_num) (by norm_num)
  rw [hratio]
  ring

theorem step33Shift16M6StepDefectN15LogStep_re_bounds :
    step33Shift16M6StepDefectN15LogReLower <=
        step33Shift16M6StepDefectN15LogStep.re ∧
      step33Shift16M6StepDefectN15LogStep.re <=
        step33Shift16M6StepDefectN15LogReUpper := by
  let a : Real := (152800 : Real) / (3572101 : Real)
  let S : Real :=
    ∑ i ∈ Finset.range 26, (-a) ^ (i + 1) /
      (((i + 1 : Nat) : Real))
  let E : Real := |(-a)| ^ (26 + 1) / (1 - |(-a)|)
  have ha_abs : |(-a)| < 1 := by
    norm_num [a]
  have hlogBound := Real.abs_log_sub_add_sum_range_le (x := -a) ha_abs 26
  have hlogBound' : |S + Real.log (1 + a)| <= E := by
    simpa [S, E, sub_eq_add_neg] using hlogBound
  have hlog_ge : -S - E <= Real.log (1 + a) := by
    have h := (abs_le.mp hlogBound').1
    linarith
  have hlog_le : Real.log (1 + a) <= -S + E := by
    have h := (abs_le.mp hlogBound').2
    linarith
  have hratio : ((3724901 : Real) / (3572101 : Real)) = 1 + a := by
    norm_num [a]
  have hRe := step33Shift16M6StepDefectN15LogStep_re_eq_half_log_ratio
  rw [hratio] at hRe
  constructor
  · rw [hRe]
    have hApprox :
        2 * step33Shift16M6StepDefectN15LogReLower <= -S - E := by
      norm_num [step33Shift16M6StepDefectN15LogReLower, S, E, a]
    have h2 : 2 * step33Shift16M6StepDefectN15LogReLower <=
        Real.log (1 + a) := hApprox.trans hlog_ge
    calc
      step33Shift16M6StepDefectN15LogReLower =
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN15LogReLower) := by
        ring
      _ <= (1 / (2 : Real)) * Real.log (1 + a) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  · rw [hRe]
    have hApprox : -S + E <=
        2 * step33Shift16M6StepDefectN15LogReUpper := by
      norm_num [step33Shift16M6StepDefectN15LogReUpper, S, E, a]
    have h2 : Real.log (1 + a) <=
        2 * step33Shift16M6StepDefectN15LogReUpper := hlog_le.trans hApprox
    calc
      (1 / (2 : Real)) * Real.log (1 + a) <=
          (1 / (2 : Real)) *
            (2 * step33Shift16M6StepDefectN15LogReUpper) := by
        exact mul_le_mul_of_nonneg_left h2 (by norm_num)
      _ = step33Shift16M6StepDefectN15LogReUpper := by
        ring

theorem step33Shift16M6StepDefectN15LogStep_im_eq_arg_sub :
    step33Shift16M6StepDefectN15LogStep.im =
      Complex.arg (step33Shift16DigammaPoint + (16 : Complex)) -
        Complex.arg (step33Shift16DigammaPoint + (15 : Complex)) := by
  rw [step33Shift16M6StepDefectN15LogStep]
  simp [Complex.log_im]

theorem step33Shift16M6StepDefectN15LogStep_im_bounds :
    step33Shift16M6StepDefectN15LogImLower <=
        step33Shift16M6StepDefectN15LogStep.im ∧
      step33Shift16M6StepDefectN15LogStep.im <=
        step33Shift16M6StepDefectN15LogImUpper := by
  let x0 : Real := (1 : Real) / (1890 : Real)
  let x1 : Real := (1 : Real) / (1930 : Real)
  let S0 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x0 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E0 : Real := x0 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  let S1 : Real :=
    ∑ i ∈ Finset.range 9,
      (-1 : Real) ^ i *
        (x1 ^ (2 * i + 1) / (((2 * i + 1 : Nat) : Real)))
  let E1 : Real := x1 ^ (2 * 9 + 1) / (((2 * 9 + 1 : Nat) : Real))
  have h0 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x0 (by norm_num [x0]) (by norm_num [x0])
    (by norm_num [x0]) (by norm_num [x0])
  have h1 := step33Shift16Arctan_error_bound_of_nonneg_le_one
    x1 (by norm_num [x1]) (by norm_num [x1])
    (by norm_num [x1]) (by norm_num [x1])
  have h0Lower : S0 - E0 <= Real.arctan x0 := by
    have h := (abs_le.mp h0).1
    dsimp [S0, E0] at h ⊢
    linarith
  have h0Upper : Real.arctan x0 <= S0 + E0 := by
    have h := (abs_le.mp h0).2
    dsimp [S0, E0] at h ⊢
    linarith
  have h1Lower : S1 - E1 <= Real.arctan x1 := by
    have h := (abs_le.mp h1).1
    dsimp [S1, E1] at h ⊢
    linarith
  have h1Upper : Real.arctan x1 <= S1 + E1 := by
    have h := (abs_le.mp h1).2
    dsimp [S1, E1] at h ⊢
    linarith
  have hIm :
      step33Shift16M6StepDefectN15LogStep.im =
        Real.arctan x1 - Real.arctan x0 := by
    rw [step33Shift16M6StepDefectN15LogStep_im_eq_arg_sub]
    change
      Complex.arg (step33Shift16DigammaPoint + (((16 : Nat) : Complex))) -
          Complex.arg (step33Shift16DigammaPoint + (((15 : Nat) : Complex))) =
        Real.arctan x1 - Real.arctan x0
    rw [step33Shift16DigammaPoint_add_nat_arg_eq_arctan 16,
      step33Shift16DigammaPoint_add_nat_arg_eq_arctan 15]
    norm_num [x0, x1]
  constructor
  · rw [hIm]
    have hApprox :
        step33Shift16M6StepDefectN15LogImLower <=
          (S1 - E1) - (S0 + E0) := by
      norm_num [step33Shift16M6StepDefectN15LogImLower, S0, E0, S1, E1,
        x0, x1]
    linarith
  · rw [hIm]
    have hApprox :
        (S1 + E1) - (S0 - E0) <=
          step33Shift16M6StepDefectN15LogImUpper := by
      norm_num [step33Shift16M6StepDefectN15LogImUpper, S0, E0, S1, E1,
        x0, x1]
    linarith

theorem step33Shift16M6StepDefectN15_eq_logStep_add_algebraicPart :
    Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (15 : Complex)) =
      step33Shift16M6StepDefectN15LogStep +
        step33Shift16M6StepDefectN15AlgebraicPart := by
  simp [Q3.digammaM6StepDefect, Q3.digammaM6AsymptoticMain,
    step33Shift16M6StepDefectN15LogStep,
    step33Shift16M6StepDefectN15AlgebraicPart]
  ring_nf

theorem step33Shift16M6StepDefectN15AlgebraicPart_re_eq :
    step33Shift16M6StepDefectN15AlgebraicPart.re =
      (-1936686321760212633062418067693912509728397258890059980159127203071070633427636099852515574746488703557601929723731294959818844541823436722584557787241322029200 : Real) /
        (92473417211902645251619338362622249212438909145388573851958990716262593737128886615676552143627954881467191476995435636199790366298071328587594502671229807135003 : Real) := by
  norm_num [step33Shift16M6StepDefectN15AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33Shift16M6StepDefectN15AlgebraicPart_im_eq :
    step33Shift16M6StepDefectN15AlgebraicPart.im =
      (276558005987470512785821972031255732518361012738036757340684458281759540512028381948596791379700543783409612783408880123449594200717046188434596721906068760 : Real) /
        (25220022875973448704987092280715158876119702494196883777806997468071616473762423622457241493716714967672870402816936991690851918081292180523889409819426311036819 : Real) := by
  norm_num [step33Shift16M6StepDefectN15AlgebraicPart,
    step33Shift16DigammaPoint, Complex.inv_re, Complex.inv_im,
    Complex.normSq_apply, Complex.I_sq, Complex.I_pow_three,
    Complex.I_pow_four, step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]
  ring_nf
  norm_num [Complex.I_sq, Complex.I_pow_three, Complex.I_pow_four,
    step33ComplexIPowFive, step33ComplexIPowSix,
    step33ComplexIPowSeven, step33ComplexIPowEight,
    step33ComplexIPowNine, step33ComplexIPowTen,
    step33ComplexIPowEleven, step33ComplexIPowTwelve]

theorem step33_shift16_m6_step_defect_n15_component_interval_of_log_step_bounds
    (hLogReLower :
      step33Shift16M6StepDefectN15LogReLower <=
        step33Shift16M6StepDefectN15LogStep.re)
    (hLogReUpper :
      step33Shift16M6StepDefectN15LogStep.re <=
        step33Shift16M6StepDefectN15LogReUpper)
    (hLogImLower :
      step33Shift16M6StepDefectN15LogImLower <=
        step33Shift16M6StepDefectN15LogStep.im)
    (hLogImUpper :
      step33Shift16M6StepDefectN15LogStep.im <=
        step33Shift16M6StepDefectN15LogImUpper) :
    (((-1 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).re <=
        (0 : Real) / ((10 : Real) ^ 25)) ∧
     ((0 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).im <=
        (1 : Real) / ((10 : Real) ^ 27))) := by
  have hReEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).re =
        step33Shift16M6StepDefectN15LogStep.re +
          step33Shift16M6StepDefectN15AlgebraicPart.re := by
    simpa using congrArg Complex.re
      step33Shift16M6StepDefectN15_eq_logStep_add_algebraicPart
  have hImEq :
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).im =
        step33Shift16M6StepDefectN15LogStep.im +
          step33Shift16M6StepDefectN15AlgebraicPart.im := by
    simpa using congrArg Complex.im
      step33Shift16M6StepDefectN15_eq_logStep_add_algebraicPart
  constructor
  · constructor
    · rw [hReEq, step33Shift16M6StepDefectN15AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN15LogReLower] at hLogReLower ⊢
      linarith [hLogReLower]
    · rw [hReEq, step33Shift16M6StepDefectN15AlgebraicPart_re_eq]
      norm_num [step33Shift16M6StepDefectN15LogReUpper] at hLogReUpper ⊢
      linarith [hLogReUpper]
  · constructor
    · rw [hImEq, step33Shift16M6StepDefectN15AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN15LogImLower] at hLogImLower ⊢
      linarith [hLogImLower]
    · rw [hImEq, step33Shift16M6StepDefectN15AlgebraicPart_im_eq]
      norm_num [step33Shift16M6StepDefectN15LogImUpper] at hLogImUpper ⊢
      linarith [hLogImUpper]

theorem step33_shift16_m6_step_defect_n15_component_interval :
    (((-1 : Real) / ((10 : Real) ^ 25) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).re ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).re <=
        (0 : Real) / ((10 : Real) ^ 25)) ∧
     ((0 : Real) / ((10 : Real) ^ 27) <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).im ∧
      (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (15 : Complex))).im <=
        (1 : Real) / ((10 : Real) ^ 27))) := by
  exact step33_shift16_m6_step_defect_n15_component_interval_of_log_step_bounds
    step33Shift16M6StepDefectN15LogStep_re_bounds.1
    step33Shift16M6StepDefectN15LogStep_re_bounds.2
    step33Shift16M6StepDefectN15LogStep_im_bounds.1
    step33Shift16M6StepDefectN15LogStep_im_bounds.2

theorem step33_shift16_digamma_m6_main_norm_of_log_add_algebraicPart_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (Complex.log step33Shift16DigammaPoint +
            step33Shift16DigammaM6AlgebraicPart)‖ <=
        step33Shift16DigammaM6MainComponentRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius := by
  simpa [step33Shift16DigammaM6Main_eq_log_add_algebraicPart] using h

theorem step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        step33Shift16DigammaM6MainComponentRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
        step33Shift16DigammaM6MainComponentRadius := by
  simpa [step33Shift16DigammaM6Main] using h

theorem step33Shift16DigammaM6FirstOmittedTermBound_le_componentRadius :
    ((1 : Real) / (12 : Real)) *
        (‖step33Shift16DigammaPoint‖⁻¹) ^ 14 <=
      step33Shift16DigammaM6MainComponentRadius := by
  have hinv :
      ‖step33Shift16DigammaPoint‖⁻¹ <= ((32 : Real)⁻¹) := by
    have h := one_div_le_one_div_of_le
      (by norm_num : (0 : Real) < 32)
      step33Shift16DigammaPoint_norm_ge_32
    simpa [one_div] using h
  have hpow :
      (‖step33Shift16DigammaPoint‖⁻¹) ^ 14 <=
        ((32 : Real)⁻¹) ^ 14 := by
    exact pow_le_pow_left₀
      (inv_nonneg.mpr (norm_nonneg _)) hinv 14
  have hscale :
      ((1 : Real) / (12 : Real)) *
          (‖step33Shift16DigammaPoint‖⁻¹) ^ 14 <=
        ((1 : Real) / (12 : Real)) * ((32 : Real)⁻¹) ^ 14 := by
    exact mul_le_mul_of_nonneg_left hpow (by norm_num)
  have harith :
      ((1 : Real) / (12 : Real)) * ((32 : Real)⁻¹) ^ 14 <=
        step33Shift16DigammaM6MainComponentRadius := by
    norm_num [step33Shift16DigammaM6MainComponentRadius]
  exact hscale.trans harith

theorem step33Shift16DigammaM6ReFirstOmittedTermBound_le_componentRadius :
    ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 <=
      step33Shift16DigammaM6MainComponentRadius := by
  rw [step33Shift16DigammaPoint_re_eq]
  norm_num [step33Shift16DigammaM6MainComponentRadius]

theorem step33_shift16_digamma_m6_re_first_omitted_term_bound_of_integral_remainder
    (hIntegral :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 := by
  have hz : 0 < step33Shift16DigammaPoint.re :=
    step33Shift16DigammaPoint_re_pos
  have hIntegralBound :
      ∫ x in Set.Ioi (0 : Real),
          1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 <=
        1 / (14 * step33Shift16DigammaPoint.re ^ 14) :=
    Q3.integral_kernel_norm_pow15_le_re step33Shift16DigammaPoint hz
  have hScaled :
      ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15 <=
        ((7 : Real) / (6 : Real)) *
          (1 / (14 * step33Shift16DigammaPoint.re ^ 14)) := by
    exact mul_le_mul_of_nonneg_left hIntegralBound (by norm_num)
  have hScalar :
      ((7 : Real) / (6 : Real)) *
          (1 / (14 * step33Shift16DigammaPoint.re ^ 14)) =
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14 := by
    rw [inv_pow]
    field_simp [show (6 : Real) ≠ 0 by norm_num,
      show (7 : Real) ≠ 0 by norm_num,
      show (12 : Real) ≠ 0 by norm_num,
      show (14 : Real) ≠ 0 by norm_num,
      pow_ne_zero 14 (ne_of_gt hz)]
    ring
  exact hIntegral.trans (hScaled.trans_eq hScalar)

theorem step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
    (hIntegral : Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 := by
  simpa [Q3.digammaM6IntegralRemainderBound, Q3.digammaM6AsymptoticMain]
    using
      Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
        step33Shift16DigammaPoint step33Shift16DigammaPoint_re_pos hIntegral

theorem step33_shift16_digamma_m6_remainder_finite_telescope (N : Nat) :
    Q3.digamma step33Shift16DigammaPoint -
        Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint =
      Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
        Q3.digammaM6AsymptoticMain (step33Shift16DigammaPoint + (N : Complex)) +
        (Finset.range N).sum
          (fun n : Nat =>
            Q3.digammaM6StepDefect (step33Shift16DigammaPoint + (n : Complex))) :=
  Q3.digamma_m6_remainder_finite_telescope
    step33Shift16DigammaPoint N step33Shift16DigammaPoint_re_pos

theorem step33_digammaM6IntegralRemainderBound_of_finite_telescope
    (N : Nat) (shiftRad defectRad : Real)
    (hShift :
      ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15) :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint :=
  Q3.digammaM6IntegralRemainderBound_of_finite_telescope
    step33Shift16DigammaPoint N step33Shift16DigammaPoint_re_pos
    shiftRad defectRad hShift hDefects hTotal

theorem step33_shift16_digamma_m6_integral_remainder_bound_of_shifted_integral_remainder
    (N : Nat) (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (N : Complex)))
    (hShiftRad :
      ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) +
              (step33Shift16DigammaPoint + (N : Complex))‖ ^ 15 <=
        shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15) :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint := by
  have hShiftSource :
      ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (N : Complex))‖ <=
        ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) +
              (step33Shift16DigammaPoint + (N : Complex))‖ ^ 15 := by
    simpa [Q3.digammaM6IntegralRemainderBound] using hShiftIntegral
  exact
    step33_digammaM6IntegralRemainderBound_of_finite_telescope
      N shiftRad defectRad (hShiftSource.trans hShiftRad) hDefects hTotal

theorem step33_shift16_digamma_m6_integral_remainder_bound_N16_of_shifted_integral_remainder
    (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) +
              (step33Shift16DigammaPoint + (16 : Complex))‖ ^ 15 <=
        shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((7 : Real) / (6 : Real)) *
          ∫ x in Set.Ioi (0 : Real),
            1 / ‖(x : Complex) + step33Shift16DigammaPoint‖ ^ 15) :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint :=
  step33_shift16_digamma_m6_integral_remainder_bound_of_shifted_integral_remainder
    16 shiftRad defectRad hShiftIntegral hShiftRad hDefects hTotal

theorem step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
    (N : Nat) (shiftRad defectRad : Real)
    (hShift :
      ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 := by
  simpa [Q3.digammaM6AsymptoticMain]
    using
      (Q3.digamma_m6_remainder_norm_le_of_finite_telescope
        step33Shift16DigammaPoint N step33Shift16DigammaPoint_re_pos
        shiftRad defectRad hShift hDefects).trans hTotal

theorem step33Shift16DigammaPoint_add_nat_re_pos (N : Nat) :
    0 < (step33Shift16DigammaPoint + (N : Complex)).re := by
  have hz : 0 < step33Shift16DigammaPoint.re :=
    step33Shift16DigammaPoint_re_pos
  have hN : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
  have hsum : 0 < step33Shift16DigammaPoint.re + (N : Real) := by
    linarith
  simpa using hsum

theorem step33_shift16_digamma_m6_integral_remainder_bound_of_re_pos_source
    (hSource : ∀ z : Complex, 0 < z.re -> Q3.digammaM6IntegralRemainderBound z) :
    Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint := by
  exact hSource step33Shift16DigammaPoint step33Shift16DigammaPoint_re_pos

theorem step33_shift16_m6_shift48_integral_remainder_bound_of_re_pos_source
    (hSource : ∀ z : Complex, 0 < z.re -> Q3.digammaM6IntegralRemainderBound z) :
    Q3.digammaM6IntegralRemainderBound
      (step33Shift16DigammaPoint + (16 : Complex)) := by
  exact hSource
    (step33Shift16DigammaPoint + (16 : Complex))
    (step33Shift16DigammaPoint_add_nat_re_pos 16)

theorem step33Shift16DigammaPoint_add_nat_add_nat_ne_zero (N n : Nat) :
    step33Shift16DigammaPoint + (N : Complex) + (n : Complex) ≠ 0 := by
  intro hzero
  have hN : (0 : Real) <= (N : Real) := Nat.cast_nonneg N
  have hn : (0 : Real) <= (n : Real) := Nat.cast_nonneg n
  have hpos :
      0 < step33Shift16DigammaPoint.re + (N : Real) + (n : Real) := by
    linarith [step33Shift16DigammaPoint_re_pos]
  have hzeroRe :
      step33Shift16DigammaPoint.re + (N : Real) + (n : Real) = 0 := by
    simpa [Complex.add_re, add_assoc] using congrArg Complex.re hzero
  linarith

structure Step33Shift16M6FiniteTelescopeScalarPayload where
  N : Nat
  shiftRad : Real
  defectRad : Real
  hShift :
    ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad
  hDefects :
    (Finset.range N).sum
        (fun n : Nat =>
          ‖Q3.digammaM6StepDefect
            (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad
  hTotal :
    shiftRad + defectRad <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14

theorem step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_scalar_payload
    (payload : Step33Shift16M6FiniteTelescopeScalarPayload) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 :=
  step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope
    payload.N payload.shiftRad payload.defectRad
    payload.hShift payload.hDefects payload.hTotal

def step33_shift16_m6_finite_telescope_scalar_payload_of_shifted_integral_remainder
    (N : Nat) (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (N : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (N : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefects :
      (Finset.range N).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeScalarPayload := by
  refine
    { N := N
      shiftRad := shiftRad
      defectRad := defectRad
      hShift := ?_
      hDefects := hDefects
      hTotal := hTotal }
  exact
    (Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
      (step33Shift16DigammaPoint + (N : Complex))
      (step33Shift16DigammaPoint_add_nat_re_pos N)
      hShiftIntegral).trans hShiftRad

def step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shifted_integral_remainder_and_defect_sum
    (shiftRad defectRad : Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeScalarPayload :=
  step33_shift16_m6_finite_telescope_scalar_payload_of_shifted_integral_remainder
    16 shiftRad defectRad hShiftIntegral hShiftRad hDefects hTotal

structure Step33Shift16M6FiniteTelescopeTermPayload where
  N : Nat
  shiftRad : Real
  defectRad : Real
  termRad : Nat -> Real
  hShift :
    ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad
  hDefectTerm : ∀ n : Nat, n < N ->
    ‖Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))‖ <= termRad n
  hDefectSum :
    (Finset.range N).sum termRad <= defectRad
  hTotal :
    shiftRad + defectRad <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14

def Step33Shift16M6FiniteTelescopeTermPayload.toScalarPayload
    (payload : Step33Shift16M6FiniteTelescopeTermPayload) :
    Step33Shift16M6FiniteTelescopeScalarPayload where
  N := payload.N
  shiftRad := payload.shiftRad
  defectRad := payload.defectRad
  hShift := payload.hShift
  hDefects := by
    exact
      (Finset.sum_le_sum
        (fun n hn => payload.hDefectTerm n (Finset.mem_range.mp hn))).trans
        payload.hDefectSum
  hTotal := payload.hTotal

theorem step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_term_payload
    (payload : Step33Shift16M6FiniteTelescopeTermPayload) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      ((1 : Real) / (12 : Real)) *
        (step33Shift16DigammaPoint.re⁻¹) ^ 14 :=
  step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_scalar_payload
    payload.toScalarPayload

theorem complex_norm_sub_le_of_component_rectangles
    {x y : Complex}
    (xReLower xReUpper xImLower xImUpper
      yReLower yReUpper yImLower yImUpper
      reRad imRad normRad : Real)
    (hxReLower : xReLower <= x.re)
    (hxReUpper : x.re <= xReUpper)
    (hxImLower : xImLower <= x.im)
    (hxImUpper : x.im <= xImUpper)
    (hyReLower : yReLower <= y.re)
    (hyReUpper : y.re <= yReUpper)
    (hyImLower : yImLower <= y.im)
    (hyImUpper : y.im <= yImUpper)
    (hReLower : -reRad <= xReLower - yReUpper)
    (hReUpper : xReUpper - yReLower <= reRad)
    (hImLower : -imRad <= xImLower - yImUpper)
    (hImUpper : xImUpper - yImLower <= imRad)
    (hNorm : reRad + imRad <= normRad) :
    ‖x - y‖ <= normRad := by
  have hreAbs : |(x - y).re| <= reRad := by
    have hLower : -reRad <= (x - y).re := by
      have hxy : xReLower - yReUpper <= x.re - y.re := by
        linarith
      simpa using hReLower.trans hxy
    have hUpper : (x - y).re <= reRad := by
      have hxy : x.re - y.re <= xReUpper - yReLower := by
        linarith
      exact hxy.trans hReUpper
    exact abs_le.mpr ⟨hLower, hUpper⟩
  have himAbs : |(x - y).im| <= imRad := by
    have hLower : -imRad <= (x - y).im := by
      have hxy : xImLower - yImUpper <= x.im - y.im := by
        linarith
      simpa using hImLower.trans hxy
    have hUpper : (x - y).im <= imRad := by
      have hxy : x.im - y.im <= xImUpper - yImLower := by
        linarith
      exact hxy.trans hImUpper
    exact abs_le.mpr ⟨hLower, hUpper⟩
  have hnorm :
      ‖x - y‖ <= |(x - y).re| + |(x - y).im| :=
    CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im
      (x - y)
  exact hnorm.trans ((add_le_add hreAbs himAbs).trans hNorm)

theorem step33_shift16_m6_shifted_remainder_bound_of_component_rectangles
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      reRad imRad shiftRad : Real)
    (hDigammaReLower :
      digammaReLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hDigammaReUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re <=
      digammaReUpper)
    (hDigammaImLower :
      digammaImLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hDigammaImUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im <=
      digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hReLower : -reRad <= digammaReLower - mainReUpper)
    (hReUpper : digammaReUpper - mainReLower <= reRad)
    (hImLower : -imRad <= digammaImLower - mainImUpper)
    (hImUpper : digammaImUpper - mainImLower <= imRad)
    (hShiftRad : reRad + imRad <= shiftRad) :
    ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad :=
  complex_norm_sub_le_of_component_rectangles
    digammaReLower digammaReUpper digammaImLower digammaImUpper
    mainReLower mainReUpper mainImLower mainImUpper
    reRad imRad shiftRad
    hDigammaReLower hDigammaReUpper hDigammaImLower hDigammaImUpper
    hMainReLower hMainReUpper hMainImLower hMainImUpper
    hReLower hReUpper hImLower hImUpper hShiftRad

theorem step33_shift16_m6_shifted_remainder_bound_of_digamma_series_prefix_tail_abs_and_main_rectangles
    (seriesN : Nat)
    (shiftRad shiftReRad shiftImRad : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).re))
    (hRePrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).re) <=
      rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              ((n + seriesN : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLower :
      digammaReLower <= -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpper :
      -gammaLower + rePrefixUpper + reTailRadius <= digammaReUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).im))
    (hImPrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).im) <=
      imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              ((n + seriesN : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLower :
      digammaImLower <= imPrefixLower - imTailRadius)
    (hImUpper :
      imPrefixUpper + imTailRadius <= digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad) :
    ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad := by
  have hzpos : 0 < (step33Shift16DigammaPoint + (16 : Complex)).re :=
    step33Shift16DigammaPoint_add_nat_re_pos 16
  have hzNoPole :
      ∀ n : Nat, step33Shift16DigammaPoint + (16 : Complex) + n ≠ 0 := by
    intro n
    simpa using step33Shift16DigammaPoint_add_nat_add_nat_ne_zero 16 n
  have hRe :
      digammaReLower <=
          (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re ∧
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re <=
          digammaReUpper :=
    Q3.re_digamma_interval_of_series_prefix_tail_abs
      (step33Shift16DigammaPoint + (16 : Complex)) seriesN
      digammaReLower digammaReUpper gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      hzpos hzNoPole hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLower hReUpper
  have hIm :
      digammaImLower <=
          (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im ∧
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im <=
          digammaImUpper :=
    Q3.im_digamma_interval_of_series_prefix_tail_abs
      (step33Shift16DigammaPoint + (16 : Complex)) seriesN
      digammaImLower digammaImUpper imPrefixLower imPrefixUpper imTailRadius
      hzpos hzNoPole hImPrefixLower hImPrefixUpper hImTail hImLower hImUpper
  exact
    step33_shift16_m6_shifted_remainder_bound_of_component_rectangles
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      shiftReRad shiftImRad shiftRad
      hRe.1 hRe.2 hIm.1 hIm.2
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad

theorem step33_shift16_m6_shifted_remainder_bound_of_shift48_digamma_series_prefix_tail_abs_and_main_rectangles
    (seriesN : Nat)
    (shiftRad shiftReRad shiftImRad : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re))
    (hRePrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re) <=
      rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLower :
      digammaReLower <= -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpper :
      -gammaLower + rePrefixUpper + reTailRadius <= digammaReUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im))
    (hImPrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im) <=
      imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLower :
      digammaImLower <= imPrefixLower - imTailRadius)
    (hImUpper :
      imPrefixUpper + imTailRadius <= digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad) :
    ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad :=
  step33_shift16_m6_shifted_remainder_bound_of_digamma_series_prefix_tail_abs_and_main_rectangles
    seriesN shiftRad shiftReRad shiftImRad
    digammaReLower digammaReUpper digammaImLower digammaImUpper
    mainReLower mainReUpper mainImLower mainImUpper
    gammaLower gammaUpper
    rePrefixLower rePrefixUpper reTailRadius
    imPrefixLower imPrefixUpper imTailRadius
    hGammaLower hGammaUpper
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hRePrefixLower)
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hRePrefixUpper)
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hReTail)
    hReLower hReUpper
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hImPrefixLower)
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hImPrefixUpper)
    (by
      simpa [step33Shift16DigammaPoint_add_16_eq_generated_shift48,
        add_assoc] using hImTail)
    hImLower hImUpper
    hMainReLower hMainReUpper hMainImLower hMainImUpper
    hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad

def step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder
    (N : Nat) (shiftRad defectRad : Real) (termRad : Nat -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (N : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (N : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectTerm : ∀ n : Nat, n < N ->
      ‖Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (n : Complex))‖ <= termRad n)
    (hDefectSum :
      (Finset.range N).sum termRad <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  refine
    { N := N
      shiftRad := shiftRad
      defectRad := defectRad
      termRad := termRad
      hShift := ?_
      hDefectTerm := hDefectTerm
      hDefectSum := hDefectSum
      hTotal := hTotal }
  exact
    (Q3.digamma_m6_re_first_omitted_bound_of_integral_remainder
      (step33Shift16DigammaPoint + (N : Complex))
      (step33Shift16DigammaPoint_add_nat_re_pos N)
      hShiftIntegral).trans hShiftRad

def step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_defects
    (N : Nat) (shiftRad defectRad : Real)
    (termReRad termImRad termRad : Nat -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (N : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (N : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectRe : ∀ n : Nat, n < N ->
      |(Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (n : Complex))).re| <= termReRad n)
    (hDefectIm : ∀ n : Nat, n < N ->
      |(Q3.digammaM6StepDefect
        (step33Shift16DigammaPoint + (n : Complex))).im| <= termImRad n)
    (hTermRad : ∀ n : Nat, n < N ->
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.range N).sum termRad <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  refine
    step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder
      N shiftRad defectRad termRad
      hShiftIntegral hShiftRad ?_ hDefectSum hTotal
  intro n hn
  let defect : Complex :=
    Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))
  have hnorm :
      ‖defect‖ <= |defect.re| + |defect.im| :=
    CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im defect
  have hcomponents :
      |defect.re| + |defect.im| <= termReRad n + termImRad n := by
    exact add_le_add (hDefectRe n hn) (hDefectIm n hn)
  exact hnorm.trans (hcomponents.trans (hTermRad n hn))

def step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_interval_defects
    (N : Nat) (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Nat -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (N : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (N : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectReLower : ∀ n : Nat, n < N ->
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).re)
    (hDefectReUpper : ∀ n : Nat, n < N ->
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Nat, n < N ->
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).im)
    (hDefectImUpper : ∀ n : Nat, n < N ->
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Nat, n < N -> -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Nat, n < N -> termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Nat, n < N -> -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Nat, n < N -> termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Nat, n < N ->
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.range N).sum termRad <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  refine
    step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_defects
      N shiftRad defectRad termReRad termImRad termRad
      hShiftIntegral hShiftRad ?_ ?_ hTermRad hDefectSum hTotal
  · intro n hn
    exact abs_le.mpr
      ⟨(hReLowerContain n hn).trans (hDefectReLower n hn),
        (hDefectReUpper n hn).trans (hReUpperContain n hn)⟩
  · intro n hn
    exact abs_le.mpr
      ⟨(hImLowerContain n hn).trans (hDefectImLower n hn),
        (hDefectImUpper n hn).trans (hImUpperContain n hn)⟩

def step33_shift16_m6_finite_telescope_term_payload_of_shifted_remainder_bound_component_interval_defects
    (N : Nat) (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Nat -> Real)
    (hShift :
      ‖Q3.digamma (step33Shift16DigammaPoint + (N : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (N : Complex))‖ <= shiftRad)
    (hDefectReLower : ∀ n : Nat, n < N ->
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).re)
    (hDefectReUpper : ∀ n : Nat, n < N ->
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Nat, n < N ->
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).im)
    (hDefectImUpper : ∀ n : Nat, n < N ->
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + (n : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Nat, n < N -> -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Nat, n < N -> termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Nat, n < N -> -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Nat, n < N -> termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Nat, n < N ->
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.range N).sum termRad <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  refine
    { N := N
      shiftRad := shiftRad
      defectRad := defectRad
      termRad := termRad
      hShift := hShift
      hDefectTerm := ?_
      hDefectSum := hDefectSum
      hTotal := hTotal }
  intro n hn
  let defect : Complex :=
    Q3.digammaM6StepDefect
      (step33Shift16DigammaPoint + (n : Complex))
  have hreLower : termReLower n <= defect.re := by
    simpa [defect] using hDefectReLower n hn
  have hreUpper : defect.re <= termReUpper n := by
    simpa [defect] using hDefectReUpper n hn
  have himLower : termImLower n <= defect.im := by
    simpa [defect] using hDefectImLower n hn
  have himUpper : defect.im <= termImUpper n := by
    simpa [defect] using hDefectImUpper n hn
  have hreAbs : |defect.re| <= termReRad n := by
    exact abs_le.mpr
      ⟨(hReLowerContain n hn).trans hreLower,
        hreUpper.trans (hReUpperContain n hn)⟩
  have himAbs : |defect.im| <= termImRad n := by
    exact abs_le.mpr
      ⟨(hImLowerContain n hn).trans himLower,
        himUpper.trans (hImUpperContain n hn)⟩
  have hnorm :
      ‖defect‖ <= |defect.re| + |defect.im| :=
    CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im defect
  exact hnorm.trans ((add_le_add hreAbs himAbs).trans (hTermRad n hn))

private def step33Shift16Fin16PayloadNat (f : Fin 16 -> Real) : Nat -> Real :=
  fun n => if h : n < 16 then f ⟨n, h⟩ else 0

private theorem step33Shift16_sum_range_fin16PayloadNat (f : Fin 16 -> Real) :
    (Finset.range 16).sum (step33Shift16Fin16PayloadNat f) =
      Finset.univ.sum f := by
  have hfin :
      (∑ k : Fin 16, step33Shift16Fin16PayloadNat f (k : Nat)) =
        (Finset.range 16).sum (step33Shift16Fin16PayloadNat f) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (f := step33Shift16Fin16PayloadNat f) (n := 16))
  have hfinL :
      (∑ k : Fin 16, step33Shift16Fin16PayloadNat f (k : Nat)) =
        Finset.univ.sum f := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    simp [step33Shift16Fin16PayloadNat]
  exact hfin.symm.trans hfinL

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_integral_remainder_component_interval_defects
    (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hShiftIntegral :
      Q3.digammaM6IntegralRemainderBound
        (step33Shift16DigammaPoint + (16 : Complex)))
    (hShiftRad :
      ((1 : Real) / (12 : Real)) *
          (((step33Shift16DigammaPoint + (16 : Complex)).re)⁻¹) ^ 14 <=
        shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  let termReLowerNat : Nat -> Real := step33Shift16Fin16PayloadNat termReLower
  let termReUpperNat : Nat -> Real := step33Shift16Fin16PayloadNat termReUpper
  let termImLowerNat : Nat -> Real := step33Shift16Fin16PayloadNat termImLower
  let termImUpperNat : Nat -> Real := step33Shift16Fin16PayloadNat termImUpper
  let termReRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termReRad
  let termImRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termImRad
  let termRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termRad
  refine
    step33_shift16_m6_finite_telescope_term_payload_of_shifted_integral_remainder_component_interval_defects
      16 shiftRad defectRad
      termReLowerNat termReUpperNat termImLowerNat termImUpperNat
      termReRadNat termImRadNat termRadNat
      hShiftIntegral hShiftRad ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hTotal
  · intro n hn
    simpa [termReLowerNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectReLower ⟨n, hn⟩
  · intro n hn
    simpa [termReUpperNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectReUpper ⟨n, hn⟩
  · intro n hn
    simpa [termImLowerNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectImLower ⟨n, hn⟩
  · intro n hn
    simpa [termImUpperNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectImUpper ⟨n, hn⟩
  · intro n hn
    simpa [termReLowerNat, termReRadNat, step33Shift16Fin16PayloadNat, hn] using
      hReLowerContain ⟨n, hn⟩
  · intro n hn
    simpa [termReUpperNat, termReRadNat, step33Shift16Fin16PayloadNat, hn] using
      hReUpperContain ⟨n, hn⟩
  · intro n hn
    simpa [termImLowerNat, termImRadNat, step33Shift16Fin16PayloadNat, hn] using
      hImLowerContain ⟨n, hn⟩
  · intro n hn
    simpa [termImUpperNat, termImRadNat, step33Shift16Fin16PayloadNat, hn] using
      hImUpperContain ⟨n, hn⟩
  · intro n hn
    simpa [termReRadNat, termImRadNat, termRadNat,
      step33Shift16Fin16PayloadNat, hn] using hTermRad ⟨n, hn⟩
  · have hsum :
        (Finset.range 16).sum termRadNat =
          Finset.univ.sum (fun n : Fin 16 => termRad n) := by
      simpa [termRadNat] using
        step33Shift16_sum_range_fin16PayloadNat termRad
    exact hsum.trans_le hDefectSum

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    (shiftRad defectRad : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hShift :
      ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  let termReLowerNat : Nat -> Real := step33Shift16Fin16PayloadNat termReLower
  let termReUpperNat : Nat -> Real := step33Shift16Fin16PayloadNat termReUpper
  let termImLowerNat : Nat -> Real := step33Shift16Fin16PayloadNat termImLower
  let termImUpperNat : Nat -> Real := step33Shift16Fin16PayloadNat termImUpper
  let termReRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termReRad
  let termImRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termImRad
  let termRadNat : Nat -> Real := step33Shift16Fin16PayloadNat termRad
  refine
    step33_shift16_m6_finite_telescope_term_payload_of_shifted_remainder_bound_component_interval_defects
      16 shiftRad defectRad
      termReLowerNat termReUpperNat termImLowerNat termImUpperNat
      termReRadNat termImRadNat termRadNat
      hShift ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hTotal
  · intro n hn
    simpa [termReLowerNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectReLower ⟨n, hn⟩
  · intro n hn
    simpa [termReUpperNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectReUpper ⟨n, hn⟩
  · intro n hn
    simpa [termImLowerNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectImLower ⟨n, hn⟩
  · intro n hn
    simpa [termImUpperNat, step33Shift16Fin16PayloadNat, hn] using
      hDefectImUpper ⟨n, hn⟩
  · intro n hn
    simpa [termReLowerNat, termReRadNat, step33Shift16Fin16PayloadNat, hn] using
      hReLowerContain ⟨n, hn⟩
  · intro n hn
    simpa [termReUpperNat, termReRadNat, step33Shift16Fin16PayloadNat, hn] using
      hReUpperContain ⟨n, hn⟩
  · intro n hn
    simpa [termImLowerNat, termImRadNat, step33Shift16Fin16PayloadNat, hn] using
      hImLowerContain ⟨n, hn⟩
  · intro n hn
    simpa [termImUpperNat, termImRadNat, step33Shift16Fin16PayloadNat, hn] using
      hImUpperContain ⟨n, hn⟩
  · intro n hn
    simpa [termReRadNat, termImRadNat, termRadNat,
      step33Shift16Fin16PayloadNat, hn] using hTermRad ⟨n, hn⟩
  · have hsum :
        (Finset.range 16).sum termRadNat =
          Finset.univ.sum (fun n : Fin 16 => termRad n) := by
      simpa [termRadNat] using
        step33Shift16_sum_range_fin16PayloadNat termRad
    exact hsum.trans_le hDefectSum

private def step33Shift16M6Fin16TermReLower (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (-219 : Real) / ((10 : Real) ^ 25)
  | 1 => (-140 : Real) / ((10 : Real) ^ 25)
  | 2 => (-90 : Real) / ((10 : Real) ^ 25)
  | 3 => (-59 : Real) / ((10 : Real) ^ 25)
  | 4 => (-39 : Real) / ((10 : Real) ^ 25)
  | 5 => (-26 : Real) / ((10 : Real) ^ 25)
  | 6 => (-18 : Real) / ((10 : Real) ^ 25)
  | 7 => (-12 : Real) / ((10 : Real) ^ 25)
  | 8 => (-9 : Real) / ((10 : Real) ^ 25)
  | 9 => (-6 : Real) / ((10 : Real) ^ 25)
  | 10 => (-5 : Real) / ((10 : Real) ^ 25)
  | 11 => (-3 : Real) / ((10 : Real) ^ 25)
  | 12 => (-3 : Real) / ((10 : Real) ^ 25)
  | 13 => (-2 : Real) / ((10 : Real) ^ 25)
  | 14 => (-2 : Real) / ((10 : Real) ^ 25)
  | 15 => (-1 : Real) / ((10 : Real) ^ 25)
  | _ => 0

private def step33Shift16M6Fin16TermReUpper (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (-218 : Real) / ((10 : Real) ^ 25)
  | 1 => (-139 : Real) / ((10 : Real) ^ 25)
  | 2 => (-89 : Real) / ((10 : Real) ^ 25)
  | 3 => (-58 : Real) / ((10 : Real) ^ 25)
  | 4 => (-38 : Real) / ((10 : Real) ^ 25)
  | 5 => (-25 : Real) / ((10 : Real) ^ 25)
  | 6 => (-17 : Real) / ((10 : Real) ^ 25)
  | 7 => (-11 : Real) / ((10 : Real) ^ 25)
  | 8 => (-8 : Real) / ((10 : Real) ^ 25)
  | 9 => (-5 : Real) / ((10 : Real) ^ 25)
  | 10 => (-4 : Real) / ((10 : Real) ^ 25)
  | 11 => (-2 : Real) / ((10 : Real) ^ 25)
  | 12 => (-2 : Real) / ((10 : Real) ^ 25)
  | 13 => (-1 : Real) / ((10 : Real) ^ 25)
  | 14 => (-1 : Real) / ((10 : Real) ^ 25)
  | 15 => (0 : Real) / ((10 : Real) ^ 25)
  | _ => 0

private def step33Shift16M6Fin16TermImLower (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (250 : Real) / ((10 : Real) ^ 27)
  | 1 => (154 : Real) / ((10 : Real) ^ 27)
  | 2 => (97 : Real) / ((10 : Real) ^ 27)
  | 3 => (61 : Real) / ((10 : Real) ^ 27)
  | 4 => (39 : Real) / ((10 : Real) ^ 27)
  | 5 => (25 : Real) / ((10 : Real) ^ 27)
  | 6 => (16 : Real) / ((10 : Real) ^ 27)
  | 7 => (11 : Real) / ((10 : Real) ^ 27)
  | 8 => (7 : Real) / ((10 : Real) ^ 27)
  | 9 => (5 : Real) / ((10 : Real) ^ 27)
  | 10 => (3 : Real) / ((10 : Real) ^ 27)
  | 11 => (2 : Real) / ((10 : Real) ^ 27)
  | 12 => (1 : Real) / ((10 : Real) ^ 27)
  | 13 => (1 : Real) / ((10 : Real) ^ 27)
  | 14 => (0 : Real) / ((10 : Real) ^ 27)
  | 15 => (0 : Real) / ((10 : Real) ^ 27)
  | _ => 0

private def step33Shift16M6Fin16TermImUpper (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (251 : Real) / ((10 : Real) ^ 27)
  | 1 => (155 : Real) / ((10 : Real) ^ 27)
  | 2 => (98 : Real) / ((10 : Real) ^ 27)
  | 3 => (62 : Real) / ((10 : Real) ^ 27)
  | 4 => (40 : Real) / ((10 : Real) ^ 27)
  | 5 => (26 : Real) / ((10 : Real) ^ 27)
  | 6 => (17 : Real) / ((10 : Real) ^ 27)
  | 7 => (12 : Real) / ((10 : Real) ^ 27)
  | 8 => (8 : Real) / ((10 : Real) ^ 27)
  | 9 => (6 : Real) / ((10 : Real) ^ 27)
  | 10 => (4 : Real) / ((10 : Real) ^ 27)
  | 11 => (3 : Real) / ((10 : Real) ^ 27)
  | 12 => (2 : Real) / ((10 : Real) ^ 27)
  | 13 => (2 : Real) / ((10 : Real) ^ 27)
  | 14 => (1 : Real) / ((10 : Real) ^ 27)
  | 15 => (1 : Real) / ((10 : Real) ^ 27)
  | _ => 0

private def step33Shift16M6Fin16TermReRad (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (219 : Real) / ((10 : Real) ^ 25)
  | 1 => (140 : Real) / ((10 : Real) ^ 25)
  | 2 => (90 : Real) / ((10 : Real) ^ 25)
  | 3 => (59 : Real) / ((10 : Real) ^ 25)
  | 4 => (39 : Real) / ((10 : Real) ^ 25)
  | 5 => (26 : Real) / ((10 : Real) ^ 25)
  | 6 => (18 : Real) / ((10 : Real) ^ 25)
  | 7 => (12 : Real) / ((10 : Real) ^ 25)
  | 8 => (9 : Real) / ((10 : Real) ^ 25)
  | 9 => (6 : Real) / ((10 : Real) ^ 25)
  | 10 => (5 : Real) / ((10 : Real) ^ 25)
  | 11 => (3 : Real) / ((10 : Real) ^ 25)
  | 12 => (3 : Real) / ((10 : Real) ^ 25)
  | 13 => (2 : Real) / ((10 : Real) ^ 25)
  | 14 => (2 : Real) / ((10 : Real) ^ 25)
  | 15 => (1 : Real) / ((10 : Real) ^ 25)
  | _ => 0

private def step33Shift16M6Fin16TermImRad (n : Fin 16) : Real :=
  match (n : Nat) with
  | 0 => (251 : Real) / ((10 : Real) ^ 27)
  | 1 => (155 : Real) / ((10 : Real) ^ 27)
  | 2 => (98 : Real) / ((10 : Real) ^ 27)
  | 3 => (62 : Real) / ((10 : Real) ^ 27)
  | 4 => (40 : Real) / ((10 : Real) ^ 27)
  | 5 => (26 : Real) / ((10 : Real) ^ 27)
  | 6 => (17 : Real) / ((10 : Real) ^ 27)
  | 7 => (12 : Real) / ((10 : Real) ^ 27)
  | 8 => (8 : Real) / ((10 : Real) ^ 27)
  | 9 => (6 : Real) / ((10 : Real) ^ 27)
  | 10 => (4 : Real) / ((10 : Real) ^ 27)
  | 11 => (3 : Real) / ((10 : Real) ^ 27)
  | 12 => (2 : Real) / ((10 : Real) ^ 27)
  | 13 => (2 : Real) / ((10 : Real) ^ 27)
  | 14 => (1 : Real) / ((10 : Real) ^ 27)
  | 15 => (1 : Real) / ((10 : Real) ^ 27)
  | _ => 0

private def step33Shift16M6Fin16TermRad (n : Fin 16) : Real :=
  step33Shift16M6Fin16TermReRad n + step33Shift16M6Fin16TermImRad n

private def step33Shift16M6Fin16DefectRad : Real :=
  Finset.univ.sum (fun n : Fin 16 => step33Shift16M6Fin16TermRad n)

private theorem step33Shift16M6Fin16DefectReLower :
    ∀ n : Fin 16, step33Shift16M6Fin16TermReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re := by
  intro n
  fin_cases n
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n0_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n1_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n2_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n3_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n4_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n5_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n6_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n7_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n8_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n9_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n10_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n11_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n12_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n13_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n14_component_interval.1.1
  · simpa [step33Shift16M6Fin16TermReLower] using step33_shift16_m6_step_defect_n15_component_interval.1.1

private theorem step33Shift16M6Fin16DefectReUpper :
    ∀ n : Fin 16, (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
        step33Shift16M6Fin16TermReUpper n := by
  intro n
  fin_cases n
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n0_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n1_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n2_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n3_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n4_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n5_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n6_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n7_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n8_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n9_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n10_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n11_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n12_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n13_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n14_component_interval.1.2
  · simpa [step33Shift16M6Fin16TermReUpper] using step33_shift16_m6_step_defect_n15_component_interval.1.2

private theorem step33Shift16M6Fin16DefectImLower :
    ∀ n : Fin 16, step33Shift16M6Fin16TermImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im := by
  intro n
  fin_cases n
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n0_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n1_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n2_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n3_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n4_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n5_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n6_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n7_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n8_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n9_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n10_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n11_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n12_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n13_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n14_component_interval.2.1
  · simpa [step33Shift16M6Fin16TermImLower] using step33_shift16_m6_step_defect_n15_component_interval.2.1

private theorem step33Shift16M6Fin16DefectImUpper :
    ∀ n : Fin 16, (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
        step33Shift16M6Fin16TermImUpper n := by
  intro n
  fin_cases n
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n0_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n1_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n2_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n3_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n4_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n5_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n6_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n7_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n8_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n9_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n10_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n11_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n12_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n13_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n14_component_interval.2.2
  · simpa [step33Shift16M6Fin16TermImUpper] using step33_shift16_m6_step_defect_n15_component_interval.2.2

private theorem step33Shift16M6Fin16ReLowerContain :
    ∀ n : Fin 16,
      -step33Shift16M6Fin16TermReRad n <=
        step33Shift16M6Fin16TermReLower n := by
  intro n
  fin_cases n <;> norm_num [step33Shift16M6Fin16TermReRad,
    step33Shift16M6Fin16TermReLower]

private theorem step33Shift16M6Fin16ReUpperContain :
    ∀ n : Fin 16,
      step33Shift16M6Fin16TermReUpper n <=
        step33Shift16M6Fin16TermReRad n := by
  intro n
  fin_cases n <;> norm_num [step33Shift16M6Fin16TermReRad,
    step33Shift16M6Fin16TermReUpper]

private theorem step33Shift16M6Fin16ImLowerContain :
    ∀ n : Fin 16,
      -step33Shift16M6Fin16TermImRad n <=
        step33Shift16M6Fin16TermImLower n := by
  intro n
  fin_cases n <;> norm_num [step33Shift16M6Fin16TermImRad,
    step33Shift16M6Fin16TermImLower]

private theorem step33Shift16M6Fin16ImUpperContain :
    ∀ n : Fin 16,
      step33Shift16M6Fin16TermImUpper n <=
        step33Shift16M6Fin16TermImRad n := by
  intro n
  fin_cases n <;> norm_num [step33Shift16M6Fin16TermImRad,
    step33Shift16M6Fin16TermImUpper]

private theorem step33Shift16M6Fin16TermRadContain :
    ∀ n : Fin 16,
      step33Shift16M6Fin16TermReRad n +
          step33Shift16M6Fin16TermImRad n <=
        step33Shift16M6Fin16TermRad n := by
  intro n
  simp [step33Shift16M6Fin16TermRad]

private theorem step33Shift16M6Fin16DefectSum_le :
    (Finset.univ.sum
        (fun n : Fin 16 => step33Shift16M6Fin16TermRad n)) <=
      step33Shift16M6Fin16DefectRad := by
  rfl

def step33_shift16_m6_finite_telescope_term_payload_N16_of_checked_component_intervals
    (shiftRad : Real)
    (hShift :
      ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad)
    (hTotal :
      shiftRad + step33Shift16M6Fin16DefectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload :=
  step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    shiftRad step33Shift16M6Fin16DefectRad
    step33Shift16M6Fin16TermReLower step33Shift16M6Fin16TermReUpper
    step33Shift16M6Fin16TermImLower step33Shift16M6Fin16TermImUpper
    step33Shift16M6Fin16TermReRad step33Shift16M6Fin16TermImRad
    step33Shift16M6Fin16TermRad hShift
    step33Shift16M6Fin16DefectReLower
    step33Shift16M6Fin16DefectReUpper
    step33Shift16M6Fin16DefectImLower
    step33Shift16M6Fin16DefectImUpper
    step33Shift16M6Fin16ReLowerContain
    step33Shift16M6Fin16ReUpperContain
    step33Shift16M6Fin16ImLowerContain
    step33Shift16M6Fin16ImUpperContain
    step33Shift16M6Fin16TermRadContain
    step33Shift16M6Fin16DefectSum_le hTotal

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_component_rectangles_and_component_interval_defects
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hDigammaReLower :
      digammaReLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hDigammaReUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).re <=
      digammaReUpper)
    (hDigammaImLower :
      digammaImLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hDigammaImUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex))).im <=
      digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload :=
  step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    shiftRad defectRad
    termReLower termReUpper termImLower termImUpper
    termReRad termImRad termRad
    (step33_shift16_m6_shifted_remainder_bound_of_component_rectangles
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      shiftReRad shiftImRad shiftRad
      hDigammaReLower hDigammaReUpper hDigammaImLower hDigammaImUpper
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad)
    hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
    hReLowerContain hReUpperContain hImLowerContain hImUpperContain
    hTermRad hDefectSum hTotal

theorem complex_norm_le_of_component_interval
    {z : Complex}
    (reLower reUpper imLower imUpper reRad imRad normRad : Real)
    (hReLower : reLower <= z.re)
    (hReUpper : z.re <= reUpper)
    (hImLower : imLower <= z.im)
    (hImUpper : z.im <= imUpper)
    (hReLowerContain : -reRad <= reLower)
    (hReUpperContain : reUpper <= reRad)
    (hImLowerContain : -imRad <= imLower)
    (hImUpperContain : imUpper <= imRad)
    (hNorm : reRad + imRad <= normRad) :
    ‖z‖ <= normRad := by
  have hreAbs : |z.re| <= reRad := by
    exact abs_le.mpr
      ⟨hReLowerContain.trans hReLower,
        hReUpper.trans hReUpperContain⟩
  have himAbs : |z.im| <= imRad := by
    exact abs_le.mpr
      ⟨hImLowerContain.trans hImLower,
        hImUpper.trans hImUpperContain⟩
  have hnorm : ‖z‖ <= |z.re| + |z.im| :=
    CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im z
  exact hnorm.trans ((add_le_add hreAbs himAbs).trans hNorm)

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_high_order_asymptotic_error_rectangles_and_component_interval_defects
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (errorReLower errorReUpper errorImLower errorImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hErrorReLower :
      errorReLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hErrorReUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))).re <=
      errorReUpper)
    (hErrorImLower :
      errorImLower <=
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hErrorImUpper :
        (Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
          Q3.digammaM6AsymptoticMain
            (step33Shift16DigammaPoint + (16 : Complex))).im <=
      errorImUpper)
    (hShiftReLower : -shiftReRad <= errorReLower)
    (hShiftReUpper : errorReUpper <= shiftReRad)
    (hShiftImLower : -shiftImRad <= errorImLower)
    (hShiftImUpper : errorImUpper <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload :=
  step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    shiftRad defectRad
    termReLower termReUpper termImLower termImUpper
    termReRad termImRad termRad
    (complex_norm_le_of_component_interval
      errorReLower errorReUpper errorImLower errorImUpper
      shiftReRad shiftImRad shiftRad
      hErrorReLower hErrorReUpper hErrorImLower hErrorImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad)
    hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
    hReLowerContain hReUpperContain hImLowerContain hImUpperContain
    hTermRad hDefectSum hTotal

def step33_shift16_m6_finite_telescope_term_payload_N16_of_digamma_series_prefix_tail_abs_main_rectangles_and_component_interval_defects
    (seriesN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).re))
    (hRePrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).re) <=
      rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              ((n + seriesN : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLower :
      digammaReLower <= -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpper :
      -gammaLower + rePrefixUpper + reTailRadius <= digammaReUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).im))
    (hImPrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              (n : Complex))).im) <=
      imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 / (step33Shift16DigammaPoint + (16 : Complex) +
              ((n + seriesN : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLower :
      digammaImLower <= imPrefixLower - imTailRadius)
    (hImUpper :
      imPrefixUpper + imTailRadius <= digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload :=
  step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    shiftRad defectRad
    termReLower termReUpper termImLower termImUpper
    termReRad termImRad termRad
    (step33_shift16_m6_shifted_remainder_bound_of_digamma_series_prefix_tail_abs_and_main_rectangles
      seriesN shiftRad shiftReRad shiftImRad
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius
      hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLower hReUpper
      hImPrefixLower hImPrefixUpper hImTail hImLower hImUpper
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad)
    hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
    hReLowerContain hReUpperContain hImLowerContain hImUpperContain
    hTermRad hDefectSum hTotal

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_digamma_series_prefix_tail_abs_main_rectangles_and_component_interval_defects
    (seriesN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hRePrefixLower :
      rePrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re))
    (hRePrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re) <=
      rePrefixUpper)
    (hReTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))).re| <=
        reTailRadius)
    (hReLower :
      digammaReLower <= -gammaUpper + rePrefixLower - reTailRadius)
    (hReUpper :
      -gammaLower + rePrefixUpper + reTailRadius <= digammaReUpper)
    (hImPrefixLower :
      imPrefixLower <=
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im))
    (hImPrefixUpper :
        (Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im) <=
      imPrefixUpper)
    (hImTail :
      |∑' n : Nat,
          (1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))).im| <=
        imTailRadius)
    (hImLower :
      digammaImLower <= imPrefixLower - imTailRadius)
    (hImUpper :
      imPrefixUpper + imTailRadius <= digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload :=
  step33_shift16_m6_finite_telescope_term_payload_N16_of_shifted_remainder_bound_component_interval_defects
    shiftRad defectRad
    termReLower termReUpper termImLower termImUpper
    termReRad termImRad termRad
    (step33_shift16_m6_shifted_remainder_bound_of_shift48_digamma_series_prefix_tail_abs_and_main_rectangles
      seriesN shiftRad shiftReRad shiftImRad
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      gammaLower gammaUpper
      rePrefixLower rePrefixUpper reTailRadius
      imPrefixLower imPrefixUpper imTailRadius
      hGammaLower hGammaUpper
      hRePrefixLower hRePrefixUpper hReTail hReLower hReUpper
      hImPrefixLower hImPrefixUpper hImTail hImLower hImUpper
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad)
    hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
    hReLowerContain hReUpperContain hImLowerContain hImUpperContain
    hTermRad hDefectSum hTotal

def step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_component_interval_defects
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad : Fin 16 -> Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefectReLower : ∀ n : Fin 16,
      termReLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re)
    (hDefectReUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).re <=
      termReUpper n)
    (hDefectImLower : ∀ n : Fin 16,
      termImLower n <=
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im)
    (hDefectImUpper : ∀ n : Fin 16,
        (Q3.digammaM6StepDefect
          (step33Shift16DigammaPoint + ((n : Nat) : Complex))).im <=
      termImUpper n)
    (hReLowerContain : ∀ n : Fin 16, -termReRad n <= termReLower n)
    (hReUpperContain : ∀ n : Fin 16, termReUpper n <= termReRad n)
    (hImLowerContain : ∀ n : Fin 16, -termImRad n <= termImLower n)
    (hImUpperContain : ∀ n : Fin 16, termImUpper n <= termImRad n)
    (hTermRad : ∀ n : Fin 16,
      termReRad n + termImRad n <= termRad n)
    (hDefectSum :
      (Finset.univ.sum (fun n : Fin 16 => termRad n)) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeTermPayload := by
  let z48 : Complex :=
    CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
      ((1 : Real) / (20 : Real)) 48
  let rePrefix : Real :=
    (Finset.range seriesN).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) - 1 / (z48 + (n : Complex))).re)
  let imPrefix : Real :=
    (Finset.range seriesN).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) - 1 / (z48 + (n : Complex))).im)
  have hGamma := Q3.eulerMascheroniConstant_interval_of_seq gammaN
  have hzNoPole : ∀ n : Nat, z48 + n ≠ 0 := by
    intro n
    simpa [z48, ← step33Shift16DigammaPoint_add_16_eq_generated_shift48,
      add_assoc] using step33Shift16DigammaPoint_add_nat_add_nat_ne_zero 16 n
  have hTail :=
    Q3.digamma_series_tail_re_im_abs_of_complex_norm_tail
      z48 seriesN tailRadius hzNoPole (by
        simpa [z48] using hTailNorm)
  exact
    step33_shift16_m6_finite_telescope_term_payload_N16_of_shift48_digamma_series_prefix_tail_abs_main_rectangles_and_component_interval_defects
      seriesN shiftRad defectRad shiftReRad shiftImRad
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      (Real.eulerMascheroniSeq gammaN) (Real.eulerMascheroniSeq' gammaN)
      rePrefix rePrefix tailRadius imPrefix imPrefix tailRadius
      termReLower termReUpper termImLower termImUpper
      termReRad termImRad termRad
      hGamma.1 hGamma.2
      le_rfl le_rfl
      (by simpa [z48] using hTail.1)
      (by simpa [z48, rePrefix] using hReLower)
      (by simpa [z48, rePrefix] using hReUpper)
      le_rfl le_rfl
      (by simpa [z48] using hTail.2)
      (by simpa [z48, imPrefix] using hImLower)
      (by simpa [z48, imPrefix] using hImUpper)
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
      hDefectReLower hDefectReUpper hDefectImLower hDefectImUpper
      hReLowerContain hReUpperContain hImLowerContain hImUpperContain
      hTermRad hDefectSum hTotal

theorem step33_shift16_m6_shifted_remainder_bound_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles
    (seriesN gammaN : Nat)
    (shiftRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad) :
    ‖Q3.digamma (step33Shift16DigammaPoint + (16 : Complex)) -
        Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))‖ <= shiftRad := by
  let z48 : Complex :=
    CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
      ((1 : Real) / (20 : Real)) 48
  let rePrefix : Real :=
    (Finset.range seriesN).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) - 1 / (z48 + (n : Complex))).re)
  let imPrefix : Real :=
    (Finset.range seriesN).sum (fun n : Nat =>
      (1 / ((n : Complex) + 1) - 1 / (z48 + (n : Complex))).im)
  have hGamma := Q3.eulerMascheroniConstant_interval_of_seq gammaN
  have hzNoPole : ∀ n : Nat, z48 + n ≠ 0 := by
    intro n
    simpa [z48, ← step33Shift16DigammaPoint_add_16_eq_generated_shift48,
      add_assoc] using step33Shift16DigammaPoint_add_nat_add_nat_ne_zero 16 n
  have hTail :=
    Q3.digamma_series_tail_re_im_abs_of_complex_norm_tail
      z48 seriesN tailRadius hzNoPole (by
        simpa [z48] using hTailNorm)
  exact
    step33_shift16_m6_shifted_remainder_bound_of_shift48_digamma_series_prefix_tail_abs_and_main_rectangles
      seriesN shiftRad shiftReRad shiftImRad
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      (Real.eulerMascheroniSeq gammaN) (Real.eulerMascheroniSeq' gammaN)
      rePrefix rePrefix tailRadius imPrefix imPrefix tailRadius
      hGamma.1 hGamma.2
      le_rfl le_rfl
      (by simpa [z48] using hTail.1)
      (by simpa [z48, rePrefix] using hReLower)
      (by simpa [z48, rePrefix] using hReUpper)
      le_rfl le_rfl
      (by simpa [z48] using hTail.2)
      (by simpa [z48, imPrefix] using hImLower)
      (by simpa [z48, imPrefix] using hImUpper)
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad

def step33_shift16_m6_finite_telescope_scalar_payload_N16_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles_and_defect_sum
    (seriesN gammaN : Nat)
    (shiftRad defectRad shiftReRad shiftImRad tailRadius : Real)
    (digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper : Real)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + seriesN : Nat) : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 +
                  ((n + seriesN : Nat) : Complex))‖) <=
        tailRadius)
    (hReLower :
      digammaReLower <= -Real.eulerMascheroniSeq' gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) -
          tailRadius)
    (hReUpper :
      -Real.eulerMascheroniSeq gammaN +
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).re)) +
          tailRadius <=
        digammaReUpper)
    (hImLower :
      digammaImLower <=
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) -
          tailRadius)
    (hImUpper :
        ((Finset.range seriesN).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) -
            1 /
              (CenteredCoeffAnalyticABoundsBackend.step22OmegaArchWeightShiftedDigammaArg
                ((1 : Real) / (20 : Real)) 48 + (n : Complex))).im)) +
          tailRadius <=
        digammaImUpper)
    (hMainReLower :
      mainReLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re)
    (hMainReUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).re <=
      mainReUpper)
    (hMainImLower :
      mainImLower <=
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im)
    (hMainImUpper :
        (Q3.digammaM6AsymptoticMain
          (step33Shift16DigammaPoint + (16 : Complex))).im <=
      mainImUpper)
    (hShiftReLower : -shiftReRad <= digammaReLower - mainReUpper)
    (hShiftReUpper : digammaReUpper - mainReLower <= shiftReRad)
    (hShiftImLower : -shiftImRad <= digammaImLower - mainImUpper)
    (hShiftImUpper : digammaImUpper - mainImLower <= shiftImRad)
    (hShiftRad : shiftReRad + shiftImRad <= shiftRad)
    (hDefects :
      (Finset.range 16).sum
          (fun n : Nat =>
            ‖Q3.digammaM6StepDefect
              (step33Shift16DigammaPoint + (n : Complex))‖) <= defectRad)
    (hTotal :
      shiftRad + defectRad <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    Step33Shift16M6FiniteTelescopeScalarPayload where
  N := 16
  shiftRad := shiftRad
  defectRad := defectRad
  hShift :=
    step33_shift16_m6_shifted_remainder_bound_of_shift48_exact_prefix_gamma_seq_complex_tail_main_rectangles
      seriesN gammaN shiftRad shiftReRad shiftImRad tailRadius
      digammaReLower digammaReUpper digammaImLower digammaImUpper
      mainReLower mainReUpper mainImLower mainImUpper
      hTailNorm hReLower hReUpper hImLower hImUpper
      hMainReLower hMainReUpper hMainImLower hMainImUpper
      hShiftReLower hShiftReUpper hShiftImLower hShiftImUpper hShiftRad
  hDefects := hDefects
  hTotal := hTotal

theorem step33_shift16_digamma_m6_expanded_asymptotic_bound_of_first_omitted_term_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (‖step33Shift16DigammaPoint‖⁻¹) ^ 14) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  h.trans step33Shift16DigammaM6FirstOmittedTermBound_le_componentRadius

theorem step33_shift16_digamma_m6_expanded_asymptotic_bound_of_re_first_omitted_term_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        (let z : Complex := step33Shift16DigammaPoint
        Complex.log z
          - ((1 : Complex) / (2 : Complex)) * z⁻¹
          - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
          + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
          - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
          + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
          - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
          + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  h.trans step33Shift16DigammaM6ReFirstOmittedTermBound_le_componentRadius

theorem step33_shift16_digamma_m6_main_norm_of_first_omitted_term_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (‖step33Shift16DigammaPoint‖⁻¹) ^ 14) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
    (step33_shift16_digamma_m6_expanded_asymptotic_bound_of_first_omitted_term_bound
      h)

theorem step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound
    (h :
      ‖Q3.digamma step33Shift16DigammaPoint -
          (let z : Complex := step33Shift16DigammaPoint
          Complex.log z
            - ((1 : Complex) / (2 : Complex)) * z⁻¹
            - ((1 : Complex) / (12 : Complex)) * (z ^ 2)⁻¹
            + ((1 : Complex) / (120 : Complex)) * (z ^ 4)⁻¹
            - ((1 : Complex) / (252 : Complex)) * (z ^ 6)⁻¹
            + ((1 : Complex) / (240 : Complex)) * (z ^ 8)⁻¹
            - ((1 : Complex) / (132 : Complex)) * (z ^ 10)⁻¹
            + (((691 : Complex) / (32760 : Complex)) * (z ^ 12)⁻¹))‖ <=
        ((1 : Real) / (12 : Real)) *
          (step33Shift16DigammaPoint.re⁻¹) ^ 14) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  step33_shift16_digamma_m6_main_norm_of_expanded_asymptotic_bound
    (step33_shift16_digamma_m6_expanded_asymptotic_bound_of_re_first_omitted_term_bound
      h)

theorem step33_shift16_digamma_m6_main_norm_of_integral_remainder_bound
    (hIntegral :
      Q3.digammaM6IntegralRemainderBound step33Shift16DigammaPoint) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound
    (step33_shift16_digamma_m6_re_first_omitted_term_bound_of_generic_integral_remainder
      hIntegral)

theorem step33_shift16_digamma_m6_main_norm :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <=
      step33Shift16DigammaM6MainComponentRadius :=
  step33_shift16_digamma_m6_main_norm_of_integral_remainder_bound
    step33_shift16_digamma_m6_integral_remainder_bound

theorem step33_shift16_digamma_m6_center_component_abs_of_log_component_abs
    (logReCenter logImCenter logReErr logImErr centerReErr centerImErr : Real)
    (hLogRe :
      |(Complex.log step33Shift16DigammaPoint).re - logReCenter| <= logReErr)
    (hLogIm :
      |(Complex.log step33Shift16DigammaPoint).im - logImCenter| <= logImErr)
    (hReBudget :
      logReErr +
          |logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
            step33Shift16DigammaFixedRe| <= centerReErr)
    (hImBudget :
      logImErr +
          |logImCenter + step33Shift16DigammaM6AlgebraicPart.im -
            step33Shift16DigammaFixedIm| <= centerImErr) :
    |(step33Shift16DigammaM6Main -
        step33Shift16DigammaFixedCenter).re| <= centerReErr ∧
      |(step33Shift16DigammaM6Main -
        step33Shift16DigammaFixedCenter).im| <= centerImErr := by
  have hMain := step33Shift16DigammaM6Main_eq_log_add_algebraicPart
  constructor
  · have hRe :
        (step33Shift16DigammaM6Main -
            step33Shift16DigammaFixedCenter).re =
          ((Complex.log step33Shift16DigammaPoint).re - logReCenter) +
            (logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
              step33Shift16DigammaFixedRe) := by
      rw [hMain]
      simp [step33Shift16DigammaFixedCenter]
      ring
    calc
      |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).re|
          = |((Complex.log step33Shift16DigammaPoint).re - logReCenter) +
              (logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
                step33Shift16DigammaFixedRe)| := by rw [hRe]
      _ <= |(Complex.log step33Shift16DigammaPoint).re - logReCenter| +
            |logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
              step33Shift16DigammaFixedRe| :=
          abs_add_le _ _
      _ <= logReErr +
            |logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
              step33Shift16DigammaFixedRe| :=
          add_le_add hLogRe le_rfl
      _ <= centerReErr := hReBudget
  · have hIm :
        (step33Shift16DigammaM6Main -
            step33Shift16DigammaFixedCenter).im =
          ((Complex.log step33Shift16DigammaPoint).im - logImCenter) +
            (logImCenter + step33Shift16DigammaM6AlgebraicPart.im -
              step33Shift16DigammaFixedIm) := by
      rw [hMain]
      simp [step33Shift16DigammaFixedCenter]
      ring
    calc
      |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).im|
          = |((Complex.log step33Shift16DigammaPoint).im - logImCenter) +
              (logImCenter + step33Shift16DigammaM6AlgebraicPart.im -
                step33Shift16DigammaFixedIm)| := by rw [hIm]
      _ <= |(Complex.log step33Shift16DigammaPoint).im - logImCenter| +
            |logImCenter + step33Shift16DigammaM6AlgebraicPart.im -
              step33Shift16DigammaFixedIm| :=
          abs_add_le _ _
      _ <= logImErr +
            |logImCenter + step33Shift16DigammaM6AlgebraicPart.im -
              step33Shift16DigammaFixedIm| :=
          add_le_add hLogIm le_rfl
      _ <= centerImErr := hImBudget

theorem step33_shift16_digamma_m6_center_component_abs_of_log_re_arg_abs
    (logReCenter argCenter logReErr argErr centerReErr centerImErr : Real)
    (hLogRe :
      |Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) -
          logReCenter| <= logReErr)
    (hArg :
      |Complex.arg step33Shift16DigammaPoint - argCenter| <= argErr)
    (hReBudget :
      logReErr +
          |logReCenter + step33Shift16DigammaM6AlgebraicPart.re -
            step33Shift16DigammaFixedRe| <= centerReErr)
    (hImBudget :
      argErr +
          |argCenter + step33Shift16DigammaM6AlgebraicPart.im -
            step33Shift16DigammaFixedIm| <= centerImErr) :
    |(step33Shift16DigammaM6Main -
        step33Shift16DigammaFixedCenter).re| <= centerReErr ∧
      |(step33Shift16DigammaM6Main -
        step33Shift16DigammaFixedCenter).im| <= centerImErr := by
  apply step33_shift16_digamma_m6_center_component_abs_of_log_component_abs
  · simpa [step33Shift16DigammaLog_re_eq_log_sqrt] using hLogRe
  · simpa [step33Shift16DigammaLog_im_eq_arg] using hArg
  · exact hReBudget
  · exact hImBudget

theorem step33_shift16_digamma_fixed_complex_ball_of_main_ball
    (psiMain : Complex) (mainErr centerErr : Real)
    (hMain :
      ‖Q3.digamma step33Shift16DigammaPoint - psiMain‖ <= mainErr)
    (hCenter :
      ‖psiMain - step33Shift16DigammaFixedCenter‖ <= centerErr)
    (hErr : mainErr + centerErr <= step33Shift16DigammaTargetRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaFixedCenter‖ <=
      step33Shift16DigammaTargetRadius := by
  let z : Complex := Q3.digamma step33Shift16DigammaPoint
  let c : Complex := step33Shift16DigammaFixedCenter
  have hdecomp : z - c = (z - psiMain) + (psiMain - c) := by
    ring
  have htri : ‖z - c‖ <= ‖z - psiMain‖ + ‖psiMain - c‖ := by
    rw [hdecomp]
    exact norm_add_le (z - psiMain) (psiMain - c)
  have hMain' : ‖z - psiMain‖ <= mainErr := by
    simpa [z] using hMain
  have hCenter' : ‖psiMain - c‖ <= centerErr := by
    simpa [c] using hCenter
  exact le_trans htri ((add_le_add hMain' hCenter').trans hErr)

theorem step33_shift16_digamma_fixed_complex_ball_of_m6_main
    (mainErr centerErr : Real)
    (hMain :
      ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main‖ <= mainErr)
    (hCenter :
      ‖step33Shift16DigammaM6Main -
        step33Shift16DigammaFixedCenter‖ <= centerErr)
    (hErr : mainErr + centerErr <= step33Shift16DigammaTargetRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaFixedCenter‖ <=
      step33Shift16DigammaTargetRadius :=
  step33_shift16_digamma_fixed_complex_ball_of_main_ball
    step33Shift16DigammaM6Main mainErr centerErr hMain hCenter hErr

theorem step33_shift16_digamma_fixed_complex_ball_of_component_abs
    (hre :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaFixedCenter).re| <=
        step33Shift16DigammaComponentRadius)
    (him :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaFixedCenter).im| <=
        step33Shift16DigammaComponentRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaFixedCenter‖ <=
      step33Shift16DigammaTargetRadius := by
  let z : Complex :=
    Q3.digamma step33Shift16DigammaPoint -
      step33Shift16DigammaFixedCenter
  have hnorm :
      ‖Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaFixedCenter‖ <=
        |(Q3.digamma step33Shift16DigammaPoint -
            step33Shift16DigammaFixedCenter).re| +
          |(Q3.digamma step33Shift16DigammaPoint -
            step33Shift16DigammaFixedCenter).im| := by
    simpa [z] using
      (CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im z)
  have hsum :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaFixedCenter).re| +
        |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaFixedCenter).im| <=
        step33Shift16DigammaComponentRadius +
          step33Shift16DigammaComponentRadius :=
    add_le_add hre him
  have hbudget :
      step33Shift16DigammaComponentRadius +
          step33Shift16DigammaComponentRadius <=
        step33Shift16DigammaTargetRadius := by
    norm_num [step33Shift16DigammaComponentRadius,
      step33Shift16DigammaTargetRadius]
  exact hnorm.trans (hsum.trans hbudget)

theorem step33_shift16_digamma_m6_main_component_abs_of_norm
    (hMain :
      ‖Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main‖ <=
        step33Shift16DigammaM6MainComponentRadius) :
    |(Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main).re| <=
        step33Shift16DigammaM6MainComponentRadius ∧
      |(Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main).im| <=
        step33Shift16DigammaM6MainComponentRadius := by
  constructor
  · exact (Complex.abs_re_le_norm
      (Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main)).trans hMain
  · exact (Complex.abs_im_le_norm
      (Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaM6Main)).trans hMain

theorem step33_shift16_digamma_m6_asymptotic_main_component_abs_of_finite_telescope_scalar_payload
    (payload : Step33Shift16M6FiniteTelescopeScalarPayload) :
    |(Q3.digamma step33Shift16DigammaPoint -
        Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).re| <=
        step33Shift16DigammaM6MainComponentRadius ∧
      |(Q3.digamma step33Shift16DigammaPoint -
        Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).im| <=
        step33Shift16DigammaM6MainComponentRadius := by
  have hMain :
      ‖Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main‖ <=
        step33Shift16DigammaM6MainComponentRadius :=
    step33_shift16_digamma_m6_main_norm_of_re_first_omitted_term_bound
      (step33_shift16_digamma_m6_re_first_omitted_term_bound_of_finite_telescope_scalar_payload
        payload)
  have hComp := step33_shift16_digamma_m6_main_component_abs_of_norm hMain
  constructor
  · simpa [step33Shift16DigammaM6Main_eq_digammaM6AsymptoticMain] using
      hComp.1
  · simpa [step33Shift16DigammaM6Main_eq_digammaM6AsymptoticMain] using
      hComp.2

theorem step33_shift16_digamma_m6_asymptotic_main_component_abs_of_finite_telescope_term_payload
    (payload : Step33Shift16M6FiniteTelescopeTermPayload) :
    |(Q3.digamma step33Shift16DigammaPoint -
        Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).re| <=
        step33Shift16DigammaM6MainComponentRadius ∧
      |(Q3.digamma step33Shift16DigammaPoint -
        Q3.digammaM6AsymptoticMain step33Shift16DigammaPoint).im| <=
        step33Shift16DigammaM6MainComponentRadius :=
  step33_shift16_digamma_m6_asymptotic_main_component_abs_of_finite_telescope_scalar_payload
    payload.toScalarPayload

theorem step33_shift16_digamma_fixed_complex_ball_of_m6_component_abs
    (mainReErr mainImErr centerReErr centerImErr : Real)
    (hMainRe :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main).re| <= mainReErr)
    (hMainIm :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main).im| <= mainImErr)
    (hCenterRe :
      |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).re| <= centerReErr)
    (hCenterIm :
      |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).im| <= centerImErr)
    (hErr :
      (mainReErr + mainImErr) + (centerReErr + centerImErr) <=
        step33Shift16DigammaTargetRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaFixedCenter‖ <=
      step33Shift16DigammaTargetRadius := by
  have hMainNorm :
      ‖Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main‖ <=
        mainReErr + mainImErr := by
    have hnorm :=
      CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im
        (Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main)
    exact hnorm.trans (add_le_add hMainRe hMainIm)
  have hCenterNorm :
      ‖step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter‖ <=
        centerReErr + centerImErr := by
    have hnorm :=
      CenteredCoeffAnalyticABoundsBackend.complex_norm_le_abs_re_add_abs_im
        (step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter)
    exact hnorm.trans (add_le_add hCenterRe hCenterIm)
  exact
    step33_shift16_digamma_fixed_complex_ball_of_m6_main
      (mainReErr + mainImErr) (centerReErr + centerImErr)
      hMainNorm hCenterNorm hErr

theorem step33_shift16_digamma_fixed_complex_ball_of_m6_log_re_arg_fixed_components
    (hMainRe :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main).re| <=
        step33Shift16DigammaM6MainComponentRadius)
    (hMainIm :
      |(Q3.digamma step33Shift16DigammaPoint -
          step33Shift16DigammaM6Main).im| <=
        step33Shift16DigammaM6MainComponentRadius)
    (hLogRe :
      |Real.log (Real.sqrt ((1664101 : Real) / (1600 : Real))) -
          step33Shift16DigammaLogReCenter| <=
        step33Shift16DigammaLogReRadius)
    (hArg :
      |Complex.arg step33Shift16DigammaPoint -
          step33Shift16DigammaArgCenter| <=
        step33Shift16DigammaArgRadius) :
    ‖Q3.digamma step33Shift16DigammaPoint -
        step33Shift16DigammaFixedCenter‖ <=
      step33Shift16DigammaTargetRadius := by
  have hCenter :
      |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).re| <=
          step33Shift16DigammaM6CenterReRadius ∧
        |(step33Shift16DigammaM6Main -
          step33Shift16DigammaFixedCenter).im| <=
          step33Shift16DigammaM6CenterImRadius :=
    step33_shift16_digamma_m6_center_component_abs_of_log_re_arg_abs
      step33Shift16DigammaLogReCenter
      step33Shift16DigammaArgCenter
      step33Shift16DigammaLogReRadius
      step33Shift16DigammaArgRadius
      step33Shift16DigammaM6CenterReRadius
      step33Shift16DigammaM6CenterImRadius
      hLogRe hArg
      (by
        rw [step33Shift16DigammaM6AlgebraicPart_re_eq]
        norm_num [step33Shift16DigammaLogReRadius,
          step33Shift16DigammaLogReCenter,
          step33Shift16DigammaFixedRe,
          step33Shift16DigammaM6CenterReRadius])
      (by
        rw [step33Shift16DigammaM6AlgebraicPart_im_eq]
        norm_num [step33Shift16DigammaArgRadius,
          step33Shift16DigammaArgCenter,
          step33Shift16DigammaFixedIm,
          step33Shift16DigammaM6CenterImRadius])
  exact
    step33_shift16_digamma_fixed_complex_ball_of_m6_component_abs
      step33Shift16DigammaM6MainComponentRadius
      step33Shift16DigammaM6MainComponentRadius
      step33Shift16DigammaM6CenterReRadius
      step33Shift16DigammaM6CenterImRadius
      hMainRe hMainIm hCenter.1 hCenter.2
      (by
        norm_num [step33Shift16DigammaM6MainComponentRadius,
          step33Shift16DigammaM6CenterReRadius,
          step33Shift16DigammaM6CenterImRadius,
          step33Shift16DigammaTargetRadius])

def step33Sub0OmegaPrimeTaylorCenter : Rat :=
  (1 : Rat) / 20

def step33Sub0OmegaPrimeTaylorRadius : Real :=
  (1 : Real) / 20

/-- Proof-bearing receiver for the active Step33A.1-A Omega-prime Taylor
model.  Numeric generators may fill the rational fields only when the `Valid`
proof fields below provide the analytic bridge; this structure by itself is
not a numerical certificate. -/
structure Step33Sub0OmegaPrimeTaylorRemainderCert where
  coeff : Fin 16 -> Rat
  coeffErrorAbs : Fin 16 -> Rat
  order16Abs : Rat
  remainderAbs : Rat

namespace Step33Sub0OmegaPrimeTaylorRemainderCert

private abbrev omegaPrimeClosedForm : Real -> Real :=
  _root_.Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.step22OmegaArchWeightDerivClosedForm

def poly (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (eta : Real) : Real :=
  _root_.Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.rawOmegaATaylorPolynomial
    15 step33Sub0OmegaPrimeTaylorCenter data.coeff eta

def exactTaylorPoly (eta : Real) : Real :=
  ∑ j : Fin 16,
    (iteratedDeriv j.1 omegaPrimeClosedForm
        ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
      (Nat.factorial j.1 : Real)) *
      (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1

structure Valid (data : Step33Sub0OmegaPrimeTaylorRemainderCert) : Prop where
  coeffError_nonneg :
    ∀ j, 0 <= (data.coeffErrorAbs j : Real)
  order16_nonneg :
    0 <= (data.order16Abs : Real)
  centerJet :
    ∀ j : Fin 16,
      ‖iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
          (Nat.factorial j.1 : Real) -
        (data.coeff j : Real)‖ <=
        (data.coeffErrorAbs j : Real)
  order16_bound :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
        (data.order16Abs : Real)
  centerTaylorBridge :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ <=
        (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real)
  remainder_budget :
    (∑ j : Fin 16,
        (data.coeffErrorAbs j : Real) *
          step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
        (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real)
      <= (data.remainderAbs : Real)

private theorem eta_sub_center_abs_le_radius
    {eta : Real}
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    |eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)| <=
      step33Sub0OmegaPrimeTaylorRadius := by
  rw [Set.mem_Icc] at heta
  rw [abs_le]
  constructor <;>
    norm_num [step33Sub0OmegaPrimeTaylorCenter,
      step33Sub0OmegaPrimeTaylorRadius] at heta ⊢ <;>
    linarith

private theorem exactTaylorPoly_sub_poly_bound
    {data : Step33Sub0OmegaPrimeTaylorRemainderCert}
    (h : data.Valid)
    {eta : Real}
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10)) :
    ‖exactTaylorPoly eta - data.poly eta‖ <=
      ∑ j : Fin 16,
        (data.coeffErrorAbs j : Real) *
          step33Sub0OmegaPrimeTaylorRadius ^ j.1 := by
  have hRadius := eta_sub_center_abs_le_radius (eta := eta) heta
  have hdiff :
      exactTaylorPoly eta - data.poly eta =
        ∑ j : Fin 16,
          ((iteratedDeriv j.1 omegaPrimeClosedForm
              ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
              (Nat.factorial j.1 : Real) -
            (data.coeff j : Real)) *
            (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1) := by
    unfold exactTaylorPoly poly
    unfold _root_.Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.rawOmegaATaylorPolynomial
    simp only [Nat.reduceAdd]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hdiff]
  refine (norm_sum_le _ _).trans ?_
  refine Finset.sum_le_sum ?_
  intro j hj
  have hPow :
      ‖(eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1‖ <=
        step33Sub0OmegaPrimeTaylorRadius ^ j.1 := by
    rw [norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hRadius j.1
  have hCoeffNonneg : 0 <= (data.coeffErrorAbs j : Real) :=
    h.coeffError_nonneg j
  calc
    ‖(iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
          (Nat.factorial j.1 : Real) -
        (data.coeff j : Real)) *
        (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1‖
        =
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ *
          ‖(eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1‖ := by
          rw [norm_mul]
    _ <=
        (data.coeffErrorAbs j : Real) *
          step33Sub0OmegaPrimeTaylorRadius ^ j.1 := by
          exact mul_le_mul (h.centerJet j) hPow (norm_nonneg _) hCoeffNonneg

theorem Valid.bound
    {data : Step33Sub0OmegaPrimeTaylorRemainderCert}
    (h : data.Valid) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖omegaPrimeClosedForm eta - data.poly eta‖ <=
        (data.remainderAbs : Real) := by
  intro eta heta
  have hsplit :
      ‖omegaPrimeClosedForm eta - data.poly eta‖ <=
        ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ +
          ‖exactTaylorPoly eta - data.poly eta‖ := by
    have hdecomp :
        omegaPrimeClosedForm eta - data.poly eta =
          (omegaPrimeClosedForm eta - exactTaylorPoly eta) +
            (exactTaylorPoly eta - data.poly eta) := by
      ring
    rw [hdecomp]
    exact norm_add_le _ _
  have hCoeff := exactTaylorPoly_sub_poly_bound h heta
  have hTaylor := h.centerTaylorBridge eta heta
  have hBudget := h.remainder_budget
  calc
    ‖omegaPrimeClosedForm eta - data.poly eta‖
        <=
        ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ +
          ‖exactTaylorPoly eta - data.poly eta‖ := hsplit
    _ <=
        (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real) +
        ∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1 := by
          exact add_le_add hTaylor hCoeff
    _ =
        (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
        (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real) := by
          ring
    _ <= (data.remainderAbs : Real) := hBudget

end Step33Sub0OmegaPrimeTaylorRemainderCert

end Step33
end PSDpd
end Q3
