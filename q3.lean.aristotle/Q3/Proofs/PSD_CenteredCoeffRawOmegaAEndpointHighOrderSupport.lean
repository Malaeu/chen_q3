import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
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

/-- The OmegaPrime closed form is `C^16`; payloads do not need to supply this
analytic smoothness proof. -/
theorem omegaPrimeClosedForm_contDiff16 :
    ContDiff Real 16 omegaPrimeClosedForm := by
  simpa [omegaPrimeClosedForm] using
    _root_.Q3.PSDpd.CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate.step22OmegaArchWeightDerivClosedForm_contDiff16

/-- Reflected-function derivative identity needed for the left half of the
centered OmegaPrime Taylor bridge. -/
theorem omegaPrimeClosedForm_reflected_iteratedDeriv
    (n : Nat) (x : Real) :
    iteratedDeriv n
        (fun y : Real =>
          omegaPrimeClosedForm (((1 : Real) / 10) - y)) x =
      (-1 : Real) ^ n *
        iteratedDeriv n omegaPrimeClosedForm (((1 : Real) / 10) - x) := by
  have hNeg :=
    iteratedDeriv_comp_neg (𝕜 := Real) (F := Real) n
      (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) + y)) x
  have hShift :=
    congrFun
      (iteratedDeriv_comp_const_add (𝕜 := Real) (F := Real) n
        omegaPrimeClosedForm ((1 : Real) / 10)) (-x)
  rw [hShift] at hNeg
  simpa [sub_eq_add_neg, smul_eq_mul] using hNeg

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

theorem taylorWithinEval_eq_exactTaylorPoly
    {s : Set Real}
    (hs : UniqueDiffOn Real s)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hCenter : ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈ s)
    (eta : Real) :
    taylorWithinEval omegaPrimeClosedForm 15 s
        ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) eta =
      exactTaylorPoly eta := by
  rw [taylor_within_apply]
  norm_num only [Nat.reduceAdd]
  rw [← Fin.sum_univ_eq_sum_range
    (f := fun k : Nat =>
      ((Nat.factorial k : Real)⁻¹ *
          (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ k) •
        iteratedDerivWithin k omegaPrimeClosedForm s
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real))
    (n := 16)]
  unfold exactTaylorPoly
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hjle : (j.1 : WithTop ENat) <= (16 : Nat) := by
    exact_mod_cast Nat.le_of_lt j.2
  have hWithin :
      iteratedDerivWithin j.1 omegaPrimeClosedForm s
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) =
        iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
    exact iteratedDerivWithin_eq_iteratedDeriv hs
      ((hSmooth.contDiffAt).of_le hjle) hCenter
  rw [hWithin]
  rw [smul_eq_mul]
  ring_nf

theorem exactTaylorPoly_center :
    ContDiff Real 16 omegaPrimeClosedForm ->
    exactTaylorPoly ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) =
      omegaPrimeClosedForm
        ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
  intro hSmooth
  have hTaylor :=
    taylorWithinEval_eq_exactTaylorPoly
      (s := Set.univ)
      uniqueDiffOn_univ
      hSmooth
      (by simp)
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)
  rw [← hTaylor]
  exact taylorWithinEval_self omegaPrimeClosedForm 15 Set.univ
    ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)

private theorem reflectedTaylorTerm_eq_exactTaylorTerm
    (j : Fin 16) (eta : Real) :
    ((Nat.factorial j.1 : Real)⁻¹ *
        ((((1 : Real) / 10) - eta) -
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1) *
      (((-1 : Real) ^ j.1) *
        iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) =
    (iteratedDeriv j.1 omegaPrimeClosedForm
        ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
      (Nat.factorial j.1 : Real)) *
      (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ j.1 := by
  have hSub :
      (((1 : Real) / 10) - eta) -
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) =
        -(eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) := by
    norm_num [step33Sub0OmegaPrimeTaylorCenter]
    ring
  rw [hSub, neg_pow]
  have hsq : (-1 : Real) ^ (j.1 * 2) = 1 := by
    exact Even.neg_one_pow ⟨j.1, by ring⟩
  ring_nf
  rw [hsq]
  ring

theorem reflectedTaylorWithinEval_eq_exactTaylorPoly
    {s : Set Real}
    (hs : UniqueDiffOn Real s)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hCenter : ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈ s)
    (eta : Real) :
    taylorWithinEval
        (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y))
        15 s ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)
        (((1 : Real) / 10) - eta) =
      exactTaylorPoly eta := by
  rw [taylor_within_apply]
  norm_num only [Nat.reduceAdd]
  rw [← Fin.sum_univ_eq_sum_range
    (f := fun k : Nat =>
      ((Nat.factorial k : Real)⁻¹ *
          ((((1 : Real) / 10) - eta) -
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ k) •
        iteratedDerivWithin k
          (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y))
          s ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real))
    (n := 16)]
  unfold exactTaylorPoly
  refine Finset.sum_congr rfl ?_
  intro j _hj
  have hjle : (j.1 : WithTop ENat) <= (16 : Nat) := by
    exact_mod_cast Nat.le_of_lt j.2
  have hReflectSmooth :
      ContDiff Real 16
        (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y)) := by
    exact hSmooth.comp (by fun_prop)
  have hWithin :
      iteratedDerivWithin j.1
          (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y))
          s ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) =
        iteratedDeriv j.1
          (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y))
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
    exact iteratedDerivWithin_eq_iteratedDeriv hs
      ((hReflectSmooth.contDiffAt).of_le hjle) hCenter
  rw [hWithin]
  rw [omegaPrimeClosedForm_reflected_iteratedDeriv]
  have hReflectCenter :
      ((1 : Real) / 10) -
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) =
        ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
    norm_num [step33Sub0OmegaPrimeTaylorCenter]
  rw [hReflectCenter]
  rw [smul_eq_mul]
  exact reflectedTaylorTerm_eq_exactTaylorTerm j eta

theorem centerTaylorBridge_right_of_order16_bound
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
          (data.order16Abs : Real))
    {eta : Real}
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hCenterLe :
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) <= eta) :
    ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ <=
      (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
        (Nat.factorial 16 : Real) := by
  by_cases hlt :
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) < eta
  · obtain ⟨xi, hxi, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := omegaPrimeClosedForm)
        (x := eta)
        (x₀ := ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real))
        (n := 15)
        hlt
        (hSmooth.contDiffOn)
    have hTaylorPoly :
        taylorWithinEval omegaPrimeClosedForm 15
            (Set.Icc ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) eta)
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) eta =
          exactTaylorPoly eta :=
      taylorWithinEval_eq_exactTaylorPoly
        (s := Set.Icc
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) eta)
        (uniqueDiffOn_Icc hlt)
        hSmooth
        ⟨le_rfl, le_of_lt hlt⟩
        eta
    rw [hTaylorPoly] at hrem
    have hxiCell : xi ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      rw [Set.mem_Ioo] at hxi
      rw [Set.mem_Icc] at heta ⊢
      constructor
      · norm_num [step33Sub0OmegaPrimeTaylorCenter] at hxi ⊢
        linarith
      · nlinarith [hxi.2, heta.2]
    have hDer := hOrder16 xi hxiCell
    have hRadius :
        |eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)| <=
          step33Sub0OmegaPrimeTaylorRadius := by
      rw [Set.mem_Icc] at heta
      rw [abs_le]
      constructor <;>
        norm_num [step33Sub0OmegaPrimeTaylorCenter,
          step33Sub0OmegaPrimeTaylorRadius] at heta ⊢ <;>
        linarith
    have hOrderNonneg : 0 <= (data.order16Abs : Real) := by
      have hc :
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈
            Set.Icc (0 : Real) ((1 : Real) / 10) := by
        norm_num [step33Sub0OmegaPrimeTaylorCenter]
      exact (norm_nonneg _).trans (hOrder16 _ hc)
    have hPow :
        ‖(eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16‖ <=
          step33Sub0OmegaPrimeTaylorRadius ^ 16 := by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hRadius 16
    calc
      ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖
          =
          ‖iteratedDeriv 16 omegaPrimeClosedForm xi *
              (eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16 /
              (Nat.factorial 16 : Real)‖ := by
            rw [hrem]
      _ =
          ‖iteratedDeriv 16 omegaPrimeClosedForm xi‖ *
              ‖(eta - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16‖ /
              (Nat.factorial 16 : Real) := by
            rw [norm_div, norm_mul]
            norm_num
      _ <=
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real) := by
            refine div_le_div_of_nonneg_right ?_ (by norm_num)
            exact mul_le_mul hDer hPow (norm_nonneg _) hOrderNonneg
  · have heta_eq :
        eta = ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
      exact le_antisymm (le_of_not_gt hlt) hCenterLe
    subst eta
    have hOrderNonneg : 0 <= (data.order16Abs : Real) := by
      have hc :
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈
            Set.Icc (0 : Real) ((1 : Real) / 10) := by
        norm_num [step33Sub0OmegaPrimeTaylorCenter]
      exact (norm_nonneg _).trans (hOrder16 _ hc)
    have hRhsNonneg :
        0 <=
          (data.order16Abs : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real) := by
      positivity
    simpa [exactTaylorPoly_center hSmooth] using hRhsNonneg

theorem centerTaylorBridge_left_of_order16_bound
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
          (data.order16Abs : Real))
    {eta : Real}
    (heta : eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10))
    (hEtaLe :
      eta <= ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) :
    ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ <=
      (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
        (Nat.factorial 16 : Real) := by
  let etaR : Real := ((1 : Real) / 10) - eta
  by_cases hlt :
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) < etaR
  · have hReflectSmooth :
        ContDiff Real 16
          (fun y : Real => omegaPrimeClosedForm (((1 : Real) / 10) - y)) := by
      exact hSmooth.comp (by fun_prop)
    obtain ⟨xi, hxi, hrem⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := fun y : Real =>
          omegaPrimeClosedForm (((1 : Real) / 10) - y))
        (x := etaR)
        (x₀ := ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real))
        (n := 15)
        hlt
        (hReflectSmooth.contDiffOn)
    have hTaylorPoly :
        taylorWithinEval
            (fun y : Real =>
              omegaPrimeClosedForm (((1 : Real) / 10) - y))
            15 (Set.Icc
              ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) etaR)
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) etaR =
          exactTaylorPoly eta := by
      simpa [etaR] using
        reflectedTaylorWithinEval_eq_exactTaylorPoly
          (s := Set.Icc
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) etaR)
          (uniqueDiffOn_Icc hlt)
          hSmooth
          ⟨le_rfl, le_of_lt hlt⟩
          eta
    rw [hTaylorPoly] at hrem
    have hxiCell :
        (((1 : Real) / 10) - xi) ∈ Set.Icc (0 : Real) ((1 : Real) / 10) := by
      rw [Set.mem_Ioo] at hxi
      rw [Set.mem_Icc] at heta ⊢
      constructor
      · norm_num [etaR, step33Sub0OmegaPrimeTaylorCenter] at hxi heta ⊢
        linarith
      · norm_num [step33Sub0OmegaPrimeTaylorCenter] at hxi ⊢
        linarith
    have hDerBase := hOrder16 (((1 : Real) / 10) - xi) hxiCell
    have hDer :
        ‖iteratedDeriv 16
            (fun y : Real =>
              omegaPrimeClosedForm (((1 : Real) / 10) - y)) xi‖ <=
          (data.order16Abs : Real) := by
      rw [omegaPrimeClosedForm_reflected_iteratedDeriv]
      norm_num
      simpa using hDerBase
    have hRadius :
        |etaR - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)| <=
          step33Sub0OmegaPrimeTaylorRadius := by
      rw [Set.mem_Icc] at heta
      rw [abs_le]
      constructor <;>
        norm_num [etaR, step33Sub0OmegaPrimeTaylorCenter,
          step33Sub0OmegaPrimeTaylorRadius] at heta ⊢ <;>
        linarith
    have hOrderNonneg : 0 <= (data.order16Abs : Real) := by
      have hc :
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈
            Set.Icc (0 : Real) ((1 : Real) / 10) := by
        norm_num [step33Sub0OmegaPrimeTaylorCenter]
      exact (norm_nonneg _).trans (hOrder16 _ hc)
    have hPow :
        ‖(etaR - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16‖ <=
          step33Sub0OmegaPrimeTaylorRadius ^ 16 := by
      rw [norm_pow, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hRadius 16
    have hrem' :
        omegaPrimeClosedForm eta - exactTaylorPoly eta =
          iteratedDeriv 16
              (fun y : Real =>
                omegaPrimeClosedForm (((1 : Real) / 10) - y)) xi *
            (etaR - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16 /
              (Nat.factorial 16 : Real) := by
      simpa [etaR] using hrem
    calc
      ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖
          =
          ‖iteratedDeriv 16
              (fun y : Real =>
                omegaPrimeClosedForm (((1 : Real) / 10) - y)) xi *
            (etaR - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16 /
              (Nat.factorial 16 : Real)‖ := by
            rw [hrem']
      _ =
          ‖iteratedDeriv 16
              (fun y : Real =>
                omegaPrimeClosedForm (((1 : Real) / 10) - y)) xi‖ *
              ‖(etaR - ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)) ^ 16‖ /
              (Nat.factorial 16 : Real) := by
            rw [norm_div, norm_mul]
            norm_num
      _ <=
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real) := by
            refine div_le_div_of_nonneg_right ?_ (by norm_num)
            exact mul_le_mul hDer hPow (norm_nonneg _) hOrderNonneg
  · have heta_eq :
        eta = ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) := by
      have hCenterLe :
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) <= eta := by
        exact le_of_not_gt (by
          intro hEtaLt
          apply hlt
          norm_num [etaR, step33Sub0OmegaPrimeTaylorCenter] at hEtaLt ⊢
          linarith)
      exact le_antisymm hEtaLe hCenterLe
    subst eta
    have hOrderNonneg : 0 <= (data.order16Abs : Real) := by
      have hc :
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈
            Set.Icc (0 : Real) ((1 : Real) / 10) := by
        norm_num [step33Sub0OmegaPrimeTaylorCenter]
      exact (norm_nonneg _).trans (hOrder16 _ hc)
    have hRhsNonneg :
        0 <=
          (data.order16Abs : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real) := by
      positivity
    simpa [exactTaylorPoly_center hSmooth] using hRhsNonneg

theorem centerTaylorBridge_of_order16_bound
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
          (data.order16Abs : Real)) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖omegaPrimeClosedForm eta - exactTaylorPoly eta‖ <=
        (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real) := by
  intro eta heta
  by_cases hEtaLe :
      eta <= ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)
  · exact centerTaylorBridge_left_of_order16_bound data hSmooth hOrder16 heta hEtaLe
  · exact centerTaylorBridge_right_of_order16_bound data hSmooth hOrder16 heta
      (le_of_lt (lt_of_not_ge hEtaLe))

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

theorem Valid.of_order16_bound
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hSmooth : ContDiff Real 16 omegaPrimeClosedForm)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
          (data.order16Abs : Real))
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid := by
  refine
    ⟨hCoeffErrorNonneg, ?_, hCenterJet, hOrder16,
      centerTaylorBridge_of_order16_bound data hSmooth hOrder16,
      hRemainderBudget⟩
  have hc :
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) ∈
        Set.Icc (0 : Real) ((1 : Real) / 10) := by
    norm_num [step33Sub0OmegaPrimeTaylorCenter]
  exact (norm_nonneg _).trans (hOrder16 _ hc)

theorem Valid.of_order16_bound_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hOrder16 :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
          (data.order16Abs : Real))
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_bound data omegaPrimeClosedForm_contDiff16
    hCoeffErrorNonneg hCenterJet hOrder16 hRemainderBudget

def omegaPrimeOrder16SeriesFactor : Real :=
  (Nat.factorial 17 : Real) / (2 : Real) ^ 17

def omegaPrimeOrder16SeriesBase (eta : Real) (n : Nat) : Complex :=
  (n : Complex) + (1 / 4 : Complex) +
    Complex.I * (((eta / 2 : Real) : Complex))

def omegaPrimeOrder16SeriesTerm (eta : Real) (n : Nat) : Real :=
  (((omegaPrimeOrder16SeriesBase eta n) ^ 18)⁻¹).im

def omegaPrimeOrder16RealMajorant (n : Nat) : Real :=
  (((n : Real) + (1 / 4 : Real)) ^ 18)⁻¹

def omegaPrimeOrder16Series (eta : Real) : Real :=
  ∑' n : Nat, omegaPrimeOrder16SeriesTerm eta n

def omegaPrimeTrigammaSeriesTerm (eta : Real) (n : Nat) : Real :=
  (1 /
    (((1 / 4 : Complex) +
          Complex.I * (((eta / 2 : Real) : Complex))) + n) ^ 2).im

def omegaPrimeTrigammaSeries (eta : Real) : Real :=
  ∑' n : Nat, omegaPrimeTrigammaSeriesTerm eta n

theorem omegaPrimeClosedForm_eq_trigamma_series (eta : Real) :
    omegaPrimeClosedForm eta =
      -((1 / 2 : Real) * omegaPrimeTrigammaSeries eta) := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hz : 0 < z.re := by
    norm_num [z]
  have hseries :
      (trigamma z).im = omegaPrimeTrigammaSeries eta := by
    have h := _root_.im_trigamma_eq_tsum_im hz
    simpa [omegaPrimeTrigammaSeries, omegaPrimeTrigammaSeriesTerm, z,
      add_comm, add_left_comm, add_assoc] using h
  change -((trigamma z).im * (1 / 2 : Real)) =
    -((1 / 2 : Real) * omegaPrimeTrigammaSeries eta)
  rw [hseries]
  ring

theorem omegaPrimeTrigammaSeries_eq_neg_two_closedForm :
    omegaPrimeTrigammaSeries =
      fun eta : Real => (-2 : Real) * omegaPrimeClosedForm eta := by
  funext eta
  calc
    omegaPrimeTrigammaSeries eta =
        (-2 : Real) * (-((1 / 2 : Real) * omegaPrimeTrigammaSeries eta)) := by
          ring
    _ = (-2 : Real) * omegaPrimeClosedForm eta := by
          rw [← omegaPrimeClosedForm_eq_trigamma_series eta]

theorem omegaPrimeTrigammaSeries_contDiff16 :
    ContDiff Real 16 omegaPrimeTrigammaSeries := by
  rw [omegaPrimeTrigammaSeries_eq_neg_two_closedForm]
  simpa [smul_eq_mul] using
    ContDiff.const_smul (-2 : Real) omegaPrimeClosedForm_contDiff16

theorem omegaPrimeTrigammaSeries_contDiffAt16 (eta : Real) :
    ContDiffAt Real 16 omegaPrimeTrigammaSeries eta :=
  omegaPrimeTrigammaSeries_contDiff16.contDiffAt

theorem omegaPrimeOrder16SeriesBase_re (eta : Real) (n : Nat) :
    (omegaPrimeOrder16SeriesBase eta n).re = (n : Real) + (1 / 4 : Real) := by
  simp [omegaPrimeOrder16SeriesBase]

theorem omegaPrimeOrder16SeriesBase_ne_zero (eta : Real) (n : Nat) :
    omegaPrimeOrder16SeriesBase eta n ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  rw [omegaPrimeOrder16SeriesBase_re] at hre
  have hn : 0 <= (n : Real) := Nat.cast_nonneg n
  norm_num at hre
  linarith

theorem omegaPrimeOrder16SeriesBase_hasDerivAt (eta : Real) (n : Nat) :
    HasDerivAt (fun t : Real => omegaPrimeOrder16SeriesBase t n)
      (Complex.I * (((1 / 2 : Real) : Real) : Complex)) eta := by
  unfold omegaPrimeOrder16SeriesBase
  have hdiv : HasDerivAt (fun t : Real => t / 2) (1 / 2 : Real) eta := by
    simpa [div_eq_mul_inv] using
      (hasDerivAt_id eta).mul_const (1 / 2 : Real)
  have hcastF :
      HasFDerivAt
        (fun t : Real => (((t / 2 : Real) : Real) : Complex))
        ((Complex.ofRealCLM).comp
          (ContinuousLinearMap.smulRight
            (1 : Real →L[Real] Real) (1 / 2 : Real))) eta := by
    simpa only [Function.comp_apply, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasFDerivAt.comp eta hdiv.hasFDerivAt)
  have hcast :
      HasDerivAt
        (fun t : Real => (((t / 2 : Real) : Real) : Complex))
        (((1 / 2 : Real) : Real) : Complex) eta := by
    simpa using hcastF.hasDerivAt
  have hI :
      HasDerivAt
        (fun t : Real => Complex.I * (((t / 2 : Real) : Real) : Complex))
        (Complex.I * (((1 / 2 : Real) : Real) : Complex)) eta := by
    exact hcast.const_mul Complex.I
  convert
    ((hasDerivAt_const eta ((n : Complex) + (1 / 4 : Complex))).add hI)
      using 1
  · ring_nf

theorem omegaPrimeOrder16SeriesBase_deriv (eta : Real) (n : Nat) :
    deriv (fun t : Real => omegaPrimeOrder16SeriesBase t n) eta =
      Complex.I * (((1 / 2 : Real) : Real) : Complex) :=
  (omegaPrimeOrder16SeriesBase_hasDerivAt eta n).deriv

theorem omegaPrimeOrder16SeriesBase_zpow_neg_two_hasDerivAt
    (eta : Real) (n : Nat) :
    HasDerivAt
      (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ (-2 : Int))
      (((-2 : Complex) * (omegaPrimeOrder16SeriesBase eta n) ^ (-3 : Int)) *
        (Complex.I * (((1 / 2 : Real) : Real) : Complex))) eta := by
  have h :=
    (hasDerivAt_zpow (-2 : Int) (omegaPrimeOrder16SeriesBase eta n)
      (Or.inl (omegaPrimeOrder16SeriesBase_ne_zero eta n))).comp eta
      (omegaPrimeOrder16SeriesBase_hasDerivAt eta n)
  simpa [Function.comp_def] using h

theorem omegaPrimeOrder16SeriesBase_zpow_iteratedDeriv
    (k : Nat) (m : Int) (eta : Real) (n : Nat) :
    iteratedDeriv k
        (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ m) eta =
      ((Finset.range k).prod
          (fun i : Nat => ((m : Complex) - (i : Complex)))) *
        (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k *
        (omegaPrimeOrder16SeriesBase eta n) ^ (m - (k : Int)) := by
  induction k generalizing m eta with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      have hfun :
          iteratedDeriv k
              (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ m) =
            fun eta : Real =>
              ((Finset.range k).prod
                  (fun i : Nat => ((m : Complex) - (i : Complex)))) *
                (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k *
                (omegaPrimeOrder16SeriesBase eta n) ^ (m - (k : Int)) := by
        funext x
        exact ih m x
      rw [hfun]
      have hstep :
          deriv
            (fun t : Real =>
              (((Finset.range k).prod
                  (fun i : Nat => ((m : Complex) - (i : Complex)))) *
                (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k *
                (omegaPrimeOrder16SeriesBase t n) ^ (m - (k : Int))))
              eta =
            (((Finset.range k).prod
                (fun i : Nat => ((m : Complex) - (i : Complex)))) *
              (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k) *
              ((((m - (k : Int)) : Complex) *
                (omegaPrimeOrder16SeriesBase eta n) ^
                  ((m - (k : Int)) - 1)) *
                (Complex.I * (((1 / 2 : Real) : Real) : Complex))) := by
        have hz :=
          (hasDerivAt_zpow (m - (k : Int))
            (omegaPrimeOrder16SeriesBase eta n)
            (Or.inl (omegaPrimeOrder16SeriesBase_ne_zero eta n))).comp eta
            (omegaPrimeOrder16SeriesBase_hasDerivAt eta n)
        have hC := hz.const_mul
          (((Finset.range k).prod
              (fun i : Nat => ((m : Complex) - (i : Complex)))) *
            (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k)
        simpa [Function.comp_def, mul_assoc] using hC.deriv
      rw [hstep]
      simp [Finset.prod_range_succ]
      ring_nf

theorem omegaPrimeOrder16SeriesBase_zpow_neg_two_iteratedDeriv16
    (eta : Real) (n : Nat) :
    iteratedDeriv 16
        (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ (-2 : Int))
        eta =
      ((Nat.factorial 17 : Complex) / (2 : Complex) ^ 16) *
        (omegaPrimeOrder16SeriesBase eta n) ^ (-18 : Int) := by
  rw [omegaPrimeOrder16SeriesBase_zpow_iteratedDeriv]
  have hbase18 : omegaPrimeOrder16SeriesBase eta n ^ 18 ≠ 0 := by
    exact pow_ne_zero 18 (omegaPrimeOrder16SeriesBase_ne_zero eta n)
  have hIhalf16 :
      (Complex.I * (1 / 2 : Complex)) ^ 16 =
        (1 / (2 : Complex) ^ 16) := by
    have hI16 : Complex.I ^ 16 = (1 : Complex) := by
      rw [show (16 : Nat) = 2 * 8 by norm_num]
      rw [pow_mul]
      rw [Complex.I_sq]
      norm_num
    rw [mul_pow, hI16]
    ring_nf
  norm_num [hbase18]
  left
  rw [hIhalf16]
  norm_num

theorem omegaPrimeOrder16SeriesBase_zpow_im_iteratedDeriv
    (k : Nat) (m : Int) (eta : Real) (n : Nat) :
    iteratedDeriv k
        (fun t : Real => ((omegaPrimeOrder16SeriesBase t n) ^ m).im) eta =
      (((Finset.range k).prod
          (fun i : Nat => ((m : Complex) - (i : Complex)))) *
        (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k *
        (omegaPrimeOrder16SeriesBase eta n) ^ (m - (k : Int))).im := by
  induction k generalizing m eta with
  | zero =>
      simp
  | succ k ih =>
      rw [iteratedDeriv_succ]
      let C : Complex :=
        ((Finset.range k).prod
            (fun i : Nat => ((m : Complex) - (i : Complex)))) *
          (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k
      have hfun :
          iteratedDeriv k
              (fun t : Real => ((omegaPrimeOrder16SeriesBase t n) ^ m).im) =
            fun eta : Real =>
              (C * (omegaPrimeOrder16SeriesBase eta n) ^
                (m - (k : Int))).im := by
        funext x
        simpa [C] using ih m x
      rw [hfun]
      have hstep :
          deriv
            (fun t : Real =>
              (C * (omegaPrimeOrder16SeriesBase t n) ^
                (m - (k : Int))).im) eta =
            (C * ((((m - (k : Int)) : Complex) *
              (omegaPrimeOrder16SeriesBase eta n) ^
                ((m - (k : Int)) - 1)) *
              (Complex.I * (((1 / 2 : Real) : Real) : Complex)))).im := by
        have hz :=
          (hasDerivAt_zpow (m - (k : Int))
            (omegaPrimeOrder16SeriesBase eta n)
            (Or.inl (omegaPrimeOrder16SeriesBase_ne_zero eta n))).comp eta
            (omegaPrimeOrder16SeriesBase_hasDerivAt eta n)
        have hC := hz.const_mul C
        have himF := Complex.imCLM.hasFDerivAt.comp eta hC.hasFDerivAt
        have him := himF.hasDerivAt
        simpa [Function.comp_def] using him.deriv
      rw [hstep]
      apply congrArg Complex.im
      simp [C, Finset.prod_range_succ]
      ring_nf

theorem omegaPrimeOrder16SeriesTerm_iteratedDeriv16
    (eta : Real) (n : Nat) :
    iteratedDeriv 16
        (fun t : Real => ((omegaPrimeOrder16SeriesBase t n) ^ (-2 : Int)).im)
        eta =
      ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
        omegaPrimeOrder16SeriesTerm eta n := by
  rw [omegaPrimeOrder16SeriesBase_zpow_im_iteratedDeriv]
  have hcoeff := omegaPrimeOrder16SeriesBase_zpow_neg_two_iteratedDeriv16 eta n
  rw [omegaPrimeOrder16SeriesBase_zpow_iteratedDeriv] at hcoeff
  rw [hcoeff]
  have hzpow :
      (omegaPrimeOrder16SeriesBase eta n) ^ (-18 : Int) =
        ((omegaPrimeOrder16SeriesBase eta n) ^ 18)⁻¹ := by
    rw [show (-18 : Int) = -(18 : Int) by norm_num]
    rw [zpow_neg]
    rfl
  rw [hzpow]
  have hcoeffRe :
      (((Nat.factorial 17 : Complex) / (2 : Complex) ^ 16).re) =
        ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) := by
    norm_num
  have hcoeffIm :
      (((Nat.factorial 17 : Complex) / (2 : Complex) ^ 16).im) = 0 := by
    norm_num
  simp [omegaPrimeOrder16SeriesTerm, hcoeffRe, hcoeffIm]

theorem omegaPrimeOrder16TrigammaSeriesTerm_iteratedDeriv16
    (eta : Real) (n : Nat) :
    iteratedDeriv 16
        (fun t : Real =>
          (1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((t / 2 : Real) : Complex))) + n) ^ 2).im)
        eta =
      ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
        omegaPrimeOrder16SeriesTerm eta n := by
  have hfun :
      (fun t : Real =>
          (1 /
            (((1 / 4 : Complex) +
                  Complex.I * (((t / 2 : Real) : Complex))) + n) ^ 2).im) =
        fun t : Real =>
          ((omegaPrimeOrder16SeriesBase t n) ^ (-2 : Int)).im := by
    funext t
    have hbase :
        (((1 / 4 : Complex) +
              Complex.I * (((t / 2 : Real) : Complex))) + n) =
          omegaPrimeOrder16SeriesBase t n := by
      unfold omegaPrimeOrder16SeriesBase
      ring_nf
    rw [hbase]
    rw [one_div]
    rw [show (-2 : Int) = -(2 : Int) by norm_num]
    rw [zpow_neg]
    rfl
  rw [hfun]
  exact omegaPrimeOrder16SeriesTerm_iteratedDeriv16 eta n

def omegaPrimeOrder16TrigammaSeriesDerivTerm (eta : Real) (n : Nat) : Real :=
  iteratedDeriv 16
    (fun t : Real =>
      (1 /
        (((1 / 4 : Complex) +
              Complex.I * (((t / 2 : Real) : Complex))) + n) ^ 2).im)
    eta

theorem omegaPrimeOrder16TrigammaSeriesDerivTerm_eq_iteratedDeriv_term
    (eta : Real) (n : Nat) :
    omegaPrimeOrder16TrigammaSeriesDerivTerm eta n =
      iteratedDeriv 16
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta := by
  rfl

theorem omegaPrimeTrigammaSeriesTerm_eq_base_zpow_neg_two
    (eta : Real) (n : Nat) :
    omegaPrimeTrigammaSeriesTerm eta n =
      ((omegaPrimeOrder16SeriesBase eta n) ^ (-2 : Int)).im := by
  have hbase :
      (((1 / 4 : Complex) +
            Complex.I * (((eta / 2 : Real) : Complex))) + n) =
        omegaPrimeOrder16SeriesBase eta n := by
    unfold omegaPrimeOrder16SeriesBase
    ring_nf
  rw [omegaPrimeTrigammaSeriesTerm, hbase]
  rw [one_div]
  rw [show (-2 : Int) = -(2 : Int) by norm_num]
  rw [zpow_neg]
  rfl

theorem omegaPrimeTrigammaSeriesTerm_iteratedDeriv
    (k : Nat) (eta : Real) (n : Nat) :
    iteratedDeriv k
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta =
      (((Finset.range k).prod
          (fun i : Nat => (((-2 : Int) : Complex) - (i : Complex)))) *
        (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k *
        (omegaPrimeOrder16SeriesBase eta n) ^ ((-2 : Int) - (k : Int))).im := by
  have hfun :
      (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) =
        fun t : Real =>
          ((omegaPrimeOrder16SeriesBase t n) ^ (-2 : Int)).im := by
    funext t
    exact omegaPrimeTrigammaSeriesTerm_eq_base_zpow_neg_two t n
  rw [hfun]
  exact omegaPrimeOrder16SeriesBase_zpow_im_iteratedDeriv k (-2 : Int) eta n

theorem omegaPrimeCenterJetPrefix_m0_N1_smoke_direct :
    ((Nat.factorial 0 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 0
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (16000 / 10201 : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, Complex.normSq]
  rw [zpow_two]
  simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im]
  norm_num

def omegaPrimeCenterBaseReRat (n : Nat) : Rat :=
  (n : Rat) + (1 / 4 : Rat)

def omegaPrimeCenterBaseImRat : Rat :=
  (1 / 40 : Rat)

def omegaPrimeCenterJetM0TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-2 * a * b) / ((a * a + b * b) ^ 2)

def omegaPrimeCenterJetM0PrefixRat (N : Nat) : Rat :=
  (-1 / 2 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM0TermRat n)

def omegaPrimeCenterJetM1TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-(a * a * a - 3 * a * b * b)) / ((a * a + b * b) ^ 3)

def omegaPrimeCenterJetM1PrefixRat (N : Nat) : Rat :=
  (-1 / 2 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM1TermRat n)

def omegaPrimeCenterJetM2TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (6 * a * b * (a * a - b * b)) / ((a * a + b * b) ^ 4)

def omegaPrimeCenterJetM2PrefixRat (N : Nat) : Rat :=
  (-1 / 4 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM2TermRat n)

def omegaPrimeCenterJetM3TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (3 * (a * a * a * a * a - 10 * a * a * a * b * b +
    5 * a * b * b * b * b)) / ((a * a + b * b) ^ 5)

def omegaPrimeCenterJetM3PrefixRat (N : Nat) : Rat :=
  (-1 / 12 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM3TermRat n)

def omegaPrimeCenterJetM4TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-45 * a * a * a * a * a * b + 150 * a * a * a * b * b * b -
    45 * a * b * b * b * b * b) / ((a * a + b * b) ^ 6)

def omegaPrimeCenterJetM4PrefixRat (N : Nat) : Rat :=
  (-1 / 48 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM4TermRat n)

def omegaPrimeCenterJetM5TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((-45 / 2 : Rat) * a ^ 7 + (945 / 2 : Rat) * a ^ 5 * b ^ 2 -
    (1575 / 2 : Rat) * a ^ 3 * b ^ 4 + (315 / 2 : Rat) * a * b ^ 6) /
      ((a * a + b * b) ^ 7)

def omegaPrimeCenterJetM5PrefixRat (N : Nat) : Rat :=
  (-1 / 240 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM5TermRat n)

def omegaPrimeCenterJetM6TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((630 : Rat) * a ^ 7 * b - (4410 : Rat) * a ^ 5 * b ^ 3 +
    (4410 : Rat) * a ^ 3 * b ^ 5 - (630 : Rat) * a * b ^ 7) /
      ((a * a + b * b) ^ 8)

def omegaPrimeCenterJetM6PrefixRat (N : Nat) : Rat :=
  (-1 / 1440 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM6TermRat n)

def omegaPrimeCenterJetM7TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((315 : Rat) * a ^ 9 - (11340 : Rat) * a ^ 7 * b ^ 2 +
    (39690 : Rat) * a ^ 5 * b ^ 4 - (26460 : Rat) * a ^ 3 * b ^ 6 +
      (2835 : Rat) * a * b ^ 8) / ((a * a + b * b) ^ 9)

def omegaPrimeCenterJetM7PrefixRat (N : Nat) : Rat :=
  (-1 / 10080 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM7TermRat n)

def omegaPrimeCenterJetM8TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-(14175 : Rat) * a ^ 9 * b + (170100 : Rat) * a ^ 7 * b ^ 3 -
    (357210 : Rat) * a ^ 5 * b ^ 5 + (170100 : Rat) * a ^ 3 * b ^ 7 -
      (14175 : Rat) * a * b ^ 9) / ((a * a + b * b) ^ 10)

def omegaPrimeCenterJetM8PrefixRat (N : Nat) : Rat :=
  (-1 / 80640 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM8TermRat n)

def omegaPrimeCenterJetM9TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-(14175 / 2 : Rat) * a ^ 11
    + (779625 / 2 : Rat) * a ^ 9 * b ^ 2
    - (2338875 : Rat) * a ^ 7 * b ^ 4
    + (3274425 : Rat) * a ^ 5 * b ^ 6
    - (2338875 / 2 : Rat) * a ^ 3 * b ^ 8
    + (155925 / 2 : Rat) * a * b ^ 10) / ((a * a + b * b) ^ 11)

def omegaPrimeCenterJetM9PrefixRat (N : Nat) : Rat :=
  (-1 / 725760 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM9TermRat n)

def omegaPrimeCenterJetM10TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((467775 : Rat) * a ^ 11 * b
    - (8575875 : Rat) * a ^ 9 * b ^ 3
    + (30873150 : Rat) * a ^ 7 * b ^ 5
    - (30873150 : Rat) * a ^ 5 * b ^ 7
    + (8575875 : Rat) * a ^ 3 * b ^ 9
    - (467775 : Rat) * a * b ^ 11) / ((a * a + b * b) ^ 12)

def omegaPrimeCenterJetM10PrefixRat (N : Nat) : Rat :=
  (-1 / 7257600 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM10TermRat n)

def omegaPrimeCenterJetM11TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((467775 / 2 : Rat) * a ^ 13
    - (18243225 : Rat) * a ^ 11 * b ^ 2
    + (334459125 / 2 : Rat) * a ^ 9 * b ^ 4
    - (401350950 : Rat) * a ^ 7 * b ^ 6
    + (602026425 / 2 : Rat) * a ^ 5 * b ^ 8
    - (66891825 : Rat) * a ^ 3 * b ^ 10
    + (6081075 / 2 : Rat) * a * b ^ 12) / ((a * a + b * b) ^ 13)

def omegaPrimeCenterJetM11PrefixRat (N : Nat) : Rat :=
  (-1 / 79833600 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM11TermRat n)

def omegaPrimeCenterJetM12TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-(42567525 / 2 : Rat) * a ^ 13 * b
    + (553377825 : Rat) * a ^ 11 * b ^ 3
    - (6087156075 / 2 : Rat) * a ^ 9 * b ^ 5
    + (5217562350 : Rat) * a ^ 7 * b ^ 7
    - (6087156075 / 2 : Rat) * a ^ 5 * b ^ 9
    + (553377825 : Rat) * a ^ 3 * b ^ 11
    - (42567525 / 2 : Rat) * a * b ^ 13) / ((a * a + b * b) ^ 14)

def omegaPrimeCenterJetM12PrefixRat (N : Nat) : Rat :=
  (-1 / 958003200 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM12TermRat n)

def omegaPrimeCenterJetM13TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  (-(42567525 / 4 : Rat) * a ^ 15
    + (4469590125 / 4 : Rat) * a ^ 13 * b ^ 2
    - (58104671625 / 4 : Rat) * a ^ 11 * b ^ 4
    + (213050462625 / 4 : Rat) * a ^ 9 * b ^ 6
    - (273922023375 / 4 : Rat) * a ^ 7 * b ^ 8
    + (127830277575 / 4 : Rat) * a ^ 5 * b ^ 10
    - (19368223875 / 4 : Rat) * a ^ 3 * b ^ 12
    + (638512875 / 4 : Rat) * a * b ^ 14) / ((a * a + b * b) ^ 15)

def omegaPrimeCenterJetM13PrefixRat (N : Nat) : Rat :=
  (-1 / 12454041600 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM13TermRat n)

def omegaPrimeCenterJetM14TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((1277025750 : Rat) * a ^ 15 * b
    - (44695901250 : Rat) * a ^ 13 * b ^ 3
    + (348628029750 : Rat) * a ^ 11 * b ^ 5
    - (913073411250 : Rat) * a ^ 9 * b ^ 7
    + (913073411250 : Rat) * a ^ 7 * b ^ 9
    - (348628029750 : Rat) * a ^ 5 * b ^ 11
    + (44695901250 : Rat) * a ^ 3 * b ^ 13
    - (1277025750 : Rat) * a * b ^ 15) / ((a * a + b * b) ^ 16)

def omegaPrimeCenterJetM14PrefixRat (N : Nat) : Rat :=
  (-1 / 174356582400 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM14TermRat n)

def omegaPrimeCenterJetM15TermRat (n : Nat) : Rat :=
  let a : Rat := omegaPrimeCenterBaseReRat n
  let b : Rat := omegaPrimeCenterBaseImRat
  ((638512875 : Rat) * a ^ 17
    - (86837751000 : Rat) * a ^ 15 * b ^ 2
    + (1519660642500 : Rat) * a ^ 13 * b ^ 4
    - (7902235341000 : Rat) * a ^ 11 * b ^ 6
    + (15522247991250 : Rat) * a ^ 9 * b ^ 8
    - (12417798393000 : Rat) * a ^ 7 * b ^ 10
    + (3951117670500 : Rat) * a ^ 5 * b ^ 12
    - (434188755000 : Rat) * a ^ 3 * b ^ 14
    + (10854718875 : Rat) * a * b ^ 16) / ((a * a + b * b) ^ 17)

def omegaPrimeCenterJetM15PrefixRat (N : Nat) : Rat :=
  (-1 / 2615348736000 : Rat) *
    (Finset.range N).sum (fun n : Nat => omegaPrimeCenterJetM15TermRat n)

theorem omegaPrimeCenterJetM0TermRat_zero :
    omegaPrimeCenterJetM0TermRat 0 = (-32000 / 10201 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM0PrefixRat_one :
    omegaPrimeCenterJetM0PrefixRat 1 = (16000 / 10201 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM1TermRat_zero :
    omegaPrimeCenterJetM1TermRat 0 = (-62080000 / 1030301 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM1PrefixRat_one :
    omegaPrimeCenterJetM1PrefixRat 1 = (31040000 / 1030301 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM2TermRat_zero :
    omegaPrimeCenterJetM2TermRat 0 = (15206400000 / 104060401 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM2PrefixRat_one :
    omegaPrimeCenterJetM2PrefixRat 1 = (-3801600000 / 104060401 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM3TermRat_zero :
    omegaPrimeCenterJetM3TermRat 0 = (27663360000000 / 10510100501 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM3PrefixRat_one :
    omegaPrimeCenterJetM3PrefixRat 1 = (-2305280000000 / 10510100501 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM4TermRat_zero :
    omegaPrimeCenterJetM4TermRat 0 =
      (-17819443200000000 / 1061520150601 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM4PrefixRat_one :
    omegaPrimeCenterJetM4PrefixRat 1 =
      (371238400000000 / 1061520150601 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM5TermRat_zero :
    omegaPrimeCenterJetM5TermRat 0 =
      (-29251325952000000000 / 107213535210701 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM5PrefixRat_one :
    omegaPrimeCenterJetM5PrefixRat 1 =
      (121880524800000000 / 107213535210701 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM6TermRat_zero :
    omegaPrimeCenterJetM6TermRat 0 =
      (38426402488320000000000 / 10828567056280801 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM6PrefixRat_one :
    omegaPrimeCenterJetM6PrefixRat 1 =
      (-26685001728000000000 / 10828567056280801 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM7TermRat_zero :
    omegaPrimeCenterJetM7TermRat 0 =
      (53881751037542400000000000 / 1093685272684360901 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM7PrefixRat_one :
    omegaPrimeCenterJetM7PrefixRat 1 =
      (-5345411809280000000000 / 1093685272684360901 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM8TermRat_zero :
    omegaPrimeCenterJetM8TermRat 0 =
      (-131172149931540480000000000000 / 110462212541120451001 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM8PrefixRat_one :
    omegaPrimeCenterJetM8PrefixRat 1 =
      (1626638764032000000000000 / 110462212541120451001 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM9TermRat_zero :
    omegaPrimeCenterJetM9TermRat 0 = (-143445186799887974400000000000000 / 11156683466653165551101 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM9PrefixRat_one :
    omegaPrimeCenterJetM9PrefixRat 1 = (197648240189440000000000000 / 11156683466653165551101 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM10TermRat_zero :
    omegaPrimeCenterJetM10TermRat 0 = (646044916487716601856000000000000000 / 1126825030131969720661201 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM10PrefixRat_one :
    omegaPrimeCenterJetM10PrefixRat 1 = (-89016329983426560000000000000 / 1126825030131969720661201 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM11TermRat_zero :
    omegaPrimeCenterJetM11TermRat 0 = (454862932252338620989440000000000000000 / 113809328043328941786781301 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM11PrefixRat_one :
    omegaPrimeCenterJetM11PrefixRat 1 = (-5697637739652710400000000000000 / 113809328043328941786781301 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM12TermRat_zero :
    omegaPrimeCenterJetM12TermRat 0 = (-4308162206443401194451763200000000000000000 / 11494742132376223120464911401 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM12PrefixRat_one :
    omegaPrimeCenterJetM12PrefixRat 1 = (4497022772411826176000000000000000 / 11494742132376223120464911401 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM13TermRat_zero :
    omegaPrimeCenterJetM13TermRat 0 = (-931945332656690743518167040000000000000000000 / 1160968955369998535166956051501 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM13PrefixRat_one :
    omegaPrimeCenterJetM13PrefixRat 1 = (74830754753275494400000000000000000 / 1160968955369998535166956051501 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM14TermRat_zero :
    omegaPrimeCenterJetM14TermRat 0 = (37109615359059830179839659212800000000000000000000 / 117257864492369852051862561201601 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM14PrefixRat_one :
    omegaPrimeCenterJetM14PrefixRat 1 = (-212837478506689462272000000000000000000 / 117257864492369852051862561201601 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM15TermRat_zero :
    omegaPrimeCenterJetM15TermRat 0 = (-14714011884359017865945234276352000000000000000000000 / 11843044313729355057238118681361701 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM15PrefixRat_one :
    omegaPrimeCenterJetM15PrefixRat 1 = (5626022901581801848832000000000000000000 / 11843044313729355057238118681361701 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM0PrefixRat_128 :
    omegaPrimeCenterJetM0PrefixRat 128 =
      (68066281403200232754570194851818451133319603953996150684561717827965622042589500813961014678375534312602413166573913726969702651300843106032869485288169280520707693614507268955925032846864902297173686260361308868704444134356442273159525087448670247891682123499322551069150253813376675515112657076983466908931154627983419187038262190473668411237554508507055773400788797835269488302299262947758889960761923896117476060966416767624433978221585830743028794791716689980230231306922520858285294417770603080250421336606463312211457557491197588331802633674588822956925084066148210145479385946013901504491721442874151077921345657106187270808522971956114498914674359437959454606040377202915480539401546127188122046019579953682411209938368342347480960021004002750526414285144102708084496607463452297585617792642169771696115602194063972949965665211437616518702968569351292956862521136079173692663720506572567399134198064576282411705455986793019365017399280102540689487590864246762804067128538500187316993126362106202126072812097858907873871041345288937379725662705082588811997725364918251004714038349470523098795319696947234727593027480922041745616227839661593105461361228536633952086622601736166763697831957088331518622470266281344479664031916785476199969759575698695533978994120589494848195670082382161430089650221467631496772802459145814251224141502484994105994036777439340221840887841244436114936394073475806612679761737795377283892664320000 /
        42942434050794799107457287852911847512458113783699090296361147193364860297635628522470663298151540673761757616318844431446534583061317845913094693659459200273008409800843188245597980331914067977431929080897490696624839785981755376301782781256764831978634212287247536862921420053691140374187514082812323210292200067041374973755357811187225266416392659066412133615108403603084445343023611609769100083955866092949492091205209625743181243667986022570575325139632921720553960619371202481242816494066679288991694760600126826692585708349501471025309587190361276830740589006096431538492549509616560288062398926173594663105926973251673586566247455936599609807488981344667338132377684360877010548700010716991266057070690964281284991692303762119064794737044359277654907085886606516520063787633494796431300518518109293612198689987308217416828491754692228506740414508473272054327440409979316757683315769285063206009181941898937281115704724727947918489796237943262507854087989767491745381886831303682859610227439206689113552827686258939105718053464947324560372277913279377536612207409490241651967629703792186119938335411668886481496230409958528841404513284259259362693180197693042477292319181117676509561535229232153192830572326495429623197462610881712833817305501290363127223844566659685626477970252463946027802471038944498466806408939308416051091820859491419512075511220237784309596323852421918299741748403455789985489671525230797508580226255693 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM1PrefixRat_128 :
    omegaPrimeCenterJetM1PrefixRat 128 =
      (104580484701119999554691561973382867385975232866344486811453231890186247178869845096173700083482222854701996139550959033830242138801855087083993257730388562934893964417622906150482638829480665854904418267458036217028584675425939693148150147624456993132182393093354532153059924928953308494322204642009201070349755060033294077946891718885591312998979892997905901812438649901730448230760461636965118066838309406237558680636734633072531495353477015808353547096748139852845503118909676236710096363983643258334488596597369550830746557862072167148236663965357299690742410692228996103834988228921442529951190692419708993961620776386621929304281215527791118466914713328858638806683045619891962860623294814708240219864045377287568350066684255342027555905489405683719079212510548293111715815196525612841034755784398128404920250727201965131684784096018334023256892160612190617734301743352727883414799752650726926743535088289862078822365104665990717741162523008573831434967165329616233576942506715591176645288133591924436727900576931946399652838703759609968737315846244529674927499220163718290787637196649203084765934411147429608011267656127499170958301928987960374456224619114139281736657713949966862260067354159530661932852786391006919436693416325860440491177535418403028874188049268317055726962464089282136984019308777632750690791522168241222631531464855557077996309959080044645104611774149675635735240715002653538771899749216740033911185553808864987277868918713295145322745765090586207458747646739347138678319454971566093923260327212033812210770278988588201275061131481183122095730844123686640944715468960030390910635946802348308933463971694567151162827458074028644252264945914703014987176704474307373842275161577301994221055268282356319961975343465173111487794002576467192448355571886352790156496374189212836308296498858446263927627255240179313657743091125061244740868880686330606498866400647386620606610959070776151127057467871801674144345916150224883723429395294430462929873976252270847504847945968567306066686042755127526684649354124496550636073192115349583260959428439967163809301033782100224572733928661437280540554917978378689486842815454652864870604800000 /
        3433553276089700863041261979930040016717580675274813367356721756410195338122555408465476579798211842799331306821255948246553097767604055576858934735045579104378834288971701832793814576025806525416145068114301479881061928085562318191042529496070964163359177950663561493253693845339561808466003182846886191849502238086427129908230072777458631217411191109251807625572453507640684859350284358750408091591697291985075746468489864371759910371044521071085325912780235695664128598270744278494523982773508736356844884874331422875702051802226259874723711478569103073693249235703459008635916755967958947563605439867652398991868737366416390371399445950846321992977485982821607853890395872958589620599194230010934760702504352569565410557130579512497377171920609485201858882007523538517462058191705232506204388599304884315627641358291958063982049280873595287642936124828731682900420415935877587944303548049725489706591375732239496619276420198625021893771519568154210921470017738458162392342614875648073664276956304353116257568145627923944700353001362832846731825642441405974204155652007134788434896470722835984053166449505638551900438701570860451108722210722113352283577757938787285246316088509452682044572422647112113292928045898464104403614326254517495518022370547461153742357253276036837231669357256582627624949664440913131851214353965873758340821959713776022120904870497831731744559028228565126018168395818210141758833020111166088889601992091835944696901350102378194099020103064618406984186595730031940046787834929241539884210071723592415456122543097565876553104083013314061991243312821064295959589855723528700203059846179941696596674721434893890117056929109402581027312003095173541094505435738903401092026630475108966059718129833684743634548670224307008900882999550672432865969104500410817456968696255386374278463569141785193852045345767082976717856731998382517907045903928303468634144352944850608362155682548398698671413989692462140656776249904927130132584649879839934774215843065032217555381909502321537419557424366282626427568980545873531449094313315274131960969903204993400452323846197182834760324993078850674139402627097491569947758185278715151214900991433 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM2PrefixRat_128 :
    omegaPrimeCenterJetM2PrefixRat 128 =
      (-4247069407304432591279693141343298168576252365301102537644405281293507310944561257474765316252499504164254914617810168388109466994130365565027774902512414592437501339656665373615441294719269793011223355544006658211466730204757619638741163046676929338714355846643636450437377041461178420050500764509054800381164292979820640570829987581029421022921023416389069138757527119945646800355948816366723984167134590911885087036242672712130148885460400807615194979288330592856318093014316575014635361384507428528954747508555649404427781789020421863556330933135356846618983082599705574345663725118855700485435501201977491567664095467507427040404170077736804657983822984888791646667851849794283723984790993939752741204629367449001103267379276684401290928950205281782490862823128846827652947685865736594466956486893839019711293297730996453174602049455463626022029685473503510219753313917544935306225438273928426049666244837144372182468472407043336656368226588795282688702893778601044745303623915899174811032519825965797915421409487096065692140810822415304100323223882231445120262224264375030897938331564890749161161031826132373906326643449811661375268561597162620518406019720493567198247663818893675501884894943304897643673297977974642562010370459520401043410477293424747422392784604771801346809674882250252880781568639475725709326853470006357492992406518103647120009674453517900122806977781110277229788082430993872175528822722799486873207122799282504951080219704906839210966943312901709058123372693662582848605483411654002512883508231492669755623299089575806450498425483357348831779518562363942420808078289429116598741383791290804203346019999589411542052555169671407483705661645855465207229994794630795030636859552084253930606009024677100955661304216899335633259656851372574153631637191937446775838519406914659240062644194311289195026618424376578284197357130997363810480337173650933903835100438295830932036854935288164865456006024803552572441641619492945298086884436906907352052897592628050539833331546120255741381241859851675493254144080131134665703419447021093099524723962588425232437687370812448771063318340763585804710439072342526351413590791357796612928334598584999040425245537825913257160406050320848226618162823600155456964175415091645631780334467611561222003320998567902276607878246900391239365700903824331818038056203382013433524252901454223050024023813279775675870866359137480335961058171072225488433932411025460923971323725168165869831420685387138759172665857769335364924578660017563701510147807345782009154058404820760642794299435044295853232751816167699015127448763107015522211803036555703121666773062763911899481910164279088459497067569519376757727108477755337079932401036947819815990436836085403489319234211674081588169267844722112060176517438720202957008094537424560124518593027316549095233686419081505700971654605099865417026360593364296417882775651934208000000 /
        116212592196151739366898603757872651218463465047554099606703432235713142936859647476679501358315994172888106149389703469771876662326836962676310359173761989264266972831833040641088068890511191366263907079968916903932240545805273746244518597252539259269839999524745929203922569857099303760724415230117581133084447926289398851219132600601654028228034539867327829111502158341321830139526027998821854570661138886623983228890955452307612879222726638966375284315229889907491647627855001760886389988303540013158231928396118964742957893591008666563941648554389624856531622096506091759002664577892056849850119542645875393787769373062219488942604936686110313619678505614372312184262528444719127703638892418792793869590750810265774128817517994871986708884274411470540279588345988078582170060066350271903137355615327405004778866629569026694409971341609678542300958678125823820127873826318608393503948896830247234062937527346042083632123091170984800828316975095523317304371132013451546366668661388715993869658861145425562910132028705698919140701236111121547759301612407421122730569822473213987043794421772643865333683421937013638893541476905941318170931124125180318774891480418907374931526103147229206694180938634022738393790400111782161221832592237484866473190134216917585144128322413911331629330183306018536725393047288722938946259986467410040536507976175710431651499749711462770744780515440808730736686537863254406637031026773935771828814732801892794494647306049870305984367801035527131077852435857283727202740983367860602028000868702361840896477646672273879544566563572475374044970864336536700773452238831192979384898209621363544368817191296875121383492154341508249165784078831472638340022333659652564110398230954754412498650377255219870905244692375346603952717520549240551276418286715969148028939786385873908582246176495913863740857913231255909026891960602111495838041208080673580406391019204731127885256654247550794334973819699081927357832389066387932671806441940506219626816624437512345459597559845246186904567596432512072265268966072982519897769790349439233783611319977267167935160913244136419741216353380924319926586692447024327914371971986637923355151197467785722812629878404546297531851789201301576417727570103456418137158795343769628023148210705731150130265020903240361689632472830011912069206060808976481025040423796398548422156709564377389405762521490501918481164601632672377236029635679667260391778492471225960854089466699625438132474848242835740411772785757089112092322148457727603255005834883467289208585342209133270932559207234822723873098039543581810257650371901444345866802057580517025921006992131599573570628815182493189487690432854500831263243669601982088450263849725736698086242037515926720770309832800820284350102885646624803221548659935233917622144587261410021333487346429623818282434365745584863849206672121381484883031672077302111349970863051708192917 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM3PrefixRat_128 :
    omegaPrimeCenterJetM3PrefixRat 128 =
      (-1714726468018808348852003720891900997542495749090222638258996931155243824966727769966934143023083639777217566821477660970340899388546013714698391794988603968512404531543862738254101312974707908576102580501050978693747857809884824222900221632143404385496977739486398555688910155698714390763399836076141092596231843892482011585804494913481107544302240493703460854831651364626188530343967987686372761013169811052163240383822250202214505810707667082121508682659757196220155494906114810088443959825954829648671461838078441721591349888093692067583540758891839019858397499309296724683311872729045219606356670408295503152414012283636947611160092168415350659720014189842686727892321111569772448431482847849644452993211424075662689591466619842765044742482480291549840228812091328360871568594273203340623688195747418733335656407940398524920078531534867083250945892630200564921555450230331757447113950640062842811100892481204701163416463542828503181713821452163565341590683892818019972595247594681096630553418928684538296844088027447543397168046649857624235268067355672924651001507709610761903669866252341218694534749270501967730530323354610349470829084457523586728496178505954880324021394230885471109975203932606057956093360852621536801682348777838268067364375220339700141347869972735795103694424043498590976916003775112639798569070806744227471579378559578405127027731455247121216464444226821761294086908202167986289650285420175893684842765655033289326834824749429622571566344314440596649120600380853029763460466803106194051938539125506223869838530656961401101223284325391887607356933605345306533850693559340505791340533801733690260826042616687256343724625444422711660897532281587761897735368663453660080570756127621880628785364115549127110391410608473395842668895224404412519404071202182688287756080720735861847089498218027501944890535416192253822441816911630347532426865067554028693062614161545846045623553188955550340853235435622734504903220380225213923860764871451879483077121338835973683114734670757155971593999316097145857337850679141029968803899194582412152968038871984460908666975869622319554104259115349625310133064184509689138405708182345753633012773112427988287965937033709632017235950686105013676344599431916627416622446122261787678474184134079100015309157341210155738606005099546045720674237345892397489002060009849779613497968939853084077008020830682473322515693372330364344521973211447206390777329811036867031330721902318385628020122656061016381138771165873780252462392555126317238350288402525226748681636144107022589230592275791703343262545096301163539235847915301085019183043885117855090648476366118983166262526539671326266957528054539840317849769660684790753807150340479300489671079963452840300481483566328828192598030209285308810619035497776454077376430905924094408374923675365719731203458604920785536012393976124863661748969721941545195463398730395253869173621474428146400515901531265911687567794282341847239036006984759079332772839015512849784507129537891979762037600915079989133569522518874234472255921132472684148143617036666546195425180451452462525794903972359985158707422823779160750155237317068358582806221293145803177867361409122083215381577084841063712516926484557741909515991214134402968989478822005339370807876779896178761278758834294077541559711334107145408584310928420226292897559124886391841518714496775119817102330169326552594992994482007052865374525978916961554085113313022791309469035512377147040175993960292166204214618668614870584322009717644299980618437009653062687867852793514634950890899696465889330658182355938535280106678747417842896749919699932774400000000 /
        7814592161273737532554892642977825503826430574054633875196057622251505970205594707908111635567800032101060662501148023795074648896155442286317594856279348484246731541456123995676216108911385233616762732268813879621706332786820323216151772618068887697196586254566372081288899563584244375152141139170082229873529736191023409036369169567320812539740369568284767471355211054469451882250203773562021678268291933014470195375348320252400671300443049263252735769758071255831795700012236213420525813217076236251681703330711588583446523979849739583016947567938896580148131747584850245347770755303727621192977565970374285239272188432712014902007631351354516579439571437426518780804754665089905518782124255739336042479844675563218549725338342079981907235718707521691724938873427933718432025475600486154798900027610640060149120905469828373238292781429147129363761130216285235388432497241551451295338173894493449984932673170379302543898054808094020931281683492192732982902321145475293312656569770607261894399303007831492689849245317088753990134669794230277622594494678882728684645963897416106372992404178062792476178913950002237372832088544893943753496499677942660848472622046032450012981566923083622012742750472113640451375933877001158960887942513514571834929098393784179639202794532718288258087937753445096769305444215284951553868996832832672935179900598425039987587363864939178803665978021124724947378745077983025783465160300109433233667306209374785845268476744625616538328035099097714641584514215377517214666114629698339607672403290129695739852163081161846608888621665719999333127846874910302183725763617194103111305246816626725989783744290343980467624404711618576469770968140708118775497180848457733300987170691367522702468730098244466394807791750680027105403512376993644808491700347838783610327502839996200021582698046129476215345095285482887391900852484934877744209400926586496955587146948774865220306535080192033022831159527165813607087833013902706903690648458552561327931475826579267961054644614472226468536146377554026880107230440696968209489438034558200974628140820403021848336319839871926536298434997314849092035146311822972572422999125789493863188656473856506720801701357793224499508884259191904318979523948294115752966879320320570699147917361571928870609044284383938846477058276120494424269209781389077652351920081040942736251263064840853429023113023181760681344390212491532627738883695718976614492130042555886995403500948217767900804173381134804773393962420469106436378609501718431807320729358644393500264206903941825150306063736846892970436581904771067743796996068708018777093963373906348523587825116824615797087127210719406796275201305046779378248426324910682457574943397986787913435346481105165080927106799473487254993714636186392000984975915463117445816639583682231867301895713827071044181578104698731671075696009577302837778349477048227497944090249815396935589152656730263759424389951500441292294935742589393115069466359307384199197439225265179652397929101726796234829817735527087549995769609355140470542060147667682876708697412258371325110114998653209703506686084634495898581235224383565356606146055003526634152830272857151205889634999946041230514098477927040691372919795731832078909321463244271520207224473768102456996248909737614053456713907063646505709447047660967568351285567619221131246332684548532781687368801735262941481473046177380422349335290710287496831698911943223845438366152416868924806065511993956470481157290001734565812586743303380612511573548718210739088974668034393656011507846924961111279637293437129293344856276301600701666518025379057931190714176802205337657 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM4PrefixRat_128 :
    omegaPrimeCenterJetM4PrefixRat 128 =
      (46278027212132553023874654311015483861173566014874893883943582936861482169813087339020068638482769100072666604287909632469829779040267427034435206679071617277583033193524953236892079697034523546563845494243285219200564088796380622247911422849363804375250603392653729760143605958937360922019974049485183793903061140255452202827461016716314510708776576918395007548204258155337306187360157761136069915177636820267847893887449602169944725296246399648057504807541046816612048993160722533493379639829055484465940408586530414289958959162893423443551683820700643127680781484201706935730170738083274786873228995721926452847610092030489124173604764431449076130536155563559766578342998374261087535343122157410191281137790002438370695455921495749383470370606340183631218194330684605908440879079947609965961053093004499542376708412281696612699998245550337406772858584482646682905754736477827240223519541404437827404659000557784777532013993021634049540276541579505447506694263163606789797211351405230112182196285231468378667647962319493701533747537092086557760576268714719514734553071283380553239653418761835888348561366315584165235177895728824463273179662526131176930989566923943162932671467483717319277181387503349832521841886901567086504259217807241447076421837923538413716102391216417693134562831624813291543163151825607658205031190080363023580514423520949695887670251297187711071311404369093615172990515474345030549268363980853953531025524126948010715374813980837044019487179636189654215372102203231742336818764328632329071568015779467021729224251580325805995610465703487937834939259560451550389049420195362844058510140937758469544635699376014115629602114809027042007183692500881781601362438308715283208322273679507568969210598109874037632382024222210383506793979482661115668513036443040042146498165002224338796059034948842917209098531051766477752261842145378632247273049796693140038362081491306986845682732180289751135469129129407370775667145958938164942723534393824869816156943563988715274232506322645574783823845051957997625673835574006565794424465465548899044145167243622993267617988391831168646970398253723771481646388224038326885419892796082740039691977506053901013007998824875440729006954847479568154991995468991181403083508283701938913039274713489110309383898825817497325539482680244192018298232537809163977415518754689059800547133094743658390149989632593450723400327262297860948981859468388937820728394535326984897183442530758891529113594525645590913992032326967294594268035555453626961957529994444158812739379069298895863077353314453029551797622869143836206386790420492898554805299596292348895221786760613732495962483416634178796908249454031285279872830141112310619095163566799896852717429191379229887141689427407681532568661165498661493163151743069208652960419214408805064098470232660348814751690331417737849409745176150415677243867605051441394446683432833055144551639191686886845110440943640497588747684476849975854288303485622999555377911515628747501406215323401803673846598808255279562601559179071285020298840691550559481174694642897987354939727347636176779283152285533575916325610609873611423579085923627334761638847809023181318452709935994135147613136651742004895365264062023051460286626345880595417418290685246590294485379143815082115487009831126398660281491587442553244795176490633726090396899258368686051568160132668235550900355488775759987460061951920836761351848764639370063239077264353590825004869752961019082404051090896049438780838353194032663515022363763043100933955291129739793343652417573089012400322720969480215136177289246802863773496516682474202038505113636946559739357234720747386217380072438973814744854465103900851969593465725431453174362050622024026354044904526685557450452334088758097482070095661382730606901679559093605159656803635569589824204617288567047450611101966451511056284193707880437419973188302462106728392535729229630800174667294635250783021358016529687955965658244932853461214892636010551319752166793092151574005640927295701335487991706912107267170771510799904576140435839281117139273716194439093083585170007262548620622734953288005080154116727388425047503289950787136435382860454036309302186544763636041959389981973976897275258265366182752351333383898275615411600223619869545260791450150721157526723475321763730337164224872230013147742618703497167413248000000000 /
        132325638375027415849940523201109150436541780813354642097403491804306695537822942229256031630397763222966530374975592674540592339893304541191190111284515608987270347228890692278715655427592959226653881196836903515047606019344099121449458104499583751651466132474697776305516869949261926690317615259223036443555756697078282334169717127395524199369106575493311488047344543303674338728355285847532479819356950196062735434953229302990631838592073486487462162571582277848862385558856203789033701279852673025565381753622787930333534316736777232730232636891036206850117478128177859936823032924383901591007791113541864045555044834410042332182891977365519628775392681090836601271473037932348348289688853476192813760549385560251080460583677261808828107286179628840099863026306881204673014393686590183382063301693091968910861790422534405637489773246283847501679351462529225821368858267052540975748182777200371282149634057069469648477517424979471211368235109617409184015198470672670413977696323457782524082645428440824895242215619330444756687916137324341646666439142474243049886742429320628668243253701718871983456400764024277482934483388471652193416168836122709887018651207545794154031740380560627587876441248992332426169355126132638312697967257483987689351273790569309482306692694989918445145412438483246527201191609335278660416847790882976791817476074373565916644600353532342996269909782166667773764931462647799291154243959820145575544050743686537821420927353331697793749520330879907491977016916398715983802024170073500928928427731863722194759111060604372658505017776917964265918543952432446566226829271813703133764569998375659409563240863941749680024106177806849869426783871285509576409656325917831238919295330391314103452275835073204810395533129283572736877567843012321554185163813945562769693926565979941805841546438258586073722265539715653727349885009068464047548354321614212795905950708140160212726619670875316636734285448592706198984414190543530778653233507393817248927795276696666885542345113109247868662752760884483533671723827167590103217927970435305012918528544367126759563395355919020267807802730580982458026988540434906423945587099428520596076179507980620853566068581982837058059034202503880791136547341657587078591497704743915857420089127182826499150248640107049757413445385687040277894668548317636298648975299623405970254995189186409110332169634427408680926417089524269452451498321791797861799411088676464109339352671908279500952552210500345933250321692658160897752591796893101081842541467022812338222495539625805618679531380499068705343200466593168337412593707029826910886094899161227572852451230746419583883045930406207551614468330591689950394335637980524632704441959946091944314502754091865277798830334180403359789952174942535169662186518044981167419834893681368829649620331178736082321423788837839397263315301042532184151060538730396899487133479157023773800765931005966008561519035296213835731021165523248088815148461163184726876904382998896149405694097261511157166851431290644944233794073671402291977634600824113974746502452639115666819462187727292676974809653463888819003250492189589939407430629927985618580595160832428537722147522938557288428243255790997691980754389845292036203753952983362780793395754657941658028005783416451545146931723613253730141353993400402079195226510966852007252262256800616799907393786229767766107702557387291979521404391318899604024706392104241062050824981633367062109786233370874230182649631509434345359635576590679861404504689445307772121035043109189761728532505963705424838561872480350099509165191475834966569133192391188782673570793110562041976649514303862530766055447589091467005585077813448013246113901504700462557801863930953703301904652189844996693072938687927983884487335063134855420309809255044018930831432233626579127281343409805332357539659547984993720989757620224418164735311210682362087113176091398361592711526366099200527374791282671744478952579246758433482185074882404364722430734233619246331673448936121484449112210301725660553820202991356332364331838684252621742455807303353166761344068358764462877785302634333704135466470477027801983340742232585349449003774412449885786515837180580816422677242295919475973144269645457080080820494124390815819547414246984701018875955510655128906049865659024061534505967457077699368182250304556034470035635642973 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM5PrefixRat_128 :
    omegaPrimeCenterJetM5PrefixRat 128 =
      (20219066658382649076457435929918392371803295930493550361148040016122767069612605986668489615210701957284069591754457412575042185416307927546845051323040833207036727431598357056297802191568982868480830564101925653052645679798900110309696216725430383868298665478230600189290684357367170297292420101990095783063932653254494300735278467468290584546880056869937248443484650256702973131773990571669337780624751104950583870949205622290165293532569260837278383706423506368641059463936396037429983346975320221806983753113672246596574066584410135255568345909128561879237956849835682290992138571147241736764004160784445377071272029715225326327281647473152594934584807339534012316226724544198895375443122517417213374845444097206534523941139802632183255848992783266375897424301261152763556461833084665379198992562534459467192930511837073813781732551350561095398734021742473828324577082560994761119463564245831802141863199229649396587821475211291255748743806411114016700904027679323865917959776387475837420179977953577817804550081271162349468188802560499083141937944532729453453154578280499668703588607613158989627815864736335587928886536159676545074226249793837200495417390840247592809744143101781279932225992433652980022934753270963084817002062842336530333701385047079243429379528171602444620134015081189140725057872139825895669224733248030649262844772959965158423813605256626703832275329418801043568983744343476379020451215814638035120794218712625347181866983526753891802268216572833198481324006489124910253339054262062656085686629159905492155918965314728526098690111382798752077031718576188374985452714064991394997132491475267251570908122766174245313282656417803997577800429825589230638530269536920849917033025880543960594923931673231279690822954985945275252588595414524446180696946450042035647922249330549915303148716656809922192501033233937996767234133181677378768010386825024174088010343943744828138685578400719902460433679100612553560265710593011478484102015181522680455502726444788810638230995612419203966299633797048479551628543448525260336884079076221984270564012278089175853140174250041740195941557043298634493989091858228578154542400839661412300361912322017269105887130547541414041293297727751568415867247423894919901963802956654621756941515532266014253562016313581155390311171241447302590545196156108292698213930789949350832539693612518767339818448229171827626650747422284724216841829132328536341969547545229712676402408457938937723838742326301727258145596535772978214157967484609455604056758434887053209112089499016800693380974398493700325255845808991513626410344059858046954072993387207552524653474143986149753766416789319770908018882761310647855604210889135921472653550928857676434646614014764279882118069298058746231607505331099983168552945252059504481585598346652174288062506860347650205329904000493554091334255659567555056851640130356180655268017392970642392176425802705995266164136871071828133004918439686898051510715218007818101113290148506757821374098161105469517277080432652548959006033560594966689714609071626708756120163478633947667087588105582851081392505087078570315738143088819829816452537013415546623877313420644591659038698667097129615490189479622860780050578306592846403467991206203254912947471399549546679949972459504965487380749698331104756398762457931506227924942539431500725629542070146265949305415325333974000110071109540801154100898101851747303472480309064704014920539531780933743388430922286577407058717612621518465877964772951389893362140696121435277918062484889807403103486805621094795971870607816358701301537165148372576155870050204011512201687480403652388419320107039662884246343312514638876324479814197440688236937634821852420123388193327375902489877233921938074890481310977153265943081633101115558469998586110644367111757385630309686871502759332777401638103230015530216213382845723824820689714641409812391115549215209257654056949869327895679972674872527377756974308700297713080736009930250747488524945021092458078790765650678375088999829585916264286840031767588264089914090178905810025621483936318667566602727381413048905999796499550602414013832193307477527400020169070883299769501453889838084551100306888885103227607820647035333488779197855960030381987202016975386888391076549473015470360741782900073323607471404078989107929251396501747899955643736636759032291616331315534336708853601002648195668896387161999402006867769232392767770167433575691465045845800659594921589342008227125966840374627195058252750018808789193408293214180286674765745735665598914734861452345787906820114158889985533764187463633593383300516925436606584556606414566107000426785249940316716010587803545541789983403089082484838382172992715759235279866705173744122064102324269715671323838925770687881313925442996808113179537860087352237205150220283743496656738694431089462730696424277522320153466796572221449538660871450056384664107808437556789267880893996571671201306644512558410339406434472668939201678628313329314755860588063622896424002683068336469260604432625627260245380659380584931132638565891054829913276416000000000 /
        17785613251525839849774578368417584345315005445026726092686292814833973433719939994007082844675584455794448223877216243951132795960368803876639935433494432534558503147669918194568133374696894111392395045792711707774780653986248860918876731641597810050640078590519075880832616904090708688061560223028181552093558091127026425281070561469263745068196361589148438701792569218809893031922867020856790236399216233688027028677857277654732230120812884123814233721328832243540619832662415724161962143374241361119942127955967933433728835188426969107966486068077773757567970283604975325419202740494729602950778365875355303753309341626593449100207551643524868637074691776668162184542220240009753316282087886228708861226545554101550396647920755771501045062033987550692850324138068246827032866314275703795983125572769183012952446344233518633706170288513745277012994925151016759120820964943751150000175893480283704057885735250154289123333864045447375775297470894591150512902522877434289859621355185486492360986380276012264038985025293024089959401093111470091329709357255919096295497946461238658464187615373691689205578068306275911194621876379067692845364797060651313399248948685170258909194488827476040283552554499526257411580255638666766690002016478318816328708170114097679097567698894582380664850834785763952535370095949702158968121422249018610406332718575236780352722999838698007493098227084108229710777409496419647648298388730372918729906707882902796932442854071341904480901758447292051367027298452504341009631592264655917985412435015308415601394039053969989785438818672253077941496570461846705358301935679017511061428296288175558891498241801586273426266044158269503654116260284426894862569180361241664528489825740998701470716794881927075206397712049244724323890059916462642596904739312031869985825555358390461226917665282241669839276990971665667724206710108245564491615925635817360630249777076731243355795235300614261858274078196595238887208750519063024239299180171606574370729011137953082158869769296579337191758442248281819252320443425919479255003413826182829751749155457534971763110402495191863532095293117382471140479453810712583706028972840183096483681935782110776904991699344499410181258088235457263644532647338508900424334898687176571527265954319193948761690134675713021162672784841158022108748364165977541195897785454702103545405625064529003676475664384930474751529400354351673706195383484431854600678592023639186333502566774346519659043976562400901527557372892035502168792562235245591763585451442635120245664891376314577072527252527985174869392574035480493090071694991071397042954565257927435847089746677357496699299938723662196795705320522492656411361599966702036289221889774505453826631943629361246909265626627812140596789864724219179595074102742426155043053296164461185106692891019631153328327659696105556636154436084688369302265468362089735869588938183601955997794582960729663453582866685967802272074522324846152724469848716086570255450236649782285851902483920142283464494374498159144485858303148347946445041566063744311222838107984140559931392063924031089908719061271959968785380555815102940464044350477171005638152377490706352125205691050685725309961354938250507251267164184258839810032066048266669977908080363086369606605418946023394610903035543560751828585701921670039394128803283163314860360007550262784586569708089575263111017570928496528662853164697664386519353176580752073313779909697128896077765801790272478126134066911735011443847452753289958730518384450718658932150435048108053192083025610198323054043900411854782110594533197660968983096917341773202974609020956379879357572517239095271320541360934395261819735414437281035486037142588237926278955895730879213819550126656892604285337356720210934655419647150572623757465709175742314957316871485256725224134844992599548738744004357508159043218265347220017768777634107005995431862588191678471098082438853666664650465752075958155376939378217355573808025938587898257047592477256352771457451005529963073970761035623657962550859764837380196463339740790627576044708809649659405609905628069549898815955013438673367939745936079724247348054145226720065793620671256863067631194769577065224226535271728675392009736333747751484237603505941247675682448857715907397536239698439689900122069094389751566697601376172298025606857311736819401155817662539946055815912050879925862982567546804960463282767796968295835098637771098125337880825847927671487377710403636022993652373470444184035880125004775814176416045333657782410054547314733270672483124632753531091594996784815949647399938366012135127095545076328794292115069067050611027566862558040036363184362525574697523660081228597335651755902520830329024728915975013489806701800887859190495481746306752898248199048387239231084715731233431615702989601887090507364752355570607473003079830578836629785664705329833178864072965851386375529544213182282256215326417722070054495199842492600065388496405756942970012917695228194233961808131126244512371259488193617640714135812840756398666310166340811873209102895481407823679790751973827158953 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM6PrefixRat_128 :
    omegaPrimeCenterJetM6PrefixRat 128 =
      (-43020231575244761406589651473582119558451463955796890460398194294089831966450695746242241049603404215154185067119377093334282937553403889014678358237226796005421894297367844152429519427951810364866536704517863849356920859701091958411387391122466859658688616888012300550681271617537115318774816968199825896759213489292809770512667526898660996690463377892095546320456490410457056984161900290277765005226900985179998390133208593508092336488637566821767319446383918117122727814270891748766544978554491715001929179276781218773369670537603677576634959365674634949117447918971290007982899105050346736043091627699893917694279345533003909494927045938311081073107483562742716163063581620900936588362191833291490084642879282084035787567282888967556306915117749387240942940375467848186272432873663977972380327690381549787766046244274051297582540339069426783157312284542564696387703328068380266439498592980926396051699624086588944934601346997136249716109886176504299958006856918527058059160886208187228240499470717329582334482034350337261406494835571447367201542832137868833161092914046904331966840500387349744686585370606418041092701736994542967460359054408500778181997062800559346124615071770334428979787613640418529686956250786249139857096924107727451424561740147940178118960599445222513106333236017679268967530030073932297201503531976068061383302352699011903313327292629665366361277971095405753050112851438205041272706102023434896233446490007537969901935054287022306295170398642854279070961455926635888231827867690229203536631301710553537557332109365049995642305963409209827960246979110047535605172197452137018794742906131620611944227991289834305570255764671423789317271532903053605613031131517514297662024926340171320383691015766368158101664561519575196096087064993156675227434088438709388421150663874263201396218720969864946836282907097951076162111785117005301958060164520036410033393085300082216196547101555046383381070818649256318709659392079642176858020938963718850231888158469897878712483221488202118293096640308611898529860984073761394810015694601515876299735351230022555628232496092130967213044566711464989517218884067224054160285094202225373895619244326676507207925543323637306912977419624163325881216360596261785085481107498055504651414907929318334747568608809967090320300146778771172918047340023501767967343882071196882113283862371763179619214013163122817903387252123394899745312848061448088536848990684995319216046590668954639877328822566020776945690493064166114931954466392451083957159344493332763575776102549298261574241007492901136312481921983320165127225740025926754393761823927243780980443253066060546685493712034562571269418215627303420163570237343790466576816990745819731367957478059760406491022966418438415098411028577847269750462435864885076505295788425855777829090468361727198992317829245222330389528021949945805482791164295257371337852219958300809819388518425429125032115042937187096965331699717944824571114632551746848657148554574009404881043723562021090135461701874124350422687293139114733925333671671824751016830762099353238802109821755664311569256495189412220497371208449409582185601316031874595323933680203276347125542132276316640420988782768532697600709528379306749123586649775131118343929595154925013121283631275977719404159511470473947751727465011824023570117468409061412955098724657476537133147839165835793375247659602189262609304836503395812121009879728168959857480563680215689607916062379955789133980364408395809961786101085692524782349112804452919541924757399667081030983391266482918831995564501038968509299875275901467507397424778716798843960788750875616129261313660027141203948221070644923623896436256602981840816501240845984564822580163140309760436317078785328728550531362927708002485327996146697773960059427547899724494486587573619735422189358613613327196354725225078414624053994450155328421826019568736665317570678595895924055158594280112637800855394782990941342776765086952662589902626403284702176593543118174106083579173470842542113334957431818008107066852321056268057297315742752773460556185854664252195999580990683607350368883297643061598705868221171209886199228239846440614254630606719053934617297985820164085588401203368733184580016513894642006780614662612371308461278853552113698636731907272351507026234873301230268479244952239145298762528722163526184678949685989463941698137307934651357108267730295650312197891266442767033786302622464442031098734986455097051657992446486707292233360799583463752057936811516519504433113548319518920794596278732088854077100453827456996186431144997423954379092395874793135257497574590958508846376325699800764569328968556325739166100716511272263033045923541537963064944331419472665276292078083524206262083277419794474584569268716460755368782663016924792754130742478873824670609054166126075486480383515582187097965824034819468519224350020737513696014401436598203970269712224224715211709219670124892834147220128592488046498123821246831860292782015543239212371159222047838497233068415274095715913904439752463845001290536679241185293276159300937404019954034710384909872113095884933736900069820887383693184230864585198849827535128477622937085495249023753675016826654443667906292147345374431136764165829681928180339152420997576691949797855678892715041691173971762429236445192073200218723359371152604026458219914325837890403249548870571274128655695579649405291579486212963727091628752067304129101520901373836059709896294990281742694623539067378739662197088288145643822796952387573188306364831405731908967765617277233667649460878359714109116842638542329134389256370688034004293035327641003765208142625541998993525770462456115745758722271425762510547192725076219715408402051254193868660178336372690104528571778404383126282342759347333298359773794721005248581804645416960000000000 /
        17457266438937109628399312469063370601560798062662016657490479359031390761719093015818366228791108488479500492163222840424890268421779370889323913790168991373466732595909640894471921605584373787967247272932415186698746520269826168689478029413238564633742541942411072644656782761538365315494990256539461662034572748907525378203122912908651134854590541479162259215201614137825305606656061044201002863674377234335670786871135701768636158189377718595742264241578982692000062231367942566272072884168233356729177583931007943618208193111008574430510648320481597712028359536499564460626716254475590952396054036420005847783156520201148622965036368758132695157701826670477111553863495266487497916108691072525784348724944035579541359095126498273120541279141551915658575696108607943785811169369462859433507761014334114178158026704612961239080163569669472666286699725284874047099462548737245281969889156680307832685208626101489897759396857331121262564194996929353996735292601987500045064302604261555041918385964876494236267983786741141638639405252810299823841404694879014324564120605321100870580407608914914040152858817646408953277583802815776481585554520225591828891094362933508461979721802719948799956140804360870941408403835087887416731514754372973570247632218208074919987753047904857413417419921879024352772574634101266708337252527872700646451187437318051622629760447747619571426192209915622306931898096373071107318166287785812529627979685880450397898320720157024217349080509000390104316486607155730787363899221925530434457805855010467232611755235266833206507255958691099246199090479798970169856085579368741336660543485626473560235196790627706893276980124778887328533635028786416861929681497208612770959676884882042038318101983848299583375691614000962873068805606174448778052733889297719098915582631732093417248908900688546717898488039652129510080581249827337596132602348519317891315507327071566430116486028450551865142743515589376317712032359745599928541877047820265446227563007536902873638828496680603019891153371023300994862000608989671265501766935500801810623888721422972261636980814673679928580945042918569094629477298263853259142409109029356441179878321845873455340465405236131182598740027237408406128836634017990535304164938849862284343615329310115478978788577345942518865592756515797530703570594392417427693009573820266704598363757685821255255463327161791111117346052937292948234381364842665928352737638560530005760797363735456613554424186607829753590614964355984041007909575461575659735031862754803298980671126317384831912644437480318271984196955019078860058474595176788834845208176585819454390054612657163125102705831433641156891990591345213997721804116745703828192339121703807754589027647311167150113708893030228103395842878398470351971270945791897916405898641502646766484443370503175496039372512978584828273989012883754326932915920795455601666577788668245857314920631428521132829532195841064365017462914158524986849843498398034629257077654549783051361139594313887123003377027213025225310908082459551465719131889275234430653784159400031978133311280590976650978871517209245576909439227983432364714264727520024404031169647405909615566717595896556358342660362464015318250387645982512469902469883104485745886029281098900402598441230886364343518731786544266066583008550456349577767102504768932074708682119034319483893468934757904431176870463530514699258798929627602613253509300368140374329147769102882988822399613790535357505969331195460540795476377394691138185870270401125514045186822097744416053096105533052823181471682633376283477135890480624798670002489000573596888233529929064097680874758570469428117973985820987680900907400823264867890651522333912450801643049020136238577564539544951710556927407834469195376219181118619439764313894217543964568827111321856185376396915764263575559134062078070715822961918406701765273030529765746311464104415121898711383203666806121414189904375291210634821967922368983030659897559228994354343607708527194049881903910234175067933372983567881178408028255008722925749024928340031214454798740820219779716691931723733810680124124742915870893040345076761775154701889580494876194753034590584250181968822830841079368526917794820551506397362155876537749539822163422257999804377017892732022686096710122545606800398955903682153913108609302090928509428647437548631455572695630816441245832965035093883340880014890010175062287404271215122013418666337030873400916235389365033887471652428477070209594738622221604717973833441540036657635192209440145731535380974990768001236351054929359712411449718591793394656181958405101447227879905129581333055953658085702797635070149507001124440200570288377479952236442465455702959020638953104537144501650062214683367558057537396490827865978543259681680277412378914072533379632646823161811308735939594802210602217827118518972328178664010301682683372306686995993672492326514897997608866261049910492477516717402773240938970239221432154145125935295746379782653591354901750279727357424635707666233095030658053911495563468470856916595966435576245680951653531010187167268203372054059372756550110992684579573048093888236034841677026643267167612190821088886606307269548823868553511070574830217582391841859646004663283127749944121489095088548683909569895138815907404801137303374076654619663786453603872823013604590695040454650285145841767490989810259835589015990011957782729028233999146653955024964316606442599546880959728890461789952052444893185565844761498830674905585173752133122877802985731533140864390055286510161183755308259392487144777043669922473057605432606611225915497397200512326474263021125362126621251554126389960649410172963550744172422226454265867823754963569178907804909312569084030804673712796951954280576831252496715241076549046020511094128474483932466598047571769898392513 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM7PrefixRat_128 :
    omegaPrimeCenterJetM7PrefixRat 128 =
      (-197842934012859810054563000535132772411809695857398318050299682210586868780575456558880655084444278344075120834770554639230800129744987727730125605169185425221163741772623920207109982870667096163890262927522554124123078924479571731793546335376059240877701639271433918181760198017717040536778990404799058930894660037363577978030497795462043279712367791320897503872168569638908878196001067581166073656603147020472477599624795095035185772858029487422095544793964602042001825211586474492455460796662495233220090349137435175941731944239014555799792850556163291523684504073299139313104264315444023264475816612526205674207466050981849544308466943496031600867944474860906748589755854416741592402726107828341877496313182866247051526333029879401220653357834136752945083508176567283374450281626310672718750698131974079216408579740839294448935829405846710333495881733492799718526484014141491268943209195781555302531914683912236859506407899370996345687370179547134421192834197587545166290318536339719235782231494835440026303701418633916013833450131591087752383152357363423099907054325833108193092930072539198618856329821942191244936275439316275538148346794584311420840721764648953318601838736369568338344033854706053556033458167099965983623240390290099465719504853876616066234233405832059934764157720331307088190416111949332700459205204455872848069484790094724214826415529768056100763219944890802104672413916463796719392298369424081894650489443271037522221488089951445271979629528594545135417762410814046903124672955536277545554690937236490311531979224311526038632876742529990183895603425602885902911367318444074710132516058474327253884504138186612787933294529572907919763132485523025290984622321088879574351314108455578682966944518784783032766758044791915533757532824467353017957511466273293440746573783758486158185668566210065721151317695957587992473168798549955684940514132613030727433777649526213242112985981196385034783200002806000238601120663996620115794404459120175830633179541700643389727147771148037151098599036169997931207307852390207982245050740935443970507692832335404643610556059729117258541563895191538186071449565470538771144744906579278629838163143600540099704707351258379008881828852748716739349057934779289899002246353500767592641480183790962605258828309729367335018326731972819618317515740894078335981462653661757556168456623363526346861047977728783467208450545881029705654205655169482427696869630192302804392492166863657397254055258978645191539640083294746786827065300709711790261807415663225204047451748141576428862396274106301725000909424918151277514860499645102892994317805353128951767283908740500525185615980655698109137481733752322374654827913036014250555331300981641555241813157608001935913091747345473689383948515718809394499014654947180146388637179811334736942732953414750687772456668183469639493850563229042596865550293172868744125185311751729549529787911404908447072406066478783944795793248834865468100495742881305215027107230032574499703691769622458787103744767944302182927301179802533195213545644933954662262972014669936289594988074258633534284040886930311753715569556278810633072574618359039805689492253872602583117020947518762439282269123814392574961804660750979917810879259341697640207035505106261007477304802491405201228070097572954540619485776729687190461987110587622037516845335009691854798896932560247207523046218035054912526119855872939108491322557985295847499511416140434676141101619524402568664980345315474191679695406283145112056987440977625417878435984867592516191105733393490950230743872356442461787742610594037524205018379417642468267991428185388919765666616560737484293878814004778423824368516958095771527267780347607314333938030992083467496195336988976212505731053630772716861197010429267864688910475139305813788560731380160621201248436434010223063275751394707269562865611322994488962104413038566764257124239269511969433922691524018668823774345212735937819815566073921291145996955079808011783902197004790975192981179446680241172003557330446104534950182281994624693259967522492034356316053672945848203439008717000891073187803318040000577554702204219666927259029664566374660799275568612192880279649181857029805584298008349778548620141508081288006344463785273002407657357088260357427503373230788260968467424391603936636578523784532356930325027064290868639808028178448230919044905081422649827900444117726587665739936725149677668362855107947351975357953490704086947570192460213347526986868953160197088585330519469235432500566176352326004227528540959626833054057593628849187897222272354849742286531119781040979966587727151769393963104749020987738557015588836656257717851749727704677167023668187530556001551914507423996030876621989799832852471411683495118019696719454735740649727378263606868310976940989348482693012208858512023413661442969662197737756865415657359349171226682754752888792818604462658922928829513652678614414354517712951281842467773447255479825129957306984195340157059500850668158970502831373798285461223058334077224520760288394096268375409648407256544191000914255639355061432165624507148448847674641714589068387615909955821748037530136852084632191077140097348832548270785941772738064681623692067986062786564675291411684832972097408785186156890210158780389378037505346007478498683259203509435241923090586736607859676965614202350100821419346702654069434529805527307398860140963454082869046563028647723801879833797198585557980663426962901390445540514282288186967031448863271012562455705478264010714473424059697612662588352278333413690070054073854741434246612327833870701460422118182649304127512781955936712806527602215241618352851547851654137801202820801293938453296732596548917463552522281478983254623270475130279778576736790086527495700795199524193137554838581625125720467750820697514107716829733716660908859482168801494172596695370156571930930623497054363311546957422652351874019871958339100888839195598382230838345632504566814719879991294943215136106599864251728241037203772767807979795809370290015976038922204662628235802123472394683326203234183137617865496566570624872288103770397734185867569891820363240162023592355596173400880594180867914551603986718948684120743067566302512391592432165364655817414037448293402481368197828046236162076317286053680377742743366534708037030203372709425472843299576854616744308929428059252582921646921891116176822637323336581398819414441445498438198988463945225166569182253419323590461616895504532188166053405962696631340112220433793266840520745996412617613530931291750400000000000 /
        40479148777649292745358099350689862059420960662869717635967469870643482952181210904292682969786966712180014241947529709817318995947629064639611055120754478895569796463794390999200370903615435951865062126970937262480255230927703183644554997665920315554140293874681713181970456715404626222866624611273994505716481590706631672814183274650819210582361342038342672528390023502939438376422653665401355594460655774630304214290183125614174595502443179622892193204400232718816441758236145339188276038162791034324021418481542408416186944705140701159527900134023234786734775288367100009885993072635313709013222063183408457356461926279733880631297293065498938223090557347308275898779949910756611552493202383654324180926132592488965893226672201792157402960397816374782136772094248328181689827978726642910595151200007726521296393734805436131913732331640411138574165532172686149245177300176341518325599702574233145002640637187244027723630307324602526076240339776954968368414370150503274171425000218307628360695818498230001955120194190646719812653586386443148415815732601003234900231530788662500344159670921561809570678860440842886001859848829629508167249934465916483937953139402080840401298739930389448530873408567372901922602169292036696876847052623097014006572936561291594740166788961438589955122465528833491874554718074358586625945554831883658893493950744797853711479234104556454815812968980951850895640032005238503642368316767138516248723432971829464122306861395266418566597307431919715037006412763583114888424532182364717342020740800991809002655578729762893723308632971199049486471853825209691803327616344415865893949351552359953544144380724679616092708902606011221561299873288768752933974857204285821090869053648049913532208311965545786739494847517582322952636982034700511212440595743800718525415437230323246573053323196476254277418460019334820380660720789338145100120143930768388417432536810889154695127399158452812216552296368347615814177439230473656268721915904162031961445034778615444641258108331938219782335703983674667063030708604794369366618593995040442676912623455004083757676777819403793958149591152572399928726750177381002570025547315724769105616729805254546701542111984899586567806711349355765365864323590350154531674646724565248501062213332404904786935983916186841714866404950080172561364883072822645719829410859396605982345243547965098642533035895473117490586875284079363923424634154665456876846962502265338913585358409564165599343881677736353669640855841859787407167207155713444061754811706137423601225563711121303478252384695144283310623810684667200388417678813670465123362665193153310050770635474194716808720694862761483002774561369836831471139473343195520467581476497774946144677332148843121476085481360891105002293446937930628237054587071172731715867147176142134420916939442953117191702754266244905151663069122675722467570922809801389251487848040209319824500553088799802332832677459475925904379259106038426298576879249561866698012814910165502203914977815591648058044265702219642591863638916559786989932519399962745926836015323234557709097068334221164318723940823675078555684287516715158570048810455745857111726983543616122102445291156077348072945692740217645776848686530879344973185172934668332886822301938684679990455672008181930153758530813985832077949138143699922306640886595584990014444152411469516645250099103545077320691195520619828829307840792142002569308172314120901779718993301772039946272045065716552040930107406072169047430841757734711094007212763143920003978175344232950630706988418198876103418634009526654878671172372696632844014167451051601784510781113556549028871297538173169705714587647650293298136814504976822090167474721986697486804520876412986274247524321088149792663340204759296504465697865041784027758692877837904058069940509009616095744066117698877218783232033528918213369124781332180546676680866164922150215026942901906049385033941932935200085641505253388689725593639053847939816877605174976704396704243104044343281125751641497063863737102494645614992443844494717482045819338080669306904895359670850088246109185166110030455206420875776690046792616886571196163749634805022345606223833641072103492471790434467675312380234341495873411432013683687777021273158414620671881352580282840968987840424576348738270477331518133756862227433399380050142957961161551082797718142033280246995932134044372722228326315777737472446690393120097041824954681889744030111547774047970814304357519557070428901797216772215605754336332463677100158789681744697219334244053760510967765945923930505940667207591316715224890011179566269287783926968254831816619701725135189999211316740625931505218239318570918291418952018481361972467588053498282600951081704126472276376671651938952320841475022095762727810325181220930143776111562102755969122094735420993692054259504820460971455059129439719600823192387387390005911455307242451070320908276445885180181299520506837716740687649081875922096058660089161143885900416735325743918810392060612918411286846184068688133133548832908289753129480513104536983147755040380806440869112638858043253952841427680271776692173395915573973087258713665708106971607802613577975702386316147048484578494407023488252972527267549142332973999275180619948839477871722519647431834740637242711692392710297821208893534137540340269945091234600882268189714768682444023993937180580005772968811371566070068134657900317632230841720117213931280406639240972684834594252021207474267823645085837519310549367357391721907543853665757824935538334198928680007053899339297197156356177630536262318351417592861541954534706155167023854075093247662979614004301834434826366467402332896417507473890388842027513773488737145517030867189809064600597411794391120870267544289557110794976464642099526849311524401958748386481786108394247064796756575114628825471179561239016558367973218680995248722396903225363805676443445154125916546774881762857547922443168636465219468100585654962322339984424075276589209724741044535342155703995063305119053095117768634396344599713701037427232572327558522387025284859344155693488959496582501938253150462532420282813419353409339244226399950334409070667377586211332163517533167573744475119813276460194924290731541191540523224845786427806793997924280719488205602668926972531805885575881696721660048378492990629865703809379903077048843027122120297699170058775844404274226107821313733288462300961277118415491502703559542126341912826036923545406866350319446623646810972643963414670414993372613700092491440652537899287815468147017910004979737 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM8PrefixRat_128 :
    omegaPrimeCenterJetM8PrefixRat 128 =
      (16967355374132849196938656914173093364093549553116597687346584853057952172755826534643815214725184277231260466984224062404756599318673062647416746932559552711721983675401551217867902725902285370975060828054098161314937072247604684506859009003507483597158312540964267843393631625541404427387713350633803613114127381709139677885129625794279420059391780757706717481401020190008333362608756037768333232931635476773064411508383954576953550755828445291629248259470123559311208950505633557044515625574862233365879417391086370891587018573829052705023014265997291931936863953909207869766081591438742700364554750500176915242843871472874579530750980581442631733157086287234429251617810562250874840700464800259012961587108698959481506694812976377651966493956755501096375633587083754099763503791244834256621729102885251455697581103829023463821125316991457272075542132027567756466665334051477716006985504610899412344028405949259093838977122633509185495527987431931140685018601747998798605983703027843300982192888831533650969614266815356594122518387974430394214987922897199023272230596629526868277689971447016195905071943612603791558317912267522806293699457217684677408316787279715902305495788953869169436760719167911183380061161897281662129436571069286864908315878667862606759890567480407898318874138315698827750100118903278168987357532035272695201562444737758172157807018524408210166657352145664946123024961293065511424652209520359259472248184317774411743430322169291468676420145458765215771939454788305761363699220940405196275411984415867392607821772360888639954203081934145490022897444434798342513105948045723617713831164227684794430461721753489898909298942216503426151683711276618678032469931422638349865076644324125299906289300343943512253796708186600366695741527908709336258444921922811173180436990780914997349490829498761681339393593934064143242129718947552876903466265145645132414486689021425831630523074214764114385411399239104002349067834873671731626304913648536728198573780353467472292255574112164064286574455285274091087454343558282379741665816105246874681826584745661122686658258350168594906789986213446481689561892981297194315599551013834299130020145522177527137332700710623326406475120025683330519654974369499362322580958788105639815958068626562975416176005693082025745705880207285276276978947598853845144220797125972031577454875255865640521444982527270310398060879953968978362226866399218971889148944686044930873657427609162711535427975497029325528739118251301684770861944303680752711805417942431450200563991019077074392017051838561463814316032052517880404323561140543769342165379962213585312978362551366579040449483573323024193987445238338437640378991657611378714136185013568220388142965927975298381697377533500920277930316890312825102188422277728442998716365345361346257536318203633371153623720660172005022760939162193122480963277137295418618967996219807462518460095164496160132100051931290244740395351837357157245168317156333195677325974480991138687812397114595310405766009954981926926578930907328814697210849972760906401246618424331306484850736032882289411837745898074226937746650804602640169693123675627751261599823056556992456763608699873231671865933305880381295064520419135517050477166827057729147048471409484693397327153765375523797554949641005807955063220470598019671995018779239550647958747673912877310322361590958670390994429545349461138012014120840773100801757843470856191115078629679869567567686893474052757957880123005731419733026642190751012006543613667555155451225670132696480080468053377479643733138854088958158576972617597412315247106651071064356018845783202795186969541746721875326252144708908466047843691586003305025534185311154668257890012285034789778967525901206560599354733196051365946432568306730901153828812322541443572843818570103374931098763698809513297378730255982337933920022086531018463277480182219374697415361351507146493431715423605223836674301266126843721643833650705364809385212444190140316472747646253197799532559228928814137744018386896266635574926996633430820432562926389852145709178058450188875887704257660323310820356437758611418285771513062239775759507140849653430718594052423944595639679989630266630175601070062752760052189055338101786109256511782116794947158511298219990605582189446197426074550637725003418899112659776681150956605855547627709754521866964846908110005810698923674163893478455945879000642692458129819841550214362549385304468842836842647205294020674854447213473399500986402232313708637648476739267579571732352400240075180814685563541992710400588018168614411476222991891650932851969234674441774447728249260071438094112628643039596385163102872321201810616488897744610259867954283059313547795407077349360705789856113873896745899127970395299745473546767878502586261174500636278580052422756267898257680828715457499522738625293071936078472531652499522968485165939542702700862637305866188000560490267226027759280105814266832041008625263070133211652558300125611669046831283067750839129493393241828490294452157162737845187912285610421852263202619258411892995864162527463309169410799294093147370565706914949148162641551396908478192457219643496334806354179518125471564938494489494283359203594402491904103053399980105610616848884026025147138318693870053494622850670406125702674660443843125916430421450639492771881266631616319836885724280354746366965610813795806032910742453496220656861237555824815039510715744564867257412714480690843841208190503822971489804531282590652607767917141651876856401439872419337945704441161533807952995294192297416254435063159493238057595753052637966709451634883906600850329137239296678281914838076607746679722561447321890831845129320598833446338795567537052737288865810854568864135007092407804148408308772189479584496156691070343069628119265115724025565075577162802639500617669048185542225668838396413214903658942424879341215437552449558753485023602929705330733909206646484202502837263295276098424297122372190275977981895314292795446306622868798143785846663649293057266921244193353216630771607696770858202078005201672242536208313608743072110967471229148773269727825284725388933500133028874413467282093097460606094086334986182790762404284212248438804159028203581440196468793043518886646455224859058003481497720420690981740017529226941685498102236322435320994869701274249236390045117796634572475454141025411723423842907937249914584510806952782900932845635138137425586419115150406287260776684715610998513373361792016953460751454896396921289088048108871152581207149618953816667858665633309358552240956180770564624919565685458292261640897520217022777693787868822215527694967419425391307878059934933096778750529059987364123571913374935932174762736141278013491797998049568562687814448548804455944445867349925427244467024348247007997368124890384624974446223938525744853750765074021884743784874413956392570902594743222414964278844374830482782127027426840558663081875572593012459094850216138968218595858179570251813248204591769630057581983552038703352979337455439599754566757662747821626546044229219290054072707651567916934223429987953954805645926311128764168830816835936427135826551734297100879260004045959885432742879699284555649013297027878058923774378202221253694741046215960286075489570058403840000000000000 /
        1152223597113980080626883489372668201275304146240665425971868810254495901691303359912645100784033189385030395519127924987990433062794763383249210976490497921926379967441582578297245630394913059866703636854811227694821264996509556544043131108414524058590862315518373717198646482040264558127377800635714568495846593285698597696756865998022009259795726312879213578064183351858705516657511843975034998632051486124439685915329840677517279911777094256690845746492687388029601966896453534592370163565399523705227047981720257584265116395991246033769177948707214747510157025422556789327934070173241941242828860929466677378125954283682106646472077021802582262784952029215654962474122863108954965251533980439235397831138597933084372373632855094167580542956498960441695169242635131164228185234364451943572560079163875735641580362257240935128939604881216113322366839018792131193259810183657870224036928584653245369927923256531038277408880481140131847852595656292578305774193533270089538636289177598787701144211555501321192857262578118151088609206803277487903870568619523722553847725431830356240506873040691262466759643288917574104782801318813525157355463401750868897308553512405177685771435732205400506406268139566338003582645472085484150880931087500763368229036341438998078612048302367011862269970877545790332014267659437671131716099987111613047965051181742789509930603233925293118579742616332832440986933928011405054068605083839781431060432422033751304512725826221628515499101673827093179030933004352394085933123897075482482535614514494295443544465815120509249820839028846446905206160629403514854323311147121050354200103769413793889628305198577249811655579350818036553529280631000082185972938142757227333060752792862599972209148999717898344828659622654307236456998659780323659375885005699094507228625147963311368422078518816998145392029795351883222523708014458821784292287465446662878959033793077331951576125361240088110414808715075246529248881931945058564596197053335735780346767619939799585672138809100135921279815497007651919321011265426479913621880393579526540103674865291670130827528970639568919290322233303116838622521706482479641807002473613202937540414900607174921933954748234592973088724688314499226757013902887583280597162800517476535482293730056264939489570560298733323653526819589117706949062217053321436343984148668366618500075678332894246109515124904860989112208929690549369241233679354990126930569996407727527561086669506340726512153487635469244611555087616300093537874889021165508026629283312254388081732841366387472830695115339102490981086191151170300744698075673606270055911668688800637988694850979399177752277510196550304070027535165902010857343134007079273797600875699144273399977369340771651783501761076430508360958376220941999077041036606576200932429835897346193233709995664263044400942970554099687841943343886771635400120718694541292875548968665484110446313963572348340907072360343773089802282649198810291684497478192454754302750093932281964583426189839593791460291652396202122131003834000207763274770225603704777898868903596291635389045916030125917871463822471201139963956008195614875076304992652810379265518977274846098909244824028290377065914476917258479669252291149888753909622756269113623026946471229356627657192612263168393555278950854464279321514482939936110895929322775574599406882354244496822617122388564491450709271571011516594958803610090802672412020959728360605586613876194242832240920429394806556649824229647282592488829657608916003495942364601548371760336167714201778259006282411254905179293314525505928102862390011339384954335742878536738775762343678661837575916940852983616511164034040130014192077928297647415960482028094680554192703455835182640816520294504425622880810504879621049789364071305242935240637782788948049087254909168379720673933749733293666191237775207938159871393902488453362931865744900168572033118913687750418216581260982362207214611141367021565645766649582873385690284369996436965972154923913686122170663257121250081412827762401563069543064241419446080270821592232234865670267517712960765300032938878739567207313989065527519426332792827928818462392022380580227677249567873965875947555369252415842410554948891097276133404224541203938311858570287471317492325422628864657150407913675573391550620516491676782319703468963893224150563522589709469598123853724699133056761080770333215257791950607226553158195914404027364192156289372127776757628590980184186108125271730943357011088773353835117239949020303585975104709167047025758393076400032711987986330151491135296401889514365716056302838053416166162224046128432594059835636398755061385350825781852177661957819094852587059205909155828815613492854414180704917025725521462507774207499418758156160902737508351666789740820965543506478616450125114585179369232922447931881549233218073329098104922720307971206486209290722200226316701528026342383361012022504207998018373184890079905887823567169409666588072061543378515527250684593782172203822880560503365744022973734239924454163629946864203025915993199889429113201401432801195111947244100377103469660522383020584130030219924703293249928240735372365626193463809830249998563478217044876068379336825864085056434044691957523401665374672843794231757997614630540194948910710406754438881809878596045967842372557753991715027506042501431976982568785309665737591404781059306941667655252880376119947881833920595701130088765163140383898152282971668631696618748857705565541099812115425216091292113827360175071399317569504529902712462901956606304189341687997272324137364303824686331562018624218670813376153184945911246781933092837938014031245004738164829513714261951401941942779568445008490595373445255279705055133322596520548929343933925882711796956645245421878364433002888341422499650065183556510970783736420823152059972932194183462786004064735191434017718447344650967849236805705020578455871702866521087914736577540846712215166848419681488577787925197981620130891813623317716865663911171428074811350671727054696486222962984423020635584067413169339876093924335174209267688505010153666833760851523667070437879973531830971236773185178593425353952973330247369663903388983978964165365662042835092445655577954566095922623211439445458648014522144433094899286866969681168323264133557858038203175020363159669377215339838107929817332452204812851528946817217698229382915444678897087119428923770844288515079779729444245747588386413640941792918072465589088366574921931875943974116336251603201438163823444489258792750273835218566842795184430617853951028656841701006603072136823959542651076064780989749573601801006368644134328095618814973838169643449790837050836043494935111034436956208749099355047898073352827080502596745169543774668273718679815699372572033174978917067324078719983559399839063565448792415151108613120011792411986925192410520396529928026075878660784272301076527645816087007935561182928103916865007363323666022329657679214741021601922820841728992715033131790070399446433829789756438699084072613412663620960357419101506249687598768609426574558497702499079275978201179307183725238422995076906262696612168185844428712968901123954211286450862076988628050479878534784609605224298158281366084097102810436295191558177986633957266833593431804650094893988344333 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM9PrefixRat_128 :
    omegaPrimeCenterJetM9PrefixRat 128 =
      (1632118766906986758634399081415515594289600119472883699051762461079683733488395291487377996138214995414060577737274808079219157213821004838611302277009912517930388515108275099985796489746156326458508147401519447978014211868271020281991917401462830685439657295943320753329425274754699522918808826383929809598393350128728874893773722750675973649206249864985877887652706352766738396692362749027456680441964963086498966423599760898772225646676588445963597630766419689808556036199111697788064017927823059251095596539850005807213621958624753445752596965733190610434686436356012400269051783197238113745651975655363265730111056321943187912338860968739202308796956944760617257828984444358349024656748694209749562093932850768160643337832098617095806002298315505038598300724164012674357033127517274231176316204920553288662402146764510548251172697658550275703888613526619397677041246659695412284774165618866898485047960671498768559846207643725636425111377470563506541114438965548980439811953864978101170598480329816407059899822443814072156477131331895370031948267024322183849232756855614593921068994912264181988548532737910170178472071599587427864054603858028252752721562431219145077092839979502706318048653845201463073914368927871724504523822279527604023831989111957540964473522553800322801576555629859094326266385928781754175873005231599588802803953268150951515915231819238241089122005984225731386811296400953900454543727155825554256088276964545247788898397673731980072017416832023621828103760289089692627455346006832601541942412167774002614022009339197952162814871030200000798231005719411106128781691683986062256135836289032954345152578265957190766352877721492851977679450583076726405208677781063444248750002772571523416921612507251971299476094304538123750534728479816373721178305875446921765801100636400066998006576329408988907475217305201564856767974094501357751841611609074285592920734099091269898984608940223533891062828434150692237119136214911387326849503446705875865838026968664827102965121467438249407250802468402721636922489747168268612615198381512420908025069789360452924181749906080918937171371015370391259807776750215682478175080660162662998864936754900262170622574884821345135060584026524848496272336234955935396644935916722187390072071785489773049436181240928602818063983192698719120597439752471001897259839711958717895288905518987142415700293066109120823076547221247704024252218154534621736121484350583962341015528821465999594306493855277170852162891421171470170423197369037874342485251591166616324529458444565540022652158786085670234033094234390767550657922699611970790530265971674021304160829299311003008357695624317806544001277450202077878581825450799703061688368599907708221433713746260883135224258324339955660167201564862044036211928232938885204497171572960441286816807188248393437536832077229987375531594104263571074146211178681804188805958961898768997367538213356665296967964134603304132559483396837303192170877400799955888566811334616165407714651939209391674411820739078537704388461699047481680971752997566556404534762936049667866921865453762514682879167104939259684580516473268218862322336240361598004303327957790750114664080641864182498677624165049538352987421414699844610579567049432276775053418353069372751159383500413422520219288092068674440064919395279574577574231841035854047390579993131229924137782441050607273275675137428380470013382828232144404070952448287931719019923041524997886357904646203975571178708301169570915620037959057172542197764058081669673246884911365911320920211324207924978844917823989702424677807846082599041095528225159914897424785056556367830871470868820401389539312945475946707482468385036831271729913883095095265653051341511014306050060661323471473656662843985513238104687457434960647508565055754730428975069568969074782724926262846657089541777521629484235200943289214487300508044941779441526394603432305893897511026011021612935501153966094589794170479382278489154806469344501342964682311911430457508039199118778773682628669949110535487587277607175968007767474384766046389149277185703759891627132609045498468410078683398686759964602689918614354454479517145415259899464175712402382289797162662423461525373846819599135887949446783755465979838748693430547761727011871930760112876699657652623768462525508715426298680638825612528463571750876537984350761718469614251229339457348638837302033943169895191608647119127483799829842671914869457925106439575785284777932625991935182476549826535585630070129614192726563858805481481604231253245352789013840490792646155300001784651001650453741615864506273313617661451116650247046677676234826971065648981683753492364628640492594131254059529554255814158613345039918711767168296805930571496689722348887929053222841425676963046593948660641184564079118780348606141859064061502381008749283787468639926700496243553952850942423311279570437053723695547076514525657816745431786162391260544426479023838708913763172609059718644269372849213758955871731779396905299600350678706153114815679692548080729235006142607747558684519945366698497998463407778344643908148164827589714363933561074732333781121987835157738768222659581593334583476148137277142190259230397655729966025059789801143284535049666668215926560278507810219857288411724589504804010624935212592353933637759850548417843816603422966510604990738797361877353927056461406668343049936816909328701847104971631427286218216998217755960636366654340920458815022416722704620977503955563070943121794918295987673578630622992121469298947891760630045687649348758497924792309246793128750691654673924324473350351911262139621280549871339309138013693716064514989124299079691613571342180280188422240259915011842749585575873560892423380603773637701006120590581326909591239227420822583348397517501783048199780510940352832696305665003795404537989994985869936170184098086717085983005696602609834533444674415324868230830511524514983164342211429800302747686645241859169832647901388711949163346534238661740688892718921450963173268837701011703331216709507136692435086954880153328051338891165435417330788405187411714782579227803685325128656072081040686748721232130081612219281844872399748129430396836221070167937172957464277579333333133509683023180552786720174411646520215372993442250243227555943542727048967119921070438232937993513782137001931014888586752215040761899563360280452278894721416058063117233932731141485273170177529555266977224351472110071791919847995171668940101190639403192925341684052215983160620720153202782408423616644722684951936692434814930753145006977080063681211434608500408358296065735015355182430657313979721792421400836497282090513434207854363900436367360251659713275288893425068636738887084981389532215713698964944596318954051802547538544077398359478777772958245545390985334806448004240306854126983233652594401173908994446532081829722241039119559155162662023656959390928432212668792207711004731819307822487532200326586486744094990298848212466572474552184772600589700180579449500295271351277829141838628307351159355953559309072536448116107595253662056272423968377059022844480469852035413681824697111189738167225413160045103826819033922694443476968374786237524819960006865529826697232660378039180785599668327619386289256629358947767887619269002676699277089850467799806702387522503247251542510247851006418676453235696606695925490594804407296128212645899427157598739814027878825763146973438271225976803669283814375496837044581290633661511760051749308803357118973880735893299134230045610240311804526345111264658701091486969609763165203309149667038312347348956723738318277923381053909000360198947488806334405259351344070429471644682479513716315380309413932299625006756903115406295044773247061224742519834337330337225701220603493047283731721890189903846741987703477704420101255816679893241155386933300584517323667904002355510402397708725513598083190050256172940394887898018868829550749756154705793762486261172702577659380533843079583042284797824553645310455873705004236800000000000000 /
        92128478371275329930486872515685804756052416263063818806328188710479396212425563888695697036157620785186476520459189604932568430363977658362198062567496354481285096048926999048146861444712722791447265103455115821117773098997199449863642547224466949441078359795302172908249104855750600630044923275012271588442278851789602049586874661071025724229947346645196507451376083792017654574587508081282505005389768309664192165854986400613618755498831679766585828699691920182621445345522833270341939703208555165176010393687816268553585172057791592534186836484522022165759563867075645465755512500956764045489813190120551816563237821069720284250709660446065876771572095917243909136560028876275830979017185271093639878209174649585478182400664001539342157138269654888571854014793255497229761753068356043466895846454177292712170656251257058366844564519328755534023609906815332199936859817731615390435887954747283329273532994805987849939574879127363202744171397622754195580150636875115367312984752008940183030452495055661207102806790436886121993423747564322270456422667614167980924802743259877121908395465484307285008256980973865988229937744680468060781922794715898757830448173468439959467854631733360932267802419996210505350636129146198636120165748159161232067782065462932766101364842933443807075191345392151033613246254674769226224709482018530518738653059689441228211951756164078783215462220972892305406156993053439604513089925419459710179120957726792192577389731957175761184228130563819027312238561651863970751037508800875108108367370662256897791066258338221401574709917796092763880208558796228216744397049371083495581076756272048615685129092837402571793652482380496019807061651490867507463280821661372640564402616026174727452540184543323158160869785038920097466024652614573888818826498640820027690337345788605347896244730017154593704696262029596400028087413505144752916947567603058954948256401383275422439566534123760294964677787682393268495651594011018370111199407037806803484987115380311628402577334265582458651868186345364483200599863378699368876571147183252956955784650644498176502804120979135846819797844047735861678499337474865968259363326757960638616575159208502866074750695138264402473118821167979988276084365392488390965725355320953638208676185795214334895530165244999268567486560874669158921503097331024293156287094031123430533614565284309297408038412510343384934294086858325545116227418044169090588859456326353267643724459290657398962730161195849350787571884850027092650915208310730341035247139846689320652653026064994161654088088581091674999234306972370723496807980216686529264804679718225112538636729554823657475618476944512249561450992473517630324236454856339605412893132972049695379424652572003935567256110352783847786113810763166042045228410927938731833126181914230343850359033703867695016735414278483495558169637839561950032084059549670650257587634298420849152308140340208229870553362733226675122296950350529494320560134487885302856662466959801811310116865156857681148841657257077455815685653592265421605435696258079963007452601041105038414657232917537615436346266711197313552141941038529238754305377951579900850788257623525623714948892841424308764369224291055709600939511274985414614652331555291209441797814183226364205232493261361433790173747358770959925633572477723012925639390495045893632396405288585102878715242391581495192246078884758144575709377161467694795777026313046177914108012126087780741265383293959116868167772978046991729818953146363946137533721530093363249288985568813815905296211447726948069883042649593364783189375381543789330198612407928727183670726578853643432810435781717467377031596707702365299590830052740438818900069876943985062789400830465344044751936666042884947820820197549525344872825616865906676244487851539758169733190204136604520402003972115615407464374893084511623958223551430702085908459817222576097701003088662949190984411412556925082855223559950166590621113911335109623525611714333572728375868931544801088611206372545969835786536274711647307311606841200425978557631783112694185106880000609651149452643312769684594353096380681373631663560297965219253368287209200760775319263518646481328925094553580142303436597443116286265363553871612280516863479586243233361124027465568577807635969409180804300489955721807830955934989072581936229022349991523171581054354283521516368328796312047234919699575221774501029496785609655466535573900811686169760972151197996720656802772655488912523187641831556354618208659758479044073583949132947231547151520511193702950107363062846903282136304524462135705307318364912566916920160030794791119765751308209539408740355104194030895458970287864541010224973458385743101694817665905604168831599040736207006480196173390145599357300097840479612819230971512148028841833608283471629306685938139862512335773593048429738942984398718064905159117068030773366450146528464874974091399438130276655196150552510284789271509429325137434043072949833100974291545909499167378435754906391731585170204473690477077933992998112252664729609337537207125385090739356523114926230037960039215206255218500486713082857988654609310651430209925906622698056218158015101641937752195231918647492023097117817756734740071863365822329630085449077845395509229745410557510082785148999732803546477631107592080640731244906469565915692838947940407110053425088526569088676789073046543654948829210414360840033342572396129413960820031648006921036157518640457563819083079133573573190100995600277557991060598534246151695254742545009937242042647287682269737870873076227111576709143076244309030335641356658212225468333455628267139173466293593068546271542587061006786120342049487227209329037365218205365257333602303894411471661687816816470923446760427542991918999930497012071520292130318251138656953942500342840826508048854510193635410196203011212419886859337015329009491464506434885578751729312503146539037691863146177227663899728522446367027969433440792783669300732082361331652536951447481618095454990897565571638393295836862707940319512955633222568550070806139600389781680598037993579261698839464834308695299386827206009098924791929392205949352191674409582506179846670027531504158492968884230042247016468731868214532414746335858782858906592968436886768711306655509274466184330441437701880096847961618194100882950421765386867556094420705916324651517738380265347439736708843307445098951151318493946921550362371533748213299505751270739101270222734247145400668031034235966299825636181427017863691562788065881281971801050209072127476967023945505220706047097065608552222497170917810673661101405020615457447791175608808192512733895868153477453204334495479843078068662467742383131473965336229819731633909216195495506241523976937411081437070766681036499620774111453489388461995906210759398080209135448067947809896096706807935368438085663206081749121560491686086975685558410062317202376192976665010745113546323892306741960438946031179604931961170373477477357899819378206823975593820563695833637678555770168089146637803614535770163193463986833859956087573833873137911012151693059011960406609194195639065369545185522280560230445962820385802960502162147512367008934651429381723548625995551322963049739457058929486258168123936694950768535133976530071889501601289584630784670883877134550902710463212469623645052444307990219564102345333214206460732006887626649168365062461407124347804493306553370945526944530163472870150230930772252516772810765812919014604700099521774371020555500698916559356697674877713247036113019113155296610803060825672404281646199850307627141058294941662532175377581001337852571802295324802037895951034816603950282909489395004944732071372075856432174750949184744939158165361903793292367145501891968350645386592694909227223890537868908060229337835065048119243411301277820083775382534454923463169740696147727264340486103645424516326682457097477817994512507798720484252432317183440913537488286031978022218198182377811687694842471741011577913130869567212773047284543832315273 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM10PrefixRat_128 :
    omegaPrimeCenterJetM10PrefixRat 128 =
      (-7143556669041368687843261047669291397081642164293163118777503128263689545484021990724256383737462844692916261269850821150411588862090809770721659129516366553656136131618021589092528066205745995638500691690124434101486476613410315604715961336920984639458766612075805636683432615768728016832067671945398020271547176432049897182150447110072020127709811193027106684998095137084776652204955437158115306143333826000588378910027764089662018350500158030468027246077363135968615706012833566534161184800089685495005233886396430362032519394185013383123253149827624060917309337453081097744351018945934447547914775651681190445742981246833457443483061855561144914877896686151079064466789306792878884257560015876861514876798806059017195733834735632351556547067734853284266370739388489821713850098831193280815288629474069931096432028868567727695573214582660006512296600502479218544348745521509578842633455228661453355033227074032971504233455144667229245861672839227582752113279522476761101379427017555902351069337198840303662954197193925758119547508211972022898837566289775201970069230772311742448401941808445298409706537554762936092937197000781089994263110765316313058536529784108262751937989524543493914548974506279093033249478203506174892566159766523511661127507845540483011250385951155292212202685568602326595911028549903717586943926879220297806079659772202410571616060310034410107857118552332062383399010692604853705476244724690954661267778765672057762491349347281890773271794385923692491145436826144054348523411590488570434391336377743922659438562217347280331564189388878836004371996280401083907279689283068109776276837822313539643996562462276852642967427049709627303804667614154549772716211842948816283396171001396187764307436115751358663232542558186461334367537505090906197307206037818607099134314990508564299756281616909394577587600537372267877117191905318456464040248341774047938735623488030031164572745875929682827875967805330856242855141691141740483795439411730451558748613338080020705648608357504458867683054951559785923881530429343404319709989269742077362483108108258171155420344558013482631820203291144056784907205450342500369161628264112356592873299810421504093238007211479076597220555093498364614039012217619266762559304064988243769875305895082210532859715050418843777535226600671632228273044479621965312489578067031121632648406580681270756713753596206531267556958528286968224549891054359452227944927788772665948164029464286541266233711325710772695151311781460242766638042252115507113134527593442424174832670906491807558054613965543616842933140274207804407488512254729906377365691410235976512858877033100390123288507881147766852439114451430317609284223663951989647259458792725429230551713535265148082038336626641718730747383007500386216899089264239231501091002401213350548795269579491079818904493033501414838268790343153241067737504300434344018875876648371831188412203255769037916809339031747577870327971659961952094030547116640135549960935310491678522495901964541168588161840562184020298888873641131899426729524430962316415966608252451770242075447889568048049154689108520905895956033855379556482481395006129090680639558163028428554832383210488519641691681128308495002169481655557536049203981963666983833217978132817061141270536724907661840403215045557143829567610902323708507611201484244598307957784943186349802425368231196819344131268916388182111561597138574264740637142860964811139756426285197256793016416304344980234243678108442023320998809010221221468034663857699829673624006272184234385776248318217361644641304338013125494030953640433931230396268463738257037079933321105063308404172561901764197419225297201233966785718537596504426739205190292736029185162865464284911885235374225591501323675906474321433922816083257818120545818912823933486754405081940533634364757644467283574265630751618445849558672199422577324261036770016197193631016712048769723704099002327999211839268789760885293394612415114781408836950562869406994230447393229396480497867056875304431485875816462373492292798087210857716133234733695417102599934161088042355099784689091195948722576591979512557766125892534758457228440284246282506858519691914908730436068349702284229177168727687534725641078542162370645471798145078192925920944436885951784277284796766417509417232372967921949201465800533934281529265702592037429598570867450420972961674667867210945165600207079232874180272571178207261532035083144593335823722854586352406617722086896592892391049254659755544624804993555405949715760300638154047418506017925300420681307514303232756654506365988787629677895682224673295907377006909184610570478489634499467712853604289011716912995583467539912040490378183280331569449503831406427762794270604248361753259344928312244717505670610025325432326880220257240837095407314302952947916031554758130935956977081794928955112394401437850114376681024883670764204503122048092354027853741750379145384771196052085354540591007630794830082674136968425688062370206047138146299326274566574665852124130893212173630834312185798742287058165851950795296367383698530455775435529361087918643837963059380554743043063506309410179927936740960003418435566096232551063443102961071550482371519321883443774279806180038993839080525940425616438636063006637949748146767833818079552684550949015578260102680097898170549180665193623395048482961969122494532450939508308306049829810740804004790756058926885393603118568729850726473423576406155594895203292062426571679667246431259792370132882010234042736171990842975117510231187321068789530952495834663059304960580951046571639811044863838387492336664267854589744254919731378083057249229987827697257008731055644666426859983956019871334190250727475978576181743248351312235915275696849101156499234006530458026474685141341270030201500033898044195004626436367542427242791661445479414162855470915823361623442177669888538480948266141995725227813759107082984898727059824211932684945268549585334394722090657131377804200446930057568255502223465812943843299032998674687628465524152709187474503207950049523347249442575285610943462227885143684287954010263396365761339255707219833931493653825709188602908067868332942164280073200610803796282193851076096423436618172638107484296967324632227838242982520269876590100953215468345272414424235173538890794898649846162875795100031612660689132788844316033712053202427340591119640583866685736700694107051094063982338059475463685888847684565545117835817514354674146390790179536941719844836882921398440440997088088101083583259663791892078702897990882861280436157592213663037944209905227204096363888045161462533615736179207914078048519196912773917699811631408002214116080538387361557520459694284888838196961625845702994592749359753721536806010065609899571437428033227555878942746674011453805689543954060728636151617439613577719924815006621672983046856411954939262358111365147494511138725308935907483480090890600265101572553791212809477321761177756236707490080348699949953805423469229141983699146759685652367963723788201663148854133010208465301114590810678870125705880680662822732649784236358469032690927538142722409513227000082873645016897879589093449242105192787478711099152266438243245890442068058173392048810815141386420753240343996055479424228570584583713449328356915890381446713811784356320019734871398751604038246795031193331914212734254525856887701194512101829361257724512483127149168044326865510378362608295932817541999914663359421879394146357406081208980584709421849561206981064445310640350141324377517589047196010654127401592240005397819958258298064680742849545733827248623531757479078805043000504130442081403291810661881726660415012545644176984437072000604791559256255953677167115088381850340820007910000950568815591849586138254712656113414932422020159851447434449710767990989178509262318826953026339933059047900018987810790875783767889700057797809820153430461203921419882180428933052875417689399300582445182571097138795970757964976613199324399449658111722169414151410269126003483346642252450332362874329449660833650656430516187711812265072376559421375920719186074786594740321304895331002827313639963329459404491383746061056405049288535822173801307150193540047984358821621685167659690038834842516616428030383852472919317512414405728726661728275780916403377387843628758388603206021772927299624083584206368028690556716816001668920574642382405001842950020665256682550495004647779206381586447703873908927757638130468147027549356561527946169432837522923226419334548591496748987901760804542382598343847898557330672315528613229294945024147621182369123016250582650811397147303916172111292464466334238705506759716845720566347210973784909940375316255058916521662154579331136274236558911581918016307200000000000000 /
        90427660311529043113492597471529849370469595474124458657371280590346741571815332457269091122705899267545885740647526843662453086720794860543953256474335025165854834059521060340053097202181255052418494235123656538640158870739634645489158515106600529565613545600147048810772168379165347692085553989490292690140110464737525680890442863964460391906846998213391418190495889409656858789777466297480102121048276629954422304643774929469336510050781029857558484274121193910825770288658232991949412428371716191036634631825189088597230915051149291588627590622525144876744727829889511498548353930749292488894224164817816590273162200940119133135470772409667972038629415885506344548092598812958661233468429315949381534806020879374438190470379086804808437700471761520017695175975175872194980499542055225563132039779549917266061118385123192416019236331458620214849440739108289113254238956005483149974327729822793163399147764170351998295422299771104416665983632447355577309688240229307458166629725443865835253094458530584530896307125440516548140592754765884956592868634274032364531178046430171868309083512869147090155951083618688507237073856613057146552631373568104282451507847536751923699696037027957173235659322386467472434200849982055193242742817901597472111353679390931649910867872896695323542782769744969523140047166380711278259442869394086863621362383296833243162702572073281694507859251879339465607167511287363779715941105646311082417924582557368989691176957782128918614530010812275729623143523920202421790903252152628066954807284361404437031842262755121153043448612695489491791263286682166521506154586552323906870684797817206068465644703614250037092271411776306017580907435965879521907628448496706102377297539582952252036075122667580007836791739330528275740314821797711453340575522233250035625460683526134962151580680963529861959841856403478126247038829181934225230276481741589575093207593449567548428042345677256834318659495633218711571713055556220725737622740010417243028620358383746115588640029411354663173613179724216855248310200990105954810278441800541333072775919979751099477488123655506836108102097463142179762168328717433027670414979261324026960669396746558065732127084500620346094300343910564820682937899000488291118912833072704443274625659727651428941711103202135309427716668719111673143929961508383731819331328977091395525998379120265422842489943215006858158782956251689419421408560053167795078093358351589047855303682220857403002877669996118224454332535672737292288137512161615018780389685246921398866958690126498454766062289243313969684569899832144122937962241752635521327255151540396876412318326623235788667696013282200327088996076695297485388569092367912333703134285616883438428915761666061875247417107534636928658826137705748548852559026351468397659639943371516113168439008688312778809573067096397693864603066149603443976929102754029214534844891430010682433668801054915528609676118129398321248555147954936454604367937126843880505897175432541881797575706482189821538915669190113913631899097198928927010056800377237419008587778279974919373018797925400343721590908257582180964924296960897651638429478076880985968204354678760423025579884942363254377327477203836372833193317992757456457045806006801795284455963514488300765773172715077805120778011168907810937966711053007361534518403568672503406895216236302505738063645618760605869369052264866165463743927298312052457276013332977087978674044174862604035168259136191428645917585381890351667386403393322578160533580323717978864817223492314243370707098996754144912462554553548041478973310171060692470864844533951579262313361923205089113825756046626696138032748886238919417994770262356981241039498884824277722329617995416597437806702455037614591586357719898569742215044818991244290506531250465740191945898827016308829915947568726109696111325394489096402455935607171217248720582171530177781796272902945649589274974590963843163496485857428736451345697005835939459141587382870335309868477915581271351670780102034165729858822403940997655534734802764126177249803863640174254503564195868866539146385018043099437957119400097892260443591353105334973534606567315070405771810225622812676451589821096475757218352328994078025736757265336517651559467853201882938529942237698495369783811077835274208460866898665450154592796776804606351322800678411914009368280888939993642157829632151735957584323940150648445366499803129032276616498054133595474241365600423247783022142753969921270856327954520789336976090472662023697018689998217589409966799363026131588102684699664864781344124549871175023629969020657284621873462063407740000275561424464977929859584565284593461608213690539134207212084205453363319542789666575371105294036379578324789068219026701377322754827033802543275649229760958796879908258444097177421505876930313503076532086781410898539604483704861472944563668878126023284502270465165790401613023328717001026743178891736530546563530589345737095045056708769582463867096554499409810635245522303391978037016478977258042331053375601094933070661992476755544231824120399119043509483473248444572489336872911936570345349526144936433459134397624375950057335113057206812178639198449946622269362670191277862388975624988423523041233628580697246914434062551581129691655548825665971155856814845077041730882533574080172140594463991461205884250949040753869462327320893816704108122947429513846990783538358015750396933446280872857107403361620251186030201071936603186013725105332157910851927798761100983717020513634538473613910538278139378694381414888143550381094855554854893765643423794188522803994266116207685635618882173989237540032426953558133346065141008312688494776432894897967473658896625111443287713726210363423090739456137785476063629948550117005630873496166834560420998170185139789068209412054599752259280184382074779008823497865585752237013868287015048081532949785243965681828164080682767579785223077040265747805897166260568636261257616438936277368024215719790388379826687156432192633691886867738521854756213160833602861168661577483851288957970897199379336993167884699413075974426361491691238024230181719753238342058148586071776071769261284169101909057098915188160145275082174099459868395569629163563242180793895936715527226635216577237099066380860502461081303726137987172281850024706837211384947828614533213546174675499809911046999382853437543593820829854664162539789148218408916476983462834526969377236021822550641262977485136869340273973757674304665327148684628048178268346648140444422727876262753789912074760073045224021807168270621359383463334016764631638689733038686818617927702837665342825881380381763586166505843771175124609668801464503229335169963168441290359023660077070904378303346841321910942413663917670680372383652408098755718217770276269093958896314786474728028123887617230542934169448630805517936491801661057666526293478422385603102211828131483454119194561253305491513829834252781564047765849973447103076949481934020986265413942749547330752825801228572961524982208465875353644451927050217630512256941374951811915484446721508502685450641057091582314326493006163520029020819509623522212604802020021523881125348510382755896984356514280929658236719200109347499294665215015197709953728479131860992624017436180635551733112152619654491089458174080720904031371234586242402164659626181410135507776417643524857635739664546491906277471812599566389369433503889770099007561924453325062084752290388497585672316364025060268533268782558860511639161457670897316525338762127586392021895418205253054719142750942616259791373435248308926405147747783369730743209822138947050256641223028185883668816481435625994474379270305221399051864626815435592848794693481326216979050334103413709993233277990111488597229498642232718039985989931724745636685860712898819324174384214508709844185907173963705842691693552952534406258393408438841595225335776910605765509466712023697671174464309919210901465259415657121789686095198270547861024897505452808487234528477280221529191783799485627691179547784722317244248236258806420040297842542884216258271887111151846986523835063103888024458126283725032878296686722994017742862856851677297583213627002567586974838479935536753592007330441390761093423687221117364679390039113483869407119367794426064915237742606315769487595786463009104032581809111776463372496846724791232718010520746726949287429222844491454452164937929753592791871702491340897539653115150733243448074510491685410733160363469927238654264522910427002265454262359862913232994808202681760911664079933161416063977544788963179809215563321596254530552305019105557623370692348057507393532920595017738541077293066587331612092489979369508389230889734851105641848753813559352771104010027568641801155233 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM11PrefixRat_128 :
    omegaPrimeCenterJetM11PrefixRat 128 =
      (-283708061469327917633209544271034808409470445502957234534146583076152133558490587407574519741143459878999286712533259740830956421880368243613731116799019814473662319053368049926258879177725158866601804537664146859794282208467736130613222122451838071461703140891666133695456462622656365939646913645580741047429753105377428443178367548685593538924647737701018733425866334239716125795850866766262299503668906496400958311830462043537099495215321235332740602136761989601722413155320007169619675258966533041802492760971638073663637118158204509638038047230062073182469651383495083509331684202478327879226337483639558924510777709599200038649700555489262112462763931991065020178535546031185596165863992255446271019111763706659963331909809154426587227244269023621297869375286392715850576331710015554894333073068109327941975634769510254584317295070646199637224001074855206659911109848648250049037951760112978266937732288949136142012072441625875022482894279901615134071331094647004001913628666522921201367450006034619730126164470692892356248883001218277970415272022189282600450921058393261619857452964229318863396410238436367436834026696223077179671371494580289627356174036520483501532995043243165400485332577537475256749100514979017249901497251378976857830036626912037885047134670989444872576143957890448443010631879054309878747225064636460626714210811203262594795639274086699602392036636223939073311798187716016200409066284096484469774165110782819195827987649658132948216383243967707774387021786324294754006351960530036906302397248712170024649086648127316061062104719471334808913261254022595232450861698079514392322077908540311102298475212949611686603378435566323450608208303917767424871176152373808848953140211998288217114538750281397215287096887171286592238599047636044279978847493291944402710972601372256589440227384016936078878063135072183749354075085635586953462021971954562258648067782713577521488232931146529745111266792210817333978274370001036430669628122283673455558291021174963295273346825131931915617781315045590223463973748294977278382887993907285955514293529293893554557074576214321954780897855629080574058916480627666273308847913271785619672622051955258834535924233247889822420981838508411635681642301213407118936548042159162861700611493073704679438546998293211716637515172720906229994027155353712235308990076041588851673341336018276648315748115857753733855517651557401509238700079132949573718241329496711435328233275051145354451206693360747012086717234433880311182378453787425385867210050039139762193039338514397440897278886070385798117711552461781968382301593796255609654974781631584154083506467490274043726999148130308189499359955129571094590295289274052323113520764800167225828389274135637750599571328038977032296836485972900498742734293880878497060460926051214866210922761537259320432435563621028058899109901339720706578906491660102411573741638097681561103282469883084702950776309635788212313420934827085690398182531103667930050227736165628800471413780750932683958149937195315353069997200157407184995779568785519950898280300801928372912566083862031845257196789789119098467538862452005074024482884438457893589943706504014783592483901117560254911087985650122335394267251272021623159321498929759559904784118011065717849726288477088775647504314654866345814509588228950936674713887017136371554677745099360379172755522804682064594493173042996456993762382896672719501769509426315803143299020784276569582442108243007582221578088204105278886180470864115755884826242571640879775165330409671811758666182820176593556998403656347751907791286864082210620053268646285618591331487194117386975731157908950546660503248685350592918534064113966620824316093253551585927505824736188793878729285354949831818648352413170013205047338926895539631856429915213108062058106197383645200998733329687906887283294316534327913923865961985750206253276171440334188428195665751849767495357637369172302930807805523207995680609801065809341708216024975893436418898292601898636143613846191136917964338501241379284157861522413673951395203948218569832099978639660113448738617835102070604516851993523212659893465753772514722263115041110850185170899717085850690642112628421582189492266881139239576158310303442078669491083086601930234845388943236040052107266244862069589946326982562100137654779327060598293820992367640022314461867346578852859390468629710452220006239449260707251039692621356970341382051631496770160320422327141934749254386438827581431913268009814073128635332067951008190991326632846982986440774900463887512775189506047588138708272654193831762848939209958646848672356996473094477746152543099622503060218766196252427684895361046448160380611263745435129392867356222745099128663998397254960100755479714549451391900288379004298428962737766756887210581201936980269466206018430786997939479259740167627072430800162879207382562121264597724669237426272278940780370991056357042723028983468616275203226144865666035288268157912131457400563022875194862398233026331615664445633475041338681696837871781381174692733157319440604941914420822801805101725806156132565605576869209032320845484979579442871855652838839516372470817889682297019200643129768894363346743057470836980812093445847828847452559823402358406363390178335808955431365704137232776105648266105685060785174955009821961070674105093956040437708821486551639638800780795400317326325604466630642290071519102125391313222558164830966492183070803122867824968238322472839100721384336343227833623259621411381238981074146734030377776602188215163271444238191549386950829879749390576028285615678863110160358168121676375025105857861278339319549145536105836777271836380336922360272682652819216653175973358363684695324474902427361848609522002911420786418587951194055981588347216682039695156706561515673983508952366743044211232402076940633140897042837154297879644064559667568401095216533060461789570179925186315279383761213761983638623483499764204512470130551086642323572144826309709177968691934862333120035870297497263038494928724183102094068856934127861223001412253792382580050758466092428560091749296846947571550281537349444955376190458361541054860681096262554235029970750298890923227169460170396302124139630141632053805471117892068483999789542514287037023524509920299981278990573997951923721365924097623975172085820467956810191470680910592623739050115846768254749552085131116619710710853172546980145802177991958324429135487323738394433396768017755189430145269528757691284532102211157575021215138850488001276061524285559484301589213893761372701053029560631548757110540056700784024255555877614515620411212257513243045280018967324073121839580585329307484794006933968303648341214053214286631254729814780002830077080306247814304703379214820910409247454896232549862666927768070295326367999698023801586454256083080182783811844137499461252273768724210517067614778952977465825497020220708411059121810074243637611641827110976593645433929863178774279954677538015145194569796203181393198571615841261546186314261202011679200208627244463239511978366412774372578462332165312391997066525319077711039817994598664831290029979714030319167689072700399675615846249985770204496976013938361565242520491198306198219256524912382027123484646789930445410291525052622026075673928079199387872018454231304704770776143072308430335166863583699075380522101123774425584518271786512516647202154259648971731668783925735396074388804439507030095182975928808738858099189021322831871679067079274226838388623844734399155129320591066034847403087083725652065891173934320434821871316123125027000660460828230633122468072366818528455388332954054957419755673176810978322411249540799847825580679599482597374006574070549083165972578751648449274616618896524130124307619898515540752330051851469523004982127063908647416822968729828777865135836965807665975350272570369696509210842404322387661453048898616704620167750230604467029297508514079437367447457630800264239397769985792861978388469057979373698899968042476036348709462518799092647312581087374762270925946099537543489753585165152520994905724050843451598240060717084698432570267216274869202724810996962815557278460416993319794686062483706339024356346808613587436593458964730474884796911444246745844289548657292758493500355816790527024848016668879206758514928887616483009007854030632097620283117405006743815909531324860385553486462253787830295640874576884198419040357082070200186183898779499562852435468995857010869062774975100885069354107672868065438263126449090840495104941451489932871144328564355679081967803450787010386149564431433414907747550459679335454325552126132896253062547960822116158748359136645530908078555319162746949252497981777541235358093572682301902766428968719850680874395824963303890795202911768944628373033131107517448141180352810559361045656121619516554100814677627914562210713698290831116463372714612936912364169745408402579554309410241953132882680208324404476553979585287807537221303983005923775018740898122357934342104155863009189118581171507355664654102320884773916483461529640550979642712498606748326840159831071358752770353045906218946821347850876465261502739958304187871409299145654405882538667192487840351063583373955628119681621372588914751620237040210155735845664863714069543745773145042114769786971098852054527886006000367645366988659797266922647332478835950027855832029891111102957464065587349408195618480135932333019814978103932953655479869452873887847333975237328896000000000000000 /
        5667019423051459265475108061392469511103111222137755702922566712419867921089255703489390321769279253881800123018436269390980112660163624696387201154828862448207554319212883704405528522706721796440380707463484488599468553739517147318263966030436580433590631641535355704478933774356556329366315773093410258522036898344881031604212329808638662164769575049239948713539018812266571722084871074860961591929454126096868929098663140935423259731320164316469911887166246903785056369239304273101145803337368478257576310198204513789033450431891568522139436674720149315040973925851350399435997595113180144610062200266311771195958278788954494653074573866820746488432250359073197775720604894926032691474950186897177665678996783606451780776645176278771509421185081685449404749569129781925600556051790041097397904521983596448276978131619333667608109616125647400075548230662582405190701985913049980390581803972351947696481372179313646613649276619768063280747784814958113379260080904082605601642214094391240956891202647390929960381854455373884210433968297222137018765685428239730140627925355110998470551507592916407986322728394273413981041192967250186994165843393151276745409384145074317784938015961952041535207409477982948237899315935967115223643470518496024527401410399515655918716157308727024271709695904287229495921881682826377416383156503727875662524481368467084600871068203404759682373895774969972864109748388591930338921684020412329142705836815851348356352155898427391251083768257503987093938661874368961340332754317782202383516560720376352951098129325656662548364467896085667604262580725035386161922811465883653090815195930555135113192326538188929495281215040944639672226987394894389306296811772177442442576429541671640485426386831958563740746258452094424605960713567850741479144594013350646881244053214102708237944318649333090195321318633896845976307512045140018787534462724332331339605594141116990579453413047169103257838443730666858162930241996018915965687635790234519072888638083338705204667821741064645428445293785216954904965322358138244441452586163995111782331449119101982204954282997151886564660797730524752867886368287169708163596087491445878594448302853159611813845401078571682068221267559934758164773988456142451297257027069777380306489671647665479741428791062716504128326646548490333224383545249271535029558911555730589866446439253304592910803617144848267786417524722450661080392498075825358054722060476905815467192832332075598437763542838518238152644303297434601634021110193426837841302713133682552491824267906224231519015619902761194826482487871472600850670120507398983343669833656971633357205706932630318713516800726271195125753517292439341247077329490523145038701436187059919014489618781771152199762981326395338677893652338969132000882694636604857898614618048267690454407466447068541243985123845414583786141379210274055474089419483500425329020647017408654156607507639981973003239563772842854887300202725906871969307461498007954404840386457827878327739705008071636310572303394929323712891899889653329371603858026009532228098387350790028908277699432393851153264879160621653714892795710337831874848579283314985279166860433405821783950378120088627294127838078917947079491205978261517282909355078082143895626907769666048070013269260484546854767743121651493165359301183759948589489538496982654858331683623441821159379480353526300867944782477799286430453051123148469387676216620736321058665350558955703374468295468925041949684498944193457127048082760998723532944732397945283027130582436210295265992084046702567706791598914377308882210556173538350623737619456924763915551021659610242652244525945856917214983238107782855621157441005787944779073236036959423152123934489580443241110874342971568393124708505582731226493660679164602204899249221103104761745112908292560257253696737104380832439720754098206965641563555017090422631871369264277063027153570108614348672113609098037785751418895792293643312197352055062638278086547847336954400063634093725431369835389674481505009646531933774710666509803250925223922410647988035415716305166600644405260166730087450451394962338380526767969333226541468856245464251110328364832781081037362106538253868539359911782167829353604364558615784309519898556859565918321842892252257703520275243161347824196346176307161831929495616361651780604268017321713192388130537783783677849106870453253702933105787983967499791005165882014934172254564240526209614117743567993254664368612483881572851368946492736333819001738239156722605828897270235557853954140671873891859334240538224944262819024861087789598552014704258615688728733038157503893228613826250253882759431211777068019135475949443901667207083765208946430162563677527395479017925310409345850356097546410998304605147080173295672129104834084398098197056050891968018256417032366542190155242880344100422306482633878428801674127814283098392695551392202830202369199314598258851736603123607221428163395359272262512374309522311431974996771807994341453004181498690079332686282515583657195357769514715717712999428089368250369453800618533520341550378175711581509300704130918052246068963116892679311739060727204701637644560295545152934082503734718918707064289414385663042196197880914708572856964898863946812953448419705630314996732805591684549255610301862471225422142999131039176640053099575839818774914690746726136561432195447742223773798421593487340359403547916768267837445749448858239250201696931405129359035832176741862111510904153992245735070890870431623718316841713359434733559115669671895424483522338098643719378924651996960083065908826696033379410258730445319019341890335575754442502356253782361351529310825396833001808670966451974116506651215737192257753407997400350492199025510218703270545095640738706073499714364876166719496454720461190062178186735456610059015172621385766162259817833892336300470272161884922969124550933930639741649622856664449186293955845140706698555955729283749609097687835827749108876991653547161591989741316725983691138139411595259353653059550815124235933902287062158250655098431022306940587919592198244026956887277048076486382028962153485071730789959369832936854415047718760297463476542894710898302591629199116392688614584128836611076520237721375276040083802251404738188335844942152346028758636673440392810889611919328617775939671514472328249745718694806440025041670381402042955981229852744481932113451667024619178892007243605972628365323192519199689219384748244985265581587519938694944887786847888019343848772969213473513237042499559903589612354144196054332325026658616592939444356418809081032919535866339771679303589306194605378696744758478953614528002713942507826273433390603580554268192026707530930849290682741147691825468841821958090767676967540054125436992519709037480911653809057251541511488231027696657994046605651746049311004786117762642621361477855060843342637582540871935011877638110635657475608069261837132379583601307259028341583595301314512725082653435962041906217513393505651339637075339484388844725080055381816588821106001012116756819707329588866063635201910351785126504087866013504406331794959107055829025695096606897673570003342760818805039885503559060170407906267167607596011055619518177207239327028590509822338079268440190614503142584627734684437374312779923332553190747381616609623307643901133152236011458412255043148107839700184165244260299127801387671780131736627871027928617203388498020872864407556457462194154097260012412855677556960435616010572138736400355160539323109734813003995558657365095706143520610350106606317435754063138677551200854326614563403851609444695160887760560149464695964266874186283572711936113403953501719346219556662570816393094102043459652286524596229972441769231698462877726417108006548800394983098230404458646820575475136615039502973584529625251623678026320863050530258647334739210505565313853264670544079734476038226741656388229801330617757773873330837642193916938907715008348670662087898856897103960910835754747835463991380254462181679897005067344882837808861960800793051177140196403491074924172064085480509546366608143789881151495941987414629422655839187760017409540355249045875060305257497277980953374362310239202312791651109308125151660778767176050677940232664576789915942394556884177157500303075896898005165656858721709425132024356993018282126742595259627161444970341809633766179091711457019238445007815655587189185147606844936802344414568362042564934730085058389660449236959215759914820399353036666368613268219433824597627376364339085590717710229847096790419202761437186403756112801178442424256432395633911708291196098685907768610818068220229281276092145163267017540668094263391285273727897249967397245975222950123943230837925833216762048627636447567544513200637401753138069647787590906507487760634508204112835743472002700883068522030162141490065576962042206156794172286573055203762899817825886761228516270858918334922263781302670787713187560810445179935146765153152495656399570595907830828985337515584728570943057416695901403271389883526484670054859037021386649456146543423614418888630015028520023653547553939470836659379211123751081339923971474057006080613228513810278410297691159936131850414519049493242421012395655502053763606097082818734726216286480447221719460352436926082987016624301823410136913385804250016753493931429981985084159814693906660242234467216268347706696764669484749468371254550022000225330524010567909239809981541685719675587720866089204024922176162601541 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM12PrefixRat_128 :
    omegaPrimeCenterJetM12PrefixRat 128 =
      (179615710531003584468283970384833621526501249146287172746034677111067494646592594198079520409183307467527819777339431595235929531036501360863322363608974797418639743774348357041374395075627170519764201596424054074244359574806631284442913474708782827891168216948777838113900905762087243641941397792866697266128642568796239516320736945339047549683494621971470988339721692655932341934762801402623224376675061627440911289170220664126175320196044343668388392229730632866515481023650195761903125983098577431990515691289954133285787488626378503527361548970231711766807505738928299104285247327245400967544283452363240444276541672703743703934131159327206496924862953478997663178392604298532940560955316716048167242638196092434568982012059037377726945354014380698019386513524589360601405975274923327698986259794536417077696005290068363467223616319362750109810917423028455824454051537075613818086713387350354736202652951701192241139805349397506047540879146089246038446983637854362559637733674947932757211069032554356145965436672715618471057068498149613971791886982561705883281930001050819989273430994448997081081152415909572637899633019321492168254280707455916265568582571793484173253488591558901924045059303114156894084505139046563992153393224208807744046699253162079727008803553964086312678192500725350874559575107172829163363482247620198326851953575899640858106724490804377845718340141421353059437707105947305002656065540937913452184688589080229389495826514019473557575754247522915453634441296452118681273259767122108036954454462976234652275005496604132815897149242576914806140856316184554826962135524115983864722610947659254880064686280735268963944779829827226996486151709578132205261889280041132777269510384173444126869169354607547298024512505707378888945430619256972256613627980682247650613802166433053451377324068900056216268037742769730634439891873365493487906118035045242068833489908480687653223050019752150191182045006199735680882116404227276362313992428301545325091288078262508437446410353989726589686812638667558326780722638926113044966288894146521780238709437906471404048439496146691783437002234421916142939522389931139535503358404279853841821432515700670439890438760227245144088583693046571583193872046914873642299723178950659654852252098540275507832319943256483906072458042579903439045018134123277290580563366436769922105091489491510802431303167461327387899264917506204092913901882902417269341240568252673322987829765468121923837624957897904443787190317636678476124292967652934919439924062782660142021217031680664174378415332394966255037807670608827406748615196101778673013598791971042313362504627090015771780180742306657358658010715742087093204285658013798903026763352561140153000509930649651216994617531790733806638224572760875056875353042019186442748544271690104525276575172831570703972980392795138346555879842728616361045747309143584331967327977665735809969906558125222312252859190657289042330844120144463655039545972493839244095186977196818063258399018472614050723662887374746652478751167402480717710394661280356545050566635498234493811921127476838588874600882288188946028416761732064255637007557618314627900065617468304251655515250580837448354870825480489217679708517030949273448605455388853319634341368615747077423279078542989404058569571357032753153671189780063295826455535005017660030910504153287166852850603017201167459103885105847265092411480491841749059942397297125400456243011108689253937662806443959594740867451922375987239074280722099263518752499241544372156142242315813023080668109472521357654663593178112473395076157081919545274742683725469266926719612433958352601443238718323573957739777338066460078387299844118767859660195059203961053532870340580082176027729590125301344844507576708931525631226952910284399655880940029493034470903030456563232966032775472806981387751351129082972362555327603141851461887461463689842878422826685624397183748784449083524329282390851564818486176947536357255220733655881728837673281069615572733991477967061538110537675685031278878246083843150229622157202284660842419080807039871090398773111728026054748541612991657082955970882700891482924850929729906869415633665628158224424579446355600635147165848813707550521987500842440239291247735163566749169517499715658714788749242635570698113544417933168625489386384569710885062571831560806272136279218902473931020428365949446183958154876190247309916530986092912453154539516461550948118654322903378504687314180562285677696996376875940191116715405823551707156153813785347611977514423518678269546472083221692605833085004590026258834796182331147592802910709999565834535098434949171402208513204489992038884979496063309268304527023486952629267285112639053592559961566845251663408919260244789099316850164654926017481606470451517032208874184392261983708285778543945327191998720107584757545935883666061410338327743846140245767441721853194626757153289414630685718165647603509371078572188722923177284390023499616119351785451025675649333141072236646366712963135461906537959555948064515109790053693760497355605528091997604521021959230733022665384065571725018948095599402076606868584564330268601960361678305512816381506091944915953118134068946484311217904823300976974800428951532099654781140521016409360102912745107518003475992359758894634523022353570512335958560562945919672423453178666931782520762730048503851467992897254878456409556897488454760561154623552970125572186982609158954363158209645452356879191363791850784779655761586098806117740841739263281342297937874192456804410133324859492906292825255483350119843128271401281832683943121700669643161906612662078526802689922607565291645530615277774117497147380855580346841754810915162308375643550409902644743257337341906286451304401114019933736035522261287940975533857289109141213564126649305903989561837589261988206304943412585896779302021183071229363965339060682712421950009978008582813280893413457975471683615601630593476273249339944668794040347427851733699467985715771172121496131188767381820265755354609272033556433733331924438041210264401957395226776071016284656196272869132176875135711258448596197205309879541232218074596278046751314933729264360994695810591666374464172226913791659295135772464445418643230695191808530549122915632028044873729242565332802121128879344583849769031803649700899492708314973409170249042573871251858576474508082691006525690447873698442029784134150348541812852605529440890939683792049983426767834627179145539135441650419945331449580876217097492517777218805894338441231535826105786720637536114750981480819919007680360702620797985881465336303995486724754974189555543252917793332263377638814160628807045177740751113980577735804104658925550154236876858862997103254694746867617162114198269056804565669678410176771863254832142724100467390169003462973408371809959774511227123624778325390392742672032326709783595337255629509004660066713403928992701869877728025461915426650372364417761455506762138549460440012388727907368872286979660950770425978123697005286708924989112846797101173463335924951903638492123865768949464811220087342374381135775030361958183414006347182340148944761893773060777327642627302775760079975337188794757229766891203995806391920568936918594301554519641591858421537519336134318300981987762278994797595534999377108056797279795163129598747323569716584357766750620930243153119644806112059478999803381432988628697535351331460281332433433926493101981257561997541930684254368056809387322603327148166662313788247623148190321284662327521665836674387081806142747060862762077268388975731327541069171243780801398413605284198968669067217312043009864418794006841865108966510160148628285331625769695743916972144477223913734376184020605043567484484034383533385510852549373237161844862293076728314341706100292589984249251883146026743960304015103114295518723008902236666041959314237049160773194039240389433927871722631863442458104303710950598383532385839594583431560334800180570196284592823998938052002204241323095808435198380714173680582296108612979213780523680797070669181372329261268308061240246697647183241147370834659185487738439912722774895012499218596052084383634624413029103317105793152912470942012784952245780794207697779734040560508371695767685071347346609365379173136809413252559947825944094438011167960322066079147215138621816938856539960394132704357341887525144475256214950164445668021287075456954340278253230895943454461870747862283922395672713250282768599727862234689865346741078066967362511134801460568179162898492223526196170149107835275151831527406700780733693328753789794572326859564228540554091294864344062459981174959594328885795395145945631969760937310867648729860394099866422092234721713533757910723220357392154691859510237661313787395097751005756546340115597260928098002438610457948311820730125490037242198350220563295786068617318331142370798041125251807903299995883830825440381040884262284930410731990444397450994664521979082299325844449363654138350258497483515980412228183675918998348805765351671010314195396246969667718227061227298534613692392142968488812914455530554940654729488746865987506778805373709394952075158784167690490069188577668955056406331827802676260583414710245014273908759878114861207089383504507871430033180536882898308791059732008123437483633998223273823920817003722651410188651305969230539903025943509077226010223632972747791265340529087890305641720584055943248799849866690637923711563537037304775282178154376008445413258861423351877170254087966767724698191052214184776494793165172166747514980448933864516778275600686896537567954006276237059727803205911547144440805284623354735613371317635127085000068199943571096597325132015843119851459980562186328604399267358651709507893183974591158977700764861906498982080000891310856132374290037311353968914835013595135727585127282861950096667375377220892322953477022284077707571565035795274446770939042479787926886039432298157537822803895380539808279776189260715234864993649369660132472301357333115370854779013878013931124167478369093160928101334993967743257492834284875431120709797165708452937736064174960195002595471992988133621799016274067557236465729791848856862696271331472725340323840000000000000000 /
        459111812384399938173273858246941142544360160689985258277676193989450576354461291998217187433618309046030642882156497307717488864613385968283560323502202582976846616145481028475978353602928729736898130624136425161460933115933451608008278470035505845904064850461604804005881132943513975033958461153270330475869438510150376805577541829769229473662554660311464863952167008932558475581582478521228013262908265830341254520311310288709005778928004551489226943094239207189938061975039579423828406339919661459132803537742132494727819928815161141965133148645472793252015439260900152164794200945183048706368297051085000032212885139060360315102582933453166299043308804919979871422460914103245028303879180364979532458376856597564832730734657200228788895444779029007155453670653897446931632105553232222461255720078252339871217600375387074877576171658526827383265835497840831599277833309778481964918101839140950985920673194620157319756962187337041612921891764548290286292119707916995343507307228101852076915030464613373518593783856427513858040042188336126306414088731895616608242514236814050063344378758720672209581151248584510870459031808341312180961388260967714911107937102960500070271034451258882247143094992570679137298976414831410580228932079492947210381501693968276612907552715199080726909494734788946357798570408957055343929488084431361134710590340971347840276611423847626687725749330548084019668361965964227438179782294080732760035924107283200029890554380330282855803608202438266670418187085121800154164409569901491291550516580295673983723567448374877146750671959800392812544361063968958618758658235838065469631532856469252814948267508597857402324208823083342404298862721112593036523649999908141737958566245377607184397180030386896739698667751693405776970280834672520901444583014460643545753786623309990029782998467828917900291760674671747281037494086327023020614467446045075284406393957037626506841698921403313983793959637967520215973385276167124269796175562264225116871701040031036318332572691642001738658031161539339814697668564087920268427548789077429728578429230120597274914334737017469734198954284414440604570740097861946903765915198874738886249231704696668013867203135787133381935891456717132959253647229244130681681139874928647892052075489956831154844572822591508246001014760429270167833629908544083195073584749306508363828709203679662951116777812571645300607045409544301829338227618436689525634614907690141194855018205157414155301704101859927726266687081461916032603213257113084477297843417806849827611951157081993383732678479266797583811838546002317555340425582898352214887235616054297351644294032724714012033913137502480706286386163154037954389003504593677009113366905327034665090786194789400265292643055760250448222324033093669417642547908330411335151989109721144656911170897358220302149174783656431515107455245378679172523404264010954836096154600764250500650182594634128863150370381476152388411742444211062587947248440599206947024665332572567586757532073330781974593882657685983688225975904062996701151687816069034804795512961380736616505526761852010329864411516776391293690719760620379267058258175469446700105426498265830513644806941516516106224722283674452354772032273197092736275338536040132377543451041579648001366566980292340367569607910282598132679250835963740381355801016025003173954415189726357272572229456789397937179240627446003007992354746485218003553438022081017831563569543911584117243869362761483074481248110234852620910100205017091573313518237049402128139855687576056528284627783303865866020939910456813876449012103566033367534818537287538451375774310467203510806345730475704872443365869524497418070963620032919738588985319014253897821041970168723757631345227433605362353933940355475341589249454671552590324224977663845053744338364993605406676824212841946425475827427544033044682076585101455492627232425102436045675542589732417381070932161739995157260179171213867905785361522723575971773777025916888993889202072085741618040523597093776928694300372151431644529769292519615932837052054422577447266068811687935832009813449406972808149761535199681516223195805433560921283646297251298598149920153224972802639528599353562006810137441607327632990655625104128716810428416333555918045089412317573287838694398253514527977710867975118085265807939082907893294550696347864383819873146862893904409145759357886847055839678362174069434933038884318179679722819018559636363059080004335379420830401678620072202012250573225136876322908288838536019117785436802708250140698500481841823683964990259802306505441785039349682391698500821126329141363069953227376340784214542756963079702197727291613242271953266733743485792951702000442089388866817246548993339683077310687929800203272893205126441768606761382624561109879626841526425089086513704407878881169587322809133029234348796415295692201196971263105318075342017247992558928889340415501069521390949371320836421385128038086068780759399052919724635434789530074191608709949307926878571110387625364297856894360326440686643910272619632838701688355279577794232570268134269531510749121647556010802018634015370680604588327026446148765652375553869327666430793819178427917848785261744734080891679861442203811917061691299380272049628196490579120660461704646731841272642109495713614086490496924272714119690934421984479962404738471834570263527691906451397259121202683791349647816234553318980717842399425538491857354707994689319385913114928719516055362662790861140886438887502378202870397367738097936804337617927825680803735188415995721687073275422990760998852783626681378296024219419665453144098952219026238437950024472086321436573885371279784328756512894381330703006937396644716972828658564515280278136423958675237083669897574744144354628775702463969746568706960251822138091647235587838442480047498952610139706066462924151516170374779965073051172195531986727211257255312251951711533046560352281622694138137511803655193346857893019591570699451728487159594949984434112831768127424991640438208983652151942574941723610007176145633083127601067332110637218815294028975975488443887254186963570603347663122861368302476301786376890451981355844059149902349763732279366679623652855381076224779683323639164792103129341352756079594672351289125543496179443382080743837371002947391320359320435999253941536428354197132371664863662489385571896829554105087775629324456856568836425375001751855528381330627316233579186824187995560027430418222387131896267054234637659194806330572594925348708307602417622701990734531717530639008371678615021644594967354702381280528566818574885912319262267343049308935072737977536632728234138858893485297266453909997570266020015645716151982601022347506336291485402517357498466628839288808277510900388259732090847597102050895711606281694667024270249478118473586698124587601210078351360300786737054810284593454449723834476586423411444025286700765707149303293030069526782632079618795768157380826071963919687034205127828144974015156718616889339288192395023636552059396478378587529936413964785224867084440297528871605892125019401943444763066835612620418953726204831863168823776597713227626249253286279228969640629555421566153970344061470901481361511201437717441202131753463300010645211838371294514019845373973301514933326488555793662915378632758437655037473937750761590843936028693696077951562119603133476237243185556309133099111842353799127463057275035503159502769942960069424146958033326770483628891083895871630381573581835350154504719161257059808935876180338595060496021936304190703952998196522482277666665757476263670533589370375667746570600366877992151440168838983284412718126066717528520338679235998253606233276751005618097717823912855533575322382313597668022275242447375696101872690458702525161176514787302906866715614401301508898166649662366505020513046019690999765906491765798060476216940663806873302966032471842498823669067641213590035122277685931489932087063382538706269236878675134543082442063870241084395199046123168649730322072020905199210191520263106525211972488993882986710720058318142523594623613588883433163519096806944154821033120580818481793466601305932781583914232277285454528188975790052204668459192992409279904955927317608086518364503473052302646601725087661429469309481399499419827969427416599115892691405723964643114267080981019417110633885367490003875356830791616568755110381184578329842315562868859934863042033727889382118021721285254899279761353901205362079939446769120362957073174268179574744895819093805741409256465452724876373718417377457419144993575015807951165494826680067861695977422211230752777462644361491811372582924603642933123283609826113209188127884726784548166322844385043780671005897123091883538283343707750945727788782787869679270918342462035494025367482223516626516355000760247645506127366641688689476023686244274768999640691403344273028149141385630527734352445176401510235540077170380241154905351163313493836144161052640802583338495436367859264330430310299280450933608095479243270151589331156146685751048713235029042253747701032280461428943307853319730016413429339211657036000995402578327669668534968932599931270995445605871167147315164633656678103191840863998858508400362306766063588742579570030110739974173685214313716143959089788123330630948178419881386535835712166403361598210876919319995347215904494426023209948847384412346023516131217476276832993554641859641375971049240168768444563022181782518751736172713420692607796764663053356999025586868233280267290912795941094210264510673926722688159147561584472991730691135416489070741348440094034008821837353625645630267950170809736332579664611818012704031204639955961317445765950897241191248905831659888534993899506923776634094772108720464433785467114642897662257181403715952863901629513091562352549961847111495994740519984243994351436604834211735494069929029407013325548477239199084790972329328461699729310694077208291693106491882433447203499850934934763131227418136120539519088208846910712386117882745642086768026578678358337876246670356683392375729571140839034739736843298389988959276083051324801516331981798589918537778782817823407813002498850166998092310743462612505915063597637219233414978913683681 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM13PrefixRat_128 :
    omegaPrimeCenterJetM13PrefixRat 128 =
      (30759443306592935244738768156820014097738610313906794927283522658830034929420988622442237782328825202123093162996621679400004185550124416776142572128010363658087164305806842695970135844285812704110488709627247598439846646044572164359939377022298920825176461139297889420051574704302922399848218240162798463382067167924694920857727285479656012785095015236346082618065935352825836370354998278135442247842343487333697115317288315337356449574368086357058854453306168929565048922467846299723997852159020500430264959867352618999248452607494061732644106834081877912580494896113259590987995596953134835824415278249533309692521068109392345823213635055950989733891883919699271557601122099987064517663922958265460605587913494782001196253127686177290488208069168048859822533349665892788454833833927257197720775592611141984108592579591834368591622910407596560194038184557103167522995260525716933062182515094514878295648916149947878955377256961028148862880429232928685593507516724468255372928572221224296192147510303049755972568043730724384776413156980472714700526078881557282165414631821954544625258451828442176150343695899567199452648856866447410997635224525257224099099499095344683136492785868826563611422352872687183781296917251157487687090615243442030512452272316452278214636570254106431796295731284670624913754495780588352072826738364504216972679266528160863088778540565795577282344921612318352195079250368488312133969767391795578954535157491874976595543495166277491405365345007178521659920426725084964742547867022210993697246559836101278222132226376856004910184062042849469785301361627453830951494893474047319386421845844522958639668033786742519342017934699869531544118920732501415527703139113531943575219869556728208196477470035604817406072383114688438877995152249041472522423861750409726430102695655584015263492854887699824741858435445341738211241108905141888535196304601542191634272000366897123813213950063079531594035351356025026194878494171958373094374030670068793782531016805157135992795818850268069327249013857305009436084989693687434163934159663253759114346929489284369623905455583654883303162350547047764388104992326946812531383523702308118459400577435158662358666588309223117456930685002866732545380344330799548284991948703063806145857236124191911992405726073489596031980897183897619791045165545920567451810329821213104906520511735839500247938301232510914232813780556121077921781377845269747264091698106572168231121248149253505854408079701595237197522232326252250403372081543402193108266738146686738116092291060245374156742588902097710898210758729580250817006446899651993529099699584432025466585002666371980436950518468455837765412926259525739321495060946281974811288245237644046993008554367200886770122414192906222217045688519193816524063539286769139991954117040065933267701886578212448893449631704306902982329124715092270409939093030695981910075918924986666718860696464450432691784278934606461893712478787480363159404958366799228567166718769550163820170541956397836409005291470026884675097334990059840499997193153259021051775639845786513307835905839610403669160101122486175981407951148311794100385590878658527613066856443651279090107916454713659679432553378694394848398630248607088166109128069460331122419878347869638815465595621247414451194891685187547914653372759194464508258473415544203468259135562913139552095674978264780916791629767111852840367730143180275110272205269300835387205684739685523013266693056747799529011056593369241473448307953904904028497535601397969579883563225254232055096514462277709701277077651042331287116578196937028089147122748226717905558225184951287224961158333766969988825327751077805324486649879528642777598258931163139401529801424523259222958535392389927521717514428625012891712277460182381632667983094039131737243137263811417045008275983167460078819764578088507519873308578938585739721227375861476350854991264039501720265114157523704308033796312368260194296928993911792443218271717725248069532150593188813818785446234468661951368696167017798307380079699176359553079143229337512862092417133902446658190140526256568536456409132658367181465161964151837588323638511811130665311116304555687911117233320440857810170189431399602293709503293330426333382508083305461461009205612729214864897432437116079005844659500758642076507079237989489556002809387370248387898449574626801655943642266347405422906500360772110105205597674499078403713792060447427715039598611176761441642242162130518907038847995428182623991824263837353396375871214433112116221620216847434216880944883407392758403331327534708316048753135456196510485552873222786696154419777768164079988769732126192304652708832576092952925875638011205191035625472937189049859634592719296435866623025223691666609108378788267338574164524226208161797574682408442530937503418876338091011163439226458286689432800932466156830126291570797801512754205492769547337401451935059001815471496633322173808616686942928897232051410573972753288670075878089573573572099133245855333802331246420354024821742454683058586783411735235440785147617447589958536026348829842639522952536671868574641863661489086345473344235356097776415748483081135446807982714837237775868917300364613015998642533684139832724321787157096711944392148373764514289829777777564841769767774352699695473247995483975052802986900321953408002038819939442410286900138108700403692640680511639357204405075430044344747567997714655037284638983150063963465116887552368931825537695196246632961042023649900781613708868330162663025523090269645714082054385469549899424424685607242151308839004558662479616958061085852410132845213675527103949117592556517547042129542519883964870442477621527330993107107836378909827381011074337003329209239287230981850850463189538181904320429965731667429950733725816249011750344300374163857693388335556845543363919781349276163815290624942516610004864359693850035091882221829918103931033251202627855591774477092452162512816272745557886994955232182940705568502194963442756997079909888662384573094172341796679743720845007781443434446860273129548178155122484822941341693732342591122780638643440285198184277376286673149649992452641664906300289015931191750669105933571927842448825824285391987995367670953870214925667466274530359982065570226626445888832507877366484640624740906821834880092617220382646419107712657378751988246902072141435840357552526354212164526734557326347009846603123207416957002466893741682364649270869138750615981776972235321804215194726966071415100217071360877471293457528589008970390350440988689814486773887448516062256931826463342149277722766555249320041952985495600683071328775370095469466809119600234394018875841914688882380402618482637982093183141262999695900018047963773990441468353607940304106725230545118678953055692402346985548619035689593320009258674673972299043832638401237204062661822186203191728591070149293954965576309612160480541332252374151080761352141901577040194357030234182033263668354475129414357814300173752321252332491778589319438857124880289285867520442696559914960725857464551943367360535056316273865769246398912324658054123192344763823742717617328856292474768384604566414387940267108336097566716537820392337943994281381604411591407856507092238716555458544895405076065900159238317804482572410393777668247671692897923761849335447068468888693069710319716149260571414715659425255985171998256283683398161293291115012894832935057939959564308297717758566907449614742237311774419236863134243866741762360927125619533422543276628426685241901126169034235323587908442574072338153809608765116433949872686848032508863314827165937825724523870699131549309477754550889764911935575786951978607168260418733858859856365124932782539200860828692498075310763710680659841432316138584212934888483830345658003086310750342073409452236425034968372629538574817515458149542841703372983748907223602379715034418014411223246867719426809156685820263625410380662033656202704608505301324436795064345389610482850881952658291225059188369792246719539351474848841142705811682842595950200493052300560561253700420169877520533139500989445981127942858411995484996915963271108351104738732216333185493983477432178823322803665220895832050545793154544769386347683104049118026874849356907983678669265191612267154547951162265177696599372388904837956898217875807042988568330320484706102247927305492304707121297015082322547869634723932792360383370936692173673408942201039607421510593643709717193260989628622233226853222530376562840253904953958878878797797101383550868182472347352550966568900325320448159082469218217059975167055556402928587204013713154752630424100041536691695675057034424148184787032919678895745979702964195672447304761181379263762508607089668207506304784172322306031536389728170535947497730542820435404882835343072836869126339185134181951569735743808552412786599537293633144953221992669649550188518591117917301027718983219219294285347326759470200266702287378113068516412033789120672377363835970640282027155445527044043894022550218333615510928688344906729160312281664656684214325050068524150872668138068542400949345286494793807911764943087558555244636828379950581347609687891747791227583708419498829835336108135773793427818784826257104809495503301948983918671453910734149113937470407868803240369792913385371443611598922771795045815551191517050819903339222676514975259954177937134754421462179434976492349894242503476315058677810514937495761189125883270146873696697632310696183717992815612652561226308595237405874991178348547845598264317985719161006121404225684899552196195777787626491944098667655900971662800770569361303001980625245897088045893335698072535993502132299673947445453693507910011067715683180882911407648231130557568908920690981046561852715540010529419755831019538219015326378452208836933903693345182507845311071744821953433047102500576068629539315694603242377442739033268261029278854255201768985202435004463979712335856608886883878010191856931594399718116860800427321460748608276918070303564111017115112538371307710479905589245116509352985239203012965083361851829505783375434435274024467768702559857339678495033840030284515842147378792274710590235799731484639064511731983381935463380622179731388161623893296308340291740367835174898102198648694493545084128435776767408043293945713698963116794878328135418860076151007263077329353480371399420894412495089054726588673531075721196067258557326155260896231450932133681644296566710919937879941906820609840370053132394184268760766919869496518836372185251268014602973008536525319878284788567593344265612811050784433353663714650213756056533320263511538767239154657111208043124465429640804891100299714792315511863754730825428659440012507798950376174916043846369413101784481786317832992720398151101827037722555864101139696882850984003444890537929302668262367773108029692099419446593884166567748386033963115570532135731482122980709117453542547457769996288000000000000000000 /
        477220346972201503718132251376148684002820892137298582904501478086794842906546996563997979743607981606533252946030740283808414020595448697859795663632954051692164838183720389492901916490722643081855562856716787238859312685413651510627085136463024328286668996558658918133538957714613967707602625628885377628896667303896710758606582096907513623828221104531073031755890086616041548418935167192217048213527077663342491422081302705327581746892905690273320384902163043880838467573472990932514096918421049499818254422066534339074567012789211665109017524062281469748333813937517320461102045273457159387463018382570175090243751026721336228910816035742275921436456765492341511604598447718362102264303081248404714163952682892534737385388479758182146613727547959001166437068312105505038789608326713718813145930027683324349237703222371474402757027188902442666449594540710880481465463223168449433667030685939689000684583272145125056581161125821703975699122597013907982252233210332584895985819096112837636627037086721354558506017250350239440320941319745030818229180209498319593608453989158231730650578337354179742467468291414682589831527418701174485657081518794609110238788193872036990986020261155766374690329932651554892465959363157648234423132892318532137211089185199251931329565639655186597752913529435139822650148242835128193877182741075887498403127871697771111128337612559357205508531744586166319858632782368193785790742782511553343290837287783085870745177423374604090138877152482879086078322713834739858844848215663261571104674580918130765379627148721752967146080466085685564599125829240401804498332214640894788793725228326205425595722205042999036907001250913886521256885353927051977525988246277017614307755144572360041404389385808333545162602842829185659696121241715925831013682824281296507919305933368022175161589651038460574392361640698182221805447566771911552719951264057742525912603067877149352526561745581143806165461663041630274643032021323335495315053887178729221471871634447398053338411410084894282773495166637931687248621236470815218910593105884978227250118836493757598979166702944272908543770845500768169453044400200470508970152657001944349471276063068177707615288313666205898872071663449503433912200929008946669539153855537795399149419949454281151358304935867915964124897969705079398267483638263455157367070455384738746013544058338069557668509467133965399847835692758652663808044517133997732980522468151744934663614113914719713917764242397919879573526147621865402340074115025961328280840418315921265665270238540547833667805231206722549251234897841991448910899335094654960527943221159590578660231700465199188548762616562583777074920665856502240856968993292307632023616419751502129569565724827158707625746221946753462338023370864033915723617294598684010247654767234084435677211068466468165418007388723502893736954021465800989374104032909244793364604560578310112971928360933660038020404231833697859932895296725669795368035980190506761748713054280530590178315318951437551778467083172445317453808928475729461256372326418560200107133846930462761187225221600819106417020147278862201451277740593089981117375416464207202649913523027525111048808845882411012501683071428671174760743923810974977791795471298103329263268103295453275575045900736165161425991827527130361572072423249644079644518304055423484722021539365671589032975075192062904474092302530080822202606736143809491257533140488880381803613511185093468713748496129943105648066389740918123815071043613817894237464028223926777631810939800068989696746348875152770577900816236088283459932046277427076101185328965243634800486556994285216356190723520371763458264636179682743207773123131514204236556517117513011828084767856116373064161013122868962324680186342455097040581819640090429338637091653290388771018884643093605505372544405394200808506674508002083198630650479927523792613734403600455340347899887006241037003863771796887061347326185171547055051628884481688513572247709070892257603670422598685828919336625736976899849665503665949179750680626257469527284091682569114446692207678489478325745224466544153075539286405894246733745921792182513122178861422155529036432353887270020888898060460976068775885909193566594926808673651166800960879673407966509549372913134696692201948391471724024079004386121699743048062646987665214963670347602221644672744318597249951397712837838014864743299648719843321984389990462050540716641835857452241430949930700348192754259714855742250408988232698926551777168914212037532779251002951575072880599365873651931724313336258492174178446718428640005618568335153230950696824946691881764133492770717986578468257983829510494189953193202570368544802822456749354245265747471553070955294564288143587387047817707865516241059052953784494056178417545461107438283894355928467462915817305734191501406910404860292517612703577246027807756466812331859325552248539979257973016407901872082375562390021148110881231003381483045166195688290336973681409826822221922718262685814664948569316214532442262974828828599497134487105086219566092231332301989045932899682808655391214246664570901567875688696311982715244105339569206024743067434316651628036316622691829309110117530041886264951442811836433418778514199689605613113480121108056855811555581363277366801536895028739613492067761820107390882786278904268092316176669710693038271645184895734484689885763862062905028944808622889810415778984020653305797542890498529397926995927893435937396045077131745889523099966691074577872302667620006783898377953409950499764125355786303135233402515639234847000529535487162250040976485277511262586074556620893795937208495681501932758315943183139416113928279294030263801485667498238208053689798292104247688871024812937549692104875643091150893119457311025273630906306536766622302212809283444838039898004928318902376237311663420969587640895985457681835543099627793851732232267282538782071386001849652753786404179371433984766518862138260647735922072384254758428836186204449065816111194612222600940765516532512601898363369921627167377545321871825236179165637664331449953287926177710722806347862932115816401719284975609986447638406232615038579859791898929832193767470921655338956791190994814241319958808619918151016608971160084219059247338196931519655789312372696310382638437197903544520094935896416361015868767813986150517093712153788820672768971301293360539528441284290612745086073792803917419676723414413854167577558830065988644684117202530530544942668305429618504318467151018250515801551177898672533657788020915046438977146060667527551713062894083816166981652826174671912871718762659003670953467521857999340196102039856988421645672282207815652661384186906614819232981531390577157557696461122593167941237540060741128672903131289196904086567103044143913767553582318917319017771218743795845028312370636445139221425196665135621230180605869597066136199739391772774731010208150895025918735917241715671042473506313736373358751486434821935142694879427105325064529926319962030026701616156924677666980115293236475163569514337877076083523358576695920982801630307175900069376708134744856541832748307826069423342217357878854201591123282141119028495427294883111777160587986336418392198015076400392680744410813192335811553098383233574510375327121039148124712891756533465386704017517836783454703771147102526257391908062085159348794205021483998937298769977127668050824844744619098327683153171928512468493477811817095818168429779198715662623356088662363739561081442088623735363181070893427315357578639821583842733342711165543990306916732924808459663768579760507762455045847818051821783784009137687020140412966815334212098246397206320910305238750186301168815203553607925984942214849981547737173437182647769601304863679164131737549037739691672334132616872484445068649486049368440852438645554670100581066985600599275018969076476768949029371187150837199191754173463362083971947538530792619794807393910654527121429775201724316291300412271825875277259425443018289145576378052555943001560294420192909250832069825172510678791991861528166182724876170519141285610590430987218931407070919482370850247095768783063148544315533672214437648844774715039475785100459593672134015173738161481237203869444270714958195218717796179339065739590869957295229242198293502169350797881478558592846966835348767791447089625198085482155823229536989896305864251626211133107103893500334451568077842942851365178181971174115787431644820005733570860743735972810758545454892857611287023928483545254320781421213850891196895639824078054997219074930002238012689222494328950639376255246577622951642764540768379805559912387775764570189190755412812493507054322633671453681950804475193258464577413832506933715560226632225613966973590587499229905204296358964541726062202656855411421564161569320730694541232818276484997771395265857712206738463571374033749971236572960959068346759228588550923411993415642431909696540222486740045308494317014182188681339229158154640678554790384331171153324775731097550464239518203472661887065529698854289790175872313818847213688981663663956008538590744316977808059967779682737442110057867649991707738907317370715755365496856389960793981095202434285328446807678122370154237871026967652981280809881855555044248084706814833358276790146691119905534909503621992417740020482404437764999521906879589550136001782336017762790976287155724928798874298761298620116329943438427313166104335526951926127353927425193243407207982568823651398839784116319594150702988325353188426687899788671298543197066894451071496969051792653886175718638526307665765390148282342038929511354526220723723539322413978967184152441212888219872207335191888299646129303227346933583691245466219846113396193884728328353117022300416964005005838315894075151573218865621316554997745413231853231567532956286075766675583654813840715124358718135167359439730366717363080771922066676375106098718284033059832319346275824213408121304276977610901834482882917757162734338962618078959665154534286205494099549461682397966875369262464544089287964929375986112734674043960412718328213817407895231952152079289596787114569589146843924055919425458682414863856867264780444469922907514650842846261016266180449740984986223265161023236481486666359249804705294232311042732141358237220638841611921444271239511959206924905495998485320680001199591412909935678384241625727711133680323879063599143905901073302938656088525618593402992564586921311290395237080981456376872807298458723818632359207378334014666567736055829826567531458138136178064099411924547191871541665867038088099447346499918771484720863053104388212969758608515178960449114599250910627298221303605471626198859409419271326627761289793322164835106658371022032481248273949470828835364102191197227742431962715069862828036405675221205412634513109503984196564377960062446905972498787934301563478637912960089953960429553058626503831173309780307595096458330271792927633062314732393 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM14PrefixRat_128 :
    omegaPrimeCenterJetM14PrefixRat 128 =
      (-50013074300024202253929860022313691032968585109690328283516098942721494091694918181859995652218104559148484580355378773139757185606663265103154500767122878292710255723946067226588885901108755840235527936467233409414774589128745972383108062592774002102872024100516506838333273508976248577806035571897860908504653155286481361248063875558157407393671344937360496328467769075296532047413891630715340144978726146007073496198214929735102135336808182848365849965966070825083907830477621161797354926408645766985936962829924703926909456002698840267444409000558861895994111922796228024287207119718734594638678886074871738111099301998052933949247664133691708824737858812077421109558415039409889549188247254252151763923492592515680319458295593798709530485574396235561073063655229574305174577577317339736220318426925928104798704043101110569242011648479975200204885572451941756305500530246739162534687042023526022971491588242475528475281772130686840045031391972625603217084658041786213329515862012643411229625738755847374822510844371644426306742163496511244923245940756564057071229092155897204823042026996707480687385699166780984718521350860143747556615325347682598158749732107336433157393936908190506472987629421173724709633978435544327827197696091435018066653437700757468947906914000601567811897073677031410348660391132301715523380870511380723232403852012853978323498271014357802417414567665891987980785045881821025774215533487791444405561796432662323034946680119221710043805760374140390837732800123229006794576435481512534394942464428961335279536443260483097865368753322362074308931435480726013475516297937578995723024953478559838648294772746543305595048930110056079605634755089605070588836430213084164120292826900345370164048156726717638024001523417556963185145226408274601717589727927147628111808219089559315307033706584579694244299119229187723484802492609938044326318684072211095357237860335127321564852861861290291398497291314518851249980813162698180619165718820418866675445136596494696976155625895372677961699704542466254636844617770590784708086188495986106651089498934450986419983068835890374647749571844589207572561042870193388716944846755076046209644557005457524102830068344502158555542477779065233799097310671651849831353840947449984770111190015922050623852182806964625218362860293362625384275304644722933276202972093251932317810325072669041122800389563724195804212357453734448539138607252208337549363915536442141052861635336957789598571616246486551356326441975111154383131921889450766087275200878461059091347506528124380824065083204670889203580159398613719056243529421409778600309616837370942475395630139856494084329405111587942107994992483584713382748593856630929053741496764494022743734588730251419629267992140361568479005815244887674969238650145747194501615487483271689759971282313241788430211795201713553922856218577012789352697265546419288412648668252231459685015971479112317935482432937495015686741650876218758022644473061287019364939469510695647669709077694063508578432597747843316573609270673379223568606212719151235868961304061274391957173850910385013838130459437751162921829123016893250843206230693793648277348541371490433683706871703782652617437353585483462757075193036207109650280908666313867013820724544195210943818742691608620611853493795224629662057391604000637591545920535948044302859785081059850046711098510383298076420460984356258424856915763412768139284209526565355581257809531580285371698952522474334109079580093529267766321789816869122738247093345334365451123569508217336291722397971578971054480678378058217169305204769102530317082678598812702296079785645229873812639557435783982021767104373240135323662453831528577113089736197472075648549581752951628281492851050708587118086102227229002680835794220695018569074778983587295120746422310060877204009214628060798891945453029019143730455730858672397328113619338339704345824003138411389588416695008572323030089601993024475806632049138294398418654027593431985424863056105931890598007976851258149793419729984777447537510304143520085077335142305785117801119556539204647982583380633833665966535303595808027186730959253626252601934029537783760949668355861054970774638645991621899942655898537319406650251146225147827889741048845219168546070351434755486016127924977411137852583774646838725524090412162436262585029227233501214873256430317602833422075154385995584187032337471840140230467202384190228870350758896338374298784405828214876175834018859431110779240023758332703090768584451726138112938731287646817761855475407588256886191504616247863343382725263284209316308205701266642074803409800358035151877809200594787498516193926934228453179160453148023291677125687280969155940440720997715654506239709818493066666980558128808972182872489607750939039298343454948673524190402137146079955018816324190786483419188382805310038978085625000736437901457041611777966484175045296358821775779053725617167870450780406343097131881362603422578822115488743360226858602332544027475938810735960308969108002148210665260964471419688120104550071691152299165871294395633191924875154152651305152436114554522610079720326412435727302506712058595369566424670720141421581606915634208379555945696800892068956025103802904802407242784987007571740380631748611705224831374132083409687669089113500925805096011966780219768704010270316648387449287918141797369703857297680294877813883589768322498097621937908540235975534260296667846676391473949664468179259533946191256366191642812395915489086105740917774582723968074393293123552200610237865801324230848433988709579583364072866692772907428133383285797534378238932970887283697714299326881791083406232624785681244947339150700525246742004980176586685797928522493611201569408814477409376169657896549438402151086240501599662148184250211610155164428211343296375406044255000130950987480654811006576752923546058407879379084890798430663263193601762915363004643212729306039431650161517678517315605557554227162283537023270937516524454453121492610368579876786891852646450654387231878751970409822774907019194641514099083294171326975572548727614965632250450376245739853567885137833198168226421396374112452673293039214034173076483144071770285199246023079624452430093794524420234479945044582056792745643410318759457706032359247451187488478739801995374256642066533076389318136579957730549246425601990921462917573017200425622654974968450286609898128937426301620791671009197502662289408190605316867706803756373109134328440578209407127504497235027848111925662057921447530384956218341473194605074477635507050767906739409023913590946031758453303171984293066455644323714433129579127581356730751299506183705803709994789593183241884332832918582279863234441704346057304433261601678610981632338204965739923625399523364993739377140451381563702244162356393362744514828727982062519491657486565420753097331349997837965614221495543259271600221721280177056675963609503858180184960995662792588958090125531297455304212113463059208091339135539857854816461585525617462149883486012625714694876199877541372495019695213445417900776758273883243984431453073701885174626009755811648710595567658089901384725958457904389357670336598314242547824139550203281237660878176885017953612157876260222282516140312363276756464432215752712378026469165370672258174184719438229047189235968596123059933906109069921676084792526485785116899661724012145036634750616892459205160002368400971727194913197433766442738553716666599124668067074115670894429985760996983942796920708425521624910863686131936250222632186349247699973728286728845240931281443243452792544991224541535844995459055652702758719634851913564312234038377287163386408351717830852638554232759034523462228882586617134528362758817922039095697265166814351104934506253489760699656740037230276426634470707254489304701372994578703541043784685306155379775341848667561679741072907442286794319198123342882109441878872650790345993311491707726327950659682578877916514270994219471809139988504743222607901657257353037348623259369893145649908139536895382866285305440816189669991828661338482746263151727779815142829502865709048336207383941142992044074799962248541323713222921629458775323461265342951325642056548435495909690280064773288610097002357479148486737391694274415533629226809246062040622426903308577321461633634321679129887142139194839077145262946801702136298320928229947133683296510404321217221579806613708605353173695794123344513468796926051605503398124847680245499993183395141217754216288473881377024315680100979124094032282985070295640444488848691077856607631157317030109787992014252646762914368001859705591246105119119042032551709105619389750503463213303186915818822309257591308871738056526958764988566456277947367467010508591731281773404928226784537528981131733502860032290837691929261706795600564839352080729214227288336190403922027109260939141388046680427782087433300012961577341189704134332501025882442051423572381526570430566527139883696969019096146598884371690379984134660124399283264184399986183459132890489749479013418476764637871562357129322513387679081350259316123233788790723535264342871009641068901398563520749738732101253153268189447849838684695539873836923596619961398526494618769645326353723489247162511038128065607210522970420969398425481308460654918866927723049410630327644304940469599144368269599934341295045426275678536829565051876414200616449560805285324314132286856423722072311416554869262849230665557578621706811908815659355054417196917420735298701279845558225672427633923316072314579739345669374172209705462421844990481777779829118142965103330154374703683728725072340078714007044959143607642717945731632197545442921821712278659152381106317044831140503157157021836238037814088777295187057238963995822694822929680987914373915499064404621956022307888388867413062378563283541699767457472228239916175393233808116756134612481418771582595862881841202745603721468521213039134286379060659741956701784282456924626089545727779911375797923084025842091376970841316703272079415077822428351587838452673740046337726681966064807112064512269287876943962812806141245136866996769539960847241607175475104930141405297013319089103019493664973780531395610863719369760698868555310605666062474625327568893471859210983566033467675571605489324641673935565319315327927250279347254943312627598800515272029165946992258186452448481927397664927233885847309285090480118334116662415784675010753134669568456094649017086940432825205198591752669259201499364574626547697328005918168867930964379831353041571879642772510203031700766421587600773402269078488902194532374044405542145228497324312249871896810602262810164833160993785728113474672057513588475843349507467336200765615522898474337264574435679516530879187342364777991137286327558722605417250922482185141931502904679760557521660530076960465734117029054036967192210805525640289520234950287609695496799931281834839959754533497167259203288280521373224680040912579554734120911177849437506078377990778857440606854747861173473810005238792290497463642408156737104946525409732828379591601158228038670828754949018752131575170354580870083351174915890701732064086547224787901876532465034565174791761106784439698402722583267376079761231679594203997036827207344300878847240085230249014015427724647669334492751192536607892569768315337701737339932348393297299357855547824312749448478047346722046127223081976191883109317647669074975514758629178076021901330018779507689129153860218727794396470031859255402672696899657936060101963164996637263352441540799260073991494915796353183727612503054488542841741967610967743448998903044404269595583127959081790694701566273277101342720000000000000000000 /
        27553541463900082789041336914505118754685232556174037980347676065473344060325613761606066821437075314809480441771755302687929803474634680172618568729192036554938592028887287326190873654527516320580730360598472578278393382886554968333175351533255392440050857747855676945355096600773607133100660667781908634692645139934135486365375291623785826886234031634182586984386390462259118701902175378922148269134106641126216937056640240484850394312107130163353248938762153361933968446476620326731691815052718622803533336826920557600423241973892991084426743219749752176818526142394484452148559556048201526396615851612050546323495061679891440269052097419715378415323895169769287643801035151962271103616447708756601645082159052601299549521959750853718593992495704443330158053467367148504375332258827922828916327164813437658234216585710924991106792161818023102626597025222906164440481914153059559735615068618593489041978271909949479064603886403590961175354523885482180128116446320982021123976382875463772809097101571463144111735204585711299118544403283079629935931818918639145127894483256892844141749576843499330963077330429192641906204862700425174291761271134776813512459820524409884755148277767335181581740757901616659413339050460037382540984321315273597726614852370491533823954771304780909243501519305694890164357910730871817303648831367777170948969286141497188883898980544741681849309157358988576806411095041259468318099458718528678186520197965035267377726442760312703224503448813284047853510865317522526235186878378475251241795972550338349596076193574780314435563092311411054827198945115787403017722649069097215548327498916337294557898756173647256877323001513768322712627590369011447702002235252390944451418715232689831081497557943500612544860384276588646959840992580926231276385104635845659765624582437467980593689312042010848727030157421441697909236317981086772931463142737697377038728115329900343996049076591875277053732918633877462645981361445614398452695561746892192298526845863777016276924166281603169049789336232069383776528922600222998513518224213942453134293144054446472222325599311791670398725043208592513900002119302776315346079660175073063164505288805931649433201239237709278937102274249737280007340513734389713709309162248507971957626441764813630102826595227310421756337493894754446805594212817426387524408133000259392793768391865125935471511610447174110536129928127248099352844092711103546225411049700641650909765860396732292716960597757107227998411864663869206272201649894654073226807634501490631447707861877768704611768179520697467795460856628408627936760242312222709927788313993857408627497248032592058923428558880787674989955735531485781239713174409052965186387450290504605437832259310786951427817091108372837232143589791660322005831942791879198414267710391510711955592277255494841765450695826081955577062548195952318263623259981775201531645753089556360728510735082724300281620552440426819496901160722488278650024073077216132815707217240193696773969842661826490634882457856368551306094314477751561219045697613305612608953760238798092653222967403500471107926956758803087199266740283957326309109590856967888855551850613600833131087309286799495753614587605206649093091733142546124751320007166920954726073641103293108126001830188095211789031617953753642501094131115811106023772408854584355373366609498160323681486267276519436274249660390511025060941211048770211209425682685325275037283883413542436209358253559145607765336004378161325596485501910712366147134783620357358617417651643264873861387347760068553340423327404737408453619484762436947890348868042150112413336028004419246347026453932615870319904799322621766194651829511074323520678748917847507543677174952941709824483688126447382449334776955073523062642328061656429879153108123614518030030195319454057264598479196295229768618505523790250552019381270595782335514046978350802366990125334948439905046222754736298492138314783628590035388809091358908235348964540603074327623462065533640708387189024556104141619722936049569306085994621254380454786208452139866867782704600229231833218680130624614139282809242219761850730271485949259409284849874255020285610179484226776925124131293515813916371210041703792278762593622346828127977146770925096040866808366161451452405141563763869504680521023497986320332181188590062958252511375364290552875137624669181608902361495928013369666161489761864974052402913933935848143314444065965568312128352891217128460604469181017600501714130040692004144234390652493592624425395361250827654478759625620525308914390620930143170900105308067155186372614234992597621186257381469392777838994556896513362182940927712908792346767139153990550395335240847600071890526116700860439424926965686901510547766082754994340895375060254618952531375071356158865783702613352146659794879064175354505339689434191600576169561819392545264909446356584723236854737238598622040922070784208427101297046063814021801966099264001545063972000001871186049191360159707703001045187187691970049212261025379853223781656488492202528161534251908335121316600547832250356255951472860774856436512093644422579538521202381443846370744844587583481961887501570962710780245266263521531878727983864716580272275942045285234107007074838894718343244861933686451947187445444326487053019523172450205095773905307353729165981154183420112854505935355092710637477984882825427081667680663351564056112215307181650699212948165106333785410860143313102351399116744577365361130202540717080040321038653938329734973836001166365858585436954941507647870912896453222323908680137299524552482515595075124842948369142154198516036967208452737897566030702758507002107013890987979619496801315579683807148662701752345587175763139596703558727929315885219690734472666420033110079394562009267033172033071262012149235936475824363433283937950909208502829963878941452220505970305441210226794043393937428810478060485037654015142753705687200010137138702610185201844748390898848654513852425564539836939518087955798852718249906024622864308614586637449428992055137898995812284069957840579473879204529402609201387945476911452847066953385972439442014253929823413274412181264169424995574849316539177881255222705414773724952641587540851211534312977511436321804932277094149365233778265393584965207762189649758577742431470165983527536576506233194221367506495903954649093020607323651297797271560796046655238989700701673628757735360580353868002911932593542296083608077531529488841465213903917476455929640128885767110784153803730889479454547492926051363145607475956155000363188724099561154088962420490504451790741007087919447201280818058116265698439654014555652807499811789450717063318749699722756594163546338703164585135319885680710101904815165390746993004336014435706248220733362441872496540869675766927142030730668467848080063334218108876196748834169830673861132224139307283064514339189886004437647975582448585243877885519891439803828783068540570552982423364127328210541582443447597668991181327227599557458032558891216893667277459794025665321247426459841985256177454986784836924615663719122069914533203194875155931451015347549844472598963141488010706014706496623874599607163732612607945966952248964447380457409680889747022634049645784039893269278267819913197556953471424719565238385093764890503776514887630408888343300484476039130483641025016708696802800517271723911233174050077138679237064376174271629005659336127111355077731317353908096419798888509645268929083492610652776106360639955028092856409229243417481076531052145230505652541665900996441017463740087692399083325129303829111464490399046989561105757036110195663841615795598241086925189691729401202036162661641020150106007006809754092147566667438104700708614179169676323663997778234645332123269074344077087200168591392855618854240110962342576477622651965914888834570589671599801400661508303194762601469289716559568580556746589089615838861795977769294566666806169600018627193709789585912820104890766410898707448320243772136317190248300812890493605321686225175923841954212412545747429450067922851869062801784874893528514644510521461211878408468372093159716546364808666553831939731671229639725540951138492306057888259020027419231843222018001225058050721065658567971119266971412237745149408903163900870076510518802053349753622661238294090242568216924056643787029809639722258702589861636868754541624982906455681890888228519679664459783754486570555286871054602102377765113577625437760804032043422546210419051812365691357143080165103996898835184370468027215750851442541802743213770426909351468895846238003879369365084312154499771242176319385145760130752383141290636251513197736529052232708610272483673785087251936406815995480057910914792834912187313754057714528180212880033212688482818565633548154071102156753599749228302134614880176036926922536445788937234639773973265184855701075870832204351745833079571707467425063070330986012948102597963670925700673841182431626998665849991859684185644435110696305121402179266216490234762171149332803747055677251088192025064238914810559506096567222068774702985878035365942321698649528756184072779687120185852087146801167120182366546166505491608525474803456934846699801341130918180994069557366138052066079066581912282485302892348474557192528745964604616890537157758092772613895526049495532982920474872174415436479259828736176172752910597141444978503469818073937077195310293555252786384729300025968700722313108920441092598772914295346495356011845584582758366510149703183929167981184313808279399177234192193961977819713196110440342337585317547944123856279446378863273912166947108461523674651969814431776522075144648660739614716334800825948355709764346081170972338236469944391401925373619625362883515024883545080574501337725838595798928460454004544168130192673734415008055394963392176682799649855560046864136328608456181427135162405770281400165394572039735339747765410517395143454179717388936476302852016492882002750917206018593547584592540994539366414075137574461639979395541432911221589415810279855484670530873375298781845043784610985773977571937111205607965826067055752581613879962079762224513827698179252496091767630619182832452954044365355790621831218704385479015402226764554318607114781296299146942731576340387677890566235027002574317486938999113015781547256720333956460804374359083560897951749500226415907327402924196378232677888455337804088213270254728736860896228150371735601631679356980429156466308084536846312340464377065896725022722947673464566592715468530484583851101073214422037185608161956863876645914919455609371552864118704939616529921048358136287864567674919279336016576930227662235821262693910829855649152066579324690258820733562267828744693410784235784392713394531040701613345996650798739629020381266885122775928120359080053984463256445791234751269937892215416463417325392420369394506634689911939380140068412369123894683250187593417369543856459303697659996984946671590659272479376839056645167711489413007675041565123018079779680713413869533106735658561017818984124448856946817278368226508956720264585533457236271987175212112414234483495261682155762023589896687076998949350194978259446956866564095295433335900350682773222824101134167562466652026784599122016269785734003332223689138634083779730802850717030914916884286890056173236690963641099040325528466395327187744829398433618461766530711479000313536181084416112060441382220749895255528907648257493109616622468091502830233405121450824911588367557199985470908137518089546575787140559858000652461341876973045766749004831215420818841276216374527546451032669087609510763859020488281984622754511471824316056331746196037306225639648093809 : Rat) := by
  native_decide

theorem omegaPrimeCenterJetM15PrefixRat_128 :
    omegaPrimeCenterJetM15PrefixRat 128 =
      (515964260829411177021984342059785050599030115835662400292713673081163216001064002326151512323948171678661998008960213010455998864668834197048643424904689536102487287154207690818282547959079840472718987610944569701086826953207255974412431581629081350694780126069664070268108715773464229660504180194313100813890789354101823613330634594960112839005977759152331336974828357972749563905843538225181438661073638312381651900991369353591537708013078803835789102044499030112450889287659966073650287535642716892954559837143598185252858446755049946703155732339840947600099598186299040390305508858413979032352432557579889886379855776862802636614392788930648386934417038339099583271034670616640370334199231143416474346466592263918950952695585620561275575018649540428456580524177775180954664905090382708905209476364959366043056730993519929097256945875261663197896619846076902303733417254353987482188114250785208875381888809011174405845247520629003711272347896987730725142167148331430982826697855084145899472465302879653483632210672943993755703886440218726765651775766625648842006024830021190472851019916068067858797937349889764429198994492768057666156194834562229522927037357011456102174073374993957339987267400766983256371333099236391425962051560121809597738501176640007524025017596216883930234057154056389632470071996894846553760011139748079565727094327909310609398992183141762586305062824863653778704718784376730659801051066999629371269588700766568888872177690986286821419601817559467621440207212426696526972273542842872924818922760105844201799442494545453885117760481646212278866550667063323112439101498317119735455560612458351643143056280411430930107766182646221195298726863571480610901525558041404982071385788047021260771954342672506550942665053469137322247176922230985957156279183702257597427540311920711443182949799383189986637484887933541360019940398128264320289074435717267999103770640382296925566123875712820120821596992011935618258998654669951967024384893893925287962090370268008553499801879518679337388634325557973056911184830685071147651848307563377592669156985334507446097058402073098715794289576152694725665120284117967685078770592286116150768957794024820627635124518465400727621680253502247539304878089675839516800555410810500168666165181414327454059794581300521708011937341321995656251573089975055976265565829799213033975241062304285847084335409429641509373795344739210040002261844356569352531515233102469791285403039226689628948623047042437360787219615767047219275142362482093237011046982732181373275994112618823901968781229414997089753517648276348382705875349392802047036243592924053544593616739657254356926782468153944613127785208078079835436623013558329183094741287984360072257096624490349908118492501731816897883101193942858347165782577699790218852642039913080291273077604770890344963693671648022559239121622722408712192273864990395029717801620387599074440011398983133649923097919180164658957804572342812162389099247674860742870866429184318298508746044611972292136516612261367892065550190865473227386017046629535686309502510942795741276091167640756738051888272545066719537355998582404918808953394136796041282530135567091611481410959664223420530068147648342832204931597221276999236873606462723860362077565279774356062052853143269646120685112390778352742708734252250567710353840504919503025974182573014224022783956421024894053725827479251008818146599740626567657173020788939369133997859575435482381971065743222956829927336461613889827399950481735435536412495261847567836786997757669880332856755323155514517114031920915306190526284802181262810627988554492067631798879923803775111569985680465725490582219706540598892690050357165025180532709487492591603631286792978095400155484079080057991063928099577251965124193657133734030172643750291792506259464379324954515263509068246460901071813964034122885340254524705470763497120348074099468690302888741598666147035387151946679982707835804223716485151091699834227971030060358056710125928442993417293982524524478715140838011588743368645080900567190435206745103356605570835657062918019855403555823580679933216728796632343524399650242783166661449545191692893058826061878853687659996014779308325706308594499088731610624567099065988416924648315971385997625487604802879283161793821512464373670005601389477742884159629687964088978825007885880484650423715416829713732703768950241162235760083693035444542605411611423663126515574333813687375810791951609477248832024615996551789356586227347978162511516167805266002641625464607129002455240549859051558974644464399929912393480822022283145548524670013697527546753769007738572207552650992658432211613325089034302928301388839884451530473071954676614290950451278543397215374367763605229635010927026599885010632237255923308651612973712455826912227970108497570548303981733622516888494768635590510522520161251783814441837008446736298008690457274338563106237764429168230302063505252401833487202529835078715922262703069203426117807163136023110874728579472752973083919151321065980110422279756753145986029144010036562198916014617283959896393520744793503471983338583546811599447565306447736730707943786015803632940060393628659861772422328488891129783700715956251393866891456588258833080386643230341397042023183456080769891468708181589418047527488031837087463952797717767795784468168830716163587490677917922281654883022251944017393190663112597570249013144596912176947861046804832814762610249158757713873573068031482269762219184134538860817518586781049984116962629514032661562470428533018613902906901440736129415921433641353885750401932196581512157559440699163931298046269587576217257838319631110834886897037258301552633292752924296044469137226662807500757031660693485579433611204587928420384986635899081420092150122553542987845796317937418969065284873364814800752748332284333852033052136251155823781487650616866804595668985492775184771632161767639867824062424810433007746705601182458565086177108730757630153391297648340631896086309486337074009776706806783451464746993479755955557437046961769109786786456527690600408544136162767542413426672289447748707451729791660945516438415547969281270469166184362820300043120469304937163826199367881492150623789585255178629175061386533853055477348343659631298949272069398624231701798386365095183151017905483701778923853757764800697607668449966925301061010828716711186734738040257379422846488456644790060382015369964544718357627660694858880617751401760623101769533457854584915413872494767965595322623539989462916729150878764776056065397659843989190910181353542798672610730780917243692417638729777254244318754652897013691478695242172709400014925905739582063042922596630313836549838547885564156592749276414774351826817050002699560151874119728509760547592746204471955655199599596983226439185210425576893460635832117572781962883068707082797489539014785346697135599977056181926289769146129439531990335894391726484919931287061280277643038856931498008344474632996145267024869017988330438057369591527130701830785622743298541869888617469392103974777894013619670890346050080097548753313500324922299309375210070066851721533573415571927096110116881285476801711350718357588775489095899148330847477490453927756793626191734058461399076191358865236003152271200747509523418623458668478772104369246509415603246622107715475898081682834665276175396566465497461586403455966525965925842725005136747214234710719877318018308767650489683499816250672584251755053438875988150619513511405939385439634729141805333153991564332965080237746597227024683581836733193410566417620912495372323541889954705407461626479626103108695101376196084216035708414896038734469806543133473526677269013160650102741569804581952898567176298544517012728209372957468464545709246207172933480797989905103183258503213098840872821264091966402758354127393895916876234752008860497274054076665704325077792999805979642200562461346208433781724776009105181580402325308329491463703037956552243814052223276629063660648114092196297468785280258181613039363246627303618999039521590848977895407126296091655621572925491589281300504091636174784387361122277819545102562006769048348541058448509790656074390209102860883243179713442676431454653338331666713809892411606276242015125146108855347627519570567214591491783722863157192562038167678321109231430842616143150955202666050365765249843701789516609614933917643880813721549763750219795665580433999866121380910007179450170738502449173241502411964597118880721101839584190895952857458152016841923598255082747760385939907787460893476883487656332371133850216371088766423265058530825897450787140617414877747966571819672870915924303100949322257978874900360347401323238696163852675544068047969251441179490583570397057338855747659292842173246309131452196716947359269289686159446841333075516716380708037197413255463124598806141473897479438011747606945306745835502606925710412249633037414526666559704542772751294857204825392820033783330259871491331364165709764961788329410027037044104015290886237320572140422382779408187618645246749034638720809115352950740974378456169183878773265843678248169457189237673580811451141794061243772188668621164132801885380957095476025949712912871862672100758790742977725375259352646695983831699776116752234197435167453174719187996547928054372765705022859874076448776886625959218057831771817650197917411144783391416052081865536486900574848965141932856413635634672566119229958201730198668293998211061118215913161597230380433546048095638332748666746457261963523645401496803537756753164225903403219620260353907009108826733636727677497683998857089727946398582628455973621478786526549705958146211537340748947332523306869646878177356109083355332427296220985976472219186103992752526706101586174847027705747028040424054439103204492127325778749875816444472909553986714236217100470408286991319724364871500688002662153826314402666173938307227258922471084629209910923223777550712415995190712529943010804336604491212663686929645025715207743310298817128520635086027938189258548866679172442816225882657621933979522365951223944999033193864412821470293244965187602208691603125732106598909868154732044041145495032436173547957148704360626026385589358439715607575202603019876647170911548005843746345617972337261769773292115839339231693938035918992771411671103049536353664299558768031039051165535609376006862472646348470889250390913843636268243613739741550040001649722174768298350565372966378778736788962856299989379782141671746995014335486930079286539201152274975765907542161283872791018734004852966517736121427526391948190986353041026633745611191011039607193072270005301880336316899893041956186957439070760182539557071976520500556668319531250967119002617772654291441830480175858977044197013665189671523741160924967389778780053914064779306539172864005758752267351458117825320506454490234399254951845479663988143591064876701613953783528335987013670450446213084691360712372361856000646471125087980859694951256301389450744894714592731792572705309938713773935366349659699364035568813241176560709776763798653576685553963157956678036424146465175262322759714560801200101287096530096943697455955814950210482850656816472135129045033089939496031714973256486350393464765731735971432331122928364423833759768078587072444033075386550982761736944666902710565998382850826560440477667518766542712154798719823936935576111893326423350499078805168992096444934521345611514675192174359307875953298625975431876367505780311867244447648617870116515177247319827832336827537816150169748421262119345891822873816879776387769061548235653682122259744741637512635447460866757168533135902478355857865055969509170311413902326735232284687212881238761549903668217279143261997903876812213516480402631060684929160540859367254101105217628041773515021950441628977498039188136731159341833393789059779220568205205036919743137119702904424606668168350944606151312615438652024389474274060974644258155307677854489389798629739208768998179347488487554058709294709616712127034422907596703810378846724071151936840838739537811886959384417506560427104731256234938406875434070193106004458319427539429396818110364706355768345239080070020322062687131389586503562612547746331707315409597495651895452752038167800135061174673913415850875673231882357204106001738134174374760627990051137651570724943983100419072275078898007558251783121684945046574442075452866560000000000000000000 /
        1086129173710212251815716409447644851369269733497310683044707917612574347686474642886190282810101726265616695161037673838429306788535362969399204556958177695776878561082728345582307323664401958293470193332951198672525173761634403319641824673706650120822741320057400996917857094649217610887530664607729291828174557060779811941589167667253791740729281223561981079496224420512469074664048896097477307802860640966329113417401458875936980672435875279826314536391053065877543189756891652871133063776969606371027884454902615965336583218267595412007170315712908740460234668936104641467432824721339254559901926213904343643134865022095083638140656470660740989505370955347393643537732823160229082048833692403527563293962175832799786143484670934644597399944065627857411415153895320090794326769514875253872978973531989073142240277190290573738516849364518767750486734956478328200610008541872175096074982441038941419735992917965615629804741005218615448431247050451568300921344893109770761527762578724566602772644154244224749682705700652006091246225385388205385273775885378750789572203330790780262908655957314081609878554099158918381577260540214239798606220331315431928059901057328572389300656724918119991031228249083198090492308661068304910401676817973947287433597465788436504523090746998959346652943756614917917066772624353803266639968479972603556729376734670787017090975757044842501877760010347479605896774459996641630302326078950298365100501003139727421306749351473713230114856096907128904320343275440196310710285430173655250412554993524615875393253195884331379070196082073927696818328367466495231466825080134520433593928319547818255560238761808791390749495899862166942535117198379882681231685671941178794682733252733952910847933047140502392799759154492350944062350151025603375014643598009386800787153698577856957825046141817639617573859849935808399581609148399129863099875985729458440459373284674127556189643531918278471457480658551007672092699852686852633650625407569420019982624024131745571722651434003170431201340143279676276618515813807555326451553541212403416970072462016044719483414575010652453864905663327313911006789791755868557724759397343219822530616655527878048989529886063040130326511576928115589442478201546391789900081955887187165494086948354700441846058597753728366704667310091422961225928781443508530251738030926681612933451298653813926764686828505009619652510706632679287407428139848103077233584106350183387280608674334058824845430337787548066040604428594461707343184105540969186325964780969340371157279017735140464041602814127339145310676289244835014320498728115574626651917581461201048292348296909831267272979966633177528776692913406407602503539704949271742465869933918142072543699911915916321258401545060358001540835908266623601312500783506874543960444870393834230660607183098366033930278880709464686807021000097082729343955213223471750964887213662649027162061621348742643951952343876936697318109548914468650942355157837170079347470991250198135898696011855953168062656529458552989786926788594053501639244673531471517923291183252162427825929506073430031218357892793602953020227843320338556742929717485419633658090525678690929033206736251980577819391875032704086226361809270073054811364601498181879522808951649137201719854274685384302512919928173477883182953730907469512294860682921331361834252956205329946855843542424441136167620302616039242192838645484008246309749763584903080241363992493183547812667304447780417568724980442040091840511300798911109406356833782714405195108928095352593005190628320608287927957586172916382181777684379721557261001176277732360680017407289232044439433477542680238621383813636267212622693802518038239813451182147268747651136880922135065096933741338133407440051203310575433051759893101687001043409486895917852131809998741903433263948823256009265417724429666652030042566299958339757378437151661863695602245403866134774740051949844754141542740304731364348808393666410055548867383377397795358199061269148214162100991841033889236396127108900784188809054483813294814771725769751587746130240877843100393604266498399164424040194067211133570548247841867314586480493665058291901273492713354406422260989527875050162593627430316679311781119441779341738264497523810483053763237587086490746548125742273937602953005891544539654516536816377111475947548857854665037501272997415884367102337918556623309231401566328591536211982014017251212958321525720678234542230513226572475942528537321699587647542894216526402404987550539939104674798296441860468516296508327281166882944307217343961793252708728943529331241776367233788802917137670395069781943067749147258811886920465967722704126602456319884703324860158101087127765110481702318213064164436419309689657465319013837981680797815769102693955632362192873033157637773232214683301403910758990452596887696544553237956902296224474568676847090925500600332438968114176197234974489856186101827927947873219078354076874665317319926503087989030337039619471367968489165175000069248693678949167262562360559413961093853686195259458349277635073148429650768139570007537282092634672922069567607759378806612104860629034232731224852918391390934148018410586885329819713680424097785600650148314990400596425722138343089844195671700482865994902094144085245637246700640533529862608834898639497111122582471867521507255295769343380563518282297664655702297557684318869056368148040375627731611667332531634296607903839008070061202960066718556154270164469440335749707607862456594833874018708565458451242917724271329202696050323818021283479205939882595995759301899542601113084935171396344347136842248774264713981119775757114222508970863591150213556135765758876060109124746010470447575264683763505664775483101437297371144420652979309017997709993508089477532805593971127361125650099798194262847271346183778045641689626568029919988170514348190874708042190104713719915865130013641788488253479043687721094803558825182412129520823541300493413498521652836994241343981532498443456757277138343630431126648009394646776461421679036895677103562250259444766242091922990720776520537118899897268766650775014830241432695415914054759591517232346721626165894343968665866463231208814606276095173701660880946244177311770953690339488841215454617091832463279843137392496635793750779122567540849783359255552017794164103076929076088819440690431409071611332115352127854379889607366297034562255981621796329806727332429495571936382961781100542520265967224509678575007934619566649070090791308705471291933828449183699264724701744483019173444682705796728295492088241297729530048480693245951959961815273444883949422885124084772945517261594685049746927288617926635195994384909011150170519624656117146441823543003309387848519830804893881971294301061727270965453080736520008338803950862074022166282006182557867616738832993645271812536665607544047461045935221360517243639546097236131808782954245321149367706822767195749081779299749723261463237569743805812457947932802847328254292558233938383379636820845402911945636913041029852752342665863685553826919001919767908657556784058297291030950866720645503242254493597236057924096880482700795368567843571734410373494300513226349038183250077711892235398225746102156377277309768894080233421621991445805728380211188066926139347053968768475246118677080549331702773594675618635369343275901307074204818687648895960176231685074148846529070221146759334946507659752911302514221150237097540753173915930854263631360764084248238536874272615508215605421753198163553946220405050882681704365972504233514095793994862866459958993073701524787531880611008981667971622784406675717551249599258334556165219897613400218649437831948082531169617660993413469387435111045935731715379956143125555460908613828398521017059822734537611672287412467185807147792956616269648946005260660041103931635650273874848192718613630749134570163411997809915594928482238401501896235497844737598669545965430272311965003134832680021002188404775280537196556391971052416373666915808768827199063604921502588684123430286035066141380827155756285822357665495769774635776445146985113283794539319265923434148003925031050041540844529123310432021051774655244404375776327405842075552066811342296074849435758737390900231111949572515099338107899446283580694733104837944078033882454624951255928836041988445371036965565949925167725277854963705013956604352743236281925242244412459840979806283152736360766154931666838543242139250794546724382724438409650885278565345314703209513564502984805642719050426721819266324452421103847141994726841767604838406108678093450048750138584661336991974900903609440603374686590828091681292594576477323759135804326892744836463681597630607452422302318560877857015089116287197332966399386975928785885732881095645958806577594415305582753961817871179381182029564544063375328810039455299943747265740015890810406098847508045361815104509416093670789852198389622721392918673269412219690293003736142622479764460828800141897843477435628961007571873035332506508553525249962192869497899860034040823723597914485847588838610130096478007998590922039051690723493306520198528891667223030854543051088615070139594066345837262153744578485340751455000991261899514605644999010416022218287357224738759853359570460259703046723232324037927186669999312134421712991668718258513185249451763404911232308281274614542521705056225266770230967455860283165898167009891841043350385608499495238163641991045538145578947707302093321838051145758368421299812284441889090619090705057685509433985302737995014803720535267874971997830898561235762910990580573741327522971264761018317961975812695505743437669014396361519044649048109312062680504455513421305092889077441065926656124837189968627830255291785585574738323795435007298437506611934298283360064466525887397911528747855847802918594844609729068464755518012670785244648032023810082164739367743050669009478997121364642801887180468152186788413778125689319427966575411809459202648069391625495859859583741098930657696509368664267715265792682177145779592984094375862204014215179470824415822463360306438219702234247003177202291149990688469609729275062955579331747358062245980310336528848805457831079958615006908153503670532215182445679329969048942274971322972944857071191452765754924566607748846581557365441214652555162055257630470121737563028428919249347322559449603109243850239637724087618850813388565491881867859698704920689261340300522502035128585122064200742058265468469507753888741307364268367763461787910734539160264156225386285632332459382998319913898204208477711083560846227361455054783426060861194637610384025397501178358633146494697446787644095108116668301995222900761431719303373944197573695658648731668236652653136651681473916799929879098333725125382790675231080569623174336130205138209644314659960200895342871045008637976465226422268824544209866967271627203275882494877803759050844144292791526428697116307773563800353930350361980247596586779994901465593736156696956674455079706540293989219699377137874785732436995406414323824423294979075312236984607479611004538798749507431020737727839153584222477420233973118914194293609855767164112209081108208425923197777147084102963725033528951415860403059863571700955985846868249344076949660878569101668217056663279121015068636073941832089515811745647427153815699057957700644041501713312003691444404650092697352678637199065788386910391152741965415124835017062734009674058541633947436426807133024538810281404121158561432877377333736478770089985946748371598383211265814497316740997030314500857008308965397410177350456399606405330916381642140427011861700198691147183559433140347171708936957429555070357489806627695934292133568179321025876827841965108234349154565150641135842975220481939212233698555312325832296503846213471610435804560373194280615914780095482173723745509122967035374539316868240754551190201288177138298973289540083048119901029673020140012188710292743620832337959005123448867181794992053476616545939897696339041167239771986219241216882592975214929640679461719932511947264394152980796755702539669403493886138463461167521048360417746161863829645236198568160858018407079651776328114201672161062840233448142639492579976365340360098565992321080679388567396646138431363286541328267656372153793581661298873711392558344432332887511907774380720937125156020513379387767942008030479199672261943657753063450092312813686789451457497 : Rat) := by
  native_decide


theorem omegaPrimeCenterJetM0TermRat_cast (n : Nat) :
    iteratedDeriv 0
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM0TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM0TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  rw [zpow_two]
  simp [Complex.add_re, Complex.add_im, Complex.I_re, Complex.I_im,
    Complex.mul_re, Complex.mul_im]
  ring_nf
  have hden :
      (101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 2 =
        10201 / 2560000 + (n : Real) * (101 / 1600) +
          (n : Real) ^ 2 * (301 / 800) + (n : Real) ^ 3 +
            (n : Real) ^ 4 := by
    ring_nf
  rw [← hden]
  rfl

theorem omegaPrimeCenterJetM1TermRat_cast (n : Nat) :
    iteratedDeriv 1
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM1TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM1TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_three, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im, Complex.mul_re, Complex.mul_im]
  rw [← pow_three]
  have hnum :
      (((n : Complex) + (1 / 4 : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 3).re =
        (n : Real) ^ 3 + (n : Real) ^ 2 * (3 / 4) +
          (n : Real) * (297 / 1600) + 97 / 6400 := by
    norm_num [pow_three, Complex.add_re, Complex.add_im, Complex.I_re,
      Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    -((((n : Complex) + (1 / 4 : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 3).re /
        (((n : Real) + 1 / 4) * ((n : Real) + 1 / 4) + 1 / 1600) ^ 3) =
        -(((n : Real) ^ 3 + (n : Real) ^ 2 * (3 / 4) +
            (n : Real) * (297 / 1600) + 97 / 6400) /
          (((n : Real) + 1 / 4) * ((n : Real) + 1 / 4) + 1 / 1600) ^ 3) := by
      exact congrArg
        (fun y : Real =>
          -(y / (((n : Real) + 1 / 4) * ((n : Real) + 1 / 4) + 1 / 1600) ^ 3))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM2TermRat_cast (n : Nat) :
    iteratedDeriv 2
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM2TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM2TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 4).im =
        (n : Real) ^ 3 * (1 / 10) + (n : Real) ^ 2 * (3 / 40) +
          (n : Real) * (299 / 16000) + 99 / 64000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 4).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 4)⁻¹ *
          (3 / 2) =
        ((n : Real) ^ 3 * (1 / 10) + (n : Real) ^ 2 * (3 / 40) +
            (n : Real) * (299 / 16000) + 99 / 64000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 4)⁻¹ *
            (3 / 2) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 4)⁻¹ *
            (3 / 2))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM3TermRat_cast (n : Nat) :
    iteratedDeriv 3
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM3TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM3TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 5).re =
        (n : Real) ^ 5 + (n : Real) ^ 4 * (5 / 4) +
          (n : Real) ^ 3 * (99 / 160) + (n : Real) ^ 2 * (97 / 640) +
            (n : Real) * (9401 / 512000) + 1801 / 2048000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 5).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 5)⁻¹ *
          3 =
        ((n : Real) ^ 5 + (n : Real) ^ 4 * (5 / 4) +
            (n : Real) ^ 3 * (99 / 160) + (n : Real) ^ 2 * (97 / 640) +
              (n : Real) * (9401 / 512000) + 1801 / 2048000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 5)⁻¹ *
            3 := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 5)⁻¹ * 3)
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM4TermRat_cast (n : Nat) :
    iteratedDeriv 4
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM4TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM4TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 6).im =
        (n : Real) ^ 5 * (3 / 20) + (n : Real) ^ 4 * (3 / 16) +
          (n : Real) ^ 3 * (299 / 3200) + (n : Real) ^ 2 * (297 / 12800) +
            (n : Real) * (147003 / 51200000) + 29003 / 204800000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 6).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 6)⁻¹ *
          (-15 / 2) =
        ((n : Real) ^ 5 * (3 / 20) + (n : Real) ^ 4 * (3 / 16) +
            (n : Real) ^ 3 * (299 / 3200) + (n : Real) ^ 2 * (297 / 12800) +
              (n : Real) * (147003 / 51200000) + 29003 / 204800000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 6)⁻¹ *
            (-15 / 2) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 6)⁻¹ *
            (-15 / 2))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM5TermRat_cast (n : Nat) :
    iteratedDeriv 5
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM5TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM5TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 7).re =
        (n : Real) ^ 7 + (n : Real) ^ 6 * (7 / 4) +
          (n : Real) ^ 5 * (2079 / 1600) +
            (n : Real) ^ 4 * (679 / 1280) +
              (n : Real) ^ 3 * (65807 / 512000) +
                (n : Real) ^ 2 * (37821 / 2048000) +
                  (n : Real) * (5960493 / 4096000000) +
                    793493 / 16384000000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 7).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 7)⁻¹ *
          (-45 / 2) =
        ((n : Real) ^ 7 + (n : Real) ^ 6 * (7 / 4) +
            (n : Real) ^ 5 * (2079 / 1600) +
              (n : Real) ^ 4 * (679 / 1280) +
                (n : Real) ^ 3 * (65807 / 512000) +
                  (n : Real) ^ 2 * (37821 / 2048000) +
                    (n : Real) * (5960493 / 4096000000) +
                      793493 / 16384000000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 7)⁻¹ *
            (-45 / 2) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 7)⁻¹ *
            (-45 / 2))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM6TermRat_cast (n : Nat) :
    iteratedDeriv 6
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM6TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM6TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 8).im =
        (n : Real) ^ 7 * (1 / 5) + (n : Real) ^ 6 * (7 / 20) +
          (n : Real) ^ 5 * (2093 / 8000) +
            (n : Real) ^ 4 * (693 / 6400) +
              (n : Real) ^ 3 * (343007 / 12800000) +
                (n : Real) ^ 2 * (203021 / 51200000) +
                  (n : Real) * (6652099 / 20480000000) +
                    930699 / 81920000000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 8).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 8)⁻¹ *
          (315 / 4) =
        ((n : Real) ^ 7 * (1 / 5) + (n : Real) ^ 6 * (7 / 20) +
            (n : Real) ^ 5 * (2093 / 8000) +
              (n : Real) ^ 4 * (693 / 6400) +
                (n : Real) ^ 3 * (343007 / 12800000) +
                  (n : Real) ^ 2 * (203021 / 51200000) +
                    (n : Real) * (6652099 / 20480000000) +
                      930699 / 81920000000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 8)⁻¹ *
            (315 / 4) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 8)⁻¹ *
            (315 / 4))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM7TermRat_cast (n : Nat) :
    iteratedDeriv 7
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM7TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM7TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 9).re =
        (n : Real) ^ 9 + (n : Real) ^ 8 * (9 / 4) +
          (n : Real) ^ 7 * (891 / 400) +
            (n : Real) ^ 6 * (2037 / 1600) +
              (n : Real) ^ 5 * (592263 / 1280000) +
                (n : Real) ^ 4 * (113463 / 1024000) +
                  (n : Real) ^ 3 * (17881479 / 1024000000) +
                    (n : Real) ^ 2 * (7141437 / 4096000000) +
                      (n : Real) * (654274809 / 6553600000000) +
                        65251609 / 26214400000000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 9).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 9)⁻¹ *
          315 =
        ((n : Real) ^ 9 + (n : Real) ^ 8 * (9 / 4) +
            (n : Real) ^ 7 * (891 / 400) +
              (n : Real) ^ 6 * (2037 / 1600) +
                (n : Real) ^ 5 * (592263 / 1280000) +
                  (n : Real) ^ 4 * (113463 / 1024000) +
                    (n : Real) ^ 3 * (17881479 / 1024000000) +
                      (n : Real) ^ 2 * (7141437 / 4096000000) +
                        (n : Real) * (654274809 / 6553600000000) +
                          65251609 / 26214400000000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 9)⁻¹ *
            315 := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 9)⁻¹ *
            315)
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM8TermRat_cast (n : Nat) :
    iteratedDeriv 8
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM8TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM8TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 10).im =
        (n : Real) ^ 9 * (1 / 4) + (n : Real) ^ 8 * (9 / 16) +
          (n : Real) ^ 7 * (897 / 1600) +
            (n : Real) ^ 6 * (2079 / 6400) +
              (n : Real) ^ 5 * (3087063 / 25600000) +
                (n : Real) ^ 4 * (609063 / 20480000) +
                  (n : Real) ^ 3 * (19956297 / 4096000000) +
                    (n : Real) ^ 2 * (8376291 / 16384000000) +
                      (n : Real) * (817256401 / 26214400000000) +
                        88250801 / 104857600000000 := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 10).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 10)⁻¹ *
          (-2835 / 2) =
        ((n : Real) ^ 9 * (1 / 4) + (n : Real) ^ 8 * (9 / 16) +
            (n : Real) ^ 7 * (897 / 1600) +
              (n : Real) ^ 6 * (2079 / 6400) +
                (n : Real) ^ 5 * (3087063 / 25600000) +
                  (n : Real) ^ 4 * (609063 / 20480000) +
                    (n : Real) ^ 3 * (19956297 / 4096000000) +
                      (n : Real) ^ 2 * (8376291 / 16384000000) +
                        (n : Real) * (817256401 / 26214400000000) +
                          88250801 / 104857600000000) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 10)⁻¹ *
            (-2835 / 2) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 10)⁻¹ *
            (-2835 / 2))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM9TermRat_cast (n : Nat) :
    iteratedDeriv 9
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM9TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM9TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 11).re =
        (n : Real) ^ 11 * (1 : Real)
          + (n : Real) ^ 10 * (11 / 4 : Real)
          + (n : Real) ^ 9 * (1089 / 320 : Real)
          + (n : Real) ^ 8 * (3201 / 1280 : Real)
          + (n : Real) ^ 7 * (310233 / 256000 : Real)
          + (n : Real) ^ 6 * (416031 / 1024000 : Real)
          + (n : Real) ^ 5 * (196696269 / 2048000000 : Real)
          + (n : Real) ^ 4 * (26185269 / 1638400000 : Real)
          + (n : Real) ^ 3 * (2399007633 / 1310720000000 : Real)
          + (n : Real) ^ 2 * (717767699 / 5242880000000 : Real)
          + (n : Real) * (62786949489 / 10485760000000000 : Real)
          + (4825396489 / 41943040000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 11).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 11)⁻¹ *
          (-14175 / 2 : Real) =
        ((n : Real) ^ 11 * (1 : Real)
         + (n : Real) ^ 10 * (11 / 4 : Real)
         + (n : Real) ^ 9 * (1089 / 320 : Real)
         + (n : Real) ^ 8 * (3201 / 1280 : Real)
         + (n : Real) ^ 7 * (310233 / 256000 : Real)
         + (n : Real) ^ 6 * (416031 / 1024000 : Real)
         + (n : Real) ^ 5 * (196696269 / 2048000000 : Real)
         + (n : Real) ^ 4 * (26185269 / 1638400000 : Real)
         + (n : Real) ^ 3 * (2399007633 / 1310720000000 : Real)
         + (n : Real) ^ 2 * (717767699 / 5242880000000 : Real)
         + (n : Real) * (62786949489 / 10485760000000000 : Real)
         + (4825396489 / 41943040000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 11)⁻¹ *
            (-14175 / 2 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 11)⁻¹ *
            (-14175 / 2 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM10TermRat_cast (n : Nat) :
    iteratedDeriv 10
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM10TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM10TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 12).im =
        (n : Real) ^ 11 * (3 / 10 : Real)
          + (n : Real) ^ 10 * (33 / 40 : Real)
          + (n : Real) ^ 9 * (3289 / 3200 : Real)
          + (n : Real) ^ 8 * (9801 / 12800 : Real)
          + (n : Real) ^ 7 * (4851099 / 12800000 : Real)
          + (n : Real) ^ 6 * (6699693 / 51200000 : Real)
          + (n : Real) ^ 5 * (658557801 / 20480000000 : Real)
          + (n : Real) ^ 4 * (92139201 / 16384000000 : Real)
          + (n : Real) ^ 3 * (8989820411 / 13107200000000 : Real)
          + (n : Real) ^ 2 * (2912276433 / 52428800000000 : Real)
          + (n : Real) * (281876116497 / 104857600000000000 : Real)
          + (24696025497 / 419430400000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 12).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 12)⁻¹ *
          (155925 / 4 : Real) =
        ((n : Real) ^ 11 * (3 / 10 : Real)
         + (n : Real) ^ 10 * (33 / 40 : Real)
         + (n : Real) ^ 9 * (3289 / 3200 : Real)
         + (n : Real) ^ 8 * (9801 / 12800 : Real)
         + (n : Real) ^ 7 * (4851099 / 12800000 : Real)
         + (n : Real) ^ 6 * (6699693 / 51200000 : Real)
         + (n : Real) ^ 5 * (658557801 / 20480000000 : Real)
         + (n : Real) ^ 4 * (92139201 / 16384000000 : Real)
         + (n : Real) ^ 3 * (8989820411 / 13107200000000 : Real)
         + (n : Real) ^ 2 * (2912276433 / 52428800000000 : Real)
         + (n : Real) * (281876116497 / 104857600000000000 : Real)
         + (24696025497 / 419430400000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 12)⁻¹ *
            (155925 / 4 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 12)⁻¹ *
            (155925 / 4 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM11TermRat_cast (n : Nat) :
    iteratedDeriv 11
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM11TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM11TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 13).re =
        (n : Real) ^ 13 * (1 : Real)
          + (n : Real) ^ 12 * (13 / 4 : Real)
          + (n : Real) ^ 11 * (3861 / 800 : Real)
          + (n : Real) ^ 10 * (13871 / 3200 : Real)
          + (n : Real) ^ 9 * (1344343 / 512000 : Real)
          + (n : Real) ^ 8 * (2317887 / 2048000 : Real)
          + (n : Real) ^ 7 * (365293071 / 1024000000 : Real)
          + (n : Real) ^ 6 * (340408497 / 4096000000 : Real)
          + (n : Real) ^ 5 * (93561297687 / 6553600000000 : Real)
          + (n : Real) ^ 4 * (9330980087 / 5242880000000 : Real)
          + (n : Real) ^ 3 * (816230343357 / 5242880000000000 : Real)
          + (n : Real) ^ 2 * (188190463071 / 20971520000000000 : Real)
          + (n : Real) * (5051552264213 / 16777216000000000000 : Real)
          + (289796841413 / 67108864000000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 13).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 13)⁻¹ *
          (467775 / 2 : Real) =
        ((n : Real) ^ 13 * (1 : Real)
         + (n : Real) ^ 12 * (13 / 4 : Real)
         + (n : Real) ^ 11 * (3861 / 800 : Real)
         + (n : Real) ^ 10 * (13871 / 3200 : Real)
         + (n : Real) ^ 9 * (1344343 / 512000 : Real)
         + (n : Real) ^ 8 * (2317887 / 2048000 : Real)
         + (n : Real) ^ 7 * (365293071 / 1024000000 : Real)
         + (n : Real) ^ 6 * (340408497 / 4096000000 : Real)
         + (n : Real) ^ 5 * (93561297687 / 6553600000000 : Real)
         + (n : Real) ^ 4 * (9330980087 / 5242880000000 : Real)
         + (n : Real) ^ 3 * (816230343357 / 5242880000000000 : Real)
         + (n : Real) ^ 2 * (188190463071 / 20971520000000000 : Real)
         + (n : Real) * (5051552264213 / 16777216000000000000 : Real)
         + (289796841413 / 67108864000000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 13)⁻¹ *
            (467775 / 2 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 13)⁻¹ *
            (467775 / 2 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM12TermRat_cast (n : Nat) :
    iteratedDeriv 12
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM12TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM12TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 14).im =
        (n : Real) ^ 13 * (7 / 20 : Real)
          + (n : Real) ^ 12 * (91 / 80 : Real)
          + (n : Real) ^ 11 * (27209 / 16000 : Real)
          + (n : Real) ^ 10 * (99099 / 64000 : Real)
          + (n : Real) ^ 9 * (49050001 / 51200000 : Real)
          + (n : Real) ^ 8 * (87096009 / 204800000 : Real)
          + (n : Real) ^ 7 * (2853750471 / 20480000000 : Real)
          + (n : Real) ^ 6 * (2794889097 / 81920000000 : Real)
          + (n : Real) ^ 5 * (818073657401 / 131072000000000 : Real)
          + (n : Real) ^ 4 * (88339051801 / 104857600000000 : Real)
          + (n : Real) ^ 3 * (8550242200409 / 104857600000000000 : Real)
          + (n : Real) ^ 2 * (2247338320227 / 419430400000000000 : Real)
          + (n : Real) * (71868937995407 / 335544320000000000000 : Real)
          + (5278393991807 / 1342177280000000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 14).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 14)⁻¹ *
          (-6081075 / 4 : Real) =
        ((n : Real) ^ 13 * (7 / 20 : Real)
         + (n : Real) ^ 12 * (91 / 80 : Real)
         + (n : Real) ^ 11 * (27209 / 16000 : Real)
         + (n : Real) ^ 10 * (99099 / 64000 : Real)
         + (n : Real) ^ 9 * (49050001 / 51200000 : Real)
         + (n : Real) ^ 8 * (87096009 / 204800000 : Real)
         + (n : Real) ^ 7 * (2853750471 / 20480000000 : Real)
         + (n : Real) ^ 6 * (2794889097 / 81920000000 : Real)
         + (n : Real) ^ 5 * (818073657401 / 131072000000000 : Real)
         + (n : Real) ^ 4 * (88339051801 / 104857600000000 : Real)
         + (n : Real) ^ 3 * (8550242200409 / 104857600000000000 : Real)
         + (n : Real) ^ 2 * (2247338320227 / 419430400000000000 : Real)
         + (n : Real) * (71868937995407 / 335544320000000000000 : Real)
         + (5278393991807 / 1342177280000000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 14)⁻¹ *
            (-6081075 / 4 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 14)⁻¹ *
            (-6081075 / 4 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM13TermRat_cast (n : Nat) :
    iteratedDeriv 13
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM13TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM13TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 15).re =
        (n : Real) ^ 15 * (1 : Real)
          + (n : Real) ^ 14 * (15 / 4 : Real)
          + (n : Real) ^ 13 * (2079 / 320 : Real)
          + (n : Real) ^ 12 * (8827 / 1280 : Real)
          + (n : Real) ^ 11 * (2566473 / 512000 : Real)
          + (n : Real) ^ 10 * (5408403 / 2048000 : Real)
          + (n : Real) ^ 9 * (852350499 / 819200000 : Real)
          + (n : Real) ^ 8 * (1021225491 / 3276800000 : Real)
          + (n : Real) ^ 7 * (93561297687 / 1310720000000 : Real)
          + (n : Real) ^ 6 * (65316860609 / 5242880000000 : Real)
          + (n : Real) ^ 5 * (17140837210497 / 10485760000000000 : Real)
          + (n : Real) ^ 4 * (1317333241497 / 8388608000000000 : Real)
          + (n : Real) ^ 3 * (35360865849491 / 3355443200000000000 : Real)
          + (n : Real) ^ 2 * (6085733669673 / 13421772800000000000 : Real)
          + (n : Real) * (56138078997297 / 5368709120000000000000 : Real)
          + (1631181003097 / 21474836480000000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 15).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 15)⁻¹ *
          (-42567525 / 4 : Real) =
        ((n : Real) ^ 15 * (1 : Real)
         + (n : Real) ^ 14 * (15 / 4 : Real)
         + (n : Real) ^ 13 * (2079 / 320 : Real)
         + (n : Real) ^ 12 * (8827 / 1280 : Real)
         + (n : Real) ^ 11 * (2566473 / 512000 : Real)
         + (n : Real) ^ 10 * (5408403 / 2048000 : Real)
         + (n : Real) ^ 9 * (852350499 / 819200000 : Real)
         + (n : Real) ^ 8 * (1021225491 / 3276800000 : Real)
         + (n : Real) ^ 7 * (93561297687 / 1310720000000 : Real)
         + (n : Real) ^ 6 * (65316860609 / 5242880000000 : Real)
         + (n : Real) ^ 5 * (17140837210497 / 10485760000000000 : Real)
         + (n : Real) ^ 4 * (1317333241497 / 8388608000000000 : Real)
         + (n : Real) ^ 3 * (35360865849491 / 3355443200000000000 : Real)
         + (n : Real) ^ 2 * (6085733669673 / 13421772800000000000 : Real)
         + (n : Real) * (56138078997297 / 5368709120000000000000 : Real)
         + (1631181003097 / 21474836480000000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 15)⁻¹ *
            (-42567525 / 4 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 15)⁻¹ *
            (-42567525 / 4 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM14TermRat_cast (n : Nat) :
    iteratedDeriv 14
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM14TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM14TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 16).im =
        (n : Real) ^ 15 * (2 / 5 : Real)
          + (n : Real) ^ 14 * (3 / 2 : Real)
          + (n : Real) ^ 13 * (2093 / 800 : Real)
          + (n : Real) ^ 12 * (9009 / 3200 : Real)
          + (n : Real) ^ 11 * (13377273 / 6400000 : Real)
          + (n : Real) ^ 10 * (29032003 / 25600000 : Real)
          + (n : Real) ^ 9 * (951250157 / 2048000000 : Real)
          + (n : Real) ^ 8 * (1197809613 / 8192000000 : Real)
          + (n : Real) ^ 7 * (116867665343 / 3276800000000 : Real)
          + (n : Real) ^ 6 * (88339051801 / 13107200000000 : Real)
          + (n : Real) ^ 5 * (25650726601227 / 26214400000000000 : Real)
          + (n : Real) ^ 4 * (2247338320227 / 20971520000000000 : Real)
          + (n : Real) ^ 3 * (71868937995407 / 8388608000000000000 : Real)
          + (n : Real) ^ 2 * (15835181975421 / 33554432000000000000 : Real)
          + (n : Real) * (1074391491360499 / 67108864000000000000000 : Real)
          + (67659212273499 / 268435456000000000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 16).im *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 16)⁻¹ *
          (638512875 / 8 : Real) =
        ((n : Real) ^ 15 * (2 / 5 : Real)
         + (n : Real) ^ 14 * (3 / 2 : Real)
         + (n : Real) ^ 13 * (2093 / 800 : Real)
         + (n : Real) ^ 12 * (9009 / 3200 : Real)
         + (n : Real) ^ 11 * (13377273 / 6400000 : Real)
         + (n : Real) ^ 10 * (29032003 / 25600000 : Real)
         + (n : Real) ^ 9 * (951250157 / 2048000000 : Real)
         + (n : Real) ^ 8 * (1197809613 / 8192000000 : Real)
         + (n : Real) ^ 7 * (116867665343 / 3276800000000 : Real)
         + (n : Real) ^ 6 * (88339051801 / 13107200000000 : Real)
         + (n : Real) ^ 5 * (25650726601227 / 26214400000000000 : Real)
         + (n : Real) ^ 4 * (2247338320227 / 20971520000000000 : Real)
         + (n : Real) ^ 3 * (71868937995407 / 8388608000000000000 : Real)
         + (n : Real) ^ 2 * (15835181975421 / 33554432000000000000 : Real)
         + (n : Real) * (1074391491360499 / 67108864000000000000000 : Real)
         + (67659212273499 / 268435456000000000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 16)⁻¹ *
            (638512875 / 8 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 16)⁻¹ *
            (638512875 / 8 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM15TermRat_cast (n : Nat) :
    iteratedDeriv 15
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
        (1 / 20 : Real) =
      (omegaPrimeCenterJetM15TermRat n : Real) := by
  simp [omegaPrimeTrigammaSeriesTerm_iteratedDeriv,
    omegaPrimeOrder16SeriesBase, omegaPrimeCenterJetM15TermRat,
    omegaPrimeCenterBaseReRat, omegaPrimeCenterBaseImRat, Complex.normSq]
  norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
    Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
  ring_nf
  have hnum :
      (((1 / 4 : Complex) + (n : Complex) +
            Complex.I * (1 / 40 : Complex)) ^ 17).re =
        (n : Real) ^ 17 * (1 : Real)
          + (n : Real) ^ 16 * (17 / 4 : Real)
          + (n : Real) ^ 15 * (1683 / 200 : Real)
          + (n : Real) ^ 14 * (1649 / 160 : Real)
          + (n : Real) ^ 13 * (1118719 / 128000 : Real)
          + (n : Real) ^ 12 * (2786147 / 512000 : Real)
          + (n : Real) ^ 11 * (1317268953 / 512000000 : Real)
          + (n : Real) ^ 10 * (1928981483 / 2048000000 : Real)
          + (n : Real) ^ 9 * (176726895631 / 655360000000 : Real)
          + (n : Real) ^ 8 * (158626661479 / 2621440000000 : Real)
          + (n : Real) ^ 7 * (13875915837069 / 1310720000000000 : Real)
          + (n : Real) ^ 6 * (7464888368483 / 5242880000000000 : Real)
          + (n : Real) ^ 5 * (601134719441347 / 4194304000000000000 : Real)
          + (n : Real) ^ 4 * (34485824128147 / 3355443200000000000 : Real)
          + (n : Real) ^ 3 * (318115780984683 / 671088640000000000000 : Real)
          + (n : Real) ^ 2 * (27730077052649 / 2684354560000000000000 : Real)
          - (n : Real) * (4399616826803983 / 42949672960000000000000000 : Real)
          - (1341348386187983 / 171798691840000000000000000 : Real) := by
    norm_num [pow_succ, pow_three, sq, Complex.add_re, Complex.add_im,
      Complex.I_re, Complex.I_im, Complex.mul_re, Complex.mul_im]
    ring_nf
  calc
    (((1 / 4 : Complex) + (n : Complex) +
          Complex.I * (1 / 40 : Complex)) ^ 17).re *
        ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 17)⁻¹ *
          (638512875 : Real) =
        ((n : Real) ^ 17 * (1 : Real)
         + (n : Real) ^ 16 * (17 / 4 : Real)
         + (n : Real) ^ 15 * (1683 / 200 : Real)
         + (n : Real) ^ 14 * (1649 / 160 : Real)
         + (n : Real) ^ 13 * (1118719 / 128000 : Real)
         + (n : Real) ^ 12 * (2786147 / 512000 : Real)
         + (n : Real) ^ 11 * (1317268953 / 512000000 : Real)
         + (n : Real) ^ 10 * (1928981483 / 2048000000 : Real)
         + (n : Real) ^ 9 * (176726895631 / 655360000000 : Real)
         + (n : Real) ^ 8 * (158626661479 / 2621440000000 : Real)
         + (n : Real) ^ 7 * (13875915837069 / 1310720000000000 : Real)
         + (n : Real) ^ 6 * (7464888368483 / 5242880000000000 : Real)
         + (n : Real) ^ 5 * (601134719441347 / 4194304000000000000 : Real)
         + (n : Real) ^ 4 * (34485824128147 / 3355443200000000000 : Real)
         + (n : Real) ^ 3 * (318115780984683 / 671088640000000000000 : Real)
         + (n : Real) ^ 2 * (27730077052649 / 2684354560000000000000 : Real)
         - (n : Real) * (4399616826803983 / 42949672960000000000000000 : Real)
         - (1341348386187983 / 171798691840000000000000000 : Real)) *
          ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 17)⁻¹ *
            (638512875 : Real) := by
      exact congrArg
        (fun y : Real =>
          y * ((101 / 1600 + (n : Real) * (1 / 2) + (n : Real) ^ 2) ^ 17)⁻¹ *
            (638512875 : Real))
        hnum
    _ = _ := by
      ring_nf

theorem omegaPrimeCenterJetM0PrefixRat_cast (N : Nat) :
    ((Nat.factorial 0 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 0
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM0PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 0
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM0TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM0TermRat_cast n
  rw [hsum]
  simp [omegaPrimeCenterJetM0PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM1PrefixRat_cast (N : Nat) :
    ((Nat.factorial 1 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 1
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM1PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 1
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM1TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM1TermRat_cast n
  rw [hsum]
  simp [omegaPrimeCenterJetM1PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM2PrefixRat_cast (N : Nat) :
    ((Nat.factorial 2 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 2
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM2PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 2
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM2TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM2TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 2 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 4 : Real) by norm_num]
  simp [omegaPrimeCenterJetM2PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM3PrefixRat_cast (N : Nat) :
    ((Nat.factorial 3 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 3
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM3PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 3
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM3TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM3TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 3 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 12 : Real) by norm_num]
  simp [omegaPrimeCenterJetM3PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM4PrefixRat_cast (N : Nat) :
    ((Nat.factorial 4 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 4
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM4PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 4
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM4TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM4TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 4 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 48 : Real) by norm_num]
  simp [omegaPrimeCenterJetM4PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM5PrefixRat_cast (N : Nat) :
    ((Nat.factorial 5 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 5
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM5PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 5
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM5TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM5TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 5 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 240 : Real) by norm_num]
  simp [omegaPrimeCenterJetM5PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM6PrefixRat_cast (N : Nat) :
    ((Nat.factorial 6 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 6
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM6PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 6
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM6TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM6TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 6 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 1440 : Real) by norm_num]
  simp [omegaPrimeCenterJetM6PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM7PrefixRat_cast (N : Nat) :
    ((Nat.factorial 7 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 7
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM7PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 7
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM7TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM7TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 7 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 10080 : Real) by norm_num]
  simp [omegaPrimeCenterJetM7PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM8PrefixRat_cast (N : Nat) :
    ((Nat.factorial 8 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 8
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM8PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 8
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM8TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM8TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 8 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 80640 : Real) by norm_num]
  simp [omegaPrimeCenterJetM8PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM9PrefixRat_cast (N : Nat) :
    ((Nat.factorial 9 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 9
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM9PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 9
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM9TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM9TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 9 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 725760 : Real) by norm_num]
  simp [omegaPrimeCenterJetM9PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM10PrefixRat_cast (N : Nat) :
    ((Nat.factorial 10 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 10
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM10PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 10
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM10TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM10TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 10 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 7257600 : Real) by norm_num]
  simp [omegaPrimeCenterJetM10PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM11PrefixRat_cast (N : Nat) :
    ((Nat.factorial 11 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 11
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM11PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 11
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM11TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM11TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 11 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 79833600 : Real) by norm_num]
  simp [omegaPrimeCenterJetM11PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM12PrefixRat_cast (N : Nat) :
    ((Nat.factorial 12 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 12
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM12PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 12
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM12TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM12TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 12 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 958003200 : Real) by norm_num]
  simp [omegaPrimeCenterJetM12PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM13PrefixRat_cast (N : Nat) :
    ((Nat.factorial 13 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 13
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM13PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 13
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM13TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM13TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 13 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 12454041600 : Real) by norm_num]
  simp [omegaPrimeCenterJetM13PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM14PrefixRat_cast (N : Nat) :
    ((Nat.factorial 14 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 14
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM14PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 14
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM14TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM14TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 14 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 174356582400 : Real) by norm_num]
  simp [omegaPrimeCenterJetM14PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetM15PrefixRat_cast (N : Nat) :
    ((Nat.factorial 15 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 15
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM15PrefixRat N : Real) := by
  have hsum :
      (Finset.range N).sum (fun n : Nat =>
          iteratedDeriv 15
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real)) =
        (Finset.range N).sum (fun n : Nat =>
          (omegaPrimeCenterJetM15TermRat n : Real)) := by
    refine Finset.sum_congr rfl ?_
    intro n _
    exact omegaPrimeCenterJetM15TermRat_cast n
  rw [hsum]
  rw [show ((Nat.factorial 15 : Real)⁻¹ * (-1 / 2 : Real)) =
      (-1 / 2615348736000 : Real) by norm_num]
  simp [omegaPrimeCenterJetM15PrefixRat, Rat.cast_sum]

theorem omegaPrimeCenterJetPrefix_m0_N1_ratCast_smoke :
    ((Nat.factorial 0 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 0
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM0PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM0PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m1_N1_ratCast_smoke :
    ((Nat.factorial 1 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 1
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM1PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM1PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m2_N1_ratCast_smoke :
    ((Nat.factorial 2 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 2
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM2PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM2PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m3_N1_ratCast_smoke :
    ((Nat.factorial 3 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 3
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM3PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM3PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m4_N1_ratCast_smoke :
    ((Nat.factorial 4 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 4
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM4PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM4PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m5_N1_ratCast_smoke :
    ((Nat.factorial 5 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 5
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM5PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM5PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m6_N1_ratCast_smoke :
    ((Nat.factorial 6 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 6
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM6PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM6PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m7_N1_ratCast_smoke :
    ((Nat.factorial 7 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 7
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM7PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM7PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m8_N1_ratCast_smoke :
    ((Nat.factorial 8 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 8
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM8PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM8PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m9_N1_ratCast_smoke :
    ((Nat.factorial 9 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 9
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM9PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM9PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m10_N1_ratCast_smoke :
    ((Nat.factorial 10 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 10
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM10PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM10PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m11_N1_ratCast_smoke :
    ((Nat.factorial 11 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 11
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM11PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM11PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m12_N1_ratCast_smoke :
    ((Nat.factorial 12 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 12
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM12PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM12PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m13_N1_ratCast_smoke :
    ((Nat.factorial 13 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 13
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM13PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM13PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m14_N1_ratCast_smoke :
    ((Nat.factorial 14 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 14
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM14PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM14PrefixRat_cast 1

theorem omegaPrimeCenterJetPrefix_m15_N1_ratCast_smoke :
    ((Nat.factorial 15 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 1).sum (fun n : Nat =>
          iteratedDeriv 15
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            (1 / 20 : Real))) =
      (omegaPrimeCenterJetM15PrefixRat 1 : Real) := by
  exact omegaPrimeCenterJetM15PrefixRat_cast 1

theorem omegaPrimeTrigammaSeriesTerm_iteratedDeriv_differentiableAt
    (k : Nat) (n : Nat) (r : Real) :
    DifferentiableAt Real
      (iteratedDeriv k (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)) r := by
  let C : Complex :=
    ((Finset.range k).prod
        (fun i : Nat => (((-2 : Int) : Complex) - (i : Complex)))) *
      (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k
  let m : Int := (-2 : Int) - (k : Int)
  have hfun :
      (iteratedDeriv k (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)) =
        fun t : Real => (C * (omegaPrimeOrder16SeriesBase t n) ^ m).im := by
    funext t
    simpa [C, m] using omegaPrimeTrigammaSeriesTerm_iteratedDeriv k t n
  rw [hfun]
  have hzpow :
      DifferentiableAt Real
        (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ m) r := by
    have hz :
        HasDerivAt
          (fun t : Real => (omegaPrimeOrder16SeriesBase t n) ^ m)
          ((((m : Complex) * (omegaPrimeOrder16SeriesBase r n) ^ (m - 1)) *
            (Complex.I * (((1 / 2 : Real) : Real) : Complex)))) r := by
      have h :=
        (hasDerivAt_zpow m (omegaPrimeOrder16SeriesBase r n)
          (Or.inl (omegaPrimeOrder16SeriesBase_ne_zero r n))).comp r
          (omegaPrimeOrder16SeriesBase_hasDerivAt r n)
      simpa [Function.comp_def] using h
    exact hz.differentiableAt
  have hmul :
      DifferentiableAt Real
        (fun t : Real => C * (omegaPrimeOrder16SeriesBase t n) ^ m) r := by
    exact (differentiableAt_const C).mul hzpow
  exact Complex.imCLM.differentiableAt.comp r hmul

theorem omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_differentiableAt
    (n k : Nat) (r : Real) :
    DifferentiableAt Real
      (iteratedDerivWithin k
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) Set.univ) r := by
  simpa [iteratedDerivWithin_univ] using
    omegaPrimeTrigammaSeriesTerm_iteratedDeriv_differentiableAt k n r

theorem omegaPrimeTrigammaSeries_deriv_layer_differentiableAt_payload :
    ∀ n k r, k <= 16 -> r ∈ Set.univ ->
      DifferentiableAt Real
        (iteratedDerivWithin k
          (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) Set.univ) r := by
  intro n k r _ _
  exact omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_differentiableAt n k r

def omegaPrimeTrigammaDerivCoeff (k : Nat) : Complex :=
  ((Finset.range k).prod
      (fun i : Nat => (((-2 : Int) : Complex) - (i : Complex)))) *
    (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k

def omegaPrimeTrigammaDerivMajorant (k : Nat) (n : Nat) : Real :=
  ‖omegaPrimeTrigammaDerivCoeff k‖ *
    (|(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2))⁻¹

theorem omegaPrimeTrigammaDerivMajorant_summable (k : Nat) :
    Summable (omegaPrimeTrigammaDerivMajorant k) := by
  have hk : (1 : Real) < (k : Real) + 2 := by
    have hkNat : 1 < k + 2 := by omega
    exact_mod_cast hkNat
  have hbase :
      Summable (fun n : Nat =>
        1 / |(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2)) :=
    (Real.summable_one_div_nat_add_rpow (a := (1 / 4 : Real))
      (s := ((k : Real) + 2))).2 hk
  have hbaseInv :
      Summable (fun n : Nat =>
        (|(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2))⁻¹) := by
    simpa [one_div] using hbase
  change Summable (fun n : Nat =>
    ‖omegaPrimeTrigammaDerivCoeff k‖ *
      (|(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2))⁻¹)
  exact Summable.mul_left ‖omegaPrimeTrigammaDerivCoeff k‖ hbaseInv

theorem omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant
    (k n : Nat) (t : Real) :
    ‖iteratedDerivWithin k
        (fun x : Real => omegaPrimeTrigammaSeriesTerm x n) Set.univ t‖ <=
      omegaPrimeTrigammaDerivMajorant k n := by
  rw [iteratedDerivWithin_univ]
  rw [omegaPrimeTrigammaSeriesTerm_iteratedDeriv]
  let C : Complex := omegaPrimeTrigammaDerivCoeff k
  let m : Int := (-2 : Int) - (k : Int)
  have hcoeff :
      ((Finset.range k).prod
          (fun i : Nat => (((-2 : Int) : Complex) - (i : Complex)))) *
        (Complex.I * (((1 / 2 : Real) : Real) : Complex)) ^ k = C := by
    rfl
  rw [hcoeff]
  have him :
      ‖(C * (omegaPrimeOrder16SeriesBase t n) ^ m).im‖ <=
        ‖C * (omegaPrimeOrder16SeriesBase t n) ^ m‖ := by
    simpa [Real.norm_eq_abs] using
      Complex.abs_im_le_norm (C * (omegaPrimeOrder16SeriesBase t n) ^ m)
  have hm : m = -(((k + 2 : Nat) : Int)) := by
    simp [m]
    omega
  have hzpowNorm :
      ‖(omegaPrimeOrder16SeriesBase t n) ^ m‖ =
        (‖omegaPrimeOrder16SeriesBase t n‖ ^ (k + 2))⁻¹ := by
    rw [hm, norm_zpow, zpow_neg, zpow_natCast]
  have hReNonneg : 0 <= (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  have hRePos : 0 < (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  have hReLeNorm :
      (n : Real) + (1 / 4 : Real) <=
        ‖omegaPrimeOrder16SeriesBase t n‖ := by
    have hAbsRe :
        |(omegaPrimeOrder16SeriesBase t n).re| <=
          ‖omegaPrimeOrder16SeriesBase t n‖ :=
      Complex.abs_re_le_norm _
    rwa [omegaPrimeOrder16SeriesBase_re, abs_of_nonneg hReNonneg] at hAbsRe
  have hPowLe :
      ((n : Real) + (1 / 4 : Real)) ^ (k + 2) <=
        ‖omegaPrimeOrder16SeriesBase t n‖ ^ (k + 2) :=
    pow_le_pow_left₀ hReNonneg hReLeNorm _
  have hInv :
      (‖omegaPrimeOrder16SeriesBase t n‖ ^ (k + 2))⁻¹ <=
        (((n : Real) + (1 / 4 : Real)) ^ (k + 2))⁻¹ :=
    inv_anti₀ (pow_pos hRePos _) hPowLe
  have hPowEq :
      ((n : Real) + (1 / 4 : Real)) ^ (k + 2) =
        |(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2) := by
    rw [abs_of_nonneg hReNonneg]
    have hkCast : (((k + 2 : Nat) : Real)) = (k : Real) + 2 := by
      norm_num
    rw [← hkCast, Real.rpow_natCast]
  calc
    ‖(C * (omegaPrimeOrder16SeriesBase t n) ^ m).im‖
        <= ‖C * (omegaPrimeOrder16SeriesBase t n) ^ m‖ := him
    _ = ‖C‖ * ‖(omegaPrimeOrder16SeriesBase t n) ^ m‖ := by
          rw [norm_mul]
    _ = ‖C‖ * (‖omegaPrimeOrder16SeriesBase t n‖ ^ (k + 2))⁻¹ := by
          rw [hzpowNorm]
    _ <= ‖C‖ * (((n : Real) + (1 / 4 : Real)) ^ (k + 2))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hInv (norm_nonneg C)
    _ = ‖C‖ *
        (|(n : Real) + (1 / 4 : Real)| ^ ((k : Real) + 2))⁻¹ := by
          rw [hPowEq]
    _ = omegaPrimeTrigammaDerivMajorant k n := by
          simp [omegaPrimeTrigammaDerivMajorant, C]

theorem omegaPrimeTrigammaSeries_deriv_layers_summableLocallyUniformlyOn_payload :
    ∀ k : Nat, 1 <= k -> k <= 16 ->
      SummableLocallyUniformlyOn
        (fun n : Nat =>
          iteratedDerivWithin k
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) Set.univ)
        Set.univ := by
  intro k _ _
  apply SummableLocallyUniformlyOn_of_locally_bounded isOpen_univ
  intro K _ _
  exact ⟨omegaPrimeTrigammaDerivMajorant k,
    omegaPrimeTrigammaDerivMajorant_summable k,
    fun n t _ =>
      omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant k n t⟩

theorem omegaPrimeOrder16TrigammaSeriesDerivTerm_eq
    (eta : Real) (n : Nat) :
    omegaPrimeOrder16TrigammaSeriesDerivTerm eta n =
      ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
        omegaPrimeOrder16SeriesTerm eta n := by
  unfold omegaPrimeOrder16TrigammaSeriesDerivTerm
  exact omegaPrimeOrder16TrigammaSeriesTerm_iteratedDeriv16 eta n

theorem omegaPrimeOrder16TrigammaSeriesDerivTerm_tsum
    (eta : Real) :
    (∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n) =
      ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
        omegaPrimeOrder16Series eta := by
  calc
    (∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n)
        = ∑' n : Nat,
            ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
              omegaPrimeOrder16SeriesTerm eta n := by
          exact tsum_congr
            (omegaPrimeOrder16TrigammaSeriesDerivTerm_eq eta)
    _ = ((Nat.factorial 17 : Real) / (2 : Real) ^ 16) *
        omegaPrimeOrder16Series eta := by
          rw [omegaPrimeOrder16Series, tsum_mul_left]

theorem omegaPrimeTrigammaSeriesTerm_summable (eta : Real) :
    Summable (fun n : Nat => omegaPrimeTrigammaSeriesTerm eta n) := by
  let z : Complex :=
    (1 / 4 : Complex) + Complex.I * (((eta / 2 : Real) : Complex))
  have hz : 0 < z.re := by
    norm_num [z]
  have hcomplex : Summable (fun n : Nat => 1 / (z + n) ^ 2) :=
    _root_.summable_trigamma_series hz
  have him : Summable (fun n : Nat => (1 / (z + n) ^ 2).im) :=
    Complex.imCLM.summable hcomplex
  simpa [omegaPrimeTrigammaSeriesTerm, z, add_comm, add_left_comm, add_assoc]
    using him

theorem omegaPrimeTrigammaSeries_iteratedDeriv16_eq_tsum_of_locally_uniform
    (eta : Real)
    (hDerivLoc :
      ∀ k : Nat, 1 <= k -> k <= 16 ->
        SummableLocallyUniformlyOn
          (fun n : Nat =>
            iteratedDerivWithin k
              (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) Set.univ)
          Set.univ)
    (hDiff :
      ∀ n k r, k <= 16 -> r ∈ Set.univ ->
        DifferentiableAt Real
          (iteratedDerivWithin k
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) Set.univ) r) :
    iteratedDeriv 16 omegaPrimeTrigammaSeries eta =
      ∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n := by
  have h :=
    iteratedDerivWithin_tsum (ι := Nat) (𝕜 := Real) (F := Real)
      (m := 16) (s := Set.univ) isOpen_univ (Set.mem_univ eta)
      (fun t _ => omegaPrimeTrigammaSeriesTerm_summable t)
      hDerivLoc hDiff
  have h' :
      iteratedDeriv 16 omegaPrimeTrigammaSeries eta =
        ∑' n : Nat,
          iteratedDeriv 16
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta := by
    simpa [omegaPrimeTrigammaSeries, iteratedDerivWithin_univ] using h
  calc
    iteratedDeriv 16 omegaPrimeTrigammaSeries eta =
        ∑' n : Nat,
          iteratedDeriv 16
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta := h'
    _ = ∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n := by
          exact tsum_congr
            (fun n =>
              (omegaPrimeOrder16TrigammaSeriesDerivTerm_eq_iteratedDeriv_term
                eta n).symm)

theorem omegaPrimeTrigammaSeries_iteratedDeriv16_eq_tsum
    (eta : Real) :
    iteratedDeriv 16 omegaPrimeTrigammaSeries eta =
      ∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n :=
  omegaPrimeTrigammaSeries_iteratedDeriv16_eq_tsum_of_locally_uniform eta
    omegaPrimeTrigammaSeries_deriv_layers_summableLocallyUniformlyOn_payload
    omegaPrimeTrigammaSeries_deriv_layer_differentiableAt_payload

/-- Lower-order version of the trigamma-series termwise differentiation
bridge.  This is the reusable receiver for OmegaPrime center-jet payloads:
generated Taylor coefficients for orders `< 16` can now target the same
termwise series convention as the order-16 budget. -/
theorem omegaPrimeTrigammaSeries_iteratedDeriv_eq_tsum_of_le16
    (m : Nat) (hm : m <= 16) (eta : Real) :
    iteratedDeriv m omegaPrimeTrigammaSeries eta =
      ∑' n : Nat,
        iteratedDeriv m
          (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta := by
  have h :=
    iteratedDerivWithin_tsum (ι := Nat) (𝕜 := Real) (F := Real)
      (m := m) (s := Set.univ) isOpen_univ (Set.mem_univ eta)
      (fun t _ => omegaPrimeTrigammaSeriesTerm_summable t)
      (fun k hk1 hkm =>
        omegaPrimeTrigammaSeries_deriv_layers_summableLocallyUniformlyOn_payload
          k hk1 (le_trans hkm hm))
      (fun n k r hkm _ =>
        omegaPrimeTrigammaSeries_deriv_layer_differentiableAt_payload
          n k r (le_trans hkm hm) (Set.mem_univ r))
  simpa [omegaPrimeTrigammaSeries, iteratedDerivWithin_univ] using h

/-- Norm-majorant consequence of the lower-order termwise differentiation
bridge.  This is the analytic surface needed by generated center-jet
payloads before replacing the right-hand side by a rational bound. -/
theorem omegaPrimeTrigammaSeries_iteratedDeriv_norm_le_tsum_majorant_of_le16
    (m : Nat) (hm : m <= 16) (eta : Real) :
    ‖iteratedDeriv m omegaPrimeTrigammaSeries eta‖ <=
      ∑' n : Nat, omegaPrimeTrigammaDerivMajorant m n := by
  have hEq :=
    omegaPrimeTrigammaSeries_iteratedDeriv_eq_tsum_of_le16 m hm eta
  rw [hEq]
  have hBound :
      ∀ n : Nat,
        ‖iteratedDeriv m
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta‖ <=
          omegaPrimeTrigammaDerivMajorant m n := by
    intro n
    simpa [iteratedDerivWithin_univ] using
      omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant
        m n eta
  have hSummDeriv :
      Summable
        (fun n : Nat =>
          iteratedDeriv m
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta) :=
    (omegaPrimeTrigammaDerivMajorant_summable m).of_norm_bounded hBound
  have hNorm :
      ‖∑' n : Nat,
          iteratedDeriv m
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta‖ <=
        ∑' n : Nat,
          ‖iteratedDeriv m
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta‖ :=
    norm_tsum_le_tsum_norm hSummDeriv.norm
  have hAbsSum :
      (∑' n : Nat,
        ‖iteratedDeriv m
          (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta‖) <=
        ∑' n : Nat, omegaPrimeTrigammaDerivMajorant m n := by
    exact Summable.tsum_le_tsum hBound hSummDeriv.norm
      (omegaPrimeTrigammaDerivMajorant_summable m)
  exact hNorm.trans hAbsSum

/-- Closed-form OmegaPrime version of the lower-order derivative majorant.
The factor `1 / 2` is exactly the normalization from
`omegaPrimeClosedForm_eq_trigamma_series`. -/
theorem omegaPrimeClosedForm_iteratedDeriv_norm_le_half_tsum_majorant_of_le16
    (m : Nat) (hm : m <= 16) (eta : Real) :
    ‖iteratedDeriv m omegaPrimeClosedForm eta‖ <=
      (1 / 2 : Real) *
        (∑' n : Nat, omegaPrimeTrigammaDerivMajorant m n) := by
  have hfun :
      omegaPrimeClosedForm =
        fun t : Real => (-1 / 2 : Real) * omegaPrimeTrigammaSeries t := by
    funext t
    rw [omegaPrimeClosedForm_eq_trigamma_series t]
    ring
  have hmWithTop : (m : WithTop ENat) <= (16 : Nat) := by
    exact_mod_cast hm
  have hSmooth :
      ContDiffAt Real m omegaPrimeTrigammaSeries eta :=
    (omegaPrimeTrigammaSeries_contDiffAt16 eta).of_le hmWithTop
  have hMajorant :=
    omegaPrimeTrigammaSeries_iteratedDeriv_norm_le_tsum_majorant_of_le16
      m hm eta
  rw [hfun]
  rw [iteratedDeriv_const_mul hSmooth (-1 / 2 : Real)]
  rw [norm_mul, Real.norm_eq_abs]
  have hhalf : |(-1 / 2 : Real)| = (1 / 2 : Real) := by
    norm_num
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hMajorant (by norm_num)

/-- Finite-prefix plus shifted-tail version of the lower-order trigamma
majorant.  Generated center-jet rows can use the finite prefix as the rational
coefficient candidate and reserve the right-hand side for the tail error. -/
theorem omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16
    (m N : Nat) (hm : m <= 16) (eta : Real) :
    ‖iteratedDeriv m omegaPrimeTrigammaSeries eta -
        (Finset.range N).sum
          (fun n : Nat =>
            iteratedDeriv m
              (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta)‖ <=
      ∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N) := by
  let f : Nat -> Real :=
    fun n : Nat =>
      iteratedDeriv m
        (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta
  have hEq :
      iteratedDeriv m omegaPrimeTrigammaSeries eta =
        ∑' n : Nat, f n := by
    simpa [f] using
      omegaPrimeTrigammaSeries_iteratedDeriv_eq_tsum_of_le16 m hm eta
  have hBound :
      ∀ n : Nat, ‖f n‖ <= omegaPrimeTrigammaDerivMajorant m n := by
    intro n
    simpa [f, iteratedDerivWithin_univ] using
      omegaPrimeTrigammaSeriesTerm_iteratedDerivWithin_norm_le_majorant
        m n eta
  have hSummDeriv : Summable f :=
    (omegaPrimeTrigammaDerivMajorant_summable m).of_norm_bounded hBound
  have hTailSummDeriv : Summable (fun k : Nat => f (k + N)) := by
    simpa using (summable_nat_add_iff N).2 hSummDeriv
  have hTailMajorant :
      Summable (fun k : Nat => omegaPrimeTrigammaDerivMajorant m (k + N)) := by
    simpa using
      (summable_nat_add_iff N).2 (omegaPrimeTrigammaDerivMajorant_summable m)
  have hsplit :
      (Finset.range N).sum f + (∑' k : Nat, f (k + N)) =
        ∑' n : Nat, f n := by
    simpa using (hSummDeriv.sum_add_tsum_nat_add N)
  have hTailEq :
      iteratedDeriv m omegaPrimeTrigammaSeries eta - (Finset.range N).sum f =
        ∑' k : Nat, f (k + N) := by
    rw [hEq, ← hsplit]
    ring
  have hNorm :
      ‖∑' k : Nat, f (k + N)‖ <=
        ∑' k : Nat, ‖f (k + N)‖ :=
    norm_tsum_le_tsum_norm hTailSummDeriv.norm
  have hAbsSum :
      (∑' k : Nat, ‖f (k + N)‖) <=
        ∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N) := by
    exact Summable.tsum_le_tsum
      (fun k => hBound (k + N)) hTailSummDeriv.norm hTailMajorant
  rw [hTailEq]
  exact hNorm.trans hAbsSum

/-- Closed-form OmegaPrime finite-prefix plus shifted-tail bridge.  This is the
Lean-side bridge requested by the center-jet payload route before inserting
concrete rational prefix and shifted-tail bounds. -/
theorem omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16
    (m N : Nat) (hm : m <= 16) (eta : Real) :
    ‖iteratedDeriv m omegaPrimeClosedForm eta -
        (-1 / 2 : Real) *
          (Finset.range N).sum
            (fun n : Nat =>
              iteratedDeriv m
                (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta)‖ <=
      (1 / 2 : Real) *
        (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N)) := by
  have hfun :
      omegaPrimeClosedForm =
        fun t : Real => (-1 / 2 : Real) * omegaPrimeTrigammaSeries t := by
    funext t
    rw [omegaPrimeClosedForm_eq_trigamma_series t]
    ring
  have hmWithTop : (m : WithTop ENat) <= (16 : Nat) := by
    exact_mod_cast hm
  have hSmooth :
      ContDiffAt Real m omegaPrimeTrigammaSeries eta :=
    (omegaPrimeTrigammaSeries_contDiffAt16 eta).of_le hmWithTop
  have hTail :=
    omegaPrimeTrigammaSeries_iteratedDeriv_sub_prefix_norm_le_shifted_tsum_majorant_of_le16
      m N hm eta
  rw [hfun]
  rw [iteratedDeriv_const_mul hSmooth (-1 / 2 : Real)]
  rw [← mul_sub, norm_mul, Real.norm_eq_abs]
  have hhalf : |(-1 / 2 : Real)| = (1 / 2 : Real) := by
    norm_num
  rw [hhalf]
  exact mul_le_mul_of_nonneg_left hTail (by norm_num)

/-- Factorial-normalized center-jet version of the finite-prefix plus
shifted-tail bridge.  The coefficient candidate is the exact finite prefix
multiplied by `m!⁻¹ * (-1/2)`, matching the Taylor `centerJet` normalization. -/
theorem omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16
    (m N : Nat) (hm : m <= 16) (eta : Real) :
    ‖((Nat.factorial m : Real)⁻¹ *
          iteratedDeriv m omegaPrimeClosedForm eta) -
        (((Nat.factorial m : Real)⁻¹ * (-1 / 2 : Real)) *
          (Finset.range N).sum
            (fun n : Nat =>
              iteratedDeriv m
                (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta))‖ <=
      (Nat.factorial m : Real)⁻¹ *
        ((1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N))) := by
  let a : Real := (Nat.factorial m : Real)⁻¹
  let pref : Real :=
    (Finset.range N).sum
      (fun n : Nat =>
        iteratedDeriv m
          (fun t : Real => omegaPrimeTrigammaSeriesTerm t n) eta)
  have hTail :=
    omegaPrimeClosedForm_iteratedDeriv_sub_prefix_norm_le_half_shifted_tsum_majorant_of_le16
      m N hm eta
  have haNonneg : 0 <= a := by
    dsimp [a]
    positivity
  have hExpr :
      a * iteratedDeriv m omegaPrimeClosedForm eta -
          (a * (-1 / 2 : Real)) * pref =
        a * (iteratedDeriv m omegaPrimeClosedForm eta -
          (-1 / 2 : Real) * pref) := by
    ring
  have hScaled :
      ‖a * (iteratedDeriv m omegaPrimeClosedForm eta -
          (-1 / 2 : Real) * pref)‖ <=
        a * ((1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N))) := by
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg haNonneg]
    exact mul_le_mul_of_nonneg_left hTail haNonneg
  rw [← hExpr] at hScaled
  simpa [a, pref] using hScaled

/-- Rewrite the lower-order derivative majorant into a shifted real-power
p-series form.  This is the first Lean bridge needed by the generated
`centerJetPrefixTailRows`: it exposes the tail as a standard positive
shifted `x ^ (-(m+2))` series. -/
theorem omegaPrimeTrigammaDerivMajorant_eq_coeff_norm_mul_shifted_rpow
    (m n : Nat) :
    omegaPrimeTrigammaDerivMajorant m n =
      ‖omegaPrimeTrigammaDerivCoeff m‖ *
        (((n : Real) + (1 / 4 : Real)) ^ (-((m : Real) + 2))) := by
  have hnonneg : 0 <= (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  unfold omegaPrimeTrigammaDerivMajorant
  rw [abs_of_nonneg hnonneg]
  rw [Real.rpow_neg hnonneg]

theorem omegaPrimeTrigammaDerivMajorant_nonneg (m n : Nat) :
    0 <= omegaPrimeTrigammaDerivMajorant m n := by
  unfold omegaPrimeTrigammaDerivMajorant
  positivity

/-- Exact coefficient norm for the generated center-jet rows `m = 0..15`.
The statement is finite on purpose: these are precisely the rows emitted by the
v9 payload generator, and it avoids making the current Step33 gate depend on a
more general product-norm API. -/
theorem omegaPrimeTrigammaDerivCoeff_norm_eq_factorial_div_pow_of_le15
    (m : Nat) (hm : m <= 15) :
    ‖omegaPrimeTrigammaDerivCoeff m‖ =
      (Nat.factorial (m + 1) : Real) / (2 : Real) ^ m := by
  interval_cases m <;>
    norm_num [omegaPrimeTrigammaDerivCoeff, Finset.prod_range_succ]

/-- Finite shifted-tail partial sums are bounded by the matching integral.
This is the sum/integral half of the generated `prefixN = 128` row proof; the
remaining steps are the improper-integral evaluation and the coefficient-norm
normalization. -/
theorem omegaPrimeTrigammaDerivMajorant_shifted_sum_le_integral
    (m N a : Nat) (hN : 1 <= N) :
    (Finset.range a).sum
        (fun k => omegaPrimeTrigammaDerivMajorant m (k + N)) <=
      ∫ x in ((N : Real) - (3 / 4 : Real))..
        (((N : Real) - (3 / 4 : Real)) + (a : Real)),
        ‖omegaPrimeTrigammaDerivCoeff m‖ *
          x ^ (-((m : Real) + 2)) := by
  let c : Real := (N : Real) - (3 / 4 : Real)
  let f : Real -> Real :=
    fun x => ‖omegaPrimeTrigammaDerivCoeff m‖ *
      x ^ (-((m : Real) + 2))
  have hc_pos : 0 < c := by
    have hNreal : (1 : Real) <= (N : Real) := by
      exact_mod_cast hN
    dsimp [c]
    linarith
  have hantiIoi :
      AntitoneOn (fun x : Real => x ^ (-((m : Real) + 2))) (Set.Ioi 0) := by
    apply Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
    have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
    linarith
  have hanti :
      AntitoneOn f (Set.Icc c (c + (a : Real))) := by
    intro x hx y hy hxy
    dsimp [f]
    exact mul_le_mul_of_nonneg_left
      (hantiIoi (lt_of_lt_of_le hc_pos hx.1) (lt_of_lt_of_le hc_pos hy.1) hxy)
      (by positivity)
  have hsum :=
    (AntitoneOn.sum_le_integral (x₀ := c) (a := a) (f := f) hanti)
  have hterms :
      (Finset.range a).sum
          (fun k => omegaPrimeTrigammaDerivMajorant m (k + N)) =
        (Finset.range a).sum (fun k => f (c + ((k + 1 : Nat) : Real))) := by
    refine Finset.sum_congr rfl ?_
    intro k _hk
    rw [omegaPrimeTrigammaDerivMajorant_eq_coeff_norm_mul_shifted_rpow]
    have hbase :
        (((k + N : Nat) : Real) + (1 / 4 : Real)) =
          c + ((k + 1 : Nat) : Real) := by
      dsimp [c]
      norm_num [Nat.cast_add, Nat.cast_one]
      ring
    dsimp [f]
    rw [hbase]
  rw [hterms]
  simpa [c, f] using hsum

/-- Closed finite-partial version of the shifted-tail integral bound.  This
keeps the coefficient norm explicit; the remaining generated-row bridge is the
finite `m = 0..15` normalization of that coefficient norm. -/
theorem omegaPrimeTrigammaDerivMajorant_shifted_sum_le_coeff_norm_rpow_bound
    (m N a : Nat) (hN : 1 <= N) :
    (Finset.range a).sum
        (fun k => omegaPrimeTrigammaDerivMajorant m (k + N)) <=
      ‖omegaPrimeTrigammaDerivCoeff m‖ *
        ((((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) /
          ((m : Real) + 1)) := by
  let c : Real := (N : Real) - (3 / 4 : Real)
  let r : Real := -((m : Real) + 2)
  have hc_pos : 0 < c := by
    have hNreal : (1 : Real) <= (N : Real) := by
      exact_mod_cast hN
    dsimp [c]
    linarith
  have hsum_int :=
    omegaPrimeTrigammaDerivMajorant_shifted_sum_le_integral m N a hN
  have hle_c : c <= c + (a : Real) := by
    have ha : 0 <= (a : Real) := Nat.cast_nonneg a
    linarith
  have h_integral :
      (∫ x in c..(c + (a : Real)),
        x ^ r) =
        (((c + (a : Real)) ^ (r + 1) - c ^ (r + 1)) / (r + 1)) := by
    have hne : r ≠ -1 := by
      dsimp [r]
      have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
      linarith
    have h0 : (0 : Real) ∉ Set.uIcc c (c + (a : Real)) := by
      intro hmem
      have hmem' : (0 : Real) ∈ Set.Icc c (c + (a : Real)) := by
        simpa [Set.uIcc_of_le hle_c] using hmem
      exact (not_le_of_gt hc_pos) hmem'.1
    have hcond : (-1 : Real) < r ∨
        r ≠ -1 ∧ (0 : Real) ∉ Set.uIcc c (c + (a : Real)) := by
      right
      exact ⟨hne, h0⟩
    simpa [r, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (integral_rpow (a := c) (b := c + (a : Real)) (r := r) hcond)
  have hden_neg : r + 1 < 0 := by
    dsimp [r]
    have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
    linarith
  have hb_nonneg : 0 <= (c + (a : Real)) ^ (r + 1) := by
    have hb : 0 <= c + (a : Real) := by
      have ha : 0 <= (a : Real) := Nat.cast_nonneg a
      linarith
    exact Real.rpow_nonneg hb _
  have hdiff :
      -c ^ (r + 1) <=
        (c + (a : Real)) ^ (r + 1) - c ^ (r + 1) := by
    nlinarith [hb_nonneg]
  have h_int_bound :
      (∫ x in c..(c + (a : Real)), x ^ r) <=
        c ^ (-((m : Real) + 1)) / ((m : Real) + 1) := by
    calc
      (∫ x in c..(c + (a : Real)), x ^ r)
          = (((c + (a : Real)) ^ (r + 1) - c ^ (r + 1)) / (r + 1)) := h_integral
      _ <= (-c ^ (r + 1)) / (r + 1) := by
          exact div_le_div_of_nonpos_of_le (le_of_lt hden_neg) hdiff
      _ = c ^ (-((m : Real) + 1)) / ((m : Real) + 1) := by
          have hden : (1 + (m : Real)) ≠ 0 := by positivity
          have hden2 : (-1 - (m : Real)) ≠ 0 := by
            have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
            linarith
          have hA :
              -(c ^ (-1 - (m : Real)) * (-1 - (m : Real))⁻¹) =
                c ^ (-1 - (m : Real)) * (1 + (m : Real))⁻¹ := by
            field_simp [hden, hden2]
            ring_nf
          dsimp [r]
          have hexp1 :
              (-((m : Real) + 2) + 1) = -1 - (m : Real) := by
            ring
          have hexp2 :
              (-((m : Real) + 1)) = -1 - (m : Real) := by
            ring
          rw [hexp1, hexp2]
          simpa [div_eq_mul_inv, add_comm, add_left_comm, add_assoc] using hA
  have hmul :
      (∫ x in c..(c + (a : Real)),
        ‖omegaPrimeTrigammaDerivCoeff m‖ * x ^ r) <=
        ‖omegaPrimeTrigammaDerivCoeff m‖ *
          (c ^ (-((m : Real) + 1)) / ((m : Real) + 1)) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left h_int_bound (by positivity)
  exact hsum_int.trans (by
    simpa [c, r, mul_assoc] using hmul)

/-- Shifted-tail `tsum` bound with the coefficient norm still explicit.  This
is the full infinite-tail integral bridge for generated center-jet rows.  The
last missing arithmetic step is the finite `m = 0..15` coefficient-norm
normalization used by the v9 row constants. -/
theorem omegaPrimeTrigammaDerivMajorant_shifted_tsum_le_coeff_norm_rpow_bound
    (m N : Nat) (hN : 1 <= N) :
    (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N)) <=
      ‖omegaPrimeTrigammaDerivCoeff m‖ *
        ((((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) /
          ((m : Real) + 1)) := by
  let f : Nat -> Real := fun k => omegaPrimeTrigammaDerivMajorant m (k + N)
  let B : Real :=
    ‖omegaPrimeTrigammaDerivCoeff m‖ *
      ((((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) /
        ((m : Real) + 1))
  have hc_pos : 0 < (N : Real) - (3 / 4 : Real) := by
    have hNreal : (1 : Real) <= (N : Real) := by
      exact_mod_cast hN
    linarith
  have hB_nonneg : 0 <= B := by
    have hden_pos : 0 < (m : Real) + 1 := by
      have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
      linarith
    have hpow_nonneg :
        0 <= ((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1)) :=
      Real.rpow_nonneg (le_of_lt hc_pos) _
    dsimp [B]
    exact mul_nonneg (by positivity)
      (div_nonneg hpow_nonneg (le_of_lt hden_pos))
  have hsumm : Summable f := by
    dsimp [f]
    simpa using
      (summable_nat_add_iff N).2 (omegaPrimeTrigammaDerivMajorant_summable m)
  have hbound :
      ∀ s : Finset Nat, s.sum f <= B := by
    intro s
    classical
    by_cases hs : s.Nonempty
    · let A := s.max' hs + 1
      have hsubset : s ⊆ Finset.range A := by
        intro k hk
        have hle : k <= s.max' hs := Finset.le_max' s k hk
        exact Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
      have hsum_le_range :
          s.sum f <= (Finset.range A).sum f := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro k _hk_range _hk_not
        dsimp [f]
        exact omegaPrimeTrigammaDerivMajorant_nonneg m (k + N)
      have hrange :
          (Finset.range A).sum f <= B := by
        dsimp [f, B]
        exact omegaPrimeTrigammaDerivMajorant_shifted_sum_le_coeff_norm_rpow_bound
          m N A hN
      exact hsum_le_range.trans hrange
    · have hs_empty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
      simp [hs_empty, hB_nonneg]
  simpa [f, B] using hsumm.tsum_le_of_sum_le hbound

/-- Generated-row shifted-tail budget in the Taylor-center normalization.
For `m = 0..15`, this is exactly the analytic inequality behind the v9
`coeffErrorAbs` formula, written in real-power form. -/
theorem omegaPrimeCenterJet_shifted_tsum_budget_le_generated_rpow_bound_of_le15
    (m N : Nat) (hm : m <= 15) (hN : 1 <= N) :
    (Nat.factorial m : Real)⁻¹ *
        ((1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N))) <=
      (1 / (2 : Real) ^ (m + 1)) *
        (((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) := by
  let c : Real := (N : Real) - (3 / 4 : Real)
  have htail :=
    omegaPrimeTrigammaDerivMajorant_shifted_tsum_le_coeff_norm_rpow_bound
      m N hN
  have hscale_nonneg :
      0 <= (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) := by
    positivity
  have hscaled :
      (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N)) <=
        (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) *
          (‖omegaPrimeTrigammaDerivCoeff m‖ *
            (c ^ (-((m : Real) + 1)) / ((m : Real) + 1))) := by
    exact mul_le_mul_of_nonneg_left (by simpa [c] using htail) hscale_nonneg
  have hcoeff :=
    omegaPrimeTrigammaDerivCoeff_norm_eq_factorial_div_pow_of_le15 m hm
  rw [hcoeff] at hscaled
  have hfact :
      (Nat.factorial (m + 1) : Real) =
        ((m : Real) + 1) * (Nat.factorial m : Real) := by
    rw [Nat.factorial_succ]
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have halg :
      (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) *
          (((Nat.factorial (m + 1) : Real) / (2 : Real) ^ m) *
            (c ^ (-((m : Real) + 1)) / ((m : Real) + 1))) =
        (1 / (2 : Real) ^ (m + 1)) *
          c ^ (-((m : Real) + 1)) := by
    have hfac_ne : (Nat.factorial m : Real) ≠ 0 := by positivity
    have hden : ((m : Real) + 1) ≠ 0 := by
      have hm_nonneg : 0 <= (m : Real) := Nat.cast_nonneg m
      linarith
    have hpow_ne : ((2 : Real) ^ m) ≠ 0 := by positivity
    rw [hfact]
    field_simp [hfac_ne, hden, hpow_ne, pow_succ]
    ring
  calc
    (Nat.factorial m : Real)⁻¹ *
        ((1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N)))
        = (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N)) := by
            ring
    _ <= (Nat.factorial m : Real)⁻¹ * (1 / 2 : Real) *
          (((Nat.factorial (m + 1) : Real) / (2 : Real) ^ m) *
            (c ^ (-((m : Real) + 1)) / ((m : Real) + 1))) := hscaled
    _ = (1 / (2 : Real) ^ (m + 1)) *
          c ^ (-((m : Real) + 1)) := halg
    _ = (1 / (2 : Real) ^ (m + 1)) *
          (((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) := by
            simp [c]

/-- Same generated-row shifted-tail budget in the exact denominator form used
by the v9 JSON payload. -/
theorem omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15
    (m N : Nat) (hm : m <= 15) (hN : 1 <= N) :
    (Nat.factorial m : Real)⁻¹ *
        ((1 / 2 : Real) *
          (∑' k : Nat, omegaPrimeTrigammaDerivMajorant m (k + N))) <=
      1 /
        ((2 : Real) ^ (m + 1) *
          (((N : Real) - (3 / 4 : Real)) ^ (m + 1))) := by
  let c : Real := (N : Real) - (3 / 4 : Real)
  have hc_pos : 0 < c := by
    have hNreal : (1 : Real) <= (N : Real) := by
      exact_mod_cast hN
    dsimp [c]
    linarith
  have hbase :=
    omegaPrimeCenterJet_shifted_tsum_budget_le_generated_rpow_bound_of_le15
      m N hm hN
  have hrpow :
      c ^ (-((m : Real) + 1)) = (c ^ (m + 1))⁻¹ := by
    calc
      c ^ (-((m : Real) + 1))
          = c ^ (-(((m + 1 : Nat) : Real))) := by
              norm_num [Nat.cast_add, Nat.cast_one]
      _ = (c ^ ((m + 1 : Nat) : Real))⁻¹ := by
              rw [Real.rpow_neg (le_of_lt hc_pos)]
      _ = (c ^ (m + 1))⁻¹ := by
              rw [Real.rpow_natCast]
  have hrewrite :
      (1 / (2 : Real) ^ (m + 1)) *
          (((N : Real) - (3 / 4 : Real)) ^ (-((m : Real) + 1))) =
        1 /
          ((2 : Real) ^ (m + 1) *
            (((N : Real) - (3 / 4 : Real)) ^ (m + 1))) := by
    have h2 : ((2 : Real) ^ (m + 1)) ≠ 0 := by positivity
    have hc_ne : (c ^ (m + 1)) ≠ 0 := by
      exact pow_ne_zero _ (ne_of_gt hc_pos)
    change (1 / (2 : Real) ^ (m + 1)) *
        (c ^ (-((m : Real) + 1))) =
      1 / ((2 : Real) ^ (m + 1) * c ^ (m + 1))
    rw [hrpow]
    field_simp [h2, hc_ne]
  exact hbase.trans_eq hrewrite

theorem omegaPrimeClosedForm_iteratedDeriv16_eq_of_trigamma_series_interchange
    (eta : Real)
    (hSmoothSeries : ContDiffAt Real 16 omegaPrimeTrigammaSeries eta)
    (hInterchange :
      iteratedDeriv 16 omegaPrimeTrigammaSeries eta =
        ∑' n : Nat, omegaPrimeOrder16TrigammaSeriesDerivTerm eta n) :
    iteratedDeriv 16 omegaPrimeClosedForm eta =
      -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta := by
  have hfun :
      omegaPrimeClosedForm =
        fun t : Real => (-1 / 2 : Real) * omegaPrimeTrigammaSeries t := by
    funext t
    rw [omegaPrimeClosedForm_eq_trigamma_series t]
    ring
  rw [hfun]
  rw [iteratedDeriv_const_mul hSmoothSeries (-1 / 2 : Real)]
  rw [hInterchange, omegaPrimeOrder16TrigammaSeriesDerivTerm_tsum]
  unfold omegaPrimeOrder16SeriesFactor
  ring

theorem omegaPrimeClosedForm_iteratedDeriv16_eq
    (eta : Real) :
    iteratedDeriv 16 omegaPrimeClosedForm eta =
      -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta :=
  omegaPrimeClosedForm_iteratedDeriv16_eq_of_trigamma_series_interchange eta
    (omegaPrimeTrigammaSeries_contDiffAt16 eta)
    (omegaPrimeTrigammaSeries_iteratedDeriv16_eq_tsum eta)

/-- Pointwise norm majorant for one order-16 OmegaPrime series term. -/
theorem omegaPrimeOrder16SeriesTerm_abs_le_norm_inv_pow
    (eta : Real) (n : Nat) :
    |omegaPrimeOrder16SeriesTerm eta n| <=
      (‖omegaPrimeOrder16SeriesBase eta n‖ ^ 18)⁻¹ := by
  have him :
      |(((omegaPrimeOrder16SeriesBase eta n) ^ 18)⁻¹).im| <=
        ‖((omegaPrimeOrder16SeriesBase eta n) ^ 18)⁻¹‖ :=
    Complex.abs_im_le_norm _
  have hnorm :
      ‖((omegaPrimeOrder16SeriesBase eta n) ^ 18)⁻¹‖ =
        (‖omegaPrimeOrder16SeriesBase eta n‖ ^ 18)⁻¹ := by
    simp [norm_inv, norm_pow]
  simpa [omegaPrimeOrder16SeriesTerm, hnorm] using him

/-- Concrete p-series-shaped pointwise majorant for one order-16 OmegaPrime
series term.  The remaining generated payload only has to prove summability
and a rational upper bound for this real majorant. -/
theorem omegaPrimeOrder16SeriesTerm_abs_le_real_majorant
    (eta : Real) (n : Nat) :
    |omegaPrimeOrder16SeriesTerm eta n| <=
      omegaPrimeOrder16RealMajorant n := by
  have hTerm := omegaPrimeOrder16SeriesTerm_abs_le_norm_inv_pow eta n
  have hReNonneg : 0 <= (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  have hRePos : 0 < (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  have hReLeNorm :
      (n : Real) + (1 / 4 : Real) <=
        ‖omegaPrimeOrder16SeriesBase eta n‖ := by
    have hAbsRe :
        |(omegaPrimeOrder16SeriesBase eta n).re| <=
          ‖omegaPrimeOrder16SeriesBase eta n‖ :=
      Complex.abs_re_le_norm _
    rwa [omegaPrimeOrder16SeriesBase_re, abs_of_nonneg hReNonneg] at hAbsRe
  have hPowLe :
      ((n : Real) + (1 / 4 : Real)) ^ 18 <=
        ‖omegaPrimeOrder16SeriesBase eta n‖ ^ 18 :=
    pow_le_pow_left₀ hReNonneg hReLeNorm 18
  have hInv :
      (‖omegaPrimeOrder16SeriesBase eta n‖ ^ 18)⁻¹ <=
        (((n : Real) + (1 / 4 : Real)) ^ 18)⁻¹ :=
    inv_anti₀ (pow_pos hRePos 18) hPowLe
  simpa [omegaPrimeOrder16RealMajorant] using hTerm.trans hInv

theorem omegaPrimeOrder16RealMajorant_summable :
    Summable omegaPrimeOrder16RealMajorant := by
  have h :
      Summable (fun n : Nat =>
        1 / |(n : Real) + (1 / 4 : Real)| ^ (18 : Real)) :=
    (Real.summable_one_div_nat_add_rpow (a := (1 / 4 : Real))
      (s := (18 : Real))).2 (by norm_num)
  refine h.congr ?_
  intro n
  have hNonneg : 0 <= (n : Real) + (1 / 4 : Real) := by
    have hn : 0 <= (n : Real) := Nat.cast_nonneg n
    linarith
  rw [abs_of_nonneg hNonneg]
  simp [omegaPrimeOrder16RealMajorant, one_div]

theorem omegaPrimeOrder16RealMajorant_nonneg (n : Nat) :
    0 <= omegaPrimeOrder16RealMajorant n := by
  unfold omegaPrimeOrder16RealMajorant
  positivity

theorem omegaPrimeOrder16RealMajorant_antitone
    {m n : Nat} (_hm : 0 < m) (hmn : m <= n) :
    omegaPrimeOrder16RealMajorant n <=
      omegaPrimeOrder16RealMajorant m := by
  have hmn' : (m : Real) + (1 / 4 : Real) <= (n : Real) + (1 / 4 : Real) := by
    have hmnR : (m : Real) <= (n : Real) := by
      exact_mod_cast hmn
    linarith
  have hpos : 0 < (m : Real) + (1 / 4 : Real) := by
    have hm0 : 0 <= (m : Real) := Nat.cast_nonneg m
    linarith
  have hpow :
      ((m : Real) + (1 / 4 : Real)) ^ 18 <=
        ((n : Real) + (1 / 4 : Real)) ^ 18 := by
    exact pow_le_pow_left₀ (le_of_lt hpos) hmn' _
  exact inv_anti₀ (pow_pos hpos 18) hpow

def omegaPrimeOrder16CondensedMajorant (k : Nat) : Real :=
  (2 ^ k : Real) * omegaPrimeOrder16RealMajorant (2 ^ k)

theorem omegaPrimeOrder16CondensedMajorant_nonneg (k : Nat) :
    0 <= omegaPrimeOrder16CondensedMajorant k := by
  unfold omegaPrimeOrder16CondensedMajorant
  exact mul_nonneg (by positivity)
    (omegaPrimeOrder16RealMajorant_nonneg _)

theorem omegaPrimeOrder16CondensedMajorant_le_geom (k : Nat) :
    omegaPrimeOrder16CondensedMajorant k <=
      (1 / (2 ^ 17 : Real)) ^ k := by
  have hpowBase : 0 < (2 ^ k : Real) := by
    positivity
  have hbaseLe :
      (2 ^ k : Real) <= (2 ^ k : Real) + (1 / 4 : Real) := by
    norm_num
  have hpow :
      (2 ^ k : Real) ^ 18 <=
        ((2 ^ k : Real) + (1 / 4 : Real)) ^ 18 := by
    exact pow_le_pow_left₀ (le_of_lt hpowBase) hbaseLe _
  have hinv :
      omegaPrimeOrder16RealMajorant (2 ^ k) <=
        1 / (2 ^ k : Real) ^ 18 := by
    have h := inv_anti₀ (pow_pos hpowBase 18) hpow
    simpa [omegaPrimeOrder16RealMajorant, one_div] using h
  calc
    omegaPrimeOrder16CondensedMajorant k
        <= (2 ^ k : Real) * (1 / (2 ^ k : Real) ^ 18) := by
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 1 / (2 ^ k : Real) ^ 17 := by
          field_simp [pow_succ, hpowBase.ne']
    _ = 1 / (2 ^ 17 : Real) ^ k := by
          have hpowEq : (2 ^ k : Real) ^ 17 = (2 ^ 17 : Real) ^ k := by
            calc
              (2 ^ k : Real) ^ 17 = (2 : Real) ^ (k * 17) := by
                simp [pow_mul]
              _ = (2 : Real) ^ (17 * k) := by
                simp [mul_comm]
              _ = (2 ^ 17 : Real) ^ k := by
                simp [pow_mul]
          simp [hpowEq]
    _ = (1 / (2 ^ 17 : Real)) ^ k := by
          simp

theorem omegaPrimeOrder16CondensedMajorant_summable :
    Summable omegaPrimeOrder16CondensedMajorant := by
  have hgeom :
      Summable (fun k : Nat => (1 / (2 ^ 17 : Real)) ^ k) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  refine Summable.of_nonneg_of_le ?_ ?_ hgeom
  · intro k
    exact omegaPrimeOrder16CondensedMajorant_nonneg k
  · intro k
    exact omegaPrimeOrder16CondensedMajorant_le_geom k

theorem omegaPrimeOrder16CondensedMajorant_tsum_le :
    (∑' k : Nat, omegaPrimeOrder16CondensedMajorant k) <=
      (1 - (1 / (2 ^ 17 : Real)))⁻¹ := by
  have hgeom :
      Summable (fun k : Nat => (1 / (2 ^ 17 : Real)) ^ k) := by
    exact summable_geometric_of_lt_one (by positivity) (by norm_num)
  have hle :
      (∑' k : Nat, omegaPrimeOrder16CondensedMajorant k) <=
        ∑' k : Nat, (1 / (2 ^ 17 : Real)) ^ k := by
    exact Summable.tsum_le_tsum
      (fun k => omegaPrimeOrder16CondensedMajorant_le_geom k)
      omegaPrimeOrder16CondensedMajorant_summable hgeom
  have hsum :
      (∑' k : Nat, (1 / (2 ^ 17 : Real)) ^ k) =
        (1 - (1 / (2 ^ 17 : Real)))⁻¹ :=
    tsum_geometric_of_lt_one (by positivity) (by norm_num)
  exact hle.trans_eq hsum

/-- Cauchy-condensation upper bound for the concrete order-16 real majorant. -/
theorem omegaPrimeOrder16RealMajorant_tsum_le_condensed_bound :
    (∑' n : Nat, omegaPrimeOrder16RealMajorant n) <=
      omegaPrimeOrder16RealMajorant 0 +
        (1 - (1 / (2 ^ 17 : Real)))⁻¹ := by
  have hbound :
      ∀ s : Finset Nat,
        ∑ n ∈ s, omegaPrimeOrder16RealMajorant n <=
          omegaPrimeOrder16RealMajorant 0 +
            ∑' k : Nat, omegaPrimeOrder16CondensedMajorant k := by
    intro s
    classical
    by_cases hs : s.Nonempty
    · let N := s.max' hs
      have hsubset : s ⊆ Finset.range (2 ^ (N + 1)) := by
        intro n hn
        have hle : n <= N := by
          simpa [N] using Finset.le_max' s n hn
        have hlt : n < N + 1 := Nat.lt_succ_of_le hle
        have hpow : N + 1 <= 2 ^ (N + 1) :=
          Nat.le_of_lt (Nat.lt_two_pow_self (n := N + 1))
        exact Finset.mem_range.mpr (lt_of_lt_of_le hlt hpow)
      have hsum_le :
          (∑ n ∈ s, omegaPrimeOrder16RealMajorant n) <=
            ∑ n ∈ Finset.range (2 ^ (N + 1)),
              omegaPrimeOrder16RealMajorant n := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
        intro n hn hnot
        exact omegaPrimeOrder16RealMajorant_nonneg n
      have hcond :
          (∑ n ∈ Finset.range (2 ^ (N + 1)),
              omegaPrimeOrder16RealMajorant n) <=
            omegaPrimeOrder16RealMajorant 0 +
              ∑ k ∈ Finset.range (N + 1),
                (2 ^ k : Real) • omegaPrimeOrder16RealMajorant (2 ^ k) := by
        simpa using (Finset.le_sum_condensed
          (f := omegaPrimeOrder16RealMajorant)
          (hf := by
            intro m n hm hmn
            exact omegaPrimeOrder16RealMajorant_antitone (m := m) (n := n)
              hm hmn)
          (n := N + 1))
      have hsum_condensed :
          (∑ k ∈ Finset.range (N + 1),
              (2 ^ k : Real) • omegaPrimeOrder16RealMajorant (2 ^ k)) <=
            ∑' k : Nat, omegaPrimeOrder16CondensedMajorant k := by
        have hsum := (Summable.sum_le_tsum
          (s := Finset.range (N + 1))
          (f := omegaPrimeOrder16CondensedMajorant)
          (hs := by
            intro k hk
            exact omegaPrimeOrder16CondensedMajorant_nonneg k)
          (hf := omegaPrimeOrder16CondensedMajorant_summable))
        simpa [omegaPrimeOrder16CondensedMajorant] using hsum
      exact le_trans hsum_le (le_trans hcond (by
        simpa [omegaPrimeOrder16CondensedMajorant] using
          add_le_add_left hsum_condensed (omegaPrimeOrder16RealMajorant 0)))
    · have hnonneg :
          0 <= omegaPrimeOrder16RealMajorant 0 +
            ∑' k : Nat, omegaPrimeOrder16CondensedMajorant k := by
        exact add_nonneg (omegaPrimeOrder16RealMajorant_nonneg 0)
          (tsum_nonneg (fun k => omegaPrimeOrder16CondensedMajorant_nonneg k))
      simp [Finset.not_nonempty_iff_eq_empty.mp hs, hnonneg]
  have htsum :
      (∑' n : Nat, omegaPrimeOrder16RealMajorant n) <=
        omegaPrimeOrder16RealMajorant 0 +
          ∑' k : Nat, omegaPrimeOrder16CondensedMajorant k :=
    omegaPrimeOrder16RealMajorant_summable.tsum_le_of_sum_le hbound
  exact htsum.trans (by
    simpa [add_comm, add_left_comm, add_assoc] using
      add_le_add_left omegaPrimeOrder16CondensedMajorant_tsum_le
        (omegaPrimeOrder16RealMajorant 0))

def omegaPrimeOrder16CondensedFactorBudgetBound : Real :=
  (Nat.factorial 17 : Real) * ((2 : Real) ^ 19 + 1)

theorem omegaPrimeOrder16CondensedFactorBudgetBound_le_generated_order16Abs :
    omegaPrimeOrder16CondensedFactorBudgetBound <=
      ((186483005989023744000 : Rat) : Real) := by
  norm_num [omegaPrimeOrder16CondensedFactorBudgetBound]

def omegaPrimeGeneratedCoeff (j : Fin 16) : Rat :=
  match j.1 with
  | 0 => omegaPrimeCenterJetM0PrefixRat 128
  | 1 => omegaPrimeCenterJetM1PrefixRat 128
  | 2 => omegaPrimeCenterJetM2PrefixRat 128
  | 3 => omegaPrimeCenterJetM3PrefixRat 128
  | 4 => omegaPrimeCenterJetM4PrefixRat 128
  | 5 => omegaPrimeCenterJetM5PrefixRat 128
  | 6 => omegaPrimeCenterJetM6PrefixRat 128
  | 7 => omegaPrimeCenterJetM7PrefixRat 128
  | 8 => omegaPrimeCenterJetM8PrefixRat 128
  | 9 => omegaPrimeCenterJetM9PrefixRat 128
  | 10 => omegaPrimeCenterJetM10PrefixRat 128
  | 11 => omegaPrimeCenterJetM11PrefixRat 128
  | 12 => omegaPrimeCenterJetM12PrefixRat 128
  | 13 => omegaPrimeCenterJetM13PrefixRat 128
  | 14 => omegaPrimeCenterJetM14PrefixRat 128
  | 15 => omegaPrimeCenterJetM15PrefixRat 128
  | _ => 0

def omegaPrimeGeneratedCoeffErrorAbs (j : Fin 16) : Rat :=
  match j.1 with
  | 0 => (2 / 509 : Rat)
  | 1 => (4 / 259081 : Rat)
  | 2 => (8 / 131872229 : Rat)
  | 3 => (16 / 67122964561 : Rat)
  | 4 => (32 / 34165588961549 : Rat)
  | 5 => (64 / 17390284781428441 : Rat)
  | 6 => (128 / 8851654953747076469 : Rat)
  | 7 => (256 / 4505492371457261922721 : Rat)
  | 8 => (512 / 2293295617071746318664989 : Rat)
  | 9 => (1024 / 1167287469089518876200479401 : Rat)
  | 10 => (2048 / 594149321766565107986044015109 : Rat)
  | 11 => (4096 / 302422004779181639964896403690481 : Rat)
  | 12 => (8192 / 153932800432603454742132269478454829 : Rat)
  | 13 => (16384 / 78351795420195158463745325164533507961 : Rat)
  | 14 => (32768 / 39881063868879335658046370508747555552149 : Rat)
  | 15 => (65536 / 20299461509259581849945602588952505776043841 : Rat)
  | _ => 0

def omegaPrimeGeneratedOrder16Abs : Rat :=
  186483005989023744000

def omegaPrimeGeneratedRemainderAbs : Rat :=
  52283179778952236279870528444304500844084393561089509958806353 /
    13303455094708359561180350112695914185388091637760000000000000000

def omegaPrimeGeneratedRemainderCert :
    Step33Sub0OmegaPrimeTaylorRemainderCert where
  coeff := omegaPrimeGeneratedCoeff
  coeffErrorAbs := omegaPrimeGeneratedCoeffErrorAbs
  order16Abs := omegaPrimeGeneratedOrder16Abs
  remainderAbs := omegaPrimeGeneratedRemainderAbs

theorem omegaPrimeGeneratedCoeffErrorAbs_nonneg :
    ∀ j : Fin 16, 0 <= (omegaPrimeGeneratedCoeffErrorAbs j : Real) := by
  intro j
  fin_cases j <;> norm_num [omegaPrimeGeneratedCoeffErrorAbs]

theorem omegaPrimeGeneratedCoeff_cast (j : Fin 16) :
    (((Nat.factorial j.1 : Real)⁻¹ * (-1 / 2 : Real)) *
        ((Finset.range 128).sum (fun n : Nat =>
          iteratedDeriv j.1
            (fun t : Real => omegaPrimeTrigammaSeriesTerm t n)
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)))) =
      (omegaPrimeGeneratedCoeff j : Real) := by
  fin_cases j
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM0PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM1PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM2PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM3PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM4PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM5PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM6PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM7PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM8PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM9PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM10PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM11PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM12PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM13PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM14PrefixRat_cast 128)
  · simpa [omegaPrimeGeneratedCoeff, step33Sub0OmegaPrimeTaylorCenter] using
      (omegaPrimeCenterJetM15PrefixRat_cast 128)

theorem omegaPrimeGeneratedCoeffErrorAbs_tail_bound (j : Fin 16) :
    1 /
        ((2 : Real) ^ (j.1 + 1) *
          (((128 : Real) - (3 / 4 : Real)) ^ (j.1 + 1))) <=
      (omegaPrimeGeneratedCoeffErrorAbs j : Real) := by
  fin_cases j <;> norm_num [omegaPrimeGeneratedCoeffErrorAbs]

theorem omegaPrimeGeneratedCenterJet :
    ∀ j : Fin 16,
      ‖iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
          (Nat.factorial j.1 : Real) -
        (omegaPrimeGeneratedCoeff j : Real)‖ <=
        (omegaPrimeGeneratedCoeffErrorAbs j : Real) := by
  intro j
  have hBridge :=
    omegaPrimeClosedForm_centerJet_invFactorial_sub_prefix_norm_le_shifted_tsum_majorant_of_le16
      j.1 128 (by omega)
      ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real)
  have hTail :=
    omegaPrimeCenterJet_shifted_tsum_budget_le_generated_bound_of_le15
      j.1 128 (by omega) (by norm_num)
  have hBridge' :
      ‖iteratedDeriv j.1 omegaPrimeClosedForm
          ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
          (Nat.factorial j.1 : Real) -
        (omegaPrimeGeneratedCoeff j : Real)‖ <=
        (Nat.factorial j.1 : Real)⁻¹ *
          ((1 / 2 : Real) *
            (∑' k : Nat, omegaPrimeTrigammaDerivMajorant j.1 (k + 128))) := by
    rw [div_eq_mul_inv]
    convert hBridge using 1
    rw [← omegaPrimeGeneratedCoeff_cast j]
    ring_nf
  exact hBridge'.trans (hTail.trans (omegaPrimeGeneratedCoeffErrorAbs_tail_bound j))

theorem omegaPrimeGeneratedRemainderBudget_le_generated_remainderAbs :
    (∑ j : Fin 16,
        (omegaPrimeGeneratedCoeffErrorAbs j : Real) *
          step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
        (omegaPrimeGeneratedOrder16Abs : Real) *
          step33Sub0OmegaPrimeTaylorRadius ^ 16 /
          (Nat.factorial 16 : Real)
      <= (omegaPrimeGeneratedRemainderAbs : Real) := by
  norm_num [omegaPrimeGeneratedCoeffErrorAbs, omegaPrimeGeneratedOrder16Abs,
    omegaPrimeGeneratedRemainderAbs, step33Sub0OmegaPrimeTaylorRadius,
    Fin.sum_univ_succ]

theorem omegaPrimeOrder16_condensed_factor_budget_le :
    omegaPrimeOrder16SeriesFactor *
        (omegaPrimeOrder16RealMajorant 0 +
          (1 - (1 / (2 ^ 17 : Real)))⁻¹) <=
      omegaPrimeOrder16CondensedFactorBudgetBound := by
  have hgeom :
      (1 - (1 / (2 ^ 17 : Real)))⁻¹ <= (2 : Real) := by
    norm_num
  have hgeomNonneg : 0 <= (1 - (1 / (2 ^ 17 : Real)))⁻¹ := by
    norm_num
  have hFactorNonneg : 0 <= omegaPrimeOrder16SeriesFactor := by
    unfold omegaPrimeOrder16SeriesFactor
    positivity
  have hsum :
      omegaPrimeOrder16RealMajorant 0 +
          (1 - (1 / (2 ^ 17 : Real)))⁻¹ <=
        (2 : Real) ^ 36 + 2 := by
    have h0 : omegaPrimeOrder16RealMajorant 0 = (2 : Real) ^ 36 := by
      norm_num [omegaPrimeOrder16RealMajorant]
    nlinarith
  calc
    omegaPrimeOrder16SeriesFactor *
        (omegaPrimeOrder16RealMajorant 0 +
          (1 - (1 / (2 ^ 17 : Real)))⁻¹)
        <= omegaPrimeOrder16SeriesFactor * ((2 : Real) ^ 36 + 2) := by
          exact mul_le_mul_of_nonneg_left hsum hFactorNonneg
    _ <= omegaPrimeOrder16CondensedFactorBudgetBound := by
          norm_num [omegaPrimeOrder16CondensedFactorBudgetBound,
            omegaPrimeOrder16SeriesFactor]

/-- Convert a summable pointwise majorant for the order-16 series terms into
the absolute `tsum` bound consumed by the OmegaPrime order-16 receiver. -/
theorem omegaPrimeOrder16Series_abs_le_of_term_majorant
    (eta B : Real) (g : Nat -> Real)
    (hg : Summable g)
    (hTerm :
      ∀ n : Nat, |omegaPrimeOrder16SeriesTerm eta n| <= g n)
    (hSum : (∑' n : Nat, g n) <= B) :
    |omegaPrimeOrder16Series eta| <= B := by
  have hTermAbs :
      Summable (fun n : Nat => |omegaPrimeOrder16SeriesTerm eta n|) := by
    exact
      Summable.of_nonneg_of_le (f := g)
        (g := fun n : Nat => |omegaPrimeOrder16SeriesTerm eta n|)
        (fun n => abs_nonneg _) hTerm hg
  have hNorm :
      ‖∑' n : Nat, omegaPrimeOrder16SeriesTerm eta n‖ <=
        ∑' n : Nat, ‖omegaPrimeOrder16SeriesTerm eta n‖ := by
    exact norm_tsum_le_tsum_norm (by
      simpa [Real.norm_eq_abs] using hTermAbs)
  have hAbsSum :
      (∑' n : Nat, |omegaPrimeOrder16SeriesTerm eta n|) <=
        ∑' n : Nat, g n := by
    exact Summable.tsum_le_tsum hTerm hTermAbs hg
  have hNorm' :
      |∑' n : Nat, omegaPrimeOrder16SeriesTerm eta n| <=
        ∑' n : Nat, |omegaPrimeOrder16SeriesTerm eta n| := by
    simpa [Real.norm_eq_abs] using hNorm
  simpa [omegaPrimeOrder16Series] using hNorm'.trans (hAbsSum.trans hSum)

/-- Same-normalization order-16 series bound from the concrete real majorant
`((n + 1/4)^18)⁻¹`. -/
theorem omegaPrimeOrder16Series_abs_le_real_majorant_tsum
    (eta B : Real)
    (hMajorantSum : (∑' n : Nat, omegaPrimeOrder16RealMajorant n) <= B) :
    |omegaPrimeOrder16Series eta| <= B :=
  omegaPrimeOrder16Series_abs_le_of_term_majorant eta B
    omegaPrimeOrder16RealMajorant
    omegaPrimeOrder16RealMajorant_summable
    (omegaPrimeOrder16SeriesTerm_abs_le_real_majorant eta)
    hMajorantSum

/-- Same-normalization order-16 series bound using the concrete real majorant's
actual `tsum` as the budget. -/
theorem omegaPrimeOrder16Series_abs_le_real_majorant_self_tsum
    (eta : Real) :
    |omegaPrimeOrder16Series eta| <=
      ∑' n : Nat, omegaPrimeOrder16RealMajorant n :=
  omegaPrimeOrder16Series_abs_le_real_majorant_tsum eta
    (∑' n : Nat, omegaPrimeOrder16RealMajorant n) le_rfl

/-- Algebraic receiver for the active OmegaPrime order-16 bound.

This theorem does not prove the termwise-differentiation bridge.  It isolates
the remaining analytic obligation into `hDerivEq` plus a same-normalization
absolute bound for the resulting `tsum`. -/
theorem order16_bound_of_tsum_abs_bound
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (B : Real)
    (hSeriesAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |omegaPrimeOrder16Series eta| <= B)
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor * B <= (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta) :
    ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
      ‖iteratedDeriv 16 omegaPrimeClosedForm eta‖ <=
        (data.order16Abs : Real) := by
  intro eta heta
  have hFactorNonneg : 0 <= omegaPrimeOrder16SeriesFactor := by
    unfold omegaPrimeOrder16SeriesFactor
    positivity
  rw [hDerivEq eta heta]
  rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hFactorNonneg]
  exact
    (mul_le_mul_of_nonneg_left (hSeriesAbs eta heta) hFactorNonneg).trans
      hFactorBudget

/-- Checked-smooth `Valid` constructor using the isolated order-16 `tsum`
surface.

The proof-grade payload still has to provide the center-jet inequalities,
the termwise-differentiation identity `hDerivEq`, the absolute `tsum` bound,
and the rational remainder budget. -/
theorem Valid.of_order16_tsum_abs_bound_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (B : Real)
    (hSeriesAbs :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        |omegaPrimeOrder16Series eta| <= B)
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor * B <= (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_bound_checked_smooth data hCoeffErrorNonneg hCenterJet
    (order16_bound_of_tsum_abs_bound data B hSeriesAbs hFactorBudget hDerivEq)
    hRemainderBudget

/-- Checked-smooth `Valid` constructor whose order-16 series bound is supplied
by a generated summable term majorant.  This closes the `hSeriesAbs` interface;
the termwise-differentiation identity and rational budget remain explicit
payload obligations. -/
theorem Valid.of_order16_tsum_majorant_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (g : Real -> Nat -> Real)
    (B : Real)
    (hMajorantSummable :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10), Summable (g eta))
    (hTermMajorant :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        ∀ n : Nat, |omegaPrimeOrder16SeriesTerm eta n| <= g eta n)
    (hMajorantSum :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        (∑' n : Nat, g eta n) <= B)
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor * B <= (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_tsum_abs_bound_checked_smooth data hCoeffErrorNonneg
    hCenterJet B
    (fun eta heta =>
      omegaPrimeOrder16Series_abs_le_of_term_majorant eta B (g eta)
        (hMajorantSummable eta heta) (hTermMajorant eta heta)
        (hMajorantSum eta heta))
    hFactorBudget hDerivEq hRemainderBudget

/-- Checked-smooth `Valid` constructor specialized to the concrete real
order-16 majorant `((n + 1/4)^18)⁻¹`.  The only remaining series payload is a
summability proof and a rational upper bound for its `tsum`. -/
theorem Valid.of_order16_real_majorant_tsum_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (B : Real)
    (hMajorantSum :
      (∑' n : Nat, omegaPrimeOrder16RealMajorant n) <= B)
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor * B <= (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_tsum_abs_bound_checked_smooth data hCoeffErrorNonneg
    hCenterJet B
    (fun eta _ =>
      omegaPrimeOrder16Series_abs_le_real_majorant_tsum eta B
        hMajorantSum)
    hFactorBudget hDerivEq hRemainderBudget

/-- Checked-smooth `Valid` constructor using the concrete real majorant's
actual `tsum` as the order-16 budget.  The remaining numeric obligation is the
same-unit factor-budget comparison for this `tsum`. -/
theorem Valid.of_order16_real_majorant_self_tsum_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor *
          (∑' n : Nat, omegaPrimeOrder16RealMajorant n) <=
        (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_real_majorant_tsum_checked_smooth data hCoeffErrorNonneg
    hCenterJet (∑' n : Nat, omegaPrimeOrder16RealMajorant n) le_rfl
    hFactorBudget hDerivEq hRemainderBudget

/-- Checked-smooth `Valid` constructor using the explicit
Cauchy-condensation/geometric upper bound for the concrete order-16 majorant.
The remaining numeric obligation is the rational factor-budget comparison
against this closed expression. -/
theorem Valid.of_order16_condensed_majorant_bound_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hFactorBudget :
      omegaPrimeOrder16SeriesFactor *
          (omegaPrimeOrder16RealMajorant 0 +
            (1 - (1 / (2 ^ 17 : Real)))⁻¹) <=
        (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid := by
  refine Valid.of_order16_real_majorant_tsum_checked_smooth data
    hCoeffErrorNonneg hCenterJet
    (omegaPrimeOrder16RealMajorant 0 +
      (1 - (1 / (2 ^ 17 : Real)))⁻¹)
    omegaPrimeOrder16RealMajorant_tsum_le_condensed_bound ?_ hDerivEq
    hRemainderBudget
  exact hFactorBudget

/-- Checked-smooth `Valid` constructor whose order-16 numeric payload is a
single integer lower bound for `data.order16Abs`. -/
theorem Valid.of_order16_integer_budget_checked_smooth
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hIntegerBudget :
      omegaPrimeOrder16CondensedFactorBudgetBound <=
        (data.order16Abs : Real))
    (hDerivEq :
      ∀ eta ∈ Set.Icc (0 : Real) ((1 : Real) / 10),
        iteratedDeriv 16 omegaPrimeClosedForm eta =
          -omegaPrimeOrder16SeriesFactor * omegaPrimeOrder16Series eta)
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_condensed_majorant_bound_checked_smooth data
    hCoeffErrorNonneg hCenterJet
    (omegaPrimeOrder16_condensed_factor_budget_le.trans hIntegerBudget)
    hDerivEq hRemainderBudget

/-- Checked-smooth `Valid` constructor after the OmegaPrime order-16
closed-form derivative identity has been proved locally.  Generated payloads
no longer need to supply `hDerivEq`; they only supply the center jet, integer
order-16 budget, and Taylor remainder budget. -/
theorem Valid.of_order16_integer_budget_checked_deriv
    (data : Step33Sub0OmegaPrimeTaylorRemainderCert)
    (hCoeffErrorNonneg :
      ∀ j, 0 <= (data.coeffErrorAbs j : Real))
    (hCenterJet :
      ∀ j : Fin 16,
        ‖iteratedDeriv j.1 omegaPrimeClosedForm
            ((step33Sub0OmegaPrimeTaylorCenter : Rat) : Real) /
            (Nat.factorial j.1 : Real) -
          (data.coeff j : Real)‖ <=
          (data.coeffErrorAbs j : Real))
    (hIntegerBudget :
      omegaPrimeOrder16CondensedFactorBudgetBound <=
        (data.order16Abs : Real))
    (hRemainderBudget :
      (∑ j : Fin 16,
          (data.coeffErrorAbs j : Real) *
            step33Sub0OmegaPrimeTaylorRadius ^ j.1) +
          (data.order16Abs : Real) * step33Sub0OmegaPrimeTaylorRadius ^ 16 /
            (Nat.factorial 16 : Real)
        <= (data.remainderAbs : Real)) :
    data.Valid :=
  Valid.of_order16_integer_budget_checked_smooth data
    hCoeffErrorNonneg hCenterJet hIntegerBudget
    (fun eta _ => omegaPrimeClosedForm_iteratedDeriv16_eq eta)
    hRemainderBudget

theorem omegaPrimeGeneratedRemainderCert_valid :
    omegaPrimeGeneratedRemainderCert.Valid := by
  refine Valid.of_order16_integer_budget_checked_deriv
    omegaPrimeGeneratedRemainderCert ?_ ?_ ?_ ?_
  · simpa [omegaPrimeGeneratedRemainderCert] using
      omegaPrimeGeneratedCoeffErrorAbs_nonneg
  · simpa [omegaPrimeGeneratedRemainderCert] using
      omegaPrimeGeneratedCenterJet
  · simpa [omegaPrimeGeneratedRemainderCert, omegaPrimeGeneratedOrder16Abs] using
      omegaPrimeOrder16CondensedFactorBudgetBound_le_generated_order16Abs
  · simpa [omegaPrimeGeneratedRemainderCert] using
      omegaPrimeGeneratedRemainderBudget_le_generated_remainderAbs

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
