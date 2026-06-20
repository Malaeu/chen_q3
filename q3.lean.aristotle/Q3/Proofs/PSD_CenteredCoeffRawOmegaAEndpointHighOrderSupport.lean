import Q3.DigammaSeries
import Q3.DigammaRemainder
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

end Step33
end PSDpd
end Q3
