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
