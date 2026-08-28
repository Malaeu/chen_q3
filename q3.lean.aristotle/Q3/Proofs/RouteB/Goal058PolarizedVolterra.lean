import Q3.Proofs.RouteB.G6N1SelectedFerrersHilbertPairing
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

open Matrix
open scoped BigOperators Interval

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def goal058ModeFrequency (mode : ι → ℤ) (k : ι) : ℂ :=
  (2 * Real.pi * (mode k : ℝ) : ℝ) * Complex.I

def goal058FiniteFourier (mode : ι → ℤ) (u : ι → ℂ) (w : ℝ) : ℂ :=
  ∑ k, u k * Complex.exp (goal058ModeFrequency mode k * w)

def goal058PolarizedHilbertWeight
    (mode : ι → ℤ) (x q : ι → ℂ) (k : ι) : ℂ :=
  let H := dividedDifferenceHilbertC (fun j => (mode j : ℝ))
  starRingEnd ℂ (x k) * (H *ᵥ q) k +
    starRingEnd ℂ ((H *ᵥ x) k) * q k

def goal058VolterraAlpha
    (mode : ι → ℤ) (x q : ι → ℂ) (k : ι) : ℂ :=
  goal058PolarizedHilbertWeight mode x q k / (Real.pi * Complex.I)

def goal058VolterraBeta (x q : ι → ℂ) (k : ι) : ℂ :=
  2 * starRingEnd ℂ (x k) * q k

def goal058PolarizedVolterraIntegral
    (mode : ι → ℤ) (x q : ι → ℂ) (w : ℝ) : ℂ :=
  ∫ t in (0 : ℝ)..w,
    goal058FiniteFourier mode (starRingEnd ℂ ∘ x) t *
        goal058FiniteFourier mode q (w - t) +
      goal058FiniteFourier mode q t *
        goal058FiniteFourier mode (starRingEnd ℂ ∘ x) (w - t)

def goal058PolarizedVolterraClosed
    (mode : ι → ℤ) (x q : ι → ℂ) (w : ℝ) : ℂ :=
  ∑ k, (goal058VolterraAlpha mode x q k +
      goal058VolterraBeta x q k * w) *
    Complex.exp (goal058ModeFrequency mode k * w)

def goal058VolterraAlphaRaw
    (mode : ι → ℤ) (x q : ι → ℂ) (k : ι) : ℂ :=
  ∑ j ∈ Finset.univ.erase k,
    2 * (starRingEnd ℂ (x k) * q j +
      q k * starRingEnd ℂ (x j)) /
        (goal058ModeFrequency mode k - goal058ModeFrequency mode j)

def goal058VolterraPairClosed
    (mode : ι → ℤ) (x q : ι → ℂ) (w : ℝ) (i j : ι) : ℂ :=
  (starRingEnd ℂ (x i) * q j + q i * starRingEnd ℂ (x j)) *
    if i = j then
      w * Complex.exp (goal058ModeFrequency mode i * w)
    else
      (Complex.exp (goal058ModeFrequency mode i * w) -
          Complex.exp (goal058ModeFrequency mode j * w)) /
        (goal058ModeFrequency mode i - goal058ModeFrequency mode j)

private theorem goal058_integral_exp_convolution_offdiag
    (a b : ℂ) (hab : a ≠ b) (w : ℝ) :
    (∫ t in (0 : ℝ)..w,
      Complex.exp (a * t) * Complex.exp (b * (w - t))) =
      (Complex.exp (a * w) - Complex.exp (b * w)) / (a - b) := by
  have hpoint (t : ℝ) :
      Complex.exp (a * t) * Complex.exp (b * (w - t)) =
        Complex.exp (b * w) * Complex.exp ((a - b) * t) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_exp_mul_complex (sub_ne_zero.mpr hab)]
  have hexp :
      Complex.exp (a * w) =
        Complex.exp (b * w) * Complex.exp ((a - b) * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [hexp]
  simp
  ring

private theorem goal058_integral_exp_convolution_diag
    (a : ℂ) (w : ℝ) :
    (∫ t in (0 : ℝ)..w,
      Complex.exp (a * t) * Complex.exp (a * (w - t))) =
      w * Complex.exp (a * w) := by
  have hpoint (t : ℝ) :
      Complex.exp (a * t) * Complex.exp (a * (w - t)) =
        Complex.exp (a * w) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  simp_rw [hpoint]
  simp

omit [Fintype ι] [DecidableEq ι] in
private theorem goal058ModeFrequency_ne
    (mode : ι → ℤ) (hmode : Function.Injective mode)
    {i j : ι} (hij : i ≠ j) :
    goal058ModeFrequency mode i ≠ goal058ModeFrequency mode j := by
  intro h
  have hpiI : ((2 * Real.pi : ℝ) : ℂ) * Complex.I ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero))
      Complex.I_ne_zero
  have hm : ((mode i : ℝ) : ℂ) = (mode j : ℝ) := by
    apply mul_left_cancel₀ hpiI
    simpa [goal058ModeFrequency, mul_assoc, mul_left_comm, mul_comm] using h
  have hmR : (mode i : ℝ) = mode j := by exact_mod_cast hm
  have hmZ : mode i = mode j := by exact_mod_cast hmR
  exact hij (hmode hmZ)

private theorem goal058HilbertMulVec_eq_sum_erase
    (mode : ι → ℤ) (u : ι → ℂ) (k : ι) :
    (dividedDifferenceHilbertC (fun j => (mode j : ℝ)) *ᵥ u) k =
      ∑ j ∈ Finset.univ.erase k,
        (((mode k : ℝ) - mode j)⁻¹ : ℂ) * u j := by
  classical
  rw [Matrix.mulVec, dotProduct]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ k)]
  have hk : dividedDifferenceHilbertC (fun j => (mode j : ℝ)) k k * u k = 0 := by
    simp [dividedDifferenceHilbertC, dividedDifferenceHilbert]
  rw [hk, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  have h : k ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
  simp [dividedDifferenceHilbertC, dividedDifferenceHilbert, h]

private theorem goal058VolterraAlphaRaw_eq
    (mode : ι → ℤ) (hmode : Function.Injective mode)
    (x q : ι → ℂ) (k : ι) :
    goal058VolterraAlphaRaw mode x q k =
      goal058VolterraAlpha mode x q k := by
  classical
  rw [goal058VolterraAlpha, goal058PolarizedHilbertWeight]
  rw [goal058HilbertMulVec_eq_sum_erase,
    goal058HilbertMulVec_eq_sum_erase]
  rw [map_sum]
  simp_rw [map_mul]
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  rw [goal058VolterraAlphaRaw, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjk : j ≠ k := Finset.ne_of_mem_erase hj
  have hmodeZ : mode k ≠ mode j := Ne.symm (hmode.ne hjk)
  have hdiffR : (mode k : ℝ) - mode j ≠ 0 := by
    exact sub_ne_zero.mpr (by exact_mod_cast hmodeZ)
  have hfreq :
      goal058ModeFrequency mode k - goal058ModeFrequency mode j ≠ 0 :=
    sub_ne_zero.mpr (goal058ModeFrequency_ne mode hmode (Ne.symm hjk))
  simp only [map_inv₀, map_sub, Complex.conj_ofReal, map_intCast]
  rw [goal058ModeFrequency, goal058ModeFrequency]
  push_cast
  field_simp [hdiffR, hfreq]

private theorem goal058PolarizedVolterraIntegral_eq_pair_sum
    (mode : ι → ℤ) (hmode : Function.Injective mode)
    (x q : ι → ℂ) (w : ℝ) :
    goal058PolarizedVolterraIntegral mode x q w =
      ∑ i, ∑ j, goal058VolterraPairClosed mode x q w i j := by
  classical
  have hexpand (t : ℝ) :
      goal058FiniteFourier mode (starRingEnd ℂ ∘ x) t *
          goal058FiniteFourier mode q (w - t) +
        goal058FiniteFourier mode q t *
          goal058FiniteFourier mode (starRingEnd ℂ ∘ x) (w - t) =
      ∑ i, ∑ j,
        (starRingEnd ℂ (x i) * q j + q i * starRingEnd ℂ (x j)) *
          (Complex.exp (goal058ModeFrequency mode i * t) *
            Complex.exp (goal058ModeFrequency mode j * (w - t))) := by
    simp only [goal058FiniteFourier, Function.comp_apply]
    rw [Finset.sum_mul, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have harg :
        goal058ModeFrequency mode j * (w - t) =
          -(t * goal058ModeFrequency mode j) +
            goal058ModeFrequency mode j * w := by
      ring
    push_cast
    rw [harg]
    ring
  rw [goal058PolarizedVolterraIntegral]
  simp_rw [hexpand]
  rw [intervalIntegral.integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [intervalIntegral.integral_const_mul]
      rw [goal058VolterraPairClosed]
      by_cases hij : i = j
      · subst j
        rw [if_pos rfl, goal058_integral_exp_convolution_diag]
      · rw [if_neg hij,
          goal058_integral_exp_convolution_offdiag _ _
            (goal058ModeFrequency_ne mode hmode hij) w]
    · intro j _
      exact (by fun_prop : Continuous (fun t : ℝ =>
        (starRingEnd ℂ (x i) * q j + q i * starRingEnd ℂ (x j)) *
          (Complex.exp (goal058ModeFrequency mode i * t) *
            Complex.exp (goal058ModeFrequency mode j * (w - t))))).intervalIntegrable 0 w
  · intro i _
    exact (by fun_prop : Continuous (fun t : ℝ =>
      ∑ j,
        (starRingEnd ℂ (x i) * q j + q i * starRingEnd ℂ (x j)) *
          (Complex.exp (goal058ModeFrequency mode i * t) *
            Complex.exp (goal058ModeFrequency mode j * (w - t))))).intervalIntegrable 0 w

private theorem goal058VolterraPair_sum_eq_raw_closed
    (mode : ι → ℤ) (hmode : Function.Injective mode)
    (x q : ι → ℂ) (w : ℝ) :
    (∑ i, ∑ j, goal058VolterraPairClosed mode x q w i j) =
      ∑ i, (goal058VolterraAlphaRaw mode x q i +
        goal058VolterraBeta x q i * w) *
          Complex.exp (goal058ModeFrequency mode i * w) := by
  classical
  let A : ι → ι → ℂ := fun i j =>
    starRingEnd ℂ (x i) * q j + q i * starRingEnd ℂ (x j)
  let E : ι → ℂ := fun i =>
    Complex.exp (goal058ModeFrequency mode i * w)
  let D : ι → ℂ := fun i => goal058VolterraBeta x q i * w * E i
  let F : ι → ι → ℂ := fun i j =>
    if i = j then 0 else
      A i j * E i /
        (goal058ModeFrequency mode i - goal058ModeFrequency mode j)
  have hpair (i j : ι) :
      goal058VolterraPairClosed mode x q w i j =
        if i = j then D i else F i j + F j i := by
    by_cases hij : i = j
    · subst j
      simp [goal058VolterraPairClosed, D, E, goal058VolterraBeta]
      ring
    · rw [goal058VolterraPairClosed, if_neg hij, if_neg hij]
      have hji : j ≠ i := Ne.symm hij
      simp only [F, if_neg hij, if_neg hji, A, E]
      have hfreq :
          goal058ModeFrequency mode i - goal058ModeFrequency mode j ≠ 0 :=
        sub_ne_zero.mpr (goal058ModeFrequency_ne mode hmode hij)
      have hfreq' :
          goal058ModeFrequency mode j - goal058ModeFrequency mode i ≠ 0 :=
        sub_ne_zero.mpr (goal058ModeFrequency_ne mode hmode hji)
      field_simp [hfreq, hfreq']
      ring
  have hFdiag (i : ι) : F i i = 0 := by simp [F]
  have hrow (i : ι) :
      (∑ j, goal058VolterraPairClosed mode x q w i j) =
        D i + ∑ j, (F i j + F j i) := by
    calc
      (∑ j, goal058VolterraPairClosed mode x q w i j) =
          (∑ j ∈ Finset.univ.erase i,
            goal058VolterraPairClosed mode x q w i j) +
              goal058VolterraPairClosed mode x q w i i := by
            rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      _ = (∑ j ∈ Finset.univ.erase i, (F i j + F j i)) + D i := by
            apply congrArg₂ (· + ·)
            · apply Finset.sum_congr rfl
              intro j hj
              rw [hpair, if_neg (Ne.symm (Finset.ne_of_mem_erase hj))]
            · rw [hpair, if_pos rfl]
      _ = D i + ∑ j, (F i j + F j i) := by
            have hs : (∑ j, (F i j + F j i)) =
                ∑ j ∈ Finset.univ.erase i, (F i j + F j i) := by
              have hh := Finset.sum_erase_add
                (s := Finset.univ) (f := fun j => F i j + F j i)
                (Finset.mem_univ i)
              have hz : (fun j => F i j + F j i) i = 0 := by
                change F i i + F i i = 0
                simp [hFdiag]
              rw [hz, add_zero] at hh
              exact hh.symm
            rw [hs]
            ring
  simp_rw [hrow]
  rw [Finset.sum_add_distrib]
  simp_rw [Finset.sum_add_distrib]
  have hswap : (∑ i, ∑ j, F j i) = ∑ i, ∑ j, F i j := by
    rw [Finset.sum_comm]
  rw [hswap]
  rw [← two_mul]
  have hraw (i : ι) :
      2 * ∑ j, F i j = goal058VolterraAlphaRaw mode x q i * E i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i), hFdiag, add_zero]
    rw [goal058VolterraAlphaRaw]
    rw [Finset.sum_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.ne_of_mem_erase hj)
    simp [F, hij, A]
    ring
  rw [Finset.mul_sum]
  simp_rw [hraw]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp [D, E]
  ring

theorem goal058PolarizedVolterraIntegral_eq_closed
    (mode : ι → ℤ) (hmode : Function.Injective mode)
    (x q : ι → ℂ) (w : ℝ) :
    goal058PolarizedVolterraIntegral mode x q w =
      goal058PolarizedVolterraClosed mode x q w := by
  rw [goal058PolarizedVolterraIntegral_eq_pair_sum mode hmode x q w]
  rw [goal058VolterraPair_sum_eq_raw_closed mode hmode x q w]
  rw [goal058PolarizedVolterraClosed]
  apply Finset.sum_congr rfl
  intro i _
  rw [goal058VolterraAlphaRaw_eq mode hmode x q i]

theorem goal058PolarizedHilbertWeight_sum_eq_zero
    (mode : ι → ℤ) (x q : ι → ℂ) :
    ∑ k, goal058PolarizedHilbertWeight mode x q k = 0 := by
  classical
  let H : Matrix ι ι ℂ :=
    dividedDifferenceHilbertC (fun j => (mode j : ℝ))
  have hHreal (i j : ι) : starRingEnd ℂ (H i j) = H i j := by
    simp [H, dividedDifferenceHilbertC]
  have hHanti (i j : ι) : H j i = -H i j := by
    dsimp [H, dividedDifferenceHilbertC]
    rw [dividedDifferenceHilbert_antisymm]
    push_cast
    rfl
  have hconjMulVec (i : ι) :
      starRingEnd ℂ ((H *ᵥ x) i) =
        ∑ j, H i j * starRingEnd ℂ (x j) := by
    rw [Matrix.mulVec, dotProduct, map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_mul, hHreal]
  simp only [goal058PolarizedHilbertWeight]
  rw [Finset.sum_add_distrib]
  have hsecond :
      (∑ k, starRingEnd ℂ ((H *ᵥ x) k) * q k) =
        -(∑ k, starRingEnd ℂ (x k) * (H *ᵥ q) k) := by
    simp_rw [hconjMulVec, Matrix.mulVec, dotProduct,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hHanti]
    ring
  rw [hsecond]
  ring

#print axioms goal058PolarizedVolterraIntegral_eq_closed
#print axioms goal058PolarizedHilbertWeight_sum_eq_zero

end Q3.RouteB
