import Q3.Proofs.PrimeCert.IntervalLemmas

set_option linter.mathlibStandardSet false

/-!
Reusable `Real.exp` interval helpers for generated PSD-pd scalar certificates.

This module factors the checked Step32G Q-row Taylor pattern into a small public
helper.  It is intended for Step21-style proof generators that reduce scalar
integrals to finite rational combinations of exponentials.
-/

noncomputable section

open MeasureTheory

namespace Q3
namespace PSDpd

def expHalfTaylorS (x : Real) (n : Nat) : Real :=
  ∑ m ∈ Finset.range n, (x / 2) ^ m / (Nat.factorial m)

def expHalfTaylorE (x : Real) (n : Nat) : Real :=
  |x / 2| ^ n * ((n.succ : Real) / (Nat.factorial n * n))

def expQuarterTaylorS (x : Real) (n : Nat) : Real :=
  ∑ m ∈ Finset.range n, (x / 4) ^ m / (Nat.factorial m)

def expQuarterTaylorE (x : Real) (n : Nat) : Real :=
  |x / 4| ^ n * ((n.succ : Real) / (Nat.factorial n * n))

lemma exp_abs_sub_le_of_half_taylor
    (x m r : Real) {n : Nat}
    (hn : 0 < n)
    (hy : |x / 2| <= (1 : Real))
    (hlow0 : 0 <= expHalfTaylorS x n - expHalfTaylorE x n)
    (htargetLow : m - r <= (expHalfTaylorS x n - expHalfTaylorE x n) ^ 2)
    (htargetHigh : (expHalfTaylorS x n + expHalfTaylorE x n) ^ 2 <= m + r) :
    |Real.exp x - m| <= r := by
  have hbound : |Real.exp (x / 2) - expHalfTaylorS x n| <= expHalfTaylorE x n := by
    simpa [expHalfTaylorS, expHalfTaylorE] using
      (Real.exp_bound (x := x / 2) hy (n := n) hn)
  have hlow : expHalfTaylorS x n - expHalfTaylorE x n <= Real.exp (x / 2) := by
    have h := (abs_sub_le_iff.mp hbound).2
    linarith
  have hhigh : Real.exp (x / 2) <= expHalfTaylorS x n + expHalfTaylorE x n := by
    have h := (abs_sub_le_iff.mp hbound).1
    linarith
  have hexp : Real.exp x = Real.exp (x / 2) ^ 2 := by
    exact Q3.Proofs.PrimeCert.exp_eq_pow_div_nat x (n := 2) (by norm_num)
  have hpowLow : (expHalfTaylorS x n - expHalfTaylorE x n) ^ 2 <= Real.exp x := by
    rw [hexp]
    exact pow_le_pow_left₀ hlow0 hlow 2
  have hpowHigh : Real.exp x <= (expHalfTaylorS x n + expHalfTaylorE x n) ^ 2 := by
    rw [hexp]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hhigh 2
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

lemma exp_abs_sub_le_of_quarter_taylor
    (x m r : Real) {n : Nat}
    (hn : 0 < n)
    (hy : |x / 4| <= (1 : Real))
    (hlow0 : 0 <= expQuarterTaylorS x n - expQuarterTaylorE x n)
    (htargetLow : m - r <= (expQuarterTaylorS x n - expQuarterTaylorE x n) ^ 4)
    (htargetHigh : (expQuarterTaylorS x n + expQuarterTaylorE x n) ^ 4 <= m + r) :
    |Real.exp x - m| <= r := by
  have hbound : |Real.exp (x / 4) - expQuarterTaylorS x n| <= expQuarterTaylorE x n := by
    simpa [expQuarterTaylorS, expQuarterTaylorE] using
      (Real.exp_bound (x := x / 4) hy (n := n) hn)
  have hlow : expQuarterTaylorS x n - expQuarterTaylorE x n <= Real.exp (x / 4) := by
    have h := (abs_sub_le_iff.mp hbound).2
    linarith
  have hhigh : Real.exp (x / 4) <= expQuarterTaylorS x n + expQuarterTaylorE x n := by
    have h := (abs_sub_le_iff.mp hbound).1
    linarith
  have hexp : Real.exp x = Real.exp (x / 4) ^ 4 := by
    exact Q3.Proofs.PrimeCert.exp_eq_pow_div_nat x (n := 4) (by norm_num)
  have hpowLow : (expQuarterTaylorS x n - expQuarterTaylorE x n) ^ 4 <= Real.exp x := by
    rw [hexp]
    exact pow_le_pow_left₀ hlow0 hlow 4
  have hpowHigh : Real.exp x <= (expQuarterTaylorS x n + expQuarterTaylorE x n) ^ 4 := by
    rw [hexp]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) hhigh 4
  rw [abs_sub_le_iff]
  constructor <;> nlinarith

lemma exp_mul_antideriv_hasDerivAt
    (lam : Real) (hlam : lam ≠ 0) (x : Real) :
    HasDerivAt (fun y : Real => Real.exp (lam * y) / lam)
      (Real.exp (lam * x)) x := by
  have hlin : HasDerivAt (fun y : Real => lam * y) lam x := by
    simpa using ((hasDerivAt_id x).const_mul lam)
  have hexp : HasDerivAt (fun y : Real => Real.exp (lam * y))
      (Real.exp (lam * x) * lam) x := by
    simpa using hlin.exp
  have hdiv := hexp.div_const lam
  convert hdiv using 1
  field_simp [hlam]

lemma intervalIntegral_exp_mul_eq
    (lam a b : Real) (hlam : lam ≠ 0) :
    ∫ x in a..b, Real.exp (lam * x) =
      Real.exp (lam * b) / lam - Real.exp (lam * a) / lam := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun x : Real => Real.exp (lam * x) / lam)
    (f' := fun x : Real => Real.exp (lam * x))
    (fun x _hx => exp_mul_antideriv_hasDerivAt lam hlam x)
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).intervalIntegrable a b)

lemma exp_mul_pow_succ_antideriv_step_hasDerivAt
    (lam : Real) (hlam : lam ≠ 0) (n : Nat) (x : Real) :
    HasDerivAt (fun y : Real => Real.exp (lam * y) * y ^ (n + 1) / lam)
      (Real.exp (lam * x) * x ^ (n + 1) +
        (((n + 1 : Nat) : Real) / lam) * (Real.exp (lam * x) * x ^ n)) x := by
  have hlin : HasDerivAt (fun y : Real => lam * y) lam x := by
    simpa using ((hasDerivAt_id x).const_mul lam)
  have hexp : HasDerivAt (fun y : Real => Real.exp (lam * y))
      (Real.exp (lam * x) * lam) x := by
    simpa using hlin.exp
  have hpow : HasDerivAt (fun y : Real => y ^ (n + 1))
      (((n + 1 : Nat) : Real) * x ^ n) x := by
    simpa [Nat.add_sub_cancel] using
      (hasDerivAt_pow (n + 1) x :
        HasDerivAt (fun y : Real => y ^ (n + 1))
          (((n + 1 : Nat) : Real) * x ^ ((n + 1) - 1)) x)
  have hmul := hexp.mul hpow
  have hdiv := hmul.div_const lam
  convert hdiv using 1
  field_simp [hlam]

lemma intervalIntegral_exp_mul_pow_succ_eq
    (lam a b : Real) (hlam : lam ≠ 0) (n : Nat) :
    ∫ x in a..b, Real.exp (lam * x) * x ^ (n + 1) =
      (Real.exp (lam * b) * b ^ (n + 1) -
          Real.exp (lam * a) * a ^ (n + 1)) / lam -
        (((n + 1 : Nat) : Real) / lam) *
          ∫ x in a..b, Real.exp (lam * x) * x ^ n := by
  have hIntMain : IntervalIntegrable
      (fun x : Real => Real.exp (lam * x) * x ^ (n + 1)) volume a b := by
    exact (by
      fun_prop :
        Continuous (fun x : Real => Real.exp (lam * x) * x ^ (n + 1))
      ).intervalIntegrable a b
  have hIntPrev : IntervalIntegrable
      (fun x : Real => Real.exp (lam * x) * x ^ n) volume a b := by
    exact (by
      fun_prop :
        Continuous (fun x : Real => Real.exp (lam * x) * x ^ n)
      ).intervalIntegrable a b
  have hIntDeriv : IntervalIntegrable
      (fun x : Real =>
        Real.exp (lam * x) * x ^ (n + 1) +
          (((n + 1 : Nat) : Real) / lam) *
            (Real.exp (lam * x) * x ^ n)) volume a b := by
    exact hIntMain.add
      (hIntPrev.const_mul (((n + 1 : Nat) : Real) / lam))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := a) (b := b)
    (f := fun y : Real => Real.exp (lam * y) * y ^ (n + 1) / lam)
    (f' := fun x : Real =>
      Real.exp (lam * x) * x ^ (n + 1) +
        (((n + 1 : Nat) : Real) / lam) *
          (Real.exp (lam * x) * x ^ n))
    (fun x _hx =>
      exp_mul_pow_succ_antideriv_step_hasDerivAt lam hlam n x)
    hIntDeriv
  rw [
    intervalIntegral.integral_add hIntMain
      (hIntPrev.const_mul (((n + 1 : Nat) : Real) / lam)),
    intervalIntegral.integral_const_mul] at hftc
  have hmain := eq_sub_of_add_eq hftc
  convert hmain using 1
  ring_nf

def expMulPowIntegral (lam a b : Real) : Nat -> Real
  | 0 => Real.exp (lam * b) / lam - Real.exp (lam * a) / lam
  | n + 1 =>
      (Real.exp (lam * b) * b ^ (n + 1) -
          Real.exp (lam * a) * a ^ (n + 1)) / lam -
        (((n + 1 : Nat) : Real) / lam) * expMulPowIntegral lam a b n

def expMulPowIntegralRightCoeff (lam a b : Real) : Nat -> Real
  | 0 => 1 / lam
  | n + 1 =>
      b ^ (n + 1) / lam -
        (((n + 1 : Nat) : Real) / lam) *
          expMulPowIntegralRightCoeff lam a b n

def expMulPowIntegralLeftCoeff (lam a b : Real) : Nat -> Real
  | 0 => -(1 / lam)
  | n + 1 =>
      -(a ^ (n + 1) / lam) -
        (((n + 1 : Nat) : Real) / lam) *
          expMulPowIntegralLeftCoeff lam a b n

lemma expMulPowIntegral_eq_exp_linear
    (lam a b : Real) :
    ∀ n : Nat,
      expMulPowIntegral lam a b n =
        expMulPowIntegralRightCoeff lam a b n * Real.exp (lam * b) +
          expMulPowIntegralLeftCoeff lam a b n * Real.exp (lam * a) := by
  intro n
  induction n with
  | zero =>
      simp [expMulPowIntegral, expMulPowIntegralRightCoeff,
        expMulPowIntegralLeftCoeff]
      ring
  | succ n ih =>
      rw [expMulPowIntegral, expMulPowIntegralRightCoeff,
        expMulPowIntegralLeftCoeff, ih]
      ring

lemma intervalIntegral_exp_mul_pow_eq_rec
    (lam a b : Real) (hlam : lam ≠ 0) :
    ∀ n : Nat,
      ∫ x in a..b, Real.exp (lam * x) * x ^ n =
        expMulPowIntegral lam a b n := by
  intro n
  induction n with
  | zero =>
      simp [expMulPowIntegral, intervalIntegral_exp_mul_eq lam a b hlam]
  | succ n ih =>
      rw [expMulPowIntegral]
      rw [intervalIntegral_exp_mul_pow_succ_eq lam a b hlam n]
      rw [ih]

def expPoly (coeff : Nat -> Real) (degree : Nat) (x : Real) : Real :=
  (Finset.range degree).sum (fun n => coeff n * x ^ n)

def expPolyIntegral (coeff : Nat -> Real) (degree : Nat)
    (lam a b : Real) : Real :=
  (Finset.range degree).sum (fun n =>
    coeff n * expMulPowIntegral lam a b n)

def expPolyIntegralRightCoeff (coeff : Nat -> Real) (degree : Nat)
    (lam a b : Real) : Real :=
  (Finset.range degree).sum (fun n =>
    coeff n * expMulPowIntegralRightCoeff lam a b n)

def expPolyIntegralLeftCoeff (coeff : Nat -> Real) (degree : Nat)
    (lam a b : Real) : Real :=
  (Finset.range degree).sum (fun n =>
    coeff n * expMulPowIntegralLeftCoeff lam a b n)

lemma expPolyIntegral_eq_exp_linear
    (coeff : Nat -> Real) (degree : Nat) (lam a b : Real) :
    expPolyIntegral coeff degree lam a b =
      expPolyIntegralRightCoeff coeff degree lam a b * Real.exp (lam * b) +
        expPolyIntegralLeftCoeff coeff degree lam a b * Real.exp (lam * a) := by
  unfold expPolyIntegral expPolyIntegralRightCoeff expPolyIntegralLeftCoeff
  simp_rw [expMulPowIntegral_eq_exp_linear]
  calc
    (Finset.range degree).sum (fun n =>
        coeff n *
          (expMulPowIntegralRightCoeff lam a b n * Real.exp (lam * b) +
            expMulPowIntegralLeftCoeff lam a b n * Real.exp (lam * a))) =
        (Finset.range degree).sum (fun n =>
          coeff n * expMulPowIntegralRightCoeff lam a b n * Real.exp (lam * b) +
            coeff n * expMulPowIntegralLeftCoeff lam a b n * Real.exp (lam * a)) := by
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = (Finset.range degree).sum (fun n =>
          coeff n * expMulPowIntegralRightCoeff lam a b n) * Real.exp (lam * b) +
        (Finset.range degree).sum (fun n =>
          coeff n * expMulPowIntegralLeftCoeff lam a b n) * Real.exp (lam * a) := by
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_mul, Finset.sum_mul]

lemma intervalIntegral_exp_mul_poly_eq_sum
    (coeff : Nat -> Real) (degree : Nat) (lam a b : Real)
    (hlam : lam ≠ 0) :
    ∫ x in a..b, Real.exp (lam * x) * expPoly coeff degree x =
      expPolyIntegral coeff degree lam a b := by
  unfold expPoly expPolyIntegral
  calc
    ∫ x in a..b,
        Real.exp (lam * x) *
          ((Finset.range degree).sum (fun n => coeff n * x ^ n))
        = ∫ x in a..b,
            (Finset.range degree).sum (fun n =>
              coeff n * (Real.exp (lam * x) * x ^ n)) := by
          apply intervalIntegral.integral_congr
          intro x _hx
          simp_rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro n _hn
          ring
    _ = (Finset.range degree).sum (fun n =>
          ∫ x in a..b, coeff n * (Real.exp (lam * x) * x ^ n)) := by
          rw [intervalIntegral.integral_finset_sum]
          intro n _hn
          exact (by
            fun_prop :
              Continuous (fun x : Real =>
                coeff n * (Real.exp (lam * x) * x ^ n))
          ).intervalIntegrable a b
    _ = (Finset.range degree).sum (fun n =>
          coeff n * expMulPowIntegral lam a b n) := by
          apply Finset.sum_congr rfl
          intro n _hn
          rw [intervalIntegral.integral_const_mul]
          rw [intervalIntegral_exp_mul_pow_eq_rec lam a b hlam n]

end PSDpd
end Q3
