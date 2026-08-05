import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreAffineKernel
import Mathlib.Data.Nat.Choose.Basic

/-!
# Three-term recurrence for the mode-four ordinary Legendre kernel

This file proves only the polynomial three-term recurrence for the ordinary
Legendre convention fixed by `D0Mode4OrdinaryLegendreAffineKernel`.  The proof
starts from Mathlib's explicit shifted-Legendre coefficients, establishes the
finite binomial identity coefficientwise over `ℤ[X]`, and transports it through
the already committed affine map.

It does not prove an `X`-action, an `X ^ 2`-action, a differential equation,
analytic bounds, a Ferrers series, or any PSWF provenance statement.
-/

open Polynomial

noncomputable section

private theorem choose_recurrence_coefficient (n k : ℕ) :
    (n + 2) * (n + 2).choose (k + 1) * (n + k + 3).choose (n + 2) +
        (n + 1) * n.choose (k + 1) * (n + k + 1).choose n =
      (2 * n + 3) * (n + 1).choose (k + 1) * (n + k + 2).choose (n + 1) +
        2 * (2 * n + 3) * (n + 1).choose k * (n + k + 1).choose (n + 1) := by
  by_cases hkn : k ≤ n + 1
  · have hA1 :
        (k + 1) * (n + 2).choose (k + 1) =
          (n + 2) * (n + 1).choose k := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using
        (Nat.add_one_mul_choose_eq (n + 1) k).symm
    have hA21 :
        (n + k + 2) * (n + k + 1).choose (n + 1) =
          (n + k + 2).choose (n + 1) * (k + 1) := by
      have hsub : n + k + 2 - (n + 1) = k + 1 := by omega
      have hraw := Nat.choose_mul_succ_eq (n + k + 1) (n + 1)
      rw [hsub] at hraw
      calc
        _ = (n + k + 1).choose (n + 1) * (n + k + 2) := by ring
        _ = _ := by convert hraw using 1
    have hA22 :
        (n + k + 3) * (n + k + 2).choose (n + 1) =
          (n + k + 3).choose (n + 2) * (n + 2) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Nat.add_one_mul_choose_eq (n + k + 2) (n + 1)
    have hA2 :
        (k + 1) * (n + 2) * (n + k + 3).choose (n + 2) =
          (n + k + 3) * (n + k + 2) *
            (n + k + 1).choose (n + 1) := by
      calc
        _ = (k + 1) * ((n + k + 3).choose (n + 2) * (n + 2)) := by ring
        _ = (k + 1) * ((n + k + 3) * (n + k + 2).choose (n + 1)) := by rw [hA22]
        _ = (n + k + 3) * ((n + k + 2).choose (n + 1) * (k + 1)) := by ring
        _ = _ := by rw [← hA21]; ring
    have hB1 :
        (k + 1) * (n + 1).choose (k + 1) =
          (n + 1 - k) * (n + 1).choose k := by
      simpa [mul_comm] using Nat.choose_succ_right_eq (n + 1) k
    have hB2 :
        (k + 1) * (n + k + 2).choose (n + 1) =
          (n + k + 2) * (n + k + 1).choose (n + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using hA21.symm
    have hD1 :
        (k + 1) * n.choose (k + 1) = (n - k) * n.choose k := by
      simpa [mul_comm] using Nat.choose_succ_right_eq n k
    have hD2 :
        (k + 1) * (n + k + 1).choose n =
          (n + 1) * (n + k + 1).choose (n + 1) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, mul_comm] using
        (Nat.choose_succ_right_eq (n + k + 1) n).symm
    have hD3 :
        (n + 1) * n.choose k = (n + 1 - k) * (n + 1).choose k := by
      simpa [mul_comm] using Nat.choose_mul_succ_eq n k
    have hA :
        (k + 1) ^ 2 *
            ((n + 2) * (n + 2).choose (k + 1) * (n + k + 3).choose (n + 2)) =
          (n + 2) * (n + k + 3) * (n + k + 2) *
            ((n + 1).choose k * (n + k + 1).choose (n + 1)) := by
      calc
        _ = ((k + 1) * (n + 2).choose (k + 1)) *
            ((k + 1) * (n + 2) * (n + k + 3).choose (n + 2)) := by ring
        _ = _ := by rw [hA1, hA2]; ring
    have hB :
        (k + 1) ^ 2 *
            ((2 * n + 3) * (n + 1).choose (k + 1) *
              (n + k + 2).choose (n + 1)) =
          (2 * n + 3) * (n + 1 - k) * (n + k + 2) *
            ((n + 1).choose k * (n + k + 1).choose (n + 1)) := by
      calc
        _ = (2 * n + 3) * ((k + 1) * (n + 1).choose (k + 1)) *
            ((k + 1) * (n + k + 2).choose (n + 1)) := by ring
        _ = _ := by rw [hB1, hB2]; ring
    have hC :
        (k + 1) ^ 2 *
            (2 * (2 * n + 3) * (n + 1).choose k *
              (n + k + 1).choose (n + 1)) =
          (2 * (2 * n + 3) * (k + 1) ^ 2) *
            ((n + 1).choose k * (n + k + 1).choose (n + 1)) := by ring
    have hD :
        (k + 1) ^ 2 *
            ((n + 1) * n.choose (k + 1) * (n + k + 1).choose n) =
          (n + 1) * (n + 1 - k) * (n - k) *
            ((n + 1).choose k * (n + k + 1).choose (n + 1)) := by
      calc
        _ = (n + 1) * ((k + 1) * n.choose (k + 1)) *
            ((k + 1) * (n + k + 1).choose n) := by ring
        _ = (n + 1) * ((n - k) * n.choose k) *
            ((n + 1) * (n + k + 1).choose (n + 1)) := by rw [hD1, hD2]
        _ = (n - k) * ((n + 1) * n.choose k) *
            ((n + 1) * (n + k + 1).choose (n + 1)) := by ring
        _ = _ := by rw [hD3]; ring
    have hscalar :
        (n + 2) * (n + k + 3) * (n + k + 2) +
            (n + 1) * (n + 1 - k) * (n - k) =
          (2 * n + 3) * (n + 1 - k) * (n + k + 2) +
            2 * (2 * n + 3) * (k + 1) ^ 2 := by
      by_cases hk0 : k ≤ n
      · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk0
        have hs0 : k + d - k = d := by omega
        have hs1 : k + d + 1 - k = d + 1 := by omega
        rw [hs0, hs1]
        ring
      · have hk_eq : k = n + 1 := by omega
        subst k
        simp
        ring
    apply mul_left_cancel₀ (a := (k + 1) ^ 2)
    · positivity
    rw [mul_add, mul_add, hA, hD, hB, hC]
    calc
      _ = ((n + 2) * (n + k + 3) * (n + k + 2) +
            (n + 1) * (n + 1 - k) * (n - k)) *
          ((n + 1).choose k * (n + k + 1).choose (n + 1)) := by ring
      _ = _ := by rw [hscalar]; ring
  · have hnk : n + 1 < k := Nat.lt_of_not_ge hkn
    simp [Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt (by omega : n < k + 1),
      Nat.choose_eq_zero_of_lt (by omega : n + 1 < k + 1),
      Nat.choose_eq_zero_of_lt (by omega : n + 2 < k + 1)]

private theorem shiftedLegendre_three_term_succ (n : ℕ) :
    C ((n + 2 : ℕ) : ℤ) * shiftedLegendre (n + 2) =
      C ((2 * n + 3 : ℕ) : ℤ) * (1 - 2 * X) * shiftedLegendre (n + 1) -
        C ((n + 1 : ℕ) : ℤ) * shiftedLegendre n := by
  rw [show C ((2 * n + 3 : ℕ) : ℤ) * (1 - 2 * X) * shiftedLegendre (n + 1) =
      C ((2 * n + 3 : ℕ) : ℤ) * shiftedLegendre (n + 1) -
        C (2 * ((2 * n + 3 : ℕ) : ℤ)) * X * shiftedLegendre (n + 1) by
    norm_num
    ring]
  simp only [mul_assoc]
  ext k
  cases k with
  | zero =>
      simp [coeff_shiftedLegendre]
      ring
  | succ k =>
      simp only [coeff_sub, coeff_C_mul, coeff_X_mul,
        coeff_shiftedLegendre]
      simp only [pow_succ]
      ring_nf
      have hs : ((-1 : ℤ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
      apply (mul_right_inj' hs).mp
      ring_nf
      have hs2 : (-1 : ℤ) ^ (k * 2) = 1 := by
        rw [Nat.mul_comm, pow_mul]
        norm_num
      rw [hs2]
      ring_nf
      have hcoeffNatAligned :
          (2 + n) * (2 + n).choose (1 + k) *
                (3 + n + k).choose (2 + n) +
              (1 + n) * n.choose (1 + k) *
                (1 + n + k).choose n =
            (3 + n * 2) * (1 + n).choose (1 + k) *
                (2 + n + k).choose (1 + n) +
              2 * (3 + n * 2) * (1 + n).choose k *
                (1 + n + k).choose (1 + n) := by
        simpa only [
          show n + 2 = 2 + n by omega,
          show k + 1 = 1 + k by omega,
          show n + k + 3 = 3 + n + k by omega,
          show n + 1 = 1 + n by omega,
          show n + k + 1 = 1 + n + k by omega,
          show 2 * n + 3 = 3 + n * 2 by omega,
          show n + k + 2 = 2 + n + k by omega] using
            choose_recurrence_coefficient n k
      have hcoeffAligned :
          ((2 + n : ℕ) : ℤ) * (2 + n).choose (1 + k) *
                (3 + n + k).choose (2 + n) +
              ((1 + n : ℕ) : ℤ) * n.choose (1 + k) *
                (1 + n + k).choose n =
            ((3 + n * 2 : ℕ) : ℤ) * (1 + n).choose (1 + k) *
                (2 + n + k).choose (1 + n) +
              2 * ((3 + n * 2 : ℕ) : ℤ) * (1 + n).choose k *
                (1 + n + k).choose (1 + n) := by
        exact_mod_cast hcoeffNatAligned
      let A : ℤ :=
        ((2 + n : ℕ) : ℤ) * (2 + n).choose (1 + k) *
          (3 + n + k).choose (2 + n)
      let B : ℤ :=
        ((3 + n * 2 : ℕ) : ℤ) * (1 + n).choose (1 + k) *
          (2 + n + k).choose (1 + n)
      let Cc : ℤ :=
        ((3 + n * 2 : ℕ) : ℤ) * (1 + n).choose k *
          (1 + n + k).choose (1 + n) * 2
      let D : ℤ :=
        ((1 + n : ℕ) : ℤ) * n.choose (1 + k) *
          (1 + n + k).choose n
      have hABCD : A + D = B + Cc := by
        dsimp only [A, B, Cc, D]
        rw [hcoeffAligned]
        ring
      change -A = -B - Cc + D
      calc
        -A = -(A + D) + D := by ring
        _ = -(B + Cc) + D := by rw [hABCD]
        _ = -B - Cc + D := by ring

private theorem mode4Affine_shifted_coordinate :
    ((map (Int.castRingHom ℝ) (1 : ℤ[X])).comp mode4OrdinaryLegendreAffine -
      (map (Int.castRingHom ℝ) (2 : ℤ[X])).comp mode4OrdinaryLegendreAffine *
        mode4OrdinaryLegendreAffine) = X := by
  have hone := mode4OrdinaryLegendrePolynomial_one
  rw [mode4OrdinaryLegendrePolynomial] at hone
  have hpoly : Polynomial.shiftedLegendre 1 = 1 - 2 * X := by
    norm_num [Polynomial.shiftedLegendre, Finset.sum_range_succ,
      sub_eq_add_neg]
  rw [hpoly] at hone
  simpa only [Polynomial.map_sub, Polynomial.map_one,
    Polynomial.map_mul, Polynomial.map_ofNat, Polynomial.map_X,
    Polynomial.sub_comp, Polynomial.one_comp, Polynomial.mul_comp,
    Polynomial.ofNat_comp, Polynomial.X_comp] using hone

/-- The exact ordinary-Legendre three-term recurrence in the convention
`P₀ = 1`, `P₁ = X`. -/
theorem mode4OrdinaryLegendrePolynomial_three_term_succ
    (n : ℕ) :
    C ((n + 2 : ℕ) : ℝ) *
        mode4OrdinaryLegendrePolynomial (n + 2) =
      C ((2 * n + 3 : ℕ) : ℝ) * X *
          mode4OrdinaryLegendrePolynomial (n + 1) -
        C ((n + 1 : ℕ) : ℝ) *
          mode4OrdinaryLegendrePolynomial n := by
  have h := congrArg
    (fun p : ℤ[X] =>
      (p.map (Int.castRingHom ℝ)).comp mode4OrdinaryLegendreAffine)
    (shiftedLegendre_three_term_succ n)
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
    Polynomial.map_X, Polynomial.mul_comp, Polynomial.sub_comp,
    Polynomial.C_comp, Polynomial.X_comp] at h
  rw [mode4Affine_shifted_coordinate] at h
  simpa [mode4OrdinaryLegendrePolynomial] using h

/-! ## Planted recurrence and transport mutants

Each false equation is rejected independently by the already proved endpoint
values or by direct evaluation of the affine coordinate.  None of these guards
uses the public recurrence theorem above.
-/

-- M-F0B-1: replace the leading coefficient `2` by `1` at `n = 0`.
private theorem mutant_wrong_leading_coefficient_rejected :
    C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 2 ≠
      C (3 : ℝ) * X * mode4OrdinaryLegendrePolynomial 1 -
        C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_sub] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change mode4OrdinaryLegendre 2 1 = 2 at heval
  norm_num at heval

-- M-F0B-2: replace the middle coefficient `3` by `1` at `n = 0`.
private theorem mutant_wrong_middle_coefficient_rejected :
    C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 2 ≠
      C (1 : ℝ) * X * mode4OrdinaryLegendrePolynomial 1 -
        C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_sub] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change mode4OrdinaryLegendre 2 1 = 0 at heval
  norm_num at heval

-- M-F0B-3: flip the sign of the middle term at `n = 0`.
private theorem mutant_wrong_middle_sign_rejected :
    C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 2 ≠
      -C (3 : ℝ) * X * mode4OrdinaryLegendrePolynomial 1 -
        C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_sub, eval_neg] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change 2 * mode4OrdinaryLegendre 2 1 = -4 at heval
  norm_num at heval

-- M-F0B-4: replace the trailing coefficient `1` by `2` at `n = 0`.
private theorem mutant_wrong_trailing_coefficient_rejected :
    C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 2 ≠
      C (3 : ℝ) * X * mode4OrdinaryLegendrePolynomial 1 -
        C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 0 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  simp only [eval_mul, eval_C, eval_X, eval_sub] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at heval
  change 2 * mode4OrdinaryLegendre 2 1 = 1 at heval
  norm_num at heval

-- M-F0B-5: replace the trailing `P₀` by `P₁` at `n = 0`.
private theorem mutant_wrong_trailing_index_rejected :
    C (2 : ℝ) * mode4OrdinaryLegendrePolynomial 2 ≠
      C (3 : ℝ) * X * mode4OrdinaryLegendrePolynomial 1 -
        C (1 : ℝ) * mode4OrdinaryLegendrePolynomial 1 := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval (-1)) h
  simp only [eval_mul, eval_C, eval_X, eval_sub] at heval
  norm_num [mode4OrdinaryLegendrePolynomial_one] at heval
  change 2 * mode4OrdinaryLegendre 2 (-1) = 4 at heval
  norm_num at heval

-- M-F0B-6: reverse the affine shifted-coordinate orientation `X → -X`.
private theorem mutant_reversed_shifted_coordinate_rejected :
    ((map (Int.castRingHom ℝ) (1 : ℤ[X])).comp mode4OrdinaryLegendreAffine -
      (map (Int.castRingHom ℝ) (2 : ℤ[X])).comp mode4OrdinaryLegendreAffine *
        mode4OrdinaryLegendreAffine) ≠ -X := by
  intro h
  have heval := congrArg (fun p : ℝ[X] => p.eval 1) h
  norm_num [mode4OrdinaryLegendreAffine] at heval

#print axioms mode4OrdinaryLegendrePolynomial_three_term_succ
