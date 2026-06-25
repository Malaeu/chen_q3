import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Small computable rational algebra for the Step33 `powDerivMajorant` table.

This file is intentionally independent of the heavy Q3 analytic imports.  It
proves the binomial closed form for the rational mirror of the recursive
Leibniz majorant; Step33 payload files can then cast the result into `Real`.
-/

namespace Q3
namespace PSDpd
namespace Step33

open scoped BigOperators

def powDerivMajorantRat : Nat -> Nat -> (Nat -> Rat) -> Rat
  | 0, n, M => M n
  | p + 1, n, M =>
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : Rat) * powDerivMajorantRat p i M * M (n - i)

theorem powDerivMajorantRat_const_mul_pow
    (c a : Rat) (p n : Nat) :
    powDerivMajorantRat p n (fun k : Nat => c * a ^ k) =
      c ^ (p + 1) * (((p + 1 : Nat) : Rat) ^ n) * a ^ n := by
  induction p generalizing n with
  | zero =>
      simp [powDerivMajorantRat]
  | succ p ih =>
      simp only [powDerivMajorantRat]
      calc
        (∑ i ∈ Finset.range (n + 1),
            (n.choose i : Rat) *
              powDerivMajorantRat p i (fun k : Nat => c * a ^ k) *
              ((fun k : Nat => c * a ^ k) (n - i))) =
          ∑ i ∈ Finset.range (n + 1),
            c ^ (p + 2) * (((p + 1 : Nat) : Rat) ^ i) *
              a ^ n * (n.choose i : Rat) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_le : i <= n :=
              Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
            have hpow : a ^ i * a ^ (n - i) = a ^ n := by
              rw [← pow_add, Nat.add_sub_of_le hi_le]
            rw [ih i]
            calc
              (n.choose i : Rat) *
                    (c ^ (p + 1) * (((p + 1 : Nat) : Rat) ^ i) *
                      a ^ i) *
                    (c * a ^ (n - i)) =
                c ^ (p + 2) * (((p + 1 : Nat) : Rat) ^ i) *
                    (a ^ i * a ^ (n - i)) * (n.choose i : Rat) := by
                  ring
              _ =
                c ^ (p + 2) * (((p + 1 : Nat) : Rat) ^ i) *
                    a ^ n * (n.choose i : Rat) := by
                  rw [hpow]
        _ = c ^ (p + 2) * a ^ n *
              (((p + 1 : Nat) : Rat) + 1) ^ n := by
            rw [add_pow]
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
        _ = c ^ ((p + 1) + 1) *
              ((((p + 1) + 1 : Nat) : Rat) ^ n) * a ^ n := by
            norm_num
            ring

theorem powDerivMajorantRat_sharpScaledSinc_11
    (n : Nat) :
    powDerivMajorantRat 11 n (fun k : Nat => (2 : Rat) * ((1 : Rat) / 40) ^ k) =
      (2 : Rat) ^ (12 : Nat) * ((3 : Rat) / 10) ^ n := by
  rw [powDerivMajorantRat_const_mul_pow]
  norm_num
  rw [mul_assoc]
  rw [← mul_pow]
  norm_num

theorem powDerivMajorantRat_sharpShapeSq_1
    (n : Nat) :
    powDerivMajorantRat 1 n
        (fun k : Nat => (2 : Rat) ^ (12 : Nat) * ((3 : Rat) / 10) ^ k) =
      (2 : Rat) ^ (24 : Nat) * ((3 : Rat) / 5) ^ n := by
  rw [powDerivMajorantRat_const_mul_pow]
  norm_num
  rw [mul_assoc]
  rw [← mul_pow]
  norm_num

end Step33
end PSDpd
end Q3
