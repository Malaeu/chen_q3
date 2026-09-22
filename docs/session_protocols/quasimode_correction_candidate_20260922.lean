import Mathlib
open Polynomial
noncomputable section
namespace Q3QuasimodeCorrection
abbrev P0 : ℝ[X] := 1
abbrev P4 : ℝ[X] := 3 - 24*X^2 + 16*X^4
abbrev Q0 : ℝ[X] := C (3/8 : ℝ)*X^2 - C (1/4 : ℝ)*X^4
abbrev Q4 : ℝ[X] := C (129/8 : ℝ)*X^2 - C (183/4 : ℝ)*X^4 + 28*X^6 - 4*X^8
def A (n : ℕ) (p : ℝ[X]) := -p.derivative.derivative + 4*X*p.derivative - C (4*(n:ℝ))*p
def T (p : ℝ[X]) := X^2*p.derivative.derivative + (2*X-4*X^3)*p.derivative + (4*X^4-6*X^2)*p
abbrev R0 : ℝ[X] := C (81/32 : ℝ)*X^2 - C (167/16 : ℝ)*X^4 + 7*X^6-X^8
abbrev R4 : ℝ[X] := C (8643/32 : ℝ)*X^2 - C (26121/16 : ℝ)*X^4 + 2548*X^6-1354*X^8+264*X^10-16*X^12

theorem correction_zero : A 0 Q0 + T P0 + C (3/4 : ℝ)*P0 = 0 := by
  apply Polynomial.funext
  intro x
  norm_num [A,T,Q0,P0,derivative_mul,derivative_pow]
  <;> ring

theorem correction_four : A 4 Q4 + T P4 + C (43/4 : ℝ)*P4 = 0 := by
  apply Polynomial.funext
  intro x
  norm_num [A,T,Q4,P4,derivative_mul,derivative_pow]
  <;> ring

theorem residual_zero : T Q0 + C (3/4 : ℝ)*Q0 = R0 := by
  apply Polynomial.funext
  intro x
  norm_num [T,Q0,R0,derivative_mul,derivative_pow]
  <;> ring

theorem residual_four : T Q4 + C (43/4 : ℝ)*Q4 = R4 := by
  apply Polynomial.funext
  intro x
  norm_num [T,Q4,R4,derivative_mul,derivative_pow]
  <;> ring

theorem center_corrections : Q0.eval 0 = 0 ∧ Q4.eval 0 = 0 := by
  norm_num [Q0,Q4]
#print axioms correction_zero
#print axioms correction_four
#print axioms residual_zero
#print axioms residual_four
#print axioms center_corrections
end Q3QuasimodeCorrection
