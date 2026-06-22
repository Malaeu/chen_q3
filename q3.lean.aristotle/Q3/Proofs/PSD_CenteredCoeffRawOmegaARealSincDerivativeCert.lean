import Q3.Proofs.PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver

set_option linter.mathlibStandardSet false
set_option autoImplicit false
set_option maxHeartbeats 0

/-!
Proof contract for the Step33A.1-A sub0 `realSinc` derivative majorant.

This file is intentionally payload-small.  It records the exact rational
majorant shape selected for the next certificate generator, and it does not
claim the missing analytic bridge from the even power series to
`iteratedDeriv k realSinc u` on `0 <= u <= 1 / 400`.

Current first missing bridge:
`STEP33_A1_SUB0_REALSINC_ITERATEDDERIV_SERIES_MAJORANT_CROSSWALK_GAP`.
-/

noncomputable section

namespace Q3
namespace PSDpd
namespace Step33

open CenteredCoeffPrimeDeltaLiveRationalPayloadImport.RawOmegaAChunkIntegral.RawOmegaATaylorModelCertificate
open scoped BigOperators

/-- Starting series index for the absolute majorant of the `k`-th derivative
of `realSinc`.  This is `ceil(k / 2)`, written in integer form. -/
def step33Sub0RealSincDerivMajorantStart (k : Nat) : Nat :=
  (k + 1) / 2

/-- Actual power-series index used by the `m`-th live term of row `k`. -/
def step33Sub0RealSincDerivMajorantIndex (k m : Nat) : Nat :=
  step33Sub0RealSincDerivMajorantStart k + m

/-- Derivative exponent `2*n-k` for the `m`-th live term of row `k`. -/
def step33Sub0RealSincDerivMajorantExponent (k m : Nat) : Nat :=
  2 * step33Sub0RealSincDerivMajorantIndex k m - k

/-- Positive integer denominator `(2*n+1) * (2*n-k)!` for the live term. -/
def step33Sub0RealSincDerivMajorantDenominator (k m : Nat) : Nat :=
  (2 * step33Sub0RealSincDerivMajorantIndex k m + 1) *
    (step33Sub0RealSincDerivMajorantExponent k m).factorial

/-- Rational absolute majorant term for the `m`-th live term in the `k`-th
`realSinc` derivative bound on `0 <= u <= 1 / 400`.

For `n = ceil(k / 2) + m` and `e = 2*n - k`, the intended analytic term is
`(1/400)^e / ((2*n+1) * e!)`.  The derivative crosswalk proving this really
majorizes `‖iteratedDeriv k realSinc u‖` is deliberately not asserted here. -/
def step33Sub0RealSincDerivMajorantTerm (k m : Nat) : Rat :=
  (((1 : Rat) / 400) ^ step33Sub0RealSincDerivMajorantExponent k m) /
    (step33Sub0RealSincDerivMajorantDenominator k m : Rat)

/-- Direct real-valued view of `step33Sub0RealSincDerivMajorantTerm`. -/
def step33Sub0RealSincDerivMajorantTermReal (k m : Nat) : Real :=
  (((1 : Real) / 400) ^ step33Sub0RealSincDerivMajorantExponent k m) /
    (step33Sub0RealSincDerivMajorantDenominator k m : Real)

/-- The rational term and its direct real formula agree after coercion. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_eq (k m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k m : Real) =
      step33Sub0RealSincDerivMajorantTermReal k m := by
  unfold step33Sub0RealSincDerivMajorantTerm
    step33Sub0RealSincDerivMajorantTermReal
  norm_num

/-- The chosen start index is large enough for the `k`-th derivative row. -/
theorem step33Sub0RealSincDerivMajorantStart_spec (k : Nat) :
    k <= 2 * step33Sub0RealSincDerivMajorantStart k := by
  unfold step33Sub0RealSincDerivMajorantStart
  omega

/-- Consecutive live terms increase the derivative exponent by exactly two. -/
theorem step33Sub0RealSincDerivMajorantExponent_succ (k m : Nat) :
    step33Sub0RealSincDerivMajorantExponent k (m + 1) =
      step33Sub0RealSincDerivMajorantExponent k m + 2 := by
  unfold step33Sub0RealSincDerivMajorantExponent
    step33Sub0RealSincDerivMajorantIndex
  have h0 : k <= 2 * (step33Sub0RealSincDerivMajorantStart k + m) := by
    have hs := step33Sub0RealSincDerivMajorantStart_spec k
    omega
  rw [show 2 * (step33Sub0RealSincDerivMajorantStart k + (m + 1)) =
      2 * (step33Sub0RealSincDerivMajorantStart k + m) + 2 by omega]
  rw [Nat.sub_add_comm h0]

/-- The live-term denominator is strictly positive. -/
theorem step33Sub0RealSincDerivMajorantDenominator_pos (k m : Nat) :
    0 < step33Sub0RealSincDerivMajorantDenominator k m := by
  unfold step33Sub0RealSincDerivMajorantDenominator
  exact Nat.mul_pos (by omega) (Nat.factorial_pos _)

/-- The live-term denominator is monotone along the tail. -/
theorem step33Sub0RealSincDerivMajorantDenominator_le_succ (k m : Nat) :
    step33Sub0RealSincDerivMajorantDenominator k m <=
      step33Sub0RealSincDerivMajorantDenominator k (m + 1) := by
  unfold step33Sub0RealSincDerivMajorantDenominator
    step33Sub0RealSincDerivMajorantIndex
  apply Nat.mul_le_mul
  · omega
  · rw [step33Sub0RealSincDerivMajorantExponent_succ]
    exact Nat.factorial_le (by omega)

/-- Consecutive real majorant terms shrink by at least the geometric ratio
`(1/400)^2`. -/
theorem step33Sub0RealSincDerivMajorantTermReal_succ_le_ratio (k m : Nat) :
    step33Sub0RealSincDerivMajorantTermReal k (m + 1) <=
      (((1 : Real) / 400) ^ 2) *
        step33Sub0RealSincDerivMajorantTermReal k m := by
  unfold step33Sub0RealSincDerivMajorantTermReal
  rw [step33Sub0RealSincDerivMajorantExponent_succ]
  rw [pow_add]
  have hnum :
      0 <= (((1 : Real) / 400) ^
          step33Sub0RealSincDerivMajorantExponent k m) *
        (((1 : Real) / 400) ^ 2) := by
    positivity
  have hdenpos :
      0 < (step33Sub0RealSincDerivMajorantDenominator k m : Real) := by
    exact_mod_cast step33Sub0RealSincDerivMajorantDenominator_pos k m
  have hdenle :
      (step33Sub0RealSincDerivMajorantDenominator k m : Real) <=
        (step33Sub0RealSincDerivMajorantDenominator k (m + 1) : Real) := by
    exact_mod_cast step33Sub0RealSincDerivMajorantDenominator_le_succ k m
  have hdiv := div_le_div_of_nonneg_left hnum hdenpos hdenle
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Consecutive rational majorant terms shrink by at least the geometric ratio
`(1/400)^2` after coercion to `Real`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_succ_le_ratio (k m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k (m + 1) : Real) <=
      (((1 : Real) / 400) ^ 2) *
        (step33Sub0RealSincDerivMajorantTerm k m : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_real_eq,
    step33Sub0RealSincDerivMajorantTerm_real_eq]
  exact step33Sub0RealSincDerivMajorantTermReal_succ_le_ratio k m

/-- The rational majorant terms are nonnegative. -/
theorem step33Sub0RealSincDerivMajorantTerm_nonneg (k m : Nat) :
    0 <= step33Sub0RealSincDerivMajorantTerm k m := by
  unfold step33Sub0RealSincDerivMajorantTerm
  positivity

/-- Real-cast form of `step33Sub0RealSincDerivMajorantTerm_nonneg`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_nonneg (k m : Nat) :
    0 <= (step33Sub0RealSincDerivMajorantTerm k m : Real) := by
  exact_mod_cast step33Sub0RealSincDerivMajorantTerm_nonneg k m

/-- Finite rational certificate surface for the `realSinc` derivative rows
`k = 0, ..., 17`.

`baseAbs` is the proof-grade row bound intended for
`‖iteratedDeriv k realSinc u‖` on `Set.Icc 0 (1/400)`.  The `Valid` predicate
checks only the rational arithmetic budget: finite prefix plus a geometric
tail allowance. -/
structure Step33Sub0RealSincDerivativeMajorantCert where
  prefixN : Fin 18 -> Nat
  tailAbs : Fin 18 -> Rat
  baseAbs : Fin 18 -> Rat

namespace Step33Sub0RealSincDerivativeMajorantCert

/-- Rational checker obligations for a candidate `realSinc` derivative
majorant certificate.

The geometric ratio `((1/400)^2)` is the intended uniform ratio for consecutive
live terms in the positive absolute series.  The proof that the actual analytic
terms are covered by this rational checker is the current crosswalk gap. -/
structure Valid (data : Step33Sub0RealSincDerivativeMajorantCert) : Prop where
  tailBudget :
    ∀ k : Fin 18,
      step33Sub0RealSincDerivMajorantTerm k.1 (data.prefixN k) /
          (1 - ((1 : Rat) / 400) ^ 2) <=
        data.tailAbs k
  totalBudget :
    ∀ k : Fin 18,
      (∑ m ∈ Finset.range (data.prefixN k),
          step33Sub0RealSincDerivMajorantTerm k.1 m) +
          data.tailAbs k <=
        data.baseAbs k

/-- Explicit marker for the live obstruction.  A proof of this proposition,
together with `Valid`, would feed the existing scaled-sinc receiver in
`PSD_CenteredCoeffRawOmegaAShapeDerivativeMajorantReceiver.lean`. -/
def ProvidesAnalyticMajorant
    (data : Step33Sub0RealSincDerivativeMajorantCert) : Prop :=
  ∀ u ∈ Set.Icc (0 : Real) ((1 : Real) / 400),
    ∀ k : Fin 18,
      ‖iteratedDeriv k.1 realSinc u‖ <= (data.baseAbs k : Real)

end Step33Sub0RealSincDerivativeMajorantCert

end Step33
end PSDpd
end Q3
