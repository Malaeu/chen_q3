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

/-- Rational absolute majorant term for the `m`-th live term in the `k`-th
`realSinc` derivative bound on `0 <= u <= 1 / 400`.

For `n = ceil(k / 2) + m` and `e = 2*n - k`, the intended analytic term is
`(1/400)^e / ((2*n+1) * e!)`.  The derivative crosswalk proving this really
majorizes `‖iteratedDeriv k realSinc u‖` is deliberately not asserted here. -/
def step33Sub0RealSincDerivMajorantTerm (k m : Nat) : Rat :=
  let n : Nat := step33Sub0RealSincDerivMajorantStart k + m
  let e : Nat := 2 * n - k
  (((1 : Rat) / 400) ^ e) /
    (((2 * n + 1 : Nat) : Rat) * ((Nat.factorial e : Nat) : Rat))

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
