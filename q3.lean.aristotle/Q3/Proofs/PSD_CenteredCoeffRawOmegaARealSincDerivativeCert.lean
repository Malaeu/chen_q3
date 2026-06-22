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

/-- A shifted live-term tail is bounded termwise by the geometric envelope
with ratio `(1/400)^2`. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric
    (k N m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) <=
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hratio :
          (step33Sub0RealSincDerivMajorantTerm k (N + (m + 1)) : Real) <=
            (((1 : Real) / 400) ^ 2) *
              (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) := by
        simpa [Nat.add_assoc] using
          step33Sub0RealSincDerivMajorantTerm_real_succ_le_ratio k (N + m)
      have hstep :
          (((1 : Real) / 400) ^ 2) *
              (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) <=
            (((1 : Real) / 400) ^ 2) *
              ((step33Sub0RealSincDerivMajorantTerm k N : Real) *
                (((1 : Real) / 400) ^ 2) ^ m) := by
        exact mul_le_mul_of_nonneg_left ih (by positivity)
      calc
        (step33Sub0RealSincDerivMajorantTerm k (N + (m + 1)) : Real)
            <= (((1 : Real) / 400) ^ 2) *
                (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real) := hratio
        _ <= (((1 : Real) / 400) ^ 2) *
              ((step33Sub0RealSincDerivMajorantTerm k N : Real) *
                (((1 : Real) / 400) ^ 2) ^ m) := hstep
        _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) *
              (((1 : Real) / 400) ^ 2) ^ (m + 1) := by
          rw [pow_succ]
          ring

/-- Shifted live-term tails are summable. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_shift_summable
    (k N : Nat) :
    Summable (fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) := by
  refine Summable.of_nonneg_of_le
    (f := fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m)
    (g := fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real))
    ?hNonneg ?hLe ?hGeom
  · intro m
    exact step33Sub0RealSincDerivMajorantTerm_real_nonneg k (N + m)
  · intro m
    exact step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric k N m
  · exact Summable.mul_left (step33Sub0RealSincDerivMajorantTerm k N : Real)
      (summable_geometric_of_lt_one (by positivity) (by norm_num))

/-- Geometric `tsum` bound for the shifted majorant tail. -/
theorem step33Sub0RealSincDerivMajorantTerm_real_tsum_tail_le
    (k N : Nat) :
    (∑' m : Nat,
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) <=
      (step33Sub0RealSincDerivMajorantTerm k N : Real) /
        (1 - (((1 : Real) / 400) ^ 2)) := by
  have hShift :=
    step33Sub0RealSincDerivMajorantTerm_real_shift_summable k N
  have hGeom : Summable (fun m : Nat =>
      (step33Sub0RealSincDerivMajorantTerm k N : Real) *
        (((1 : Real) / 400) ^ 2) ^ m) := by
    exact Summable.mul_left (step33Sub0RealSincDerivMajorantTerm k N : Real)
      (summable_geometric_of_lt_one (by positivity) (by norm_num))
  have hsum :
      (∑' m : Nat,
        (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real)) <=
        ∑' m : Nat,
          (step33Sub0RealSincDerivMajorantTerm k N : Real) *
            (((1 : Real) / 400) ^ 2) ^ m := by
    exact Summable.tsum_le_tsum
      (step33Sub0RealSincDerivMajorantTerm_real_shift_le_geometric k N)
      hShift hGeom
  calc
    (∑' m : Nat,
      (step33Sub0RealSincDerivMajorantTerm k (N + m) : Real))
        <= ∑' m : Nat,
          (step33Sub0RealSincDerivMajorantTerm k N : Real) *
            (((1 : Real) / 400) ^ 2) ^ m := hsum
    _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) *
          (1 - (((1 : Real) / 400) ^ 2))⁻¹ := by
      rw [tsum_mul_left,
        tsum_geometric_of_lt_one (by positivity) (by norm_num)]
    _ = (step33Sub0RealSincDerivMajorantTerm k N : Real) /
          (1 - (((1 : Real) / 400) ^ 2)) := by
      simp [div_eq_mul_inv]

/-- Closed form of the row-`0` majorant term. -/
theorem step33Sub0RealSincDerivMajorantTerm_zero_eq (m : Nat) :
    (step33Sub0RealSincDerivMajorantTerm 0 m : Real) =
      (((1 : Real) / 400) ^ (2 * m)) /
        (Nat.factorial (2 * m + 1) : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_real_eq]
  unfold step33Sub0RealSincDerivMajorantTermReal
    step33Sub0RealSincDerivMajorantExponent
    step33Sub0RealSincDerivMajorantDenominator
    step33Sub0RealSincDerivMajorantIndex
    step33Sub0RealSincDerivMajorantStart
  norm_num
  rw [show step33Sub0RealSincDerivMajorantExponent 0 m = 2 * m by
    unfold step33Sub0RealSincDerivMajorantExponent
      step33Sub0RealSincDerivMajorantIndex
      step33Sub0RealSincDerivMajorantStart
    norm_num]
  rw [show (2 * m + 1).factorial = (2 * m + 1) * (2 * m).factorial by
    simpa [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using (Nat.factorial_succ (2 * m))]
  norm_num

/-- The absolute row-`0` sinc series term is bounded by the row-`0` majorant
on `0 <= u <= 1/400`. -/
theorem step33Sub0RealSinc_seriesTerm_norm_le_majorant_zero
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400))
    (m : Nat) :
    ‖((-1 : Real) ^ m * u ^ (2 * m) /
        (Nat.factorial (2 * m + 1) : Real))‖ <=
      (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  rw [step33Sub0RealSincDerivMajorantTerm_zero_eq]
  have hu_abs : |u| <= (1 : Real) / 400 := by
    rw [abs_of_nonneg hu.1]
    exact hu.2
  have hpow :
      |u| ^ (2 * m) <= ((1 : Real) / 400) ^ (2 * m) :=
    pow_le_pow_left₀ (abs_nonneg u) hu_abs (2 * m)
  have hden_nonneg :
      0 <= ((Nat.factorial (2 * m + 1) : Real))⁻¹ := by
    positivity
  calc
    ‖((-1 : Real) ^ m * u ^ (2 * m) /
        (Nat.factorial (2 * m + 1) : Real))‖
        = |u| ^ (2 * m) /
            (Nat.factorial (2 * m + 1) : Real) := by
          have hfact_pos :
              0 < (Nat.factorial (2 * m + 1) : Real) := by
            positivity
          rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow]
          simp [abs_of_pos hfact_pos, div_eq_mul_inv]
    _ <= ((1 : Real) / 400) ^ (2 * m) /
          (Nat.factorial (2 * m + 1) : Real) := by
          exact mul_le_mul_of_nonneg_right hpow hden_nonneg

/-- Row-`0` analytic crosswalk from the sinc series to the exact majorant
`tsum`.  This closes only the zeroth derivative row. -/
theorem realSinc_norm_le_tsum_majorant_zero
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) :
    ‖realSinc u‖ <=
      ∑' m : Nat, (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  let f : Nat -> Real := fun m : Nat =>
    ((-1 : Real) ^ m * u ^ (2 * m)) /
      (Nat.factorial (2 * m + 1) : Real)
  let g : Nat -> Real := fun m : Nat =>
    (step33Sub0RealSincDerivMajorantTerm 0 m : Real)
  have hg : Summable g := by
    simpa [g] using
      step33Sub0RealSincDerivMajorantTerm_real_shift_summable 0 0
  have hfg : ∀ m : Nat, ‖f m‖ <= g m := by
    intro m
    simpa [f, g] using
      step33Sub0RealSinc_seriesTerm_norm_le_majorant_zero hu m
  have hf : Summable (fun m : Nat => ‖f m‖) := by
    refine Summable.of_nonneg_of_le (f := g) (g := fun m : Nat => ‖f m‖)
      ?hNonneg ?hLe hg
    · intro m
      exact norm_nonneg _
    · exact hfg
  have hsum_norm :
      ‖∑' m : Nat, f m‖ <= ∑' m : Nat, ‖f m‖ :=
    norm_tsum_le_tsum_norm hf
  have hsum_le :
      (∑' m : Nat, ‖f m‖) <= ∑' m : Nat, g m :=
    Summable.tsum_le_tsum hfg hf hg
  have hseries : HasSum f (realSinc u) := by
    simpa [f] using realSinc_hasSum_even_powerSeries u
  rw [← hseries.tsum_eq]
  exact le_trans hsum_norm hsum_le

/-- Zeroth-derivative version of the row-`0` analytic crosswalk. -/
theorem realSinc_iteratedDeriv_zero_norm_le_tsum_majorant
    {u : Real} (hu : u ∈ Set.Icc (0 : Real) ((1 : Real) / 400)) :
    ‖iteratedDeriv 0 realSinc u‖ <=
      ∑' m : Nat, (step33Sub0RealSincDerivMajorantTerm 0 m : Real) := by
  simpa [iteratedDeriv] using realSinc_norm_le_tsum_majorant_zero hu

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
