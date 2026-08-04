import Mathlib

/-!
# A finite-to-infinite core for the scaled Jacobi forced receiver

This file isolates the algebraic and limiting part of the proposed receiver route.  It does not
construct a source-specific receiver, prove its polynomial growth, or assert any sign conclusion.
-/

open Filter Topology
open scoped BigOperators

/-- The half-line Jacobi operator, with the absent `q = 0` left neighbor set to zero. -/
def jacobiOp
    (p d r : ℕ → ℝ)
    (y : ℕ → ℝ)
    (q : ℕ) : ℝ :=
  (if q = 0 then 0 else p q * y (q - 1)) +
    d q * y q +
    r q * y (q + 1)

/-- The live right boundary term in the finite Jacobi Green identity. -/
def jacobiTerminal
    (ω r Y δ : ℕ → ℝ)
    (Q : ℕ) : ℝ :=
  ω Q * r Q *
    (Y Q * δ (Q + 1) - δ Q * Y (Q + 1))

/-- A sequence has at most polynomial growth. -/
def SequencePolynomialGrowth (y : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∃ d : ℕ, ∀ q : ℕ,
      |y q| ≤ C * (q + 1 : ℝ) ^ d

/-- A sequence decays faster than every polynomial weight. -/
def SequenceRapidDecay (y : ℕ → ℝ) : Prop :=
  ∀ d : ℕ,
    Tendsto
      (fun q : ℕ ↦ (q + 1 : ℝ) ^ d * |y q|)
      atTop
      (nhds 0)

/-- Finite summation by parts for a symmetrizable half-line Jacobi operator. -/
theorem finiteJacobiGreenIdentity
    (p d r ω Y δ : ℕ → ℝ)
    (Q : ℕ)
    (hsym :
      ∀ q, ω q * r q = ω (q + 1) * p (q + 1)) :
    Finset.sum (Finset.range (Q + 1)) (fun q ↦
        ω q *
          (Y q * jacobiOp p d r δ q -
            δ q * jacobiOp p d r Y q)) =
      jacobiTerminal ω r Y δ Q := by
  induction Q with
  | zero =>
      simp [jacobiOp, jacobiTerminal]
      ring
  | succ Q ih =>
      rw [Finset.sum_range_succ, ih]
      simp only [jacobiTerminal]
      rw [hsym Q]
      simp [jacobiOp]
      ring

private theorem sequencePolynomialGrowth_mul
    {u v : ℕ → ℝ}
    (hu : SequencePolynomialGrowth u)
    (hv : SequencePolynomialGrowth v) :
    SequencePolynomialGrowth (fun q ↦ u q * v q) := by
  rcases hu with ⟨Cu, hCu, du, hu⟩
  rcases hv with ⟨Cv, hCv, dv, hv⟩
  refine ⟨Cu * Cv, mul_nonneg hCu hCv, du + dv, ?_⟩
  intro q
  rw [abs_mul, pow_add]
  calc
    |u q| * |v q| ≤
        (Cu * (q + 1 : ℝ) ^ du) * (Cv * (q + 1 : ℝ) ^ dv) :=
      mul_le_mul (hu q) (hv q) (abs_nonneg _) (mul_nonneg hCu (by positivity))
    _ = (Cu * Cv) * ((q + 1 : ℝ) ^ du * (q + 1 : ℝ) ^ dv) := by ring

private theorem sequencePolynomialGrowth_shift
    {y : ℕ → ℝ}
    (hy : SequencePolynomialGrowth y) :
    SequencePolynomialGrowth (fun q ↦ y (q + 1)) := by
  rcases hy with ⟨C, hC, d, hy⟩
  refine ⟨C * 2 ^ d, mul_nonneg hC (by positivity), d, ?_⟩
  intro q
  have hbase : ((q + 1 : ℕ) + 1 : ℝ) ≤ 2 * (q + 1 : ℝ) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ (q : ℝ) by positivity]
  have hpow : ((q + 1 : ℕ) + 1 : ℝ) ^ d ≤ (2 * (q + 1 : ℝ)) ^ d := by
    gcongr
  calc
    |y (q + 1)| ≤ C * ((q + 1 : ℕ) + 1 : ℝ) ^ d := hy (q + 1)
    _ ≤ C * (2 * (q + 1 : ℝ)) ^ d := mul_le_mul_of_nonneg_left hpow hC
    _ = (C * 2 ^ d) * (q + 1 : ℝ) ^ d := by rw [mul_pow]; ring

private theorem sequenceRapidDecay_shift
    {y : ℕ → ℝ}
    (hy : SequenceRapidDecay y) :
    SequenceRapidDecay (fun q ↦ y (q + 1)) := by
  intro d
  refine squeeze_zero
    (g := fun q ↦ ((q + 1 : ℕ) + 1 : ℝ) ^ d * |y (q + 1)|)
    (fun q ↦ mul_nonneg (by positivity) (abs_nonneg _))
    (fun q ↦ ?_) ?_
  · apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    gcongr
    norm_num
  · simpa only [Function.comp_apply] using
      (hy d).comp (tendsto_add_atTop_nat 1)

private theorem tendsto_mul_zero_of_polynomialGrowth_rapidDecay
    {u v : ℕ → ℝ}
    (hu : SequencePolynomialGrowth u)
    (hv : SequenceRapidDecay v) :
    Tendsto (fun q ↦ u q * v q) atTop (nhds 0) := by
  rcases hu with ⟨C, hC, d, hu⟩
  refine squeeze_zero_norm
    (a := fun q : ℕ ↦ C * ((q + 1 : ℝ) ^ d * |v q|))
    (fun q ↦ ?_) ?_
  · rw [Real.norm_eq_abs, abs_mul]
    calc
      |u q| * |v q| ≤ (C * (q + 1 : ℝ) ^ d) * |v q| :=
        mul_le_mul_of_nonneg_right (hu q) (abs_nonneg _)
      _ = C * ((q + 1 : ℝ) ^ d * |v q|) := by ring
  · simpa using tendsto_const_nhds.mul (hv d)

/-- Polynomial coefficient growth and rapid solution decay kill the live Jacobi boundary. -/
theorem jacobiTerminal_tendsto_zero_of_growth_decay
    (ω r Y δ : ℕ → ℝ)
    (hωr : SequencePolynomialGrowth (fun q ↦ ω q * r q))
    (hY : SequencePolynomialGrowth Y)
    (hδ : SequenceRapidDecay δ) :
    Tendsto
      (jacobiTerminal ω r Y δ)
      atTop
      (nhds 0) := by
  have hleft :
      Tendsto
        (fun q ↦ ((ω q * r q) * Y q) * δ (q + 1))
        atTop
        (nhds 0) :=
    tendsto_mul_zero_of_polynomialGrowth_rapidDecay
      (sequencePolynomialGrowth_mul hωr hY)
      (sequenceRapidDecay_shift hδ)
  have hright :
      Tendsto
        (fun q ↦ ((ω q * r q) * Y (q + 1)) * δ q)
        atTop
        (nhds 0) :=
    tendsto_mul_zero_of_polynomialGrowth_rapidDecay
      (sequencePolynomialGrowth_mul hωr (sequencePolynomialGrowth_shift hY))
      hδ
  have hfun :
      jacobiTerminal ω r Y δ =
        fun q ↦ ((ω q * r q) * Y q) * δ (q + 1) -
          ((ω q * r q) * Y (q + 1)) * δ q := by
    funext q
    simp only [jacobiTerminal]
    ring
  rw [hfun]
  simpa using hleft.sub hright

/-- Adding a homogeneous mode does not change the receiver pairing when it is orthogonal to the
forcing mode. -/
theorem jacobiReceiverPair_gauge_invariant
    (ω Y b0 b4 : ℕ → ℝ)
    (c : ℝ)
    (hsumY : Summable (fun q ↦ ω q * Y q * b0 q))
    (hsumB4 : Summable (fun q ↦ ω q * b4 q * b0 q))
    (horth :
      ∑' q, ω q * b4 q * b0 q = 0) :
    (∑' q, ω q * (Y q + c * b4 q) * b0 q) =
      ∑' q, ω q * Y q * b0 q := by
  have hscaled : Summable (fun q ↦ c * (ω q * b4 q * b0 q)) :=
    hsumB4.mul_left c
  calc
    tsum (fun q ↦ ω q * (Y q + c * b4 q) * b0 q) =
        tsum (fun q ↦ (ω q * Y q * b0 q) + c * (ω q * b4 q * b0 q)) := by
      apply tsum_congr
      intro q
      ring
    _ = tsum (fun q ↦ ω q * Y q * b0 q) +
        tsum (fun q ↦ c * (ω q * b4 q * b0 q)) :=
      hsumY.tsum_add hscaled
    _ = tsum (fun q ↦ ω q * Y q * b0 q) +
        c * tsum (fun q ↦ ω q * b4 q * b0 q) := by
      rw [hsumB4.tsum_mul_left]
    _ = tsum (fun q ↦ ω q * Y q * b0 q) := by rw [horth]; ring

/-- The infinite forced-receiver identity.  Its orientation is `response = gap * pairing`; the
existence and growth of a source-specific receiver remain external hypotheses. -/
theorem scaledSampledResponse_eq_gap_mul_receiverPair
    (p d r ω δ Y b0 A : ℕ → ℝ)
    (gap : ℝ)
    (hω : ∀ q, ω q ≠ 0)
    (hsym :
      ∀ q, ω q * r q = ω (q + 1) * p (q + 1))
    (hdelta :
      ∀ q, jacobiOp p d r δ q = gap * b0 q)
    (hreceiver :
      ∀ q, jacobiOp p d r Y q = A q / ω q)
    (hresponse :
      Summable (fun q ↦ δ q * A q))
    (hpair :
      Summable (fun q ↦ ω q * Y q * b0 q))
    (hterminal :
      Tendsto (jacobiTerminal ω r Y δ) atTop (nhds 0)) :
    (∑' q, δ q * A q) =
      gap * ∑' q, ω q * Y q * b0 q := by
  have hfinite : ∀ Q : ℕ,
      Finset.sum (Finset.range (Q + 1)) (fun q ↦ δ q * A q) =
        gap * Finset.sum (Finset.range (Q + 1)) (fun q ↦ ω q * Y q * b0 q) -
          jacobiTerminal ω r Y δ Q := by
    intro Q
    have hgreen := finiteJacobiGreenIdentity p d r ω Y δ Q hsym
    have htermwise : ∀ q,
        ω q *
            (Y q * jacobiOp p d r δ q -
              δ q * jacobiOp p d r Y q) =
          gap * (ω q * Y q * b0 q) - δ q * A q := by
      intro q
      rw [hdelta q, hreceiver q]
      field_simp [hω q]
    rw [Finset.sum_congr rfl (fun q _ ↦ htermwise q)] at hgreen
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hgreen
    linarith
  have hresponseLimit :
      Tendsto
        (fun Q ↦ Finset.sum (Finset.range (Q + 1)) (fun q ↦ δ q * A q))
        atTop
        (nhds (∑' q, δ q * A q)) :=
    (tendsto_add_atTop_iff_nat 1).2 hresponse.hasSum.tendsto_sum_nat
  have hpairLimit :
      Tendsto
        (fun Q ↦ Finset.sum (Finset.range (Q + 1)) (fun q ↦ ω q * Y q * b0 q))
        atTop
        (nhds (∑' q, ω q * Y q * b0 q)) :=
    (tendsto_add_atTop_iff_nat 1).2 hpair.hasSum.tendsto_sum_nat
  have hforcedLimit :
      Tendsto
        (fun Q ↦ Finset.sum (Finset.range (Q + 1)) (fun q ↦ δ q * A q))
        atTop
        (nhds (gap * (∑' q, ω q * Y q * b0 q) - 0)) := by
    convert (tendsto_const_nhds.mul hpairLimit).sub hterminal using 1
    ext Q
    exact hfinite Q
  have hunique := tendsto_nhds_unique hresponseLimit hforcedLimit
  simpa using hunique

/-!
The following tiny mutation plants record the scope of the interface.

* P-JY-1: the live orientation sends `gap = 2`, `pair = 3` to `response = 6`; its reciprocal
  mutant does not.
* P-JY-2: `jacobiTerminal` remains a live boundary expression until the decay theorem is applied.
* P-JY-3: polynomial growth is a load-bearing hypothesis of the terminal limit.
* P-JY-4: gauge invariance explicitly requires the `b4`--`b0` orthogonality equation.
* P-JY-5: the core accepts a negative pairing and makes no sign claim.
* P-JY-6: every theorem is parameter-uniform; no distinguished finite calibration index occurs.
-/

example : (6 : ℝ) = 2 * 3 := by norm_num

example : (6 : ℝ) ≠ (2 : ℝ)⁻¹ * 3 := by norm_num

example : (-6 : ℝ) = 2 * (-3) := by norm_num
