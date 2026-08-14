import Q3.Proofs.RouteB.D0Mode4JacobiMatchedNormalizedCoefficientRow
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreIntervalBound
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Absolute summability at the mode-four Ferrers boundary

The committed matched recurrence row already has an exact splice to a
positive tail bounded by `2⁻ⁿ`.  This file records the analytic consequence
needed before that row may be used as coefficients of a Ferrers series:
absolute summability of the whole row.

The file also fixes the intended even-Legendre series, consumes the sharp
ordinary-Legendre bound on `[-1, 1]`, and proves uniform convergence and
continuity on that source window.  Every fixed polynomial coefficient moment
is summable as well, preparing later termwise differentiation.

This does not identify the series with a regular first-kind PSWF, prove its
differential equation, or select the degree-four ordered mode.
-/

noncomputable section

/-- An exact splice to the committed geometrically decaying right tail makes
the entire coefficient row absolutely summable.  The finite prefix is handled
by `summable_nat_add_iff`; no square-summability-to-absolute-summability
shortcut is used. -/
theorem mode4RecurrenceRow_abs_summable_of_tail_splice
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (a : ℕ → ℝ)
    (hsplice : ∀ n : ℕ,
      a (K - 1 + n) =
        a (K - 1) *
          mode4TailCoefficientRow mProject Λ K n) :
    Summable (fun q : ℕ => |a q|) := by
  have hgeom : Summable (fun n : ℕ => |a (K - 1)| * (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_of_abs_lt_one (by norm_num)).mul_left |a (K - 1)|
  have htail :
      Summable (fun n : ℕ => |a (K - 1 + n)|) := by
    refine Summable.of_nonneg_of_le (fun n => abs_nonneg _) (fun n => ?_) hgeom
    rw [hsplice n, abs_mul]
    have htailPos := mode4TailCoefficientRow_pos
      mProject K Λ hm hK hsep hΛ n
    rw [abs_of_pos htailPos]
    exact mul_le_mul_of_nonneg_left
      (mode4TailCoefficientRow_le_half_pow
        mProject K Λ hm hK hsep hΛ n)
      (abs_nonneg _)
  apply (summable_nat_add_iff (K - 1)).1
  simpa only [Nat.add_comm] using htail

/-- Every fixed polynomial moment of the matched row is absolutely summable.
The proof uses only the exact geometric tail splice and keeps the finite
prefix explicit. -/
theorem mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (a : ℕ → ℝ)
    (hsplice : ∀ n : ℕ,
      a (K - 1 + n) =
        a (K - 1) *
          mode4TailCoefficientRow mProject Λ K n)
    (r : ℕ) :
    Summable (fun q : ℕ => (((q + 1 : ℕ) : ℝ) ^ r) * |a q|) := by
  have hbase :
      Summable (fun n : ℕ => (n : ℝ) ^ r * (1 / 2 : ℝ) ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one r (by norm_num)
  have hshift :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ r *
        (1 / 2 : ℝ) ^ (n + 1)) :=
    (summable_nat_add_iff
      (f := fun n : ℕ => (n : ℝ) ^ r * (1 / 2 : ℝ) ^ n) 1).2 hbase
  have hone :
      Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ r *
        (1 / 2 : ℝ) ^ n) := by
    have hs := hshift.mul_left 2
    convert hs using 1
    funext n
    push_cast
    rw [pow_succ]
    ring
  have hmajor :
      Summable (fun n : ℕ =>
        (|a (K - 1)| * (K : ℝ) ^ r) *
          (((n + 1 : ℕ) : ℝ) ^ r * (1 / 2 : ℝ) ^ n)) :=
    hone.mul_left (|a (K - 1)| * (K : ℝ) ^ r)
  have htail :
      Summable (fun n : ℕ =>
        (((K - 1 + n + 1 : ℕ) : ℝ) ^ r) *
          |a (K - 1 + n)|) := by
    refine Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (abs_nonneg _))
      (fun n => ?_) hmajor
    rw [hsplice n, abs_mul]
    have htailPos := mode4TailCoefficientRow_pos
      mProject K Λ hm hK hsep hΛ n
    rw [abs_of_pos htailPos]
    have htailLe := mode4TailCoefficientRow_le_half_pow
      mProject K Λ hm hK hsep hΛ n
    have hKpos : (0 : ℝ) ≤ K := by positivity
    have hn1pos : (0 : ℝ) ≤ (n + 1 : ℕ) := by positivity
    have hindex :
        ((K - 1 + n + 1 : ℕ) : ℝ) ≤
          (K : ℝ) * (n + 1 : ℕ) := by
      have hKnat : 1 ≤ K := le_trans (by omega : 1 ≤ 3) hK
      have hnle : n ≤ K * n :=
        Nat.le_mul_of_pos_left n (by omega)
      have hidxNat : K - 1 + n + 1 = K + n := by omega
      have hleNat : K + n ≤ K * (n + 1) := by
        rw [Nat.mul_add]
        omega
      rw [hidxNat]
      exact_mod_cast hleNat
    have hpow :
        (((K - 1 + n + 1 : ℕ) : ℝ) ^ r) ≤
          ((K : ℝ) * (n + 1 : ℕ)) ^ r := by
      gcongr
    calc
      (((K - 1 + n + 1 : ℕ) : ℝ) ^ r) *
          (|a (K - 1)| * mode4TailCoefficientRow mProject Λ K n) ≤
        (((K : ℝ) * (n + 1 : ℕ)) ^ r) *
          (|a (K - 1)| * (1 / 2 : ℝ) ^ n) := by
            gcongr
      _ = (|a (K - 1)| * (K : ℝ) ^ r) *
          (((n + 1 : ℕ) : ℝ) ^ r * (1 / 2 : ℝ) ^ n) := by
        rw [mul_pow]
        ring
  apply (summable_nat_add_iff (K - 1)).1
  simpa only [Nat.add_comm] using htail

/-- One source-shaped even Ferrers term.  The alternating factor is the fixed
phase convention of the mode-four Legendre recurrence. -/
noncomputable def mode4FerrersTerm
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ q * a q *
    mode4OrdinaryLegendre (2 * q) x

/-- The source-shaped even Ferrers series associated with a coefficient row. -/
noncomputable def mode4FerrersSeries
    (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑' q : ℕ, mode4FerrersTerm a q x

/-- Parity is termwise and therefore does not require convergence. -/
theorem mode4FerrersSeries_even (a : ℕ → ℝ) :
    Function.Even (mode4FerrersSeries a) := by
  intro x
  unfold mode4FerrersSeries mode4FerrersTerm
  apply tsum_congr
  intro q
  rw [mode4OrdinaryLegendre_even]

/-- At the right endpoint the even Legendre factors are exactly one. -/
theorem mode4FerrersSeries_at_one (a : ℕ → ℝ) :
    mode4FerrersSeries a 1 =
      ∑' q : ℕ, (-1 : ℝ) ^ q * a q := by
  unfold mode4FerrersSeries
  apply tsum_congr
  intro q
  simp [mode4FerrersTerm]

/-- At the left endpoint the even Legendre factors are also exactly one. -/
theorem mode4FerrersSeries_at_neg_one (a : ℕ → ℝ) :
    mode4FerrersSeries a (-1) =
      ∑' q : ℕ, (-1 : ℝ) ^ q * a q := by
  calc
    mode4FerrersSeries a (-1) = mode4FerrersSeries a 1 :=
      mode4FerrersSeries_even a 1
    _ = ∑' q : ℕ, (-1 : ℝ) ^ q * a q :=
      mode4FerrersSeries_at_one a

/-- The coefficient absolute values dominate the Ferrers terms uniformly on
the closed unit interval. -/
theorem mode4FerrersTerm_norm_le_coefficientAbs
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    ‖mode4FerrersTerm a q x‖ ≤ |a q| := by
  have hP := mode4OrdinaryLegendre_abs_le_one (2 * q) x hx
  rw [Real.norm_eq_abs]
  unfold mode4FerrersTerm
  rw [abs_mul, abs_mul, abs_pow]
  norm_num
  exact mul_le_of_le_one_right (abs_nonneg _) hP

/-- Absolute summability of the coefficient row gives pointwise summability
of the Ferrers series at every point of the closed unit interval. -/
theorem mode4FerrersTerm_summable
    (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => |a q|))
    (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun q : ℕ => mode4FerrersTerm a q x) := by
  have hnorm : Summable (fun q : ℕ => ‖mode4FerrersTerm a q x‖) :=
    Summable.of_nonneg_of_le
      (fun q => norm_nonneg _)
      (fun q => mode4FerrersTerm_norm_le_coefficientAbs a q x hx)
      ha
  exact hnorm.of_norm

/-- The Ferrers partial sums converge uniformly on the closed unit interval. -/
theorem mode4FerrersSeries_hasSumUniformlyOn
    (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => |a q|)) :
    HasSumUniformlyOn
      (mode4FerrersTerm a)
      (mode4FerrersSeries a)
      (Set.Icc (-1 : ℝ) 1) := by
  apply HasSumUniformlyOn.of_norm_le_summable ha
  intro q x hx
  exact mode4FerrersTerm_norm_le_coefficientAbs a q x hx

/-- The uniformly convergent Ferrers series is continuous on the closed unit
interval. -/
theorem mode4FerrersSeries_continuousOn
    (a : ℕ → ℝ)
    (ha : Summable (fun q : ℕ => |a q|)) :
    ContinuousOn (mode4FerrersSeries a) (Set.Icc (-1 : ℝ) 1) := by
  unfold mode4FerrersSeries
  apply continuousOn_tsum
  · intro q
    unfold mode4FerrersTerm mode4OrdinaryLegendre
    exact
      (continuous_const.mul
        (mode4OrdinaryLegendrePolynomial (2 * q)).continuous).continuousOn
  · exact ha
  · intro q x hx
    exact mode4FerrersTerm_norm_le_coefficientAbs a q x hx

/-- A zero of the committed matching function now supplies a normalized
recurrence row together with the absolute summability needed at the Ferrers
boundary.  All recurrence and normalization conclusions are preserved
literally from the existing constructor. -/
theorem exists_mode4MatchedNormalizedAbsSummableRecurrenceRow_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q : ℕ => |a q|) ∧
      Summable (fun q : ℕ => (a q) ^ 2) ∧
      HasSum
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        1 ∧
      (∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) q * a (q - 1) +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) q -
              (Λ + mode4JacobiG mProject)) * a q +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) q * a (q + 1) = 0) ∧
      a (K - 1) ≠ 0 ∧
      ∀ n : ℕ,
        a (K - 1 + n) =
          a (K - 1) *
            mode4TailCoefficientRow mProject Λ K n := by
  obtain ⟨a, ha0, haSq, haNorm, haRec, haSpliceNe, haSplice⟩ :=
    exists_mode4MatchedNormalizedRecurrenceRow_of_root
      mProject K Λ hm hK hsep hΛ hroot
  refine ⟨a, ha0, ?_, haSq, haNorm, haRec, haSpliceNe, haSplice⟩
  exact mode4RecurrenceRow_abs_summable_of_tail_splice
    mProject K Λ hm hK hsep hΛ a haSplice

/-- The matched row constructor therefore supplies a continuous even Ferrers
series on the source window, while retaining every exact recurrence and
normalization conclusion.  No PSWF or ordered-mode identification is claimed. -/
theorem exists_mode4MatchedNormalizedContinuousFerrersRow_of_root
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q *
              (mode4JacobiIndex q + 1) -
            20)
    (hΛ : Λ ≤ 20)
    (hroot : mode4RootFunction mProject K Λ = 0) :
    ∃ a : ℕ → ℝ,
      0 < a 0 ∧
      Summable (fun q : ℕ => |a q|) ∧
      Summable (fun q : ℕ => (a q) ^ 2) ∧
      HasSum
        (fun q : ℕ =>
          (a q) ^ 2 / (4 * (q : ℝ) + 1))
        1 ∧
      (∀ q : ℕ,
        mode4PSWFLegendreSubdiagonal
              (mode4JacobiG mProject) q * a (q - 1) +
          (mode4PSWFLegendreDiagonal
                (mode4JacobiG mProject) q -
              (Λ + mode4JacobiG mProject)) * a q +
          mode4PSWFLegendreSuperdiagonal
              (mode4JacobiG mProject) q * a (q + 1) = 0) ∧
      a (K - 1) ≠ 0 ∧
      (∀ n : ℕ,
        a (K - 1 + n) =
          a (K - 1) *
            mode4TailCoefficientRow mProject Λ K n) ∧
      ContinuousOn (mode4FerrersSeries a) (Set.Icc (-1 : ℝ) 1) := by
  obtain ⟨a, ha0, haAbs, haSq, haNorm, haRec, haSpliceNe, haSplice⟩ :=
    exists_mode4MatchedNormalizedAbsSummableRecurrenceRow_of_root
      mProject K Λ hm hK hsep hΛ hroot
  exact ⟨a, ha0, haAbs, haSq, haNorm, haRec, haSpliceNe,
    haSplice, mode4FerrersSeries_continuousOn a haAbs⟩
