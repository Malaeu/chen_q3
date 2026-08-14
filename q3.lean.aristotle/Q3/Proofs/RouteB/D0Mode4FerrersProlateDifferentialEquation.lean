import Q3.Proofs.RouteB.D0Mode4FerrersInteriorRegularity
import Q3.Proofs.RouteB.D0Mode4OrdinaryLegendreXSquaredAction

/-!
# Exact prolate ODE for the matched mode-four Ferrers series

This file closes the analytic-algebraic seam from the exact three-term
Legendre recurrence to the source spheroidal differential equation.  The
proof keeps the zero row explicit, proves absolute summability of every
reindexed band, and performs only legal shifts of summable series.

The result constructs a C2 interior Ferrers eigenfunction from a matching
root.  It does not yet identify the ordered degree-four PSWF, prove the
finite-Fourier eigenrelation, or construct the degree-zero companion.
-/

open Polynomial

noncomputable section

theorem mode4FerrersLegendre_Xsq_zero (G x : ℝ) :
    G * x ^ 2 * mode4OrdinaryLegendre 0 x =
      -mode4PSWFLegendreSubdiagonal G 1 *
          mode4OrdinaryLegendre 2 x +
        (mode4PSWFLegendreDiagonal G 0 -
          ((0 : ℝ) * (0 + 1))) *
          mode4OrdinaryLegendre 0 x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_three_term_succ 0)
  simp only [eval_mul, eval_C, eval_X, eval_sub] at h
  norm_num [mode4OrdinaryLegendrePolynomial_zero,
    mode4OrdinaryLegendrePolynomial_one] at h ⊢
  unfold mode4PSWFLegendreSubdiagonal mode4PSWFLegendreDiagonal
  norm_num [mode4JacobiIndex]
  change G * x ^ 2 =
    -(-(G * 2) / 3 *
      (mode4OrdinaryLegendrePolynomial 2).eval x) + G / 3
  have hx : x ^ 2 =
      (2 * (mode4OrdinaryLegendrePolynomial 2).eval x + 1) / 3 := by
    linarith
  rw [hx]
  ring

theorem mode4FerrersLegendre_Xsq_succ (G x : ℝ) (q : ℕ) :
    G * x ^ 2 * mode4OrdinaryLegendre (2 * (q + 1)) x =
      -mode4PSWFLegendreSubdiagonal G (q + 2) *
          mode4OrdinaryLegendre (2 * (q + 2)) x +
        (mode4PSWFLegendreDiagonal G (q + 1) -
          (((2 * (q + 1) : ℕ) : ℝ) *
            (((2 * (q + 1) : ℕ) : ℝ) + 1))) *
          mode4OrdinaryLegendre (2 * (q + 1)) x -
        mode4PSWFLegendreSuperdiagonal G q *
          mode4OrdinaryLegendre (2 * q) x := by
  have h := congrArg (fun p : ℝ[X] => p.eval x)
    (mode4OrdinaryLegendrePolynomial_X_sq_mul (2 * q))
  simp only [eval_mul, eval_pow, eval_X, eval_C, eval_add] at h
  have hupper :
      G * ((((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
        (((2 * q + 4 : ℕ) : ℝ) / ((4 * q + 7 : ℕ) : ℝ))) =
        -mode4PSWFLegendreSubdiagonal G (q + 2) := by
    have hN : mode4JacobiIndex (q + 2) = 2 * (q : ℝ) + 4 := by
      unfold mode4JacobiIndex
      push_cast
      ring
    have hsub :
        -mode4PSWFLegendreSubdiagonal G (q + 2) =
          G * (mode4JacobiIndex (q + 2) - 1) *
              mode4JacobiIndex (q + 2) /
            ((2 * mode4JacobiIndex (q + 2) - 3) *
              (2 * mode4JacobiIndex (q + 2) - 1)) := by
      unfold mode4PSWFLegendreSubdiagonal
      dsimp
      ring
    rw [hsub, hN]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rw [div_mul_div_comm]
    ring
  have hdiag :
      G * (((((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
          (((2 * q + 3 : ℕ) : ℝ) / ((4 * q + 7 : ℕ) : ℝ))) +
        ((((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
          (((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 3 : ℕ) : ℝ)))) =
        mode4PSWFLegendreDiagonal G (q + 1) -
          (((2 * (q + 1) : ℕ) : ℝ) *
            (((2 * (q + 1) : ℕ) : ℝ) + 1)) := by
    have hN : mode4JacobiIndex (q + 1) = 2 * (q : ℝ) + 2 := by
      unfold mode4JacobiIndex
      push_cast
      ring
    have hD :
        mode4PSWFLegendreDiagonal G (q + 1) -
            mode4JacobiIndex (q + 1) *
              (mode4JacobiIndex (q + 1) + 1) =
          G * (2 * mode4JacobiIndex (q + 1) *
              (mode4JacobiIndex (q + 1) + 1) - 1) /
            ((2 * mode4JacobiIndex (q + 1) - 1) *
              (2 * mode4JacobiIndex (q + 1) + 3)) := by
      unfold mode4PSWFLegendreDiagonal
      dsimp
      ring
    rw [show (((2 * (q + 1) : ℕ) : ℝ) *
          (((2 * (q + 1) : ℕ) : ℝ) + 1)) =
        mode4JacobiIndex (q + 1) *
          (mode4JacobiIndex (q + 1) + 1) by
      rw [hN]
      norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
      ring,
      hD, hN]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    have hden : (4 * (q : ℝ) + 3) ≠ 0 := by positivity
    have hden' : (3 + (q : ℝ) * 4) ≠ 0 := by positivity
    field_simp [hden]
    have hcancel := inv_mul_cancel₀ hden'
    ring_nf at hcancel ⊢
    linear_combination
      -(G * (385 + 1228 * (q : ℝ) + 1416 * (q : ℝ) ^ 2 +
        704 * (q : ℝ) ^ 3 + 128 * (q : ℝ) ^ 4)) * hcancel
  have hlower :
      G * ((((2 * q + 2 : ℕ) : ℝ) / ((4 * q + 5 : ℕ) : ℝ)) *
        (((2 * q + 1 : ℕ) : ℝ) / ((4 * q + 3 : ℕ) : ℝ))) =
        -mode4PSWFLegendreSuperdiagonal G q := by
    unfold mode4PSWFLegendreSuperdiagonal mode4JacobiIndex
    push_cast
    field_simp
    all_goals ring
  change G * x ^ 2 *
      (mode4OrdinaryLegendrePolynomial (2 * (q + 1))).eval x = _
  simp only [mode4OrdinaryLegendre]
  norm_num [Nat.mul_add, Nat.mul_assoc] at h ⊢
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hupper hdiag hlower ⊢
  calc
    _ = G *
        (((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 5) *
            ((2 * (q : ℝ) + 4) / (4 * (q : ℝ) + 7))) *
            (mode4OrdinaryLegendrePolynomial (2 * q + 4)).eval x +
          (((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 5) *
              ((2 * (q : ℝ) + 3) / (4 * (q : ℝ) + 7)) +
            (2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 5) *
              ((2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 3))) *
            (mode4OrdinaryLegendrePolynomial (2 * q + 2)).eval x +
          ((2 * (q : ℝ) + 2) / (4 * (q : ℝ) + 5) *
            ((2 * (q : ℝ) + 1) / (4 * (q : ℝ) + 3))) *
            (mode4OrdinaryLegendrePolynomial (2 * q)).eval x)) := by
        have hG := congrArg (fun y : ℝ => G * y) h
        ring_nf at hG ⊢
        exact hG
    _ = _ := by
      rw [mul_add, mul_add, ← mul_assoc, hupper,
        ← mul_assoc, hdiag, ← mul_assoc, hlower]
      ring

noncomputable def mode4FerrersPhase (a : ℕ → ℝ) (q : ℕ) : ℝ :=
  (-1 : ℝ) ^ q * a q

theorem mode4FerrersPhase_recurrence
    (G E : ℝ) (a : ℕ → ℝ)
    (ha : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - E) * a q +
        mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0) :
    ∀ q : ℕ,
      -mode4PSWFLegendreSubdiagonal G q * mode4FerrersPhase a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - E) * mode4FerrersPhase a q -
        mode4PSWFLegendreSuperdiagonal G q * mode4FerrersPhase a (q + 1) = 0 := by
  intro q
  cases q with
  | zero =>
      have h := ha 0
      simp [mode4FerrersPhase, mode4PSWFLegendreSubdiagonal,
        mode4JacobiIndex] at h ⊢
      linarith
  | succ q =>
      have h := ha (q + 1)
      simp only [mode4FerrersPhase, Nat.add_sub_cancel,
        pow_succ, Nat.add_assoc] at h ⊢
      rw [show q + (1 + 1) = q + 2 by omega] at h
      linear_combination -((-1 : ℝ) ^ q) * h

noncomputable def mode4FerrersUpperBand
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersPhase a q * (-mode4PSWFLegendreSubdiagonal G (q + 1)) *
    mode4OrdinaryLegendre (2 * (q + 1)) x

noncomputable def mode4FerrersDiagonalBand
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersPhase a q *
    (mode4PSWFLegendreDiagonal G q -
      (((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1))) *
    mode4OrdinaryLegendre (2 * q) x

noncomputable def mode4FerrersLowerBand
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  if q = 0 then 0 else
    mode4FerrersPhase a q * (-mode4PSWFLegendreSuperdiagonal G (q - 1)) *
      mode4OrdinaryLegendre (2 * (q - 1)) x

theorem mode4FerrersTerm_prolateBand_action (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    G * x ^ 2 * mode4FerrersTerm a q x =
      mode4FerrersUpperBand G a q x + mode4FerrersDiagonalBand G a q x +
        mode4FerrersLowerBand G a q x := by
  cases q with
  | zero =>
      have h := mode4FerrersLegendre_Xsq_zero G x
      simp [mode4FerrersTerm, mode4FerrersPhase, mode4FerrersUpperBand, mode4FerrersDiagonalBand,
        mode4FerrersLowerBand] at h ⊢
      linear_combination a 0 * h
  | succ q =>
      have h := mode4FerrersLegendre_Xsq_succ G x q
      simp only [mode4FerrersTerm, mode4FerrersPhase, mode4FerrersUpperBand, mode4FerrersDiagonalBand,
        mode4FerrersLowerBand, Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      norm_num [Nat.mul_add, Nat.mul_assoc] at h ⊢
      linear_combination ((-1 : ℝ) ^ (q + 1) * a (q + 1)) * h

theorem mode4FerrersUpperBand_summable
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hG : 0 < G)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun q : ℕ => mode4FerrersUpperBand G a q x) := by
  apply Summable.of_norm_bounded_eventually_nat
    (haAbs.mul_left ((1 / 3 : ℝ) * G))
  filter_upwards [Filter.eventually_ge_atTop (2 : ℕ)] with q hq
  have hq1 : 3 ≤ q + 1 := by omega
  have hLpos := mode4JacobiLower_pos G (q + 1) hG hq1
  have hLle := mode4JacobiLower_le_one_third_mul_G G (q + 1) hG hq1
  have hcross := mode4JacobiLower_eq_neg_pswfLegendreSubdiagonal G (q + 1)
  have hP := mode4OrdinaryLegendre_abs_le_one (2 * (q + 1)) x hx
  rw [Real.norm_eq_abs]
  unfold mode4FerrersUpperBand mode4FerrersPhase
  rw [← hcross, abs_mul, abs_mul, abs_mul, abs_pow,
    abs_of_pos hLpos]
  norm_num
  calc
      |a q| * mode4JacobiLower G (q + 1) *
        |mode4OrdinaryLegendre (2 * (q + 1)) x| ≤
      |a q| * mode4JacobiLower G (q + 1) * 1 := by
        exact mul_le_mul_of_nonneg_left hP
          (mul_nonneg (abs_nonneg _) hLpos.le)
    _ ≤ |a q| * ((1 / 3 : ℝ) * G) := by
      simpa using mul_le_mul_of_nonneg_left hLle (abs_nonneg (a q))
    _ = (1 / 3 : ℝ) * G * |a q| := by ring

theorem mode4FerrersLowerBand_summable
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hG : 0 < G)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun q : ℕ => mode4FerrersLowerBand G a q x) := by
  apply Summable.of_norm_bounded
    (haAbs.mul_left ((1 / 4 : ℝ) * G))
  intro q
  cases q with
  | zero =>
      simp [mode4FerrersLowerBand]
      positivity
  | succ q =>
      have hUpos := mode4JacobiUpper_pos G q hG
      have hUle := mode4JacobiUpper_le_one_quarter_mul_G G q hG
      have hcross := mode4JacobiUpper_eq_neg_pswfLegendreSuperdiagonal G q
      have hP := mode4OrdinaryLegendre_abs_le_one (2 * q) x hx
      rw [Real.norm_eq_abs]
      simp only [mode4FerrersLowerBand, Nat.succ_ne_zero, if_false,
        Nat.succ_sub_one, mode4FerrersPhase]
      rw [← hcross, abs_mul, abs_mul, abs_mul, abs_pow,
        abs_of_pos hUpos]
      norm_num
      calc
        |a (q + 1)| * mode4JacobiUpper G q *
            |mode4OrdinaryLegendre (2 * q) x| ≤
          |a (q + 1)| * mode4JacobiUpper G q * 1 := by
            exact mul_le_mul_of_nonneg_left hP
              (mul_nonneg (abs_nonneg _) hUpos.le)
        _ ≤ |a (q + 1)| * ((1 / 4 : ℝ) * G) := by
          simpa using mul_le_mul_of_nonneg_left hUle (abs_nonneg (a (q + 1)))
        _ = (1 / 4 : ℝ) * G * |a (q + 1)| := by ring

theorem mode4FerrersDiagonalBand_summable
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hG : 0 < G)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun q : ℕ => mode4FerrersDiagonalBand G a q x) := by
  have htotal : Summable (fun q : ℕ =>
      G * x ^ 2 * mode4FerrersTerm a q x) := by
    convert (mode4FerrersTerm_summable a haAbs x hx).mul_left (G * x ^ 2) using 1
  have hupper := mode4FerrersUpperBand_summable G a x hG haAbs hx
  have hlower := mode4FerrersLowerBand_summable G a x hG haAbs hx
  convert (htotal.sub hupper).sub hlower using 1
  funext q
  rw [mode4FerrersTerm_prolateBand_action]
  ring

noncomputable def mode4FerrersIncomingLowerBand
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersPhase a (q - 1) * (-mode4PSWFLegendreSubdiagonal G q) *
    mode4OrdinaryLegendre (2 * q) x

noncomputable def mode4FerrersIncomingUpperBand
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersPhase a (q + 1) * (-mode4PSWFLegendreSuperdiagonal G q) *
    mode4OrdinaryLegendre (2 * q) x

theorem mode4FerrersIncomingLowerBand_zero
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    mode4FerrersIncomingLowerBand G a 0 x = 0 := by
  simp [mode4FerrersIncomingLowerBand, mode4PSWFLegendreSubdiagonal,
    mode4JacobiIndex]

theorem mode4FerrersIncomingLowerBand_succ
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    mode4FerrersIncomingLowerBand G a (q + 1) x = mode4FerrersUpperBand G a q x := by
  simp [mode4FerrersIncomingLowerBand, mode4FerrersUpperBand]

theorem mode4FerrersLowerBand_succ
    (G : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) :
    mode4FerrersLowerBand G a (q + 1) x = mode4FerrersIncomingUpperBand G a q x := by
  simp [mode4FerrersLowerBand, mode4FerrersIncomingUpperBand]

theorem mode4FerrersIncomingLowerBand_summable
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hupper : Summable (fun q : ℕ => mode4FerrersUpperBand G a q x)) :
    Summable (fun q : ℕ => mode4FerrersIncomingLowerBand G a q x) := by
  apply (summable_nat_add_iff 1).1
  convert hupper using 1

theorem mode4FerrersIncomingUpperBand_summable
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hlower : Summable (fun q : ℕ => mode4FerrersLowerBand G a q x)) :
    Summable (fun q : ℕ => mode4FerrersIncomingUpperBand G a q x) := by
  have hshift := (summable_nat_add_iff 1).2 hlower
  convert hshift using 1

theorem mode4Ferrers_tsum_upper_eq_incomingLower
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hupper : Summable (fun q : ℕ => mode4FerrersUpperBand G a q x)) :
    ∑' q : ℕ, mode4FerrersUpperBand G a q x =
      ∑' q : ℕ, mode4FerrersIncomingLowerBand G a q x := by
  have hin := mode4FerrersIncomingLowerBand_summable G a x hupper
  have hsplit := hin.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, mode4FerrersIncomingLowerBand_zero, zero_add] at hsplit
  calc
    ∑' q : ℕ, mode4FerrersUpperBand G a q x =
        ∑' q : ℕ, mode4FerrersIncomingLowerBand G a (q + 1) x := by
      apply tsum_congr
      intro q
      exact (mode4FerrersIncomingLowerBand_succ G a q x).symm
    _ = ∑' q : ℕ, mode4FerrersIncomingLowerBand G a q x := hsplit

theorem mode4Ferrers_tsum_lower_eq_incomingUpper
    (G : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hlower : Summable (fun q : ℕ => mode4FerrersLowerBand G a q x)) :
    ∑' q : ℕ, mode4FerrersLowerBand G a q x =
      ∑' q : ℕ, mode4FerrersIncomingUpperBand G a q x := by
  have hsplit := hlower.sum_add_tsum_nat_add 1
  simp only [Finset.sum_range_one, mode4FerrersLowerBand, if_pos, zero_add] at hsplit
  calc
    ∑' q : ℕ, mode4FerrersLowerBand G a q x =
        ∑' q : ℕ, mode4FerrersLowerBand G a (q + 1) x := hsplit.symm
    _ = ∑' q : ℕ, mode4FerrersIncomingUpperBand G a q x := by
      apply tsum_congr
      intro q
      exact mode4FerrersLowerBand_succ G a q x

noncomputable def mode4FerrersSpectralTerm
    (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersPhase a q *
    (((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1)) *
    mode4OrdinaryLegendre (2 * q) x

theorem mode4FerrersSpectralTerm_summable
    (a : ℕ → ℝ) (x : ℝ)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    Summable (fun q : ℕ => mode4FerrersSpectralTerm a q x) := by
  have ha2' : Summable (fun q : ℕ =>
      (((q : ℝ) + 1) ^ 2) * |a q|) := by
    convert ha2 using 1
    funext q
    push_cast
    rfl
  apply Summable.of_norm_bounded
    (ha2'.mul_left 4)
  intro q
  have hN :
      (((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1)) ≤
        4 * (((q + 1 : ℕ) : ℝ) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (q : ℝ)]
  have hN0 : 0 ≤
      (((2 * q : ℕ) : ℝ) * (((2 * q : ℕ) : ℝ) + 1)) := by
    positivity
  have hP := mode4OrdinaryLegendre_abs_le_one (2 * q) x hx
  rw [Real.norm_eq_abs]
  unfold mode4FerrersSpectralTerm mode4FerrersPhase
  rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_of_nonneg hN0]
  norm_num
  push_cast at hN hN0 ⊢
  calc
    |a q| *
          (2 * (q : ℝ) * (2 * (q : ℝ) + 1)) *
        |mode4OrdinaryLegendre (2 * q) x| ≤
      |a q| *
          (2 * (q : ℝ) * (2 * (q : ℝ) + 1)) * 1 := by
        exact mul_le_mul_of_nonneg_left hP
          (mul_nonneg (abs_nonneg _) hN0)
    _ ≤ |a q| * (4 * (((q : ℝ) + 1) ^ 2)) := by
      simpa using mul_le_mul_of_nonneg_left hN (abs_nonneg (a q))
    _ = 4 * (((q : ℝ) + 1) ^ 2 * |a q|) := by ring

noncomputable def mode4FerrersRowResidual
    (G E : ℝ) (a : ℕ → ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  mode4FerrersIncomingLowerBand G a q x + mode4FerrersDiagonalBand G a q x +
      mode4FerrersIncomingUpperBand G a q x + mode4FerrersSpectralTerm a q x -
    E * mode4FerrersTerm a q x

theorem mode4FerrersRowResidual_eq_zero
    (G E : ℝ) (a : ℕ → ℝ)
    (ha : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - E) * a q +
        mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0)
    (q : ℕ) (x : ℝ) :
    mode4FerrersRowResidual G E a q x = 0 := by
  have h := mode4FerrersPhase_recurrence G E a ha q
  unfold mode4FerrersPhase at h
  unfold mode4FerrersRowResidual mode4FerrersIncomingLowerBand mode4FerrersDiagonalBand mode4FerrersIncomingUpperBand
    mode4FerrersSpectralTerm mode4FerrersTerm mode4FerrersPhase at ⊢
  linear_combination mode4OrdinaryLegendre (2 * q) x * h

theorem mode4FerrersSeries_spectralIdentity
    (G E : ℝ) (a : ℕ → ℝ) (x : ℝ)
    (hG : 0 < G)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (hx : x ∈ Set.Icc (-1 : ℝ) 1)
    (haRec : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - E) * a q +
        mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0) :
    (∑' q : ℕ, G * x ^ 2 * mode4FerrersTerm a q x) +
        ∑' q : ℕ, mode4FerrersSpectralTerm a q x =
      E * (∑' q : ℕ, mode4FerrersTerm a q x) := by
  have hterm := mode4FerrersTerm_summable a haAbs x hx
  have hupper := mode4FerrersUpperBand_summable G a x hG haAbs hx
  have hlower := mode4FerrersLowerBand_summable G a x hG haAbs hx
  have hdiag := mode4FerrersDiagonalBand_summable G a x hG haAbs hx
  have hinL := mode4FerrersIncomingLowerBand_summable G a x hupper
  have hinU := mode4FerrersIncomingUpperBand_summable G a x hlower
  have hspec := mode4FerrersSpectralTerm_summable a x ha2 hx
  have hEterm : Summable (fun q : ℕ => E * mode4FerrersTerm a q x) :=
    hterm.mul_left E
  have htotalSplit :
      (∑' q : ℕ, G * x ^ 2 * mode4FerrersTerm a q x) =
        (∑' q : ℕ, mode4FerrersUpperBand G a q x) +
          (∑' q : ℕ, mode4FerrersDiagonalBand G a q x) +
          (∑' q : ℕ, mode4FerrersLowerBand G a q x) := by
    calc
      (∑' q : ℕ, G * x ^ 2 * mode4FerrersTerm a q x) =
          ∑' q : ℕ, ((mode4FerrersUpperBand G a q x +
            mode4FerrersDiagonalBand G a q x) + mode4FerrersLowerBand G a q x) := by
        apply tsum_congr
        intro q
        rw [mode4FerrersTerm_prolateBand_action]
      _ = _ := by
        rw [(hupper.add hdiag).tsum_add hlower,
          hupper.tsum_add hdiag]
  have hrowExpand :
      (∑' q : ℕ, mode4FerrersRowResidual G E a q x) =
        (∑' q : ℕ, mode4FerrersIncomingLowerBand G a q x) +
            (∑' q : ℕ, mode4FerrersDiagonalBand G a q x) +
            (∑' q : ℕ, mode4FerrersIncomingUpperBand G a q x) +
            (∑' q : ℕ, mode4FerrersSpectralTerm a q x) -
          ∑' q : ℕ, E * mode4FerrersTerm a q x := by
    unfold mode4FerrersRowResidual
    rw [(((hinL.add hdiag).add hinU).add hspec).tsum_sub hEterm,
      ((hinL.add hdiag).add hinU).tsum_add hspec,
      (hinL.add hdiag).tsum_add hinU,
      hinL.tsum_add hdiag]
  have hrowZero :
      (∑' q : ℕ, mode4FerrersRowResidual G E a q x) = 0 := by
    calc
      (∑' q : ℕ, mode4FerrersRowResidual G E a q x) =
          ∑' _q : ℕ, (0 : ℝ) := by
        apply tsum_congr
        intro q
        exact mode4FerrersRowResidual_eq_zero G E a haRec q x
      _ = 0 := tsum_zero
  have hEtsum :
      (∑' q : ℕ, E * mode4FerrersTerm a q x) =
        E * (∑' q : ℕ, mode4FerrersTerm a q x) := by
    exact tsum_mul_left
  rw [htotalSplit, mode4Ferrers_tsum_upper_eq_incomingLower G a x hupper,
    mode4Ferrers_tsum_lower_eq_incomingUpper G a x hlower]
  linarith [hrowExpand, hrowZero, hEtsum]

theorem mode4FerrersSpectralTsum_eq_derivatives
    (a : ℕ → ℝ) (x : ℝ)
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    (∑' q : ℕ, mode4FerrersSpectralTerm a q x) =
      -(1 - x ^ 2) * mode4FerrersSecondDerivativeSeries a x +
        2 * x * mode4FerrersFirstDerivativeSeries a x := by
  let r : ℝ := (|x| + 1) / 2
  have hxAbs : |x| < 1 := (abs_lt).2 hx
  have hr0 : 0 < r := by
    dsimp [r]
    linarith [abs_nonneg x]
  have hr1 : r < 1 := by
    dsimp [r]
    linarith
  have hxrAbs : |x| ≤ r := by
    dsimp [r]
    linarith
  have hxr : x ∈ Set.Icc (-r) r := by
    constructor
    · linarith [neg_le_abs x, hxrAbs]
    · exact (le_abs_self x).trans hxrAbs
  have hfirst := mode4FerrersFirstDerivativeTerm_summable
    a r hr0.le hr1 ha2 x hxr
  have hsecond := mode4FerrersSecondDerivativeTerm_summable
    a r hr0.le hr1 ha2 x hxr
  have hterm : ∀ q : ℕ,
      mode4FerrersSpectralTerm a q x =
        -(1 - x ^ 2) * mode4FerrersSecondDerivativeTerm a q x +
          2 * x * mode4FerrersFirstDerivativeTerm a q x := by
    intro q
    have hode := mode4OrdinaryLegendre_differentialEquation (2 * q) x
    unfold mode4FerrersSpectralTerm mode4FerrersPhase mode4FerrersSecondDerivativeTerm
      mode4FerrersFirstDerivativeTerm
    push_cast at hode ⊢
    linear_combination ((-1 : ℝ) ^ q * a q) * hode
  unfold mode4FerrersSecondDerivativeSeries
    mode4FerrersFirstDerivativeSeries
  calc
    (∑' q : ℕ, mode4FerrersSpectralTerm a q x) =
        ∑' q : ℕ,
          (-(1 - x ^ 2) * mode4FerrersSecondDerivativeTerm a q x +
            2 * x * mode4FerrersFirstDerivativeTerm a q x) := by
      apply tsum_congr
      exact hterm
    _ = _ := by
      rw [(hsecond.mul_left (-(1 - x ^ 2))).tsum_add
        (hfirst.mul_left (2 * x)), tsum_mul_left, tsum_mul_left]

theorem mode4FerrersSeries_prolateDifferentialEquation
    (G E : ℝ) (a : ℕ → ℝ)
    (hG : 0 < G)
    (haAbs : Summable (fun q : ℕ => |a q|))
    (ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |a q|))
    (haRec : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal G q * a (q - 1) +
        (mode4PSWFLegendreDiagonal G q - E) * a q +
        mode4PSWFLegendreSuperdiagonal G q * a (q + 1) = 0)
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -(1 - x ^ 2) * mode4FerrersSecondDerivativeSeries a x +
          2 * x * mode4FerrersFirstDerivativeSeries a x +
        G * x ^ 2 * mode4FerrersSeries a x =
      E * mode4FerrersSeries a x := by
  have hxClosed : x ∈ Set.Icc (-1 : ℝ) 1 := ⟨hx.1.le, hx.2.le⟩
  have hseries := mode4FerrersSeries_spectralIdentity
    G E a x hG haAbs ha2 hxClosed haRec
  have hspec := mode4FerrersSpectralTsum_eq_derivatives a x ha2 hx
  unfold mode4FerrersSeries
  rw [tsum_mul_left] at hseries
  rw [hspec] at hseries
  linarith

/-- The canonical geometric tail splice supplies all convergence hypotheses,
so an exact source recurrence row satisfies the prolate ODE on the full open
Ferrers interval. -/
theorem mode4FerrersSeries_prolateDifferentialEquation_of_tail_splice
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
    (haRec : ∀ q : ℕ,
      mode4PSWFLegendreSubdiagonal
            (mode4JacobiG mProject) q * a (q - 1) +
        (mode4PSWFLegendreDiagonal
              (mode4JacobiG mProject) q -
            (Λ + mode4JacobiG mProject)) * a q +
        mode4PSWFLegendreSuperdiagonal
            (mode4JacobiG mProject) q * a (q + 1) = 0)
    (x : ℝ) (hx : x ∈ Set.Ioo (-1 : ℝ) 1) :
    -(1 - x ^ 2) * mode4FerrersSecondDerivativeSeries a x +
          2 * x * mode4FerrersFirstDerivativeSeries a x +
        mode4JacobiG mProject * x ^ 2 * mode4FerrersSeries a x =
      (Λ + mode4JacobiG mProject) * mode4FerrersSeries a x := by
  have hG : 0 < mode4JacobiG mProject := by
    have hm0 : 0 < mProject := lt_of_lt_of_le (by decide : 0 < 2) hm
    have hmR : (0 : ℝ) < (mProject : ℝ) := by exact_mod_cast hm0
    unfold mode4JacobiG
    positivity
  have haAbs := mode4RecurrenceRow_abs_summable_of_tail_splice
    mProject K Λ hm hK hsep hΛ a hsplice
  have ha2 :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mProject K Λ hm hK hsep hΛ a hsplice 2
  exact mode4FerrersSeries_prolateDifferentialEquation
    (mode4JacobiG mProject) (Λ + mode4JacobiG mProject)
    a hG haAbs ha2 haRec x hx

/-- A matching root now constructs a normalized recurrence row whose Ferrers
series is continuous on the closed source window, `C²` in the interior, and
satisfies the exact prolate ODE there.  Ordered-mode and Fourier-eigenvalue
identification remain separate obligations. -/
theorem exists_mode4MatchedNormalizedProlateFerrersRow_of_root
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
      ContDiffOn ℝ 2 (mode4FerrersSeries a) (Set.Ioo (-1 : ℝ) 1) ∧
      ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
        -(1 - x ^ 2) * mode4FerrersSecondDerivativeSeries a x +
              2 * x * mode4FerrersFirstDerivativeSeries a x +
            mode4JacobiG mProject * x ^ 2 * mode4FerrersSeries a x =
          (Λ + mode4JacobiG mProject) * mode4FerrersSeries a x := by
  obtain ⟨a, ha0, haAbs, haSq, haNorm, haRec, haSpliceNe, haSplice⟩ :=
    exists_mode4MatchedNormalizedAbsSummableRecurrenceRow_of_root
      mProject K Λ hm hK hsep hΛ hroot
  have hC2 := mode4FerrersSeries_contDiffOn_two_of_tail_splice
    mProject K Λ hm hK hsep hΛ a haSplice
  have hODE : ∀ x ∈ Set.Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * mode4FerrersSecondDerivativeSeries a x +
            2 * x * mode4FerrersFirstDerivativeSeries a x +
          mode4JacobiG mProject * x ^ 2 * mode4FerrersSeries a x =
        (Λ + mode4JacobiG mProject) * mode4FerrersSeries a x := by
    intro x hx
    exact mode4FerrersSeries_prolateDifferentialEquation_of_tail_splice
      mProject K Λ hm hK hsep hΛ a haSplice haRec x hx
  exact ⟨a, ha0, haAbs, haSq, haNorm, haRec, haSpliceNe,
    haSplice, hC2, hODE⟩

#print axioms mode4FerrersSeries_prolateDifferentialEquation
#print axioms mode4FerrersSeries_prolateDifferentialEquation_of_tail_splice
#print axioms exists_mode4MatchedNormalizedProlateFerrersRow_of_root
