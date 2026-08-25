import Q3.Proofs.RouteB.G6N1SelectedFerrersQuantitativeShiftedRootEnergy
import Q3.Proofs.RouteB.G6N1SelectedFerrersFactorFourPortRate

/-!
# W5 — cofinal decay of the repaired internal seam sum

The repaired W4 jump ledger pays the internal seams with

`Seam_k = ‖h_k(lambda_k)‖ * sqrt(lambda_k) * sum_{n=2}^{k+2} n^(-1/2)`,

because the packet argument inside that sum does not depend on `n`: it is
always the window edge `lambda_k`.  The sum therefore factors and only the
edge value carries the analysis.

This file supplies the quantitative edge rate and the resulting seam rate.  It
does not claim a rate for `L1_k`, `Derivative_k` or the two full-endpoint
values: those are separate components of the budget and are explicitly not
controlled by the edge rate.

SEARCH_FLAGS:
  - `./ask.sh "explicitCCMLimitH decay gaussian polynomial"`
  - `./ask.sh "selectedFerrers factorFourPortPacketRate mode chi rates"`
  - `./ask.sh "finite inverse square root sum bound"`

LEDGER:
  CLOSES:
    - W5_REPAIRED_INTERNAL_SEAM_SUM_COFINAL_DECAY
  OPENS: []
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-! ## The explicit limiting packet decays like an inverse fourth power -/

/-- The literal CCM limit packet is polynomial times a Gaussian, so on
`1 ≤ |x|` it is dominated by `33 / x ^ 4` with a wide margin.  The proof spends
only `t ^ 4 / 4! ≤ exp t`, never a numerical evaluation. -/
private theorem explicitCCMLimitH_inverse_four_decay
    {x : ℝ} (hx : 1 ≤ |x|) :
    ‖explicitCCMLimitH x‖ ≤ 33 / x ^ 4 := by
  have hpi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hx2 : (1 : ℝ) ≤ x ^ 2 := by
    nlinarith [hx, abs_nonneg x, sq_abs x]
  have hx2pos : (0 : ℝ) < x ^ 2 := lt_of_lt_of_le one_pos hx2
  have hx4pos : (0 : ℝ) < x ^ 4 := by
    have : x ^ 4 = (x ^ 2) ^ 2 := by ring
    rw [this]; positivity
  have hx8pos : (0 : ℝ) < x ^ 8 := by
    have : x ^ 8 = (x ^ 4) ^ 2 := by ring
    rw [this]; positivity
  -- Gaussian bound from the fourth Taylor term of the exponential.
  have hexp : Real.exp (-Real.pi * x ^ 2) ≤ 24 / (Real.pi ^ 4 * x ^ 8) := by
    have hterm : (Real.pi * x ^ 2) ^ 4 / (Nat.factorial 4 : ℝ) ≤
        Real.exp (Real.pi * x ^ 2) :=
      Real.pow_div_factorial_le_exp (x := Real.pi * x ^ 2)
        (by positivity) 4
    have hfac : ((Nat.factorial 4 : ℕ) : ℝ) = 24 := by norm_num [Nat.factorial]
    rw [hfac] at hterm
    have hlower : Real.pi ^ 4 * x ^ 8 / 24 ≤ Real.exp (Real.pi * x ^ 2) := by
      calc
        Real.pi ^ 4 * x ^ 8 / 24 = (Real.pi * x ^ 2) ^ 4 / 24 := by ring
        _ ≤ Real.exp (Real.pi * x ^ 2) := hterm
    have hden : (0 : ℝ) < Real.pi ^ 4 * x ^ 8 := by positivity
    rw [show (-Real.pi * x ^ 2) = -(Real.pi * x ^ 2) by ring, Real.exp_neg,
      inv_le_iff_one_le_mul₀ (Real.exp_pos _), div_mul_eq_mul_div,
      le_div_iff₀ hden]
    nlinarith [hlower, Real.exp_pos (Real.pi * x ^ 2)]
  -- The norm of the explicit packet, factored.
  have hnorm : ‖explicitCCMLimitH x‖ =
      |(Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| *
        Real.exp (-Real.pi * x ^ 2) := by
    rw [explicitCCMLimitH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (-Real.pi * (x : ℂ) ^ 2) = ((-Real.pi * x ^ 2 : ℝ) : ℂ) by
      push_cast; ring]
    exact Complex.norm_exp_ofReal _
  have hpoly : |(Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| ≤
      Real.pi ^ 2 * x ^ 4 + 2 * Real.pi * x ^ 2 := by
    have h1 : |(Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| =
        (Real.pi / 2) * x ^ 2 * |2 * Real.pi * x ^ 2 - 3| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2),
        abs_of_nonneg (le_of_lt hx2pos)]
    have h2 : |2 * Real.pi * x ^ 2 - 3| ≤ 2 * Real.pi * x ^ 2 + 3 := by
      rw [abs_le]
      constructor <;> nlinarith [hx2pos, hpi]
    rw [h1]
    have h3 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0:ℝ) ≤ Real.pi / 2 * x ^ 2)
    nlinarith [h3, hx2pos, hpi]
  have hexpNonneg : (0 : ℝ) ≤ Real.exp (-Real.pi * x ^ 2) := (Real.exp_pos _).le
  have habsNonneg : (0 : ℝ) ≤
      |(Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| := abs_nonneg _
  rw [le_div_iff₀ hx4pos, hnorm]
  have hstep :
      |(Real.pi / 2) * x ^ 2 * (2 * Real.pi * x ^ 2 - 3)| *
          Real.exp (-Real.pi * x ^ 2) * x ^ 4 ≤
        (Real.pi ^ 2 * x ^ 4 + 2 * Real.pi * x ^ 2) *
          (24 / (Real.pi ^ 4 * x ^ 8)) * x ^ 4 := by
    have hmul := mul_le_mul hpoly hexp hexpNonneg
      (by positivity : (0:ℝ) ≤ Real.pi ^ 2 * x ^ 4 + 2 * Real.pi * x ^ 2)
    exact mul_le_mul_of_nonneg_right hmul hx4pos.le
  refine le_trans hstep ?_
  have hden : (0 : ℝ) < Real.pi ^ 4 * x ^ 8 := by positivity
  have hkey :
      (Real.pi ^ 2 * x ^ 4 + 2 * Real.pi * x ^ 2) *
          (24 / (Real.pi ^ 4 * x ^ 8)) * x ^ 4 =
        (24 * (Real.pi ^ 2 * x ^ 4 + 2 * Real.pi * x ^ 2) * x ^ 4) /
          (Real.pi ^ 4 * x ^ 8) := by
    field_simp
  rw [hkey, div_le_iff₀ hden]
  have hx6 : x ^ 6 ≤ x ^ 8 := by nlinarith [hx2, hx2pos, hx4pos, hx8pos]
  have hcube : 24 * Real.pi ^ 2 + 48 * Real.pi ≤ 33 * Real.pi ^ 4 := by
    have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
    nlinarith [hpi3, hpi4, hpi, sq_nonneg (Real.pi - 3)]
  have hscale := mul_le_mul_of_nonneg_right hcube hx8pos.le
  have hsix := mul_le_mul_of_nonneg_left hx6
    (by positivity : (0:ℝ) ≤ 48 * Real.pi)
  nlinarith [hscale, hsix, hx8pos, hpi]

/-! ## The finite inverse square-root sum -/

/-- `sum_{n=1}^{N} n^(-1/2) <= 2 * sqrt N`.  Induction on `N`; the step is the
elementary `sqrt (N+1) + sqrt N <= 2 * sqrt (N+1)`. -/
private theorem inverse_sqrt_sum_Icc_one_le_two_sqrt (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt (N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hN1 : (0 : ℝ) < ((N : ℝ) + 1) := by positivity
    have hsN : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) :=
      Real.sqrt_le_sqrt (by linarith)
    have hsN1 : 0 < Real.sqrt ((N : ℝ) + 1) := Real.sqrt_pos.mpr hN1
    have hstep : (Real.sqrt ((N : ℝ) + 1))⁻¹ ≤
        2 * Real.sqrt ((N : ℝ) + 1) - 2 * Real.sqrt (N : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ hsN1] at *
      have hsq : Real.sqrt ((N : ℝ) + 1) * Real.sqrt ((N : ℝ) + 1) =
          (N : ℝ) + 1 := Real.mul_self_sqrt (le_of_lt hN1)
      have hsqN : Real.sqrt (N : ℝ) * Real.sqrt (N : ℝ) = (N : ℝ) :=
        Real.mul_self_sqrt hN
      nlinarith [hsq, hsqN, hsN, hsN1, Real.sqrt_nonneg (N : ℝ)]
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast
    calc
      ∑ n ∈ Finset.Icc 1 N, (Real.sqrt (n : ℝ))⁻¹ +
            (Real.sqrt ((N : ℝ) + 1))⁻¹ ≤
          2 * Real.sqrt (N : ℝ) +
            (2 * Real.sqrt ((N : ℝ) + 1) - 2 * Real.sqrt (N : ℝ)) := by
        exact add_le_add ih hstep
      _ = 2 * Real.sqrt ((N : ℝ) + 1) := by ring

/-- The exact seam range starts at `n = 2`, so the same bound holds a
fortiori. -/
private theorem finite_inverse_sqrt_sum_le_two_sqrt (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, (Real.sqrt (n : ℝ))⁻¹ ≤ 2 * Real.sqrt (N : ℝ) := by
  refine le_trans ?_ (inverse_sqrt_sum_Icc_one_le_two_sqrt N)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨by omega, hn.2⟩
  · intro n _ _
    positivity

/-! ## The packet edge rate -/

/-- The F72.6 packet rate plus the explicit target decay give the edge rate.
The window edge is the one point where the production packet need not vanish,
and it is exactly the argument the repaired seam sum pays for. -/
private theorem selectedFerrersLemma73SourcePacket_edge_rate
    {C : ℝ} (hC : 0 ≤ C)
    (hrate : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) x -
          (4 : ℂ) * explicitCCMLimitH x‖ ≤
            C / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourcePacket k (selectedFerrersPaperLambda k)‖ ≤
        (C + 132) / (selectedFerrersPaperLambda k) ^ 2 := by
  filter_upwards [hrate] with k hk
  have hlam : selectedFerrersPaperLambda k = Real.sqrt ((k + 2 : ℕ) : ℝ) :=
    rfl
  have hone : (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
    rw [hlam]
    have : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast this
    simpa using Real.one_le_sqrt.mpr this
  have hpos : (0 : ℝ) < selectedFerrersPaperLambda k := lt_of_lt_of_le one_pos hone
  have hsq : (1 : ℝ) ≤ (selectedFerrersPaperLambda k) ^ 2 := by nlinarith [hone, hpos]
  have hsqpos : (0 : ℝ) < (selectedFerrersPaperLambda k) ^ 2 := by positivity
  have hmem : selectedFerrersPaperLambda k ∈
      Set.Icc (-(selectedFerrersPaperLambda k)) (selectedFerrersPaperLambda k) :=
    ⟨by linarith, le_rfl⟩
  have hdiff := hk _ hmem
  -- The explicit limit packet decays like an inverse fourth power at the edge.
  have habs : (1 : ℝ) ≤ |selectedFerrersPaperLambda k| := by
    rwa [abs_of_pos hpos]
  have htarget := explicitCCMLimitH_inverse_four_decay habs
  have hfour : ‖(4 : ℂ) * explicitCCMLimitH (selectedFerrersPaperLambda k)‖ ≤
      132 / (selectedFerrersPaperLambda k) ^ 4 := by
    rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by
      rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_real]
      norm_num]
    have := mul_le_mul_of_nonneg_left htarget (by norm_num : (0:ℝ) ≤ 4)
    calc
      4 * ‖explicitCCMLimitH (selectedFerrersPaperLambda k)‖ ≤
          4 * (33 / (selectedFerrersPaperLambda k) ^ 4) := this
      _ = 132 / (selectedFerrersPaperLambda k) ^ 4 := by ring
  -- Fourth power dominates the square once the edge is past one.
  have hpow : 132 / (selectedFerrersPaperLambda k) ^ 4 ≤
      132 / (selectedFerrersPaperLambda k) ^ 2 := by
    apply div_le_div_of_nonneg_left (by norm_num) hsqpos
    nlinarith [hsq, hsqpos]
  have hpacket : selectedFerrersLemma73SourcePacket k
      (selectedFerrersPaperLambda k) =
      selectedFerrersLemma73SourceScale k *
        prolateCombination (selectedFerrersPreAnchorPair k)
          (selectedFerrersPaperLambda k) := rfl
  calc
    ‖selectedFerrersLemma73SourcePacket k (selectedFerrersPaperLambda k)‖
        ≤ ‖selectedFerrersLemma73SourceScale k *
              prolateCombination (selectedFerrersPreAnchorPair k)
                (selectedFerrersPaperLambda k) -
            (4 : ℂ) * explicitCCMLimitH (selectedFerrersPaperLambda k)‖ +
          ‖(4 : ℂ) * explicitCCMLimitH (selectedFerrersPaperLambda k)‖ := by
      rw [hpacket]
      have hadd := norm_add_le
        (selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k)
              (selectedFerrersPaperLambda k) -
          (4 : ℂ) * explicitCCMLimitH (selectedFerrersPaperLambda k))
        ((4 : ℂ) * explicitCCMLimitH (selectedFerrersPaperLambda k))
      simpa using hadd
    _ ≤ C / (selectedFerrersPaperLambda k) ^ 2 +
          132 / (selectedFerrersPaperLambda k) ^ 2 :=
      add_le_add hdiff (le_trans hfour hpow)
    _ = (C + 132) / (selectedFerrersPaperLambda k) ^ 2 := by ring

/-! ## The repaired internal seam sum decays -/

/-- The internal seam sum of the repaired W4 jump ledger tends to zero along
the family.  The packet argument inside the sum is always the window edge, so
the sum factors into the edge value times an explicit scalar, and the edge rate
beats the growth of that scalar.

This closes only the seam component.  The `L1` mass, the derivative budget and
the two full-endpoint values are separate components of `C_k` and are not
controlled here. -/
theorem selectedFerrersAbelLogInternalSeamSum_rate_of_modeAndChiRates
    {C : ℝ} (hC : 0 ≤ C)
    (hrate : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) x -
          (4 : ℂ) * explicitCCMLimitH x‖ ≤
            C / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ∑ n ∈ Finset.Icc (2 : ℕ) (k + 2),
          ‖((Real.sqrt (selectedFerrersPaperLambda k / (n : ℝ)) : ℝ) : ℂ) *
            selectedFerrersLemma73SourcePacket k
              (selectedFerrersPaperLambda k)‖ ≤
        2 * (C + 132) / Real.sqrt (selectedFerrersPaperLambda k) := by
  filter_upwards [selectedFerrersLemma73SourcePacket_edge_rate hC hrate] with k hedge
  set lam := selectedFerrersPaperLambda k with hlamdef
  have hlam : lam = Real.sqrt ((k + 2 : ℕ) : ℝ) := rfl
  have hone : (1 : ℝ) ≤ lam := by
    rw [hlam]
    have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast this
    simpa using Real.one_le_sqrt.mpr h1
  have hpos : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hone
  have hsqrtlam : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hpos
  have hlamsq : (0 : ℝ) < lam ^ 2 := by positivity
  -- Each summand splits into the fixed edge value and an explicit scalar.
  have hsplit : ∀ n ∈ Finset.Icc (2 : ℕ) (k + 2),
      ‖((Real.sqrt (lam / (n : ℝ)) : ℝ) : ℂ) *
          selectedFerrersLemma73SourcePacket k lam‖ =
        Real.sqrt lam * (Real.sqrt (n : ℝ))⁻¹ *
          ‖selectedFerrersLemma73SourcePacket k lam‖ := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      have : 0 < n := by omega
      exact_mod_cast this
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _),
      Real.sqrt_div (le_of_lt hpos) (n : ℝ), div_eq_mul_inv]
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_mul, ← Finset.mul_sum]
  -- The scalar factor is bounded by the finite inverse square-root sum.
  have hsum := finite_inverse_sqrt_sum_le_two_sqrt (k + 2)
  have hsumcast : ∑ n ∈ Finset.Icc (2 : ℕ) (k + 2), (Real.sqrt (n : ℝ))⁻¹ ≤
      2 * lam := by
    rw [hlam]
    exact hsum
  have hpacketNonneg : (0 : ℝ) ≤ ‖selectedFerrersLemma73SourcePacket k lam‖ :=
    norm_nonneg _
  calc
    Real.sqrt lam * (∑ n ∈ Finset.Icc (2 : ℕ) (k + 2), (Real.sqrt (n : ℝ))⁻¹) *
          ‖selectedFerrersLemma73SourcePacket k lam‖ ≤
        Real.sqrt lam * (2 * lam) * ((C + 132) / lam ^ 2) := by
      apply mul_le_mul _ hedge hpacketNonneg
      · positivity
      · exact mul_le_mul_of_nonneg_left hsumcast (Real.sqrt_nonneg _)
    _ = 2 * (C + 132) / Real.sqrt lam := by
      have hll : Real.sqrt lam * Real.sqrt lam = lam :=
        Real.mul_self_sqrt (le_of_lt hpos)
      field_simp
      nlinarith [hll, hsqrtlam, hpos]

#print axioms selectedFerrersAbelLogInternalSeamSum_rate_of_modeAndChiRates

end Q3.RouteB.D0Pstar
