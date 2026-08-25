import Q3.Proofs.RouteB.G6N1SelectedFerrersW5L1MassRate

/-!
# W5 — the two full-endpoint values decay

`Jump_k` pays `‖rep 0‖` and `‖rep L‖` as separate summands.  Both are
pointwise evaluations of the Abel limit at the window edges `u = 1 / lam` and
`u = lam`; by the committed inversion the two starred targets coincide, so a
single right-edge Gaussian bound pays them both.

The analytic bricks of the `L¹` node are private in its file, and its frozen
contract is one public theorem, so the three needed here are reconstructed
locally — the same pattern the W4 node used for the W2 chain.

SEARCH_FLAGS:
  - `./ask.sh "full endpoint value rate abel limit window edge"`

LEDGER:
  CLOSES:
    - W5_FULL_ENDPOINT_VALUE_RATE
  OPENS: []
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-! ## Local reconstruction of the target bounds -/

private theorem w5e_target_le_half_gaussian (y : ℝ) :
    ‖explicitCCMLimitH y‖ ≤ 12 * Real.exp (-(Real.pi * y ^ 2) / 2) := by
  have hpi := Real.pi_pos
  set t : ℝ := y ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hnorm : ‖explicitCCMLimitH y‖ =
      |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| *
        Real.exp (-Real.pi * t) := by
    rw [explicitCCMLimitH, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    congr 1
    rw [show (-Real.pi * (y : ℂ) ^ 2) = ((-Real.pi * t : ℝ) : ℂ) by
      rw [ht]; push_cast; ring]
    exact Complex.norm_exp_ofReal _
  have hpoly : |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| ≤
      Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t := by
    have h1 : |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| =
        (Real.pi / 2) * t * |2 * Real.pi * t - 3| := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.pi / 2),
        abs_of_nonneg ht0]
    have h2 : |2 * Real.pi * t - 3| ≤ 2 * Real.pi * t + 3 := by
      rw [abs_le]
      constructor <;> nlinarith [ht0, hpi]
    rw [h1]
    have h3 := mul_le_mul_of_nonneg_left h2
      (by positivity : (0:ℝ) ≤ Real.pi / 2 * t)
    nlinarith [ht0, hpi, h3]
  have hsplit : Real.exp (-Real.pi * t) =
      Real.exp (-(Real.pi * t) / 2) * Real.exp (-(Real.pi * t) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hhalf : (Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t) *
      Real.exp (-(Real.pi * t) / 2) ≤ 12 := by
    have hquad : (Real.pi * t / 2) ^ 2 / 2 ≤ Real.exp (Real.pi * t / 2) := by
      have h := Real.pow_div_factorial_le_exp (x := Real.pi * t / 2)
        (by positivity) 2
      simpa [Nat.factorial] using h
    have hlin : Real.pi * t / 2 ≤ Real.exp (Real.pi * t / 2) := by
      have h := Real.pow_div_factorial_le_exp (x := Real.pi * t / 2)
        (by positivity) 1
      simpa [Nat.factorial] using h
    have hexppos : (0 : ℝ) < Real.exp (Real.pi * t / 2) := Real.exp_pos _
    have hinv : Real.exp (-(Real.pi * t) / 2) =
        (Real.exp (Real.pi * t / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hinv, mul_inv_le_iff₀ hexppos]
    nlinarith [hquad, hlin, hexppos, ht0, hpi]
  rw [hnorm, hsplit, ← mul_assoc]
  have hexpNonneg : (0 : ℝ) ≤ Real.exp (-(Real.pi * t) / 2) := (Real.exp_pos _).le
  have hstep := mul_le_mul_of_nonneg_right hpoly hexpNonneg
  calc
    |(Real.pi / 2) * t * (2 * Real.pi * t - 3)| *
          Real.exp (-(Real.pi * t) / 2) *
        Real.exp (-(Real.pi * t) / 2) ≤
        ((Real.pi ^ 2 * t ^ 2 + 2 * Real.pi * t) *
            Real.exp (-(Real.pi * t) / 2)) *
          Real.exp (-(Real.pi * t) / 2) :=
      mul_le_mul_of_nonneg_right hstep hexpNonneg
    _ ≤ 12 * Real.exp (-(Real.pi * t) / 2) :=
      mul_le_mul_of_nonneg_right hhalf hexpNonneg
    _ = 12 * Real.exp (-(Real.pi * y ^ 2) / 2) := by rw [ht]

private theorem w5e_gaussian_series_le_geometric
    {u : ℝ} (hu : 1 ≤ u) (n : ℕ) (hn : 1 ≤ n) :
    Real.exp (-(Real.pi * ((n : ℝ) * u) ^ 2) / 2) ≤
      Real.exp (-(Real.pi * u ^ 2) / 2) * (2 : ℝ)⁻¹ ^ (n - 1) := by
  have hpi := Real.pi_pos
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hgap : (Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2 ≥ ((n : ℝ) - 1) := by
    have hu2 : (1 : ℝ) ≤ u ^ 2 := by nlinarith
    have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
    have hsq : (0 : ℝ) ≤ (n : ℝ) ^ 2 - 1 := by nlinarith [hn1]
    have htwo : (2 : ℝ) * ((n : ℝ) - 1) ≤ (n : ℝ) ^ 2 - 1 := by
      nlinarith [sq_nonneg ((n : ℝ) - 1)]
    have hthree : (3 : ℝ) ≤ Real.pi * u ^ 2 := by nlinarith [hpi3, hu2, hpi]
    have hchain : (3 : ℝ) * ((n : ℝ) ^ 2 - 1) ≤
        Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hthree hsq
    linarith [hchain, htwo]
  have hsplit : -(Real.pi * ((n : ℝ) * u) ^ 2) / 2 =
      -(Real.pi * u ^ 2) / 2 - (Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2 := by
    ring
  rw [hsplit, Real.exp_sub]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  have hstep1 : Real.exp (-((Real.pi * u ^ 2 * ((n : ℝ) ^ 2 - 1)) / 2)) ≤
      Real.exp (-((n : ℝ) - 1)) := by
    apply Real.exp_le_exp.mpr
    linarith [hgap]
  refine le_trans (by simpa [Real.exp_neg] using hstep1) ?_
  have hgoal : Real.exp (1 - (n : ℝ)) = (Real.exp ((n : ℝ) - 1))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hgoal, show ((2 : ℝ)⁻¹ ^ (n - 1)) = ((2 : ℝ) ^ (n - 1))⁻¹ by
    rw [inv_pow]]
  rw [inv_le_inv₀ (Real.exp_pos _) (by positivity)]
  have hcast : ((n : ℝ) - 1) = ((n - 1 : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ n := hn
    push_cast [Nat.cast_sub this]
    ring
  rw [hcast, ← Real.exp_one_rpow ((n - 1 : ℕ) : ℝ), Real.rpow_natCast]
  apply pow_le_pow_left₀ (by norm_num)
  linarith [Real.add_one_le_exp (1 : ℝ)]

private theorem w5e_E_star_norm_le_of_one_le
    {u : ℝ} (hu : 1 ≤ u) :
    ‖E_star explicitCCMLimitH u‖ ≤
      24 * Real.sqrt u * Real.exp (-(Real.pi * u ^ 2) / 2) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le one_pos hu
  have hgeo : Summable (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hinj : Function.Injective (fun n : ℕ+ => ((n : ℕ) - 1)) := by
    intro a b hab
    have ha := a.pos
    have hb := b.pos
    have hab' : (a : ℕ) - 1 = (b : ℕ) - 1 := hab
    exact PNat.coe_injective (by omega)
  have hnorm_summable : Summable
      (fun n : ℕ+ => ‖explicitCCMLimitH ((n : ℕ) * u)‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      (fun n => ?_)
      (f := fun n : ℕ+ =>
        12 * Real.exp (-(Real.pi * u ^ 2) / 2) * (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1))
    · apply Summable.mul_left
      simpa using hgeo.comp_injective hinj
    · calc
        ‖explicitCCMLimitH ((n : ℕ) * u)‖ ≤
            12 * Real.exp (-(Real.pi * ((n : ℕ) * u) ^ 2) / 2) :=
          w5e_target_le_half_gaussian _
        _ ≤ 12 * (Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1)) := by
          have := w5e_gaussian_series_le_geometric hu (n : ℕ) n.pos
          nlinarith [this, Real.exp_pos (-(Real.pi * ((n:ℕ) * u) ^ 2) / 2)]
        _ = 12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by ring
  rw [E_star, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have htsum : ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
      24 * Real.exp (-(Real.pi * u ^ 2) / 2) := by
    calc
      ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
          ∑' n : ℕ+, ‖explicitCCMLimitH ((n : ℕ) * u)‖ :=
        norm_tsum_le_tsum_norm hnorm_summable
      _ ≤ ∑' n : ℕ+,
            12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
              (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by
        apply hnorm_summable.tsum_le_tsum _ ?_
        · intro n
          calc
            ‖explicitCCMLimitH ((n : ℕ) * u)‖ ≤
                12 * Real.exp (-(Real.pi * ((n : ℕ) * u) ^ 2) / 2) :=
              w5e_target_le_half_gaussian _
            _ ≤ 12 * Real.exp (-(Real.pi * u ^ 2) / 2) *
                  (2 : ℝ)⁻¹ ^ ((n : ℕ) - 1) := by
              have := w5e_gaussian_series_le_geometric hu (n : ℕ) n.pos
              nlinarith [this,
                Real.exp_pos (-(Real.pi * ((n:ℕ) * u) ^ 2) / 2)]
        · apply Summable.mul_left
          simpa using hgeo.comp_injective hinj
      _ ≤ 24 * Real.exp (-(Real.pi * u ^ 2) / 2) := by
        rw [tsum_mul_left]
        have hval : ∑' n : ℕ+, ((2 : ℝ)⁻¹) ^ ((n : ℕ) - 1) = 2 := by
          have hfun : (fun n : ℕ+ => ((2 : ℝ)⁻¹) ^ ((n : ℕ) - 1)) =
              (fun n : ℕ+ =>
                (fun m : ℕ => ((2 : ℝ)⁻¹) ^ m) (Equiv.pnatEquivNat n)) := by
            funext n
            simp [Equiv.pnatEquivNat, PNat.natPred]
          rw [hfun, Equiv.pnatEquivNat.tsum_eq
            (f := fun m : ℕ => ((2 : ℝ)⁻¹) ^ m), tsum_geometric_inv_two]
        rw [hval]
        nlinarith [Real.exp_pos (-(Real.pi * u ^ 2) / 2)]
  calc
    Real.sqrt u * ‖∑' n : ℕ+, explicitCCMLimitH ((n : ℕ) * u)‖ ≤
        Real.sqrt u * (24 * Real.exp (-(Real.pi * u ^ 2) / 2)) :=
      mul_le_mul_of_nonneg_left htsum (Real.sqrt_nonneg _)
    _ = 24 * Real.sqrt u * Real.exp (-(Real.pi * u ^ 2) / 2) := by ring

/-! ## Local reconstruction of the error, center and decomposition bounds -/

private theorem w5e_fullEStarError_window_bound
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ u ∈ sourceWindow (selectedFerrersPaperLambda k),
          ‖selectedFerrersFullEStarError k u‖ ≤
            C / (selectedFerrersPaperLambda k * Real.sqrt u) := by
  obtain ⟨C1, hC1, hmain⟩ :=
    selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨C2, hC2, htail⟩ := selectedFerrersExplicitTargetTail_bound
  refine ⟨C1 + C2, by linarith, ?_⟩
  filter_upwards [hmain, htail] with k hk1 hk2
  intro u hu
  rw [selectedFerrersFullEStarError_eq_main_sub_targetTail k hu]
  calc
    ‖selectedFerrersEStarWindowMainError k u -
        selectedFerrersExplicitTargetTail k u‖ ≤
        ‖selectedFerrersEStarWindowMainError k u‖ +
          ‖selectedFerrersExplicitTargetTail k u‖ := norm_sub_le _ _
    _ ≤ C1 / (selectedFerrersPaperLambda k * Real.sqrt u) +
          C2 / (selectedFerrersPaperLambda k * Real.sqrt u) :=
      add_le_add (hk1 u hu) (hk2 u hu)
    _ = (C1 + C2) / (selectedFerrersPaperLambda k * Real.sqrt u) := by
      rw [div_add_div_same]

private theorem w5e_center_bound
    {C : ℝ}
    (hrate : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) x -
          (4 : ℂ) * explicitCCMLimitH x‖ ≤
            C / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourcePacket k 0‖ ≤
        C / (selectedFerrersPaperLambda k) ^ 2 := by
  filter_upwards [hrate] with k hk
  have hlam : 0 ≤ selectedFerrersPaperLambda k := Real.sqrt_nonneg _
  have hmem : (0 : ℝ) ∈ Set.Icc (-(selectedFerrersPaperLambda k))
      (selectedFerrersPaperLambda k) := ⟨by linarith, hlam⟩
  have h := hk 0 hmem
  have hH0 : explicitCCMLimitH 0 = 0 := by
    rw [explicitCCMLimitH]
    norm_num
  rw [hH0, mul_zero, sub_zero] at h
  exact h

private theorem w5e_abelLimit_decomposition (k : ℕ) (u : ℝ) :
    selectedFerrersAbelLimit k u =
      (4 : ℂ) * E_star explicitCCMLimitH u +
        selectedFerrersFullEStarError k u +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (Real.sqrt u : ℂ) := by
  rw [selectedFerrersAbelLimit, selectedFerrersFullEStarError]
  have hlin : E_star (selectedFerrersLemma73SourcePacket k) u =
      selectedFerrersLemma73SourceScale k *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u := by
    rw [E_star, E_star]
    have hfun : (fun n : ℕ+ =>
        selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u)) =
        (fun n : ℕ+ =>
          selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k)
              (((n : ℕ) : ℝ) * u)) := by
      funext n
      rfl
    rw [hfun, tsum_mul_left]
    ring
  rw [hlin]
  ring

/-! ## The public endpoint rate -/

/-- Both full-endpoint values of the additive-log representative decay like
`1 / sqrt lambda`, conditional on the F72.6 mode and chi rate inputs.  The
starred target coincides at the two edges by the committed inversion, so one
right-edge Gaussian bound pays both; the error and shadow bounds are direct
evaluations. -/
theorem selectedFerrersAbelLogEndpointValues_rate_of_modeAndChiRates
    (C0 C4 Cχ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hmode :
      ∀ᶠ k in Filter.atTop,
        ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 x -
            ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C0 / (selectedFerrersPaperLambda k) ^ 2 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 x -
            ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
              C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ :
      ∀ᶠ k in Filter.atTop,
        |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
          |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
            Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ᶠ k in Filter.atTop,
        ‖selectedFerrersAbelLogRepresentative k 0‖ ≤
            A / Real.sqrt (selectedFerrersPaperLambda k) ∧
          ‖selectedFerrersAbelLogRepresentative k
              (L_m (selectedFerrersPreAnchorIndex k))‖ ≤
            A / Real.sqrt (selectedFerrersPaperLambda k) := by
  obtain ⟨C1, hC1, herr⟩ := w5e_fullEStarError_window_bound
    C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨C2, hC2, hrate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hcenter := w5e_center_bound hrate
  refine ⟨96 + C1 + C2, by linarith, ?_⟩
  filter_upwards [herr, hcenter] with k herrk hcenterk
  set lam : ℝ := selectedFerrersPaperLambda k with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef, selectedFerrersPaperLambda]
    have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
      exact_mod_cast this
    simpa using Real.one_le_sqrt.mpr h1
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam1
  have hs0 : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
  have hs1 : (1 : ℝ) ≤ Real.sqrt lam := by
    simpa using Real.one_le_sqrt.mpr hlam1
  have hlameq : lambda_m (selectedFerrersPreAnchorIndex k) = lam :=
    (selectedFerrersPaperLambda_eq_lambda_m k).symm
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hexpL : Real.exp L = lam * lam := by
    have hnat : Real.exp L = ((k + 2 : ℕ) : ℝ) := by
      rw [hLdef, show L_m (selectedFerrersPreAnchorIndex k) =
        Real.log ((k + 2 : ℕ) : ℝ) from rfl,
        Real.exp_log (by positivity)]
    have hsq : lam * lam = ((k + 2 : ℕ) : ℝ) := by
      rw [hlamdef, selectedFerrersPaperLambda]
      exact Real.mul_self_sqrt (by positivity)
    rw [hnat, hsq]
  -- the shared target bound: E_star H at lam pays both edges via inversion
  have htargetlam : ‖E_star explicitCCMLimitH lam‖ ≤ 24 / Real.sqrt lam := by
    refine le_trans (w5e_E_star_norm_le_of_one_le hlam1) ?_
    -- 24 sqrt(lam) exp(-(pi lam^2)/2) <= 24 / sqrt(lam)
    rw [div_eq_mul_inv]
    have hgauss : Real.exp (-(Real.pi * lam ^ 2) / 2) ≤ lam⁻¹ := by
      have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
      have hlin : Real.pi * lam ^ 2 / 2 ≤
          Real.exp (Real.pi * lam ^ 2 / 2) := by
        have h := Real.add_one_le_exp (Real.pi * lam ^ 2 / 2)
        linarith
      have hexppos : (0 : ℝ) < Real.exp (Real.pi * lam ^ 2 / 2) :=
        Real.exp_pos _
      have hinvform : Real.exp (-(Real.pi * lam ^ 2) / 2) =
          (Real.exp (Real.pi * lam ^ 2 / 2))⁻¹ := by
        rw [← Real.exp_neg]
        congr 1
        ring
      rw [hinvform, inv_le_inv₀ hexppos hlam0]
      calc
        lam ≤ Real.pi * lam ^ 2 / 2 := by nlinarith [hlam1, hpi3]
        _ ≤ Real.exp (Real.pi * lam ^ 2 / 2) := hlin
    calc
      24 * Real.sqrt lam * Real.exp (-(Real.pi * lam ^ 2) / 2) ≤
          24 * Real.sqrt lam * lam⁻¹ :=
        mul_le_mul_of_nonneg_left hgauss (by positivity)
      _ ≤ 24 * (Real.sqrt lam)⁻¹ := by
        have hkey : Real.sqrt lam * lam⁻¹ ≤ (Real.sqrt lam)⁻¹ := by
          have hmul := Real.mul_self_sqrt hlam0.le
          have hne : lam ≠ 0 := ne_of_gt hlam0
          have hsne : Real.sqrt lam ≠ 0 := ne_of_gt hs0
          have heq : Real.sqrt lam * lam⁻¹ = (Real.sqrt lam)⁻¹ := by
            field_simp
            linarith [hmul]
          exact le_of_eq heq
        calc
          24 * Real.sqrt lam * lam⁻¹ = 24 * (Real.sqrt lam * lam⁻¹) := by
            ring
          _ ≤ 24 * (Real.sqrt lam)⁻¹ :=
            mul_le_mul_of_nonneg_left hkey (by norm_num)
  have htargetinv : ‖E_star explicitCCMLimitH lam⁻¹‖ ≤ 24 / Real.sqrt lam := by
    rw [E_star_explicitCCMLimitH_inv lam hlam0]
    exact htargetlam
  -- generic edge assembly
  have hedge : ∀ u : ℝ, 0 < u →
      u ∈ sourceWindow lam →
      ‖E_star explicitCCMLimitH u‖ ≤ 24 / Real.sqrt lam →
      Real.sqrt u ≤ Real.sqrt lam →
      ‖selectedFerrersAbelLimit k u‖ ≤ (96 + C1 + C2) / Real.sqrt lam := by
    intro u hu0 humem htarget hsqrtu
    rw [w5e_abelLimit_decomposition]
    refine le_trans (norm_add_le _ _) ?_
    refine le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_
    have ht1 : ‖(4 : ℂ) * E_star explicitCCMLimitH u‖ ≤
        96 / Real.sqrt lam := by
      rw [norm_mul, show ‖(4 : ℂ)‖ = 4 by
        rw [show (4 : ℂ) = ((4 : ℝ) : ℂ) by norm_num, Complex.norm_real]
        norm_num]
      calc
        4 * ‖E_star explicitCCMLimitH u‖ ≤ 4 * (24 / Real.sqrt lam) :=
          mul_le_mul_of_nonneg_left htarget (by norm_num)
        _ = 96 / Real.sqrt lam := by ring
    have ht2 : ‖selectedFerrersFullEStarError k u‖ ≤ C1 / Real.sqrt lam := by
      refine le_trans (herrk u humem) ?_
      apply div_le_div_of_nonneg_left hC1
        (by positivity)
      -- sqrt lam <= lam * sqrt u since sqrt u >= 1/sqrt lam
      have hlow : (Real.sqrt lam)⁻¹ ≤ Real.sqrt u := by
        have h1 := humem.1
        have := Real.sqrt_le_sqrt h1
        rwa [Real.sqrt_inv] at this
      calc
        Real.sqrt lam = lam * (Real.sqrt lam)⁻¹ := by
          have hmul := Real.mul_self_sqrt hlam0.le
          have hne : lam ≠ 0 := ne_of_gt hlam0
          have hsne : Real.sqrt lam ≠ 0 := ne_of_gt hs0
          field_simp
          linarith [hmul]
        _ ≤ lam * Real.sqrt u :=
          mul_le_mul_of_nonneg_left hlow hlam0.le
    have ht3 : ‖(1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        (Real.sqrt u : ℂ)‖ ≤ C2 / Real.sqrt lam := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _),
        show ‖(1 / 2 : ℂ)‖ = 1 / 2 by
          rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
            Complex.norm_real]
          norm_num]
      have hc := hcenterk
      calc
        1 / 2 * ‖selectedFerrersLemma73SourcePacket k 0‖ * Real.sqrt u ≤
            1 / 2 * (C2 / lam ^ 2) * Real.sqrt lam := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hc (by norm_num)
          · exact hsqrtu
          · exact Real.sqrt_nonneg _
          · positivity
        _ ≤ C2 / Real.sqrt lam := by
          have hs2 : Real.sqrt lam * Real.sqrt lam = lam :=
            Real.mul_self_sqrt hlam0.le
          rw [le_div_iff₀ hs0]
          have heq : 1 / 2 * (C2 / lam ^ 2) * lam = C2 / (2 * lam) := by
            field_simp
          calc
            1 / 2 * (C2 / lam ^ 2) * Real.sqrt lam * Real.sqrt lam =
                1 / 2 * (C2 / lam ^ 2) * lam := by
              rw [mul_assoc, hs2]
            _ = C2 / (2 * lam) := heq
            _ ≤ C2 := div_le_self hC2 (by nlinarith [hlam1])
    calc
      ‖(4 : ℂ) * E_star explicitCCMLimitH u‖ +
          ‖selectedFerrersFullEStarError k u‖ +
          ‖(1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
            (Real.sqrt u : ℂ)‖ ≤
          96 / Real.sqrt lam + C1 / Real.sqrt lam + C2 / Real.sqrt lam :=
        add_le_add (add_le_add ht1 ht2) ht3
      _ = (96 + C1 + C2) / Real.sqrt lam := by
        rw [div_add_div_same, div_add_div_same]
  -- specialize to the two edges
  have hlowmem : lam⁻¹ ∈ sourceWindow lam :=
    ⟨le_refl _, by
      rw [inv_le_iff_one_le_mul₀ hlam0]
      nlinarith [hlam1]⟩
  have hhighmem : lam ∈ sourceWindow lam :=
    ⟨by
      rw [inv_le_iff_one_le_mul₀' hlam0]
      nlinarith [hlam1], le_refl _⟩
  constructor
  · -- x = 0: u = exp 0 / lam = 1/lam
    have hrep : selectedFerrersAbelLogRepresentative k 0 =
        selectedFerrersAbelLimit k lam⁻¹ := by
      rw [selectedFerrersAbelLogRepresentative, hlameq, Real.exp_zero,
        one_div]
    rw [hrep]
    apply hedge lam⁻¹ (by positivity) hlowmem htargetinv
    calc
      Real.sqrt lam⁻¹ = (Real.sqrt lam)⁻¹ := Real.sqrt_inv lam
      _ ≤ 1 := by
        rw [inv_le_one_iff₀]
        right
        exact hs1
      _ ≤ Real.sqrt lam := hs1
  · -- x = L: u = exp L / lam = lam
    have hrep : selectedFerrersAbelLogRepresentative k L =
        selectedFerrersAbelLimit k lam := by
      rw [selectedFerrersAbelLogRepresentative, hlameq]
      congr 1
      rw [hexpL, mul_div_assoc, div_self (ne_of_gt hlam0), mul_one]
    rw [hrep]
    exact hedge lam hlam0 hhighmem htargetlam le_rfl

#print axioms selectedFerrersAbelLogEndpointValues_rate_of_modeAndChiRates

end Q3.RouteB.D0Pstar
