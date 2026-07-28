import Mathlib

open scoped BigOperators NNReal
open Set MeasureTheory

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.sqrt u * ∑' n : ℕ+, h ((n : ℝ) * u)

/-- A right-endpoint sum of a function supported on `[0,b]` is a finite sum.
The endpoint `b` is retained when it is hit exactly. -/
theorem riemannBoundaryCellBridge_finiteReduction
    (h : ℝ → ℂ) (b u : ℝ) (hu : 0 < u)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0) :
    ∑' n : ℕ+, h ((n : ℝ) * u) =
      ∑ n ∈ Finset.Icc 1 (Nat.ceil (b / u)), h ((n : ℝ) * u) := by
    by_cases hb : 0 < b
    · -- b > 0 case: show tsum equals finite sum
      -- First, show that for n > ceil(b/u), h(n*u) = 0
      have hlarge : ∀ n : ℕ+, n > Nat.ceil (b / u) → h ((n : ℝ) * u) = 0 := by
        intro n hn
        apply hsupp
        intro hv
        simp at hv
        have h1 : (n : ℝ) * u ≤ b := hv.2
        have h2 : (n : ℕ) > Nat.ceil (b / u) := hn
        have h3 : (n : ℝ) * u > b := by
          have hn_bound : (n : ℝ) ≥ Nat.ceil (b / u) + 1 := by exact_mod_cast h2
          have hceil := Nat.le_ceil (b / u)
          have : (n : ℝ) * u ≥ (Nat.ceil (b / u) + 1) * u := by nlinarith
          have : (Nat.ceil (b / u) + 1) * u > (b / u) * u := by nlinarith
          linarith [mul_div_cancel₀ b (ne_of_gt hu)]
        nlinarith
      -- Create a finset over ℕ+ corresponding to Icc 1 (Nat.ceil(b/u))
      have hceil_pos : 0 < Nat.ceil (b / u) := Nat.ceil_pos.mpr (by positivity)
      let m : ℕ+ := ⟨Nat.ceil (b / u), hceil_pos⟩
      let S : Finset ℕ+ := Finset.Icc 1 m
      -- Apply tsum_eq_sum
      have h_sum_eq : ∑' n : ℕ+, h ((n : ℝ) * u) = ∑ n ∈ S, h ((n : ℝ) * u) := by
        apply tsum_eq_sum
        intro n hn
        simp only [S, Finset.mem_Icc, not_and, not_le] at hn
        have h1 : 1 ≤ (n : ℕ) := PNat.one_le n
        have h2 : (m : ℕ+) < n := hn h1
        exact hlarge n h2
      -- Convert the sum
      rw [h_sum_eq]
      -- Now we need to show ∑ n ∈ S, h ((n : ℝ) * u) = ∑ n ∈ Finset.Icc 1 (Nat.ceil(b/u)), h ((n : ℝ) * u)
      simp only [S]
      refine Finset.sum_bij' (fun n _ => n.val) (fun n hn => ⟨n, Nat.lt_of_lt_of_le zero_lt_one (Finset.mem_Icc.mp hn |>.1)⟩) ?_ ?_ ?_ ?_ ?_
      · intro a ha
        simp only [Finset.mem_Icc] at ha ⊢
        exact ⟨ha.1, ha.2⟩
      · intro a ha
        simp only [Finset.mem_Icc, m] at ha ⊢
        exact ⟨ha.1, ha.2⟩
      · intro a _; rfl
      · intro a _; simp
      · intro a _; rfl
    · -- b ≤ 0 case: both sums are 0
      have hbu : b / u ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hb) hu.le
      have hceil : Nat.ceil (b / u) = 0 := Nat.ceil_eq_zero.mpr hbu
      simp [hceil]
      have hall_zero : ∀ n : ℕ+, h ((n : ℝ) * u) = 0 := by
        intro n
        apply hsupp
        intro hv
        simp at hv
        nlinarith [hv.1, hv.2, show (n : ℝ) ≥ 1 by exact Nat.one_le_cast.mpr n.pos]
      simp [hall_zero]

/-- A measurable function with the stated compact support and one-sided Lipschitz bound is
Bochner integrable, despite its possible jump at `b`. -/
lemma riemannBoundaryCellBridge_integrable
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmeas : Measurable h) : Integrable h := by
  have hi : IntegrableOn h (Set.Icc (0 : ℝ) b) := by
    apply IntegrableOn.of_bound measure_Icc_lt_top hmeas.aestronglyMeasurable.restrict
      (max ‖h b‖ ((K : ℝ) * b + ‖h 0‖))
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with x hx
    by_cases he : x = b
    · simp [he]
    · have hxo : x ∈ Set.Ico (0 : ℝ) b := ⟨hx.1, lt_of_le_of_ne hx.2 he⟩
      have H := hlip.norm_sub_le hxo ⟨le_rfl, hb⟩
      calc
        ‖h x‖ ≤ ‖h x - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add _ _
        _ ≤ (K : ℝ) * ‖x - 0‖ + ‖h 0‖ := by gcongr
        _ ≤ max ‖h b‖ ((K : ℝ) * b + ‖h 0‖) := by
          apply le_max_of_le_right
          rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hx.1]
          simpa [add_comm] using add_le_add_right
            (mul_le_mul_of_nonneg_left hx.2 K.coe_nonneg) ‖h 0‖
  have heq : (Set.Icc (0 : ℝ) b).indicator h = h := by
    funext x
    by_cases hx : x ∈ Set.Icc (0 : ℝ) b
    · simp [hx]
    · simp [hx, hsupp x hx]
  rw [← heq]
  exact hi.integrable_indicator measurableSet_Icc

/-- Error on one full mesh cell whose right endpoint is strictly before the support boundary. -/
lemma riemannBoundaryCellBridge_fullCell
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hint : Integrable h) (u a : ℝ) (hu : 0 < u)
    (ha : 0 ≤ a) (hab : a + u < b) :
    ‖(u : ℂ) * h (a + u) - ∫ x in a..a + u, h x‖ ≤ (K : ℝ) * u * u := by
  have hend : a + u ∈ Set.Ico (0 : ℝ) b := ⟨by linarith, hab⟩
  have hcell : ∀ x ∈ Set.uIoc a (a + u),
      ‖h (a + u) - h x‖ ≤ (K : ℝ) * u := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx' : x ∈ Set.Ico (0 : ℝ) b := ⟨by linarith [hx.1], by linarith [hx.2]⟩
    calc
      ‖h (a + u) - h x‖ ≤ (K : ℝ) * dist (a + u) x := hlip.norm_sub_le hend hx'
      _ ≤ (K : ℝ) * u := by
        rw [Real.dist_eq]
        have : |a + u - x| ≤ u := by rw [abs_of_nonneg (by linarith [hx.2])]; linarith [hx.1]
        exact mul_le_mul_of_nonneg_left this K.coe_nonneg
  have heq : (u : ℂ) * h (a + u) = ∫ _ in a..a + u, h (a + u) := by
    rw [intervalIntegral.integral_const, sub_eq_add_neg]
    norm_num
  rw [heq]
  rw [← intervalIntegral.integral_sub]
  · simpa [abs_of_pos hu, mul_assoc] using
      intervalIntegral.norm_integral_le_of_norm_le_const hcell
  · exact intervalIntegrable_const
  · exact hint.intervalIntegrable

/-- The last (possibly shortened) cell, including the discontinuous endpoint. -/
lemma riemannBoundaryCellBridge_terminalCell
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (u : ℝ) (hu : 0 < u) (N : ℕ) (hN : 0 < N)
    (hlo : ((N : ℝ) - 1) * u < b) (hhi : b ≤ (N : ℝ) * u) :
    ‖(u : ℂ) * h ((N : ℝ) * u) -
        ∫ x in ((N : ℝ) - 1) * u..b, h x‖ ≤
      u * ((‖h 0‖ + (K : ℝ) * b) + ‖h b‖) := by
  have hNone : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN.ne'
  have ha : 0 ≤ ((N : ℝ) - 1) * u := mul_nonneg (sub_nonneg.mpr hNone) hu.le
  have hbound : ∀ᵐ x, x ∈ Set.uIoc (((N : ℝ) - 1) * u) b →
      ‖h x‖ ≤ ‖h 0‖ + (K : ℝ) * b := by
    filter_upwards [(volume : Measure ℝ).ae_ne b] with x hxb hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    have hx' : x ∈ Set.Ico (0 : ℝ) b := ⟨by linarith [hx.1], lt_of_le_of_ne hx.2 hxb⟩
    have H := hlip.norm_sub_le hx' ⟨le_rfl, hb⟩
    calc
      ‖h x‖ ≤ ‖h x - h 0‖ + ‖h 0‖ := norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * ‖x - 0‖ + ‖h 0‖ := by gcongr
      _ ≤ ‖h 0‖ + (K : ℝ) * b := by
        rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hx'.1]
        nlinarith [mul_le_mul_of_nonneg_left hx.2 K.coe_nonneg]
  have hintbd := intervalIntegral.norm_integral_le_of_norm_le_const_ae hbound
  have hlen : |b - ((N : ℝ) - 1) * u| ≤ u := by
    rw [abs_of_nonneg (by linarith)]
    nlinarith
  have hintle : ‖∫ x in ((N : ℝ) - 1) * u..b, h x‖ ≤
      u * (‖h 0‖ + (K : ℝ) * b) := by
    calc
      _ ≤ (‖h 0‖ + (K : ℝ) * b) * |b - ((N : ℝ) - 1) * u| := hintbd
      _ ≤ (‖h 0‖ + (K : ℝ) * b) * u := by
        gcongr
      _ = _ := by ring
  by_cases heq : (N : ℝ) * u = b
  · rw [heq]
    calc
      _ ≤ ‖(u : ℂ) * h b‖ + ‖∫ x in ((N : ℝ) - 1) * u..b, h x‖ := norm_sub_le _ _
      _ ≤ u * ‖h b‖ + u * (‖h 0‖ + (K : ℝ) * b) := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu]
        gcongr
      _ = _ := by ring
  · have hgt : b < (N : ℝ) * u := lt_of_le_of_ne hhi (Ne.symm heq)
    have hz : h ((N : ℝ) * u) = 0 := hsupp _ (by
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inr (fun hi => (not_le_of_gt hgt) hi))
    rw [hz, mul_zero, zero_sub, norm_neg]
    calc
      _ ≤ u * (‖h 0‖ + (K : ℝ) * b) := hintle
      _ ≤ u * ((‖h 0‖ + (K : ℝ) * b) + ‖h b‖) := by
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hu.le

lemma sum_Icc_one_eq_sum_range {E : Type*} [AddCommMonoid E] (f : ℕ → E) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_Icc_succ_top (Nat.le_add_left 1 N), ih]

/-- Finite right-endpoint mesh estimate, including the possibly discontinuous boundary cell. -/
theorem riemannBoundaryCellBridge_main
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmeas : Measurable h) (u : ℝ) (hu : 0 < u) :
    ‖(u : ℂ) * ∑' n : ℕ+, h ((n : ℝ) * u) -
        ∫ x in Set.Ioi (0 : ℝ), h x‖ ≤
      u * (K * b + (‖h 0‖ + K * b) + ‖h b‖) := by
  let N := Nat.ceil (b / u)
  have hN : 0 < N := Nat.ceil_pos.mpr (div_pos hb hu)
  have hceil : b ≤ (N : ℝ) * u := by
    have := Nat.le_ceil (b / u)
    calc b = (b / u) * u := by field_simp
         _ ≤ (N : ℝ) * u := mul_le_mul_of_nonneg_right this hu.le
  have hprev : ((N : ℝ) - 1) * u < b := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ b / u by positivity)
    have hm := mul_lt_mul_of_pos_right hc hu
    have hdiv : (b / u) * u = b := div_mul_cancel₀ b hu.ne'
    dsimp [N] at hm ⊢
    nlinarith
  have hint := riemannBoundaryCellBridge_integrable h b hb K hsupp hlip hmeas
  have hInt : (∫ x in Set.Ioi (0 : ℝ), h x) = ∫ x in (0 : ℝ)..b, h x := by
    rw [intervalIntegral.integral_of_le hb.le]
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
        ← MeasureTheory.integral_indicator measurableSet_Ioc]
    congr 1
    funext x
    by_cases hx : x ∈ Set.Ioc (0 : ℝ) b
    · simp [hx, hx.1]
    · by_cases hx0 : x = 0
      · subst x
        simp
      · have hz : h x = 0 := by
          apply hsupp
          intro hi
          apply hx
          exact ⟨lt_of_le_of_ne hi.1 (Ne.symm hx0), hi.2⟩
        simp [hx, hz]
  rw [riemannBoundaryCellBridge_finiteReduction h b u hu hsupp, hInt,
      sum_Icc_one_eq_sum_range]
  change ‖(u : ℂ) * ∑ i ∈ Finset.range N, h (((i + 1 : ℕ) : ℝ) * u) -
      ∫ x in (0 : ℝ)..b, h x‖ ≤ _
  simp_rw [Nat.cast_add, Nat.cast_one]
  have hsumInt : ∑ k ∈ Finset.range N,
      (∫ x in (k : ℝ) * u..((k : ℝ) + 1) * u, h x) =
      ∫ x in (0 : ℝ)..(N : ℝ) * u, h x := by
    simpa [Nat.cast_add, Nat.cast_one, add_mul] using
      (intervalIntegral.sum_integral_adjacent_intervals
        (f := h) (a := fun k : ℕ => (k : ℝ) * u) (n := N)
        (fun _ _ => hint.intervalIntegrable))
  have htailzero : (∫ x in b..(N : ℝ) * u, h x) = 0 := by
    rw [intervalIntegral.integral_of_le hceil]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards [(volume.restrict (Set.Ioc b ((N : ℝ) * u))).ae_ne b,
      self_mem_ae_restrict measurableSet_Ioc] with x hxb hx
    exact hsupp x (by
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inr (fun hib => (not_le_of_gt hx.1) hib))
  have hIntN : (∫ x in (0 : ℝ)..(N : ℝ) * u, h x) = ∫ x in (0 : ℝ)..b, h x := by
    rw [← intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
      hint.intervalIntegrable, htailzero, add_zero]
  rw [← hIntN, ← hsumInt, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  have hsplit : Finset.range N = Finset.range (N - 1) ∪ {N - 1} := by
    ext k
    simp only [Finset.mem_range, Finset.mem_union, Finset.mem_singleton]
    omega
  rw [hsplit, Finset.sum_union]
  · rw [Finset.sum_singleton]
    have hinter : ‖∑ k ∈ Finset.range (N - 1),
          ((u : ℂ) * h (((k : ℝ) + 1) * u) -
            ∫ x in (k : ℝ) * u..((k : ℝ) + 1) * u, h x)‖ ≤
          (K : ℝ) * b * u := by
        calc
          _ ≤ ∑ k ∈ Finset.range (N - 1),
              ‖(u : ℂ) * h (((k : ℝ) + 1) * u) -
                ∫ x in (k : ℝ) * u..((k : ℝ) + 1) * u, h x‖ := norm_sum_le _ _
          _ ≤ ∑ _k ∈ Finset.range (N - 1), (K : ℝ) * u * u := by
            gcongr with k hk
            simpa [add_mul] using
              riemannBoundaryCellBridge_fullCell h b K hlip hint u ((k : ℝ) * u) hu
                (by positivity) (by
                  have hk' : k < N - 1 := Finset.mem_range.mp hk
                  have hkNat : k + 1 ≤ N - 1 := by omega
                  have hkcast' : ((k + 1 : ℕ) : ℝ) ≤ ((N - 1 : ℕ) : ℝ) := by exact_mod_cast hkNat
                  have hNm : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
                    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
                    norm_num
                  have hkcast : (k : ℝ) + 1 ≤ (N : ℝ) - 1 := by
                    simpa [Nat.cast_add] using hkcast'.trans_eq hNm
                  nlinarith [hprev, mul_le_mul_of_nonneg_right hkcast hu.le])
          _ ≤ (K : ℝ) * b * u := by
            simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            have hc : ((N - 1 : ℕ) : ℝ) * u < b := by
              have hcN : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
                rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
                norm_num
              rw [hcN]
              exact hprev
            calc
              ((N - 1 : ℕ) : ℝ) * ((K : ℝ) * u * u) =
                  (K : ℝ) * ((((N - 1 : ℕ) : ℝ) * u) * u) := by ring
              _ ≤ (K : ℝ) * (b * u) := by gcongr
              _ = (K : ℝ) * b * u := by ring
    have hterm := riemannBoundaryCellBridge_terminalCell h b hb K hsupp hlip u hu N hN hprev hceil
    have hlast : (((N - 1 : ℕ) : ℝ) + 1) * u = (N : ℝ) * u := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
      norm_num
    have hleft : ((N - 1 : ℕ) : ℝ) * u = ((N : ℝ) - 1) * u := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN.ne')]
      norm_num
    have hlastInt : (∫ x in ((N : ℝ) - 1) * u..(N : ℝ) * u, h x) =
        ∫ x in ((N : ℝ) - 1) * u..b, h x := by
      rw [← intervalIntegral.integral_add_adjacent_intervals hint.intervalIntegrable
        hint.intervalIntegrable, htailzero, add_zero]
    rw [hlast, hleft, hlastInt]
    calc
        _ ≤ ‖∑ k ∈ Finset.range (N - 1),
            ((u : ℂ) * h (((k : ℝ) + 1) * u) -
              ∫ x in (k : ℝ) * u..((k : ℝ) + 1) * u, h x)‖ +
            ‖(u : ℂ) * h ((N : ℝ) * u) -
              ∫ x in ((N : ℝ) - 1) * u..b, h x‖ := norm_add_le _ _
        _ ≤ (K : ℝ) * b * u + u * ((‖h 0‖ + (K : ℝ) * b) + ‖h b‖) := add_le_add hinter hterm
        _ = u * ((K : ℝ) * b + (‖h 0‖ + (K : ℝ) * b) + ‖h b‖) := by ring
  · simp

/-- The mesh estimate when the integral (mass) is zero. -/
theorem riemannBoundaryCellBridge_zeroMass
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmeas : Measurable h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (u : ℝ) (hu : 0 < u) :
    ‖∑' n : ℕ+, h ((n : ℝ) * u)‖ ≤
      K * b + (‖h 0‖ + K * b) + ‖h b‖ := by
  have hmain := riemannBoundaryCellBridge_main h b hb K hsupp hlip hmeas u hu
  rw [hmass, sub_zero, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hu] at hmain
  exact (mul_le_mul_iff_of_pos_left hu).mp hmain

/-- The corresponding estimate after multiplication by `sqrt u`. -/
theorem riemannBoundaryCellBridge_Estar
    (h : ℝ → ℂ) (b : ℝ) (hb : 0 < b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (hmeas : Measurable h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0)
    (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) :
    ‖Estar h u‖ ≤
      (K * b + (‖h 0‖ + K * b) + ‖h b‖) * Real.sqrt u := by
  rw [Estar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg u)]
  simpa [mul_comm] using mul_le_mul_of_nonneg_right
    (riemannBoundaryCellBridge_zeroMass h b hb K hsupp hlip hmeas hmass u hu.1)
    (Real.sqrt_nonneg u)
