import Q3.Proofs.RouteB.G6N1SturmDefectTruncatedEnergy

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# WEIGHTED_CONSUMER nodes 3A/3B (verdict c47b75a8, REQ-2026-08-26-B)

The weighted Cauchy–Schwarz consumer for the W5 defect comb, in the exact
W5 normalization: spacing `u = eˣ/λ`, log window `x ∈ (0, log m)`,
active lattice `n ∈ [1, m]`, budget weight `√u`, `λ = √m`.

* `sturm_weighted_consumer_interior_bound` (node 3A): every lattice
  contribution with `y_n ≤ λ/2` is bounded by
  `2λ·√(½ log(4/3))·√E0` — an absolute companion constant.
* `sturm_weighted_consumer_nonTop_sqrtLog_bound` (node 3B): every non-top
  contribution (`y_n ≤ λ − u`) is bounded by `2λ·√(½ log(m+1))·√E0` —
  the honest `√log` rate of the energy-only black box.

The top lattice point is EXCLUDED by the filter in both statements; its
functional is the carried-open supplier
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`.
No uniform edge-band claim is made (killed by the judge's counterprofile).
-/

/-! ## Arithmetic helper: `Σ n^{-1/2} ≤ 2√m` -/

theorem wc_sum_inv_sqrt_le (m : ℕ) :
    ∑ n ∈ Finset.Icc 1 m, (1 : ℝ) / Real.sqrt n ≤ 2 * Real.sqrt m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_Icc_succ_top (Nat.one_le_iff_ne_zero.mpr (Nat.succ_ne_zero m))]
    have hs : (0 : ℝ) < Real.sqrt (m + 1) := by
      apply Real.sqrt_pos.2; positivity
    have hsq1 : (Real.sqrt ((m : ℝ) + 1)) ^ 2 = (m : ℝ) + 1 :=
      Real.sq_sqrt (by positivity)
    have hsq0 : (Real.sqrt (m : ℝ)) ^ 2 = (m : ℝ) :=
      Real.sq_sqrt (Nat.cast_nonneg m)
    have ht0 : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hstep : (1 : ℝ) / Real.sqrt ((m : ℕ) + 1 : ℕ) ≤
        2 * Real.sqrt ((m : ℕ) + 1 : ℕ) - 2 * Real.sqrt m := by
      have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
      rw [hcast, div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt ((m : ℝ) + 1) - Real.sqrt m)]
    have hcast : (((m : ℕ) + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    calc (∑ n ∈ Finset.Icc 1 m, (1 : ℝ) / Real.sqrt n) +
        (1 : ℝ) / Real.sqrt ((m : ℕ) + 1 : ℕ) ≤
        2 * Real.sqrt m +
          (2 * Real.sqrt ((m : ℕ) + 1 : ℕ) - 2 * Real.sqrt m) := by
          exact add_le_add ih hstep
      _ = 2 * Real.sqrt ((m : ℕ) + 1 : ℕ) := by ring

/-! ## Companion integral: exact antiderivative and bound -/

theorem wc_companion_integral_le (lam a b : ℝ) (hlam : 0 < lam)
    (h0 : 0 ≤ a) (hab : a ≤ b) (hb : b < lam) :
    ∫ y in a..b, y / (lam ^ 2 - y ^ 2) ≤
      (1 / 2) * Real.log (lam ^ 2 / (lam ^ 2 - b ^ 2)) := by
  have hbpos : 0 < lam ^ 2 - b ^ 2 := by nlinarith [h0.trans hab]
  have hwpos : ∀ y ∈ Icc a b, 0 < lam ^ 2 - y ^ 2 := by
    intro y hy
    nlinarith [hy.1, hy.2, h0]
  have hderiv : ∀ y ∈ uIcc a b,
      HasDerivAt (fun z : ℝ => -(1 / 2) * Real.log (lam ^ 2 - z ^ 2))
        (y / (lam ^ 2 - y ^ 2)) y := by
    intro y hy
    rw [uIcc_of_le hab] at hy
    have hne : lam ^ 2 - y ^ 2 ≠ 0 := (hwpos y hy).ne'
    have hinner : HasDerivAt (fun z : ℝ => lam ^ 2 - z ^ 2) (-(2 * y)) y := by
      have h2 := hasDerivAt_pow 2 y
      have hc := hasDerivAt_const y (lam ^ 2)
      exact (hc.sub h2).congr_deriv (by push_cast; ring)
    have hlog := hinner.log hne
    have := hlog.const_mul (-(1 / 2) : ℝ)
    refine this.congr_deriv ?_
    field_simp
  have hcont : IntervalIntegrable (fun y : ℝ => y / (lam ^ 2 - y ^ 2))
      volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    apply ContinuousOn.div continuousOn_id
    · exact (continuousOn_const.sub (continuous_pow 2).continuousOn)
    · intro y hy
      exact (hwpos y hy).ne'
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  rw [heq]
  have hapos : 0 < lam ^ 2 - a ^ 2 := by nlinarith [hab.trans_lt hb, h0]
  have hle : lam ^ 2 - a ^ 2 ≤ lam ^ 2 := by nlinarith
  have hloga : Real.log (lam ^ 2 - a ^ 2) ≤ Real.log (lam ^ 2) :=
    Real.log_le_log hapos hle
  rw [Real.log_div (by positivity) hbpos.ne']
  ring_nf
  nlinarith [hloga]

/-! ## Pointwise AM–GM against the energy weight -/

theorem wc_pointwise_amgm (lam t y gval : ℝ) (ht : 0 < t)
    (hy : 0 < y) (hylam : y < lam) :
    Real.sqrt y * |gval| ≤
      (1 / (2 * t)) * (y / (lam ^ 2 - y ^ 2)) +
        (t / 2) * ((lam ^ 2 - y ^ 2) * gval ^ 2) := by
  have hw : (0 : ℝ) < lam ^ 2 - y ^ 2 := by nlinarith
  set A := Real.sqrt (y / (lam ^ 2 - y ^ 2)) with hA
  set B := Real.sqrt (lam ^ 2 - y ^ 2) * |gval| with hB
  have hA2 : A ^ 2 = y / (lam ^ 2 - y ^ 2) := by
    rw [hA, Real.sq_sqrt (div_nonneg hy.le hw.le)]
  have hB2 : B ^ 2 = (lam ^ 2 - y ^ 2) * gval ^ 2 := by
    rw [hB, mul_pow, Real.sq_sqrt hw.le, sq_abs]
  have hAB : A * B = Real.sqrt y * |gval| := by
    rw [hA, hB, ← mul_assoc, ← Real.sqrt_mul (div_nonneg hy.le hw.le),
      div_mul_cancel₀ _ hw.ne']
  have hkey : 0 ≤ A ^ 2 - 2 * t * (A * B) + t ^ 2 * B ^ 2 := by
    nlinarith [sq_nonneg (A - t * B)]
  rw [← hAB, ← hA2, ← hB2]
  have ht2 : (0 : ℝ) < 2 * t := by linarith
  rw [← sub_nonneg]
  have hexpand : (1 / (2 * t)) * A ^ 2 + (t / 2) * B ^ 2 - A * B =
      (1 / (2 * t)) * (A ^ 2 - 2 * t * (A * B) + t ^ 2 * B ^ 2) := by
    field_simp
    ring
  rw [hexpand]
  exact mul_nonneg (by positivity) hkey

/-! ## The core consumer bound (abstract threshold `β`) -/

/-- **Core weighted-consumer bound.**  For any threshold family `β` with
`n < β n` and companion cap `(1/2)·log(β²/(β²−n²)) ≤ Ccap`, the
`√u`-weighted comb of the lattice points with `β n · u ≤ λ` is bounded by
`2λ·√Ccap·√E0`. -/
theorem wc_core_bound
    (m : ℕ) (hm : 1 ≤ m)
    (β : ℕ → ℝ)
    (hβgt : ∀ n ∈ Finset.Icc 1 m, (n : ℝ) < β n)
    (Ccap : ℝ) (hCcap : 0 < Ccap)
    (hβcomp : ∀ n ∈ Finset.Icc 1 m,
      (1 / 2) * Real.log ((β n) ^ 2 / ((β n) ^ 2 - (n : ℝ) ^ 2)) ≤ Ccap)
    (gd : ℝ → ℝ)
    (hgd : ContinuousOn gd (Ioo 0 (Real.sqrt m)))
    (E0 : ℝ) (hE0 : 0 < E0)
    (hEint : IntegrableOn
      (fun y : ℝ => ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo 0 (Real.sqrt m)) volume)
    (hE : (∫ y in Ioo 0 (Real.sqrt m),
      ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2) ≤ E0) :
    (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / Real.sqrt m) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n => β n * (Real.exp x / Real.sqrt m) ≤ Real.sqrt m),
          ((n : ℝ) * (Real.exp x / Real.sqrt m)) *
            gd ((n : ℝ) * (Real.exp x / Real.sqrt m))|) ≤
      2 * Real.sqrt m * (Real.sqrt Ccap * Real.sqrt E0) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  set lam := Real.sqrt (m : ℝ) with hlamdef
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  have hsq : lam ^ 2 = (m : ℝ) := Real.sq_sqrt hmR.le
  have hL0 : (0 : ℝ) ≤ Real.log m := Real.log_nonneg hm1
  -- the signed and absolute per-n integrands
  set Fs : ℕ → ℝ → ℝ := fun n x =>
    if β n * (Real.exp x / lam) ≤ lam then
      Real.sqrt (Real.exp x / lam) *
        (((n : ℝ) * (Real.exp x / lam)) *
          gd ((n : ℝ) * (Real.exp x / lam))) else 0 with hFs
  set Fa : ℕ → ℝ → ℝ := fun n x =>
    if β n * (Real.exp x / lam) ≤ lam then
      Real.sqrt (Real.exp x / lam) *
        (((n : ℝ) * (Real.exp x / lam)) *
          |gd ((n : ℝ) * (Real.exp x / lam))|) else 0 with hFa
  -- per-n analysis
  have hper : ∀ n ∈ Finset.Icc 1 m,
      IntervalIntegrable (Fs n) volume 0 (Real.log m) ∧
      IntervalIntegrable (Fa n) volume 0 (Real.log m) ∧
      (∫ x in (0 : ℝ)..Real.log m, Fa n x) ≤
        (1 / Real.sqrt n) * (Real.sqrt Ccap * Real.sqrt E0) := by
    intro n hn
    obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.mp hn
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
    have hβn := hβgt n hn
    have hβ0 : (0 : ℝ) < β n := lt_trans hn0 hβn
    have hβ1 : (1 : ℝ) < β n := lt_of_le_of_lt hnR hβn
    set c : ℝ := Real.log ((m : ℝ) / β n) with hc
    -- the condition is an interval in x
    have hcond : ∀ x : ℝ, (β n * (Real.exp x / lam) ≤ lam ↔ x ≤ c) := by
      intro x
      rw [hc, Real.le_log_iff_exp_le (by positivity), le_div_iff₀ hβ0,
        ← mul_div_assoc, div_le_iff₀ hlam0]
      constructor
      · intro h
        nlinarith [h, hsq]
      · intro h
        nlinarith [h, hsq]
    -- c is strictly below the top of the log window
    have hcL : c < Real.log m := by
      rw [hc]
      apply Real.log_lt_log (by positivity)
      rw [div_lt_iff₀ hβ0]
      nlinarith [hβ1, hmR]
    by_cases hcpos : c ≤ 0
    · -- the condition never holds inside the window: everything vanishes
      have hnever : ∀ x ∈ Ioc (0 : ℝ) (Real.log m),
          ¬(β n * (Real.exp x / lam) ≤ lam) := by
        intro x hx h
        have := (hcond x).1 h
        linarith [hx.1]
      have hzs : ∀ x ∈ Ioc (0 : ℝ) (Real.log m), Fs n x = 0 := by
        intro x hx
        simp only [hFs]
        rw [if_neg (hnever x hx)]
      have hza : ∀ x ∈ Ioc (0 : ℝ) (Real.log m), Fa n x = 0 := by
        intro x hx
        simp only [hFa]
        rw [if_neg (hnever x hx)]
      have hints : IntervalIntegrable (Fs n) volume 0 (Real.log m) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0]
        exact integrableOn_zero.congr_fun
          (fun x hx => (hzs x hx).symm) measurableSet_Ioc
      have hinta : IntervalIntegrable (Fa n) volume 0 (Real.log m) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0]
        exact integrableOn_zero.congr_fun
          (fun x hx => (hza x hx).symm) measurableSet_Ioc
      refine ⟨hints, hinta, ?_⟩
      rw [intervalIntegral.integral_of_le hL0,
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hza]
      simp only [MeasureTheory.integral_zero]
      positivity
    · push_neg at hcpos
      -- the scale map and its exact derivative
      have hβm : β n < (m : ℝ) := by
        by_contra hcon
        push_neg at hcon
        have h1 : (m : ℝ) / β n ≤ 1 := (div_le_one hβ0).mpr hcon
        have h2 : Real.log ((m : ℝ) / β n) ≤ 0 :=
          Real.log_nonpos (by positivity) h1
        rw [← hc] at h2
        linarith
      set φ : ℝ → ℝ := fun x => (n : ℝ) * (Real.exp x / lam) with hφ
      have hφd : ∀ x : ℝ, HasDerivAt φ (φ x) x := by
        intro x
        exact ((Real.hasDerivAt_exp x).div_const lam).const_mul _
      have hφcont : Continuous φ := by
        simp only [hφ]
        fun_prop
      have hφ0 : φ 0 = (n : ℝ) / lam := by
        simp only [hφ]
        rw [Real.exp_zero, mul_one_div]
      have hφc : φ c = (n : ℝ) * lam / β n := by
        simp only [hφ, hc]
        rw [Real.exp_log (div_pos hmR hβ0), ← hsq]
        field_simp
      have hendlt : (n : ℝ) * lam / β n < lam := by
        rw [div_lt_iff₀ hβ0]
        nlinarith [hβn, hlam0]
      have hendpos : (0 : ℝ) < (n : ℝ) / lam := by positivity
      have hab' : (n : ℝ) / lam ≤ (n : ℝ) * lam / β n := by
        rw [div_le_div_iff₀ hlam0 hβ0]
        have hb2 : β n ≤ lam * lam := by nlinarith [hβm, hsq]
        nlinarith [mul_le_mul_of_nonneg_left hb2 hn0.le]
      have hφmono : Monotone φ := by
        intro x₁ x₂ h
        simp only [hφ]
        gcongr <;> exact Real.exp_le_exp.mpr h
      have hφmaps : ∀ x ∈ Icc (0 : ℝ) c,
          φ x ∈ Icc ((n : ℝ) / lam) ((n : ℝ) * lam / β n) := by
        intro x hx
        constructor
        · rw [← hφ0]; exact hφmono hx.1
        · rw [← hφc]; exact hφmono hx.2
      have hIccsub : Icc ((n : ℝ) / lam) ((n : ℝ) * lam / β n) ⊆
          Ioo 0 lam := by
        intro y hy
        exact ⟨lt_of_lt_of_le hendpos hy.1, lt_of_le_of_lt hy.2 hendlt⟩
      -- the value functions on [0, c]
      set vs : ℝ → ℝ := fun x =>
        Real.sqrt (Real.exp x / lam) * (φ x * gd (φ x)) with hvs
      set va : ℝ → ℝ := fun x =>
        Real.sqrt (Real.exp x / lam) * (φ x * |gd (φ x)|) with hva
      have hgd_comp : ContinuousOn (fun x : ℝ => gd (φ x)) (Icc 0 c) := by
        apply ContinuousOn.comp hgd hφcont.continuousOn
        intro x hx
        exact hIccsub (hφmaps x hx)
      have hvs_cont : ContinuousOn vs (Icc 0 c) := by
        simp only [hvs]
        apply ContinuousOn.mul
        · apply Continuous.continuousOn
          fun_prop
        · exact hφcont.continuousOn.mul hgd_comp
      have hva_cont : ContinuousOn va (Icc 0 c) := by
        simp only [hva]
        apply ContinuousOn.mul
        · apply Continuous.continuousOn
          fun_prop
        · exact hφcont.continuousOn.mul hgd_comp.abs
      -- Fs, Fa agree with vs, va on [0, c] and vanish beyond c
      have hEqs : EqOn (Fs n) vs (Icc 0 c) := by
        intro x hx
        simp only [hFs, hvs, hφ]
        rw [if_pos ((hcond x).2 hx.2)]
      have hEqa : EqOn (Fa n) va (Icc 0 c) := by
        intro x hx
        simp only [hFa, hva, hφ]
        rw [if_pos ((hcond x).2 hx.2)]
      have hzs2 : ∀ x ∈ Ioc c (Real.log m), Fs n x = 0 := by
        intro x hx
        simp only [hFs]
        rw [if_neg]
        intro hcon
        have := (hcond x).1 hcon
        linarith [hx.1]
      have hza2 : ∀ x ∈ Ioc c (Real.log m), Fa n x = 0 := by
        intro x hx
        simp only [hFa]
        rw [if_neg]
        intro hcon
        have := (hcond x).1 hcon
        linarith [hx.1]
      -- integrability on the two pieces
      have hints1 : IntervalIntegrable (Fs n) volume 0 c := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcpos.le]
        apply MeasureTheory.IntegrableOn.congr_fun _
          (fun x hx => (hEqs (Ioc_subset_Icc_self hx)).symm) measurableSet_Ioc
        exact (hvs_cont.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self
      have hinta1 : IntervalIntegrable (Fa n) volume 0 c := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcpos.le]
        apply MeasureTheory.IntegrableOn.congr_fun _
          (fun x hx => (hEqa (Ioc_subset_Icc_self hx)).symm) measurableSet_Ioc
        exact (hva_cont.integrableOn_compact isCompact_Icc).mono_set
          Ioc_subset_Icc_self
      have hints2 : IntervalIntegrable (Fs n) volume c (Real.log m) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcL.le]
        exact integrableOn_zero.congr_fun
          (fun x hx => (hzs2 x hx).symm) measurableSet_Ioc
      have hinta2 : IntervalIntegrable (Fa n) volume c (Real.log m) := by
        rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hcL.le]
        exact integrableOn_zero.congr_fun
          (fun x hx => (hza2 x hx).symm) measurableSet_Ioc
      refine ⟨hints1.trans hints2, hinta1.trans hinta2, ?_⟩
      -- the value: only the [0, c] piece survives
      have hsplit := intervalIntegral.integral_add_adjacent_intervals
        hinta1 hinta2
      have hzero2 : (∫ x in c..Real.log m, Fa n x) = 0 := by
        rw [intervalIntegral.integral_of_le hcL.le,
          MeasureTheory.setIntegral_congr_fun measurableSet_Ioc hza2]
        simp
      have hval1 : (∫ x in (0:ℝ)..c, Fa n x) = ∫ x in (0:ℝ)..c, va x :=
        intervalIntegral.integral_congr (by
          rw [uIcc_of_le hcpos.le]; exact hEqa)
      -- change of variables on the surviving piece
      have hgfun_cont : ContinuousOn
          (fun y : ℝ => (1 / Real.sqrt n) * (Real.sqrt y * |gd y|))
          (Icc ((n : ℝ) / lam) ((n : ℝ) * lam / β n)) := by
        apply ContinuousOn.mul continuousOn_const
        apply ContinuousOn.mul
        · exact (Real.continuous_sqrt).continuousOn
        · exact (hgd.mono hIccsub).abs
      have hva_comp : EqOn va
          (fun x => ((fun y : ℝ => (1 / Real.sqrt n) *
            (Real.sqrt y * |gd y|)) ∘ φ) x * φ x) (Icc 0 c) := by
        intro x hx
        simp only [hva, Function.comp_apply, hφ]
        have hsn : Real.sqrt ((n : ℝ) * (Real.exp x / lam)) =
            Real.sqrt n * Real.sqrt (Real.exp x / lam) :=
          Real.sqrt_mul (Nat.cast_nonneg n) _
        have hsn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
        have hkey : (1 / Real.sqrt n) *
            Real.sqrt ((n : ℝ) * (Real.exp x / lam)) =
            Real.sqrt (Real.exp x / lam) := by
          rw [hsn]
          field_simp
        linear_combination
          (-(((n : ℝ) * (Real.exp x / lam)) *
            |gd ((n : ℝ) * (Real.exp x / lam))|)) * hkey
      have hcov : (∫ x in (0:ℝ)..c, va x) =
          ∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
            (1 / Real.sqrt n) * (Real.sqrt y * |gd y|) := by
        rw [intervalIntegral.integral_congr (by
          rw [uIcc_of_le hcpos.le]; exact hva_comp)]
        have h := intervalIntegral.integral_comp_mul_deriv'
          (f := φ) (f' := φ)
          (g := fun y : ℝ => (1 / Real.sqrt n) * (Real.sqrt y * |gd y|))
          (a := (0:ℝ)) (b := c)
          (fun x _ => hφd x)
          hφcont.continuousOn
          (by
            apply hgfun_cont.mono
            rw [uIcc_of_le hcpos.le]
            intro y hy
            obtain ⟨x, hx, rfl⟩ := hy
            exact hφmaps x hx)
        rw [hφ0, hφc] at h
        exact h
      -- AM–GM against the energy weight, with the global t
      set t : ℝ := Real.sqrt Ccap / Real.sqrt E0 with ht
      have hsC : (0 : ℝ) < Real.sqrt Ccap := Real.sqrt_pos.2 hCcap
      have hsE : (0 : ℝ) < Real.sqrt E0 := Real.sqrt_pos.2 hE0
      have ht0 : (0 : ℝ) < t := by rw [ht]; positivity
      have hsqrt_int : IntervalIntegrable
          (fun y : ℝ => Real.sqrt y * |gd y|) volume
          ((n : ℝ) / lam) ((n : ℝ) * lam / β n) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab']
        apply ContinuousOn.mul (Real.continuous_sqrt).continuousOn
        exact (hgd.mono hIccsub).abs
      have hmaj_int : IntervalIntegrable
          (fun y : ℝ => (1 / (2 * t)) * (y / (lam ^ 2 - y ^ 2)) +
            (t / 2) * ((lam ^ 2 - y ^ 2) * gd y ^ 2)) volume
          ((n : ℝ) / lam) ((n : ℝ) * lam / β n) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab']
        apply ContinuousOn.add
        · apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.div continuousOn_id
          · exact continuousOn_const.sub (continuous_pow 2).continuousOn
          · intro y hy
            have := hIccsub hy
            nlinarith [this.1, this.2]
        · apply ContinuousOn.mul continuousOn_const
          apply ContinuousOn.mul
          · exact continuousOn_const.sub (continuous_pow 2).continuousOn
          · exact ((hgd.mono hIccsub).pow 2)
      have hamgm : (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
          Real.sqrt y * |gd y|) ≤
          ∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
            ((1 / (2 * t)) * (y / (lam ^ 2 - y ^ 2)) +
              (t / 2) * ((lam ^ 2 - y ^ 2) * gd y ^ 2)) := by
        apply intervalIntegral.integral_mono_on hab' hsqrt_int hmaj_int
        intro y hy
        have hyI := hIccsub hy
        exact wc_pointwise_amgm lam t y (gd y) ht0 hyI.1 hyI.2
      -- the two majorant pieces
      have hcompanion : (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
          y / (lam ^ 2 - y ^ 2)) ≤ Ccap := by
        have h1 := wc_companion_integral_le lam ((n : ℝ) / lam)
          ((n : ℝ) * lam / β n) hlam0 hendpos.le hab' hendlt
        have h2 : lam ^ 2 / (lam ^ 2 - ((n : ℝ) * lam / β n) ^ 2) =
            (β n) ^ 2 / ((β n) ^ 2 - (n : ℝ) ^ 2) := by
          have hβsq : (0 : ℝ) < (β n) ^ 2 - (n : ℝ) ^ 2 := by
            nlinarith [hβn, hn0]
          field_simp
        rw [h2] at h1
        exact h1.trans (hβcomp n hn)
      have henergy : (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
          (lam ^ 2 - y ^ 2) * gd y ^ 2) ≤ E0 := by
        rw [intervalIntegral.integral_of_le hab']
        have hsub2 : Ioc ((n : ℝ) / lam) ((n : ℝ) * lam / β n) ⊆
            Ioo 0 lam := fun y hy => hIccsub ⟨hy.1.le, hy.2⟩
        have hf0 : (0 : ℝ → ℝ) ≤ᵐ[volume.restrict (Ioo 0 lam)]
            fun y => (lam ^ 2 - y ^ 2) * gd y ^ 2 := by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo]
            with y hy
          have h1 : y ^ 2 < lam ^ 2 := by nlinarith [hy.1, hy.2]
          simp only [Pi.zero_apply]
          exact mul_nonneg (by linarith) (sq_nonneg _)
        have hmono := MeasureTheory.setIntegral_mono_set hEint hf0
          hsub2.eventuallyLE
        exact hmono.trans hE
      -- the two majorant pieces are separately integrable
      have hcomp_int : IntervalIntegrable
          (fun y : ℝ => y / (lam ^ 2 - y ^ 2)) volume
          ((n : ℝ) / lam) ((n : ℝ) * lam / β n) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab']
        apply ContinuousOn.div continuousOn_id
          (continuousOn_const.sub (continuous_pow 2).continuousOn)
        intro y hy
        have := hIccsub hy
        nlinarith [this.1, this.2]
      have hen_int : IntervalIntegrable
          (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y ^ 2) volume
          ((n : ℝ) / lam) ((n : ℝ) * lam / β n) := by
        apply ContinuousOn.intervalIntegrable
        rw [uIcc_of_le hab']
        exact (continuousOn_const.sub (continuous_pow 2).continuousOn).mul
          ((hgd.mono hIccsub).pow 2)
      -- algebra of the optimal split constant
      have h1t : t * Real.sqrt E0 = Real.sqrt Ccap := by
        rw [ht]
        field_simp
      have hCC : Real.sqrt Ccap * Real.sqrt Ccap = Ccap :=
        Real.mul_self_sqrt hCcap.le
      have hEE : Real.sqrt E0 * Real.sqrt E0 = E0 :=
        Real.mul_self_sqrt hE0.le
      have hCt : Ccap = t ^ 2 * E0 := by
        rw [← hCC, ← h1t]
        linear_combination t ^ 2 * hEE
      have hprod_t : Real.sqrt Ccap * Real.sqrt E0 = t * E0 := by
        rw [← h1t]
        linear_combination t * hEE
      have halg : (1 / (2 * t)) * Ccap + (t / 2) * E0 =
          Real.sqrt Ccap * Real.sqrt E0 := by
        rw [hprod_t, hCt]
        field_simp
        ring
      -- assemble the per-n value bound
      rw [← hsplit, hzero2, add_zero, hval1, hcov,
        intervalIntegral.integral_const_mul]
      have hsn0 : (0 : ℝ) < Real.sqrt n := Real.sqrt_pos.2 hn0
      apply mul_le_mul_of_nonneg_left _ (by positivity :
        (0 : ℝ) ≤ 1 / Real.sqrt n)
      calc (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
          Real.sqrt y * |gd y|) ≤
          ∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
            ((1 / (2 * t)) * (y / (lam ^ 2 - y ^ 2)) +
              (t / 2) * ((lam ^ 2 - y ^ 2) * gd y ^ 2)) := hamgm
        _ = (1 / (2 * t)) *
              (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
                y / (lam ^ 2 - y ^ 2)) +
            (t / 2) *
              (∫ y in ((n : ℝ) / lam)..((n : ℝ) * lam / β n),
                (lam ^ 2 - y ^ 2) * gd y ^ 2) := by
            rw [intervalIntegral.integral_add
                (hcomp_int.const_mul _) (hen_int.const_mul _),
              intervalIntegral.integral_const_mul,
              intervalIntegral.integral_const_mul]
        _ ≤ (1 / (2 * t)) * Ccap + (t / 2) * E0 := by
            have hA := mul_le_mul_of_nonneg_left hcompanion
              (by positivity : (0 : ℝ) ≤ 1 / (2 * t))
            have hB := mul_le_mul_of_nonneg_left henergy
              (by positivity : (0 : ℝ) ≤ t / 2)
            linarith
        _ = Real.sqrt Ccap * Real.sqrt E0 := halg
  -- pointwise identity and domination, then sum the per-n bounds
  have hpoint_eq : ∀ x : ℝ,
      Real.sqrt (Real.exp x / lam) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n => β n * (Real.exp x / lam) ≤ lam),
          ((n : ℝ) * (Real.exp x / lam)) *
            gd ((n : ℝ) * (Real.exp x / lam))| =
      |∑ n ∈ Finset.Icc 1 m, Fs n x| := by
    intro x
    rw [Finset.sum_filter, ← abs_of_nonneg (Real.sqrt_nonneg
      (Real.exp x / lam)), ← abs_mul, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    simp only [hFs]
    rw [mul_ite, mul_zero]
  have hpoint_le : ∀ x : ℝ,
      |∑ n ∈ Finset.Icc 1 m, Fs n x| ≤ ∑ n ∈ Finset.Icc 1 m, Fa n x := by
    intro x
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    apply Finset.sum_le_sum
    intro n _
    simp only [hFs, hFa]
    by_cases hcase : β n * (Real.exp x / lam) ≤ lam
    · rw [if_pos hcase, if_pos hcase, abs_mul, abs_mul,
        abs_of_nonneg (Real.sqrt_nonneg _),
        abs_of_nonneg (by positivity : (0:ℝ) ≤ (n : ℝ) * (Real.exp x / lam))]
    · rw [if_neg hcase, if_neg hcase, abs_zero]
  have hsum_s_int : IntervalIntegrable
      (fun x => ∑ n ∈ Finset.Icc 1 m, Fs n x) volume 0 (Real.log m) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0]
    exact MeasureTheory.integrable_finset_sum _ (fun n hn => by
      have := (hper n hn).1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0] at this
      exact this)
  have hsum_a_int : IntervalIntegrable
      (fun x => ∑ n ∈ Finset.Icc 1 m, Fa n x) volume 0 (Real.log m) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0]
    exact MeasureTheory.integrable_finset_sum _ (fun n hn => by
      have := (hper n hn).2.1
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL0] at this
      exact this)
  calc (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / lam) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n => β n * (Real.exp x / lam) ≤ lam),
          ((n : ℝ) * (Real.exp x / lam)) *
            gd ((n : ℝ) * (Real.exp x / lam))|) =
      ∫ x in (0 : ℝ)..Real.log m, |∑ n ∈ Finset.Icc 1 m, Fs n x| := by
        apply intervalIntegral.integral_congr
        intro x _
        exact hpoint_eq x
    _ ≤ ∫ x in (0 : ℝ)..Real.log m, ∑ n ∈ Finset.Icc 1 m, Fa n x := by
        apply intervalIntegral.integral_mono_on hL0 hsum_s_int.abs
          hsum_a_int
        intro x _
        exact hpoint_le x
    _ = ∑ n ∈ Finset.Icc 1 m, ∫ x in (0 : ℝ)..Real.log m, Fa n x :=
        intervalIntegral.integral_finset_sum
          (fun n hn => (hper n hn).2.1)
    _ ≤ ∑ n ∈ Finset.Icc 1 m,
        (1 / Real.sqrt n) * (Real.sqrt Ccap * Real.sqrt E0) :=
        Finset.sum_le_sum (fun n hn => (hper n hn).2.2)
    _ = (∑ n ∈ Finset.Icc 1 m, (1 : ℝ) / Real.sqrt n) *
        (Real.sqrt Ccap * Real.sqrt E0) := by
        rw [Finset.sum_mul]
    _ ≤ 2 * Real.sqrt m * (Real.sqrt Ccap * Real.sqrt E0) := by
        apply mul_le_mul_of_nonneg_right (wc_sum_inv_sqrt_le m)
        positivity


/-! ## Node 3A: the interior consumer bound -/

/-- **Interior consumer bound.**  Every lattice contribution with
`y_n = n·u ≤ λ/2` (filter `2n·u ≤ λ`) is bounded by
`2λ·√(½·log(4/3))·√E0` — the companion constant is ABSOLUTE.
Under the node-1 rate `E0 ≤ C_E²/λ²` this is `≤ 2·√(½ log(4/3))·C_E ≈ 0.76·C_E`,
uniformly in the family. -/
theorem sturm_weighted_consumer_interior_bound
    (m : ℕ) (hm : 1 ≤ m)
    (gd : ℝ → ℝ) (hgd : ContinuousOn gd (Ioo 0 (Real.sqrt m)))
    (E0 : ℝ) (hE0 : 0 < E0)
    (hEint : IntegrableOn
      (fun y : ℝ => ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo 0 (Real.sqrt m)) volume)
    (hE : (∫ y in Ioo 0 (Real.sqrt m),
      ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2) ≤ E0) :
    (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / Real.sqrt m) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n : ℕ => 2 * (n : ℝ) * (Real.exp x / Real.sqrt m) ≤
              Real.sqrt m),
          ((n : ℝ) * (Real.exp x / Real.sqrt m)) *
            gd ((n : ℝ) * (Real.exp x / Real.sqrt m))|) ≤
      2 * Real.sqrt m *
        (Real.sqrt ((1 / 2) * Real.log (4 / 3)) * Real.sqrt E0) := by
  have h43 : (0 : ℝ) < (1 / 2) * Real.log (4 / 3) := by
    have := Real.log_pos (by norm_num : (1 : ℝ) < 4 / 3)
    linarith
  exact wc_core_bound m hm (fun n => 2 * (n : ℝ))
    (fun n hn => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      linarith)
    ((1 / 2) * Real.log (4 / 3)) h43
    (fun n hn => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
      have heq : (2 * (n : ℝ)) ^ 2 /
          ((2 * (n : ℝ)) ^ 2 - (n : ℝ) ^ 2) = 4 / 3 := by
        have h3 : (2 * (n : ℝ)) ^ 2 - (n : ℝ) ^ 2 = 3 * (n : ℝ) ^ 2 := by
          ring
        rw [h3]
        rw [div_eq_div_iff (by positivity) (by norm_num)]
        ring
      rw [heq])
    gd hgd E0 hE0 hEint hE

/-! ## Node 3B: the honest non-top `√log` rate -/

/-- **Non-top consumer bound.**  EVERY non-top lattice contribution
(`y_n = n·u ≤ λ − u`, filter `(n+1)·u ≤ λ`; the single uppermost point per
spacing is EXCLUDED) is bounded by `2λ·√(½·log(m+1))·√E0`.  Under the
node-1 rate this is `√2·C_E·√(log(m+1))` — the honest output of the
energy-only black box (the `√log` excess is REAL: killed-counterprofile
verdict c47b75a8).  The top lattice functional is the carried-open supplier
`W5_DEFECT_EDGE_TOP_LATTICE_BUDGET_BANDWIDTH_NEGLIGIBLE`. -/
theorem sturm_weighted_consumer_nonTop_sqrtLog_bound
    (m : ℕ) (hm : 1 ≤ m)
    (gd : ℝ → ℝ) (hgd : ContinuousOn gd (Ioo 0 (Real.sqrt m)))
    (E0 : ℝ) (hE0 : 0 < E0)
    (hEint : IntegrableOn
      (fun y : ℝ => ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo 0 (Real.sqrt m)) volume)
    (hE : (∫ y in Ioo 0 (Real.sqrt m),
      ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2) ≤ E0) :
    (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / Real.sqrt m) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n : ℕ => ((n : ℝ) + 1) * (Real.exp x / Real.sqrt m) ≤
              Real.sqrt m),
          ((n : ℝ) * (Real.exp x / Real.sqrt m)) *
            gd ((n : ℝ) * (Real.exp x / Real.sqrt m))|) ≤
      2 * Real.sqrt m *
        (Real.sqrt ((1 / 2) * Real.log ((m : ℝ) + 1)) * Real.sqrt E0) := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog : (0 : ℝ) < (1 / 2) * Real.log ((m : ℝ) + 1) := by
    have := Real.log_pos (by linarith : (1 : ℝ) < (m : ℝ) + 1)
    linarith
  exact wc_core_bound m hm (fun n => (n : ℝ) + 1)
    (fun n _ => lt_add_one _)
    ((1 / 2) * Real.log ((m : ℝ) + 1)) hlog
    (fun n hn => by
      obtain ⟨hn1, hnm⟩ := Finset.mem_Icc.mp hn
      have h1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have h2 : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
      have h3 : ((n : ℝ) + 1) ^ 2 - (n : ℝ) ^ 2 = 2 * (n : ℝ) + 1 := by
        ring
      rw [h3]
      have hratio_pos : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) := by
        positivity
      have hratio_le : ((n : ℝ) + 1) ^ 2 / (2 * (n : ℝ) + 1) ≤
          (m : ℝ) + 1 := by
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      have := Real.log_le_log hratio_pos hratio_le
      linarith)
    gd hgd E0 hE0 hEint hE

/-! ## Rate corollaries under the node-1 energy rate `E0 ≤ C_E²/λ²` -/

/-- Interior rate corollary: with the node-1 energy rate the interior
budget is `≤ 2·√(½ log(4/3))·C_E` — UNIFORM in the family. -/
theorem sturm_weighted_consumer_interior_rate
    (m : ℕ) (hm : 1 ≤ m)
    (gd : ℝ → ℝ) (hgd : ContinuousOn gd (Ioo 0 (Real.sqrt m)))
    (CE : ℝ) (hCE : 0 < CE)
    (hEint : IntegrableOn
      (fun y : ℝ => ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo 0 (Real.sqrt m)) volume)
    (hE : (∫ y in Ioo 0 (Real.sqrt m),
      ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2) ≤
        CE ^ 2 / (Real.sqrt m) ^ 2) :
    (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / Real.sqrt m) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n : ℕ => 2 * (n : ℝ) * (Real.exp x / Real.sqrt m) ≤
              Real.sqrt m),
          ((n : ℝ) * (Real.exp x / Real.sqrt m)) *
            gd ((n : ℝ) * (Real.exp x / Real.sqrt m))|) ≤
      2 * (Real.sqrt ((1 / 2) * Real.log (4 / 3)) * CE) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlam0 : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hE0 : (0 : ℝ) < CE ^ 2 / (Real.sqrt m) ^ 2 := by positivity
  have h := sturm_weighted_consumer_interior_bound m hm gd hgd
    (CE ^ 2 / (Real.sqrt m) ^ 2) hE0 hEint hE
  have hsqrtE : Real.sqrt (CE ^ 2 / (Real.sqrt m) ^ 2) =
      CE / Real.sqrt m := by
    rw [← div_pow]
    exact Real.sqrt_sq (by positivity)
  rw [hsqrtE] at h
  refine h.trans (le_of_eq ?_)
  field_simp

/-- Non-top rate corollary: with the node-1 energy rate the full non-top
budget is `≤ 2·√(½ log(m+1))·C_E = √2·C_E·√(log(m+1))` — the honest
`√log` rate consumed downstream by the rate-aware receiver together with
`bandwidth ≥ π√(k+2)`. -/
theorem sturm_weighted_consumer_nonTop_rate
    (m : ℕ) (hm : 1 ≤ m)
    (gd : ℝ → ℝ) (hgd : ContinuousOn gd (Ioo 0 (Real.sqrt m)))
    (CE : ℝ) (hCE : 0 < CE)
    (hEint : IntegrableOn
      (fun y : ℝ => ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo 0 (Real.sqrt m)) volume)
    (hE : (∫ y in Ioo 0 (Real.sqrt m),
      ((Real.sqrt m) ^ 2 - y ^ 2) * gd y ^ 2) ≤
        CE ^ 2 / (Real.sqrt m) ^ 2) :
    (∫ x in (0 : ℝ)..Real.log m,
      Real.sqrt (Real.exp x / Real.sqrt m) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n : ℕ => ((n : ℝ) + 1) * (Real.exp x / Real.sqrt m) ≤
              Real.sqrt m),
          ((n : ℝ) * (Real.exp x / Real.sqrt m)) *
            gd ((n : ℝ) * (Real.exp x / Real.sqrt m))|) ≤
      2 * (Real.sqrt ((1 / 2) * Real.log ((m : ℝ) + 1)) * CE) := by
  have hmR : (0 : ℝ) < (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    linarith
  have hlam0 : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hmR
  have hE0 : (0 : ℝ) < CE ^ 2 / (Real.sqrt m) ^ 2 := by positivity
  have h := sturm_weighted_consumer_nonTop_sqrtLog_bound m hm gd hgd
    (CE ^ 2 / (Real.sqrt m) ^ 2) hE0 hEint hE
  have hsqrtE : Real.sqrt (CE ^ 2 / (Real.sqrt m) ^ 2) =
      CE / Real.sqrt m := by
    rw [← div_pow]
    exact Real.sqrt_sq (by positivity)
  rw [hsqrtE] at h
  refine h.trans (le_of_eq ?_)
  field_simp

#print axioms wc_sum_inv_sqrt_le
#print axioms wc_companion_integral_le
#print axioms wc_pointwise_amgm
#print axioms wc_core_bound
#print axioms sturm_weighted_consumer_interior_bound
#print axioms sturm_weighted_consumer_nonTop_sqrtLog_bound
#print axioms sturm_weighted_consumer_interior_rate
#print axioms sturm_weighted_consumer_nonTop_rate

end Q3.RouteB.D0Pstar
