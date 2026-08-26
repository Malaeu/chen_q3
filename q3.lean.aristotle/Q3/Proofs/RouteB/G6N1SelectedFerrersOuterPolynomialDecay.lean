import Q3.Proofs.RouteB.G6N1SturmDefectTruncatedEnergy
import Q3.Proofs.RouteB.G6N1SelectedFerrersPaperParameterDictionary
import Q3.Proofs.RouteB.G6N1CenterAnchorScalarLock
import Q3.Proofs.RouteB.G6N1ParabolicCylinderD0D4Exact
import Q3.Proofs.RouteB.D0Mode4ClassicalCarrierHeadUpper

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 1200000

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-!
# Outer polynomial decay of the committed even prolate Ferrers modes
(verdict fce7669c, REQ-2026-08-26-D)

Core mechanism (the judge's flux monotonicity, quantified): the energy
function `E(y) = ((λ²−y²)·φ′(y))·φ(y)` satisfies, by the committed physical
prolate ODE, `E′ = q̃·φ² + (λ²−y²)·φ′²` with `q̃(y) = (2πλy)² − θ ≥ λ⁴` on
the outer region `y ≥ λ/4` (given the eigenvalue window `θ ≤ λ⁴`).  The
committed zero-flux transport gives `E(λ⁻) = 0`, hence `E ≤ 0` on the outer
region: `φ²` is NONINCREASING there — no zero-freeness needed, no cutoff.
Quantitatively, with `M(y) = ∫_y^λ φ²` and `w = λ/32`,

  `λ⁴·M(y) ≤ −E(y) ≤ λ²·(−φφ′)(y)` pointwise, which integrates to
  `M(a+w) ≤ M(a−w)/(2λ²w²) = 512·λ⁻⁴·M(a−w)`.

Three steps of this recursion replace the Caccioppoli shells and give
outer mass `O(λ⁻¹²)`; the monotone conversion on a `λ/32`-interval gives
`sup_{[λ/2,λ]} |φ| ≤ 2¹⁶·√B·λ^{−13/2} ≤ 2¹⁶·√B·λ⁻⁶`.

Forbidden moves honored: no FTC through the degenerate endpoint weight, no
derivative sup-norm, no `δ″`, no new analytic hypothesis, no numerics.
-/

variable {mProject K : ℕ} {Λ : ℝ}

/-- **Core outer polynomial decay** for the raw committed physical Ferrers
series: with the eigenvalue window `Λ + G ≤ λ⁴` and an `L²` mass bound `B`
on the half-window, the series is bounded by `2¹⁶·√B/λ⁶` on `[λ/2, λ]`. -/
theorem sturm_outer_polynomial_decay
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hθ : Λ + mode4JacobiG mProject ≤ (Real.sqrt mProject) ^ 4)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : (∫ y in Ioo 0 (Real.sqrt mProject),
      (mode4PhysicalFerrersSeries mProject S.coefficients y) ^ 2) ≤ B) :
    ∀ y ∈ Icc (Real.sqrt mProject / 2) (Real.sqrt mProject),
      |mode4PhysicalFerrersSeries mProject S.coefficients y| ≤
        65536 * Real.sqrt B / (Real.sqrt mProject) ^ 6 := by
  set lam := Real.sqrt (mProject : ℝ) with hlamdef
  set φ : ℝ → ℝ := mode4PhysicalFerrersSeries mProject S.coefficients
    with hφdef
  set φd : ℝ → ℝ :=
    mode4PhysicalFerrersFirstDerivativeSeries mProject S.coefficients
    with hφddef
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hm2 : (2 : ℝ) ≤ (mProject : ℝ) := by exact_mod_cast hm
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hsq : lam ^ 2 = (mProject : ℝ) := Real.sq_sqrt hmR.le
  -- committed continuity and derivatives
  have hφcont : ContinuousOn φ (Icc (-lam) lam) :=
    sturm_physSeries_continuousOn_closed S hm
  have hφd_at : ∀ x ∈ Ioo (-lam) lam, HasDerivAt φ (φd x) x := fun x hx =>
    S.physicalFerrersSeries_hasDerivAt_firstDerivativeSeries hm hx
  have hφd_cont : ContinuousOn φd (Ioo (-lam) lam) := by
    intro x hx
    exact ((S.physicalFirstDerivativeSeries_hasDerivAt_secondDerivativeSeries
      hm hx).continuousAt).continuousWithinAt
  -- the sup bound on the closed window
  obtain ⟨Cs, hCs⟩ := (isCompact_Icc (a := -lam) (b := lam)).exists_bound_of_continuousOn
    hφcont
  have hCs0 : (0 : ℝ) ≤ Cs := le_trans (norm_nonneg _)
    (hCs 0 ⟨by linarith, by linarith⟩)
  -- outer region inclusion helpers
  have hquarter : lam / 4 < lam := by linarith
  have hOuterSub : Icc (lam / 4) lam ⊆ Icc (-lam) lam := by
    intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  have hOuterOpen : Ico (lam / 4) lam ⊆ Ioo (-lam) lam := by
    intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  -- the energy function and its derivative
  set E : ℝ → ℝ := fun y => ((lam ^ 2 - y ^ 2) * φd y) * φ y with hEdef
  have hE_at : ∀ x ∈ Ioo (-lam) lam,
      HasDerivAt E
        (((2 * Real.pi * lam * x) ^ 2 * φ x -
            (Λ + mode4JacobiG mProject) * φ x) * φ x +
          ((lam ^ 2 - x ^ 2) * φd x) * φd x) x := fun x hx =>
    (sturm_mode_flux_hasDerivAt S hm hx).mul (hφd_at x hx)
  -- E′ dominates λ⁴·φ² on the outer region
  have hEd_ge : ∀ x ∈ Ico (lam / 4) lam,
      lam ^ 4 * φ x ^ 2 ≤
        ((2 * Real.pi * lam * x) ^ 2 * φ x -
            (Λ + mode4JacobiG mProject) * φ x) * φ x +
          ((lam ^ 2 - x ^ 2) * φd x) * φd x := by
    intro x hx
    have hx2 : lam ^ 2 / 16 ≤ x ^ 2 := by nlinarith [hx.1, hlam0]
    have hpot : lam ^ 4 ≤ (2 * Real.pi * lam * x) ^ 2 -
        (Λ + mode4JacobiG mProject) := by
      have hpi2 : (9 : ℝ) ≤ Real.pi ^ 2 := by
        nlinarith [Real.pi_gt_three]
      have h1 : (2 * Real.pi * lam * x) ^ 2 =
          4 * Real.pi ^ 2 * lam ^ 2 * x ^ 2 := by ring
      have h2 : 4 * (9 : ℝ) * lam ^ 2 * (lam ^ 2 / 16) ≤
          4 * Real.pi ^ 2 * lam ^ 2 * x ^ 2 := by
        have ha : (0:ℝ) ≤ 4 * lam ^ 2 * (lam ^ 2 / 16) := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hx2
            (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2 * lam ^ 2),
          mul_le_mul_of_nonneg_right hpi2 ha]
      nlinarith [hθ, h2, h1]
    have hw : (0 : ℝ) ≤ (lam ^ 2 - x ^ 2) := by nlinarith [hx.2, hx.1, hlam0]
    have h2 : ((2 * Real.pi * lam * x) ^ 2 * φ x -
          (Λ + mode4JacobiG mProject) * φ x) * φ x =
        ((2 * Real.pi * lam * x) ^ 2 - (Λ + mode4JacobiG mProject)) *
          φ x ^ 2 := by ring
    have h3 : ((lam ^ 2 - x ^ 2) * φd x) * φd x =
        (lam ^ 2 - x ^ 2) * φd x ^ 2 := by ring
    rw [h2, h3]
    nlinarith [mul_le_mul_of_nonneg_right hpot (sq_nonneg (φ x)),
      mul_nonneg hw (sq_nonneg (φd x))]
  -- flux and mode limits at the top endpoint
  have hflux_top := sturm_mode_flux_tendsto_zero_top S hm hK hsep hΛ
  have hIooIio :
      nhdsWithin lam (Ioo (-lam) lam) = nhdsWithin lam (Iio lam) :=
    nhdsWithin_Ioo_eq_nhdsLT (by linarith)
  have hφ_top : Tendsto φ (nhdsWithin lam (Iio lam)) (𝓝 (φ lam)) := by
    have hcw : Tendsto φ (nhdsWithin lam (Icc (-lam) lam)) (𝓝 (φ lam)) :=
      hφcont lam ⟨by linarith, le_refl _⟩
    rw [← hIooIio]
    exact hcw.mono_left (nhdsWithin_mono _ Ioo_subset_Icc_self)
  have hE_top : Tendsto E (nhdsWithin lam (Iio lam)) (𝓝 0) := by
    have h := hflux_top.mul hφ_top
    rw [zero_mul] at h
    exact h
  -- the outer mass function
  set Mf : ℝ → ℝ := fun t => ∫ s in t..lam, φ s ^ 2 with hMdef
  have hg2int : ∀ a b : ℝ, a ∈ Icc (-lam) lam → b ∈ Icc (-lam) lam →
      IntervalIntegrable (fun s => φ s ^ 2) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply (hφcont.pow 2).mono
    intro t ht
    rcases le_total a b with h | h
    · rw [uIcc_of_le h] at ht
      exact ⟨le_trans ha.1 ht.1, le_trans ht.2 hb.2⟩
    · rw [uIcc_of_ge h] at ht
      exact ⟨le_trans hb.1 ht.1, le_trans ht.2 ha.2⟩
  have hM_nonneg : ∀ t ∈ Icc (lam / 4) lam, 0 ≤ Mf t := by
    intro t ht
    apply intervalIntegral.integral_nonneg ht.2
    intro s _
    positivity
  -- L2: the pointwise mass bound λ⁴·M(y) ≤ −E(y) on the outer region
  have hMass : ∀ y ∈ Ico (lam / 4) lam, lam ^ 4 * Mf y ≤ -E y := by
    intro y hy
    -- the truncated inequality
    have hL1 : ∀ z ∈ Ico y lam,
        lam ^ 4 * (∫ s in y..z, φ s ^ 2) ≤ E z - E y := by
      intro z hz
      have hyz : y ≤ z := hz.1
      have hsubIco : Icc y z ⊆ Ico (lam / 4) lam := by
        intro t ht
        exact ⟨le_trans hy.1 ht.1, lt_of_le_of_lt ht.2 hz.2⟩
      have hsubIoo : Icc y z ⊆ Ioo (-lam) lam := fun t ht =>
        hOuterOpen (hsubIco ht)
      have hEd_cont : ContinuousOn (fun x =>
          ((2 * Real.pi * lam * x) ^ 2 * φ x -
              (Λ + mode4JacobiG mProject) * φ x) * φ x +
            ((lam ^ 2 - x ^ 2) * φd x) * φd x) (Icc y z) := by
        have hφc : ContinuousOn φ (Icc y z) :=
          hφcont.mono (fun t ht =>
            hOuterSub (Ico_subset_Icc_self (hsubIco ht)))
        have hφdc : ContinuousOn φd (Icc y z) := hφd_cont.mono hsubIoo
        apply ContinuousOn.add
        · apply ContinuousOn.mul _ hφc
          apply ContinuousOn.sub
          · apply ContinuousOn.mul _ hφc
            fun_prop
          · exact continuousOn_const.mul hφc
        · exact ((continuousOn_const.sub
            (continuous_pow 2).continuousOn).mul hφdc).mul hφdc
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := E)
        (fun t ht => by
          rw [uIcc_of_le hyz] at ht
          exact hE_at t (hsubIoo ht))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hyz]
          exact hEd_cont)
      rw [← hftc]
      have hmono := intervalIntegral.integral_mono_on hyz
        (((hg2int y z
          (hOuterSub (Ico_subset_Icc_self (hsubIco ⟨le_refl _, hyz⟩)))
          (hOuterSub (Ico_subset_Icc_self
            (hsubIco ⟨hyz, le_refl _⟩)))).const_mul (lam ^ 4)))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hyz]
          exact hEd_cont)
        (fun t ht => hEd_ge t (hsubIco ht))
      calc lam ^ 4 * ∫ s in y..z, φ s ^ 2
          = ∫ s in y..z, lam ^ 4 * φ s ^ 2 :=
            (intervalIntegral.integral_const_mul _ _).symm
        _ ≤ ∫ s in y..z,
            (((2 * Real.pi * lam * s) ^ 2 * φ s -
                (Λ + mode4JacobiG mProject) * φ s) * φ s +
              ((lam ^ 2 - s ^ 2) * φd s) * φd s) := hmono
    -- pass to the limit z → λ⁻
    have hOooMem : Ioo (lam / 4) lam ∈ nhdsWithin lam (Iio lam) := by
      apply mem_nhdsWithin.mpr
      exact ⟨Ioi (lam / 4), isOpen_Ioi, hquarter, fun t ht => ⟨ht.1, ht.2⟩⟩
    have hrem : Tendsto (fun z => ∫ s in z..lam, φ s ^ 2)
        (nhdsWithin lam (Iio lam)) (𝓝 0) := by
      apply squeeze_zero' (g := fun z => Cs ^ 2 * (lam - z))
      · filter_upwards [self_mem_nhdsWithin] with z hz
        apply intervalIntegral.integral_nonneg (le_of_lt hz)
        intro s _
        positivity
      · filter_upwards [hOooMem] with z hz
        have hzmem : z ∈ Icc (-lam) lam :=
          hOuterSub (Ico_subset_Icc_self ⟨hz.1.le, hz.2⟩)
        have hmono := intervalIntegral.integral_mono_on hz.2.le
          (hg2int z lam hzmem ⟨by linarith, le_refl _⟩)
          (intervalIntegral.intervalIntegrable_const (c := Cs ^ 2))
          (fun s hs => by
            have hsmem : s ∈ Icc (-lam) lam :=
              ⟨le_trans hzmem.1 hs.1, hs.2⟩
            have := hCs s hsmem
            have habs : |φ s| ≤ Cs := by
              rwa [Real.norm_eq_abs] at this
            have h2 := abs_le.1 habs
            nlinarith [h2.1, h2.2])
        calc (∫ s in z..lam, φ s ^ 2) ≤ ∫ _ in z..lam, Cs ^ 2 := hmono
          _ = (lam - z) • Cs ^ 2 := intervalIntegral.integral_const _
          _ = Cs ^ 2 * (lam - z) := by rw [smul_eq_mul]; ring
      · have h : Tendsto (fun z : ℝ => Cs ^ 2 * (lam - z)) (𝓝 lam)
            (𝓝 (Cs ^ 2 * (lam - lam))) :=
          (continuous_const.mul
            (continuous_const.sub continuous_id')).tendsto lam
        rw [sub_self, mul_zero] at h
        exact h.mono_left nhdsWithin_le_nhds
    have hT1 : Tendsto (fun z => lam ^ 4 * ∫ s in y..z, φ s ^ 2)
        (nhdsWithin lam (Iio lam)) (𝓝 (lam ^ 4 * Mf y)) := by
      have hyIcc : y ∈ Icc (-lam) lam :=
        hOuterSub (Ico_subset_Icc_self hy)
      have hbase : Tendsto (fun z => lam ^ 4 *
          (Mf y - ∫ s in z..lam, φ s ^ 2))
          (nhdsWithin lam (Iio lam)) (𝓝 (lam ^ 4 * (Mf y - 0))) :=
        (tendsto_const_nhds.sub hrem).const_mul _
      rw [sub_zero] at hbase
      apply hbase.congr'
      have hyMem : Ioo y lam ∈ nhdsWithin lam (Iio lam) := by
        apply mem_nhdsWithin.mpr
        exact ⟨Ioi y, isOpen_Ioi, hy.2, fun t ht => ⟨ht.1, ht.2⟩⟩
      filter_upwards [hyMem] with z hz
      have hzIcc : z ∈ Icc (-lam) lam :=
        ⟨by linarith [hyIcc.1, hz.1], hz.2.le⟩
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hg2int y z hyIcc hzIcc)
        (hg2int z lam hzIcc ⟨by linarith, le_refl _⟩)
      rw [hMdef]
      simp only
      rw [← hadd]
      ring
    have hT2 : Tendsto (fun z => E z - E y)
        (nhdsWithin lam (Iio lam)) (𝓝 (0 - E y)) :=
      hE_top.sub_const _
    have hev : ∀ᶠ z in nhdsWithin lam (Iio lam),
        lam ^ 4 * ∫ s in y..z, φ s ^ 2 ≤ E z - E y := by
      have hyMem : Ioo y lam ∈ nhdsWithin lam (Iio lam) := by
        apply mem_nhdsWithin.mpr
        exact ⟨Ioi y, isOpen_Ioi, hy.2, fun t ht => ⟨ht.1, ht.2⟩⟩
      filter_upwards [hyMem] with z hz
      exact hL1 z ⟨hz.1.le, hz.2⟩
    have := le_of_tendsto_of_tendsto hT1 hT2 hev
    linarith [this]
  -- E is nonpositive on the outer region, hence φ² is antitone there
  have hE_nonpos : ∀ y ∈ Ico (lam / 4) lam, E y ≤ 0 := by
    intro y hy
    have h1 := hMass y hy
    have h2 := hM_nonneg y (Ico_subset_Icc_self hy)
    nlinarith [mul_nonneg (by positivity : (0:ℝ) ≤ lam ^ 4) h2]
  have hφφd_nonpos : ∀ x ∈ Ico (lam / 4) lam, φ x * φd x ≤ 0 := by
    intro x hx
    have hEx := hE_nonpos x hx
    have hw : (0 : ℝ) < lam ^ 2 - x ^ 2 := by
      nlinarith [hx.2, hx.1, hlam0]
    simp only [hEdef] at hEx
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos hw hcon]
  have hg_anti : AntitoneOn (fun t => φ t ^ 2) (Icc (lam / 4) lam) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · exact (hφcont.mono hOuterSub).pow 2
    · rw [interior_Icc]
      intro x hx
      exact (((hφd_at x (hOuterOpen ⟨hx.1.le, hx.2⟩)).pow
        2).differentiableAt).differentiableWithinAt
    · rw [interior_Icc]
      intro x hx
      have hgd : HasDerivAt (fun t => φ t ^ 2)
          ((2 : ℕ) * φ x ^ 1 * φd x) x :=
        (hφd_at x (hOuterOpen ⟨hx.1.le, hx.2⟩)).pow 2
      rw [hgd.deriv]
      have h2 := hφφd_nonpos x ⟨hx.1.le, hx.2⟩
      simp only [Nat.cast_ofNat, pow_one]
      nlinarith [h2]
  -- continuity and antitonicity of the outer mass
  have hMfcont : ContinuousOn Mf (Icc (lam / 4) lam) := by
    have hprim := intervalIntegral.continuousOn_primitive_interval'
      (f := fun s => φ s ^ 2) (μ := volume)
      (b₁ := lam / 4) (b₂ := lam) (a := lam)
      (hg2int (lam / 4) lam ⟨by linarith, by linarith⟩
        ⟨by linarith, le_refl _⟩)
      (by rw [uIcc_of_le hquarter.le]; exact ⟨hquarter.le, le_refl _⟩)
    rw [uIcc_of_le hquarter.le] at hprim
    apply (hprim.neg).congr
    intro b _
    rw [hMdef]
    simp only
    rw [← intervalIntegral.integral_symm]
  have hMf_anti : ∀ a b : ℝ, lam / 4 ≤ a → a ≤ b → b ≤ lam →
      Mf b ≤ Mf a := by
    intro a b ha hab hb
    have haIcc : a ∈ Icc (-lam) lam := ⟨by linarith, by linarith⟩
    have hbIcc : b ∈ Icc (-lam) lam := ⟨by linarith, hb⟩
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hg2int a b haIcc hbIcc)
      (hg2int b lam hbIcc ⟨by linarith, le_refl _⟩)
    have hnn : (0:ℝ) ≤ ∫ s in a..b, φ s ^ 2 := by
      apply intervalIntegral.integral_nonneg hab
      intro s _
      positivity
    rw [hMdef]
    simp only
    linarith [hadd, hnn]
  -- the block-mean estimate: one recursion step of the outer mass
  have hstep : ∀ a : ℝ, lam / 4 + lam / 32 ≤ a → a + lam / 32 ≤ lam / 2 →
      Mf (a + lam / 32) ≤ 512 / lam ^ 4 * Mf (a - lam / 32) := by
    intro a ha1 ha2
    have hw0 : (0 : ℝ) < lam / 32 := by positivity
    have hmem_am : a - lam / 32 ∈ Icc (lam / 4) lam := by
      constructor <;> nlinarith
    have hmem_a : a ∈ Icc (lam / 4) lam := by
      constructor <;> nlinarith
    have hmem_ap : a + lam / 32 ∈ Icc (lam / 4) lam := by
      constructor <;> nlinarith
    -- (i) the value at a is paid by the mass on the left block
    have hga : φ a ^ 2 * (lam / 32) ≤ Mf (a - lam / 32) := by
      have hadd := intervalIntegral.integral_add_adjacent_intervals
        (hg2int (a - lam / 32) a (hOuterSub hmem_am) (hOuterSub hmem_a))
        (hg2int a lam (hOuterSub hmem_a) ⟨by linarith, le_refl _⟩)
      have hmono := intervalIntegral.integral_mono_on
        (by linarith : a - lam / 32 ≤ a)
        (intervalIntegral.intervalIntegrable_const (c := φ a ^ 2))
        (hg2int (a - lam / 32) a (hOuterSub hmem_am) (hOuterSub hmem_a))
        (fun t ht => by
          have htmem : t ∈ Icc (lam / 4) lam :=
            ⟨by linarith [ht.1, hmem_am.1], by linarith [ht.2, hmem_a.2]⟩
          exact hg_anti htmem hmem_a ht.2)
      have hconst : (∫ _ in (a - lam / 32)..a, φ a ^ 2) =
          (lam / 32) * φ a ^ 2 := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring_nf
      have hMnn := hM_nonneg a hmem_a
      rw [hMdef]
      simp only
      rw [hconst] at hmono
      have : (∫ s in (a - lam/32)..a, φ s ^ 2) =
          (∫ s in (a - lam/32)..lam, φ s ^ 2) -
          (∫ s in a..lam, φ s ^ 2) := by linarith [hadd]
      nlinarith [hmono, hM_nonneg a hmem_a, this]
    -- (ii)-(iv): integrate the pointwise mass bound over the right block
    have hsubIoo2 : Icc a (a + lam / 32) ⊆ Ioo (-lam) lam := by
      intro t ht
      constructor <;> nlinarith [ht.1, ht.2, hmem_a.1]
    have hφφd_cont : ContinuousOn (fun t => -(φ t * φd t) / lam ^ 2)
        (Icc a (a + lam / 32)) := by
      apply ContinuousOn.div_const
      apply ContinuousOn.neg
      apply ContinuousOn.mul
      · exact hφcont.mono (fun t ht => hOuterSub
          ⟨by linarith [ht.1, hmem_a.1], by linarith [ht.2, hmem_ap.2]⟩)
      · exact hφd_cont.mono hsubIoo2
    have hint23 : (∫ t in a..(a + lam / 32), Mf t) ≤
        (φ a ^ 2 - φ (a + lam / 32) ^ 2) / (2 * lam ^ 2) := by
      have hmono := intervalIntegral.integral_mono_on
        (by linarith : a ≤ a + lam / 32)
        (by
          apply ContinuousOn.intervalIntegrable (μ := volume)
          rw [uIcc_of_le (by linarith : a ≤ a + lam / 32)]
          exact hMfcont.mono (fun t ht =>
            ⟨by linarith [ht.1, hmem_a.1], by linarith [ht.2, hmem_ap.2]⟩))
        (by
          apply ContinuousOn.intervalIntegrable (μ := volume)
          rw [uIcc_of_le (by linarith : a ≤ a + lam / 32)]
          exact hφφd_cont)
        (fun t ht => by
          have htIco : t ∈ Ico (lam / 4) lam :=
            ⟨by linarith [ht.1, hmem_a.1],
             by nlinarith [ht.2, hmem_ap.2, hlam0]⟩
          have h1 := hMass t htIco
          have h2 := hφφd_nonpos t htIco
          have hw : (0:ℝ) ≤ lam ^ 2 - t ^ 2 := by
            nlinarith [htIco.2, htIco.1, hlam0]
          simp only [hEdef] at h1
          rw [le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 2)]
          nlinarith [mul_le_mul_of_nonneg_right
            (show lam ^ 2 - t ^ 2 ≤ lam ^ 2 by nlinarith [sq_nonneg t])
            (show (0:ℝ) ≤ -(φd t * φ t) by nlinarith [h2])])
      have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun t => φ t ^ 2)
        (f' := fun t => 2 * φ t ^ 1 * φd t)
        (a := a) (b := a + lam / 32)
        (fun t ht => by
          rw [uIcc_of_le (by linarith : a ≤ a + lam / 32)] at ht
          exact ((hφd_at t (hsubIoo2 ht)).pow 2).congr_deriv (by
            push_cast
            ring))
        (by
          apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le (by linarith : a ≤ a + lam / 32)]
          apply ContinuousOn.mul
          · apply ContinuousOn.mul continuousOn_const
            exact (hφcont.mono (fun t ht => hOuterSub
              ⟨by linarith [ht.1, hmem_a.1],
               by linarith [ht.2, hmem_ap.2]⟩)).pow 1
          · exact hφd_cont.mono hsubIoo2)
      have heqint : (∫ t in a..(a + lam / 32), -(φ t * φd t) / lam ^ 2) =
          (φ a ^ 2 - φ (a + lam / 32) ^ 2) / (2 * lam ^ 2) := by
        have hrw : (fun t => -(φ t * φd t) / lam ^ 2) =
            fun t => (-(1 / (2 * lam ^ 2))) * (2 * φ t ^ 1 * φd t) := by
          funext t
          field_simp
        rw [hrw, intervalIntegral.integral_const_mul, hftc]
        ring
      rw [heqint] at hmono
      exact hmono
    have hlow : (lam / 32) * Mf (a + lam / 32) ≤
        ∫ t in a..(a + lam / 32), Mf t := by
      have hmono := intervalIntegral.integral_mono_on
        (by linarith : a ≤ a + lam / 32)
        (intervalIntegral.intervalIntegrable_const (c := Mf (a + lam / 32)))
        (by
          apply ContinuousOn.intervalIntegrable (μ := volume)
          rw [uIcc_of_le (by linarith : a ≤ a + lam / 32)]
          exact hMfcont.mono (fun t ht =>
            ⟨by linarith [ht.1, hmem_a.1], by linarith [ht.2, hmem_ap.2]⟩))
        (fun t ht => hMf_anti t (a + lam / 32)
          (by linarith [ht.1, hmem_a.1]) ht.2 hmem_ap.2)
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      calc (lam / 32) * Mf (a + lam / 32) =
          (a + lam / 32 - a) * Mf (a + lam / 32) := by ring_nf
        _ ≤ ∫ t in a..(a + lam / 32), Mf t := hmono
    -- assemble the recursion step
    have hgap_nn : (0:ℝ) ≤ φ (a + lam / 32) ^ 2 := sq_nonneg _
    have hchain1 : 2 * lam ^ 2 * ((lam / 32) * Mf (a + lam / 32)) ≤
        φ a ^ 2 := by
      have h1 := hlow.trans hint23
      rw [le_div_iff₀ (by positivity : (0:ℝ) < 2 * lam ^ 2)] at h1
      nlinarith [h1, hgap_nn]
    have hchain2 : 2 * lam ^ 2 * ((lam / 32) * Mf (a + lam / 32)) *
        (lam / 32) ≤ Mf (a - lam / 32) := by
      calc 2 * lam ^ 2 * ((lam / 32) * Mf (a + lam / 32)) * (lam / 32) ≤
          φ a ^ 2 * (lam / 32) :=
            mul_le_mul_of_nonneg_right hchain1 hw0.le
        _ ≤ Mf (a - lam / 32) := hga
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < lam ^ 4)]
    nlinarith [hchain2]
  -- iterate the three precommitted steps from λ/4
  have hMB : Mf (8 * lam / 32) ≤ B := by
    have h8 : (8 : ℝ) * lam / 32 = lam / 4 := by ring
    rw [h8, hMdef]
    simp only
    rw [intervalIntegral.integral_of_le (by linarith : lam / 4 ≤ lam),
      MeasureTheory.integral_Ioc_eq_integral_Ioo]
    have hIntBig : IntegrableOn (fun s => φ s ^ 2) (Ioo 0 lam) volume := by
      apply MeasureTheory.IntegrableOn.mono_set
        (t := Icc (-lam) lam)
      · exact ((hφcont.pow 2).integrableOn_compact isCompact_Icc)
      · intro t ht
        exact ⟨by linarith [ht.1], ht.2.le⟩
    have hmono := MeasureTheory.setIntegral_mono_set hIntBig
      (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo]
          with t _
        positivity)
      (HasSubset.Subset.eventuallyLE
        (by
          intro t ht
          exact ⟨by linarith [ht.1, hlam0], ht.2⟩ :
          Ioo (lam / 4) lam ⊆ Ioo 0 lam))
    exact hmono.trans hB
  have hfac_nn : (0:ℝ) ≤ 512 / lam ^ 4 := by positivity
  have hs1 := hstep (9 * lam / 32) (by linarith) (by nlinarith [hlam0.le])
  have hs2 := hstep (11 * lam / 32) (by nlinarith [hlam0.le])
    (by nlinarith [hlam0.le])
  have hs3 := hstep (13 * lam / 32) (by nlinarith [hlam0.le])
    (by nlinarith [hlam0.le])
  rw [show (9:ℝ) * lam / 32 + lam / 32 = 10 * lam / 32 by ring,
    show (9:ℝ) * lam / 32 - lam / 32 = 8 * lam / 32 by ring] at hs1
  rw [show (11:ℝ) * lam / 32 + lam / 32 = 12 * lam / 32 by ring,
    show (11:ℝ) * lam / 32 - lam / 32 = 10 * lam / 32 by ring] at hs2
  rw [show (13:ℝ) * lam / 32 + lam / 32 = 14 * lam / 32 by ring,
    show (13:ℝ) * lam / 32 - lam / 32 = 12 * lam / 32 by ring] at hs3
  have hM14 : Mf (14 * lam / 32) ≤ (512 / lam ^ 4) ^ 3 * B := by
    have hM10nn : 0 ≤ Mf (10 * lam / 32) :=
      hM_nonneg _ ⟨by nlinarith, by nlinarith⟩
    have hM12nn : 0 ≤ Mf (12 * lam / 32) :=
      hM_nonneg _ ⟨by nlinarith, by nlinarith⟩
    calc Mf (14 * lam / 32) ≤ 512 / lam ^ 4 * Mf (12 * lam / 32) := hs3
      _ ≤ 512 / lam ^ 4 * (512 / lam ^ 4 * Mf (10 * lam / 32)) := by
          apply mul_le_mul_of_nonneg_left hs2 hfac_nn
      _ ≤ 512 / lam ^ 4 * (512 / lam ^ 4 *
          (512 / lam ^ 4 * Mf (8 * lam / 32))) := by
          apply mul_le_mul_of_nonneg_left _ hfac_nn
          apply mul_le_mul_of_nonneg_left hs1 hfac_nn
      _ ≤ 512 / lam ^ 4 * (512 / lam ^ 4 * (512 / lam ^ 4 * B)) := by
          apply mul_le_mul_of_nonneg_left _ hfac_nn
          apply mul_le_mul_of_nonneg_left _ hfac_nn
          apply mul_le_mul_of_nonneg_left hMB hfac_nn
      _ = (512 / lam ^ 4) ^ 3 * B := by ring
  -- transfer the mass to the value at λ/2 and finish
  have hga15 : φ (15 * lam / 32) ^ 2 * (lam / 32) ≤ Mf (14 * lam / 32) := by
    have hmem_am : (15:ℝ) * lam / 32 - lam / 32 ∈ Icc (lam / 4) lam := by
      constructor <;> nlinarith
    have hmem_a : (15:ℝ) * lam / 32 ∈ Icc (lam / 4) lam := by
      constructor <;> nlinarith
    have hadd := intervalIntegral.integral_add_adjacent_intervals
      (hg2int (15 * lam / 32 - lam / 32) (15 * lam / 32)
        (hOuterSub hmem_am) (hOuterSub hmem_a))
      (hg2int (15 * lam / 32) lam (hOuterSub hmem_a)
        ⟨by linarith, le_refl _⟩)
    have hmono := intervalIntegral.integral_mono_on
      (by nlinarith : 15 * lam / 32 - lam / 32 ≤ 15 * lam / 32)
      (intervalIntegral.intervalIntegrable_const (c := φ (15 * lam / 32) ^ 2))
      (hg2int (15 * lam / 32 - lam / 32) (15 * lam / 32)
        (hOuterSub hmem_am) (hOuterSub hmem_a))
      (fun t ht => by
        have htmem : t ∈ Icc (lam / 4) lam :=
          ⟨by linarith [ht.1, hmem_am.1], by linarith [ht.2, hmem_a.2]⟩
        exact hg_anti htmem hmem_a ht.2)
    have hconst : (∫ _ in (15 * lam / 32 - lam / 32)..(15 * lam / 32),
        φ (15 * lam / 32) ^ 2) = (lam / 32) * φ (15 * lam / 32) ^ 2 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring_nf
    rw [hconst] at hmono
    have hMnn := hM_nonneg (15 * lam / 32) hmem_a
    have h14 : (15:ℝ) * lam / 32 - lam / 32 = 14 * lam / 32 := by ring
    rw [h14] at hadd hmono
    rw [hMdef]
    simp only
    have heq : (∫ s in (14 * lam / 32)..(15 * lam / 32), φ s ^ 2) =
        (∫ s in (14 * lam / 32)..lam, φ s ^ 2) -
        (∫ s in (15 * lam / 32)..lam, φ s ^ 2) := by linarith [hadd]
    rw [hMdef] at hMnn
    simp only at hMnn
    nlinarith [hmono, hMnn, heq]
  intro y hy
  have hyIcc : y ∈ Icc (lam / 4) lam := ⟨by linarith [hy.1], hy.2⟩
  have h15mem : (15:ℝ) * lam / 32 ∈ Icc (lam / 4) lam := by
    constructor <;> nlinarith
  have hhalfmem : lam / 2 ∈ Icc (lam / 4) lam := by
    constructor <;> nlinarith
  have hgy : φ y ^ 2 ≤ φ (15 * lam / 32) ^ 2 := by
    calc φ y ^ 2 ≤ φ (lam / 2) ^ 2 :=
        hg_anti hhalfmem hyIcc hy.1
      _ ≤ φ (15 * lam / 32) ^ 2 :=
        hg_anti h15mem hhalfmem (by nlinarith)
  have hgK : φ y ^ 2 ≤ 2 ^ 32 * B / lam ^ 13 := by
    have h1 : φ (15 * lam / 32) ^ 2 ≤ (32 / lam) * Mf (14 * lam / 32) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlam0]
      nlinarith [hga15]
    have h2 : (32 / lam) * Mf (14 * lam / 32) ≤
        (32 / lam) * ((512 / lam ^ 4) ^ 3 * B) :=
      mul_le_mul_of_nonneg_left hM14 (by positivity)
    have h3 : (32 / lam) * ((512 / lam ^ 4) ^ 3 * B) =
        2 ^ 32 * B / lam ^ 13 := by
      field_simp
      ring
    linarith [hgy, h1, h2, h3.le, h3.ge]
  have hKle : (2:ℝ) ^ 32 * B / lam ^ 13 ≤
      (65536 * Real.sqrt B / lam ^ 6) ^ 2 := by
    have hsqB : Real.sqrt B ^ 2 = B := Real.sq_sqrt hB0
    have hlampow : lam ^ 12 ≤ lam ^ 13 :=
      pow_le_pow_right₀ hlam1 (by norm_num)
    have hexp : (65536 * Real.sqrt B / lam ^ 6) ^ 2 =
        2 ^ 32 * B / lam ^ 12 := by
      rw [div_pow, mul_pow, hsqB, ← pow_mul]
      norm_num
    rw [hexp]
    apply div_le_div_of_nonneg_left _ (by positivity) hlampow
    positivity
  have := Real.abs_le_sqrt (hgK.trans hKle)
  rwa [Real.sqrt_sq (by positivity)] at this


/-! ## The anchored selected-family theorem -/

/-- Gaussian envelope for the two cylinder targets at the project argument:
`|D_j(√(4π)x)| ≤ 1008·e^{−πx²/2}` for `j ∈ {0, 4}`. -/
private theorem opd_target_envelope (n : ℕ) (hn : n = 0 ∨ n = 4) (x : ℝ) :
    |parabolicCylinderD n (projectCylinderArgument x)| ≤
      1008 * Real.exp (-(Real.pi * x ^ 2) / 2) := by
  set s : ℝ := Real.pi * x ^ 2 with hsdef
  have hs0 : (0 : ℝ) ≤ s := by rw [hsdef]; positivity
  have hkey : (16 * s ^ 2 + 24 * s + 3) ≤ 1008 * Real.exp (s / 2) := by
    by_cases hcase : s ≤ 6
    · have h1 : (1 : ℝ) ≤ Real.exp (s / 2) := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      nlinarith [hcase, hs0, h1]
    · push_neg at hcase
      have h3 := Real.pow_div_factorial_le_exp (x := s / 2)
        (by linarith) 3
      have h3' : s ^ 3 / 48 ≤ Real.exp (s / 2) := by
        have heq : (s / 2) ^ 3 / (Nat.factorial 3 : ℝ) = s ^ 3 / 48 := by
          norm_num [Nat.factorial]
          ring
        rwa [heq] at h3
      nlinarith [mul_le_mul_of_nonneg_left h3'
          (by norm_num : (0:ℝ) ≤ 1008),
        mul_nonneg (mul_nonneg
          (by linarith : (0:ℝ) ≤ s - 6) (by linarith : (0:ℝ) ≤ s))
          (by linarith : (0:ℝ) ≤ s)]
  have hpoly_env : ∀ P : ℝ, |P| ≤ 16 * s ^ 2 + 24 * s + 3 →
      Real.exp (-s) * |P| ≤ 1008 * Real.exp (-s / 2) := by
    intro P hP
    calc Real.exp (-s) * |P| ≤
        Real.exp (-s) * (16 * s ^ 2 + 24 * s + 3) :=
          mul_le_mul_of_nonneg_left hP (Real.exp_pos _).le
      _ ≤ Real.exp (-s) * (1008 * Real.exp (s / 2)) :=
          mul_le_mul_of_nonneg_left hkey (Real.exp_pos _).le
      _ = 1008 * (Real.exp (-s) * Real.exp (s / 2)) := by ring
      _ = 1008 * Real.exp (-s / 2) := by
          rw [← Real.exp_add, show (-s + s / 2 : ℝ) = -s / 2 by ring]
  have hhalf : (-(Real.pi * x ^ 2) / 2 : ℝ) = -s / 2 := by
    rw [hsdef]
  rcases hn with hn | hn
  · subst hn
    rw [parabolicCylinderD_zero_projectArgument, hhalf]
    have h1 : |Real.exp (-Real.pi * x ^ 2)| = Real.exp (-s) * |(1:ℝ)| := by
      rw [abs_of_pos (Real.exp_pos _), abs_one, mul_one, hsdef]
      ring_nf
    rw [h1]
    exact hpoly_env 1 (by
      rw [abs_one]
      nlinarith [hs0, sq_nonneg s])
  · subst hn
    rw [parabolicCylinderD_four_projectArgument, hhalf]
    have h1 : |Real.exp (-Real.pi * x ^ 2) *
        (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3)| =
        Real.exp (-s) * |16 * s ^ 2 - 24 * s + 3| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      congr 1
      · rw [hsdef]; ring_nf
      · congr 1
        rw [hsdef]; ring
    rw [h1]
    apply hpoly_env
    calc |16 * s ^ 2 - 24 * s + 3| =
        |(16 * s ^ 2 + 3) - 24 * s| := by
          rw [show 16 * s ^ 2 - 24 * s + 3 =
            (16 * s ^ 2 + 3) - 24 * s by ring]
      _ ≤ |16 * s ^ 2 + 3| + |24 * s| := abs_sub _ _
      _ ≤ 16 * s ^ 2 + 24 * s + 3 := by
          rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
          linarith

/-- The Gaussian mass on the half-line window is at most one. -/
private theorem opd_gauss_int (lam : ℝ) :
    (∫ x in Ioo (0:ℝ) lam, Real.exp (-(Real.pi * x ^ 2))) ≤ 1 := by
  have hint : Integrable (fun x : ℝ => Real.exp (-(Real.pi * x ^ 2)))
      volume := by
    have := integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
    apply this.congr
    filter_upwards with x
    ring_nf
  have h1 : (∫ x in Ioo (0:ℝ) lam, Real.exp (-(Real.pi * x ^ 2))) ≤
      ∫ x : ℝ, Real.exp (-(Real.pi * x ^ 2)) := by
    apply MeasureTheory.setIntegral_le_integral hint
    filter_upwards with x
    positivity
  have h2 : (∫ x : ℝ, Real.exp (-(Real.pi * x ^ 2))) = 1 := by
    have := integral_gaussian Real.pi
    rw [div_self Real.pi_pos.ne', Real.sqrt_one] at this
    rw [← this]
    congr 1
    funext x
    ring_nf
  linarith [h1, h2.le, h2.ge]

/-- Per-mode anchored assembly: the anchored cylinder rate plus the
eigenvalue window deliver the `65536·√2032129/λ⁶` outer bound for one
literal anchored mode. -/
private theorem opd_anchored_mode_bound
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K')
    (hsep :
      ∀ q ≥ K',
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hθc : Λ + mode4JacobiG mProject ≤ (Real.sqrt mProject) ^ 4)
    (a : ℂ) (ha : a ≠ 0)
    (n : ℕ) (hn : n = 0 ∨ n = 4)
    (Cj : ℝ) (hCj : 0 ≤ Cj)
    (hrate : ∀ x ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject),
      ‖a * S.normalizedPhysicalMode x -
        ((parabolicCylinderD n (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
        Cj / (Real.sqrt mProject) ^ 2)
    (hsize : 2 * Cj ^ 2 ≤ (mProject : ℝ)) :
    ∀ y ∈ Icc (Real.sqrt mProject / 2) (Real.sqrt mProject),
      ‖a * S.normalizedPhysicalMode y‖ ≤
        65536 * Real.sqrt 2032129 / (Real.sqrt mProject) ^ 6 := by
  set lam := Real.sqrt (mProject : ℝ) with hlamdef
  set φ : ℝ → ℝ := mode4PhysicalFerrersSeries mProject S.coefficients
    with hφdef
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hm2 : (2 : ℝ) ≤ (mProject : ℝ) := by exact_mod_cast hm
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef]
    exact Real.one_le_sqrt.mpr (by linarith)
  have hsq : lam ^ 2 = (mProject : ℝ) := Real.sq_sqrt hmR.le
  have hN : (0 : ℝ) < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have ha' : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  set sc : ℝ := ‖a‖ / S.physicalL2Normalization with hscdef
  have hsc : (0 : ℝ) < sc := div_pos ha' hN
  -- the anchored norm is the scaled raw series on the window
  have hnormEq : ∀ y ∈ Icc (-lam) lam,
      ‖a * S.normalizedPhysicalMode y‖ = sc * |φ y| := by
    intro y hy
    have hind : S.physicalZeroExtension y =
        mode4PhysicalFerrersSeriesComplex mProject S.coefficients y := by
      rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
        Set.indicator_of_mem hy]
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      hind, mode4PhysicalFerrersSeriesComplex]
    rw [norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hN]
    rw [hscdef]
    field_simp
    rw [hφdef]
  -- the anchored L² mass on the half-window is uniformly bounded
  have hφcont : ContinuousOn φ (Icc (-lam) lam) :=
    sturm_physSeries_continuousOn_closed S hm
  have hIooSub : Ioo (0 : ℝ) lam ⊆ Icc (-lam) lam := by
    intro t ht
    exact ⟨by linarith [ht.1], ht.2.le⟩
  have hint_sq : IntegrableOn (fun y => sc ^ 2 * φ y ^ 2)
      (Ioo (0 : ℝ) lam) volume := by
    apply MeasureTheory.IntegrableOn.mono_set (t := Icc (-lam) lam)
    · exact (((hφcont.pow 2).const_smul (sc ^ 2)).congr
        (fun x _ => by simp [smul_eq_mul])).integrableOn_compact
        isCompact_Icc
    · exact hIooSub
  have hint_gauss : IntegrableOn
      (fun y : ℝ => 2 * 1008 ^ 2 * Real.exp (-(Real.pi * y ^ 2)))
      (Ioo (0 : ℝ) lam) volume := by
    apply MeasureTheory.Integrable.integrableOn
    have := integrable_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
    exact (this.congr (by
      filter_upwards with x
      ring_nf)).const_mul _
  have hint_const : IntegrableOn
      (fun _ : ℝ => 2 * Cj ^ 2 / lam ^ 4) (Ioo (0 : ℝ) lam) volume :=
    MeasureTheory.integrableOn_const
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
  have hL2raw : (∫ y in Ioo (0 : ℝ) lam, φ y ^ 2) ≤ 2032129 / sc ^ 2 := by
    have hpoint : ∀ y ∈ Ioo (0 : ℝ) lam,
        sc ^ 2 * φ y ^ 2 ≤
          2 * 1008 ^ 2 * Real.exp (-(Real.pi * y ^ 2)) +
            2 * Cj ^ 2 / lam ^ 4 := by
      intro y hy
      have hyIcc := hIooSub hy
      have htri : sc * |φ y| ≤
          |parabolicCylinderD n (projectCylinderArgument y)| +
            Cj / lam ^ 2 := by
        have h1 := hrate y hyIcc
        have h2 : ‖a * S.normalizedPhysicalMode y‖ ≤
            ‖a * S.normalizedPhysicalMode y -
              ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ)‖ +
            ‖((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ)‖ := by
          have := norm_add_le
            (a * S.normalizedPhysicalMode y -
              ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))
            (((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))
          simpa using this
        rw [hnormEq y hyIcc] at h2
        rw [Complex.norm_real, Real.norm_eq_abs] at h2
        linarith [h1, h2]
      have henv := opd_target_envelope n hn y
      have hCjnn : (0 : ℝ) ≤ Cj / lam ^ 2 := by positivity
      have hboth : sc * |φ y| ≤
          1008 * Real.exp (-(Real.pi * y ^ 2) / 2) + Cj / lam ^ 2 := by
        linarith [htri, henv]
      have hsq2 : (sc * |φ y|) ^ 2 ≤
          2 * (1008 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 +
            2 * (Cj / lam ^ 2) ^ 2 := by
        nlinarith [hboth, mul_nonneg hsc.le (abs_nonneg (φ y)),
          mul_pos (by norm_num : (0:ℝ) < 1008)
            (Real.exp_pos (-(Real.pi * y ^ 2) / 2)), hCjnn,
          sq_nonneg (1008 * Real.exp (-(Real.pi * y ^ 2) / 2) -
            Cj / lam ^ 2)]
      have hexp2 : (1008 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 =
          1008 ^ 2 * Real.exp (-(Real.pi * y ^ 2)) := by
        rw [mul_pow]
        congr 1
        rw [sq, ← Real.exp_add,
          show (-(Real.pi * y ^ 2) / 2 + -(Real.pi * y ^ 2) / 2 : ℝ) =
            -(Real.pi * y ^ 2) by ring]
      have hstart : sc ^ 2 * φ y ^ 2 = (sc * |φ y|) ^ 2 := by
        rw [mul_pow, sq_abs]
      have hfin : 2 * (1008 * Real.exp (-(Real.pi * y ^ 2) / 2)) ^ 2 +
          2 * (Cj / lam ^ 2) ^ 2 =
          2 * 1008 ^ 2 * Real.exp (-(Real.pi * y ^ 2)) +
            2 * Cj ^ 2 / lam ^ 4 := by
        rw [hexp2]
        field_simp
      rw [hstart, ← hfin]
      exact hsq2
    have hmono := MeasureTheory.setIntegral_mono_on hint_sq
      (hint_gauss.add hint_const) measurableSet_Ioo hpoint
    have hsplit : (∫ y in Ioo (0:ℝ) lam,
        (2 * 1008 ^ 2 * Real.exp (-(Real.pi * y ^ 2)) +
          2 * Cj ^ 2 / lam ^ 4)) =
        2 * 1008 ^ 2 * (∫ y in Ioo (0:ℝ) lam, Real.exp (-(Real.pi * y ^ 2)))
          + (2 * Cj ^ 2 / lam ^ 4) * lam := by
      rw [MeasureTheory.integral_add hint_gauss hint_const,
        MeasureTheory.integral_const_mul, MeasureTheory.setIntegral_const,
        smul_eq_mul, measureReal_def, Real.volume_Ioo]
      rw [ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ lam - 0)]
      ring
    have hgauss := opd_gauss_int lam
    have hconst_small : (2 * Cj ^ 2 / lam ^ 4) * lam ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one (by positivity)]
      calc 2 * Cj ^ 2 * lam ≤ (mProject : ℝ) * lam :=
          mul_le_mul_of_nonneg_right hsize hlam0.le
        _ = lam ^ 2 * lam := by rw [hsq]
        _ ≤ lam ^ 4 := by
            have h34 := pow_le_pow_right₀ hlam1 (show 3 ≤ 4 by norm_num)
            nlinarith [h34]
    have hchain : (∫ y in Ioo (0:ℝ) lam, sc ^ 2 * φ y ^ 2) ≤ 2032129 := by
      calc (∫ y in Ioo (0:ℝ) lam, sc ^ 2 * φ y ^ 2) ≤
          2 * 1008 ^ 2 *
            (∫ y in Ioo (0:ℝ) lam, Real.exp (-(Real.pi * y ^ 2)))
            + (2 * Cj ^ 2 / lam ^ 4) * lam := by
            rw [← hsplit]; exact hmono
        _ ≤ 2 * 1008 ^ 2 * 1 + 1 := by
            have h2 := mul_le_mul_of_nonneg_left hgauss
              (by norm_num : (0:ℝ) ≤ 2 * 1008 ^ 2)
            linarith [h2, hconst_small]
        _ = 2032129 := by norm_num
    have hfactor : (∫ y in Ioo (0:ℝ) lam, sc ^ 2 * φ y ^ 2) =
        sc ^ 2 * ∫ y in Ioo (0:ℝ) lam, φ y ^ 2 :=
      MeasureTheory.integral_const_mul _ _
    rw [hfactor] at hchain
    rw [le_div_iff₀ (by positivity : (0:ℝ) < sc ^ 2)]
    linarith [hchain]
  -- apply the core theorem and rescale
  have hcore := sturm_outer_polynomial_decay S hm hK hsep hΛ hθc
    (2032129 / sc ^ 2) (by positivity) hL2raw
  intro y hy
  have hyIcc : y ∈ Icc (-lam) lam :=
    ⟨by nlinarith [hy.1, hlam0], hy.2⟩
  rw [hnormEq y hyIcc]
  have h1 := hcore y hy
  have hsqrtB : Real.sqrt (2032129 / sc ^ 2) =
      Real.sqrt 2032129 / sc := by
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 2032129),
      Real.sqrt_sq hsc.le]
  rw [hsqrtB] at h1
  calc sc * |φ y| ≤
      sc * (65536 * (Real.sqrt 2032129 / sc) / lam ^ 6) :=
        mul_le_mul_of_nonneg_left h1 hsc.le
    _ = 65536 * Real.sqrt 2032129 / lam ^ 6 := by
        field_simp

/--
**The anchored outer polynomial decay of the selected Ferrers modes**
(verdict fce7669c, REQ-2026-08-26-D).  From the committed anchored
cylinder rate (F72.6 input family) and the differential eigenvalue rate
(F72.3 scale), both literal center-anchored selected modes decay like
`C/λ⁶` uniformly on the outer half-window `[λ/2, λ]` — the single supplier
feeding the exact top-lattice flux consumer.  No derivative hypothesis, no
new analytic supplier: the mechanism is the exact ODE, zero flux, and the
sign of the outer cylinder potential.
-/
theorem selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates
    (C0 C4 Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4)
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
    (hθ :
      ∀ᶠ k in Filter.atTop,
        mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
            mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ) ∧
          mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
            mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ k in Filter.atTop,
        ∀ y ∈ Set.Icc (selectedFerrersPaperLambda k / 2)
            (selectedFerrersPaperLambda k),
          ‖centerAnchorScalarZero k *
              (selectedFerrersPreAnchorPair k).h0 y‖ ≤
            (65536 * Real.sqrt 2032129) /
              (selectedFerrersPaperLambda k) ^ 6 ∧
          ‖centerAnchorScalarFour k *
              (selectedFerrersPreAnchorPair k).h4 y‖ ≤
            (65536 * Real.sqrt 2032129) /
              (selectedFerrersPaperLambda k) ^ 6 := by
  refine ⟨65536 * Real.sqrt 2032129, by positivity, ?_⟩
  -- eventual size conditions
  have hev1 : ∀ᶠ k : ℕ in Filter.atTop,
      2 * C0 ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * C0 ^ 2)
    filter_upwards [this] with k hk
    push_cast
    push_cast at hk
    linarith
  have hev2 : ∀ᶠ k : ℕ in Filter.atTop,
      2 * C4 ^ 2 ≤ ((k + 2 : ℕ) : ℝ) := by
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) (2 * C4 ^ 2)
    filter_upwards [this] with k hk
    push_cast
    push_cast at hk
    linarith
  have hev3 : ∀ᶠ k : ℕ in Filter.atTop,
      Cθ ≤ ((k + 2 : ℕ) : ℝ) := by
    have := Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
    filter_upwards [this] with k hk
    push_cast
    push_cast at hk
    linarith
  filter_upwards [hmode, hθ, hev1, hev2, hev3] with k hmodek hθk h1k h2k h3k
  intro y hy
  have hG : (0 : ℝ) < mode4JacobiG (k + 2) := by
    rw [mode4JacobiG]
    positivity
  have hlam4 : ∀ Λv : ℝ, Λv + mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ) →
      Λv + mode4JacobiG (k + 2) ≤ (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 := by
    intro Λv hv
    have hm2 : (0 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by positivity
    have hsq2 : (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 =
        ((k + 2 : ℕ) : ℝ) ^ 2 := by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
        Real.sq_sqrt hm2]
    rw [hsq2]
    calc Λv + mode4JacobiG (k + 2) ≤ Cθ * ((k + 2 : ℕ) : ℝ) := hv
      _ ≤ ((k + 2 : ℕ) : ℝ) * ((k + 2 : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h3k hm2
      _ = ((k + 2 : ℕ) : ℝ) ^ 2 := by ring
  have hspec := selectedFerrersPreAnchorPair_spec k
  constructor
  · -- mode zero
    have hb := opd_anchored_mode_bound
      (selectedFerrersPreAnchorSolution0 k)
      (by omega) (by omega)
      (selectedFerrersPreAnchorSeparation k)
      (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three _ hG 0
        (by norm_num)).le
      (hlam4 _ hθk.1)
      (centerAnchorScalarZero k) (centerAnchorScalarZero_ne k)
      0 (Or.inl rfl) C0 hC0
      (fun x hx => by
        have := (hmodek x (by
          simpa [selectedFerrersPaperLambda] using hx)).1
        rw [hspec.2.1] at this
        simpa [selectedFerrersPaperLambda] using this)
      h1k
    have := hb y (by simpa [selectedFerrersPaperLambda] using hy)
    rw [hspec.2.1]
    simpa [selectedFerrersPaperLambda] using this
  · -- mode four
    have hb := opd_anchored_mode_bound
      (selectedFerrersPreAnchorSolution4 k)
      (by omega) (by omega)
      (selectedFerrersPreAnchorSeparation k)
      (mode4ClassicalEvenEigenvalue_lt_twenty_of_lt_three _ hG 2
        (by norm_num)).le
      (hlam4 _ hθk.2)
      (centerAnchorScalarFour k) (centerAnchorScalarFour_ne k)
      4 (Or.inr rfl) C4 hC4
      (fun x hx => by
        have := (hmodek x (by
          simpa [selectedFerrersPaperLambda] using hx)).2
        rw [hspec.2.2.1] at this
        simpa [selectedFerrersPaperLambda] using this)
      h2k
    have := hb y (by simpa [selectedFerrersPaperLambda] using hy)
    rw [hspec.2.2.1]
    simpa [selectedFerrersPaperLambda] using this

#print axioms sturm_outer_polynomial_decay
#print axioms selectedFerrersAnchoredOuterPolynomialDecay_of_modeAndThetaRates

end Q3.RouteB.D0Pstar
