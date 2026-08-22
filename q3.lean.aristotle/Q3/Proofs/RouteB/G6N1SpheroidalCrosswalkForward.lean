import Q3.Proofs.RouteB.D0Mode4DLMF3035EvenCharacteristicSource
import Q3.Proofs.RouteB.SpheroidalSourceEvenPackage

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1600000

open Set Filter Topology Polynomial MeasureTheory

namespace Q3.RouteB

/-!
# The forward crosswalk: a source eigenvalue satisfies the DLMF characteristic equation

Floor U2.3 of verdict `68e9cd78`, per the object lock
`DLMF3035_FORWARD_SOURCE_AND_PROJECT_OBJECT_LOCKED`
(`docs/routeB_bus/litreview/DLMF_3035_FORWARD_MEMBERSHIP_PROJECT_CROSSWALK_2026-08-22.md`).

Proof source: Meixner–Schäfke 1954, §3.24 Satz 6, via the §1.8 theory of
three-term recursions.  The Lean realization is native, in the Legendre basis:

1. The Legendre moments of a regular even eigenfunction satisfy the DLMF
   30.3.7 three-term recursion (integration by parts against the mixed
   Wronskian; boundary terms die by the flux condition).
2. The alternating-sign, `(4q+1)`-weighted moments are a nontrivial,
   polynomially bounded solution of the project's mode-four recursion,
   proportional to the left continuant pair.
3. Pincherle uniqueness, Wronskian-vanishing form: against the decaying
   backward-tail solution, the transported determinant both telescopes with
   factor `Lower/Upper ≥ 1` and collapses to `0`, forcing the pair equality
   at the split — hence `mode4RootFunction = 0`, hence the pole-safe DLMF
   characteristic equation through the ratified iff.

No use of the reverse crosswalk; the direction comes from the eigenfunction's
own coefficients.  One-way only: no iff with the source spectrum is stated.

LEDGER:
  CLOSES: [U2_3_EVEN_BRANCH_FORWARD_MEMBERSHIP]
  OPENS:  []
-/

/-! ## Legendre polynomials are bounded by one on the interval -/

/-- The Legendre Lyapunov function `P_n² + (1-x²) P_n′² / (n(n+1))` has
derivative `2x P_n′² / (n(n+1))`. -/
theorem fwd_legendre_lyapunov_hasDerivAt (n : ℕ) (hn : 1 ≤ n) (x : ℝ) :
    HasDerivAt
      (fun t : ℝ => lpv n t ^ 2 + (1 - t ^ 2) * lpd n t ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)))
      (2 * x * lpd n x ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) x := by
  have hnR : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  have hsq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have h1 : HasDerivAt (fun t : ℝ => lpv n t ^ 2) (2 * lpv n x * lpd n x) x := by
    have h := (hasDerivAt_lpv n x).mul (hasDerivAt_lpv n x)
    convert h using 1
    · ext t; simp [Pi.mul_apply, sq]
    · ring
  have h2 : HasDerivAt (fun t : ℝ => lpd n t ^ 2) (2 * lpd n x * lpdd n x) x := by
    have h := (hasDerivAt_lpd n x).mul (hasDerivAt_lpd n x)
    convert h using 1
    · ext t; simp [Pi.mul_apply, sq]
    · ring
  have h3 : HasDerivAt (fun t : ℝ => (1 - t ^ 2) * lpd n t ^ 2)
      (-(2 * x) * lpd n x ^ 2 + (1 - x ^ 2) * (2 * lpd n x * lpdd n x)) x :=
    hsq.mul h2
  have h4 := h1.add (h3.div_const ((n : ℝ) * ((n : ℝ) + 1)))
  convert h4 using 1
  have hode := legendre_ode n x
  have hne : ((n : ℝ) * ((n : ℝ) + 1)) ≠ 0 := ne_of_gt hnR
  field_simp
  linear_combination (-(lpd n x)) * hode

/-- On `[-1, 1]` every Legendre polynomial value is bounded by one. -/
theorem fwd_lpv_abs_le_one (n : ℕ) {x : ℝ} (hx : |x| ≤ 1) : |lpv n x| ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · simp [hn0]
  -- the Lyapunov function is monotone on [0,1]
  have hnR : (0 : ℝ) < (n : ℝ) * ((n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    nlinarith
  set V : ℝ → ℝ :=
    fun t => lpv n t ^ 2 + (1 - t ^ 2) * lpd n t ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) with hV
  have hVd : ∀ t : ℝ, HasDerivAt V
      (2 * t * lpd n t ^ 2 / ((n : ℝ) * ((n : ℝ) + 1))) t :=
    fun t => fwd_legendre_lyapunov_hasDerivAt n hn t
  have hVmono : MonotoneOn V (Icc (0 : ℝ) 1) := by
    have hcont : ContinuousOn V (Icc (0 : ℝ) 1) :=
      fun t _ => (hVd t).continuousAt.continuousWithinAt
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont
      (fun t _ => (hVd t).differentiableAt.differentiableWithinAt) ?_
    intro t ht
    rw [interior_Icc] at ht
    rw [(hVd t).deriv]
    have h0t : 0 < t := ht.1
    positivity
  have hVone : V 1 = 1 := by
    rw [hV]
    norm_num [lpv_at_one]
  have hkey : ∀ y : ℝ, y ∈ Icc (0 : ℝ) 1 → |lpv n y| ≤ 1 := by
    intro y hy
    have hle : V y ≤ V 1 := hVmono hy (by norm_num) hy.2
    have hnn : 0 ≤ (1 - y ^ 2) * lpd n y ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      have h1 : (0 : ℝ) ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
      positivity
    have hVy : V y = lpv n y ^ 2 + (1 - y ^ 2) * lpd n y ^ 2 / ((n : ℝ) * ((n : ℝ) + 1)) :=
      rfl
    have hsq : lpv n y ^ 2 ≤ 1 := by
      rw [hVone] at hle
      rw [hVy] at hle
      linarith
    nlinarith [sq_abs (lpv n y), abs_nonneg (lpv n y)]
  rcases le_total 0 x with hx0 | hx0
  · exact hkey x ⟨hx0, (abs_le.mp hx).2⟩
  · have hmem : -x ∈ Icc (0 : ℝ) 1 := ⟨by linarith, by linarith [(abs_le.mp hx).1]⟩
    have := hkey (-x) hmem
    rwa [lpv_neg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul] at this

/-! ## Legendre flux vanishes at the endpoints -/

theorem fwd_legendre_flux_one (n : ℕ) :
    Tendsto (fun x : ℝ => (1 - x ^ 2) * lpd n x) (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ => (1 - x ^ 2) * lpd n x) :=
    (continuous_const.sub (continuous_pow 2)).mul (continuous_lpd n)
  have := (hcont.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
  simpa using this

theorem fwd_legendre_flux_neg_one (n : ℕ) :
    Tendsto (fun x : ℝ => (1 - x ^ 2) * lpd n x) (𝓝[>] (-1 : ℝ)) (𝓝 0) := by
  have hcont : Continuous (fun x : ℝ => (1 - x ^ 2) * lpd n x) :=
    (continuous_const.sub (continuous_pow 2)).mul (continuous_lpd n)
  have := (hcont.tendsto (-1)).mono_left (nhdsWithin_le_nhds (s := Ioi (-1 : ℝ)))
  simpa using this

/-! ## Vanishing-flux fundamental theorem on the open interval -/

/-- If `W` has derivative `h` on `(-1,1)`, `h` extends continuously to the
closed interval, and `W → 0` at both endpoints, then `∫ h = 0`. -/
theorem fwd_integral_eq_zero_of_flux (W h : ℝ → ℝ)
    (hcont : ContinuousOn h (Icc (-1 : ℝ) 1))
    (hd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt W (h x) x)
    (hWr : Tendsto W (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hWl : Tendsto W (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    ∫ x in (-1 : ℝ)..1, h x = 0 := by
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |h x| ≤ C := by
    obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hcont
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      le_trans (by simpa [Real.norm_eq_abs] using hCb x hx) (le_max_left _ _)⟩
  have hint : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable h volume a b := by
    intro a b ha hb
    exact ContinuousOn.intervalIntegrable
      (hcont.mono ((Set.ordConnected_Icc).uIcc_subset ha hb))
  set I := ∫ x in (-1 : ℝ)..1, h x with hI
  have hFTC : ∀ a b : ℝ, a ∈ Ioo (-1 : ℝ) 1 → b ∈ Ioo (-1 : ℝ) 1 →
      (∫ x in a..b, h x) = W b - W a := by
    intro a b ha hb
    have hsub : uIcc a b ⊆ Ioo (-1 : ℝ) 1 := (Set.ordConnected_Ioo).uIcc_subset ha hb
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x hx => hd x (hsub hx))
      (hint a b (Ioo_subset_Icc_self ha) (Ioo_subset_Icc_self hb))
  have hkey : ∀ ε : ℝ, 0 < ε → |I| ≤ ε := by
    intro ε hε
    set D := C + 1 with hD
    have hD0 : 0 < D := by positivity
    set δ := ε / (4 * D) with hδ
    have hδ0 : 0 < δ := by positivity
    obtain ⟨b, hbmem, hbW⟩ : ∃ b ∈ Ioo (max 0 (1 - δ)) 1, |W b| < ε / 4 := by
      have h1 : Ioo (max 0 (1 - δ)) 1 ∈ 𝓝[<] (1 : ℝ) :=
        Ioo_mem_nhdsLT (max_lt (by norm_num) (by linarith))
      have h2 : {x : ℝ | |W x| < ε / 4} ∈ 𝓝[<] (1 : ℝ) := by
        have hball := hWr (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 4))
        filter_upwards [hball] with x hx
        simpa [Real.dist_eq] using hx
      obtain ⟨b, hb⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
      exact ⟨b, hb.1, hb.2⟩
    obtain ⟨a, hamem, haW⟩ : ∃ a ∈ Ioo (-1 : ℝ) (min 0 (-1 + δ)), |W a| < ε / 4 := by
      have h1 : Ioo (-1 : ℝ) (min 0 (-1 + δ)) ∈ 𝓝[>] (-1 : ℝ) :=
        Ioo_mem_nhdsGT (lt_min (by norm_num) (by linarith))
      have h2 : {x : ℝ | |W x| < ε / 4} ∈ 𝓝[>] (-1 : ℝ) := by
        have hball := hWl (Metric.ball_mem_nhds (0 : ℝ) (by positivity : (0 : ℝ) < ε / 4))
        filter_upwards [hball] with x hx
        simpa [Real.dist_eq] using hx
      obtain ⟨a, ha⟩ := Filter.nonempty_of_mem (inter_mem h1 h2)
      exact ⟨a, ha.1, ha.2⟩
    have hb1 : b < 1 := hbmem.2
    have hb0 : 0 ≤ b := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hbmem.1)
    have hbδ : 1 - δ < b := lt_of_le_of_lt (le_max_right _ _) hbmem.1
    have ha1 : -1 < a := hamem.1
    have ha0 : a ≤ 0 := le_of_lt (lt_of_lt_of_le hamem.2 (min_le_left _ _))
    have haδ : a < -1 + δ := lt_of_lt_of_le hamem.2 (min_le_right _ _)
    have haI : a ∈ Ioo (-1 : ℝ) 1 := ⟨ha1, by linarith⟩
    have hbI : b ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith, hb1⟩
    have hs1 : (∫ x in (-1 : ℝ)..a, h x) + (∫ x in a..b, h x)
        + (∫ x in b..(1 : ℝ), h x) = I := by
      rw [intervalIntegral.integral_add_adjacent_intervals
        (hint (-1) a (by norm_num) (Ioo_subset_Icc_self haI))
        (hint a b (Ioo_subset_Icc_self haI) (Ioo_subset_Icc_self hbI)),
        intervalIntegral.integral_add_adjacent_intervals
        (hint (-1) b (by norm_num) (Ioo_subset_Icc_self hbI))
        (hint b 1 (Ioo_subset_Icc_self hbI) (by norm_num))]
    have hbnd1 : |∫ x in (-1 : ℝ)..a, h x| ≤ C * |a - (-1)| := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C) (f := h) (a := (-1 : ℝ)) (b := a) ?_
      · simpa [Real.norm_eq_abs] using hnorm
      · intro x hx
        rw [uIoc_of_le (by linarith : (-1 : ℝ) ≤ a)] at hx
        simpa [Real.norm_eq_abs] using hC x ⟨le_of_lt hx.1, by linarith [hx.2]⟩
    have hbnd2 : |∫ x in b..(1 : ℝ), h x| ≤ C * |1 - b| := by
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := C) (f := h) (a := b) (b := (1 : ℝ)) ?_
      · simpa [Real.norm_eq_abs] using hnorm
      · intro x hx
        rw [uIoc_of_le (by linarith : b ≤ (1 : ℝ))] at hx
        simpa [Real.norm_eq_abs] using hC x ⟨by linarith [hx.1], hx.2⟩
    have hmid := hFTC a b haI hbI
    have hab : |a - (-1)| ≤ δ := by rw [abs_of_nonneg (by linarith)]; linarith
    have hbb : |1 - b| ≤ δ := by rw [abs_of_nonneg (by linarith)]; linarith
    have hIexp : I = (∫ x in (-1 : ℝ)..a, h x)
        + (∫ x in b..(1 : ℝ), h x) + (W b - W a) := by
      rw [← hmid, ← hs1]; ring
    have hCd : C * |a - (-1)| + C * |1 - b| ≤ 2 * D * δ := by
      have h1 : C * |a - (-1)| ≤ D * δ := by
        have := mul_le_mul (le_of_lt (by linarith : C < D)) hab
          (abs_nonneg _) (le_of_lt hD0)
        linarith
      have h2 : C * |1 - b| ≤ D * δ := by
        have := mul_le_mul (le_of_lt (by linarith : C < D)) hbb
          (abs_nonneg _) (le_of_lt hD0)
        linarith
      linarith
    have h4δ : 2 * D * δ = ε / 2 := by rw [hδ]; field_simp; ring
    have t1 : |I| ≤ |(∫ x in (-1 : ℝ)..a, h x) + ∫ x in b..(1 : ℝ), h x|
        + |W b - W a| := by
      rw [hIexp]; exact abs_add_le _ _
    have t2 : |(∫ x in (-1 : ℝ)..a, h x) + ∫ x in b..(1 : ℝ), h x|
        ≤ |∫ x in (-1 : ℝ)..a, h x| + |∫ x in b..(1 : ℝ), h x| := abs_add_le _ _
    have t3 : |W b - W a| ≤ |W b| + |W a| := abs_sub _ _
    linarith [hbnd1, hbnd2]
  by_contra hcon
  have habs : 0 < |I| := abs_pos.mpr hcon
  have hhalf := hkey (|I| / 2) (by linarith)
  linarith

/-! ## The mixed Wronskian: spheroidal eigenfunction against a Legendre polynomial -/

theorem fwd_mixed_wronskian_hasDerivAt (G Λ : ℝ) (n : ℕ) (f f1 f2 : ℝ → ℝ)
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun t : ℝ => (1 - t ^ 2) * (f1 t * lpv n t - f t * lpd n t))
      (((n : ℝ) * ((n : ℝ) + 1) - Λ - G * (1 - x ^ 2)) * (f x * lpv n x)) x := by
  obtain ⟨hf, hf'⟩ := hfd x hx
  have hsq : HasDerivAt (fun t : ℝ => 1 - t ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have H := hsq.mul ((hf'.mul (hasDerivAt_lpv n x)).sub (hf.mul (hasDerivAt_lpd n x)))
  simp only [Pi.mul_apply, Pi.sub_apply] at H
  convert H using 1
  have e1 := hfe x hx
  have e2 := legendre_ode n x
  linear_combination (lpv n x) * e1 + (f x) * e2

/-- **Pairing the eigen-equation against `P_n`.**  The boundary terms die by
the flux condition; what remains is the weighted-moment identity. -/
theorem fwd_legendre_pairing (G Λ : ℝ) (n : ℕ) (f f1 f2 : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hfr : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hfl : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0)) :
    ((n : ℝ) * ((n : ℝ) + 1) - Λ) * (∫ x in (-1 : ℝ)..1, f x * lpv n x)
      = G * ∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (f x * lpv n x) := by
  have hgc : ContinuousOn (lpv n) (Icc (-1 : ℝ) 1) := (continuous_lpv n).continuousOn
  have hWr := spheroidal_wronskian_tendsto_one f f1 (lpv n) (lpd n)
    hfc hgc hfr (fwd_legendre_flux_one n)
  have hWl := spheroidal_wronskian_tendsto_neg_one f f1 (lpv n) (lpd n)
    hfc hgc hfl (fwd_legendre_flux_neg_one n)
  have hcont1 : ContinuousOn (fun x : ℝ => f x * lpv n x) (Icc (-1 : ℝ) 1) :=
    hfc.mul hgc
  have hcont2 : ContinuousOn (fun x : ℝ => (1 - x ^ 2) * (f x * lpv n x))
      (Icc (-1 : ℝ) 1) :=
    ((continuous_const.sub (continuous_pow 2)).continuousOn).mul hcont1
  have hint1 : IntervalIntegrable (fun x : ℝ => f x * lpv n x) volume (-1 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable (by
      rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])
  have hint2 : IntervalIntegrable (fun x : ℝ => (1 - x ^ 2) * (f x * lpv n x))
      volume (-1 : ℝ) 1 :=
    ContinuousOn.intervalIntegrable (by
      rwa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)])
  have hzero := fwd_integral_eq_zero_of_flux
    (fun t : ℝ => (1 - t ^ 2) * (f1 t * lpv n t - f t * lpd n t))
    (fun x : ℝ => ((n : ℝ) * ((n : ℝ) + 1) - Λ) * (f x * lpv n x)
      - G * ((1 - x ^ 2) * (f x * lpv n x)))
    (((continuousOn_const).mul hcont1).sub ((continuousOn_const).mul hcont2))
    (fun x hx => by
      have := fwd_mixed_wronskian_hasDerivAt G Λ n f f1 f2 hfd hfe hx
      convert this using 1
      ring)
    hWr hWl
  rw [intervalIntegral.integral_sub (hint1.const_mul _) (hint2.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    at hzero
  linarith

/-! ## The even moment sequence and its three-term recursion -/

/-- The `k`-th even Legendre moment of `f`. -/
noncomputable def fwdMoment (f : ℝ → ℝ) (k : ℕ) : ℝ :=
  ∫ x in (-1 : ℝ)..1, f x * lpv (2 * k) x

theorem fwd_intM (f : ℝ → ℝ) (hfc : ContinuousOn f (Icc (-1 : ℝ) 1)) (m : ℕ) :
    IntervalIntegrable (fun x : ℝ => f x * lpv m x) volume (-1 : ℝ) 1 :=
  ContinuousOn.intervalIntegrable (by
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
    exact hfc.mul (continuous_lpv m).continuousOn)

/-- **The moment recursion.**  The even Legendre moments of a regular even
eigenfunction satisfy the three-term recursion with the `(1-x²)` Jacobi
coefficients. -/
theorem fwdMoment_rec (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hfr : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hfl : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    (k : ℕ) :
    ((2 * k : ℝ) * ((2 * k : ℝ) + 1) - Λ) * fwdMoment f k
      = G * (jacA k * fwdMoment f (k + 1) + jacB k * fwdMoment f k
          + jacC k * fwdMoment f (k - 1)) := by
  have hpair := fwd_legendre_pairing G Λ (2 * k) f f1 f2 hfc hfd hfe hfr hfl
  have h1 : 2 * (k + 1) = 2 * k + 2 := by omega
  have h2 : 2 * (k - 1) = 2 * k - 2 := by omega
  have hcongr : ∀ x : ℝ, (1 - x ^ 2) * (f x * lpv (2 * k) x)
      = jacA k * (f x * lpv (2 * (k + 1)) x)
        + (jacB k * (f x * lpv (2 * k) x)
          + jacC k * (f x * lpv (2 * (k - 1)) x)) := by
    intro x
    have hexp := legendre_even_expansion k x
    rw [h1, h2]
    linear_combination (f x) * hexp
  have hsplit : (∫ x in (-1 : ℝ)..1, (1 - x ^ 2) * (f x * lpv (2 * k) x))
      = jacA k * fwdMoment f (k + 1) + jacB k * fwdMoment f k
        + jacC k * fwdMoment f (k - 1) := by
    rw [intervalIntegral.integral_congr (g :=
      fun x : ℝ => jacA k * (f x * lpv (2 * (k + 1)) x)
        + (jacB k * (f x * lpv (2 * k) x)
          + jacC k * (f x * lpv (2 * (k - 1)) x)))
      (fun x _ => hcongr x)]
    rw [intervalIntegral.integral_add ((fwd_intM f hfc _).const_mul _)
      (((fwd_intM f hfc _).const_mul _).add ((fwd_intM f hfc _).const_mul _)),
      intervalIntegral.integral_add ((fwd_intM f hfc _).const_mul _)
        ((fwd_intM f hfc _).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul]
    show jacA k * fwdMoment f (k + 1) + (jacB k * fwdMoment f k
      + jacC k * fwdMoment f (k - 1)) = _
    ring
  rw [hsplit] at hpair
  have hcast : ((2 * k : ℕ) : ℝ) = (2 * k : ℝ) := by push_cast; ring
  rw [hcast] at hpair
  have hfold : fwdMoment f k = ∫ x in (-1 : ℝ)..1, f x * lpv (2 * k) x := rfl
  rw [← hfold] at hpair
  linarith

/-- Odd moments of an even function vanish. -/
theorem fwd_odd_moment_zero (f : ℝ → ℝ) (hev : ∀ x : ℝ, f (-x) = f x) (m : ℕ)
    (hm : Odd m) :
    ∫ x in (-1 : ℝ)..1, f x * lpv m x = 0 := by
  have hneg : ∀ x : ℝ, f (-x) * lpv m (-x) = -(f x * lpv m x) := by
    intro x
    rw [hev, lpv_neg, hm.neg_one_pow]
    ring
  have hcomp := intervalIntegral.integral_comp_neg (fun x : ℝ => f x * lpv m x)
    (a := (-1 : ℝ)) (b := 1)
  simp only [neg_neg] at hcomp
  have : (∫ x in (-1 : ℝ)..1, f (-x) * lpv m (-x))
      = ∫ x in (-1 : ℝ)..1, -(f x * lpv m x) := by
    exact intervalIntegral.integral_congr (fun x _ => hneg x)
  rw [this, intervalIntegral.integral_neg] at hcomp
  linarith [hcomp]

/-- Uniform bound on the moments: `|M_k| ≤ 2 sup |f|`. -/
theorem fwdMoment_abs_le (f : ℝ → ℝ) (Cf : ℝ)
    (hCf : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ Cf) (k : ℕ) :
    |fwdMoment f k| ≤ 2 * Cf := by
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf 0 (by norm_num))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (C := Cf) (f := fun x : ℝ => f x * lpv (2 * k) x) (a := (-1 : ℝ)) (b := 1) ?_
  · rw [fwdMoment]
    have : |(1 : ℝ) - (-1)| = 2 := by norm_num
    calc |∫ x in (-1 : ℝ)..1, f x * lpv (2 * k) x|
        ≤ Cf * |(1 : ℝ) - (-1)| := by
          simpa [Real.norm_eq_abs] using hnorm
      _ = 2 * Cf := by rw [this]; ring
  · intro x hx
    rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
    have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
    have habs : |x| ≤ 1 := abs_le.mpr ⟨hxI.1, hxI.2⟩
    rw [Real.norm_eq_abs, abs_mul]
    calc |f x| * |lpv (2 * k) x| ≤ Cf * 1 :=
        mul_le_mul (hCf x hxI) (fwd_lpv_abs_le_one (2 * k) habs)
          (abs_nonneg _) hCf0
      _ = Cf := mul_one Cf

/-! ## Nontriviality: some even moment is nonzero -/

/-- The `n`-th Legendre polynomial has degree `n` and positive leading
coefficient. -/
theorem fwd_legendreP_deg (n : ℕ) :
    (legendreP n).natDegree = n ∧ 0 < (legendreP n).leadingCoeff := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => refine ⟨by simp, by simp⟩
    | 1 => refine ⟨by simp, by simp⟩
    | (m + 2) =>
      obtain ⟨hd1, hl1⟩ := ih (m + 1) (by omega)
      obtain ⟨hd0, hl0⟩ := ih m (by omega)
      have hP1ne : legendreP (m + 1) ≠ 0 := by
        intro h
        rw [h] at hl1
        simp [Polynomial.leadingCoeff_zero] at hl1
      have haC : ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) ≠ 0 := by positivity
      set q1 : Polynomial ℝ :=
        Polynomial.C ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * X * legendreP (m + 1) with hq1
      set q2 : Polynomial ℝ :=
        Polynomial.C (((m : ℝ) + 1) / ((m : ℝ) + 2)) * legendreP m with hq2
      have hq1d : q1.natDegree = m + 2 := by
        rw [hq1, mul_assoc, Polynomial.natDegree_C_mul haC,
          Polynomial.natDegree_mul Polynomial.X_ne_zero hP1ne,
          Polynomial.natDegree_X, hd1]
        omega
      have hq1l : q1.leadingCoeff
          = ((2 * (m : ℝ) + 3) / ((m : ℝ) + 2)) * (legendreP (m + 1)).leadingCoeff := by
        rw [hq1, mul_assoc, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_mul,
          Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_X]
        ring
      have hq2d : q2.natDegree ≤ m := by
        rw [hq2]
        exact le_trans (Polynomial.natDegree_C_mul_le _ _) (le_of_eq hd0)
      have hdlt : q2.natDegree < q1.natDegree := by omega
      have hsub : legendreP (m + 2) = q1 - q2 := by
        rw [hq1, hq2, legendreP_add_two]
      constructor
      · rw [hsub, Polynomial.natDegree_sub_eq_left_of_natDegree_lt hdlt, hq1d]
      · rw [hsub, Polynomial.leadingCoeff_sub_of_degree_lt ?_, hq1l]
        · positivity
        · have hq1ne : q1 ≠ 0 := by
            intro h
            rw [h] at hq1d
            simp at hq1d
          calc q2.degree ≤ (q2.natDegree : WithBot ℕ) := Polynomial.degree_le_natDegree
            _ < (q1.natDegree : WithBot ℕ) := by exact_mod_cast hdlt
            _ = q1.degree := (Polynomial.degree_eq_natDegree hq1ne).symm

/-- If every even moment vanishes and `f` is even, then `f` pairs to zero
with every polynomial. -/
theorem fwd_poly_moment_zero (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hev : ∀ x : ℝ, f (-x) = f x)
    (hmom : ∀ k, fwdMoment f k = 0) :
    ∀ p : Polynomial ℝ, ∫ x in (-1 : ℝ)..1, f x * p.eval x = 0 := by
  have hintP : ∀ p : Polynomial ℝ,
      IntervalIntegrable (fun x : ℝ => f x * p.eval x) volume (-1 : ℝ) 1 := by
    intro p
    exact ContinuousOn.intervalIntegrable (by
      rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
      exact hfc.mul p.continuous.continuousOn)
  have hleg : ∀ m : ℕ, ∫ x in (-1 : ℝ)..1, f x * lpv m x = 0 := by
    intro m
    rcases Nat.even_or_odd m with he | ho
    · obtain ⟨j, hj⟩ := he
      have := hmom j
      rw [fwdMoment] at this
      rw [show m = 2 * j by omega]
      exact this
    · exact fwd_odd_moment_zero f hev m ho
  suffices H : ∀ N : ℕ, ∀ p : Polynomial ℝ, p.natDegree ≤ N →
      ∫ x in (-1 : ℝ)..1, f x * p.eval x = 0 by
    exact fun p => H p.natDegree p le_rfl
  intro N
  induction N with
  | zero =>
    intro p hp
    rw [Polynomial.eq_C_of_natDegree_le_zero hp]
    have h0 := hleg 0
    have : (∫ x in (-1 : ℝ)..1, f x * (Polynomial.C (p.coeff 0)).eval x)
        = (∫ x in (-1 : ℝ)..1, f x * lpv 0 x) * p.coeff 0 := by
      rw [← intervalIntegral.integral_mul_const]
      exact intervalIntegral.integral_congr (fun x _ => by
        simp [lpv])
    rw [this, h0, zero_mul]
  | succ N ihN =>
    intro p hp
    by_cases hple : p.natDegree ≤ N
    · exact ihN p hple
    · have hn : p.natDegree = N + 1 := le_antisymm hp (by omega)
      have hp0 : p ≠ 0 := by
        intro h
        rw [h] at hn
        simp at hn
      obtain ⟨hLd, hLl⟩ := fwd_legendreP_deg (N + 1)
      have hLne : legendreP (N + 1) ≠ 0 := by
        intro h
        rw [h] at hLl
        simp [Polynomial.leadingCoeff_zero] at hLl
      set c : ℝ := p.leadingCoeff / (legendreP (N + 1)).leadingCoeff with hc
      have hcne : c ≠ 0 := by
        rw [hc]
        exact div_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp0) (ne_of_gt hLl)
      set q : Polynomial ℝ := Polynomial.C c * legendreP (N + 1) with hq
      have hqd : q.natDegree = N + 1 := by
        rw [hq, Polynomial.natDegree_C_mul hcne, hLd]
      have hqne : q ≠ 0 := by
        intro h
        rw [h] at hqd
        simp at hqd
      have hql : q.leadingCoeff = p.leadingCoeff := by
        rw [hq, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc,
          div_mul_cancel₀ _ (ne_of_gt hLl)]
      set r : Polynomial ℝ := p - q with hr
      have hrd : r.natDegree ≤ N := by
        by_cases hr0 : r = 0
        · rw [hr0]; simp
        · have hdeg : r.degree < p.degree := by
            rw [hr]
            exact Polynomial.degree_sub_lt
              (by rw [Polynomial.degree_eq_natDegree hp0,
                Polynomial.degree_eq_natDegree hqne, hn, hqd])
              hp0 hql.symm
          have hdeg' : r.degree < ((N + 1 : ℕ) : WithBot ℕ) := by
            rw [Polynomial.degree_eq_natDegree hp0, hn] at hdeg
            exact_mod_cast hdeg
          have := (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr hdeg'
          omega
      have hsplit : ∀ x : ℝ, p.eval x = c * lpv (N + 1) x + r.eval x := by
        intro x
        rw [hr]
        simp [hq, lpv]
      have hint1 : IntervalIntegrable (fun x : ℝ => f x * lpv (N + 1) x)
          volume (-1 : ℝ) 1 := fwd_intM f hfc (N + 1)
      calc (∫ x in (-1 : ℝ)..1, f x * p.eval x)
          = ∫ x in (-1 : ℝ)..1,
              (f x * lpv (N + 1) x * c + f x * r.eval x) := by
            exact intervalIntegral.integral_congr (fun x _ => by
              rw [hsplit x]; ring)
        _ = (∫ x in (-1 : ℝ)..1, f x * lpv (N + 1) x) * c
              + ∫ x in (-1 : ℝ)..1, f x * r.eval x := by
            rw [intervalIntegral.integral_add (hint1.mul_const _) (hintP r),
              intervalIntegral.integral_mul_const]
        _ = 0 := by
            rw [hleg (N + 1), ihN r hrd, zero_mul, zero_add]

/-- A continuous function on `[-1,1]`, somewhere nonzero, has positive
squared mass. -/
theorem fwd_sq_integral_pos (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hnz : ∃ x ∈ Icc (-1 : ℝ) 1, f x ≠ 0) :
    0 < ∫ x in (-1 : ℝ)..1, f x * f x := by
  obtain ⟨x0, hx0, hfx0⟩ := hnz
  set g : ℝ → ℝ := fun x => f x * f x with hg
  have hgc : ContinuousOn g (Icc (-1 : ℝ) 1) := hfc.mul hfc
  have hgnn : ∀ x ∈ Icc (-1 : ℝ) 1, 0 ≤ g x := fun x _ => mul_self_nonneg (f x)
  have hgx0 : 0 < g x0 := by
    rw [hg]
    exact mul_self_pos.mpr hfx0
  -- a neighbourhood of `x0` inside the interval on which `g ≥ g x0 / 2`
  obtain ⟨η, hη0, hη⟩ : ∃ η > 0, ∀ x ∈ Icc (-1 : ℝ) 1,
      |x - x0| < η → g x0 / 2 < g x := by
    have hcw : ContinuousWithinAt g (Icc (-1 : ℝ) 1) x0 := hgc x0 hx0
    have hmem : {y : ℝ | g x0 / 2 < y} ∈ 𝓝 (g x0) :=
      IsOpen.mem_nhds isOpen_Ioi (by simpa using by linarith)
    have hpre := hcw hmem
    rw [Filter.mem_map, Metric.mem_nhdsWithin_iff] at hpre
    obtain ⟨η, hη0, hsub⟩ := hpre
    refine ⟨η, hη0, fun x hx hdist => ?_⟩
    have : x ∈ Metric.ball x0 η ∩ Icc (-1 : ℝ) 1 :=
      ⟨by simpa [Real.dist_eq] using hdist, hx⟩
    exact hsub this
  set τ : ℝ := min (η / 2) 1 with hτ
  have hτ0 : 0 < τ := by
    rw [hτ]
    exact lt_min (by linarith) one_pos
  have hτη : τ ≤ η / 2 := min_le_left _ _
  have hτ1 : τ ≤ 1 := min_le_right _ _
  set u : ℝ := max (-1) (x0 - τ) with hu
  set v : ℝ := min 1 (x0 + τ) with hv
  have hux : u ≤ x0 := max_le hx0.1 (by linarith)
  have hxv : x0 ≤ v := le_min hx0.2 (by linarith)
  have huv : u < v := by
    rcases le_total x0 0 with hx0s | hx0s
    · have hv' : x0 + τ ≤ 1 := by linarith
      have : v = x0 + τ := min_eq_right hv'
      rw [this]
      calc u ≤ x0 := hux
        _ < x0 + τ := by linarith
    · have hu' : -1 ≤ x0 - τ := by linarith [hx0.1]
      have : u = x0 - τ := max_eq_right hu'
      rw [this]
      calc x0 - τ < x0 := by linarith
        _ ≤ v := hxv
  have huI : u ∈ Icc (-1 : ℝ) 1 := ⟨le_max_left _ _, le_trans hux hx0.2⟩
  have hvI : v ∈ Icc (-1 : ℝ) 1 := ⟨le_trans hx0.1 hxv, min_le_left _ _⟩
  have hginta : ∀ a b : ℝ, a ∈ Icc (-1 : ℝ) 1 → b ∈ Icc (-1 : ℝ) 1 →
      IntervalIntegrable g volume a b := by
    intro a b ha hb
    exact ContinuousOn.intervalIntegrable
      (hgc.mono ((Set.ordConnected_Icc).uIcc_subset ha hb))
  have hmid : (g x0 / 2) * (v - u) ≤ ∫ x in u..v, g x := by
    have hconst : (∫ _x in u..v, g x0 / 2) = (g x0 / 2) * (v - u) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    rw [← hconst]
    refine intervalIntegral.integral_mono_on (le_of_lt huv)
      intervalIntegrable_const (hginta u v huI hvI) ?_
    intro x hx
    have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨le_trans huI.1 hx.1, le_trans hx.2 hvI.2⟩
    have hxdist : |x - x0| < η := by
      rw [abs_lt]
      constructor
      · have : u ≤ x := hx.1
        have hub : x0 - τ ≤ u := le_max_right _ _
        linarith
      · have : x ≤ v := hx.2
        have hvb : v ≤ x0 + τ := min_le_right _ _
        linarith
    exact le_of_lt (hη x hxI hxdist)
  have hleft : 0 ≤ ∫ x in (-1 : ℝ)..u, g x := by
    refine intervalIntegral.integral_nonneg huI.1 ?_
    intro x hx
    exact hgnn x ⟨hx.1, le_trans hx.2 huI.2⟩
  have hright : 0 ≤ ∫ x in v..(1 : ℝ), g x := by
    refine intervalIntegral.integral_nonneg hvI.2 ?_
    intro x hx
    exact hgnn x ⟨le_trans hvI.1 hx.1, hx.2⟩
  have hs1 : (∫ x in (-1 : ℝ)..u, g x) + (∫ x in u..v, g x)
      + (∫ x in v..(1 : ℝ), g x) = ∫ x in (-1 : ℝ)..1, g x := by
    rw [intervalIntegral.integral_add_adjacent_intervals
      (hginta (-1) u (by norm_num) huI) (hginta u v huI hvI),
      intervalIntegral.integral_add_adjacent_intervals
      (hginta (-1) v (by norm_num) hvI) (hginta v 1 hvI (by norm_num))]
  have hpos : 0 < (g x0 / 2) * (v - u) := by
    apply mul_pos (by linarith) (by linarith)
  calc (0 : ℝ) < (g x0 / 2) * (v - u) := hpos
    _ ≤ ∫ x in u..v, g x := hmid
    _ ≤ (∫ x in (-1 : ℝ)..u, g x) + (∫ x in u..v, g x)
        + (∫ x in v..(1 : ℝ), g x) := by linarith
    _ = ∫ x in (-1 : ℝ)..1, g x := hs1

/-- **Nontriviality.**  A continuous even function on the interval that is
somewhere nonzero has a nonzero even Legendre moment. -/
theorem fwd_exists_moment_ne_zero (f : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hev : ∀ x : ℝ, f (-x) = f x)
    (hnz : ∃ x ∈ Icc (-1 : ℝ) 1, f x ≠ 0) :
    ∃ k, fwdMoment f k ≠ 0 := by
  by_contra hall
  push_neg at hall
  have hpoly := fwd_poly_moment_zero f hfc hev hall
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ Cf := by
    obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hfc
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      le_trans (by simpa [Real.norm_eq_abs] using hCb x hx) (le_max_left _ _)⟩
  have hsq : (∫ x in (-1 : ℝ)..1, f x * f x) = 0 := by
    have hkey : ∀ ε : ℝ, 0 < ε → |∫ x in (-1 : ℝ)..1, f x * f x| ≤ ε := by
      intro ε hε
      set ε' : ℝ := ε / (2 * Cf + 1) with hε'
      have hε'0 : 0 < ε' := by
        rw [hε']
        positivity
      obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn (-1 : ℝ) 1 f
        hfc ε' hε'0
      have hdiff : (∫ x in (-1 : ℝ)..1, f x * f x)
          = ∫ x in (-1 : ℝ)..1, f x * (f x - p.eval x) := by
        have hintf : IntervalIntegrable (fun x : ℝ => f x * f x) volume (-1 : ℝ) 1 :=
          ContinuousOn.intervalIntegrable (by
            rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
            exact hfc.mul hfc)
        have hintp : IntervalIntegrable (fun x : ℝ => f x * p.eval x)
            volume (-1 : ℝ) 1 :=
          ContinuousOn.intervalIntegrable (by
            rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)]
            exact hfc.mul p.continuous.continuousOn)
        rw [show (fun x : ℝ => f x * (f x - p.eval x))
            = fun x : ℝ => f x * f x - f x * p.eval x from funext (fun x => by ring)]
        rw [intervalIntegral.integral_sub hintf hintp, hpoly p, sub_zero]
      rw [hdiff]
      have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := Cf * ε') (f := fun x : ℝ => f x * (f x - p.eval x))
        (a := (-1 : ℝ)) (b := 1) ?_
      · have h2 : Cf * ε' * |(1 : ℝ) - (-1)| = 2 * Cf * ε' := by
          rw [show |(1 : ℝ) - (-1)| = 2 by norm_num]
          ring
        have h3 : 2 * Cf * ε' ≤ ε := by
          rw [hε']
          have hd0 : 0 ≤ ε / (2 * Cf + 1) := by positivity
          have hmul : (2 * Cf + 1) * (ε / (2 * Cf + 1)) = ε :=
            mul_div_cancel₀ _ (by positivity)
          linarith [hd0, hmul]
        calc |∫ x in (-1 : ℝ)..1, f x * (f x - p.eval x)|
            ≤ Cf * ε' * |(1 : ℝ) - (-1)| := by
              simpa [Real.norm_eq_abs] using hnorm
          _ = 2 * Cf * ε' := h2
          _ ≤ ε := h3
      · intro x hx
        rw [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
        have hxI : x ∈ Icc (-1 : ℝ) 1 := ⟨le_of_lt hx.1, hx.2⟩
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |f x - p.eval x| ≤ ε' := by
          have := hp x hxI
          rw [abs_sub_comm]
          linarith [this]
        exact mul_le_mul (hCf x hxI) h1 (abs_nonneg _) hCf0
    by_contra hcon
    have habs : 0 < |∫ x in (-1 : ℝ)..1, f x * f x| := abs_pos.mpr hcon
    have hhalf := hkey (|∫ x in (-1 : ℝ)..1, f x * f x| / 2) (by linarith)
    linarith
  have hpos := fwd_sq_integral_pos f hfc hnz
  linarith

/-! ## The alternating weighted moment sequence solves the mode-four recursion -/

/-- The alternating, `(4q+1)`-weighted even moment sequence.  The weight is
the Legendre norm conversion (moments to expansion coefficients); the sign
converts the negative `(1-x²)` off-diagonals into the positive DLMF 30.3.7
convention. -/
noncomputable def fwdSeq (f : ℝ → ℝ) (q : ℕ) : ℝ :=
  (-1 : ℝ) ^ q * (4 * (q : ℝ) + 1) * fwdMoment f q

@[simp] theorem fwd_mode4JacobiLower_zero (G : ℝ) : mode4JacobiLower G 0 = 0 := by
  unfold mode4JacobiLower mode4JacobiIndex
  norm_num

/-- **The dictionary.**  The weighted moment sequence satisfies the project's
mode-four three-term recursion, uniformly in `q` (the `q = 0` boundary is
carried by `mode4JacobiLower G 0 = 0`). -/
theorem fwdSeq_rec (G Λ : ℝ) (f f1 f2 : ℝ → ℝ)
    (hfc : ContinuousOn f (Icc (-1 : ℝ) 1))
    (hfd : ∀ x ∈ Ioo (-1 : ℝ) 1, HasDerivAt f (f1 x) x ∧ HasDerivAt f1 (f2 x) x)
    (hfe : ∀ x ∈ Ioo (-1 : ℝ) 1,
      -(1 - x ^ 2) * f2 x + 2 * x * f1 x + G * x ^ 2 * f x = (Λ + G) * f x)
    (hfr : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[<] (1 : ℝ)) (𝓝 0))
    (hfl : Tendsto (fun x : ℝ => (1 - x ^ 2) * f1 x) (𝓝[>] (-1 : ℝ)) (𝓝 0))
    (q : ℕ) :
    mode4JacobiCenter G Λ q * fwdSeq f q
      = mode4JacobiLower G q * fwdSeq f (q - 1)
        + mode4JacobiUpper G q * fwdSeq f (q + 1) := by
  match q with
  | 0 =>
    have hrec := fwdMoment_rec G Λ f f1 f2 hfc hfd hfe hfr hfl 0
    have hI0 : mode4JacobiCenter G Λ 0 = -Λ - G * jacB 0 := by
      unfold mode4JacobiCenter mode4JacobiIndex jacB lcU lcV lcS lcT
      norm_num
      ring
    have hII0 : mode4JacobiUpper G 0 * 5 = -(G * jacA 0) * 1 := by
      unfold mode4JacobiUpper mode4JacobiIndex jacA lcU lcS
      norm_num
      ring
    have hL0 : mode4JacobiLower G 0 = 0 := fwd_mode4JacobiLower_zero G
    have hC0 : jacC 0 = 0 := jacC_zero
    unfold fwdSeq
    simp only [Nat.zero_sub, Nat.cast_zero, pow_zero]
    push_cast at hrec ⊢
    linear_combination (fwdMoment f 0) * hI0 + hrec + (fwdMoment f 1) * hII0
      + (G * fwdMoment f 0) * hC0 + (-(fwdMoment f 0)) * hL0
  | (j + 1) =>
    have hrec := fwdMoment_rec G Λ f f1 f2 hfc hfd hfe hfr hfl (j + 1)
    have h1 : (1 + (j : ℝ) * 4) ≠ 0 := by positivity
    have h3 : (3 + (j : ℝ) * 4) ≠ 0 := by positivity
    have h5 : (5 + (j : ℝ) * 4) ≠ 0 := by positivity
    have h7 : (7 + (j : ℝ) * 4) ≠ 0 := by positivity
    have h9 : (9 + (j : ℝ) * 4) ≠ 0 := by positivity
    have hI : mode4JacobiCenter G Λ (j + 1)
        = ((2 * ((j : ℝ) + 1)) * (2 * ((j : ℝ) + 1) + 1) - Λ) - G * jacB (j + 1) := by
      unfold mode4JacobiCenter mode4JacobiIndex jacB lcU lcV lcS lcT
      simp only [Nat.add_sub_cancel]
      push_cast
      ring_nf
      field_simp
      ring
    have hII : mode4JacobiUpper G (j + 1) * (4 * ((j : ℝ) + 1) + 5)
        = -(G * jacA (j + 1)) * (4 * ((j : ℝ) + 1) + 1) := by
      unfold mode4JacobiUpper mode4JacobiIndex jacA lcU lcS
      push_cast
      ring_nf
      field_simp
      ring
    have hIII : mode4JacobiLower G (j + 1) * (4 * ((j : ℝ) + 1) - 3)
        = -(G * jacC (j + 1)) * (4 * ((j : ℝ) + 1) + 1) := by
      unfold mode4JacobiLower mode4JacobiIndex jacC lcV lcT
      simp only [Nat.add_sub_cancel]
      push_cast
      ring_nf
      field_simp
      ring
    unfold fwdSeq
    simp only [Nat.add_sub_cancel]
    push_cast at hrec ⊢
    simp only [pow_succ]
    linear_combination
      (-(((-1 : ℝ) ^ j) * (4 * (j : ℝ) + 5)) * fwdMoment f (j + 1)) * hI
      + (-(((-1 : ℝ) ^ j) * (4 * (j : ℝ) + 5))) * hrec
      + (-((-1 : ℝ) ^ j) * fwdMoment f (j + 1 + 1)) * hII
      + (-((-1 : ℝ) ^ j) * fwdMoment f j) * hIII

/-- Polynomial bound on the weighted sequence. -/
theorem fwdSeq_abs_le (f : ℝ → ℝ) (Cf : ℝ)
    (hCf : ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ Cf) (q : ℕ) :
    |fwdSeq f q| ≤ (4 * (q : ℝ) + 1) * (2 * Cf) := by
  have h1 : (0 : ℝ) < 4 * (q : ℝ) + 1 := by positivity
  rw [fwdSeq, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_pos h1]
  exact mul_le_mul_of_nonneg_left (fwdMoment_abs_le f Cf hCf q) (le_of_lt h1)

/-- If the head of a mode-four recursion solution vanishes, the whole
solution vanishes. -/
theorem fwdSeq_zero_propagate (G Λ : ℝ) (a : ℕ → ℝ)
    (hG : 0 < G)
    (hrec : ∀ q : ℕ, mode4JacobiCenter G Λ q * a q
      = mode4JacobiLower G q * a (q - 1) + mode4JacobiUpper G q * a (q + 1))
    (h0 : a 0 = 0) :
    ∀ q, a q = 0 := by
  have hstep : ∀ q : ℕ, a q = 0 → a (q - 1) = 0 → a (q + 1) = 0 := by
    intro q hq hqm
    have h := hrec q
    rw [hq, hqm, mul_zero, mul_zero, zero_add] at h
    have hU : mode4JacobiUpper G q ≠ 0 := (mode4JacobiUpper_pos G q hG).ne'
    exact (mul_eq_zero.mp h.symm).resolve_left hU
  have hpair : ∀ q : ℕ, a q = 0 ∧ a (q + 1) = 0 := by
    intro q
    induction q with
    | zero => exact ⟨h0, hstep 0 h0 (by simpa using h0)⟩
    | succ n ihn =>
      refine ⟨ihn.2, hstep (n + 1) ihn.2 (by simpa using ihn.1)⟩
  exact fun q => (hpair q).1

/-- The weighted sequence is proportional to the left continuant. -/
theorem fwdSeq_eq_head_mul_leftPair (G Λ : ℝ) (a : ℕ → ℝ)
    (hG : 0 < G)
    (hrec : ∀ q : ℕ, mode4JacobiCenter G Λ q * a q
      = mode4JacobiLower G q * a (q - 1) + mode4JacobiUpper G q * a (q + 1)) :
    ∀ q : ℕ, a q = a 0 * (mode4LeftPair G Λ q).2 := by
  have hUne : ∀ q : ℕ, mode4JacobiUpper G q ≠ 0 :=
    fun q => (mode4JacobiUpper_pos G q hG).ne'
  have hsnd : ∀ n : ℕ, (mode4LeftPair G Λ (n + 1)).2
      = (mode4JacobiCenter G Λ n * (mode4LeftPair G Λ n).2
        - mode4JacobiLower G n * (mode4LeftPair G Λ n).1)
        / mode4JacobiUpper G n := fun n => rfl
  have hfst : ∀ n : ℕ, (mode4LeftPair G Λ (n + 1)).1
      = (mode4LeftPair G Λ n).2 := fun n => rfl
  have hpairInd : ∀ n : ℕ, a n = a 0 * (mode4LeftPair G Λ n).2
      ∧ a (n + 1) = a 0 * (mode4LeftPair G Λ (n + 1)).2 := by
    intro n
    induction n with
    | zero =>
      have hbase : a 0 = a 0 * (mode4LeftPair G Λ 0).2 := by
        simp [mode4LeftPair]
      refine ⟨hbase, ?_⟩
      have h := hrec 0
      rw [fwd_mode4JacobiLower_zero, zero_mul, zero_add] at h
      rw [hsnd 0]
      have hzero : (mode4LeftPair G Λ 0).1 = 0 := rfl
      have hone : (mode4LeftPair G Λ 0).2 = 1 := rfl
      rw [hzero, hone]
      have hU0 := hUne 0
      field_simp
      linarith [h]
    | succ n ihn =>
      refine ⟨ihn.2, ?_⟩
      have h := hrec (n + 1)
      have hm : n + 1 - 1 = n := by omega
      rw [hm, ihn.1, ihn.2] at h
      rw [hsnd (n + 1), hfst n]
      have hU := hUne (n + 1)
      field_simp
      linarith [h]
  exact fun q => (hpairInd q).1

/-! ## Pincherle uniqueness in the contraction domain, Wronskian-vanishing form -/

/-- The backward-tail product solution: `fwdTailProd n` is the minimal
solution value `b_{K-1+n}`, normalized by `b_{K-1} = 1`. -/
noncomputable def fwdTailProd (mProject : ℕ) (Λ : ℝ) (K : ℕ) : ℕ → ℝ
  | 0 => 1
  | n + 1 => fwdTailProd mProject Λ K n * mode4RightTailLimit mProject Λ (K + n)

/-- Beyond the cutoff the project lower coefficient dominates the upper one. -/
theorem fwd_lower_ge_upper (G : ℝ) (q : ℕ) (hG : 0 < G) (hq : 3 ≤ q) :
    mode4JacobiUpper G q ≤ mode4JacobiLower G q := by
  have hqR : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  unfold mode4JacobiUpper mode4JacobiLower mode4JacobiIndex
  have hd1 : (0 : ℝ) < (2 * (2 * (q : ℝ)) - 3) * (2 * (2 * (q : ℝ)) - 1) := by
    apply mul_pos <;> linarith
  have hd2 : (0 : ℝ) < (2 * (2 * (q : ℝ)) + 3) * (2 * (2 * (q : ℝ)) + 5) := by
    apply mul_pos <;> linarith
  rw [div_le_div_iff₀ hd2 hd1]
  have hkey : (0 : ℝ) ≤ 64 * (q : ℝ) ^ 3 + 48 * (q : ℝ) ^ 2 - 16 * (q : ℝ) - 6 := by
    nlinarith [hqR, sq_nonneg ((q : ℝ) - 3)]
  nlinarith [mul_nonneg hG.le hkey]

/-- **The pair lock.**  A polynomially bounded solution of the mode-four
recursion matches the right-tail ratio at the cutoff. -/
theorem fwd_boundedSolution_pair_lock
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (a : ℕ → ℝ) (Cf : ℝ) (hCf0 : 0 ≤ Cf)
    (habs : ∀ q : ℕ, |a q| ≤ (4 * (q : ℝ) + 1) * (2 * Cf))
    (hrec : ∀ q : ℕ, mode4JacobiCenter (mode4JacobiG mProject) Λ q * a q
      = mode4JacobiLower (mode4JacobiG mProject) q * a (q - 1)
        + mode4JacobiUpper (mode4JacobiG mProject) q * a (q + 1)) :
    a K = mode4RightTailLimit mProject Λ K * a (K - 1) := by
  set G := mode4JacobiG mProject with hGdef
  have hG : 0 < G := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
    rw [hGdef]
    unfold mode4JacobiG
    positivity
  -- shifted hypotheses at every index `q ≥ K`
  have hshift : ∀ q : ℕ, K ≤ q → (3 ≤ q ∧
      ∀ r ≥ q, (31 / 24 : ℝ) * G ≤
        mode4JacobiIndex r * (mode4JacobiIndex r + 1) - 20) := by
    intro q hq
    exact ⟨le_trans hK hq, fun r hr => hsep r (le_trans hq hr)⟩
  set x : ℕ → ℝ := fun q => mode4RightTailLimit mProject Λ q with hx
  have hxmem : ∀ q : ℕ, K ≤ q → x q ∈ Icc (0 : ℝ) (1 / 2) := by
    intro q hq
    obtain ⟨h3, hs⟩ := hshift q hq
    exact mode4RightTailLimit_mem_Icc mProject q Λ hm h3 hs hΛ
  have hxfix : ∀ q : ℕ, K ≤ q →
      x q * (mode4JacobiCenter G Λ q - mode4JacobiUpper G q * x (q + 1))
        = mode4JacobiLower G q := by
    intro q hq
    obtain ⟨h3, hs⟩ := hshift q hq
    have hfix := mode4RightTailLimit_eq_tailMap_succ mProject q Λ hm h3 hs hΛ
    have hmemSucc : x (q + 1) ∈ Icc (0 : ℝ) (1 / 2) :=
      hxmem (q + 1) (le_trans hq (Nat.le_succ q))
    have hden : (2 / 3 : ℝ) * G ≤
        mode4JacobiCenter G Λ q - mode4JacobiUpper G q * x (q + 1) :=
      mode4JacobiCenter_sub_upper_mul_lower_bound G Λ (x (q + 1)) q hG h3
        (hs q le_rfl) hΛ hmemSucc
    have hdne : mode4JacobiCenter G Λ q - mode4JacobiUpper G q * x (q + 1) ≠ 0 := by
      have : (0 : ℝ) < (2 / 3 : ℝ) * G := by positivity
      linarith
    have hfix' : x q = mode4TailMap G Λ q (x (q + 1)) := hfix
    rw [hfix']
    unfold mode4TailMap
    field_simp
  set P : ℕ → ℝ := fwdTailProd mProject Λ K with hP
  have hPzero : P 0 = 1 := rfl
  have hPsucc : ∀ n : ℕ, P (n + 1) = P n * x (K + n) := fun n => rfl
  have hPbounds : ∀ n : ℕ, 0 ≤ P n ∧ P n ≤ (1 / 2 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => rw [hPzero]; norm_num
    | succ n ihn =>
      have hmemx : x (K + n) ∈ Icc (0 : ℝ) (1 / 2) :=
        hxmem (K + n) (Nat.le_add_right K n)
      constructor
      · rw [hPsucc n]
        exact mul_nonneg ihn.1 hmemx.1
      · rw [hPsucc n, pow_succ]
        exact mul_le_mul ihn.2 hmemx.2 hmemx.1 (by positivity)
  have hPrec : ∀ n : ℕ,
      mode4JacobiCenter G Λ (K + n) * P (n + 1)
        = mode4JacobiLower G (K + n) * P n
          + mode4JacobiUpper G (K + n) * P (n + 2) := by
    intro n
    have hfix := hxfix (K + n) (Nat.le_add_right K n)
    have h2 : P (n + 2) = P (n + 1) * x (K + n + 1) := by
      have := hPsucc (n + 1)
      rwa [show K + (n + 1) = K + n + 1 by omega] at this
    rw [hPsucc n, h2, hPsucc n]
    have := congrArg (fun t => t * P n) hfix
    simp only at this
    ring_nf
    ring_nf at this
    linarith [this]
  -- the transported determinant
  set δ : ℕ → ℝ := fun n => a (K + n) * P n - a (K + n - 1) * P (n + 1) with hδ
  have htrans : ∀ n : ℕ,
      mode4JacobiUpper G (K + n) * δ (n + 1) = mode4JacobiLower G (K + n) * δ n := by
    intro n
    have hra := hrec (K + n)
    have hidx2 : K + (n + 1) = K + n + 1 := by omega
    have hPr := hPrec n
    rw [hδ]
    simp only [hidx2]
    -- U * (a(K+n+1) P(n+1) - a(K+n) P(n+2)) = L * (a(K+n) P n - a(K+n-1) P(n+1))
    have hUa : mode4JacobiUpper G (K + n) * a (K + n + 1)
        = mode4JacobiCenter G Λ (K + n) * a (K + n)
          - mode4JacobiLower G (K + n) * a (K + n - 1) := by
      linarith [hra]
    calc mode4JacobiUpper G (K + n) * (a (K + n + 1) * P (n + 1) - a (K + n) * P (n + 2))
        = (mode4JacobiUpper G (K + n) * a (K + n + 1)) * P (n + 1)
          - a (K + n) * (mode4JacobiUpper G (K + n) * P (n + 2)) := by ring
      _ = (mode4JacobiCenter G Λ (K + n) * a (K + n)
            - mode4JacobiLower G (K + n) * a (K + n - 1)) * P (n + 1)
          - a (K + n) * (mode4JacobiCenter G Λ (K + n) * P (n + 1)
            - mode4JacobiLower G (K + n) * P n) := by
          rw [hUa]
          have : mode4JacobiUpper G (K + n) * P (n + 2)
              = mode4JacobiCenter G Λ (K + n) * P (n + 1)
                - mode4JacobiLower G (K + n) * P n := by linarith [hPr]
          rw [this]
      _ = mode4JacobiLower G (K + n) * (a (K + n) * P n - a (K + n - 1) * P (n + 1)) := by
          ring
  -- |δ| is nondecreasing
  have hmono : ∀ n : ℕ, |δ n| ≤ |δ (n + 1)| := by
    intro n
    have hq3 : 3 ≤ K + n := le_trans hK (Nat.le_add_right K n)
    have hL : 0 < mode4JacobiLower G (K + n) := mode4JacobiLower_pos G (K + n) hG hq3
    have hU : 0 < mode4JacobiUpper G (K + n) := mode4JacobiUpper_pos G (K + n) hG
    have hLU : mode4JacobiUpper G (K + n) ≤ mode4JacobiLower G (K + n) :=
      fwd_lower_ge_upper G (K + n) hG hq3
    have habseq : mode4JacobiLower G (K + n) * |δ n|
        = mode4JacobiUpper G (K + n) * |δ (n + 1)| := by
      rw [← abs_of_pos hL, ← abs_of_pos hU, ← abs_mul, ← abs_mul, htrans n]
    nlinarith [abs_nonneg (δ n), abs_nonneg (δ (n + 1))]
  have hmono' : ∀ n : ℕ, |δ 0| ≤ |δ n| := by
    intro n
    induction n with
    | zero => exact le_rfl
    | succ n ihn => exact le_trans ihn (hmono n)
  -- |δ n| collapses geometrically
  have hnat_pow : ∀ n : ℕ, (n : ℝ) ≤ 4 * (5 / 4 : ℝ) ^ n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ihn =>
      have hpow : (1 : ℝ) ≤ (5 / 4 : ℝ) ^ n := one_le_pow₀ (by norm_num)
      push_cast
      rw [pow_succ]
      nlinarith
  have hδbound : ∀ n : ℕ, |δ n| ≤ (4 * (K : ℝ) + 17) * (4 * Cf) * (5 / 8 : ℝ) ^ n := by
    intro n
    have hPb := hPbounds n
    have hPb1 := hPbounds (n + 1)
    have ha1 := habs (K + n)
    have ha2 := habs (K + n - 1)
    have hcast1 : ((K + n : ℕ) : ℝ) = (K : ℝ) + n := by push_cast; ring
    have hcast2 : ((K + n - 1 : ℕ) : ℝ) ≤ (K : ℝ) + n := by
      have : (K + n - 1 : ℕ) ≤ K + n := by omega
      calc ((K + n - 1 : ℕ) : ℝ) ≤ ((K + n : ℕ) : ℝ) := by exact_mod_cast this
        _ = (K : ℝ) + n := hcast1
    have ha1' : |a (K + n)| ≤ (4 * ((K : ℝ) + n) + 1) * (2 * Cf) := by
      rw [hcast1] at ha1
      exact ha1
    have ha2' : |a (K + n - 1)| ≤ (4 * ((K : ℝ) + n) + 1) * (2 * Cf) := by
      refine le_trans ha2 ?_
      have h4 : (4 : ℝ) * ((K + n - 1 : ℕ) : ℝ) + 1 ≤ 4 * ((K : ℝ) + n) + 1 := by
        linarith [hcast2]
      exact mul_le_mul_of_nonneg_right h4 (by positivity)
    have hW : (4 * ((K : ℝ) + n) + 1) ≥ 0 := by positivity
    have habs1 : |a (K + n) * P n| ≤ (4 * ((K : ℝ) + n) + 1) * (2 * Cf) * (1 / 2 : ℝ) ^ n := by
      rw [abs_mul, abs_of_nonneg hPb.1]
      exact mul_le_mul ha1' hPb.2 hPb.1 (by positivity)
    have habs2 : |a (K + n - 1) * P (n + 1)|
        ≤ (4 * ((K : ℝ) + n) + 1) * (2 * Cf) * (1 / 2 : ℝ) ^ n := by
      rw [abs_mul, abs_of_nonneg hPb1.1]
      refine le_trans (mul_le_mul ha2' hPb1.2 hPb1.1 (by positivity)) ?_
      have hstep : ((1 : ℝ) / 2) ^ (n + 1) ≤ ((1 : ℝ) / 2) ^ n := by
        rw [pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) n]
      exact mul_le_mul_of_nonneg_left hstep (by positivity)
    have htri : |δ n| ≤ |a (K + n) * P n| + |a (K + n - 1) * P (n + 1)| := by
      rw [hδ]
      exact abs_sub _ _
    have hcollect : |δ n| ≤ (4 * (K : ℝ) + 1 + 4 * n) * (4 * Cf) * (1 / 2 : ℝ) ^ n := by
      calc |δ n| ≤ (4 * ((K : ℝ) + n) + 1) * (2 * Cf) * (1 / 2 : ℝ) ^ n
            + (4 * ((K : ℝ) + n) + 1) * (2 * Cf) * (1 / 2 : ℝ) ^ n := by
            linarith [htri, habs1, habs2]
        _ = (4 * (K : ℝ) + 1 + 4 * n) * (4 * Cf) * (1 / 2 : ℝ) ^ n := by ring
    have hhalf_le : ((1 : ℝ) / 2) ^ n ≤ ((5 : ℝ) / 8) ^ n := by
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
    have hn58 : (n : ℝ) * ((1 : ℝ) / 2) ^ n ≤ 4 * ((5 : ℝ) / 8) ^ n := by
      have h1 : (n : ℝ) * ((1 : ℝ) / 2) ^ n ≤ (4 * (5 / 4 : ℝ) ^ n) * ((1 : ℝ) / 2) ^ n :=
        mul_le_mul_of_nonneg_right (hnat_pow n) (by positivity)
      have h2 : (4 * (5 / 4 : ℝ) ^ n) * ((1 : ℝ) / 2) ^ n = 4 * ((5 : ℝ) / 8) ^ n := by
        rw [mul_assoc, ← mul_pow]
        norm_num
      rw [h2] at h1
      exact h1
    calc |δ n| ≤ (4 * (K : ℝ) + 1 + 4 * n) * (4 * Cf) * (1 / 2 : ℝ) ^ n := hcollect
      _ = (4 * (K : ℝ) + 1) * (4 * Cf) * ((1 / 2 : ℝ) ^ n)
          + (4 * Cf) * (4 * ((n : ℝ) * ((1 / 2 : ℝ) ^ n))) := by ring
      _ ≤ (4 * (K : ℝ) + 1) * (4 * Cf) * ((5 / 8 : ℝ) ^ n)
          + (4 * Cf) * (4 * (4 * ((5 : ℝ) / 8) ^ n)) := by
          have t1 : (4 * (K : ℝ) + 1) * (4 * Cf) * ((1 / 2 : ℝ) ^ n)
              ≤ (4 * (K : ℝ) + 1) * (4 * Cf) * ((5 / 8 : ℝ) ^ n) :=
            mul_le_mul_of_nonneg_left hhalf_le (by positivity)
          have t2 : (4 * Cf) * (4 * ((n : ℝ) * ((1 / 2 : ℝ) ^ n)))
              ≤ (4 * Cf) * (4 * (4 * ((5 : ℝ) / 8) ^ n)) := by
            have := mul_le_mul_of_nonneg_left hn58
              (by positivity : (0 : ℝ) ≤ 4)
            exact mul_le_mul_of_nonneg_left this (by positivity)
          linarith
      _ = (4 * (K : ℝ) + 17) * (4 * Cf) * (5 / 8 : ℝ) ^ n := by ring
  -- conclude δ 0 = 0
  have hδ0 : δ 0 = 0 := by
    by_contra hne
    have hpos : 0 < |δ 0| := abs_pos.mpr hne
    set D : ℝ := (4 * (K : ℝ) + 17) * (4 * Cf) + 1 with hD
    have hD0 : 0 < D := by positivity
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one
      (show (0 : ℝ) < |δ 0| / D by positivity)
      (show (5 / 8 : ℝ) < 1 by norm_num)
    have hchain : |δ 0| ≤ (4 * (K : ℝ) + 17) * (4 * Cf) * (5 / 8 : ℝ) ^ n :=
      le_trans (hmono' n) (hδbound n)
    have hstep : (4 * (K : ℝ) + 17) * (4 * Cf) * (5 / 8 : ℝ) ^ n
        < D * (|δ 0| / D) := by
      have hpow0 : (0 : ℝ) ≤ (5 / 8 : ℝ) ^ n := by positivity
      have hlt : (5 / 8 : ℝ) ^ n < |δ 0| / D := hn
      have hcoef : (4 * (K : ℝ) + 17) * (4 * Cf) < D := by
        rw [hD]
        linarith
      nlinarith [hpow0, hlt, hcoef, hD0]
    have hcancel : D * (|δ 0| / D) = |δ 0| := by
      field_simp
    rw [hcancel] at hstep
    linarith [hchain, hstep]
  -- unfold δ 0
  have hP1 : P 1 = x K := by
    rw [hPsucc 0, hPzero, one_mul, Nat.add_zero]
  rw [hδ] at hδ0
  simp only [Nat.add_zero] at hδ0
  rw [hPzero, hP1, mul_one] at hδ0
  rw [hx] at hδ0
  linarith [hδ0]

/-! ## Assembly: forward membership -/

/-- **A regular even spheroidal eigenvalue is a root of the project residual.**
The eigenfunction's weighted Legendre moments are a nontrivial, polynomially
bounded solution of the mode-four recursion; Pincherle uniqueness locks its
left continuant to the right-tail ratio. -/
theorem mode4RootFunction_eq_zero_of_regularEvenSpheroidal
    (mProject K : ℕ) (Λ : ℝ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep :
      ∀ q ≥ K,
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (h : RegularEvenSpheroidalEigenvalue (mode4JacobiG mProject) Λ) :
    mode4RootFunction mProject K Λ = 0 := by
  set G := mode4JacobiG mProject with hGdef
  have hG : 0 < G := by
    have hmR : (0 : ℝ) < (mProject : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
    rw [hGdef]
    unfold mode4JacobiG
    positivity
  obtain ⟨f, f1, f2, hnz, hev, hfc, hfd, hfe, hfr, hfl⟩ := h
  set a : ℕ → ℝ := fwdSeq f with ha
  have hrecAll : ∀ q : ℕ, mode4JacobiCenter G Λ q * a q
      = mode4JacobiLower G q * a (q - 1) + mode4JacobiUpper G q * a (q + 1) :=
    fun q => fwdSeq_rec G Λ f f1 f2 hfc hfd hfe hfr hfl q
  obtain ⟨Cf, hCf0, hCf⟩ : ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |f x| ≤ Cf := by
    obtain ⟨C, hCb⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
      hfc
    exact ⟨max C 0, le_max_right _ _, fun x hx =>
      le_trans (by simpa [Real.norm_eq_abs] using hCb x hx) (le_max_left _ _)⟩
  have habs : ∀ q : ℕ, |a q| ≤ (4 * (q : ℝ) + 1) * (2 * Cf) :=
    fun q => fwdSeq_abs_le f Cf hCf q
  have hhead : a 0 ≠ 0 := by
    intro h0
    have hallzero := fwdSeq_zero_propagate G Λ a hG hrecAll h0
    have hallM : ∀ k, fwdMoment f k = 0 := by
      intro k
      have hz := hallzero k
      rw [ha, fwdSeq] at hz
      have hcoef : ((-1 : ℝ) ^ k * (4 * (k : ℝ) + 1)) ≠ 0 := by
        apply mul_ne_zero
        · exact pow_ne_zero k (by norm_num)
        · positivity
      rcases mul_eq_zero.mp hz with hcase | hcase
      · exact absurd hcase hcoef
      · exact hcase
    obtain ⟨k, hk⟩ := fwd_exists_moment_ne_zero f hfc hev hnz
    exact hk (hallM k)
  have hprop := fwdSeq_eq_head_mul_leftPair G Λ a hG hrecAll
  have hlock := fwd_boundedSolution_pair_lock mProject K Λ hm hK hsep hΛ
    a Cf hCf0 habs (by
      intro q
      have := hrecAll q
      rw [hGdef] at this
      exact this)
  have hKpair : a K = a 0 * (mode4LeftPair G Λ K).2 := hprop K
  have hKm1pair : a (K - 1) = a 0 * (mode4LeftPair G Λ K).1 := by
    have h1 := hprop (K - 1)
    have hfst : (mode4LeftPair G Λ K).1 = (mode4LeftPair G Λ (K - 1)).2 := by
      have hKeq : K - 1 + 1 = K := by omega
      calc (mode4LeftPair G Λ K).1
          = (mode4LeftPair G Λ (K - 1 + 1)).1 := by rw [hKeq]
        _ = (mode4LeftPair G Λ (K - 1)).2 := rfl
    rw [hfst]
    exact h1
  have hzero : a 0 * ((mode4LeftPair G Λ K).2
      - mode4RightTailLimit mProject Λ K * (mode4LeftPair G Λ K).1) = 0 := by
    rw [hGdef] at hKpair hKm1pair
    rw [hKpair, hKm1pair] at hlock
    rw [hGdef]
    linarith [hlock]
  have hres : (mode4LeftPair G Λ K).2
      - mode4RightTailLimit mProject Λ K * (mode4LeftPair G Λ K).1 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left hhead
  unfold mode4RootFunction
  rw [hGdef] at hres
  linarith [hres]

/-- **U2.3, verdict shape.**  Every value of the source-pure even branch below
the cutoff satisfies the pole-safe DLMF 30.3.5 even characteristic equation at
the locked split.  One-way only. -/
theorem evenBranch_mode4DLMF3035EvenCharacteristic
    (mProject K r : ℕ)
    (hm : 2 ≤ mProject)
    (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mProject ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (P : BookRegularEvenSpectrumEven (mode4JacobiG mProject))
    (hcut : P.evenBranch r < 20) :
    mode4DLMF3035EvenCharacteristicEquation
      (mode4JacobiG mProject)
      (P.evenBranch r)
      (2 * (K - 1)) := by
  have hΛ : P.evenBranch r ≤ 20 := le_of_lt hcut
  have hroot : mode4RootFunction mProject K (P.evenBranch r) = 0 :=
    mode4RootFunction_eq_zero_of_regularEvenSpheroidal mProject K (P.evenBranch r)
      hm hK hsep hΛ (P.evenBranch_regular r)
  exact (mode4DLMF3035EvenCharacteristicEquation_iff_rootFunction_eq_zero
    mProject K (P.evenBranch r) hm hK hsep hΛ).mpr hroot

#print axioms mode4RootFunction_eq_zero_of_regularEvenSpheroidal
#print axioms evenBranch_mode4DLMF3035EvenCharacteristic

end Q3.RouteB
