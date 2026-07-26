import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.OpenMapping
import Q3.Proofs.RouteB.ZeroEscapeLogic

set_option linter.mathlibStandardSet false

open Filter Set Metric
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- A quantitative open-mapping replacement for the one-disk Rouché step.
If an entire function is close to a function with a zero at the center and a
positive boundary modulus, it has a zero in the closed disk. -/
theorem exists_zero_closedBall_of_uniform_close
    {f g : ℂ → ℂ} {z₀ : ℂ} {r ε : ℝ}
    (hg : Differentiable ℂ g)
    (hr : 0 < r) (hε : 0 < ε)
    (hf0 : f z₀ = 0)
    (hboundary : ∀ z ∈ sphere z₀ r, ε ≤ ‖f z‖)
    (hclose : ∀ z ∈ closedBall z₀ r, ‖g z - f z‖ < ε / 4) :
    ∃ w ∈ closedBall z₀ r, g w = 0 := by
  have hcenter : ‖g z₀‖ < ε / 4 := by
    have hz₀ : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
    simpa [hf0] using hclose z₀ hz₀
  have hsep : ∀ z ∈ sphere z₀ r, ε / 2 ≤ ‖g z - g z₀‖ := by
    intro z hz
    have hz' : z ∈ closedBall z₀ r := sphere_subset_closedBall hz
    have h1 := hclose z hz'
    have h0 := hclose z₀ (mem_closedBall_self hr.le)
    have htri : dist (f z) (f z₀) ≤
        dist (f z) (g z) + dist (g z) (g z₀) + dist (g z₀) (f z₀) :=
      dist_triangle4 _ _ _ _
    simp only [dist_eq_norm] at htri
    rw [hf0, sub_zero] at htri
    have h1' : ‖f z - g z‖ < ε / 4 := by simpa [norm_sub_rev] using h1
    have h0' : ‖g z₀ - f z₀‖ < ε / 4 := h0
    rw [hf0] at h0'
    linarith [hboundary z hz]
  have hfrequent : ∃ᶠ z in 𝓝 z₀, g z ≠ g z₀ := by
    by_contra h
    have hevent : ∀ᶠ z in 𝓝 z₀, g z = g z₀ := by
      simpa only [not_frequently, not_not] using h
    have hgan : AnalyticOnNhd ℂ g Set.univ :=
      Complex.analyticOnNhd_univ_iff_differentiable.mpr hg
    have hconst : AnalyticOnNhd ℂ (fun _ : ℂ => g z₀) Set.univ := analyticOnNhd_const
    have heq : g = (fun _ : ℂ => g z₀) := hgan.eq_of_eventuallyEq hconst hevent
    obtain ⟨z, hz⟩ : (sphere z₀ r).Nonempty :=
      NormedSpace.sphere_nonempty.mpr hr.le
    have := hsep z hz
    rw [congr_fun heq z, congr_fun heq z₀, sub_self, norm_zero] at this
    linarith
  have himage := (hg.diffContOnCl (s := ball z₀ r)).ball_subset_image_closedBall
    hr hsep hfrequent
  have hzero : (0 : ℂ) ∈ ball (g z₀) ((ε / 2) / 2) := by
    rw [mem_ball, dist_zero_left]
    have hdiv : ε / 4 = (ε / 2) / 2 := by ring
    simpa only [hdiv] using hcenter
  obtain ⟨w, hw, hgw⟩ := himage hzero
  exact ⟨w, hw, hgw⟩

/-- A nontrivial entire limit has an approximating zero eventually in every
prescribed closed disk around each of its zeros, provided the convergence is
locally uniform on an open set containing that disk. -/
theorem eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn_local
    {U : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hz₀U : z₀ ∈ U)
    (hFentire : ∀ n, Differentiable ℂ (F n))
    (hfholomorphic : DifferentiableOn ℂ f U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hf_not_local_zero : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0)
    (hf0 : f z₀ = 0)
    (hR : 0 < R) :
    ∀ᶠ n in atTop, ∃ w ∈ closedBall z₀ R, F n w = 0 := by
  have hpunc : ∀ᶠ z in 𝓝[({z₀}ᶜ)] z₀, f z ≠ 0 :=
    (hfholomorphic.analyticAt (hU.mem_nhds hz₀U)).eventually_eq_zero_or_eventually_ne_zero.resolve_left
      hf_not_local_zero
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hpunc
  obtain ⟨ρ, hρ, hpunc⟩ := hpunc
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀U)
  let r : ℝ := min (min (ρ / 2) (R / 2)) (δ / 2)
  have hr : 0 < r := (lt_min_iff).mpr ⟨
    (lt_min_iff).mpr ⟨half_pos hρ, half_pos hR⟩, half_pos hδ⟩
  have hrρ : r < ρ :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_left _ _)) (half_lt_self hρ)
  have hrR : r < R :=
    lt_of_le_of_lt (le_trans (min_le_left _ _) (min_le_right _ _)) (half_lt_self hR)
  have hrδ : r < δ :=
    lt_of_le_of_lt (min_le_right _ _) (half_lt_self hδ)
  have hballU : closedBall z₀ r ⊆ U := by
    intro w hw
    apply hδU
    rw [mem_ball]
    exact (mem_closedBall.mp hw).trans_lt hrδ
  have hfsphere : ∀ w ∈ sphere z₀ r, f w ≠ 0 := by
    intro w hw
    apply hpunc (show dist w z₀ < ρ by simpa [mem_sphere.mp hw] using hrρ)
    exact ne_of_mem_sphere hw hr.ne.symm
  have hsph_nonempty : (sphere z₀ r).Nonempty :=
    NormedSpace.sphere_nonempty.mpr hr.le
  have hcont : ContinuousOn (fun w => ‖f w‖) (sphere z₀ r) :=
    continuous_norm.comp_continuousOn
      (hfholomorphic.continuousOn.mono fun w hw =>
        hballU (sphere_subset_closedBall hw))
  obtain ⟨w₀, hw₀, hw₀min⟩ :=
    (isCompact_sphere z₀ r).exists_isMinOn hsph_nonempty hcont
  let m : ℝ := ‖f w₀‖
  have hm : 0 < m := norm_pos_iff.mpr (hfsphere w₀ hw₀)
  have hflower : ∀ w ∈ sphere z₀ r, m ≤ ‖f w‖ := by
    intro w hw
    exact hw₀min hw
  have hunif : TendstoUniformlyOn F f atTop (closedBall z₀ r) :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).mp hconv
      (closedBall z₀ r) hballU (isCompact_closedBall z₀ r)
  rw [tendstoUniformlyOn_iff] at hunif
  have hquarter : 0 < m / 4 := div_pos hm (by norm_num)
  filter_upwards [hunif (m / 4) hquarter] with n hn
  have hclose : ∀ w ∈ closedBall z₀ r, ‖F n w - f w‖ < m / 4 := by
    intro w hw
    simpa only [dist_eq_norm, norm_sub_rev] using hn w hw
  obtain ⟨w, hw, hFw⟩ :=
    exists_zero_closedBall_of_uniform_close (hFentire n) hr hm hf0 hflower hclose
  refine ⟨w, ?_, hFw⟩
  exact mem_closedBall.mpr ((mem_closedBall.mp hw).trans hrR.le)

/-- Whole-plane wrapper retained for existing consumers. -/
theorem eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
    {U : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hU : IsOpen U)
    (hz₀U : z₀ ∈ U)
    (hFentire : ∀ n, Differentiable ℂ (F n))
    (hfentire : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hf_nonzero : f ≠ 0)
    (hf0 : f z₀ = 0)
    (hR : 0 < R) :
    ∀ᶠ n in atTop, ∃ w ∈ closedBall z₀ R, F n w = 0 := by
  have hnotlocalzero : ¬ ∀ᶠ z in 𝓝 z₀, f z = 0 := by
    intro hlocal
    have heq : f = (fun _ : ℂ => 0) :=
      (hfentire.differentiableOn.analyticOnNhd isOpen_univ).eq_of_eventuallyEq
        analyticOnNhd_const hlocal
    apply hf_nonzero
    simpa only [Pi.zero_apply] using heq
  exact eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn_local
    hU hz₀U hFentire hfentire.differentiableOn hconv hnotlocalzero hf0 hR

/-- A diagonal choice lemma for root sets.  Fixed-radius eventual existence is
enough to choose one root at every sufficiently large index, with the chosen
roots converging to the prescribed center. -/
theorem exists_tendsto_of_eventually_exists_closedBall
    {P : ℕ → ℂ → Prop} {z₀ : ℂ}
    (hroot : ∀ r : ℝ, 0 < r →
      ∀ᶠ n in atTop, ∃ w ∈ closedBall z₀ r, P n w) :
    ∃ w : ℕ → ℂ, Tendsto w atTop (𝓝 z₀) ∧ ∀ᶠ n in atTop, P n (w n) := by
  have hradius : ∀ k : ℕ, 0 < (1 : ℝ) / (k + 1) := by
    intro k
    positivity
  have hthreshold : ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N,
      ∃ w ∈ closedBall z₀ ((1 : ℝ) / (k + 1)), P n w := by
    intro k
    exact (eventually_atTop.1 (hroot _ (hradius k)))
  choose N hN using hthreshold
  let level : ℕ → ℕ := fun n => Nat.findGreatest (fun k => N k ≤ n) n
  have hlevel_spec : ∀ n, N 0 ≤ n → N (level n) ≤ n := by
    intro n hn
    exact Nat.findGreatest_spec (P := fun k => N k ≤ n) (m := 0)
      (Nat.zero_le n) hn
  have hlevel_tendsto : Tendsto level atTop atTop := by
    refine tendsto_atTop.2 ?_
    intro k
    filter_upwards [eventually_ge_atTop (max k (N k))] with n hn
    apply Nat.le_findGreatest
    · exact (le_max_left _ _).trans hn
    · exact (le_max_right _ _).trans hn
  have hlevel_root : ∀ n, N 0 ≤ n →
      ∃ w ∈ closedBall z₀ ((1 : ℝ) / (level n + 1)), P n w := by
    intro n hn
    exact hN (level n) n (hlevel_spec n hn)
  let w : ℕ → ℂ := fun n => if hn : N 0 ≤ n then
    Classical.choose (hlevel_root n hn) else z₀
  have hw_mem : ∀ n (hn : N 0 ≤ n),
      w n ∈ closedBall z₀ ((1 : ℝ) / (level n + 1)) := by
    intro n hn
    simpa only [w, dif_pos hn] using (Classical.choose_spec (hlevel_root n hn)).1
  have hw_root : ∀ n (hn : N 0 ≤ n), P n (w n) := by
    intro n hn
    simpa only [w, dif_pos hn] using (Classical.choose_spec (hlevel_root n hn)).2
  refine ⟨w, ?_, ?_⟩
  · have hradius_tendsto :
        Tendsto (fun n => (1 : ℝ) / (level n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.comp hlevel_tendsto
    rw [Metric.tendsto_atTop]
    intro ε hε
    have heps := (Metric.tendsto_atTop.1 hradius_tendsto) ε hε
    obtain ⟨M, hM⟩ := heps
    refine ⟨max M (N 0), ?_⟩
    intro n hn
    have hnM : M ≤ n := (le_max_left M (N 0)).trans hn
    have hnN : N 0 ≤ n := (le_max_right M (N 0)).trans hn
    have hnε := hM n hnM
    have hdist : dist (w n) z₀ ≤ (1 : ℝ) / (level n + 1) :=
      mem_closedBall.mp (hw_mem n hnN)
    have hrad_nonneg : 0 ≤ (1 : ℝ) / (level n + 1) := (hradius _).le
    rw [Real.dist_0_eq_abs, abs_of_nonneg hrad_nonneg] at hnε
    exact hdist.trans_lt hnε
  · filter_upwards [eventually_ge_atTop (N 0)] with n hn
    exact hw_root n hn

/-- Generic Hurwitz zero transfer for the Route B interface.  The theorem is
fully quantitative underneath: isolated zeros give a certified boundary
circle, open mapping produces an approximating zero in each fixed disk, and a
diagonal choice produces a single convergent sequence of zeros. -/
theorem zerosApproachOn_of_tendstoLocallyUniformlyOn
    {U S : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U)
    (hSU : S ⊆ U)
    (hFentire : ∀ n, Differentiable ℂ (F n))
    (hfentire : Differentiable ℂ f)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hf_nonzero : f ≠ 0) :
    ZerosApproachOn S F f := by
  intro z₀ hz₀S hf0
  apply exists_tendsto_of_eventually_exists_closedBall
    (P := fun n w => F n w = 0)
  intro R hR
  exact eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
    hU (hSU hz₀S) hFentire hfentire hconv hf_nonzero hf0 hR

/-- Strip-local Hurwitz transfer.  Unlike the whole-plane wrapper, this
version asks only for holomorphy on the open convergence domain.  Nontriviality
is stated in the exact local form consumed by isolated-zero theory. -/
theorem zerosApproachOn_of_tendstoLocallyUniformlyOn_local
    {U S : Set ℂ} {F : ℕ → ℂ → ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U)
    (hSU : S ⊆ U)
    (hFentire : ∀ n, Differentiable ℂ (F n))
    (hfholomorphic : DifferentiableOn ℂ f U)
    (hconv : TendstoLocallyUniformlyOn F f atTop U)
    (hf_not_local_zero :
      ∀ z ∈ S, ¬ ∀ᶠ w in 𝓝 z, f w = 0) :
    ZerosApproachOn S F f := by
  intro z₀ hz₀S hf0
  apply exists_tendsto_of_eventually_exists_closedBall
    (P := fun n w => F n w = 0)
  intro R hR
  exact eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn_local
    hU (hSU hz₀S) hFentire hfholomorphic hconv
      (hf_not_local_zero z₀ hz₀S) hf0 hR

#print axioms exists_zero_closedBall_of_uniform_close
#print axioms exists_tendsto_of_eventually_exists_closedBall
#print axioms eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn_local
#print axioms eventually_exists_zero_closedBall_of_tendstoLocallyUniformlyOn
#print axioms zerosApproachOn_of_tendstoLocallyUniformlyOn
#print axioms zerosApproachOn_of_tendstoLocallyUniformlyOn_local

end Q3.RouteB
