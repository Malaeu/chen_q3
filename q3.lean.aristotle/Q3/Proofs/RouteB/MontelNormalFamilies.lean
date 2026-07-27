import Mathlib

open Filter Function Set Topology Uniformity UniformConvergence
open scoped NNReal

set_option autoImplicit false

namespace Q3.RouteB

/-- Cauchy's estimate gives a common derivative bound near each point of a
locally bounded family of entire functions. -/
lemma entire_locallyBounded_eventually_deriv_bound
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (x : ℂ) :
    ∃ C : ℝ≥0, ∀ n, ∀ y ∈ Metric.ball x (1 / 2 : ℝ), ‖deriv (f n) y‖₊ ≤ C := by
  -- The closed ball of radius 1 around x is compact
  have hclosed : IsCompact (Metric.closedBall x 1) := isCompact_closedBall x 1
  -- By local boundedness, all f n are bounded on this ball
  obtain ⟨M, hM⟩ := hbdd (Metric.closedBall x 1) hclosed
  -- Use Cauchy's estimate: need a bound on closedBall of radius 1
  -- First find a bound for all f n on closedBall x 1
  have hM' : ∀ n, ∀ z ∈ Metric.closedBall x 1, ‖f n z‖ ≤ max M 1 :=
    fun n z hz => le_trans (hM n z hz) (le_max_left _ _)
  have hM'' : max M 1 ≥ 0 :=
    le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_right _ _)
  use ⟨2 * (max M 1), by positivity⟩
  intro n y hy
  have hdiff : DifferentiableOn ℂ (f n) (Metric.closedBall x 1) :=
    (hf n).differentiableOn
  have hball : y ∈ Metric.ball x (1 / 2) := hy
  have hR : (1 : ℝ) > 0 := by norm_num
  have h1 : ∀ z ∈ Metric.closedBall x 1, ‖f n z‖ ≤ max M 1 := hM' n
  -- Use the Cauchy estimate lemma from InnerProductSpace namespace
  have hcauchy : ∀ z ∈ Metric.ball x (1 / 2), ‖deriv (f n) z‖ ≤ 2 * (max M 1) := by
    intro z hz
    have hdist_lt_half : dist z x < 1 / 2 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hle : dist z x < 1 := by linarith
    calc
      ‖deriv (f n) z‖
          ≤ max M 1 / (1 - dist z x) := by
            refine Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
              (by linarith : 0 < 1 - dist z x) ?_ ?_
            · exact (hf n).diffContOnCl
            · intro z_1 hz1
              have hdist1 : dist z_1 x ≤ 1 := by
                have := dist_triangle z_1 z x
                rw [hz1] at this
                linarith
              exact h1 z_1 hdist1
      _ ≤ max M 1 / (1 - 1 / 2) := by
            rw [div_le_div_iff₀]
            · nlinarith [hM'', hdist_lt_half]
            · linarith [hdist_lt_half]
            · norm_num
      _ = 2 * max M 1 := by ring
  specialize hcauchy y hball
  exact hcauchy

/-- A locally bounded family of entire functions is equicontinuous. This is the
Cauchy-estimate input to Montel's theorem. -/
lemma entire_locallyBounded_equicontinuous
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    Equicontinuous f := by
  have hderiv :
      ∀ x : ℂ, ∃ C : ℝ≥0, ∀ n, ∀ y ∈ Metric.ball x (1 / 2 : ℝ),
        ‖deriv (f n) y‖₊ ≤ C :=
    entire_locallyBounded_eventually_deriv_bound f hf hbdd
  unfold Equicontinuous
  intro x₀
  rw [Metric.equicontinuousAt_iff]
  obtain ⟨C, hC⟩ := hderiv x₀
  intro ε hε
  use min (1 / 2) (ε / (C + 1))
  constructor
  · positivity
  intro x hx n
  have hx_ball : x ∈ Metric.ball x₀ (1 / 2) :=
    lt_of_lt_of_le hx (min_le_left _ _)
  have hle : ‖f n x - f n x₀‖ ≤ C * ‖x - x₀‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun x _ => (hf n).differentiableAt) (fun y hy => hC n y hy)
      (convex_ball _ _) (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1 / 2))
      hx_ball
  rw [dist_comm, dist_eq_norm]
  have h2 : ‖x - x₀‖ < ε / (C + 1) := by
    rw [← dist_eq_norm]
    exact hx.trans_le (min_le_right _ _)
  have hC_pos : (0 : ℝ) < C + 1 := by positivity
  have hmul : (C : ℝ) * ε / (C + 1) < ε := by
    rw [div_lt_iff₀ hC_pos]
    nlinarith [C.prop]
  by_cases hC_eq : C = 0
  · simp_all
  · have hC_pos' : (0 : ℝ) < C := by
      have : (0 : ℝ≥0) < C := lt_of_le_of_ne' (zero_le C) hC_eq
      exact_mod_cast this
    calc
      ‖f n x - f n x₀‖ ≤ ↑C * ‖x - x₀‖ := hle
      _ < ↑C * (ε / (↑C + 1)) := by nlinarith
      _ = ↑C * ε / (↑C + 1) := by ring
      _ < ε := hmul

/-- The closure of a locally bounded family of entire functions is compact in
the compact-open topology on continuous maps. -/
lemma entire_locallyBounded_isCompact_closure_range
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    IsCompact (closure (range (fun n : ℕ =>
      ContinuousMap.mk (f n) (hf n).continuous))) := by
  let F : C(ℂ, ℂ) → ℂ → ℂ := fun g => g
  let s : Set C(ℂ, ℂ) := range (fun n : ℕ =>
    ContinuousMap.mk (f n) (hf n).continuous)
  have hclemb :
      IsClosedEmbedding (UniformOnFun.ofFun {K : Set ℂ | IsCompact K} ∘ F) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (range ContinuousMap.toUniformOnFunIsCompact)
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous
      CompactlyCoherentSpace.isCoherentWith
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {K : Set ℂ | IsCompact K}) (F := F) (s := s)
    (fun K hK => hK) hclemb
  · intro K hK
    let u : s → ℕ := fun i => Classical.choose i.2
    have hu : F ∘ ((↑) : s → C(ℂ, ℂ)) = f ∘ u := by
      funext i x
      have hi := Classical.choose_spec i.2
      exact (congrArg (fun g : C(ℂ, ℂ) => g x) hi).symm
    rw [hu]
    exact ((entire_locallyBounded_equicontinuous f hf hbdd).comp u).equicontinuousOn K
  · intro K hK x hx
    obtain ⟨M, hM⟩ := hbdd K hK
    refine ⟨Metric.closedBall 0 (max M 0), isCompact_closedBall _ _, ?_⟩
    rintro i ⟨n, rfl⟩
    simp only [F, ContinuousMap.coe_mk, Metric.mem_closedBall, dist_zero_right]
    exact (hM n x hx).trans (le_max_left _ _)

/-- Montel's theorem for locally bounded sequences of entire functions. -/
theorem montel_exists_subseq_tendstoLocallyUniformlyOn
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ L : ℂ → ℂ,
      Differentiable ℂ L ∧
      TendstoLocallyUniformlyOn (fun k => f (e k)) L atTop Set.univ := by
  let g : ℕ → C(ℂ, ℂ) := fun n => ContinuousMap.mk (f n) (hf n).continuous
  have hcompact : IsCompact (closure (range g)) :=
    entire_locallyBounded_isCompact_closure_range f hf hbdd
  obtain ⟨L, _, e, he, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hloc : TendstoLocallyUniformly (fun k z => g (e k) z) L atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  have hlocOn :
      TendstoLocallyUniformlyOn (fun k => f (e k)) L atTop Set.univ := by
    simpa [g] using hloc.tendstoLocallyUniformlyOn
  have hdiffOn : DifferentiableOn ℂ L Set.univ :=
    hlocOn.differentiableOn
      (Filter.Eventually.of_forall fun k => (hf (e k)).differentiableOn)
      isOpen_univ
  exact ⟨e, he, L, differentiableOn_univ.mp hdiffOn, hlocOn⟩

/-- An anchored nonzero locally bounded family has a nonzero Montel limit. -/
theorem montel_anchor_nonzero_limit
    (f : ℕ → ℂ → ℂ) (a c : ℂ)
    (hf : ∀ n, Differentiable ℂ (f n))
    (hbdd : ∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hA : ∀ n, f n a = c) (hc : c ≠ 0) :
    ∃ e : ℕ → ℕ, StrictMono e ∧ ∃ L : ℂ → ℂ,
      Differentiable ℂ L ∧
      TendstoLocallyUniformlyOn (fun k => f (e k)) L atTop Set.univ ∧
      L a = c ∧ L ≠ 0 := by
  obtain ⟨e, he, L, hLd, hconv⟩ :=
    montel_exists_subseq_tendstoLocallyUniformlyOn f hf hbdd
  have hLa : L a = c := by
    apply tendsto_nhds_unique (hconv.tendsto_at (Set.mem_univ a))
    simp [hA]
  refine ⟨e, he, L, hLd, hconv, hLa, ?_⟩
  intro hzero
  have hLzero : L a = 0 := by rw [hzero]; rfl
  exact hc (hLa.symm.trans hLzero)

/-- The anchor in `montel_anchor_nonzero_limit` is load-bearing: for the entire,
locally bounded family `z ↦ z / (n + 1)`, every locally uniformly convergent
subsequence selected by a strictly increasing map has zero limit. -/
lemma anchor_is_load_bearing_limit_zero
    (e : ℕ → ℕ) (L : ℂ → ℂ) (he : StrictMono e)
    (hL : TendstoLocallyUniformlyOn
      (fun k (z : ℂ) => z / ((e k + 1 : ℕ) : ℂ)) L atTop Set.univ) :
    L = 0 := by
  funext z
  simp
  rw [Metric.tendstoLocallyUniformlyOn_iff] at hL
  -- First show that L z is the limit of z / (e n + 1)
  have hptwise :
      Filter.Tendsto (fun n => z / ((e n + 1 : ℕ) : ℂ))
        Filter.atTop (nhds (L z)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨t, ht₁, ht₂⟩ := hL ε hε z (by trivial)
    -- z is in t since t is a neighborhood of z
    have hz_in_t : z ∈ t := mem_of_mem_nhdsWithin (by trivial) ht₁
    rw [Filter.eventually_atTop] at ht₂
    obtain ⟨N, hN⟩ := ht₂
    exact ⟨N, fun n hn => by simpa [dist_comm] using hN n hn z hz_in_t⟩
  -- Since e is strictly monotone, e n → ∞, so z / (e n + 1) → 0
  -- Hence L z = 0 by uniqueness of limits
  have hzero :
      Filter.Tendsto (fun n => z / ((e n + 1 : ℕ) : ℂ))
        Filter.atTop (nhds 0) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    -- dist (z / (e n + 1)) 0 = ‖z‖ / (e n + 1)
    -- We need e n + 1 > ‖z‖ / ε
    have he_inf : Filter.Tendsto e Filter.atTop Filter.atTop := he.tendsto_atTop
    -- Need e n + 1 > ‖z‖ / ε, i.e., e n > ‖z‖ / ε
    -- Use Nat.ceil to get a natural number bound
    let k := ⌈‖z‖ / ε⌉₊
    obtain ⟨N, hN⟩ :=
      Filter.eventually_atTop.mp (he_inf.eventually_gt_atTop k)
    use N
    intro n hn
    simp [dist_eq_norm]
    have hnorm : ‖((e n : ℕ) + 1 : ℂ)‖ = (e n : ℝ) + 1 := by
      norm_cast
    rw [hnorm]
    rw [div_lt_iff₀ (by linarith : (e n : ℝ) + 1 > 0)]
    have h := hN n hn
    -- h : k < e n, i.e., ⌈‖z‖ / ε⌉₊ < e n
    -- Since k ≥ ‖z‖ / ε, we have ‖z‖ ≤ k * ε < e n * ε < (e n + 1) * ε
    have hk : (k : ℝ) < (e n : ℝ) := by exact_mod_cast h
    have hzbdd : ‖z‖ ≤ (k : ℝ) * ε := by
      have := Nat.le_ceil (‖z‖ / ε)
      rwa [div_le_iff₀ hε] at this
    nlinarith
  exact tendsto_nhds_unique hptwise hzero

/-- The explicit family `f n z = z / (n + 1)` is entire and locally bounded,
but every locally uniformly convergent subsequence selected by a strictly
increasing map has the identically zero limit. Thus local boundedness alone
cannot imply the nonzero conclusion of `montel_anchor_nonzero_limit`. -/
theorem anchor_is_load_bearing :
    (∀ n : ℕ, Differentiable ℂ (fun z : ℂ => z / ((n + 1 : ℕ) : ℂ))) ∧
    (∀ K : Set ℂ, IsCompact K → ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ K,
      ‖z / ((n + 1 : ℕ) : ℂ)‖ ≤ M) ∧
    ∀ (e : ℕ → ℕ) (L : ℂ → ℂ), StrictMono e →
      TendstoLocallyUniformlyOn
        (fun k (z : ℂ) => z / ((e k + 1 : ℕ) : ℂ)) L atTop Set.univ →
      L = 0 := by
  refine ⟨fun n => by fun_prop, ?_, ?_⟩
  · intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall 0
    refine ⟨r, fun n z hz => ?_⟩
    have hzNorm : ‖z‖ ≤ r := by
      simpa [Metric.mem_closedBall, dist_zero_right] using hr hz
    calc
      ‖z / ((n + 1 : ℕ) : ℂ)‖ = ‖z‖ / (n + 1 : ℝ) := by
        rw [norm_div]
        congr 1
        norm_cast
      _ ≤ ‖z‖ := div_le_self (norm_nonneg z)
        (by exact_mod_cast Nat.succ_pos n)
      _ ≤ r := hzNorm
  · intro e L he hL
    exact anchor_is_load_bearing_limit_zero e L he hL

#print axioms montel_exists_subseq_tendstoLocallyUniformlyOn
#print axioms montel_anchor_nonzero_limit
#print axioms anchor_is_load_bearing

end Q3.RouteB
