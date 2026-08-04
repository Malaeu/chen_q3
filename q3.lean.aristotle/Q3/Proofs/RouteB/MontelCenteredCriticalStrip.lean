import Q3.Proofs.RouteB.D0CriticalStripCompactBound
import Q3.Proofs.RouteB.MontelNormalFamilies

open Filter Function Set Topology Uniformity UniformConvergence
open scoped NNReal

set_option autoImplicit false
set_option linter.mathlibStandardSet false

noncomputable section

namespace Q3.RouteB

open CanonicalRHRoute

/-- The open centered critical strip is preconnected. -/
theorem isPreconnected_centeredCriticalStrip :
    IsPreconnected centeredCriticalStrip := by
  have hset : centeredCriticalStrip =
      Complex.imCLM ⁻¹' Set.Ioo (-(1 / 2)) (1 / 2) := by
    ext z
    simp [centeredCriticalStrip, abs_lt, Complex.imCLM_apply]
  rw [hset]
  exact ((convex_Ioo (-(1 / 2 : ℝ)) (1 / 2)).linear_preimage
    Complex.imCLM.toLinearMap).isPreconnected

private abbrev CenteredStripPoint :=
  {z : ℂ // z ∈ centeredCriticalStrip}

/-- Cauchy's estimate gives a common derivative bound on a smaller ambient
ball around every point of the open strip. -/
private lemma centeredStrip_locallyBounded_eventually_deriv_bound
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) centeredCriticalStrip)
    (hbdd :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (x : CenteredStripPoint) :
    ∃ r : ℝ, 0 < r ∧
      Metric.ball (x : ℂ) r ⊆ centeredCriticalStrip ∧
      ∃ C : ℝ≥0, ∀ n, ∀ y ∈ Metric.ball (x : ℂ) r,
        ‖deriv (f n) y‖₊ ≤ C := by
  obtain ⟨ε, hε, hεsub⟩ :=
    Metric.isOpen_iff.mp isOpen_centeredCriticalStrip x x.property
  let r : ℝ := ε / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hhalf : ε / 2 < ε := by linarith
  have hKsub : Metric.closedBall (x : ℂ) (ε / 2) ⊆ centeredCriticalStrip :=
    (Metric.closedBall_subset_ball hhalf).trans hεsub
  obtain ⟨M, hM⟩ :=
    hbdd (Metric.closedBall (x : ℂ) (ε / 2))
      (isCompact_closedBall _ _) hKsub
  have hM' :
      ∀ n, ∀ z ∈ Metric.closedBall (x : ℂ) (ε / 2),
        ‖f n z‖ ≤ max M 1 :=
    fun n z hz => (hM n z hz).trans (le_max_left _ _)
  let C : ℝ≥0 :=
    ⟨max M 1 / r, div_nonneg (le_trans (by norm_num) (le_max_right M 1)) hr.le⟩
  have hrε : r < ε := by dsimp [r]; linarith
  refine ⟨r, hr, (Metric.ball_subset_ball hrε.le).trans hεsub, C, ?_⟩
  intro n y hy
  have hyx : dist y (x : ℂ) < r := by simpa [Metric.mem_ball] using hy
  have hclosed : Metric.closedBall y r ⊆ Metric.closedBall (x : ℂ) (ε / 2) := by
    intro z hz
    rw [Metric.mem_closedBall] at hz ⊢
    calc
      dist z (x : ℂ) ≤ dist z y + dist y (x : ℂ) := dist_triangle _ _ _
      _ ≤ r + r := add_le_add hz hyx.le
      _ = ε / 2 := by dsimp [r]; ring
  have hdiff : DiffContOnCl ℂ (f n) (Metric.ball y r) := by
    refine DifferentiableOn.diffContOnCl ?_
    rw [closure_ball y hr.ne']
    exact (hf n).mono (hclosed.trans hKsub)
  have hcauchy : ‖deriv (f n) y‖ ≤ max M 1 / r := by
    exact Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr hdiff
      (fun z hz => hM' n z (hclosed (Metric.sphere_subset_closedBall hz)))
  exact hcauchy

/-- The restrictions of a compact-locally bounded holomorphic family to the
open centered strip form an equicontinuous family. -/
private lemma centeredStrip_locallyBounded_equicontinuous
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) centeredCriticalStrip)
    (hbdd :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    Equicontinuous (fun n (z : CenteredStripPoint) => f n z) := by
  unfold Equicontinuous
  intro x
  rw [Metric.equicontinuousAt_iff]
  obtain ⟨r, hr, hrsub, C, hC⟩ :=
    centeredStrip_locallyBounded_eventually_deriv_bound f hf hbdd x
  intro ε hε
  refine ⟨min r (ε / (C + 1)), by positivity, ?_⟩
  intro y hy n
  have hy_ball : (y : ℂ) ∈ Metric.ball (x : ℂ) r := by
    rw [Metric.mem_ball]
    exact hy.trans_le (min_le_left _ _)
  have hx_ball : (x : ℂ) ∈ Metric.ball (x : ℂ) r :=
    Metric.mem_ball_self hr
  have hle : ‖f n y - f n x‖ ≤ C * ‖(y : ℂ) - x‖ := by
    exact Convex.norm_image_sub_le_of_norm_deriv_le
      (fun z hz => (hf n z (hrsub hz)).differentiableAt
        (isOpen_centeredCriticalStrip.mem_nhds (hrsub hz)))
      (fun z hz => hC n z hz)
      (convex_ball _ _) hx_ball hy_ball
  rw [dist_comm, dist_eq_norm]
  have hsmall : ‖(y : ℂ) - x‖ < ε / (C + 1) := by
    have hdist : dist (y : ℂ) (x : ℂ) < ε / (C + 1) := by
      simpa using hy.trans_le (min_le_right _ _)
    simpa [dist_eq_norm] using hdist
  have hCpos : (0 : ℝ) < C + 1 := by positivity
  have hmul : (C : ℝ) * ε / (C + 1) < ε := by
    rw [div_lt_iff₀ hCpos]
    nlinarith [C.prop]
  by_cases hCzero : C = 0
  · simp_all
  calc
    ‖f n y - f n x‖ ≤ (C : ℝ) * ‖(y : ℂ) - x‖ := hle
    _ < (C : ℝ) * (ε / (C + 1)) := by
      have hCpos' : (0 : ℝ) < C := by
        exact_mod_cast (lt_of_le_of_ne' (zero_le C) hCzero)
      nlinarith
    _ = (C : ℝ) * ε / (C + 1) := by ring
    _ < ε := hmul

/-- The closure of the restricted family is compact for the compact-open
topology on continuous maps from the strip subtype. -/
private lemma centeredStrip_locallyBounded_isCompact_closure_range
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) centeredCriticalStrip)
    (hbdd :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ, ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    IsCompact (closure (range (fun n : ℕ =>
      ContinuousMap.mk (fun z : CenteredStripPoint => f n z)
        (hf n).continuousOn.restrict))) := by
  let F : C(CenteredStripPoint, ℂ) → CenteredStripPoint → ℂ := fun g => g
  let s : Set C(CenteredStripPoint, ℂ) := range (fun n : ℕ =>
    ContinuousMap.mk (fun z : CenteredStripPoint => f n z)
      (hf n).continuousOn.restrict)
  have hclemb :
      IsClosedEmbedding
        (UniformOnFun.ofFun {K : Set CenteredStripPoint | IsCompact K} ∘ F) := by
    refine ⟨ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isEmbedding, ?_⟩
    change IsClosed (range ContinuousMap.toUniformOnFunIsCompact)
    rw [ContinuousMap.range_toUniformOnFunIsCompact]
    exact UniformOnFun.isClosed_setOf_continuous
      CompactlyCoherentSpace.isCoherentWith
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (𝔖 := {K : Set CenteredStripPoint | IsCompact K}) (F := F) (s := s)
    (fun K hK => hK) hclemb
  · intro K hK
    let u : s → ℕ := fun i => Classical.choose i.2
    have hu : F ∘ ((↑) : s → C(CenteredStripPoint, ℂ)) =
        (fun n (z : CenteredStripPoint) => f n z) ∘ u := by
      funext i z
      have hi := Classical.choose_spec i.2
      exact (congrArg (fun g : C(CenteredStripPoint, ℂ) => g z) hi).symm
    rw [hu]
    exact ((centeredStrip_locallyBounded_equicontinuous f hf hbdd).comp u).equicontinuousOn K
  · intro K hK x hx
    obtain ⟨M, hM⟩ := hbdd ({(x : ℂ)} : Set ℂ) isCompact_singleton
      (by simpa using x.property)
    refine ⟨Metric.closedBall 0 (max M 0), isCompact_closedBall _ _, ?_⟩
    rintro i ⟨n, rfl⟩
    simp only [F, ContinuousMap.coe_mk, Metric.mem_closedBall, dist_zero_right]
    exact (hM n x (mem_singleton _)).trans (le_max_left _ _)

/-- Montel compactness for holomorphic functions that are locally bounded only
on compact subsets of the open centered critical strip. -/
theorem montel_centeredCriticalStrip_exists_subseq_tendstoLocallyUniformlyOn
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) centeredCriticalStrip)
    (hbdd :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ,
            ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
      ∃ L : ℂ → ℂ,
        DifferentiableOn ℂ L centeredCriticalStrip ∧
        TendstoLocallyUniformlyOn
          (fun k => f (e k)) L atTop centeredCriticalStrip := by
  classical
  letI : LocallyCompactSpace CenteredStripPoint :=
    isOpen_centeredCriticalStrip.locallyCompactSpace
  let g : ℕ → C(CenteredStripPoint, ℂ) := fun n =>
    ContinuousMap.mk (fun z : CenteredStripPoint => f n z)
      (hf n).continuousOn.restrict
  have hcompact : IsCompact (closure (range g)) :=
    centeredStrip_locallyBounded_isCompact_closure_range f hf hbdd
  obtain ⟨Ls, _, e, he, hlim⟩ :=
    hcompact.tendsto_subseq (fun n => subset_closure (mem_range_self n))
  have hloc : TendstoLocallyUniformly
      (fun k z => g (e k) z) Ls atTop :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp hlim
  let L : ℂ → ℂ := fun z => if hz : z ∈ centeredCriticalStrip then Ls ⟨z, hz⟩ else 0
  have hconv : TendstoLocallyUniformlyOn
      (fun k => f (e k)) L atTop centeredCriticalStrip := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_centeredCriticalStrip]
    intro K hKsub hK
    let Ks : Set CenteredStripPoint :=
      {z | (z : ℂ) ∈ K}
    have hKs : IsCompact Ks := by
      rw [Subtype.isCompact_iff]
      have himage : ((↑) '' Ks : Set ℂ) = K := by
        ext z
        constructor
        · rintro ⟨w, hw, rfl⟩
          exact hw
        · intro hz
          exact ⟨⟨z, hKsub hz⟩, hz, rfl⟩
      rw [himage]
      exact hK
    have hUK : TendstoUniformlyOn
        (fun k z => g (e k) z) Ls atTop Ks :=
      (tendstoLocallyUniformly_iff_forall_isCompact.mp hloc) Ks hKs
    intro u hu
    filter_upwards [hUK u hu] with k hk
    intro z hz
    let zs : CenteredStripPoint := ⟨z, hKsub hz⟩
    have hzs : zs ∈ Ks := hz
    have hLz : L z = Ls zs := by simp [L, zs, hKsub hz]
    rw [hLz]
    simpa [g, zs] using hk zs hzs
  have hdiff : DifferentiableOn ℂ L centeredCriticalStrip :=
    hconv.differentiableOn
      (Filter.Eventually.of_forall fun k => hf (e k))
      isOpen_centeredCriticalStrip
  exact ⟨e, he, L, hdiff, hconv⟩

/-- A fixed nonzero anchor forces every Montel limit above to be locally
nonzero throughout the preconnected centered critical strip. -/
theorem montel_centeredCriticalStrip_anchor_nonzero_limit
    (f : ℕ → ℂ → ℂ)
    (a c : ℂ)
    (ha : a ∈ centeredCriticalStrip)
    (hf : ∀ n, DifferentiableOn ℂ (f n) centeredCriticalStrip)
    (hbdd :
      ∀ K : Set ℂ, IsCompact K →
        K ⊆ centeredCriticalStrip →
          ∃ M : ℝ,
            ∀ n : ℕ, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hA : ∀ n, f n a = c)
    (hc : c ≠ 0) :
    ∃ e : ℕ → ℕ, StrictMono e ∧
      ∃ L : ℂ → ℂ,
        DifferentiableOn ℂ L centeredCriticalStrip ∧
        TendstoLocallyUniformlyOn
          (fun k => f (e k)) L atTop centeredCriticalStrip ∧
        L a = c ∧
        (∀ z ∈ centeredCriticalStrip,
          ¬ ∀ᶠ w in 𝓝 z, L w = 0) := by
  obtain ⟨e, he, L, hLd, hconv⟩ :=
    montel_centeredCriticalStrip_exists_subseq_tendstoLocallyUniformlyOn f hf hbdd
  have hLa : L a = c := by
    apply tendsto_nhds_unique (hconv.tendsto_at ha)
    simp [hA]
  refine ⟨e, he, L, hLd, hconv, hLa, ?_⟩
  intro z hz hzero
  have hLanalytic : AnalyticOnNhd ℂ L centeredCriticalStrip :=
    hLd.analyticOnNhd isOpen_centeredCriticalStrip
  have hEqOn : Set.EqOn L 0 centeredCriticalStrip :=
    hLanalytic.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_centeredCriticalStrip hz hzero
  exact hc (hLa.symm.trans (hEqOn ha))

#print axioms isPreconnected_centeredCriticalStrip
#print axioms montel_centeredCriticalStrip_exists_subseq_tendstoLocallyUniformlyOn
#print axioms montel_centeredCriticalStrip_anchor_nonzero_limit

end Q3.RouteB
