import Mathlib

set_option linter.mathlibStandardSet false

noncomputable section

open Filter Topology

namespace Q3.RouteB

/-- A uniform evaluation bound on a compact set transfers any vanishing
product `C i * ‖e i‖` to uniform convergence of the evaluated error to zero. -/
theorem tendstoUniformlyOn_zero_of_evaluation_rate
    {ι α E V : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup V]
    {l : Filter ι} (T : ι → V → α → E) (e : ι → V)
    (K : Set α) (C : ι → ℝ)
    (hrate : Tendsto (fun i => C i * ‖e i‖) l (𝓝 0))
    (hbound : ∀ᶠ i in l, ∀ z ∈ K, ‖T i (e i) z‖ ≤ C i * ‖e i‖) :
    TendstoUniformlyOn
      (fun i z => T i (e i) z) (fun _ => 0) l K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ i in l, C i * ‖e i‖ < epsilon :=
    (tendsto_order.1 hrate).2 epsilon hepsilon
  filter_upwards [hsmall, hbound] with i hi hTi
  intro z hz
  simpa [dist_zero_left] using (hTi z hz).trans_lt hi

/-- If every compact subset of an open locally compact domain has a
vanishing norm envelope, then the family tends locally uniformly to zero. -/
theorem tendstoLocallyUniformlyOn_zero_of_compact_envelopes
    {ι α E : Type*} [TopologicalSpace α] [LocallyCompactSpace α]
    [NormedAddCommGroup E] {l : Filter ι}
    (F : ι → α → E) (U : Set α)
    (hU : IsOpen U)
    (henv : ∀ K ⊆ U, IsCompact K →
      ∃ b : ι → ℝ, Tendsto b l (𝓝 0) ∧
        ∀ᶠ i in l, ∀ z ∈ K, ‖F i z‖ ≤ b i) :
    TendstoLocallyUniformlyOn F (fun _ => 0) l U := by
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hU]
  intro K hKU hK
  obtain ⟨b, hb, hbound⟩ := henv K hKU hK
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ i in l, b i < epsilon :=
    (tendsto_order.1 hb).2 epsilon hepsilon
  filter_upwards [hsmall, hbound] with i hi hFi
  intro z hz
  simpa [dist_zero_left] using (hFi z hz).trans_lt hi

/-- A fixed compact bound is not enough: without a vanishing envelope, the
constant-one family does not converge uniformly to zero even on a singleton. -/
theorem fixed_bound_without_vanishing_rate_not_uniform_zero :
    (∀ _n : ℕ, ∀ z ∈ ({()} : Set Unit),
      ‖(1 : ℝ)‖ ≤ (1 : ℝ)) ∧
    ¬ TendstoUniformlyOn
      (fun _ : ℕ => fun _ : Unit => (1 : ℝ))
      (fun _ => (0 : ℝ)) atTop ({()} : Set Unit) := by
  constructor
  · simp
  · intro h
    have hzero : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
      h.tendsto_at (x := ()) (by simp)
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
    norm_num at this

#print axioms tendstoUniformlyOn_zero_of_evaluation_rate
#print axioms tendstoLocallyUniformlyOn_zero_of_compact_envelopes
#print axioms fixed_bound_without_vanishing_rate_not_uniform_zero

end Q3.RouteB
