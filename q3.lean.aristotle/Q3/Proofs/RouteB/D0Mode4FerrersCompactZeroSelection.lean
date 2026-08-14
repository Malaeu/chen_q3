import Q3.Proofs.RouteB.D0Mode4FerrersSturmComparison

/-!
# Goal 058 G3: compact zero selection for the mode-four Ferrers source

This file turns the previously proved simplicity of every interior zero into
finite zero sets on compact interior intervals.  It then selects the first
zero to the right of a supplied endpoint and removes the one-nodal-interval
guard from the Sturm-comparison consumer.

The knowledge preflight at `Goal058.G3.CompactZeroSelection` found no existing
project supplier for this step.  The proof uses the Mathlib primitives
`HasDerivAt.eventually_ne` and `IsCompact.finite` and remains entirely inside
the accepted dimensionless Ferrers solution interface.  It does not count
zeros, identify the ordered degree-four PSWF, or construct a source mode.
-/

open Set Filter Topology

namespace Q3.RouteB

private theorem finite_zeros_on_Icc_of_simple
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, f x = 0 → HasDerivAt f (f' x) x)
    (hne : ∀ x ∈ Icc a b, f x = 0 → f' x ≠ 0) :
    ({x : Set.Icc a b | f x = 0} : Set (Set.Icc a b)).Finite := by
  let g : Set.Icc a b → ℝ := fun x => f x
  let Z : Set (Set.Icc a b) := {x | g x = 0}
  have hg : Continuous g := hcont.restrict
  have hZclosed : IsClosed Z := by
    change IsClosed (g ⁻¹' ({0} : Set ℝ))
    exact isClosed_singleton.preimage hg
  have hZcompact : IsCompact Z := hZclosed.isCompact
  have hZdiscrete : IsDiscrete Z := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro x hx
    have hxzero : f (x : ℝ) = 0 := hx
    have hd := hderiv (x : ℝ) x.property hxzero
    have hdnz := hne (x : ℝ) x.property hxzero
    have hlocal : ∀ᶠ y in 𝓝[≠] (x : ℝ), f y ≠ 0 :=
      hd.eventually_ne hdnz
    change {y : ℝ | f y ≠ 0} ∈ 𝓝[≠] (x : ℝ) at hlocal
    rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at hlocal
    rcases hlocal with ⟨V, hVnhds, hVsub⟩
    rcases Metric.mem_nhds_iff.mp hVnhds with ⟨ε, hε, hball⟩
    let U : Set (Set.Icc a b) :=
      Subtype.val ⁻¹' Metric.ball (x : ℝ) ε
    refine ⟨U, Metric.isOpen_ball.preimage continuous_subtype_val, ?_⟩
    ext y
    constructor
    · rintro ⟨hyU, hyZ⟩
      by_cases hyx : (y : ℝ) = (x : ℝ)
      · exact Subtype.ext hyx
      · exfalso
        have hyV : (y : ℝ) ∈ V := hball hyU
        have hycomp : (y : ℝ) ∈ ({(x : ℝ)} : Set ℝ)ᶜ := by
          simpa
        have : f (y : ℝ) ≠ 0 := hVsub ⟨hyV, hycomp⟩
        exact this hyZ
    · intro hyx
      subst y
      exact ⟨by simpa [U] using hε, hx⟩
  change Z.Finite
  exact hZcompact.finite hZdiscrete

private theorem finite_zeros_on_Icc_of_simple_real
    {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Icc a b, f x = 0 → HasDerivAt f (f' x) x)
    (hne : ∀ x ∈ Icc a b, f x = 0 → f' x ≠ 0) :
    {x : ℝ | x ∈ Icc a b ∧ f x = 0}.Finite := by
  let Z : Set (Set.Icc a b) := {x | f x = 0}
  have hZ : Z.Finite := finite_zeros_on_Icc_of_simple hcont hderiv hne
  have hImage : ((fun x : Set.Icc a b => (x : ℝ)) '' Z).Finite :=
    Set.Finite.image (fun x : Set.Icc a b => (x : ℝ)) hZ
  have hImageEq :
      (fun x : Set.Icc a b => (x : ℝ)) '' Z =
        {x : ℝ | x ∈ Icc a b ∧ f x = 0} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, hx.2, rfl⟩
  rw [hImageEq] at hImage
  exact hImage

/-- The zeros of an accepted mode-four Ferrers solution on a compact interval
strictly inside the singular endpoints form a finite set. -/
theorem Mode4FerrersRegularEvenProlateSolution.interior_zeros_on_Icc_finite
    {mProject K : ℕ} {Λ a b : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K Λ)
    (ha : a ∈ Ioo (-1 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    {x : ℝ | x ∈ Icc a b ∧
      mode4FerrersSeries S.coefficients x = 0}.Finite := by
  have hsub : Icc a b ⊆ Icc (-1 : ℝ) 1 := by
    intro x hx
    exact ⟨ha.1.le.trans hx.1, hx.2.trans hb.2.le⟩
  apply finite_zeros_on_Icc_of_simple_real
      (f' := mode4FerrersFirstDerivativeSeries S.coefficients)
      (S.continuousOn_closed.mono hsub)
  · intro x hx hz
    have hxOpen : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
    exact S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hxOpen
  · intro x hx hz
    have hxOpen : x ∈ Ioo (-1 : ℝ) 1 :=
      ⟨ha.1.trans_le hx.1, hx.2.trans_lt hb.2⟩
    have hSimple := S.interior_zero_simple hxOpen hz
    rw [← (S.ferrersSeries_hasDerivAt_firstDerivativeSeries x hxOpen).deriv]
    exact hSimple

private theorem exists_consecutive_zero_right_of_finite
    {f : ℝ → ℝ} {x1 x2 : ℝ}
    (hfinite : {x : ℝ | x ∈ Icc x1 x2 ∧ f x = 0}.Finite)
    (hxx : x1 < x2)
    (hz2 : f x2 = 0) :
    ∃ y ∈ Ioc x1 x2, f y = 0 ∧
      ∀ z ∈ Ioo x1 y, f z ≠ 0 := by
  let t : Finset ℝ := hfinite.toFinset.filter (fun y => x1 < y)
  have hx2t : x2 ∈ t := by
    simp [t, hxx, hxx.le, hz2]
  have ht : t.Nonempty := ⟨x2, hx2t⟩
  let y : ℝ := t.min' ht
  have hyt : y ∈ t := t.min'_mem ht
  have hyData : y ∈ Icc x1 x2 ∧ f y = 0 ∧ x1 < y := by
    simpa [t, y] using hyt
  have hyle : y ≤ x2 := t.min'_le x2 hx2t
  refine ⟨y, ⟨hyData.2.2, hyle⟩, hyData.2.1, ?_⟩
  intro z hz hfz
  have hzt : z ∈ t := by
    simp only [t, Finset.mem_filter, Set.Finite.mem_toFinset]
    exact ⟨⟨⟨hz.1.le, hz.2.le.trans hyle⟩, hfz⟩, hz.1⟩
  have hyz : y ≤ z := t.min'_le z hzt
  exact (not_lt_of_ge hyz) hz.2

/-- The one-nodal-interval hypothesis of the preceding Sturm theorem can be
selected internally: between any two distinct interior zeros of the lower
spectral-parameter solution, the higher solution has an interior zero. -/
theorem exists_mode4Ferrers_zero_between_of_lt_Lambda_between_lower_zeros
    {mProject K : ℕ} {ΛLo ΛHi x1 x2 : ℝ}
    (SLo : Mode4FerrersRegularEvenProlateSolution mProject K ΛLo)
    (SHi : Mode4FerrersRegularEvenProlateSolution mProject K ΛHi)
    (hΛ : ΛLo < ΛHi)
    (hx1 : x1 ∈ Ioo (-1 : ℝ) 1)
    (hx2 : x2 ∈ Ioo (-1 : ℝ) 1)
    (hxx : x1 < x2)
    (hz1 : mode4FerrersSeries SLo.coefficients x1 = 0)
    (hz2 : mode4FerrersSeries SLo.coefficients x2 = 0) :
    ∃ x ∈ Ioo x1 x2,
      mode4FerrersSeries SHi.coefficients x = 0 := by
  have hfinite := SLo.interior_zeros_on_Icc_finite hx1 hx2
  obtain ⟨y, hyRange, hyZero, hyNodal⟩ :=
    exists_consecutive_zero_right_of_finite hfinite hxx hz2
  have hyInterior : y ∈ Ioo (-1 : ℝ) 1 :=
    ⟨hx1.1.trans hyRange.1, hyRange.2.trans_lt hx2.2⟩
  obtain ⟨x, hx, hxZero⟩ :=
    exists_mode4Ferrers_zero_between_of_lt_Lambda_on_nodal_interval
      SLo SHi hΛ hx1 hyInterior hyRange.1 hz1 hyZero hyNodal
  exact ⟨x, ⟨hx.1, hx.2.trans_le hyRange.2⟩, hxZero⟩

#print axioms Mode4FerrersRegularEvenProlateSolution.interior_zeros_on_Icc_finite
#print axioms exists_mode4Ferrers_zero_between_of_lt_Lambda_between_lower_zeros

end Q3.RouteB
