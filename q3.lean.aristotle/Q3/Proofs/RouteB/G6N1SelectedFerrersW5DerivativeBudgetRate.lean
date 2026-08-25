import Q3.Proofs.RouteB.G6N1SelectedFerrersW5EndpointValueRate

/-!
# W5 — towards the eventual bound of the log-derivative budget

Target of the derivative-node verdict: `∃ D ≥ 0`, eventually
`selectedFerrersAbelLogDerivativeBudget k ≤ D`, with no new `C¹` premise.

This file starts with the exact additive derivative decomposition the verdict
puts first: at every seam-free interior point,

`d/dx rep = (1/2) · rep + √u · Σ_{n active} Q_k(n·u)`,

where `Q_k(y) = y · pkt'(y)` and `u = exp x / lam`.  The weighted-derivative
comb `Q_k` is kept signed; the endpoint defect of its mass is *not* erased —
that is the critical repair the verdict demands.

SEARCH_FLAGS:
  - `./ask.sh "derivative budget log representative interval integrable bound"`
  - `./ask.sh "packet variation bounded window"`

LEDGER:
  CLOSES: []
  OPENS: []
-/

open Filter MeasureTheory Set
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

/-! ## Local reconstruction: differentiability of the packet off the edge -/

private theorem w5d_packet_differentiableAt_of_mem_open
    (k : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    DifferentiableAt ℝ (selectedFerrersLemma73SourcePacket k) y := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have hm : 2 ≤ k + 2 := by omega
  have hyOpen : y ∈ Set.Ioo (-(Real.sqrt (((k + 2 : ℕ) : ℝ))))
      (Real.sqrt (((k + 2 : ℕ) : ℝ))) := by
    rwa [hlam] at hy
  have hh0d : DifferentiableAt ℝ (selectedFerrersPreAnchorPair k).h0 y := by
    rw [hh0]
    exact (normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution0 k) hm hyOpen).differentiableAt
  have hh4d : DifferentiableAt ℝ (selectedFerrersPreAnchorPair k).h4 y := by
    rw [hh4]
    exact (normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution4 k) hm hyOpen).differentiableAt
  have hcomb : DifferentiableAt ℝ
      (prolateCombination (selectedFerrersPreAnchorPair k)) y := by
    unfold prolateCombination
    exact ((hh0d.const_mul _).sub (hh4d.const_mul _)).div_const _
  unfold selectedFerrersLemma73SourcePacket
  exact hcomb.const_mul _

private theorem w5d_packet_zero_outside (k : ℕ) (y : ℝ)
    (hy : y ∉ Set.Icc (-(selectedFerrersPreAnchorPair k).pw.lambda)
      (selectedFerrersPreAnchorPair k).pw.lambda) :
    selectedFerrersLemma73SourcePacket k y = 0 := by
  have h0 : (selectedFerrersPreAnchorPair k).h0 y = 0 := by
    by_contra hne
    exact hy ((selectedFerrersPreAnchorPair k).h0_support hne)
  have h4 : (selectedFerrersPreAnchorPair k).h4 y = 0 := by
    by_contra hne
    exact hy ((selectedFerrersPreAnchorPair k).h4_support hne)
  simp [selectedFerrersLemma73SourcePacket, prolateCombination, h0, h4]

private theorem w5d_packet_differentiableAt_of_gt
    (k : ℕ) {y : ℝ}
    (hy : (selectedFerrersPreAnchorPair k).pw.lambda < y) :
    DifferentiableAt ℝ (selectedFerrersLemma73SourcePacket k) y := by
  have heq : selectedFerrersLemma73SourcePacket k =ᶠ[nhds y]
      (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact w5d_packet_zero_outside k z
      (fun hmem => absurd hmem.2 (not_le.mpr hz))
  exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq heq

/-- Off the single positive seam `y = lambda` the packet is differentiable at
every positive argument. -/
private theorem w5d_packet_differentiableAt_of_pos_ne
    (k : ℕ) {y : ℝ} (hpos : 0 < y)
    (hne : y ≠ (selectedFerrersPreAnchorPair k).pw.lambda) :
    DifferentiableAt ℝ (selectedFerrersLemma73SourcePacket k) y := by
  have hlam : 0 < (selectedFerrersPreAnchorPair k).pw.lambda := by
    rw [selectedFerrersPreAnchorPair_lambda_eq k]
    rw [lambda_m]
    apply Real.sqrt_pos.mpr
    have : (0 : ℕ) < (selectedFerrersPreAnchorIndex k).m := by
      have : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
      omega
    exact_mod_cast this
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact w5d_packet_differentiableAt_of_mem_open k ⟨by linarith, hlt⟩
  · exact w5d_packet_differentiableAt_of_gt k hgt

/-! ## The finite representation on the window -/

private theorem w5d_packet_windowFiniteSupport (k : ℕ) :
    WindowFiniteSupport
      (lambda_m (selectedFerrersPreAnchorIndex k))
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k) := by
  have hbase := prolateCombination_windowFiniteSupport
    (selectedFerrersPreAnchorIndex k) (selectedFerrersPreAnchorPair k)
    (selectedFerrersPreAnchorPair_lambda_eq k)
  intro u hu n hn
  rw [selectedFerrersLemma73SourcePacket,
    hbase u hu n hn, mul_zero]

private theorem w5d_logCoordinate_mem_window
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k) ∈
      I_m (selectedFerrersPreAnchorIndex k) := by
  have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
    rw [lambda_m]
    apply Real.sqrt_pos.mpr
    have : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
    rw [this]
    positivity
  have hsq : lambda_m (selectedFerrersPreAnchorIndex k) *
      lambda_m (selectedFerrersPreAnchorIndex k) =
      (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) := by
    rw [lambda_m, Real.mul_self_sqrt]
    have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
    rw [h1]
    positivity
  constructor
  · -- lower edge
    rw [le_div_iff₀ hlam, inv_mul_cancel₀ (ne_of_gt hlam)]
    exact Real.one_le_exp_iff.mpr hx.1
  · -- upper edge
    rw [div_le_iff₀ hlam]
    have hexp : Real.exp x ≤
        (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) := by
      calc
        Real.exp x ≤
            Real.exp (L_m (selectedFerrersPreAnchorIndex k)) :=
          Real.exp_le_exp.mpr hx.2
        _ = (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) := by
          have hmpos : (0 : ℝ) <
              (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) := by
            have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
            rw [h1]
            positivity
          rw [show L_m (selectedFerrersPreAnchorIndex k) =
            Real.log (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) from rfl,
            Real.exp_log hmpos]
    calc
      Real.exp x ≤ (((selectedFerrersPreAnchorIndex k).m : ℕ) : ℝ) := hexp
      _ = lambda_m (selectedFerrersPreAnchorIndex k) *
            lambda_m (selectedFerrersPreAnchorIndex k) := hsq.symm

/-- On the closed additive window the representative is the finite comb plus
the center shadow. -/
private theorem w5d_rep_eq_finite
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    selectedFerrersAbelLogRepresentative k x =
      finiteEStar
          (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (selectedFerrersLemma73SourcePacket k)
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (Real.sqrt
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) := by
  rw [selectedFerrersAbelLogRepresentative, selectedFerrersAbelLimit,
    E_star_eq_finiteEStar_of_windowFiniteSupport
      (w5d_packet_windowFiniteSupport k)
      (w5d_logCoordinate_mem_window k hx)]

#print axioms w5d_packet_differentiableAt_of_pos_ne
#print axioms w5d_rep_eq_finite

/-! ## The exact additive derivative decomposition -/

/-- The weighted-derivative packet `Q_k(y) = y * pkt'(y)`.  Its comb is the
exact derivative content of the representative; it is kept signed. -/
private noncomputable def w5d_Q (k : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) * deriv (selectedFerrersLemma73SourcePacket k) y

/-- At every seam-free interior point the representative has the exact
derivative `(1/2) * rep + sqrt u * Σ_{active} Q(n u)`.  This is the additive
decomposition the derivative verdict puts first; nothing is taken in norm and
nothing about the mass of `Q` is asserted. -/
private theorem w5d_hasDerivAt_of_no_seam
    (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioo 0 (L_m (selectedFerrersPreAnchorIndex k)))
    (hseam : ∀ n : ℕ+,
      ((n : ℕ) : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠
        lambda_m (selectedFerrersPreAnchorIndex k)) :
    HasDerivAt (selectedFerrersAbelLogRepresentative k)
      ((1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
        (Real.sqrt
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
          ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            w5d_Q k (((n : ℕ) : ℝ) *
              (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))) x := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam0 : (0 : ℝ) < lam := by
    rw [hlamdef, lambda_m]
    apply Real.sqrt_pos.mpr
    have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
    rw [h1]
    positivity
  set u : ℝ → ℝ := fun z => Real.exp z / lam with hudef
  have hu0 : ∀ z, 0 < u z := fun z => by
    rw [hudef]
    positivity
  have hcoordDeriv : ∀ z : ℝ, HasDerivAt u (u z) z := by
    intro z
    rw [hudef]
    simpa using (Real.hasDerivAt_exp z).div_const lam
  -- derivative of the sqrt weight, as a complex-valued map
  have hsqrtDeriv : ∀ z : ℝ,
      HasDerivAt (fun w : ℝ => ((Real.sqrt (u w) : ℝ) : ℂ))
        (((1 / 2 * Real.sqrt (u z) : ℝ) : ℂ)) z := by
    intro z
    have hreal : HasDerivAt (fun w : ℝ => Real.sqrt (u w))
        (1 / (2 * Real.sqrt (u z)) * u z) z := by
      have h := (Real.hasDerivAt_sqrt (ne_of_gt (hu0 z))).comp z (hcoordDeriv z)
      exact h
    have hval : 1 / (2 * Real.sqrt (u z)) * u z = 1 / 2 * Real.sqrt (u z) := by
      have hss : Real.sqrt (u z) * Real.sqrt (u z) = u z :=
        Real.mul_self_sqrt (hu0 z).le
      have hs0 : (0 : ℝ) < Real.sqrt (u z) := Real.sqrt_pos.mpr (hu0 z)
      field_simp
      linarith [hss]
    rw [hval] at hreal
    exact hreal.ofReal_comp
  -- derivative of each comb term
  have htermDeriv : ∀ n ∈ sourcePositiveIndexFinset
      (selectedFerrersPreAnchorIndex k),
      HasDerivAt (fun w : ℝ =>
        selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u w))
        (w5d_Q k (((n : ℕ) : ℝ) * u x)) x := by
    intro n _
    have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hargPos : 0 < ((n : ℕ) : ℝ) * u x := mul_pos hnpos (hu0 x)
    have hargNe : ((n : ℕ) : ℝ) * u x ≠
        (selectedFerrersPreAnchorPair k).pw.lambda := by
      rw [selectedFerrersPreAnchorPair_lambda_eq k, ← hlamdef]
      exact hseam n
    have hpkt := (w5d_packet_differentiableAt_of_pos_ne k hargPos
      hargNe).hasDerivAt
    have hinner : HasDerivAt (fun w : ℝ => ((n : ℕ) : ℝ) * u w)
        (((n : ℕ) : ℝ) * u x) x := (hcoordDeriv x).const_mul _
    have hcomp := hpkt.scomp x hinner
    have hval : (((n : ℕ) : ℝ) * u x) •
        deriv (selectedFerrersLemma73SourcePacket k) (((n : ℕ) : ℝ) * u x) =
        w5d_Q k (((n : ℕ) : ℝ) * u x) := by
      rw [w5d_Q, Complex.real_smul]
    rw [hval] at hcomp
    exact hcomp
  -- derivative of the finite comb
  have hcombDeriv : HasDerivAt (fun w : ℝ =>
      ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u w))
      (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        w5d_Q k (((n : ℕ) : ℝ) * u x)) x :=
    HasDerivAt.fun_sum htermDeriv
  -- product with the sqrt weight, plus the shadow
  have hfinite : HasDerivAt (fun w : ℝ =>
      ((Real.sqrt (u w) : ℝ) : ℂ) *
        ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
          selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u w) +
      (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        ((Real.sqrt (u w) : ℝ) : ℂ))
      ((((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ)) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u x)) +
        ((Real.sqrt (u x) : ℝ) : ℂ) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            w5d_Q k (((n : ℕ) : ℝ) * u x)) +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ))) x := by
    exact ((hsqrtDeriv x).mul hcombDeriv).add
      (((hsqrtDeriv x).const_mul
        ((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0)))
  -- the representative agrees with the finite form on a neighbourhood
  have hrepEq : selectedFerrersAbelLogRepresentative k =ᶠ[nhds x]
      (fun w : ℝ =>
        ((Real.sqrt (u w) : ℝ) : ℂ) *
          ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u w) +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          ((Real.sqrt (u w) : ℝ) : ℂ)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hx] with w hw
    rw [w5d_rep_eq_finite k ⟨hw.1.le, hw.2.le⟩, finiteEStar, finiteEStarCore]
  have hgoal := hfinite.congr_of_eventuallyEq hrepEq
  -- identify the derivative value with the stated decomposition
  have hvalue :
      ((((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ)) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u x)) +
        ((Real.sqrt (u x) : ℝ) : ℂ) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            w5d_Q k (((n : ℕ) : ℝ) * u x)) +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ))) =
      ((1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
        ((Real.sqrt (u x) : ℝ) : ℂ) *
          ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            w5d_Q k (((n : ℕ) : ℝ) * u x)) := by
    rw [w5d_rep_eq_finite k ⟨hx.1.le, hx.2.le⟩, finiteEStar, finiteEStarCore]
    push_cast
    ring
  rw [hvalue] at hgoal
  exact hgoal

#print axioms w5d_hasDerivAt_of_no_seam

/-! ## The authorized reduction

`DerivativeBudget ≤ (1/2)·L1 + ∫ √u·‖Q-comb‖`.  The derivative equals the D2
decomposition off the finite seam set, hence almost everywhere; the budget
integrand is dominated pointwise a.e. and the comparison integral carries the
rest.  Nothing here bounds the `Q`-comb: that is the exact open supplier
`W5_LOG_DERIVATIVE_BUDGET_BOUNDED` of the conditional-closure verdict. -/

/-- The finite additive seam set: images of the multiplicative seams. -/
private def w5d_seamSet (k : ℕ) : Set ℝ :=
  ⋃ n ∈ ((sourcePositiveIndexFinset
      (selectedFerrersPreAnchorIndex k) : Finset ℕ+) : Set ℕ+),
    {x : ℝ | ((n : ℕ) : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) =
      lambda_m (selectedFerrersPreAnchorIndex k)}

private theorem w5d_seamSet_measure_zero (k : ℕ) :
    MeasureTheory.volume (w5d_seamSet k) = 0 := by
  have hfin : (w5d_seamSet k).Finite := by
    rw [w5d_seamSet]
    apply Set.Finite.biUnion (Finset.finite_toSet _)
    intro n _
    have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
      rw [lambda_m]
      apply Real.sqrt_pos.mpr
      have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
      rw [h1]
      positivity
    have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    apply Set.Finite.subset
      (Set.finite_singleton
        (Real.log (lambda_m (selectedFerrersPreAnchorIndex k) *
          lambda_m (selectedFerrersPreAnchorIndex k) / ((n : ℕ) : ℝ))))
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    simp only [Set.mem_singleton_iff]
    have hexp : Real.exp x = lambda_m (selectedFerrersPreAnchorIndex k) *
        lambda_m (selectedFerrersPreAnchorIndex k) / ((n : ℕ) : ℝ) := by
      field_simp at hx ⊢
      nlinarith [hx]
    rw [← hexp, Real.log_exp]
  exact hfin.measure_zero _

/-- The authorized reduction: the derivative budget is at most half the `L¹`
window mass plus the weighted `Q`-comb integral.  Almost everywhere off the
finite seam set the derivative is the D2 decomposition; the triangle
inequality and a.e. interval-integral monotonicity carry the rest.  Nothing
here bounds the `Q`-comb: that is the open supplier
`W5_LOG_DERIVATIVE_BUDGET_BOUNDED`. -/
private theorem w5d_budget_reduction (k : ℕ)
    (hint : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
        Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
          ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            w5d_Q k (((n : ℕ) : ℝ) *
              (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)))
    (hbudget : IntervalIntegrable
      (fun x : ℝ => ‖deriv (selectedFerrersAbelLogRepresentative k) x‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k))) :
    selectedFerrersAbelLogDerivativeBudget k ≤
      ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        ((1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
          Real.sqrt
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
              w5d_Q k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))‖) := by
  have hL0 : (0 : ℝ) ≤ L_m (selectedFerrersPreAnchorIndex k) :=
    (logLength_pos (selectedFerrersPreAnchorIndex k)).le
  rw [selectedFerrersAbelLogDerivativeBudget]
  apply intervalIntegral.integral_mono_ae_restrict hL0 hbudget hint
  -- pointwise a.e. bound off the seam set
  have hnull : MeasureTheory.volume (w5d_seamSet k) = 0 :=
    w5d_seamSet_measure_zero k
  have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))),
      x ∉ w5d_seamSet k :=
    MeasureTheory.ae_restrict_of_ae
      ((MeasureTheory.ae_iff).mpr (by simpa using hnull))
  have hbd : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))),
      x ∉ ({0, L_m (selectedFerrersPreAnchorIndex k)} : Set ℝ) := by
    apply MeasureTheory.ae_restrict_of_ae
    have hfin : ({0, L_m (selectedFerrersPreAnchorIndex k)} : Set ℝ).Finite :=
      (Set.finite_singleton _).insert _
    exact MeasureTheory.measure_zero_iff_ae_notMem.mp
      (hfin.measure_zero (μ := MeasureTheory.volume))
  filter_upwards [hae,
    MeasureTheory.ae_restrict_mem measurableSet_Icc, hbd]
    with x hxseam hxmem hxbd
  have hxint : x ∈ Set.Ioo (0 : ℝ)
      (L_m (selectedFerrersPreAnchorIndex k)) := by
    rcases lt_or_eq_of_le hxmem.1 with h0 | h0
    · rcases lt_or_eq_of_le hxmem.2 with hL | hL
      · exact ⟨h0, hL⟩
      · exact absurd (by simp [hL] : x ∈ ({0,
          L_m (selectedFerrersPreAnchorIndex k)} : Set ℝ)) hxbd
    · exact absurd (by simp [← h0] : x ∈ ({0,
        L_m (selectedFerrersPreAnchorIndex k)} : Set ℝ)) hxbd
  · -- interior seam-free point: the D2 decomposition is the derivative
    have hseam : ∀ n : ℕ+,
        ((n : ℕ) : ℝ) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠
          lambda_m (selectedFerrersPreAnchorIndex k) := by
      intro n hcontra
      apply hxseam
      rw [w5d_seamSet]
      by_cases hn : n ∈ sourcePositiveIndexFinset
          (selectedFerrersPreAnchorIndex k)
      · exact Set.mem_biUnion hn hcontra
      · -- an index outside the finset means n > k + 2, and then the seam
        -- equation contradicts u > 1 / lambda on the open window.
        exfalso
        have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
          rw [lambda_m]
          apply Real.sqrt_pos.mpr
          have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
          rw [h1]
          positivity
        have hsq : lambda_m (selectedFerrersPreAnchorIndex k) *
            lambda_m (selectedFerrersPreAnchorIndex k) =
            ((k + 2 : ℕ) : ℝ) := by
          have h1 : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
          rw [lambda_m, h1, Real.mul_self_sqrt (by positivity)]
        have hbig : (k + 2 : ℕ) < (n : ℕ) := by
          rw [sourcePositiveIndexFinset, Finset.mem_Icc] at hn
          push_neg at hn
          have hle := hn n.one_le
          exact_mod_cast hle
        have hu_gt : (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ <
            Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k) := by
          rw [div_eq_mul_inv]
          have hex : (1 : ℝ) < Real.exp x := by
            rw [show (1 : ℝ) = Real.exp 0 from (Real.exp_zero).symm]
            exact Real.exp_lt_exp.mpr hxint.1
          nlinarith [hex, inv_pos.mpr hlam]
        have hbigR : ((k + 2 : ℕ) : ℝ) < ((n : ℕ) : ℝ) := by
          exact_mod_cast hbig
        -- lambda = n*u > n/lambda > (k+2)/lambda = lambda: contradiction.
        have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
        have h1 := mul_lt_mul_of_pos_left hu_gt hnpos
        rw [hcontra] at h1
        have h2 := mul_lt_mul_of_pos_right hbigR (inv_pos.mpr hlam)
        have hinv : lambda_m (selectedFerrersPreAnchorIndex k) *
            (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ = 1 :=
          mul_inv_cancel₀ (ne_of_gt hlam)
        nlinarith [h1, h2, hsq, hinv, hlam, inv_pos.mpr hlam]
    have hd := w5d_hasDerivAt_of_no_seam k hxint hseam
    rw [hd.deriv]
    calc
      ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
          (Real.sqrt (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
            ∑ n ∈ sourcePositiveIndexFinset
              (selectedFerrersPreAnchorIndex k),
              w5d_Q k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))‖ ≤
          ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x‖ +
            ‖(Real.sqrt (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
              ∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
                w5d_Q k (((n : ℕ) : ℝ) *
                  (Real.exp x /
                    lambda_m (selectedFerrersPreAnchorIndex k)))‖ :=
        norm_add_le _ _
      _ = (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
            Real.sqrt (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) *
              ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
                w5d_Q k (((n : ℕ) : ℝ) *
                  (Real.exp x /
                    lambda_m (selectedFerrersPreAnchorIndex k)))‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Real.sqrt_nonneg _),
          show ‖(1 / 2 : ℂ)‖ = 1 / 2 by
            rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
              Complex.norm_real]
            norm_num]

/-! ## The conditional W5 closure

Everything proved so far assembles into: the full Fourier budget `C_k` is
eventually bounded, conditional on the F72.6 inputs and on the one open
supplier `W5_LOG_DERIVATIVE_BUDGET_BOUNDED`, carried here as the hypothesis
`hD`.  This is exactly consumer strength: `BOUNDED_CK_SUFFICES`. -/

theorem selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates
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
            Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hD : ∃ D : ℝ, 0 ≤ D ∧
      ∀ᶠ k in Filter.atTop,
        selectedFerrersAbelLogDerivativeBudget k ≤ D) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ᶠ k in Filter.atTop,
        selectedFerrersAbelFourierDecayBudget k ≤ Cb := by
  obtain ⟨AL1, BL1, hAL1, hBL1, hL1⟩ :=
    selectedFerrersAbelLogZeroExtension_l1_rate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨AE, hAE, hends⟩ :=
    selectedFerrersAbelLogEndpointValues_rate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  obtain ⟨CS, hCS, hrate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hseam := selectedFerrersAbelLogInternalSeamSum_rate_of_modeAndChiRates
    hCS hrate
  obtain ⟨D, hD0, hDbound⟩ := hD
  have hpi := Real.pi_pos
  refine ⟨2 * ((BL1 + AL1) +
      (D + (2 * AE + 2 * (CS + 132))) / (2 * Real.pi)),
    by positivity, ?_⟩
  filter_upwards [hL1, hends, hseam, hDbound] with k hL1k hendsk hseamk hDk
  have hs1 : (1 : ℝ) ≤ Real.sqrt (selectedFerrersPaperLambda k) := by
    apply Real.one_le_sqrt.mpr
    rw [selectedFerrersPaperLambda]
    have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
      exact_mod_cast this
    simpa using Real.one_le_sqrt.mpr h1
  have hs0 : (0 : ℝ) < Real.sqrt (selectedFerrersPaperLambda k) :=
    lt_of_lt_of_le one_pos hs1
  -- each 1/sqrt(lambda) correction is at most its own constant
  have hdrop : ∀ {c : ℝ}, 0 ≤ c →
      c / Real.sqrt (selectedFerrersPaperLambda k) ≤ c := fun {c} hc =>
    div_le_self hc hs1
  have hlameq : lambda_m (selectedFerrersPreAnchorIndex k) =
      selectedFerrersPaperLambda k :=
    selectedFerrersPaperLambda_eq_lambda_m k
  -- bound the jump budget
  have hjump : selectedFerrersAbelLogJumpBudget k ≤
      2 * AE + 2 * (CS + 132) := by
    rw [selectedFerrersAbelLogJumpBudget]
    have h0 := hendsk.1
    have hL := hendsk.2
    have hseam' := hseamk
    rw [hlameq]
    calc
      ‖selectedFerrersAbelLogRepresentative k 0‖ +
          ‖selectedFerrersAbelLogRepresentative k
            (L_m (selectedFerrersPreAnchorIndex k))‖ +
          ∑ n ∈ Finset.Icc 2 (k + 2),
            ‖((Real.sqrt
                (selectedFerrersPaperLambda k / (n : ℝ)) : ℝ) : ℂ) *
              selectedFerrersLemma73SourcePacket k
                (selectedFerrersPaperLambda k)‖ ≤
          AE / Real.sqrt (selectedFerrersPaperLambda k) +
            AE / Real.sqrt (selectedFerrersPaperLambda k) +
            2 * (CS + 132) / Real.sqrt (selectedFerrersPaperLambda k) :=
        add_le_add (add_le_add h0 hL) hseam'
      _ ≤ AE + AE + 2 * (CS + 132) := by
        have h1 := hdrop hAE
        have h2 := hdrop (by linarith : (0:ℝ) ≤ 2 * (CS + 132))
        linarith
      _ = 2 * AE + 2 * (CS + 132) := by ring
  -- bound the L1 mass
  have hmass : (∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖) ≤
      BL1 + AL1 := by
    refine le_trans hL1k ?_
    have := hdrop hAL1
    linarith
  -- assemble
  rw [selectedFerrersAbelFourierDecayBudget]
  have hsum : selectedFerrersAbelLogDerivativeBudget k +
      selectedFerrersAbelLogJumpBudget k ≤
      D + (2 * AE + 2 * (CS + 132)) := add_le_add hDk hjump
  have hdiv : (selectedFerrersAbelLogDerivativeBudget k +
      selectedFerrersAbelLogJumpBudget k) / (2 * Real.pi) ≤
      (D + (2 * AE + 2 * (CS + 132))) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right hsum
    positivity
  nlinarith [hmass, hdiv]

#print axioms selectedFerrersAbelFourierDecayBudget_bounded_of_modeAndChiRates

end Q3.RouteB.D0Pstar
