import Q3.Proofs.RouteB.G6N1SelectedFerrersFirstOrderBudgetApplication
import Q3.Proofs.RouteB.G6N1SelectedFerrersEdgeTopFluxConsumer
import Q3.Proofs.RouteB.G6N1SelectedFerrersScaleBandwidthClosure
import Q3.Proofs.RouteB.G6N1CylinderTransportL1Budget
import Q3.Proofs.RouteB.G6N1SturmWeightedConsumerNonTopRate
import Q3.Proofs.RouteB.D0PstarFirstOrderProjectionTailReceiver

set_option linter.mathlibStandardSet false
set_option maxHeartbeats 2000000

open Filter MeasureTheory Set intervalIntegral
open scoped Topology

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# W5 rate assembly (verdict 66362fe1, REQ-2026-08-26-F)

The final route-level assembly: the four kernel-green W5 components — the
explicit `H` comb, the non-top `√log` consumer, the W4 seam ledger, and
the strict-top flux consumer — feed the growing first-order coefficient
envelope, and the rate-aware receiver turns it into the literal
`SelectedProjectionTailDecay` of the production family.

Private machinery of the committed conditional-closure chain is
reconstructed verbatim under the `etw_`/`etw2_` prefixes
(PRIVATE_RECONSTRUCTION_ALLOWED; the original files are append-only).
-/

private theorem etw_packet_differentiableAt_of_mem_open
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

private theorem etw_packet_zero_outside (k : ℕ) (y : ℝ)
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

private theorem etw_packet_differentiableAt_of_gt
    (k : ℕ) {y : ℝ}
    (hy : (selectedFerrersPreAnchorPair k).pw.lambda < y) :
    DifferentiableAt ℝ (selectedFerrersLemma73SourcePacket k) y := by
  have heq : selectedFerrersLemma73SourcePacket k =ᶠ[nhds y]
      (fun _ : ℝ => (0 : ℂ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hy] with z hz
    exact etw_packet_zero_outside k z
      (fun hmem => absurd hmem.2 (not_le.mpr hz))
  exact (differentiableAt_const (0 : ℂ)).congr_of_eventuallyEq heq

/-- Off the single positive seam `y = lambda` the packet is differentiable at
every positive argument. -/
private theorem etw_packet_differentiableAt_of_pos_ne
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
  · exact etw_packet_differentiableAt_of_mem_open k ⟨by linarith, hlt⟩
  · exact etw_packet_differentiableAt_of_gt k hgt

/-! ## The finite representation on the window -/

private theorem etw_packet_windowFiniteSupport (k : ℕ) :
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

private theorem etw_logCoordinate_mem_window
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
private theorem etw_rep_eq_finite
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
      (etw_packet_windowFiniteSupport k)
      (etw_logCoordinate_mem_window k hx)]

#print axioms etw_packet_differentiableAt_of_pos_ne
#print axioms etw_rep_eq_finite

/-! ## The exact additive derivative decomposition -/

/-- The weighted-derivative packet `Q_k(y) = y * pkt'(y)`.  Its comb is the
exact derivative content of the representative; it is kept signed. -/
private noncomputable def etw_Q (k : ℕ) (y : ℝ) : ℂ :=
  (y : ℂ) * deriv (selectedFerrersLemma73SourcePacket k) y

/-- At every seam-free interior point the representative has the exact
derivative `(1/2) * rep + sqrt u * Σ_{active} Q(n u)`.  This is the additive
decomposition the derivative verdict puts first; nothing is taken in norm and
nothing about the mass of `Q` is asserted. -/
private theorem etw_hasDerivAt_of_no_seam
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
            etw_Q k (((n : ℕ) : ℝ) *
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
        (etw_Q k (((n : ℕ) : ℝ) * u x)) x := by
    intro n _
    have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hargPos : 0 < ((n : ℕ) : ℝ) * u x := mul_pos hnpos (hu0 x)
    have hargNe : ((n : ℕ) : ℝ) * u x ≠
        (selectedFerrersPreAnchorPair k).pw.lambda := by
      rw [selectedFerrersPreAnchorPair_lambda_eq k, ← hlamdef]
      exact hseam n
    have hpkt := (etw_packet_differentiableAt_of_pos_ne k hargPos
      hargNe).hasDerivAt
    have hinner : HasDerivAt (fun w : ℝ => ((n : ℕ) : ℝ) * u w)
        (((n : ℕ) : ℝ) * u x) x := (hcoordDeriv x).const_mul _
    have hcomp := hpkt.scomp x hinner
    have hval : (((n : ℕ) : ℝ) * u x) •
        deriv (selectedFerrersLemma73SourcePacket k) (((n : ℕ) : ℝ) * u x) =
        etw_Q k (((n : ℕ) : ℝ) * u x) := by
      rw [etw_Q, Complex.real_smul]
    rw [hval] at hcomp
    exact hcomp
  -- derivative of the finite comb
  have hcombDeriv : HasDerivAt (fun w : ℝ =>
      ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u w))
      (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        etw_Q k (((n : ℕ) : ℝ) * u x)) x :=
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
            etw_Q k (((n : ℕ) : ℝ) * u x)) +
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
    rw [etw_rep_eq_finite k ⟨hw.1.le, hw.2.le⟩, finiteEStar, finiteEStarCore]
  have hgoal := hfinite.congr_of_eventuallyEq hrepEq
  -- identify the derivative value with the stated decomposition
  have hvalue :
      ((((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ)) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u x)) +
        ((Real.sqrt (u x) : ℝ) : ℂ) *
          (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            etw_Q k (((n : ℕ) : ℝ) * u x)) +
        (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
          (((1 / 2 * Real.sqrt (u x) : ℝ) : ℂ))) =
      ((1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
        ((Real.sqrt (u x) : ℝ) : ℂ) *
          ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            etw_Q k (((n : ℕ) : ℝ) * u x)) := by
    rw [etw_rep_eq_finite k ⟨hx.1.le, hx.2.le⟩, finiteEStar, finiteEStarCore]
    push_cast
    ring
  rw [hvalue] at hgoal
  exact hgoal

#print axioms etw_hasDerivAt_of_no_seam

/-! ## The authorized reduction

`DerivativeBudget ≤ (1/2)·L1 + ∫ √u·‖Q-comb‖`.  The derivative equals the D2
decomposition off the finite seam set, hence almost everywhere; the budget
integrand is dominated pointwise a.e. and the comparison integral carries the
rest.  Nothing here bounds the `Q`-comb: that is the exact open supplier
`W5_LOG_DERIVATIVE_BUDGET_BOUNDED` of the conditional-closure verdict. -/

/-- The finite additive seam set: images of the multiplicative seams. -/
private def etw_seamSet (k : ℕ) : Set ℝ :=
  ⋃ n ∈ ((sourcePositiveIndexFinset
      (selectedFerrersPreAnchorIndex k) : Finset ℕ+) : Set ℕ+),
    {x : ℝ | ((n : ℕ) : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) =
      lambda_m (selectedFerrersPreAnchorIndex k)}

private theorem etw_seamSet_measure_zero (k : ℕ) :
    MeasureTheory.volume (etw_seamSet k) = 0 := by
  have hfin : (etw_seamSet k).Finite := by
    rw [etw_seamSet]
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
private theorem etw_budget_reduction (k : ℕ)
    (hint : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
        Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
          ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            etw_Q k (((n : ℕ) : ℝ) *
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
              etw_Q k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))‖) := by
  have hL0 : (0 : ℝ) ≤ L_m (selectedFerrersPreAnchorIndex k) :=
    (logLength_pos (selectedFerrersPreAnchorIndex k)).le
  rw [selectedFerrersAbelLogDerivativeBudget]
  apply intervalIntegral.integral_mono_ae_restrict hL0 hbudget hint
  -- pointwise a.e. bound off the seam set
  have hnull : MeasureTheory.volume (etw_seamSet k) = 0 :=
    etw_seamSet_measure_zero k
  have hae : ∀ᵐ x ∂(MeasureTheory.volume.restrict
      (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))),
      x ∉ etw_seamSet k :=
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
      rw [etw_seamSet]
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
    have hd := etw_hasDerivAt_of_no_seam k hxint hseam
    rw [hd.deriv]
    calc
      ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
          (Real.sqrt (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
            ∑ n ∈ sourcePositiveIndexFinset
              (selectedFerrersPreAnchorIndex k),
              etw_Q k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))‖ ≤
          ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x‖ +
            ‖(Real.sqrt (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) : ℂ) *
              ∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
                etw_Q k (((n : ℕ) : ℝ) *
                  (Real.exp x /
                    lambda_m (selectedFerrersPreAnchorIndex k)))‖ :=
        norm_add_le _ _
      _ = (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
            Real.sqrt (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) *
              ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
                etw_Q k (((n : ℕ) : ℝ) *
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

private theorem etw2_coeff_transport
    {i i' : PairIndex} (hii : i = i')
    {h h' : ℝ → ℂ} (hhh : h = h')
    (w : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (w' : MemLp (E_star h') 2 (dStar.restrict (I_m i')))
    (n : ℤ) :
    physicalFourierCoefficient i (gTrial_m i h w) n =
      physicalFourierCoefficient i' (gTrial_m i' h' w') n := by
  subst hii
  subst hhh
  rfl

private theorem etw2_eStar_scale (k : ℕ) (u : ℝ) :
    E_star (selectedFerrersLemma73SourcePacket k) u =
      selectedFerrersLemma73SourceScale k *
        E_star (prolateCombination (selectedFerrersPreAnchorPair k)) u := by
  unfold E_star selectedFerrersLemma73SourcePacket
  rw [tsum_mul_left]
  ring

private theorem etw2_gTrial_eq_smul (k : ℕ) :
    gTrial_m (selectedFerrersPreAnchorIndex k)
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) =
      (selectedFerrersLemma73SourceScale k)⁻¹ • selectedFerrersEStarHm k := by
  set i := selectedFerrersPreAnchorIndex k with hi
  have hcne : selectedFerrersLemma73SourceScale k ≠ 0 :=
    selectedFerrersLemma73SourceScale_ne k
  apply MeasureTheory.Lp.ext
  have h1 : (gTrial_m i
        (prolateCombination (selectedFerrersPreAnchorPair k))
        (selectedFerrersPreAnchorPair_eStar_memLp k) : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      E_star (prolateCombination (selectedFerrersPreAnchorPair k)) :=
    MemLp.coeFn_toLp _
  have h2 : (selectedFerrersEStarHm k : ℝ → ℂ)
      =ᵐ[dStar.restrict (I_m i)]
      E_star (selectedFerrersLemma73SourcePacket k) :=
    MemLp.coeFn_toLp (w5m_eStar_memLp k)
  have hsmul := MeasureTheory.Lp.coeFn_smul
    ((selectedFerrersLemma73SourceScale k)⁻¹) (selectedFerrersEStarHm k)
  filter_upwards [h1, h2, hsmul] with u hu1 hu2 hu3
  rw [hu1, hu3]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hu2, etw2_eStar_scale k u]
  field_simp

/-- Local clone of the private center bound: `H(0) = 0`, so the F72.6 window
rate at the origin bounds the packet's central value. -/
private theorem etw2_center_bound
    {C : ℝ}
    (hrate : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖selectedFerrersLemma73SourceScale k *
            prolateCombination (selectedFerrersPreAnchorPair k) x -
          (4 : ℂ) * explicitCCMLimitH x‖ ≤
            C / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      ‖selectedFerrersLemma73SourcePacket k 0‖ ≤
        C / (selectedFerrersPaperLambda k) ^ 2 := by
  filter_upwards [hrate] with k hk
  have hlam : 0 ≤ selectedFerrersPaperLambda k := Real.sqrt_nonneg _
  have hmem : (0 : ℝ) ∈ Set.Icc (-(selectedFerrersPaperLambda k))
      (selectedFerrersPaperLambda k) := ⟨by linarith, hlam⟩
  have h := hk 0 hmem
  have hH0 : explicitCCMLimitH 0 = 0 := by
    rw [explicitCCMLimitH]
    norm_num
  rw [hH0, mul_zero, sub_zero] at h
  exact h

private theorem etw2_paperLambda_one_le (k : ℕ) :
    (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
  apply Real.one_le_sqrt.mpr
  have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
  exact_mod_cast this



/-! ## S1: per-mode Sturm energy instantiation on the selected family -/

/-- Imaginary parts of the two anchor scalars vanish. -/
private theorem etw3_anchor0_im (k : ℕ) :
    (centerAnchorScalarZero k).im = 0 := by
  rw [centerAnchorScalarZero, one_div, Complex.inv_im,
    selectedFerrersCenterZero_im]
  simp

private theorem etw3_anchor4_im (k : ℕ) :
    (centerAnchorScalarFour k).im = 0 := by
  rw [centerAnchorScalarFour, Complex.div_im,
    selectedFerrersCenterFour_im]
  simp

/-- Real product bookkeeping: products of imaginary-free numbers stay
imaginary-free with multiplicative real parts. -/
private theorem etw3_mul_real {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z * w).im = 0 ∧ (z * w).re = z.re * w.re := by
  constructor
  · rw [Complex.mul_im, hz, hw]
    ring
  · rw [Complex.mul_re, hz, hw]
    ring

/-- The χ-scaled anchored real scalar: on the open window,
`re(χ·a·h(y)) = c·φ(y)` with `c = χ·a.re/N`. -/
private theorem etw3_re_eq
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject)
    (χv : ℝ) (a : ℂ) (ha : a.im = 0) {y : ℝ}
    (hy : y ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject)) :
    ((χv : ℂ) * (a * S.normalizedPhysicalMode y)).re =
      (χv * a.re / S.physicalL2Normalization) *
        mode4PhysicalFerrersSeries mProject S.coefficients y := by
  have hN : (0 : ℝ) < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hval : S.normalizedPhysicalMode y =
      (((mode4PhysicalFerrersSeries mProject S.coefficients y /
        S.physicalL2Normalization : ℝ)) : ℂ) := by
    rw [Mode4FerrersRegularEvenProlateSolution.normalizedPhysicalMode,
      Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem hy, mode4PhysicalFerrersSeriesComplex]
    push_cast
    ring
  rw [hval]
  have h1 := etw3_mul_real (z := a)
    (w := (((mode4PhysicalFerrersSeries mProject S.coefficients y /
      S.physicalL2Normalization : ℝ)) : ℂ)) ha (Complex.ofReal_im _)
  have h2 := etw3_mul_real (z := (χv : ℂ))
    (w := a * (((mode4PhysicalFerrersSeries mProject S.coefficients y /
      S.physicalL2Normalization : ℝ)) : ℂ)) (Complex.ofReal_im _) h1.1
  rw [h2.2, h1.2, Complex.ofReal_re, Complex.ofReal_re]
  field_simp

/-- Per-mode `C0` defect rate against the χ-scaled cylinder profile. -/
private theorem etw3_defect_rate
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject)
    (χv : ℝ) (hχ2 : |χv| ≤ 2)
    (a : ℂ) (ha : a.im = 0)
    (ctW : ℝ → ℝ) (n : ℕ)
    (hctW : ∀ y : ℝ, ((ctW y : ℝ) : ℂ) =
      ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))
    (Cj : ℝ)
    (hrate : ∀ y ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject),
      ‖a * S.normalizedPhysicalMode y -
        ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ)‖ ≤
        Cj / (Real.sqrt mProject) ^ 2) :
    ∀ y ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject),
      |(χv * a.re / S.physicalL2Normalization) *
        mode4PhysicalFerrersSeries mProject S.coefficients y -
        χv * ctW y| ≤ 2 * Cj / (Real.sqrt mProject) ^ 2 := by
  intro y hy
  have h1 := hrate y hy
  have h2 : ‖(χv : ℂ) * (a * S.normalizedPhysicalMode y -
      ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))‖ ≤
      2 * (Cj / (Real.sqrt mProject) ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul hχ2 h1 (norm_nonneg _) (by norm_num)
  have h3 : ((χv : ℂ) * (a * S.normalizedPhysicalMode y -
      ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))).re =
      (χv * a.re / S.physicalL2Normalization) *
        mode4PhysicalFerrersSeries mProject S.coefficients y -
        χv * ctW y := by
    rw [mul_sub, Complex.sub_re, etw3_re_eq S hm χv a ha hy]
    congr 1
    rw [← hctW]
    have := etw3_mul_real (z := (χv : ℂ)) (w := ((ctW y : ℝ) : ℂ))
      (Complex.ofReal_im _) (Complex.ofReal_im _)
    rw [this.2, Complex.ofReal_re, Complex.ofReal_re]
  calc |(χv * a.re / S.physicalL2Normalization) *
      mode4PhysicalFerrersSeries mProject S.coefficients y - χv * ctW y| =
      |((χv : ℂ) * (a * S.normalizedPhysicalMode y -
        ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))).re| := by
        rw [h3]
    _ ≤ ‖(χv : ℂ) * (a * S.normalizedPhysicalMode y -
        ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))‖ :=
        Complex.abs_re_le_norm _
    _ ≤ 2 * (Cj / (Real.sqrt mProject) ^ 2) := h2
    _ = 2 * Cj / (Real.sqrt mProject) ^ 2 := by ring


/-- **Per-mode energy instantiation.**  The node-1 rate ledger applied to
the χ-scaled cylinder profile: the defect-derivative energy obeys the
`/λ²`-class bound with fully explicit constants. -/
private theorem etw3_energy
    {mProject K' : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mProject K' Λ)
    (hm : 2 ≤ mProject) (hK : 3 ≤ K')
    (hsep :
      ∀ q ≥ K',
        (31 / 24 : ℝ) * mode4JacobiG mProject ≤
          mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (χv : ℝ) (hχ2 : |χv| ≤ 2) (a : ℂ) (ha : a.im = 0)
    (ctW ctWd ctWdd : ℝ → ℝ) (μ : ℝ) (hμ : 0 < μ)
    (hW : ∀ y : ℝ, HasDerivAt ctW (ctWd y) y)
    (hWd : ∀ y : ℝ, HasDerivAt ctWd (ctWdd y) y)
    (hWcont : Continuous ctW) (hWddcont : Continuous ctWdd)
    (hcylrel : ∀ y : ℝ, -ctWdd y + 4 * Real.pi ^ 2 * y ^ 2 * ctW y =
      μ * ctW y)
    (n : ℕ)
    (hctW : ∀ y : ℝ, ((ctW y : ℝ) : ℂ) =
      ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ))
    (Cj : ℝ) (hCj : 0 ≤ Cj)
    (hrate : ∀ y ∈ Icc (-(Real.sqrt mProject)) (Real.sqrt mProject),
      ‖a * S.normalizedPhysicalMode y -
        ((parabolicCylinderD n (projectCylinderArgument y) : ℝ) : ℂ)‖ ≤
        Cj / (Real.sqrt mProject) ^ 2)
    (Ce : ℝ)
    (hEps : |Λ + mode4JacobiG mProject - (mProject : ℝ) * μ| ≤ Ce)
    (KW Dtr : ℝ)
    (hKW : (∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
      |ctW y|) ≤ KW)
    (hDtr : (∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
      |y ^ 2 * ctWdd y + 2 * y * ctWd y|) ≤ Dtr)
    (hKW0 : 0 ≤ KW) (hDtr0 : 0 ≤ Dtr) :
    (∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
      ((Real.sqrt mProject) ^ 2 - y ^ 2) *
        ((χv * a.re / S.physicalL2Normalization) *
          mode4PhysicalFerrersFirstDerivativeSeries mProject
            S.coefficients y - χv * ctWd y) ^ 2) ≤
      ((mProject : ℝ) * μ * (2 * Cj / (Real.sqrt mProject) ^ 2) ^ 2 *
        (Real.sqrt μ / Real.pi) +
      Ce * (2 * KW + 2 * (2 * Cj)) * (2 * Cj / (Real.sqrt mProject) ^ 2) +
      (2 * Dtr) * (2 * Cj / (Real.sqrt mProject) ^ 2)) := by
  have hmR : (0 : ℝ) < (mProject : ℝ) := by positivity
  have hm2 : (2 : ℝ) ≤ (mProject : ℝ) := by exact_mod_cast hm
  have hlam0 : (0 : ℝ) < Real.sqrt mProject := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ Real.sqrt mProject := by
    apply Real.one_le_sqrt.mpr
    linarith
  set c : ℝ := χv * a.re / S.physicalL2Normalization with hc
  have hCd := etw3_defect_rate S hm χv hχ2 a ha ctW n hctW Cj hrate
  -- ledger with W := χ·ctW
  apply sturm_defect_energy_rate_ledger S hm hK hsep hΛ c
    (fun y => χv * ctW y) (fun y => χv * ctWd y) (fun y => χv * ctWdd y)
    (fun y => (hW y).const_mul χv) (fun y => (hWd y).const_mul χv)
    (continuous_const.mul hWcont) (continuous_const.mul hWddcont)
    μ (2 * Cj / (Real.sqrt mProject) ^ 2) Ce
    (2 * KW + 2 * (2 * Cj)) (2 * Dtr) hμ (by positivity)
    (fun y => by
      have h := hcylrel y
      simp only
      linear_combination (-χv) * h)
    (fun y hy => by
      have := hCd y (Ioo_subset_Icc_self hy)
      rw [← hc] at this
      exact this)
    hEps
    ?_ ?_
  · -- the mode L¹ mass
    have hpoint : ∀ y ∈ Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
        |c * mode4PhysicalFerrersSeries mProject S.coefficients y| ≤
        |χv * ctW y| + 2 * Cj / (Real.sqrt mProject) ^ 2 := by
      intro y hy
      have h1 := hCd y (Ioo_subset_Icc_self hy)
      rw [← hc] at h1
      have := abs_sub_abs_le_abs_sub
        (c * mode4PhysicalFerrersSeries mProject S.coefficients y)
        (χv * ctW y)
      linarith [this, h1]
    have hint1 : IntegrableOn
        (fun y => |c * mode4PhysicalFerrersSeries mProject
          S.coefficients y|)
        (Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject)) volume := by
      apply MeasureTheory.IntegrableOn.mono_set
        (t := Icc (-(Real.sqrt mProject)) (Real.sqrt mProject))
      · apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply ContinuousOn.abs
        exact (sturm_physSeries_continuousOn_closed S hm).const_smul c
          |>.congr (fun x _ => by simp [smul_eq_mul])
      · exact Ioo_subset_Icc_self
    have hint2 : IntegrableOn
        (fun y => |χv * ctW y| + 2 * Cj / (Real.sqrt mProject) ^ 2)
        (Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject)) volume := by
      apply MeasureTheory.Integrable.add
      · apply MeasureTheory.IntegrableOn.mono_set
          (t := Icc (-(Real.sqrt mProject)) (Real.sqrt mProject))
        · exact ((continuous_const.mul hWcont).abs.continuousOn).integrableOn_compact
            isCompact_Icc
        · exact Ioo_subset_Icc_self
      · exact MeasureTheory.integrableOn_const
          (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top)
    calc (∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
        |c * mode4PhysicalFerrersSeries mProject S.coefficients y|) ≤
        ∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
          (|χv * ctW y| + 2 * Cj / (Real.sqrt mProject) ^ 2) := by
          apply MeasureTheory.setIntegral_mono_on hint1 hint2
            measurableSet_Ioo hpoint
      _ ≤ 2 * KW + 2 * (2 * Cj) := by
          have hint2a : IntegrableOn (fun y => |χv * ctW y|)
              (Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject))
              volume := by
            apply MeasureTheory.IntegrableOn.mono_set
              (t := Icc (-(Real.sqrt mProject)) (Real.sqrt mProject))
            · exact ((continuous_const.mul
                hWcont).abs.continuousOn).integrableOn_compact
                isCompact_Icc
            · exact Ioo_subset_Icc_self
          rw [MeasureTheory.integral_add hint2a
            (MeasureTheory.integrableOn_const
              (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top))]
          have hA : (∫ y in Ioo (-(Real.sqrt mProject))
              (Real.sqrt mProject), |χv * ctW y|) ≤ 2 * KW := by
            have hpt : ∀ y ∈ Ioo (-(Real.sqrt mProject))
                (Real.sqrt mProject), |χv * ctW y| ≤ 2 * |ctW y| := by
              intro y _
              rw [abs_mul]
              apply mul_le_mul_of_nonneg_right hχ2 (abs_nonneg _)
            calc (∫ y in Ioo (-(Real.sqrt mProject))
                (Real.sqrt mProject), |χv * ctW y|) ≤
                ∫ y in Ioo (-(Real.sqrt mProject))
                  (Real.sqrt mProject), 2 * |ctW y| := by
                  apply MeasureTheory.setIntegral_mono_on _ _
                    measurableSet_Ioo hpt
                  · apply MeasureTheory.IntegrableOn.mono_set
                      (t := Icc (-(Real.sqrt mProject))
                        (Real.sqrt mProject))
                    · exact ((continuous_const.mul
                        hWcont).abs.continuousOn).integrableOn_compact
                        isCompact_Icc
                    · exact Ioo_subset_Icc_self
                  · apply MeasureTheory.IntegrableOn.mono_set
                      (t := Icc (-(Real.sqrt mProject))
                        (Real.sqrt mProject))
                    · exact ((hWcont.abs.continuousOn).const_smul
                        (2:ℝ)).congr (fun x _ => by
                          simp [smul_eq_mul]) |>.integrableOn_compact
                        isCompact_Icc
                    · exact Ioo_subset_Icc_self
              _ = 2 * ∫ y in Ioo (-(Real.sqrt mProject))
                  (Real.sqrt mProject), |ctW y| :=
                  MeasureTheory.integral_const_mul _ _
              _ ≤ 2 * KW := by linarith [hKW]
          have hB : (∫ _ in Ioo (-(Real.sqrt mProject))
              (Real.sqrt mProject),
              (2 * Cj / (Real.sqrt mProject) ^ 2 : ℝ)) ≤ 2 * (2 * Cj) := by
            rw [MeasureTheory.setIntegral_const, smul_eq_mul,
              measureReal_def, Real.volume_Ioo,
              ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤
                Real.sqrt mProject - -(Real.sqrt mProject))]
            have h2lam : Real.sqrt (mProject : ℝ) -
                -(Real.sqrt mProject) = 2 * Real.sqrt mProject := by ring
            rw [h2lam]
            have hle : 2 * Real.sqrt mProject *
                (2 * Cj / (Real.sqrt mProject) ^ 2) =
                4 * Cj / Real.sqrt mProject := by
              field_simp
              ring
            rw [hle]
            rw [div_le_iff₀ hlam0]
            nlinarith [hCj, hlam1]
          linarith [hA, hB]
  · -- the χ-scaled transport L¹ mass
    have hpt : ∀ y ∈ Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
        |y ^ 2 * (χv * ctWdd y) + 2 * y * (χv * ctWd y)| ≤
        2 * |y ^ 2 * ctWdd y + 2 * y * ctWd y| := by
      intro y _
      have heq : y ^ 2 * (χv * ctWdd y) + 2 * y * (χv * ctWd y) =
          χv * (y ^ 2 * ctWdd y + 2 * y * ctWd y) := by ring
      rw [heq, abs_mul]
      apply mul_le_mul_of_nonneg_right hχ2 (abs_nonneg _)
    have hWdcont : Continuous ctWd :=
      continuous_iff_continuousAt.mpr fun x => (hWd x).continuousAt
    have htr_cont : Continuous
        (fun y : ℝ => y ^ 2 * ctWdd y + 2 * y * ctWd y) := by
      fun_prop
    have hint1 : IntegrableOn
        (fun y => |y ^ 2 * (χv * ctWdd y) + 2 * y * (χv * ctWd y)|)
        (Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject)) volume := by
      apply MeasureTheory.IntegrableOn.mono_set
        (t := Icc (-(Real.sqrt mProject)) (Real.sqrt mProject))
      · apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply Continuous.continuousOn
        fun_prop
      · exact Ioo_subset_Icc_self
    have hint2 : IntegrableOn
        (fun y => 2 * |y ^ 2 * ctWdd y + 2 * y * ctWd y|)
        (Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject)) volume := by
      apply MeasureTheory.IntegrableOn.mono_set
        (t := Icc (-(Real.sqrt mProject)) (Real.sqrt mProject))
      · apply ContinuousOn.integrableOn_compact isCompact_Icc
        apply Continuous.continuousOn
        fun_prop
      · exact Ioo_subset_Icc_self
    calc (∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
        |y ^ 2 * (χv * ctWdd y) + 2 * y * (χv * ctWd y)|) ≤
        ∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
          2 * |y ^ 2 * ctWdd y + 2 * y * ctWd y| :=
        MeasureTheory.setIntegral_mono_on hint1 hint2 measurableSet_Ioo hpt
      _ = 2 * ∫ y in Ioo (-(Real.sqrt mProject)) (Real.sqrt mProject),
          |y ^ 2 * ctWdd y + 2 * y * ctWd y| :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ 2 * Dtr := by linarith [hDtr]

/-! ### S2: cylinder transport identification and explicit L¹ constants

The Sturm ledger consumes the transport mass `∫ |y²W'' + 2yW'|`.  For the
two fixed profiles this integrand is literally the committed transport
profile `ctT₀ / ctT₄`, so the committed global L¹ bound pays it.  The
profile L¹ masses `KW` are paid by an elementary envelope
`|poly| ≤ C e^{s/2}` — no Gaussian moments are needed. -/

private theorem etw4_ctT0_eq (y : ℝ) :
    y ^ 2 * ctW0dd y + 2 * y * ctW0d y = ctT0 y := by
  simp only [ctW0dd, ctW0d, ctT0]
  ring

private theorem etw4_ctT4_eq (y : ℝ) :
    y ^ 2 * ctW4dd y + 2 * y * ctW4d y = ctT4 y := by
  simp only [ctW4dd, ctW4d, ctT4]
  ring

/-- Elementary sub-exponential envelope: `s ≤ 4 e^{s/2}` for `s ≥ 0`. -/
private theorem etw4_lin_exp {s : ℝ} (hs : 0 ≤ s) :
    s ≤ 4 * Real.exp (s / 2) := by
  have h := Real.add_one_le_exp (s / 2)
  have hpos := Real.exp_pos (s / 2)
  nlinarith

/-- Elementary sub-exponential envelope: `s² ≤ 16 e^{s/2}` for `s ≥ 0`. -/
private theorem etw4_sq_exp {s : ℝ} (hs : 0 ≤ s) :
    s ^ 2 ≤ 16 * Real.exp (s / 2) := by
  have h := Real.add_one_le_exp (s / 4)
  have hpos := Real.exp_pos (s / 4)
  have hsq : (s / 4 + 1) ^ 2 ≤ Real.exp (s / 4) ^ 2 := by
    have h0 : 0 ≤ s / 4 + 1 := by linarith
    exact pow_le_pow_left₀ h0 h 2
  have hexp2 : Real.exp (s / 4) ^ 2 = Real.exp (s / 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  nlinarith [hsq, hexp2]

/-- Pointwise envelope for the mode-4 profile:
`|ctW₄ y| ≤ 355 e^{-π y²/2}`. -/
private theorem etw4_ctW4_envelope (y : ℝ) :
    |ctW4 y| ≤ 355 * Real.exp (-(Real.pi * y ^ 2) / 2) := by
  have hs : 0 ≤ Real.pi * y ^ 2 := by positivity
  set s : ℝ := Real.pi * y ^ 2 with hsdef
  have habs : |ctW4 y| ≤
      (16 * s ^ 2 + 24 * s + 3) * Real.exp (-s) := by
    rw [ctW4]
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexpeq : Real.exp (-Real.pi * y ^ 2) = Real.exp (-s) := by
      rw [hsdef]
      ring_nf
    rw [hexpeq]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : 16 * Real.pi ^ 2 * y ^ 4 - 24 * Real.pi * y ^ 2 + 3 =
        16 * s ^ 2 - 24 * s + 3 := by
      rw [hsdef]; ring
    rw [h1]
    have h2 : |16 * s ^ 2 - 24 * s + 3| ≤ 16 * s ^ 2 + 24 * s + 3 := by
      cases abs_cases (16 * s ^ 2 - 24 * s + 3) with
      | inl h => rw [h.1]; nlinarith
      | inr h => rw [h.1]; nlinarith
    exact h2
  have henv : (16 * s ^ 2 + 24 * s + 3) ≤ 355 * Real.exp (s / 2) := by
    have h1 := etw4_sq_exp hs
    have h2 := etw4_lin_exp hs
    have h3 : (1 : ℝ) ≤ Real.exp (s / 2) := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    nlinarith
  calc |ctW4 y| ≤ (16 * s ^ 2 + 24 * s + 3) * Real.exp (-s) := habs
    _ ≤ (355 * Real.exp (s / 2)) * Real.exp (-s) := by
        apply mul_le_mul_of_nonneg_right henv (Real.exp_pos _).le
    _ = 355 * Real.exp (-s / 2) := by
        rw [mul_assoc, ← Real.exp_add]
        ring_nf
    _ = 355 * Real.exp (-(Real.pi * y ^ 2) / 2) := by rw [hsdef]

/-- The half-Gaussian has total mass `√2 ≤ 3/2`. -/
private theorem etw4_half_gauss :
    (∫ y : ℝ, Real.exp (-(Real.pi * y ^ 2) / 2)) ≤ 3 / 2 := by
  have hrw : (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) =
      fun y : ℝ => Real.exp (-(Real.pi / 2) * y ^ 2) := by
    funext y
    congr 1
    ring
  rw [hrw, integral_gaussian]
  have h2 : Real.pi / (Real.pi / 2) = 2 := by
    field_simp
  rw [h2]
  have hs : Real.sqrt 2 ≤ 3 / 2 := by
    rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    apply Real.sqrt_le_sqrt
    norm_num
  exact hs

private theorem etw4_half_gauss_integrable :
    Integrable (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) volume := by
  have hrw : (fun y : ℝ => Real.exp (-(Real.pi * y ^ 2) / 2)) =
      fun y : ℝ => Real.exp (-(Real.pi / 2) * y ^ 2) := by
    funext y
    congr 1
    ring
  rw [hrw]
  exact integrable_exp_neg_mul_sq (by positivity)

/-- Mode-0 profile L¹ mass on any window: `∫ |ctW₀| ≤ 1`. -/
private theorem etw4_KW0 (lam : ℝ) :
    (∫ y in Ioo (-lam) lam, |ctW0 y|) ≤ 1 := by
  have habs : ∀ y : ℝ, |ctW0 y| = Real.exp (-Real.pi * y ^ 2) := by
    intro y
    rw [ctW0]
    exact abs_of_pos (Real.exp_pos _)
  have hint : Integrable (fun y : ℝ => |ctW0 y|) volume := by
    simp only [habs]
    exact integrable_exp_neg_mul_sq Real.pi_pos
  have hle : (∫ y in Ioo (-lam) lam, |ctW0 y|) ≤ ∫ y : ℝ, |ctW0 y| :=
    setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hval : (∫ y : ℝ, |ctW0 y|) = 1 := by
    simp only [habs]
    rw [integral_gaussian]
    rw [div_self Real.pi_pos.ne']
    exact Real.sqrt_one
  linarith [hle, hval.le]

/-- Mode-4 profile L¹ mass on any window: `∫ |ctW₄| ≤ 533`. -/
private theorem etw4_KW4 (lam : ℝ) :
    (∫ y in Ioo (-lam) lam, |ctW4 y|) ≤ 533 := by
  have hmaj : Integrable
      (fun y : ℝ => 355 * Real.exp (-(Real.pi * y ^ 2) / 2)) volume :=
    etw4_half_gauss_integrable.const_mul 355
  have hint : Integrable (fun y : ℝ => |ctW4 y|) volume := by
    apply hmaj.mono'
    · apply Measurable.aestronglyMeasurable
      apply Measurable.abs
      have : Continuous ctW4 := by
        rw [show ctW4 = fun x : ℝ =>
          (16 * Real.pi ^ 2 * x ^ 4 - 24 * Real.pi * x ^ 2 + 3) *
            Real.exp (-Real.pi * x ^ 2) from rfl]
        fun_prop
      exact this.measurable
    · apply Filter.Eventually.of_forall
      intro y
      rw [Real.norm_eq_abs, abs_abs]
      exact etw4_ctW4_envelope y
  have hle : (∫ y in Ioo (-lam) lam, |ctW4 y|) ≤ ∫ y : ℝ, |ctW4 y| :=
    setIntegral_le_integral hint
      (Filter.Eventually.of_forall fun y => abs_nonneg _)
  have hval : (∫ y : ℝ, |ctW4 y|) ≤ 355 * (3 / 2) := by
    calc (∫ y : ℝ, |ctW4 y|) ≤
        ∫ y : ℝ, 355 * Real.exp (-(Real.pi * y ^ 2) / 2) := by
          apply integral_mono hint hmaj
          intro y
          exact etw4_ctW4_envelope y
      _ = 355 * ∫ y : ℝ, Real.exp (-(Real.pi * y ^ 2) / 2) :=
          integral_const_mul _ _
      _ ≤ 355 * (3 / 2) := by
          have := etw4_half_gauss
          nlinarith
  linarith [hle, hval]

/-- The committed transport L¹ budget, restricted to the ledger window and
rewritten in the `y²W'' + 2yW'` form the ledger consumes. -/
private theorem etw4_Dtr :
    ∃ Dtr : ℝ, 0 ≤ Dtr ∧ ∀ lam : ℝ,
      (∫ y in Ioo (-lam) lam, |y ^ 2 * ctW0dd y + 2 * y * ctW0d y|) ≤ Dtr ∧
      (∫ y in Ioo (-lam) lam, |y ^ 2 * ctW4dd y + 2 * y * ctW4d y|) ≤ Dtr := by
  obtain ⟨D, hD0, hD0le, hD4le, hint0, hint4⟩ := cylinderTransport_L1_bounded
  refine ⟨D, hD0, fun lam => ⟨?_, ?_⟩⟩
  · have hrw : (fun y : ℝ => |y ^ 2 * ctW0dd y + 2 * y * ctW0d y|) =
        fun y : ℝ => |ctT0 y| := by
      funext y
      rw [etw4_ctT0_eq]
    rw [hrw]
    have hle : (∫ y in Ioo (-lam) lam, |ctT0 y|) ≤ ∫ y : ℝ, |ctT0 y| :=
      setIntegral_le_integral hint0
        (Filter.Eventually.of_forall fun y => abs_nonneg _)
    linarith
  · have hrw : (fun y : ℝ => |y ^ 2 * ctW4dd y + 2 * y * ctW4d y|) =
        fun y : ℝ => |ctT4 y| := by
      funext y
      rw [etw4_ctT4_eq]
    rw [hrw]
    have hle : (∫ y in Ioo (-lam) lam, |ctT4 y|) ≤ ∫ y : ℝ, |ctT4 y| :=
      setIntegral_le_integral hint4
        (Filter.Eventually.of_forall fun y => abs_nonneg _)
    linarith

/-! ### S2b: the two selected χ-inclusive defect derivatives and their
Sturm energies

The mode-0 solution rides with `χ₂` and the mode-4 solution with `χ₀`
(the anchored packet identity fixes this pairing).  Each defect derivative
`gd_j = c_j φd_j − χ_j ctW_jd` receives the node-1 ledger with the χ-scaled
cylinder profile; the θ-input is the defect form `|Λ_j + G − (k+2)μ_j| ≤ Cθ`
with the exact per-mode cylinder eigenvalues `μ₀ = 2π`, `μ₄ = 18π`. -/

/-- Mode-0 χ-inclusive defect derivative on the selected schedule. -/
private noncomputable def etw4_gd0 (k : ℕ) (y : ℝ) : ℝ :=
  ((selectedFerrersPreAnchorPair k).chi2 *
      (centerAnchorScalarZero k).re /
      (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
    mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
      (selectedFerrersPreAnchorSolution0 k).coefficients y -
  (selectedFerrersPreAnchorPair k).chi2 * ctW0d y

/-- Mode-4 χ-inclusive defect derivative on the selected schedule. -/
private noncomputable def etw4_gd4 (k : ℕ) (y : ℝ) : ℝ :=
  ((selectedFerrersPreAnchorPair k).chi0 *
      (centerAnchorScalarFour k).re /
      (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
    mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
      (selectedFerrersPreAnchorSolution4 k).coefficients y -
  (selectedFerrersPreAnchorPair k).chi0 * ctW4d y

/-- Both selected classical eigenvalues are eventually `≤ 20`: the θ-defect
form pins `Λ_j ≈ (k+2)μ_j − G` and `G = (2π(k+2))²` dominates. -/
private theorem etw4_hLambda_ev
    (Cθ : ℝ)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤ Cθ) :
    ∀ᶠ k in Filter.atTop,
      mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 ≤ 20 ∧
      mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 ≤ 20 := by
  have hev : ∀ᶠ k : ℕ in Filter.atTop, Cθ ≤ ((k : ℕ) : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
  filter_upwards [hθ, hev] with k hk hkC
  have hpi : (3 : ℝ) ≤ Real.pi := by
    have := Real.pi_gt_three
    linarith
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have hG : mode4JacobiG (k + 2) = (2 * Real.pi * ((k + 2 : ℕ) : ℝ)) ^ 2 := by
    rw [mode4JacobiG]
  have hm2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hkk : ((k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (k : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  set M : ℝ := ((k + 2 : ℕ) : ℝ) with hM
  have hCM : Cθ ≤ M := le_trans hkC hkk
  have hpisq : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have hGge : 36 * M ^ 2 ≤ (2 * Real.pi * M) ^ 2 := by
    nlinarith [hpisq, sq_nonneg M]
  have hquad : (0 : ℝ) ≤ (M - 2) * (36 * M - 1) :=
    mul_nonneg (by linarith) (by linarith)
  constructor
  · have h1 := (abs_le.1 hk.1).2
    have h2pim : 2 * Real.pi * M ≤ 8 * M := by nlinarith
    nlinarith [h1, hG, hGge, hquad, h2pim]
  · have h1 := (abs_le.1 hk.2).2
    have h18pim : 18 * Real.pi * M ≤ 72 * M := by nlinarith
    nlinarith [h1, hG, hGge, hquad, h18pim]

/-- Eventual χ-scalar boundedness `|χ_j| ≤ 2` from the χ-defect family. -/
private theorem etw4_hchi2_ev
    (Cχ : ℝ)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2) :
    ∀ᶠ k in Filter.atTop,
      |(selectedFerrersPreAnchorPair k).chi0| ≤ 2 ∧
      |(selectedFerrersPreAnchorPair k).chi2| ≤ 2 := by
  have hev : ∀ᶠ k : ℕ in Filter.atTop, Cχ ≤ ((k : ℕ) : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cχ
  filter_upwards [hχ, hev] with k hk hkC
  have hlam : (selectedFerrersPaperLambda k) ^ 2 = ((k + 2 : ℕ) : ℝ) := by
    rw [selectedFerrersPaperLambda]
    exact Real.sq_sqrt (by positivity)
  have hkk : ((k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (k : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hm2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hfrac : Cχ / (selectedFerrersPaperLambda k) ^ 2 ≤ 1 := by
    rw [hlam, div_le_one (by linarith)]
    linarith
  constructor
  · have h0 := hk.1
    have habs := abs_sub_abs_le_abs_sub (1 : ℝ)
      (selectedFerrersPreAnchorPair k).chi0
    have h1 : |(1 : ℝ)| = 1 := abs_one
    have h2 := abs_sub_comm (1 : ℝ) (selectedFerrersPreAnchorPair k).chi0
    have h3 : |(selectedFerrersPreAnchorPair k).chi0| - 1 ≤
        |1 - (selectedFerrersPreAnchorPair k).chi0| := by
      calc |(selectedFerrersPreAnchorPair k).chi0| - 1 =
          |(selectedFerrersPreAnchorPair k).chi0| - |(1:ℝ)| := by rw [h1]
        _ ≤ |(selectedFerrersPreAnchorPair k).chi0 - 1| :=
            abs_sub_abs_le_abs_sub _ _
        _ = |1 - (selectedFerrersPreAnchorPair k).chi0| :=
            abs_sub_comm _ _
    linarith [le_trans h0 hfrac]
  · have h0 := hk.2
    have h3 : |(selectedFerrersPreAnchorPair k).chi2| - 1 ≤
        |1 - (selectedFerrersPreAnchorPair k).chi2| := by
      calc |(selectedFerrersPreAnchorPair k).chi2| - 1 =
          |(selectedFerrersPreAnchorPair k).chi2| - |(1:ℝ)| := by
            rw [abs_one]
        _ ≤ |(selectedFerrersPreAnchorPair k).chi2 - 1| :=
            abs_sub_abs_le_abs_sub _ _
        _ = |1 - (selectedFerrersPreAnchorPair k).chi2| :=
            abs_sub_comm _ _
    linarith [le_trans h0 hfrac]

/-- Continuity of the fixed second derivatives (plain poly-Gaussian). -/
private theorem etw4_ctW0dd_cont : Continuous ctW0dd := by
  rw [show ctW0dd = fun x : ℝ =>
    (4 * Real.pi ^ 2 * x ^ 2 - 2 * Real.pi) *
      Real.exp (-Real.pi * x ^ 2) from rfl]
  fun_prop

private theorem etw4_ctW4dd_cont : Continuous ctW4dd := by
  rw [show ctW4dd = fun x : ℝ =>
    (64 * Real.pi ^ 4 * x ^ 6 - 384 * Real.pi ^ 3 * x ^ 4 +
        444 * Real.pi ^ 2 * x ^ 2 - 54 * Real.pi) *
      Real.exp (-Real.pi * x ^ 2) from rfl]
  fun_prop

/-- **S2 mode-0 energy.**  The selected mode-0 defect derivative eventually
pays the node-1 Sturm energy at the exact `1/λ²` rate. -/
private theorem etw4_energy0_ev
    (C0 Cχ Cθ Dtr : ℝ) (hC0 : 0 ≤ C0) (hDtrNN : 0 ≤ Dtr)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤ Cθ)
    (hDtr : ∀ lam : ℝ,
      (∫ y in Ioo (-lam) lam, |y ^ 2 * ctW0dd y + 2 * y * ctW0d y|) ≤ Dtr) :
    ∀ᶠ k in Filter.atTop,
      (∫ y in Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
          (Real.sqrt ((k + 2 : ℕ) : ℝ)),
        ((Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 - y ^ 2) * etw4_gd0 k y ^ 2) ≤
      ((2 * Real.pi) * (2 * C0) ^ 2 * (Real.sqrt (2 * Real.pi) / Real.pi) +
        Cθ * (2 * 1 + 2 * (2 * C0)) * (2 * C0) + (2 * Dtr) * (2 * C0)) /
        ((k + 2 : ℕ) : ℝ) := by
  filter_upwards [hmode, etw4_hchi2_ev Cχ hχ, etw4_hLambda_ev Cθ hθ, hθ]
    with k hkmode hkχ hkΛ hkθ
  set m : ℕ := k + 2 with hm
  have hmcast : (0 : ℝ) < ((m : ℕ) : ℝ) := by positivity
  have hlamsq : (Real.sqrt ((m : ℕ) : ℝ)) ^ 2 = ((m : ℕ) : ℝ) :=
    Real.sq_sqrt hmcast.le
  have hpairh0 := (selectedFerrersPreAnchorPair_spec k).2.1
  have henergy := etw3_energy (mProject := m) (K' := 5 * m)
    (selectedFerrersPreAnchorSolution0 k)
    (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k)
    hkΛ.1
    (selectedFerrersPreAnchorPair k).chi2 hkχ.2
    (centerAnchorScalarZero k) (etw3_anchor0_im k)
    ctW0 ctW0d ctW0dd (2 * Real.pi) (by positivity)
    ctW0_hasDerivAt' ctW0d_hasDerivAt
    (continuous_iff_continuousAt.mpr fun x =>
      (ctW0_hasDerivAt' x).continuousAt)
    etw4_ctW0dd_cont
    ctW0_cylinder_eigenrelation
    0
    (fun y => by rw [ctW0_eq_cylinder])
    C0 hC0
    (by
      intro y hy
      have := hkmode y (by
        rw [selectedFerrersPaperLambda]
        exact hy)
      rw [hpairh0, selectedFerrersPaperLambda] at this
      exact this)
    Cθ hkθ.1
    1 Dtr (etw4_KW0 _) (hDtr _) (by norm_num) hDtrNN
  have hgd : ∀ y : ℝ, ((selectedFerrersPreAnchorPair k).chi2 *
      (centerAnchorScalarZero k).re /
      (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
        mode4PhysicalFerrersFirstDerivativeSeries m
          (selectedFerrersPreAnchorSolution0 k).coefficients y -
      (selectedFerrersPreAnchorPair k).chi2 * ctW0d y = etw4_gd0 k y := by
    intro y
    rw [etw4_gd0]
  have hrw : (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
      (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) * etw4_gd0 k y ^ 2) =
      (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
        (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) *
          (((selectedFerrersPreAnchorPair k).chi2 *
            (centerAnchorScalarZero k).re /
            (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
              mode4PhysicalFerrersFirstDerivativeSeries m
                (selectedFerrersPreAnchorSolution0 k).coefficients y -
            (selectedFerrersPreAnchorPair k).chi2 * ctW0d y) ^ 2) := rfl
  rw [hrw]
  calc (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
      (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) *
          (((selectedFerrersPreAnchorPair k).chi2 *
            (centerAnchorScalarZero k).re /
            (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
              mode4PhysicalFerrersFirstDerivativeSeries m
                (selectedFerrersPreAnchorSolution0 k).coefficients y -
            (selectedFerrersPreAnchorPair k).chi2 * ctW0d y) ^ 2) ≤
      ((m : ℝ) * (2 * Real.pi) *
          (2 * C0 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2) ^ 2 *
          (Real.sqrt (2 * Real.pi) / Real.pi) +
        Cθ * (2 * 1 + 2 * (2 * C0)) *
          (2 * C0 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2) +
        (2 * Dtr) * (2 * C0 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2)) := henergy
    _ = ((2 * Real.pi) * (2 * C0) ^ 2 *
          (Real.sqrt (2 * Real.pi) / Real.pi) +
        Cθ * (2 * 1 + 2 * (2 * C0)) * (2 * C0) +
        (2 * Dtr) * (2 * C0)) / ((m : ℕ) : ℝ) := by
        rw [hlamsq]
        field_simp

/-- **S2 mode-4 energy.**  Mirror of the mode-0 statement with `χ₀`,
`μ₄ = 18π` and the mode-4 profile constants. -/
private theorem etw4_energy4_ev
    (C4 Cχ Cθ Dtr : ℝ) (hC4 : 0 ≤ C4) (hDtrNN : 0 ≤ Dtr)
    (hmode : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2)
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤ Cθ)
    (hDtr : ∀ lam : ℝ,
      (∫ y in Ioo (-lam) lam, |y ^ 2 * ctW4dd y + 2 * y * ctW4d y|) ≤ Dtr) :
    ∀ᶠ k in Filter.atTop,
      (∫ y in Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
          (Real.sqrt ((k + 2 : ℕ) : ℝ)),
        ((Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 - y ^ 2) * etw4_gd4 k y ^ 2) ≤
      ((18 * Real.pi) * (2 * C4) ^ 2 *
          (Real.sqrt (18 * Real.pi) / Real.pi) +
        Cθ * (2 * 533 + 2 * (2 * C4)) * (2 * C4) + (2 * Dtr) * (2 * C4)) /
        ((k + 2 : ℕ) : ℝ) := by
  filter_upwards [hmode, etw4_hchi2_ev Cχ hχ, etw4_hLambda_ev Cθ hθ, hθ]
    with k hkmode hkχ hkΛ hkθ
  set m : ℕ := k + 2 with hm
  have hmcast : (0 : ℝ) < ((m : ℕ) : ℝ) := by positivity
  have hlamsq : (Real.sqrt ((m : ℕ) : ℝ)) ^ 2 = ((m : ℕ) : ℝ) :=
    Real.sq_sqrt hmcast.le
  have hpairh4 := (selectedFerrersPreAnchorPair_spec k).2.2.1
  have henergy := etw3_energy (mProject := m) (K' := 5 * m)
    (selectedFerrersPreAnchorSolution4 k)
    (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k)
    hkΛ.2
    (selectedFerrersPreAnchorPair k).chi0 hkχ.1
    (centerAnchorScalarFour k) (etw3_anchor4_im k)
    ctW4 ctW4d ctW4dd (18 * Real.pi) (by positivity)
    ctW4_hasDerivAt' ctW4d_hasDerivAt
    (continuous_iff_continuousAt.mpr fun x =>
      (ctW4_hasDerivAt' x).continuousAt)
    etw4_ctW4dd_cont
    ctW4_cylinder_eigenrelation
    4
    (fun y => by
      rw [parabolicCylinderD_four_projectArgument, ctW4]
      norm_cast
      ring)
    C4 hC4
    (by
      intro y hy
      have := hkmode y (by
        rw [selectedFerrersPaperLambda]
        exact hy)
      rw [hpairh4, selectedFerrersPaperLambda] at this
      exact this)
    Cθ hkθ.2
    533 Dtr (etw4_KW4 _) (hDtr _) (by norm_num) hDtrNN
  have hrw : (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
      (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) * etw4_gd4 k y ^ 2) =
      (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
        (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) *
          (((selectedFerrersPreAnchorPair k).chi0 *
            (centerAnchorScalarFour k).re /
            (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
              mode4PhysicalFerrersFirstDerivativeSeries m
                (selectedFerrersPreAnchorSolution4 k).coefficients y -
            (selectedFerrersPreAnchorPair k).chi0 * ctW4d y) ^ 2) := rfl
  rw [hrw]
  calc (∫ y in Ioo (-(Real.sqrt ((m : ℕ) : ℝ)))
      (Real.sqrt ((m : ℕ) : ℝ)),
        ((Real.sqrt ((m : ℕ) : ℝ)) ^ 2 - y ^ 2) *
          (((selectedFerrersPreAnchorPair k).chi0 *
            (centerAnchorScalarFour k).re /
            (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
              mode4PhysicalFerrersFirstDerivativeSeries m
                (selectedFerrersPreAnchorSolution4 k).coefficients y -
            (selectedFerrersPreAnchorPair k).chi0 * ctW4d y) ^ 2) ≤
      ((m : ℝ) * (18 * Real.pi) *
          (2 * C4 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2) ^ 2 *
          (Real.sqrt (18 * Real.pi) / Real.pi) +
        Cθ * (2 * 533 + 2 * (2 * C4)) *
          (2 * C4 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2) +
        (2 * Dtr) * (2 * C4 / (Real.sqrt ((m : ℕ) : ℝ)) ^ 2)) := henergy
    _ = ((18 * Real.pi) * (2 * C4) ^ 2 *
          (Real.sqrt (18 * Real.pi) / Real.pi) +
        Cθ * (2 * 533 + 2 * (2 * C4)) * (2 * C4) +
        (2 * Dtr) * (2 * C4)) / ((m : ℕ) : ℝ) := by
        rw [hlamsq]
        field_simp

/-! ### S3a: per-index global derivative bounds (integrability certificates)

These bounds certify integrability only; the sharp rate never passes through
them.  The inner half-window is paid by the committed derivative-term
majorant at `r = 1/2`; the outer band `[λ/2, λ)` is paid by the flux
derivative bound with the crude envelope `A = (Σ|a_q|) λ⁶`. -/

/-- The raw Ferrers series is dominated by the coefficient `ℓ¹` mass on the
closed unit interval. -/
private theorem etw5_series_le_l1
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ)
    {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    |mode4FerrersSeries S.coefficients t| ≤ ∑' q : ℕ, |S.coefficients q| := by
  have hterm : ∀ q : ℕ, ‖mode4FerrersTerm S.coefficients q t‖ ≤
      |S.coefficients q| := fun q =>
    mode4FerrersTerm_norm_le_coefficientAbs S.coefficients q t ht
  have hsumnorm : Summable
      (fun q : ℕ => ‖mode4FerrersTerm S.coefficients q t‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm
      S.coefficients_abs_summable
  rw [← Real.norm_eq_abs]
  calc ‖mode4FerrersSeries S.coefficients t‖ ≤
      ∑' q : ℕ, ‖mode4FerrersTerm S.coefficients q t‖ :=
        norm_tsum_le_tsum_norm hsumnorm
    _ ≤ ∑' q : ℕ, |S.coefficients q| :=
        hsumnorm.tsum_le_tsum hterm S.coefficients_abs_summable

/-- Inner-half bound on the physical first-derivative series via the
committed `r = 1/2` term majorant. -/
private theorem etw5_dseries_le_majorant
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ)
    (hm : 2 ≤ mP) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mP ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    {y : ℝ} (hy : |y| ≤ Real.sqrt mP / 2) :
    |mode4PhysicalFerrersFirstDerivativeSeries mP S.coefficients y| ≤
      ∑' q : ℕ,
        mode4FerrersFirstDerivativeMajorant S.coefficients (1 / 2) q := by
  have ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |S.coefficients q|) :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mP K Λ hm hK hsep hΛ S.coefficients S.tail_splice 2
  have hmR : (0 : ℝ) < (mP : ℝ) := by
    have : (0 : ℕ) < mP := by omega
    exact_mod_cast this
  have hlam0 : (0 : ℝ) < Real.sqrt mP := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ Real.sqrt mP := by
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ mP := by omega
    exact_mod_cast this
  set t : ℝ := y / Real.sqrt mP with htdef
  have ht : t ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2) := by
    rw [htdef]
    constructor
    · rw [neg_le, ← neg_div]
      apply div_le_of_le_mul₀ hlam0.le (by norm_num)
      have := (abs_le.1 hy).1
      nlinarith
    · apply div_le_of_le_mul₀ hlam0.le (by norm_num)
      have := (abs_le.1 hy).2
      nlinarith
  have hterm : ∀ q : ℕ,
      ‖mode4FerrersFirstDerivativeTerm S.coefficients q t‖ ≤
        mode4FerrersFirstDerivativeMajorant S.coefficients (1 / 2) q :=
    fun q => mode4FerrersFirstDerivativeTerm_norm_le
      S.coefficients (1 / 2) (by norm_num) (by norm_num) q t ht
  have hsumMaj : Summable (fun q : ℕ =>
      mode4FerrersFirstDerivativeMajorant S.coefficients (1 / 2) q) :=
    mode4FerrersFirstDerivativeMajorant_summable
      S.coefficients (1 / 2) ha2
  have hsumnorm : Summable (fun q : ℕ =>
      ‖mode4FerrersFirstDerivativeTerm S.coefficients q t‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm hsumMaj
  have hseries :
      |mode4FerrersFirstDerivativeSeries S.coefficients t| ≤
        ∑' q : ℕ,
          mode4FerrersFirstDerivativeMajorant S.coefficients (1 / 2) q := by
    rw [← Real.norm_eq_abs]
    calc ‖mode4FerrersFirstDerivativeSeries S.coefficients t‖ ≤
        ∑' q : ℕ, ‖mode4FerrersFirstDerivativeTerm S.coefficients q t‖ :=
          norm_tsum_le_tsum_norm hsumnorm
      _ ≤ _ := hsumnorm.tsum_le_tsum hterm hsumMaj
  have hphys : mode4PhysicalFerrersFirstDerivativeSeries mP
      S.coefficients y =
      (Real.sqrt mP)⁻¹ *
        mode4FerrersFirstDerivativeSeries S.coefficients t := rfl
  rw [hphys, abs_mul, abs_of_pos (inv_pos.2 hlam0)]
  have hinv1 : (Real.sqrt mP)⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hlam1
  have hnn : (0 : ℝ) ≤
      |mode4FerrersFirstDerivativeSeries S.coefficients t| := abs_nonneg _
  nlinarith [hseries]

/-- Global bound on the physical first-derivative series over the positive
open window: inner majorant + outer flux bound. -/
private theorem etw5_dseries_bound
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ)
    (hm : 2 ≤ mP) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mP ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20)
    (hθabs : |Λ + mode4JacobiG mP| ≤ (Real.sqrt mP) ^ 4) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ Set.Ioo (0 : ℝ) (Real.sqrt mP),
      |mode4PhysicalFerrersFirstDerivativeSeries mP S.coefficients y| ≤
        M := by
  set lam : ℝ := Real.sqrt mP with hlamdef
  have hmR : (0 : ℝ) < (mP : ℝ) := by
    have : (0 : ℕ) < mP := by omega
    exact_mod_cast this
  have hlam0 : (0 : ℝ) < lam := Real.sqrt_pos.2 hmR
  set S1 : ℝ := ∑' q : ℕ, |S.coefficients q| with hS1def
  have hS1nn : 0 ≤ S1 := tsum_nonneg fun q => abs_nonneg _
  set Minner : ℝ := ∑' q : ℕ,
    mode4FerrersFirstDerivativeMajorant S.coefficients (1 / 2) q
    with hMinnerdef
  have hMinnernn : 0 ≤ Minner := by
    apply tsum_nonneg
    intro q
    rw [mode4FerrersFirstDerivativeMajorant]
    positivity
  have houter : ∀ t ∈ Icc (lam / 2) lam,
      |mode4PhysicalFerrersSeries mP S.coefficients t| ≤
        (S1 * lam ^ 6) / lam ^ 6 := by
    intro t ht
    have hval : (S1 * lam ^ 6) / lam ^ 6 = S1 := by
      field_simp
    rw [hval]
    have hphys : mode4PhysicalFerrersSeries mP S.coefficients t =
        mode4FerrersSeries S.coefficients (t / lam) := rfl
    rw [hphys]
    apply etw5_series_le_l1 S
    constructor
    · have h1 : (0 : ℝ) ≤ t := le_trans (by positivity) ht.1
      have := div_nonneg h1 hlam0.le
      linarith
    · rw [div_le_one hlam0]
      exact ht.2
  have hflux := sturm_outer_flux_derivative_bound S hm hK hsep hΛ hθabs
    (S1 * lam ^ 6) (by positivity) houter
  refine ⟨max Minner (41 * (S1 * lam ^ 6) / lam ^ 3),
    le_max_of_le_left hMinnernn, ?_⟩
  intro y hy
  rcases le_or_gt y (lam / 2) with hin | hout
  · apply le_max_of_le_left
    apply etw5_dseries_le_majorant S hm hK hsep hΛ
    rw [abs_le]
    constructor
    · linarith [hy.1, hlam0]
    · exact hin
  · apply le_max_of_le_right
    exact hflux y ⟨hout.le, hy.2⟩

/-- The window coordinate of the selected schedule. -/
private theorem etw5_lambda_m_eq (k : ℕ) :
    lambda_m (selectedFerrersPreAnchorIndex k) =
      Real.sqrt ((k + 2 : ℕ) : ℝ) := rfl

/-- Exact packet derivative on the open positive window. -/
private theorem etw5_pkt_hasDerivAt (k : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ))) :
    HasDerivAt (selectedFerrersLemma73SourcePacket k)
      (selectedFerrersLemma73SourceScale k *
        ((((selectedFerrersPreAnchorPair k).I4 : ℂ) *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution0 k).coefficients y /
            ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
              ℂ)) -
          ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution4 k).coefficients y /
            ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
              ℂ))) /
          ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ))) y := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have hm : 2 ≤ k + 2 := by omega
  have hd0 : HasDerivAt (selectedFerrersPreAnchorPair k).h0
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y /
        ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
          ℂ)) y := by
    rw [hh0]
    exact normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution0 k) hm hy
  have hd4 : HasDerivAt (selectedFerrersPreAnchorPair k).h4
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y /
        ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
          ℂ)) y := by
    rw [hh4]
    exact normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution4 k) hm hy
  have hcomb : HasDerivAt
      (prolateCombination (selectedFerrersPreAnchorPair k))
      ((((selectedFerrersPreAnchorPair k).I4 : ℂ) *
          (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients y /
          ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
            ℂ)) -
        ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
          (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients y /
          ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
            ℂ))) /
        ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)) y := by
    unfold prolateCombination
    exact ((hd0.const_mul _).sub (hd4.const_mul _)).div_const _
  unfold selectedFerrersLemma73SourcePacket
  exact hcomb.const_mul _

/-- **Global packet-derivative bound** off the single positive seam, from
per-mode global derivative-series bounds. -/
private theorem etw5_pkt_deriv_bound (k : ℕ) (M0 M4 : ℝ)
    (hM0 : 0 ≤ M0) (hM4 : 0 ≤ M4)
    (hb0 : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ)),
      |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y| ≤ M0)
    (hb4 : ∀ y ∈ Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ)),
      |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y| ≤ M4) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ y : ℝ, 0 < y →
      y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
      ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P := by
  set lam : ℝ := Real.sqrt ((k + 2 : ℕ) : ℝ) with hlamdef
  set N0 : ℝ := (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization
    with hN0def
  set N4 : ℝ := (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization
    with hN4def
  have hN0pos : 0 < N0 :=
    (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization_pos
      (by omega)
  have hN4pos : 0 < N4 :=
    (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization_pos
      (by omega)
  set P : ℝ := ‖selectedFerrersLemma73SourceScale k‖ /
      ‖((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)‖ *
      (|(selectedFerrersPreAnchorPair k).I4| * (M0 / N0) +
        |(selectedFerrersPreAnchorPair k).I0| * (M4 / N4)) with hPdef
  have hPnn : 0 ≤ P := by
    rw [hPdef]
    positivity
  refine ⟨P, hPnn, ?_⟩
  intro y hy0 hyne
  have hlam_eq := etw5_lambda_m_eq k
  rcases lt_or_gt_of_ne hyne with hlt | hgt
  · -- interior: exact derivative formula
    have hyOpen : y ∈ Set.Ioo (-lam) lam := by
      constructor
      · linarith
      · rw [hlamdef, ← hlam_eq]
        exact hlt
    have hder := etw5_pkt_hasDerivAt k hyOpen
    rw [hder.deriv]
    have hyPos : y ∈ Set.Ioo (0 : ℝ) lam := ⟨hy0, hyOpen.2⟩
    have hnorm0 :
        ‖mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients y‖ ≤ M0 := by
      have hcast : mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients y =
          ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) :
            ℂ) := rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact hb0 y hyPos
    have hnorm4 :
        ‖mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients y‖ ≤ M4 := by
      have hcast : mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients y =
          ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) :
            ℂ) := rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      exact hb4 y hyPos
    set d0C := mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
      (selectedFerrersPreAnchorSolution0 k).coefficients y with hd0Cdef
    set d4C := mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
      (selectedFerrersPreAnchorSolution4 k).coefficients y with hd4Cdef
    set inner : ℂ := ((selectedFerrersPreAnchorPair k).I4 : ℂ) *
        (d0C / ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization :
          ℂ)) -
      ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
        (d4C / ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization :
          ℂ)) with hinnerdef
    have hinner_le : ‖inner‖ ≤
        |(selectedFerrersPreAnchorPair k).I4| * (M0 / N0) +
          |(selectedFerrersPreAnchorPair k).I0| * (M4 / N4) := by
      rw [hinnerdef]
      calc ‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
          (d0C / ((selectedFerrersPreAnchorSolution0
            k).physicalL2Normalization : ℂ)) -
          ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
          (d4C / ((selectedFerrersPreAnchorSolution4
            k).physicalL2Normalization : ℂ))‖ ≤
          ‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
            (d0C / ((selectedFerrersPreAnchorSolution0
              k).physicalL2Normalization : ℂ))‖ +
          ‖((selectedFerrersPreAnchorPair k).I0 : ℂ) *
            (d4C / ((selectedFerrersPreAnchorSolution4
              k).physicalL2Normalization : ℂ))‖ := norm_sub_le _ _
        _ = |(selectedFerrersPreAnchorPair k).I4| * (‖d0C‖ / N0) +
            |(selectedFerrersPreAnchorPair k).I0| * (‖d4C‖ / N4) := by
            rw [norm_mul, norm_mul, norm_div, norm_div,
              Complex.norm_real, Complex.norm_real,
              Complex.norm_real, Complex.norm_real,
              Real.norm_eq_abs, Real.norm_eq_abs,
              Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_pos hN0pos, abs_of_pos hN4pos]
        _ ≤ |(selectedFerrersPreAnchorPair k).I4| * (M0 / N0) +
            |(selectedFerrersPreAnchorPair k).I0| * (M4 / N4) := by
            gcongr
    rw [hPdef]
    by_cases hden : ‖((selectedFerrersPreAnchorPair
        k).normalizingDenominator : ℂ)‖ = 0
    · have hdz : ((selectedFerrersPreAnchorPair
          k).normalizingDenominator : ℂ) = 0 := by
        rwa [norm_eq_zero] at hden
      rw [hdz, div_zero, mul_zero, norm_zero]
      positivity
    · have hdpos : 0 < ‖((selectedFerrersPreAnchorPair
          k).normalizingDenominator : ℂ)‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hden)
      calc ‖selectedFerrersLemma73SourceScale k *
          (inner / ((selectedFerrersPreAnchorPair
            k).normalizingDenominator : ℂ))‖ =
          ‖selectedFerrersLemma73SourceScale k‖ *
            (‖inner‖ / ‖((selectedFerrersPreAnchorPair
              k).normalizingDenominator : ℂ)‖) := by
            rw [norm_mul, norm_div]
        _ ≤ ‖selectedFerrersLemma73SourceScale k‖ *
            ((|(selectedFerrersPreAnchorPair k).I4| * (M0 / N0) +
              |(selectedFerrersPreAnchorPair k).I0| * (M4 / N4)) /
              ‖((selectedFerrersPreAnchorPair
                k).normalizingDenominator : ℂ)‖) := by
            gcongr
        _ = ‖selectedFerrersLemma73SourceScale k‖ /
            ‖((selectedFerrersPreAnchorPair
              k).normalizingDenominator : ℂ)‖ *
            (|(selectedFerrersPreAnchorPair k).I4| * (M0 / N0) +
              |(selectedFerrersPreAnchorPair k).I0| * (M4 / N4)) := by
            ring
  · -- beyond the window: the packet vanishes on a neighborhood
    have hzero : selectedFerrersLemma73SourcePacket k =ᶠ[nhds y]
        (fun _ : ℝ => (0 : ℂ)) := by
      have hylam : (selectedFerrersPreAnchorPair k).pw.lambda < y := by
        rw [selectedFerrersPreAnchorPair_lambda_eq k]
        exact hgt
      filter_upwards [isOpen_Ioi.mem_nhds hylam] with z hz
      apply etw_packet_zero_outside k z
      intro hmem
      exact absurd hmem.2 (not_le.mpr hz)
    have hd : deriv (selectedFerrersLemma73SourcePacket k) y =
        deriv (fun _ : ℝ => (0 : ℂ)) y := hzero.deriv_eq
    rw [hd, deriv_const]
    simpa using hPnn

/-- **Eventual global packet-derivative bound** off the positive seam. -/
private theorem etw5_pktDeriv_bound_ev
    (Cθ : ℝ)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤ Cθ) :
    ∀ᶠ k in Filter.atTop,
      ∃ P : ℝ, 0 ≤ P ∧ ∀ y : ℝ, 0 < y →
        y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
        ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P := by
  have hevC : ∀ᶠ k : ℕ in Filter.atTop, Cθ ≤ ((k : ℕ) : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
  have hev57 : ∀ᶠ k : ℕ in Filter.atTop, 71 ≤ k :=
    Filter.eventually_ge_atTop 71
  filter_upwards [hθ, etw4_hLambda_ev Cθ hθ, hevC, hev57]
    with k hkθ hkΛ hkC hk57
  set m : ℕ := k + 2 with hm
  have hmR : (0 : ℝ) < ((m : ℕ) : ℝ) := by positivity
  have hsq4 : (Real.sqrt ((m : ℕ) : ℝ)) ^ 4 = ((m : ℕ) : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul,
      Real.sq_sqrt hmR.le]
  have hmk : ((k : ℕ) : ℝ) ≤ ((m : ℕ) : ℝ) := by
    have : (k : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hm73 : (73 : ℝ) ≤ ((m : ℕ) : ℝ) := by
    have : (73 : ℕ) ≤ m := by omega
    exact_mod_cast this
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have habs_bound : ∀ μv : ℝ, 0 ≤ μv → μv ≤ 18 * Real.pi →
      ∀ Λv : ℝ, |Λv + mode4JacobiG m - ((m : ℕ) : ℝ) * μv| ≤ Cθ →
      |Λv + mode4JacobiG m| ≤ (Real.sqrt ((m : ℕ) : ℝ)) ^ 4 := by
    intro μv hμ0 hμ18 Λv hΛv
    rw [hsq4]
    have h1 := (abs_le.1 hΛv).1
    have h2 := (abs_le.1 hΛv).2
    rw [abs_le]
    constructor
    · have hmul : 0 ≤ ((m : ℕ) : ℝ) * μv := by positivity
      nlinarith [hkC, hmk]
    · have hmul : ((m : ℕ) : ℝ) * μv ≤ ((m : ℕ) : ℝ) * (72 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hmR.le
        nlinarith
      nlinarith [hkC, hmk]
  have hθabs0 := habs_bound (2 * Real.pi) (by positivity)
    (by nlinarith [Real.pi_pos]) _ hkθ.1
  have hθabs4 := habs_bound (18 * Real.pi) (by positivity)
    (by nlinarith [Real.pi_pos]) _ hkθ.2
  obtain ⟨M0, hM0nn, hM0⟩ := etw5_dseries_bound
    (selectedFerrersPreAnchorSolution0 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.1 hθabs0
  obtain ⟨M4, hM4nn, hM4⟩ := etw5_dseries_bound
    (selectedFerrersPreAnchorSolution4 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.2 hθabs4
  exact etw5_pkt_deriv_bound k M0 M4 hM0nn hM4nn hM0 hM4

/-! ### S3b: packet value bound, representative bound, measurability -/

/-- The normalized mode is globally dominated by the coefficient `ℓ¹` mass
over the normalization. -/
private theorem etw6_mode_bound
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ)
    (hm : 2 ≤ mP) (y : ℝ) :
    ‖S.normalizedPhysicalMode y‖ ≤
      (∑' q : ℕ, |S.coefficients q|) / S.physicalL2Normalization := by
  have hN : 0 < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hS1nn : (0 : ℝ) ≤ ∑' q : ℕ, |S.coefficients q| :=
    tsum_nonneg fun q => abs_nonneg _
  have hz : ‖S.physicalZeroExtension y‖ ≤
      ∑' q : ℕ, |S.coefficients q| := by
    rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension]
    rw [Set.indicator_apply]
    split_ifs with hmem
    · have hcast : mode4PhysicalFerrersSeriesComplex mP S.coefficients y =
          ((mode4PhysicalFerrersSeries mP S.coefficients y : ℝ) : ℂ) := rfl
      rw [hcast, Complex.norm_real, Real.norm_eq_abs]
      have hphys : mode4PhysicalFerrersSeries mP S.coefficients y =
          mode4FerrersSeries S.coefficients (y / Real.sqrt mP) := rfl
      rw [hphys]
      apply etw5_series_le_l1 S
      have hlam0 : (0 : ℝ) < Real.sqrt mP := by
        apply Real.sqrt_pos.2
        have : (0 : ℕ) < mP := by omega
        exact_mod_cast this
      constructor
      · rw [neg_le, ← neg_div]
        apply div_le_of_le_mul₀ hlam0.le (by norm_num)
        have := hmem.1
        nlinarith
      · apply div_le_of_le_mul₀ hlam0.le (by norm_num)
        have := hmem.2
        nlinarith
    · simp [hS1nn]
  have hmode : S.normalizedPhysicalMode y =
      S.physicalZeroExtension y / (S.physicalL2Normalization : ℂ) := rfl
  rw [hmode, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hN]
  gcongr

/-- Global packet value bound. -/
private theorem etw6_pkt_bound (k : ℕ) :
    ∃ Bp : ℝ, 0 ≤ Bp ∧ ∀ y : ℝ,
      ‖selectedFerrersLemma73SourcePacket k y‖ ≤ Bp := by
  obtain ⟨-, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  set B0 : ℝ := (∑' q : ℕ,
      |(selectedFerrersPreAnchorSolution0 k).coefficients q|) /
    (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization with hB0
  set B4 : ℝ := (∑' q : ℕ,
      |(selectedFerrersPreAnchorSolution4 k).coefficients q|) /
    (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization with hB4
  have hB0nn : 0 ≤ B0 := by
    rw [hB0]
    apply div_nonneg (tsum_nonneg fun q => abs_nonneg _)
    exact ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization_pos
      (by omega)).le
  have hB4nn : 0 ≤ B4 := by
    rw [hB4]
    apply div_nonneg (tsum_nonneg fun q => abs_nonneg _)
    exact ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization_pos
      (by omega)).le
  refine ⟨‖selectedFerrersLemma73SourceScale k‖ /
    ‖((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)‖ *
      (|(selectedFerrersPreAnchorPair k).I4| * B0 +
        |(selectedFerrersPreAnchorPair k).I0| * B4), by positivity, ?_⟩
  intro y
  have hb0 : ‖(selectedFerrersPreAnchorPair k).h0 y‖ ≤ B0 := by
    rw [hh0, hB0]
    exact etw6_mode_bound (selectedFerrersPreAnchorSolution0 k) (by omega) y
  have hb4 : ‖(selectedFerrersPreAnchorPair k).h4 y‖ ≤ B4 := by
    rw [hh4, hB4]
    exact etw6_mode_bound (selectedFerrersPreAnchorSolution4 k) (by omega) y
  have hpkt : selectedFerrersLemma73SourcePacket k y =
      selectedFerrersLemma73SourceScale k *
        ((((selectedFerrersPreAnchorPair k).I4 : ℂ) *
            (selectedFerrersPreAnchorPair k).h0 y -
          ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
            (selectedFerrersPreAnchorPair k).h4 y) /
          ((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)) :=
    rfl
  rw [hpkt, norm_mul, norm_div]
  have hnum : ‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
      (selectedFerrersPreAnchorPair k).h0 y -
      ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
      (selectedFerrersPreAnchorPair k).h4 y‖ ≤
      |(selectedFerrersPreAnchorPair k).I4| * B0 +
        |(selectedFerrersPreAnchorPair k).I0| * B4 := by
    calc ‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
        (selectedFerrersPreAnchorPair k).h0 y -
        ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
        (selectedFerrersPreAnchorPair k).h4 y‖ ≤
        ‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
          (selectedFerrersPreAnchorPair k).h0 y‖ +
        ‖((selectedFerrersPreAnchorPair k).I0 : ℂ) *
          (selectedFerrersPreAnchorPair k).h4 y‖ := norm_sub_le _ _
      _ = |(selectedFerrersPreAnchorPair k).I4| *
            ‖(selectedFerrersPreAnchorPair k).h0 y‖ +
          |(selectedFerrersPreAnchorPair k).I0| *
            ‖(selectedFerrersPreAnchorPair k).h4 y‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs]
      _ ≤ |(selectedFerrersPreAnchorPair k).I4| * B0 +
          |(selectedFerrersPreAnchorPair k).I0| * B4 := by
          gcongr
  by_cases hden : ‖((selectedFerrersPreAnchorPair
      k).normalizingDenominator : ℂ)‖ = 0
  · rw [hden, div_zero, mul_zero]
    positivity
  · have hdpos : 0 < ‖((selectedFerrersPreAnchorPair
        k).normalizingDenominator : ℂ)‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hden)
    calc ‖selectedFerrersLemma73SourceScale k‖ *
        (‖((selectedFerrersPreAnchorPair k).I4 : ℂ) *
            (selectedFerrersPreAnchorPair k).h0 y -
          ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
            (selectedFerrersPreAnchorPair k).h4 y‖ /
          ‖((selectedFerrersPreAnchorPair k).normalizingDenominator :
            ℂ)‖) ≤
        ‖selectedFerrersLemma73SourceScale k‖ *
          ((|(selectedFerrersPreAnchorPair k).I4| * B0 +
            |(selectedFerrersPreAnchorPair k).I0| * B4) /
          ‖((selectedFerrersPreAnchorPair k).normalizingDenominator :
            ℂ)‖) := by
          gcongr
      _ = ‖selectedFerrersLemma73SourceScale k‖ /
          ‖((selectedFerrersPreAnchorPair k).normalizingDenominator : ℂ)‖ *
          (|(selectedFerrersPreAnchorPair k).I4| * B0 +
            |(selectedFerrersPreAnchorPair k).I0| * B4) := by
          ring

/-- The physical series is continuous on the open window (it agrees with the
normalization multiple of the differentiable normalized mode there). -/
private theorem etw6_seriesC_contOn
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ) (hm : 2 ≤ mP) :
    ContinuousOn (mode4PhysicalFerrersSeriesComplex mP S.coefficients)
      (Set.Ioo (-(Real.sqrt mP)) (Real.sqrt mP)) := by
  have hmode : ContinuousOn S.normalizedPhysicalMode
      (Set.Ioo (-(Real.sqrt mP)) (Real.sqrt mP)) := by
    intro y hy
    exact ((normalizedPhysicalMode_hasDerivAt S hm
      hy).continuousAt).continuousWithinAt
  have hcont : ContinuousOn
      (fun y => (S.physicalL2Normalization : ℂ) *
        S.normalizedPhysicalMode y)
      (Set.Ioo (-(Real.sqrt mP)) (Real.sqrt mP)) :=
    continuousOn_const.mul hmode
  apply hcont.congr
  intro y hy
  have hNpos : (0 : ℝ) < S.physicalL2Normalization :=
    S.physicalL2Normalization_pos hm
  have hNne : ((S.physicalL2Normalization : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast hNpos.ne'
  have hmem : y ∈ Set.Icc (-(Real.sqrt mP)) (Real.sqrt mP) :=
    ⟨hy.1.le, hy.2.le⟩
  have hz : S.physicalZeroExtension y =
      mode4PhysicalFerrersSeriesComplex mP S.coefficients y := by
    rw [Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension,
      Set.indicator_of_mem hmem]
  have hnm : S.normalizedPhysicalMode y =
      S.physicalZeroExtension y / (S.physicalL2Normalization : ℂ) := rfl
  show mode4PhysicalFerrersSeriesComplex mP S.coefficients y =
    (S.physicalL2Normalization : ℂ) * S.normalizedPhysicalMode y
  rw [hnm, hz]
  field_simp

/-- Almost-everywhere strong measurability of the packet along an
exponential ray `x ↦ pkt (c e^x)` with `c > 0`. -/
private theorem etw6_pkt_comp_asm (k : ℕ) (c : ℝ) (hc : 0 < c) :
    AEStronglyMeasurable
      (fun x : ℝ => selectedFerrersLemma73SourcePacket k
        (c * Real.exp x)) volume := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  set lam : ℝ := Real.sqrt ((k + 2 : ℕ) : ℝ) with hlamdef
  have hlampos : 0 < lam := by
    rw [hlamdef]
    apply Real.sqrt_pos.2
    positivity
  set ψ : ℝ → ℝ := fun x => c * Real.exp x with hψdef
  have hψc : Continuous ψ := by
    rw [hψdef]
    fun_prop
  have hψpos : ∀ x, 0 < ψ x := fun x => by
    rw [hψdef]
    positivity
  have hψinj : Function.Injective ψ := by
    intro a b hab
    rw [hψdef] at hab
    simp only [mul_eq_mul_left_iff] at hab
    rcases hab with h | h
    · exact Real.exp_injective h
    · exact absurd h hc.ne'
  set U : Set ℝ := ψ ⁻¹' (Set.Ioo (-lam) lam) with hUdef
  have hUopen : IsOpen U := isOpen_Ioo.preimage hψc
  have hbadnull : volume (ψ ⁻¹' {lam}) = 0 := by
    apply Set.Subsingleton.measure_zero
    intro a ha b hb
    exact hψinj (ha.trans hb.symm)
  -- one normalized mode along the ray
  have hmodecomp : ∀ {mM KM : ℕ} {ΛM : ℝ}
      (S : Mode4FerrersRegularEvenProlateSolution mM KM ΛM),
      2 ≤ mM → mM = k + 2 →
      AEStronglyMeasurable
        (fun x : ℝ => S.normalizedPhysicalMode (ψ x)) volume := by
    intro mM KM ΛM S hm hmk
    subst hmk
    have hindEq : (fun x : ℝ => S.normalizedPhysicalMode (ψ x)) =ᶠ[ae volume]
        (fun x : ℝ => U.indicator
          (fun z => mode4PhysicalFerrersSeriesComplex (k + 2)
            S.coefficients (ψ z)) x /
          (S.physicalL2Normalization : ℂ)) := by
      have hae : ∀ᵐ x ∂volume, x ∉ ψ ⁻¹' {lam} :=
        (MeasureTheory.measure_eq_zero_iff_ae_notMem).1 hbadnull
      filter_upwards [hae] with x hx
      have hnm : S.normalizedPhysicalMode (ψ x) =
          S.physicalZeroExtension (ψ x) /
            (S.physicalL2Normalization : ℂ) := rfl
      rw [hnm, Mode4FerrersRegularEvenProlateSolution.physicalZeroExtension]
      congr 1
      by_cases hmem : ψ x ∈ Set.Ioo (-lam) lam
      · have hIcc : ψ x ∈ Set.Icc (-lam) lam := ⟨hmem.1.le, hmem.2.le⟩
        have hU : x ∈ U := hmem
        rw [Set.indicator_of_mem hIcc, Set.indicator_of_mem hU]
      · have hU : x ∉ U := hmem
        rw [Set.indicator_of_notMem hU, Set.indicator_apply]
        split_ifs with hIcc
        · exfalso
          have h1 : -lam < ψ x :=
            lt_of_lt_of_le (neg_lt_zero.2 hlampos) (hψpos x).le
          have h2 : ψ x ≠ lam := fun h =>
            hx (Set.mem_preimage.2 (Set.mem_singleton_iff.2 h))
          exact hmem ⟨h1, lt_of_le_of_ne hIcc.2 h2⟩
        · rfl
    apply AEStronglyMeasurable.congr _ hindEq.symm
    simp only [div_eq_mul_inv]
    apply AEStronglyMeasurable.mul_const
    rw [aestronglyMeasurable_indicator_iff hUopen.measurableSet]
    apply ContinuousOn.aestronglyMeasurable _ hUopen.measurableSet
    apply ContinuousOn.comp (etw6_seriesC_contOn S hm)
      hψc.continuousOn
    exact fun x hx => hx
  have h0asm := hmodecomp (selectedFerrersPreAnchorSolution0 k)
    (by omega) rfl
  have h4asm := hmodecomp (selectedFerrersPreAnchorSolution4 k)
    (by omega) rfl
  have hpkt : (fun x : ℝ => selectedFerrersLemma73SourcePacket k
      (c * Real.exp x)) =
      fun x : ℝ => selectedFerrersLemma73SourceScale k *
        ((((selectedFerrersPreAnchorPair k).I4 : ℂ) *
            (selectedFerrersPreAnchorPair k).h0 (ψ x) -
          ((selectedFerrersPreAnchorPair k).I0 : ℂ) *
            (selectedFerrersPreAnchorPair k).h4 (ψ x)) /
          ((selectedFerrersPreAnchorPair k).normalizingDenominator :
            ℂ)) := rfl
  rw [hpkt]
  apply AEStronglyMeasurable.const_mul
  simp only [div_eq_mul_inv]
  apply AEStronglyMeasurable.mul_const
  apply AEStronglyMeasurable.sub
  · apply AEStronglyMeasurable.const_mul
    rw [show (fun x : ℝ => (selectedFerrersPreAnchorPair k).h0 (ψ x)) =
      fun x : ℝ => (selectedFerrersPreAnchorSolution0
        k).normalizedPhysicalMode (ψ x) by
      funext x; rw [hh0]]
    exact h0asm
  · apply AEStronglyMeasurable.const_mul
    rw [show (fun x : ℝ => (selectedFerrersPreAnchorPair k).h4 (ψ x)) =
      fun x : ℝ => (selectedFerrersPreAnchorSolution4
        k).normalizedPhysicalMode (ψ x) by
      funext x; rw [hh4]]
    exact h4asm

/-- The additive-log window coordinate stays at most `√(k+2)`. -/
private theorem etw6_u_le (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k))) :
    Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k) ≤
      Real.sqrt ((k + 2 : ℕ) : ℝ) := by
  have hL : L_m (selectedFerrersPreAnchorIndex k) =
      Real.log ((k + 2 : ℕ) : ℝ) := rfl
  have hmpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  have hexp : Real.exp x ≤ ((k + 2 : ℕ) : ℝ) := by
    calc Real.exp x ≤ Real.exp (L_m (selectedFerrersPreAnchorIndex k)) :=
        Real.exp_le_exp.2 hx.2
      _ = ((k + 2 : ℕ) : ℝ) := by
          rw [hL, Real.exp_log hmpos]
  rw [etw5_lambda_m_eq k, div_le_iff₀ (Real.sqrt_pos.2 hmpos)]
  calc Real.exp x ≤ ((k + 2 : ℕ) : ℝ) := hexp
    _ = Real.sqrt ((k + 2 : ℕ) : ℝ) * Real.sqrt ((k + 2 : ℕ) : ℝ) :=
        (Real.mul_self_sqrt hmpos.le).symm

/-- Value bound for the representative on the closed log window. -/
private theorem etw6_rep_bound (k : ℕ) (Bp : ℝ) (hBp : 0 ≤ Bp)
    (hpkt : ∀ y : ℝ, ‖selectedFerrersLemma73SourcePacket k y‖ ≤ Bp) :
    ∀ x ∈ Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)),
      ‖selectedFerrersAbelLogRepresentative k x‖ ≤
        Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) * Bp *
          (((sourcePositiveIndexFinset
            (selectedFerrersPreAnchorIndex k)).card : ℝ) + 1) := by
  intro x hx
  rw [etw_rep_eq_finite k hx]
  set u : ℝ := Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)
    with hudef
  have hu0 : 0 ≤ u := by
    rw [hudef, etw5_lambda_m_eq k]
    positivity
  have hule : u ≤ Real.sqrt ((k + 2 : ℕ) : ℝ) := etw6_u_le k hx
  have hsqrtu : Real.sqrt u ≤ Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) :=
    Real.sqrt_le_sqrt hule
  have hsqrtu0 : 0 ≤ Real.sqrt u := Real.sqrt_nonneg _
  have hEcore : ‖finiteEStarCore
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k) u‖ ≤
      ((sourcePositiveIndexFinset
        (selectedFerrersPreAnchorIndex k)).card : ℝ) * Bp := by
    calc ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
        selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u)‖ ≤
        ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
          ‖selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) * u)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ sourcePositiveIndexFinset
            (selectedFerrersPreAnchorIndex k), Bp :=
        Finset.sum_le_sum fun n _ => hpkt _
      _ = ((sourcePositiveIndexFinset
          (selectedFerrersPreAnchorIndex k)).card : ℝ) * Bp := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hEstar : finiteEStar
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k) u =
      ((Real.sqrt u : ℝ) : ℂ) * finiteEStarCore
        (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
        (selectedFerrersLemma73SourcePacket k) u := rfl
  calc ‖(finiteEStar
      (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k) u +
      (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        ((Real.sqrt u : ℝ) : ℂ))‖ ≤
      ‖(finiteEStar
        (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
        (selectedFerrersLemma73SourcePacket k) u)‖ +
      ‖((1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
        ((Real.sqrt u : ℝ) : ℂ))‖ := norm_add_le _ _
    _ ≤ Real.sqrt u * (((sourcePositiveIndexFinset
          (selectedFerrersPreAnchorIndex k)).card : ℝ) * Bp) +
        (1 / 2) * Bp * Real.sqrt u := by
        apply add_le_add
        · rw [hEstar, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hsqrtu0]
          exact mul_le_mul_of_nonneg_left hEcore hsqrtu0
        · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hsqrtu0]
          have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
            rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
              Complex.norm_real, Real.norm_eq_abs]
            norm_num
          rw [hhalf]
          have := hpkt 0
          nlinarith [hsqrtu0, norm_nonneg
            (selectedFerrersLemma73SourcePacket k 0)]
    _ ≤ Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) * Bp *
        (((sourcePositiveIndexFinset
          (selectedFerrersPreAnchorIndex k)).card : ℝ) + 1) := by
        have hcard : (0 : ℝ) ≤ ((sourcePositiveIndexFinset
          (selectedFerrersPreAnchorIndex k)).card : ℝ) := by positivity
        have h1 := mul_le_mul_of_nonneg_right hsqrtu
          (mul_nonneg hcard hBp)
        have h2 := mul_le_mul_of_nonneg_left hsqrtu
          (by positivity : (0 : ℝ) ≤ 1 / 2 * Bp)
        have h3 : (0 : ℝ) ≤ Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) * Bp :=
          mul_nonneg (Real.sqrt_nonneg _) hBp
        nlinarith [h1, h2, h3]

/-- Beyond the window the packet derivative vanishes. -/
private theorem etw6_pkt_deriv_zero_of_gt (k : ℕ) {y : ℝ}
    (hy : lambda_m (selectedFerrersPreAnchorIndex k) < y) :
    deriv (selectedFerrersLemma73SourcePacket k) y = 0 := by
  have hzero : selectedFerrersLemma73SourcePacket k =ᶠ[nhds y]
      (fun _ : ℝ => (0 : ℂ)) := by
    have hylam : (selectedFerrersPreAnchorPair k).pw.lambda < y := by
      rw [selectedFerrersPreAnchorPair_lambda_eq k]
      exact hy
    filter_upwards [isOpen_Ioi.mem_nhds hylam] with z hz
    apply etw_packet_zero_outside k z
    intro hmem
    exact absurd hmem.2 (not_le.mpr hz)
  rw [hzero.deriv_eq, deriv_const]

/-- Almost every log coordinate avoids every positive seam. -/
private theorem etw6_ae_no_seam (k : ℕ) :
    ∀ᵐ x : ℝ ∂volume, ∀ n : ℕ+,
      ((n : ℕ) : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠
      lambda_m (selectedFerrersPreAnchorIndex k) := by
  have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
    rw [etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  have hnull : volume (⋃ n : ℕ+, {x : ℝ |
      ((n : ℕ) : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) =
      lambda_m (selectedFerrersPreAnchorIndex k)}) = 0 := by
    apply MeasureTheory.measure_iUnion_null
    intro n
    apply Set.Subsingleton.measure_zero
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb
    have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have hexp : Real.exp a = Real.exp b := by
      have h1 : Real.exp a =
          lambda_m (selectedFerrersPreAnchorIndex k) *
            lambda_m (selectedFerrersPreAnchorIndex k) / ((n : ℕ) : ℝ) := by
        field_simp at ha ⊢
        nlinarith [ha]
      have h2 : Real.exp b =
          lambda_m (selectedFerrersPreAnchorIndex k) *
            lambda_m (selectedFerrersPreAnchorIndex k) / ((n : ℕ) : ℝ) := by
        field_simp at hb ⊢
        nlinarith [hb]
      rw [h1, h2]
    exact Real.exp_injective hexp
  have hsub := MeasureTheory.measure_eq_zero_iff_ae_notMem.1 hnull
  filter_upwards [hsub] with x hx n
  intro hcontra
  apply hx
  exact Set.mem_iUnion.2 ⟨n, hcontra⟩

/-- The representative is a.e.-strongly measurable on the log interval. -/
private theorem etw6_rep_asm (k : ℕ) :
    AEStronglyMeasurable (selectedFerrersAbelLogRepresentative k)
      (volume.restrict
        (Set.Ioc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))) := by
  have hlam : 0 < lambda_m (selectedFerrersPreAnchorIndex k) := by
    rw [etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set F : ℝ → ℂ := fun x =>
    finiteEStar (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
      (selectedFerrersLemma73SourcePacket k)
      (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) +
    (1 / 2 : ℂ) * selectedFerrersLemma73SourcePacket k 0 *
      ((Real.sqrt
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) : ℝ) : ℂ)
    with hFdef
  have hFasm : AEStronglyMeasurable F volume := by
    rw [hFdef]
    apply AEStronglyMeasurable.add
    · have hcore : AEStronglyMeasurable (fun x : ℝ =>
          ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
              (Real.exp x /
                lambda_m (selectedFerrersPreAnchorIndex k)))) volume := by
        have := Finset.aestronglyMeasurable_sum
          (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
          (f := fun (n : ℕ+) (x : ℝ) =>
            selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
              (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))))
          (fun n _ => by
            have heq : (fun x : ℝ =>
                selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
                  (Real.exp x /
                    lambda_m (selectedFerrersPreAnchorIndex k)))) =
                fun x : ℝ =>
                  selectedFerrersLemma73SourcePacket k
                    ((((n : ℕ) : ℝ) /
                      lambda_m (selectedFerrersPreAnchorIndex k)) *
                      Real.exp x) := by
              funext x
              congr 1
              ring
            beta_reduce
            rw [heq]
            apply etw6_pkt_comp_asm
            have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
            positivity)
        have hsumeq : (fun x : ℝ =>
            ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
              selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))) =
            ∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
              fun x : ℝ =>
                selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
                  (Real.exp x /
                    lambda_m (selectedFerrersPreAnchorIndex k))) := by
          funext x
          simp [Finset.sum_apply]
        rw [hsumeq]
        exact this
      have hsqrt : Continuous (fun x : ℝ =>
          ((Real.sqrt (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) : ℝ) : ℂ)) := by
        fun_prop
      have hfes : (fun x : ℝ =>
          finiteEStar
            (sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k))
            (selectedFerrersLemma73SourcePacket k)
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) =
          fun x : ℝ =>
            ((Real.sqrt (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) : ℝ) : ℂ) *
            ∑ n ∈ sourcePositiveIndexFinset
              (selectedFerrersPreAnchorIndex k),
              selectedFerrersLemma73SourcePacket k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k))) := rfl
      rw [hfes]
      exact hsqrt.aestronglyMeasurable.mul hcore
    · apply AEStronglyMeasurable.const_mul
      apply Continuous.aestronglyMeasurable
      fun_prop
  apply AEStronglyMeasurable.congr (hFasm.restrict)
  have hL0 : (0 : ℝ) ≤ L_m (selectedFerrersPreAnchorIndex k) :=
    (logLength_pos (selectedFerrersPreAnchorIndex k)).le
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
    with x hx
  rw [etw_rep_eq_finite k ⟨hx.1.le, hx.2⟩]

/-- **The discharged reduction**: with global packet value/derivative bounds
in hand, both integrability hypotheses of the copied reduction hold, so the
derivative budget is at most the exact majorant integral. -/
private theorem etw7_budget_reduced (k : ℕ) (Bp P : ℝ)
    (hBp : 0 ≤ Bp) (hP : 0 ≤ P)
    (hpkt : ∀ y : ℝ, ‖selectedFerrersLemma73SourcePacket k y‖ ≤ Bp)
    (hder : ∀ y : ℝ, 0 < y →
      y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
      ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P) :
    selectedFerrersAbelLogDerivativeBudget k ≤
      ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        ((1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
          Real.sqrt (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) *
            ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
              etw_Q k (((n : ℕ) : ℝ) *
                (Real.exp x /
                  lambda_m (selectedFerrersPreAnchorIndex k)))‖) := by
  set i := selectedFerrersPreAnchorIndex k with hidef
  set lam : ℝ := lambda_m i with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, hidef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set L : ℝ := L_m i with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos i).le
  set card : ℝ := ((sourcePositiveIndexFinset i).card : ℝ) with hcarddef
  have hcard0 : 0 ≤ card := by rw [hcarddef]; positivity
  set s4 : ℝ := Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) with hs4def
  have hs40 : 0 ≤ s4 := Real.sqrt_nonneg _
  set R : ℝ := s4 * Bp * (card + 1) with hRdef
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  set C2 : ℝ := s4 * (card * (lam * P)) with hC2def
  have hC20 : 0 ≤ C2 := by
    rw [hC2def]
    have := hlam.le
    positivity
  -- measurability of the Q-comb part
  have hu_cont : Continuous (fun x : ℝ => Real.exp x / lam) := by
    fun_prop
  have hQm : ∀ n : ℕ+, Measurable (fun x : ℝ =>
      etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))) := by
    intro n
    have harg : Measurable (fun x : ℝ =>
        ((n : ℕ) : ℝ) * (Real.exp x / lam)) :=
      (continuous_const.mul hu_cont).measurable
    have h1 : Measurable (fun x : ℝ =>
        ((((n : ℕ) : ℝ) * (Real.exp x / lam) : ℝ) : ℂ)) :=
      Complex.measurable_ofReal.comp harg
    have h2 : Measurable (fun x : ℝ =>
        deriv (selectedFerrersLemma73SourcePacket k)
          (((n : ℕ) : ℝ) * (Real.exp x / lam))) :=
      (measurable_deriv _).comp harg
    exact h1.mul h2
  have hp2m : Measurable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lam) *
        ‖∑ n ∈ sourcePositiveIndexFinset i,
          etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖) := by
    apply Measurable.mul
    · exact (Real.continuous_sqrt.comp hu_cont).measurable
    · apply Measurable.norm
      exact Finset.measurable_sum _ fun n _ => hQm n
  -- a.e. bound on the Q-comb part
  have hqsum_bound : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) L →
      (∀ n : ℕ+, ((n : ℕ) : ℝ) * (Real.exp x / lam) ≠ lam) →
      ‖∑ n ∈ sourcePositiveIndexFinset i,
        etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤
        card * (lam * P) := by
    intro x hx hns
    have hupos : 0 < Real.exp x / lam := by positivity
    calc ‖∑ n ∈ sourcePositiveIndexFinset i,
        etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤
        ∑ n ∈ sourcePositiveIndexFinset i,
          ‖etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ sourcePositiveIndexFinset i, lam * P := by
        apply Finset.sum_le_sum
        intro n _
        set y : ℝ := ((n : ℕ) : ℝ) * (Real.exp x / lam) with hydef
        have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
        have hy0 : 0 < y := by rw [hydef]; positivity
        have hyne : y ≠ lam := hns n
        have hQval : etw_Q k y = ((y : ℝ) : ℂ) *
            deriv (selectedFerrersLemma73SourcePacket k) y := rfl
        rw [hQval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hy0]
        rcases le_or_gt y lam with hylt | hygt
        · exact mul_le_mul hylt (hder y hy0 hyne) (norm_nonneg _) hlam.le
        · rw [etw6_pkt_deriv_zero_of_gt k hygt, norm_zero, mul_zero]
          positivity
      _ = card * (lam * P) := by
        rw [Finset.sum_const, nsmul_eq_mul]
  have hsqrtu_le : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) L →
      Real.sqrt (Real.exp x / lam) ≤ s4 := by
    intro x hx
    rw [hs4def]
    apply Real.sqrt_le_sqrt
    exact etw6_u_le k ⟨hx.1.le, hx.2⟩
  -- the two integrability certificates
  have hint : IntervalIntegrable
      (fun x : ℝ =>
        (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
        Real.sqrt (Real.exp x / lam) *
          ‖∑ n ∈ sourcePositiveIndexFinset i,
            etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖)
      MeasureTheory.volume 0 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const ((1 / 2) * R + C2))
    · apply AEStronglyMeasurable.add
      · exact ((etw6_rep_asm k).norm).const_mul _
      · exact hp2m.aestronglyMeasurable.restrict
    · have hae : ∀ᵐ x : ℝ
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) L)),
          ∀ n : ℕ+, ((n : ℕ) : ℝ) * (Real.exp x / lam) ≠ lam :=
        (etw6_ae_no_seam k).filter_mono
          (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        hae] with x hx hnoseam
      have hp1 : (1 / 2 : ℝ) *
          ‖selectedFerrersAbelLogRepresentative k x‖ ≤ (1 / 2) * R := by
        have := etw6_rep_bound k Bp hBp hpkt x ⟨hx.1.le, hx.2⟩
        rw [hRdef]
        linarith
      have hp2 : Real.sqrt (Real.exp x / lam) *
          ‖∑ n ∈ sourcePositiveIndexFinset i,
            etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤ C2 := by
        rw [hC2def]
        apply mul_le_mul (hsqrtu_le x hx) (hqsum_bound x hx hnoseam)
          (norm_nonneg _) hs40
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      linarith
  have hbudget : IntervalIntegrable
      (fun x : ℝ =>
        ‖deriv (selectedFerrersAbelLogRepresentative k) x‖)
      MeasureTheory.volume 0 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const ((1 / 2) * R + C2))
    · exact ((measurable_deriv _).norm.aestronglyMeasurable).restrict
    · have hae : ∀ᵐ x : ℝ
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) L)),
          ∀ n : ℕ+, ((n : ℕ) : ℝ) * (Real.exp x / lam) ≠ lam :=
        (etw6_ae_no_seam k).filter_mono
          (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
      have haeL : ∀ᵐ x : ℝ
          ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) L)),
          x ≠ L := by
        apply Filter.Eventually.filter_mono
          (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
        have hnull : MeasureTheory.volume ({L} : Set ℝ) = 0 :=
          MeasureTheory.measure_singleton L
        filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
          hnull] with x hx
        exact hx
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc,
        hae, haeL] with x hx hnoseam hxL
      have hxIoo : x ∈ Set.Ioo (0 : ℝ) L :=
        ⟨hx.1, lt_of_le_of_ne hx.2 hxL⟩
      have hd := (etw_hasDerivAt_of_no_seam k hxIoo hnoseam).deriv
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), hd]
      have hrepb := etw6_rep_bound k Bp hBp hpkt x ⟨hx.1.le, hx.2⟩
      calc ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x +
          ((Real.sqrt (Real.exp x / lam) : ℝ) : ℂ) *
            ∑ n ∈ sourcePositiveIndexFinset i,
              etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤
          ‖(1 / 2 : ℂ) * selectedFerrersAbelLogRepresentative k x‖ +
          ‖((Real.sqrt (Real.exp x / lam) : ℝ) : ℂ) *
            ∑ n ∈ sourcePositiveIndexFinset i,
              etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ :=
          norm_add_le _ _
        _ ≤ (1 / 2) * R + C2 := by
          apply add_le_add
          · rw [norm_mul]
            have hhalf : ‖(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
              rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num,
                Complex.norm_real, Real.norm_eq_abs]
              norm_num
            rw [hhalf, hRdef]
            nlinarith [hrepb, norm_nonneg
              (selectedFerrersAbelLogRepresentative k x)]
          · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
              abs_of_nonneg (Real.sqrt_nonneg _), hC2def]
            apply mul_le_mul (hsqrtu_le x hx)
              (hqsum_bound x hx hnoseam) (norm_nonneg _) hs40
  exact etw_budget_reduction k hint hbudget

/-! ### S3c: the exact comb split — explicit H part, non-top defect,
χ-junk and strict top -/

/-- Explicit derivative value of the real `H` profile. -/
private noncomputable def etw8_dH (y : ℝ) : ℝ :=
  (-(2 * Real.pi ^ 3) * y ^ 5 + 7 * Real.pi ^ 2 * y ^ 3 -
      3 * Real.pi * y) * Real.exp (-Real.pi * y ^ 2)

private theorem etw8_hbHRe_hasDerivAt (y : ℝ) :
    HasDerivAt hbHRe (etw8_dH y) y := by
  have hexp : HasDerivAt (fun t : ℝ => Real.exp (-Real.pi * t ^ 2))
      (-2 * Real.pi * y * Real.exp (-Real.pi * y ^ 2)) y := by
    have h1 : HasDerivAt (fun t : ℝ => -Real.pi * t ^ 2)
        (-Real.pi * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (-Real.pi))
    have h2 := (Real.hasDerivAt_exp (-Real.pi * y ^ 2)).comp y h1
    convert h2 using 1
    ring
  have hpoly : HasDerivAt (fun t : ℝ =>
      (Real.pi / 2) * t ^ 2 * (2 * Real.pi * t ^ 2 - 3))
      (Real.pi / 2 * (2 * y) * (2 * Real.pi * y ^ 2 - 3) +
        (Real.pi / 2) * y ^ 2 * (2 * Real.pi * (2 * y))) y := by
    have h1 : HasDerivAt (fun t : ℝ => (Real.pi / 2) * t ^ 2)
        (Real.pi / 2 * (2 * y)) y := by
      simpa using ((hasDerivAt_pow 2 y).const_mul (Real.pi / 2))
    have h2 : HasDerivAt (fun t : ℝ => 2 * Real.pi * t ^ 2 - 3)
        (2 * Real.pi * (2 * y)) y := by
      simpa using (((hasDerivAt_pow 2 y).const_mul
        (2 * Real.pi)).sub_const 3)
    exact h1.mul h2
  have hprod := hpoly.mul hexp
  have hfun : hbHRe = fun t : ℝ =>
      (Real.pi / 2) * t ^ 2 * (2 * Real.pi * t ^ 2 - 3) *
        Real.exp (-Real.pi * t ^ 2) := rfl
  rw [hfun]
  convert hprod using 1
  rw [etw8_dH]
  ring

/-- The complex `H` has the cast derivative. -/
private theorem etw8_H_hasDerivAt (y : ℝ) :
    HasDerivAt explicitCCMLimitH ((etw8_dH y : ℝ) : ℂ) y := by
  have hre := etw8_hbHRe_hasDerivAt y
  have hcast := hre.ofReal_comp
  apply hcast.congr_of_eventuallyEq
  filter_upwards [] with t
  rw [explicitCCMLimitH_eq_hbHRe]

/-- `hbG` at a nonzero point is the weighted `H`-derivative. -/
private theorem etw8_hbG_eq (y : ℝ) :
    (4 : ℝ) * y * etw8_dH y = hbG y := by
  rw [etw8_dH, hbG]
  ring

/-- ℕ⁺-comb equals the ℕ-comb over `Icc 1 (k+2)`. -/
private theorem etw8_comb_crosswalk (k : ℕ) (g : ℝ → ℂ) (u : ℝ) :
    (∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
      g (((n : ℕ) : ℝ) * u)) =
    ∑ n ∈ Finset.Icc 1 (k + 2), g ((n : ℝ) * u) := by
  have hidx : sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k) =
      Finset.Icc ⟨1, Nat.one_pos⟩
        ⟨(selectedFerrersPreAnchorIndex k).m,
          lt_of_lt_of_le Nat.zero_lt_two
            (selectedFerrersPreAnchorIndex k).hm⟩ := rfl
  rw [hidx]
  apply Finset.sum_nbij' (i := fun (n : ℕ+) => (n : ℕ))
    (j := fun (n : ℕ) => (⟨max n 1, by omega⟩ : ℕ+))
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    have h1 : (1 : ℕ+) ≤ a := ha.1
    have h2 := ha.2
    have hm : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
    constructor
    · exact_mod_cast h1
    · have h3 := (PNat.coe_le_coe _ _).2 h2
      simp only [PNat.mk_coe] at h3
      rw [hm] at h3
      exact h3
  · intro a ha
    simp only [Finset.mem_Icc] at ha ⊢
    have hm : (selectedFerrersPreAnchorIndex k).m = k + 2 := rfl
    constructor
    · exact PNat.one_le _
    · apply (PNat.coe_le_coe _ _).1
      simp only [PNat.mk_coe]
      rw [hm]
      omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    have h1 : 1 ≤ (a : ℕ) := a.one_le
    apply PNat.coe_injective
    simp only [PNat.mk_coe]
    omega
  · intro a ha
    simp only [Finset.mem_Icc] at ha
    simp only [PNat.mk_coe]
    omega
  · intro a ha
    rfl

/-- The cylinder split of the `H`-derivative:
`16·H' = ctW₄' − 3·ctW₀'`. -/
private theorem etw8_dH_cylinder (y : ℝ) :
    16 * etw8_dH y = ctW4d y - 3 * ctW0d y := by
  rw [etw8_dH, ctW4d, ctW0d]
  ring

/-- Real value of one anchored-mode derivative term on the open window. -/
private theorem etw8_anchored_deriv (k : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ))) :
    HasDerivAt (selectedFerrersLemma73SourcePacket k)
      ((1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution4 k).coefficients y /
            ((selectedFerrersPreAnchorSolution4
              k).physicalL2Normalization : ℂ))) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution0 k).coefficients y /
            ((selectedFerrersPreAnchorSolution0
              k).physicalL2Normalization : ℂ))))) y := by
  obtain ⟨hlam, hh0, hh4, -⟩ := selectedFerrersPreAnchorPair_spec k
  have hm : 2 ≤ k + 2 := by omega
  have hfun : selectedFerrersLemma73SourcePacket k = fun x : ℝ =>
      (1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x)) := by
    funext x
    exact selectedFerrersLemma73SourcePacket_eq_anchored_combination k x
  have hd4 : HasDerivAt (selectedFerrersPreAnchorPair k).h4
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y /
        ((selectedFerrersPreAnchorSolution4
          k).physicalL2Normalization : ℂ)) y := by
    rw [hh4]
    exact normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution4 k) hm hy
  have hd0 : HasDerivAt (selectedFerrersPreAnchorPair k).h0
      (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y /
        ((selectedFerrersPreAnchorSolution0
          k).physicalL2Normalization : ℂ)) y := by
    rw [hh0]
    exact normalizedPhysicalMode_hasDerivAt
      (selectedFerrersPreAnchorSolution0 k) hm hy
  rw [hfun]
  have hstep := (((hd4.const_mul (centerAnchorScalarFour k)).const_mul
      (((selectedFerrersPreAnchorPair k).chi0 : ℂ))).sub
    (((hd0.const_mul (centerAnchorScalarZero k)).const_mul
      (3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ)))))
  have hfinal := hstep.const_mul (1 / 4 : ℂ)
  convert hfinal using 1

/-- The pointwise defect derivative in χ-inclusive real components. -/
private theorem etw8_defect_deriv (k : ℕ) {y : ℝ}
    (hy : y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ))) :
    deriv (fun t : ℝ => selectedFerrersLemma73SourcePacket k t -
        (4 : ℂ) * explicitCCMLimitH t) y =
      (1 / 4 : ℂ) *
        (((etw4_gd4 k y : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
            ((ctW4d y : ℝ) : ℂ) -
        3 * (((etw4_gd0 k y : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
            ((ctW0d y : ℝ) : ℂ))) := by
  have hpkt := etw8_anchored_deriv k hy
  have hH : HasDerivAt (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t)
      ((4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)) y :=
    (etw8_H_hasDerivAt y).const_mul (4 : ℂ)
  have hsub : HasDerivAt (fun t : ℝ =>
      selectedFerrersLemma73SourcePacket k t -
        (4 : ℂ) * explicitCCMLimitH t)
      ((1 / 4 : ℂ) *
        (((selectedFerrersPreAnchorPair k).chi0 : ℂ) *
          (centerAnchorScalarFour k *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution4 k).coefficients y /
            ((selectedFerrersPreAnchorSolution4
              k).physicalL2Normalization : ℂ))) -
        3 * ((selectedFerrersPreAnchorPair k).chi2 : ℂ) *
          (centerAnchorScalarZero k *
            (mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
              (selectedFerrersPreAnchorSolution0 k).coefficients y /
            ((selectedFerrersPreAnchorSolution0
              k).physicalL2Normalization : ℂ)))) -
        (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)) y := hpkt.sub hH
  rw [hsub.deriv]
  -- anchors are real
  have ha4 : centerAnchorScalarFour k =
      (((centerAnchorScalarFour k).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [etw3_anchor4_im k]
  have ha0 : centerAnchorScalarZero k =
      (((centerAnchorScalarZero k).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [etw3_anchor0_im k]
  have h16 : ((etw8_dH y : ℝ) : ℂ) =
      (((ctW4d y - 3 * ctW0d y) / 16 : ℝ) : ℂ) := by
    have hre : etw8_dH y = (ctW4d y - 3 * ctW0d y) / 16 := by
      have := etw8_dH_cylinder y
      linarith
    rw [hre]
  rw [ha4, ha0, h16, etw4_gd4, etw4_gd0]
  have hcast4 : mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
      (selectedFerrersPreAnchorSolution4 k).coefficients y =
      ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y : ℝ) : ℂ) :=
    rfl
  have hcast0 : mode4PhysicalFerrersFirstDerivativeSeriesComplex (k + 2)
      (selectedFerrersPreAnchorSolution0 k).coefficients y =
      ((mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y : ℝ) : ℂ) :=
    rfl
  rw [hcast4, hcast0]
  have hN4 : ((selectedFerrersPreAnchorSolution4
      k).physicalL2Normalization : ℝ) ≠ 0 :=
    ((selectedFerrersPreAnchorSolution4 k).physicalL2Normalization_pos
      (by omega)).ne'
  have hN0 : ((selectedFerrersPreAnchorSolution0
      k).physicalL2Normalization : ℝ) ≠ 0 :=
    ((selectedFerrersPreAnchorSolution0 k).physicalL2Normalization_pos
      (by omega)).ne'
  push_cast
  field_simp
  ring

/-- **The master pointwise comb split.**  Off the seams the full weighted
`Q`-comb is dominated by the explicit `H`-comb, the two per-mode non-top
defect combs, the two χ-junk combs and the strict-top defect comb. -/
private theorem etw8_qcomb_split (k : ℕ) {x : ℝ}
    (hx : x ∈ Set.Ioc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))
    (hns : ∀ n : ℕ+, ((n : ℕ) : ℝ) *
      (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠
      lambda_m (selectedFerrersPreAnchorIndex k)) :
    ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
      etw_Q k (((n : ℕ) : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖ ≤
    |∑ n ∈ Finset.Icc 1 (Nat.floor
        (lambda_m (selectedFerrersPreAnchorIndex k) /
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))),
      hbG ((n : ℝ) *
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))| +
    ((1 / 4) * |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        lambda_m (selectedFerrersPreAnchorIndex k)),
      (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        etw4_gd4 k ((n : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))| +
    (3 / 4) * |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        lambda_m (selectedFerrersPreAnchorIndex k)),
      (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        etw4_gd0 k ((n : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))| +
    (1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| *
      |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        lambda_m (selectedFerrersPreAnchorIndex k)),
      (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        ctW4d ((n : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))| +
    (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| *
      |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        lambda_m (selectedFerrersPreAnchorIndex k)),
      (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        ctW0d ((n : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))|) +
    ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
          selectedFerrersPaperLambda k ∧
        selectedFerrersPaperLambda k <
          ((n : ℝ) + 1) * (Real.exp x / selectedFerrersPaperLambda k)),
      (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) : ℂ) *
        deriv (fun t => selectedFerrersLemma73SourcePacket k t -
          (4 : ℂ) * explicitCCMLimitH t)
          ((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k))‖ := by
  have hpaper : selectedFerrersPaperLambda k =
      lambda_m (selectedFerrersPreAnchorIndex k) := rfl
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set u : ℝ := Real.exp x / lam with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  have hu1 : 1 / lam < u := by
    rw [hudef]
    rw [div_lt_div_iff_of_pos_right hlam]
    calc (1 : ℝ) = Real.exp 0 := Real.exp_zero.symm
      _ < Real.exp x := Real.exp_lt_exp.2 hx.1
  have hlamsq : lam * lam = ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, etw5_lambda_m_eq k]
    exact Real.mul_self_sqrt (by positivity)
  -- step 1: ℕ⁺ → ℕ crosswalk
  rw [etw8_comb_crosswalk k (fun y => etw_Q k y) u]
  -- step 2: drop the vanishing beyond-window terms
  have hzero_beyond : ∀ n ∈ Finset.Icc 1 (k + 2),
      ¬((n : ℝ) * u < lam) → etw_Q k ((n : ℝ) * u) = 0 := by
    intro n hn hnot
    have hne : (n : ℝ) * u ≠ lam := by
      have hmem : n ∈ Finset.Icc 1 (k + 2) := hn
      simp only [Finset.mem_Icc] at hmem
      have := hns ⟨n, by omega⟩
      simpa using this
    have hgt : lam < (n : ℝ) * u := lt_of_le_of_ne (not_lt.1 hnot)
      (Ne.symm hne)
    have hQ : etw_Q k ((n : ℝ) * u) = (((n : ℝ) * u : ℝ) : ℂ) *
        deriv (selectedFerrersLemma73SourcePacket k) ((n : ℝ) * u) := rfl
    rw [hQ, etw6_pkt_deriv_zero_of_gt k hgt, mul_zero]
  rw [← Finset.sum_filter_of_ne (fun n hn hne => by
    by_contra hnot
    exact hne (hzero_beyond n hn hnot))]
  -- step 3: per-term H/defect split on the inside filter
  have hterm : ∀ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam),
      etw_Q k ((n : ℝ) * u) =
        ((hbG ((n : ℝ) * u) : ℝ) : ℂ) +
        (((n : ℝ) * u : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    set y : ℝ := (n : ℝ) * u with hydef
    have hn1 : 1 ≤ n := hn.1.1
    have hy0 : 0 < y := by
      rw [hydef]
      have : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      nlinarith
    have hylt : y < lam := hn.2
    have hyIoo : y ∈ Set.Ioo (-(selectedFerrersPreAnchorPair k).pw.lambda)
        (selectedFerrersPreAnchorPair k).pw.lambda := by
      rw [selectedFerrersPreAnchorPair_lambda_eq k]
      exact ⟨by linarith, hylt⟩
    have hpktDiff : DifferentiableAt ℝ
        (selectedFerrersLemma73SourcePacket k) y :=
      etw_packet_differentiableAt_of_mem_open k hyIoo
    have hHDiff : DifferentiableAt ℝ
        (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y :=
      ((etw8_H_hasDerivAt y).const_mul (4 : ℂ)).differentiableAt
    have hsub : deriv (fun t => selectedFerrersLemma73SourcePacket k t -
        (4 : ℂ) * explicitCCMLimitH t) y =
        deriv (selectedFerrersLemma73SourcePacket k) y -
          deriv (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y :=
      deriv_sub hpktDiff hHDiff
    have hHval : deriv (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y =
        (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ) :=
      ((etw8_H_hasDerivAt y).const_mul (4 : ℂ)).deriv
    have hQ : etw_Q k y = ((y : ℝ) : ℂ) *
        deriv (selectedFerrersLemma73SourcePacket k) y := rfl
    rw [hQ, hsub, hHval]
    have hbGcast : ((hbG y : ℝ) : ℂ) =
        ((y : ℝ) : ℂ) * ((4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)) := by
      rw [← etw8_hbG_eq y]
      push_cast
      ring
    rw [hbGcast]
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  -- step 4: the H part collapses to the committed floor comb
  have hHindex : (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam) =
      Finset.Icc 1 (Nat.floor (lam / u)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨h1, _⟩, hlt⟩
      refine ⟨h1, ?_⟩
      apply Nat.le_floor
      rw [le_div_iff₀ hu]
      exact hlt.le
    · rintro ⟨h1, hfl⟩
      have hle : (n : ℝ) ≤ lam / u := by
        have := Nat.floor_le (by positivity : (0 : ℝ) ≤ lam / u)
        have hcast : (n : ℝ) ≤ (Nat.floor (lam / u) : ℝ) := by
          exact_mod_cast hfl
        linarith
      have hnu_le : (n : ℝ) * u ≤ lam := by
        rw [← le_div_iff₀ hu]
        exact hle
      have hne : (n : ℝ) * u ≠ lam := by
        have := hns ⟨n, by omega⟩
        simpa using this
      have hnk : n ≤ k + 2 := by
        have h1' : (n : ℝ) * u < lam := lt_of_le_of_ne hnu_le hne
        have hlam_div : lam / u < lam * lam := by
          have h := div_lt_div_of_pos_left hlam
            (by positivity : (0 : ℝ) < 1 / lam) hu1
          have heq : lam / (1 / lam) = lam * lam := by
            field_simp
          rwa [heq] at h
        have : (n : ℝ) ≤ lam / u := hle
        have hreal : (n : ℝ) < lam * lam := lt_of_le_of_lt this hlam_div
        rw [hlamsq] at hreal
        exact_mod_cast hreal.le
      exact ⟨⟨h1, hnk⟩, lt_of_le_of_ne hnu_le hne⟩
  have hH_eq : (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam),
      ((hbG ((n : ℝ) * u) : ℝ) : ℂ)) =
      (((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
        hbG ((n : ℝ) * u) : ℝ)) : ℂ) := by
    rw [hHindex]
    push_cast
    rfl
  -- step 5: split the defect filter into non-top and strict-top
  have hfilter_split : (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam) =
      ((Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam)) ∪
      ((Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u)) := by
    rw [← Finset.filter_or]
    apply Finset.filter_congr
    intro n _
    constructor
    · intro hlt
      rcases le_or_gt (((n : ℝ) + 1) * u) lam with hle | hgt
      · exact Or.inl hle
      · exact Or.inr ⟨hlt, hgt⟩
    · intro h
      rcases h with hle | ⟨hlt, _⟩
      · have : (n : ℝ) * u < ((n : ℝ) + 1) * u := by nlinarith
        linarith
      · exact hlt
  have hdisj : Disjoint
      ((Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam))
      ((Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u)) := by
    apply Finset.disjoint_filter_filter'
    rw [disjoint_iff_inf_le]
    intro n hn
    simp only [Pi.inf_apply, inf_Prop_eq] at hn
    exact absurd hn.1 (not_le.2 hn.2.2)
  have hD_eq : (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam),
      (((n : ℝ) * u : ℝ) : ℂ) *
        deriv (fun t => selectedFerrersLemma73SourcePacket k t -
          (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u)) =
      (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
        (((n : ℝ) * u : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u)) +
      (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u),
        (((n : ℝ) * u : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u)) := by
    rw [hfilter_split, Finset.sum_union hdisj]
  rw [hH_eq, hD_eq]
  -- step 6: per-term defect expansion on the non-top band
  have hterm2 : ∀ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
      (((n : ℝ) * u : ℝ) : ℂ) *
        deriv (fun t => selectedFerrersLemma73SourcePacket k t -
          (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u) =
      (1 / 4 : ℂ) *
        ((((n : ℝ) * u * etw4_gd4 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
            (((n : ℝ) * u * ctW4d ((n : ℝ) * u) : ℝ) : ℂ) -
        3 * ((((n : ℝ) * u * etw4_gd0 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
            (((n : ℝ) * u * ctW0d ((n : ℝ) * u) : ℝ) : ℂ))) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : 1 ≤ n := hn.1.1
    have hnpos : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hy0 : 0 < (n : ℝ) * u := by nlinarith
    have hylt : (n : ℝ) * u < lam := by nlinarith [hn.2, hu]
    have hyIoo : (n : ℝ) * u ∈
        Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
          (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
      have hlam_eq : lam = Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        rw [hlamdef, etw5_lambda_m_eq k]
      rw [← hlam_eq]
      exact ⟨by linarith, hylt⟩
    rw [etw8_defect_deriv k hyIoo]
    push_cast
    ring
  rw [Finset.sum_congr rfl hterm2]
  -- linear rearrangement of the non-top defect comb
  have hlin : (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
      (1 / 4 : ℂ) *
        ((((n : ℝ) * u * etw4_gd4 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
            (((n : ℝ) * u * ctW4d ((n : ℝ) * u) : ℝ) : ℂ) -
        3 * ((((n : ℝ) * u * etw4_gd0 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
            (((n : ℝ) * u * ctW0d ((n : ℝ) * u) : ℝ) : ℂ)))) =
      (1 / 4 : ℂ) *
        (((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
          (n : ℝ) * u * etw4_gd4 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
            ((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
              (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
            (n : ℝ) * u * ctW4d ((n : ℝ) * u) : ℝ) : ℂ) -
        3 * (((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
          (n : ℝ) * u * etw4_gd0 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
            ((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
              (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
            (n : ℝ) * u * ctW0d ((n : ℝ) * u) : ℝ) : ℂ))) := by
    rw [← Finset.mul_sum]
    congr 1
    push_cast
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum]
  rw [hlin]
  -- step 7: triangle and final assembly
  have htri1 := norm_add_le
    ((((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
      hbG ((n : ℝ) * u) : ℝ)) : ℂ))
    ((1 / 4 : ℂ) *
        (((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
          (n : ℝ) * u * etw4_gd4 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
            ((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
              (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
            (n : ℝ) * u * ctW4d ((n : ℝ) * u) : ℝ) : ℂ) -
        3 * (((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
          (n : ℝ) * u * etw4_gd0 k ((n : ℝ) * u) : ℝ) : ℂ) +
          (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
            ((∑ n ∈ (Finset.Icc 1 (k + 2)).filter
              (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
            (n : ℝ) * u * ctW0d ((n : ℝ) * u) : ℝ) : ℂ))) +
      (∑ n ∈ (Finset.Icc 1 (k + 2)).filter
        (fun n : ℕ => (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u),
        (((n : ℝ) * u : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u)))
  set S4 : ℝ := ∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
    (n : ℝ) * u * etw4_gd4 k ((n : ℝ) * u) with hS4def
  set S0 : ℝ := ∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
    (n : ℝ) * u * etw4_gd0 k ((n : ℝ) * u) with hS0def
  set J4 : ℝ := ∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
    (n : ℝ) * u * ctW4d ((n : ℝ) * u) with hJ4def
  set J0 : ℝ := ∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => ((n : ℝ) + 1) * u ≤ lam),
    (n : ℝ) * u * ctW0d ((n : ℝ) * u) with hJ0def
  set Ctop : ℂ := ∑ n ∈ (Finset.Icc 1 (k + 2)).filter
      (fun n : ℕ => (n : ℝ) * u < lam ∧ lam < ((n : ℝ) + 1) * u),
    (((n : ℝ) * u : ℝ) : ℂ) *
      deriv (fun t => selectedFerrersLemma73SourcePacket k t -
        (4 : ℂ) * explicitCCMLimitH t) ((n : ℝ) * u) with hCtopdef
  set Bmid : ℂ := (1 / 4 : ℂ) *
      (((S4 : ℝ) : ℂ) +
        (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
          ((J4 : ℝ) : ℂ) -
      3 * (((S0 : ℝ) : ℂ) +
        (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
          ((J0 : ℝ) : ℂ))) with hBmiddef
  have hAeq : ‖(((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
      hbG ((n : ℝ) * u) : ℝ)) : ℂ)‖ =
      |∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)), hbG ((n : ℝ) * u)| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hZinner : ((S4 : ℝ) : ℂ) +
      (((selectedFerrersPreAnchorPair k).chi0 - 1 : ℝ) : ℂ) *
        ((J4 : ℝ) : ℂ) -
      3 * (((S0 : ℝ) : ℂ) +
        (((selectedFerrersPreAnchorPair k).chi2 - 1 : ℝ) : ℂ) *
          ((J0 : ℝ) : ℂ)) =
      (((S4 + ((selectedFerrersPreAnchorPair k).chi0 - 1) * J4 -
        3 * (S0 + ((selectedFerrersPreAnchorPair k).chi2 - 1) * J0) :
          ℝ)) : ℂ) := by
    push_cast
    ring
  have hBle : ‖Bmid‖ ≤
      (1 / 4) * |S4| +
      (3 / 4) * |S0| +
      (1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| * |J4| +
      (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| * |J0| := by
    rw [hBmiddef, norm_mul, hZinner, Complex.norm_real, Real.norm_eq_abs]
    have hq : ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) := by
      rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num,
        Complex.norm_real, Real.norm_eq_abs]
      norm_num
    rw [hq]
    have habs : |S4 + ((selectedFerrersPreAnchorPair k).chi0 - 1) * J4 -
        3 * (S0 + ((selectedFerrersPreAnchorPair k).chi2 - 1) * J0)| ≤
        |S4| + |(selectedFerrersPreAnchorPair k).chi0 - 1| * |J4| +
        3 * (|S0| + |(selectedFerrersPreAnchorPair k).chi2 - 1| * |J0|) := by
      have htriangle : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := by
        intro a b
        calc |a - b| = |a + -b| := by ring_nf
          _ ≤ |a| + |-b| := abs_add_le _ _
          _ = |a| + |b| := by rw [abs_neg]
      have h1 := htriangle (S4 +
        ((selectedFerrersPreAnchorPair k).chi0 - 1) * J4)
        (3 * (S0 + ((selectedFerrersPreAnchorPair k).chi2 - 1) * J0))
      have h2 := abs_add_le S4
        (((selectedFerrersPreAnchorPair k).chi0 - 1) * J4)
      have h3 := abs_mul ((selectedFerrersPreAnchorPair k).chi0 - 1) J4
      have h4 := abs_mul (3 : ℝ)
        (S0 + ((selectedFerrersPreAnchorPair k).chi2 - 1) * J0)
      have h5 := abs_add_le S0
        (((selectedFerrersPreAnchorPair k).chi2 - 1) * J0)
      have h6 := abs_mul ((selectedFerrersPreAnchorPair k).chi2 - 1) J0
      have h7 : |(3 : ℝ)| = 3 := by norm_num
      rw [h3] at h2
      rw [h7] at h4
      rw [h6] at h5
      linarith [h1, h2, h4, h5]
    nlinarith [habs]
  calc ‖(((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
      hbG ((n : ℝ) * u) : ℝ)) : ℂ) + (Bmid + Ctop)‖ ≤
      ‖(((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
        hbG ((n : ℝ) * u) : ℝ)) : ℂ)‖ + ‖Bmid + Ctop‖ := norm_add_le _ _
    _ ≤ ‖(((∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)),
        hbG ((n : ℝ) * u) : ℝ)) : ℂ)‖ + (‖Bmid‖ + ‖Ctop‖) := by
        have := norm_add_le Bmid Ctop
        linarith
    _ ≤ |∑ n ∈ Finset.Icc 1 (Nat.floor (lam / u)), hbG ((n : ℝ) * u)| +
        (((1 / 4) * |S4| + (3 / 4) * |S0| +
          (1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| * |J4| +
          (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| * |J0|) +
          ‖Ctop‖) := by
        rw [hAeq]
        linarith [hBle]
    _ = _ := by
        have hCtop_eq : Ctop =
            ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
                (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
                  selectedFerrersPaperLambda k ∧
                selectedFerrersPaperLambda k <
                  ((n : ℝ) + 1) *
                    (Real.exp x / selectedFerrersPaperLambda k)),
              (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) :
                ℝ) : ℂ) *
                deriv (fun t => selectedFerrersLemma73SourcePacket k t -
                  (4 : ℂ) * explicitCCMLimitH t)
                  ((n : ℝ) *
                    (Real.exp x / selectedFerrersPaperLambda k)) := by
          rw [hCtopdef, hpaper]
        rw [hCtop_eq]
        ring

/-! ### S3d: absolute bounds for the fixed derivative profiles -/

/-- The damped modulus obeys `|y| e^{-π y²/2} ≤ 1`. -/
private theorem etw9_abs_gauss (y : ℝ) :
    |y| * Real.exp (-(Real.pi * y ^ 2) / 2) ≤ 1 := by
  have hexp := Real.add_one_le_exp (Real.pi * y ^ 2 / 2)
  have hpi := Real.pi_gt_three
  have hy : |y| ≤ 1 + Real.pi * y ^ 2 / 2 := by
    nlinarith [sq_abs y, sq_nonneg (|y| - 1), abs_nonneg y]
  have hpos := Real.exp_pos (Real.pi * y ^ 2 / 2)
  have hkey : |y| ≤ Real.exp (Real.pi * y ^ 2 / 2) :=
    le_trans hy (by linarith)
  have hrw : Real.exp (-(Real.pi * y ^ 2) / 2) =
      (Real.exp (Real.pi * y ^ 2 / 2))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hrw]
  rw [mul_inv_le_iff₀ hpos, one_mul]
  exact hkey

/-- Absolute bound for the mode-0 derivative profile. -/
private theorem etw9_K0 (y : ℝ) : |ctW0d y| ≤ 8 := by
  have h1 := etw9_abs_gauss y
  have h2 : Real.exp (-(Real.pi * y ^ 2) / 2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg y, Real.pi_pos.le]
  have hpi := Real.pi_le_four
  have hsplit : Real.exp (-Real.pi * y ^ 2) =
      Real.exp (-(Real.pi * y ^ 2) / 2) *
        Real.exp (-(Real.pi * y ^ 2) / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [ctW0d, abs_mul, abs_of_pos (Real.exp_pos _), hsplit]
  have habs : |(-2 : ℝ) * Real.pi * y| = 2 * Real.pi * |y| := by
    rw [abs_mul, abs_mul]
    simp [abs_of_pos Real.pi_pos]
  rw [habs]
  have hexp_nn : 0 ≤ Real.exp (-(Real.pi * y ^ 2) / 2) :=
    (Real.exp_pos _).le
  nlinarith [abs_nonneg y, Real.pi_pos.le, hexp_nn,
    mul_le_mul h1 h2 hexp_nn zero_le_one]

/-- Absolute bound for the mode-4 derivative profile. -/
private theorem etw9_K4 (y : ℝ) : |ctW4d y| ≤ 4056 := by
  have h1 := etw9_abs_gauss y
  have hpi3 : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  set u : ℝ := y ^ 2 with hudef
  have hu0 : 0 ≤ u := sq_nonneg y
  have hB : (32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u + 54 *
      Real.pi) * Real.exp (-(Real.pi * u) / 2) ≤ 4056 := by
    have ht1 := Real.add_one_le_exp (Real.pi * u / 4)
    have ht2 : Real.pi * u ≤ 4 * Real.exp (Real.pi * u / 4) := by
      nlinarith [Real.exp_pos (Real.pi * u / 4)]
    have ht3 : Real.pi ^ 2 * u ^ 2 ≤ 16 * Real.exp (Real.pi * u / 2) := by
      have hsq := mul_le_mul ht2 ht2 (by positivity) (by positivity)
      have hexp2 : Real.exp (Real.pi * u / 4) *
          Real.exp (Real.pi * u / 4) = Real.exp (Real.pi * u / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      nlinarith [hsq, hexp2]
    have hexp14 : Real.exp (Real.pi * u / 4) ≤
        Real.exp (Real.pi * u / 2) := by
      apply Real.exp_le_exp.2
      nlinarith
    have hone : (1 : ℝ) ≤ Real.exp (Real.pi * u / 2) := by
      rw [← Real.exp_zero]
      apply Real.exp_le_exp.2
      positivity
    have hexppos := Real.exp_pos (Real.pi * u / 2)
    have hexpinv : Real.exp (-(Real.pi * u) / 2) =
        (Real.exp (Real.pi * u / 2))⁻¹ := by
      rw [← Real.exp_neg]
      congr 1
      ring
    rw [hexpinv]
    rw [mul_inv_le_iff₀ hexppos]
    have hterm1 : 32 * Real.pi ^ 3 * u ^ 2 ≤
        2048 * Real.exp (Real.pi * u / 2) := by
      have := mul_le_mul_of_nonneg_left ht3
        (by positivity : (0 : ℝ) ≤ 32 * Real.pi)
      nlinarith [Real.exp_pos (Real.pi * u / 2)]
    have hterm2 : 112 * Real.pi ^ 2 * u ≤
        1792 * Real.exp (Real.pi * u / 2) := by
      have := mul_le_mul_of_nonneg_left ht2
        (by positivity : (0 : ℝ) ≤ 112 * Real.pi)
      nlinarith [hexp14, Real.exp_pos (Real.pi * u / 4)]
    have hterm3 : 54 * Real.pi ≤ 216 * Real.exp (Real.pi * u / 2) := by
      nlinarith [hone]
    linarith
  have hApart : |y| * Real.exp (-(Real.pi * u) / 2) ≤ 1 := by
    rw [hudef]
    exact etw9_abs_gauss y
  have hsplit : Real.exp (-Real.pi * y ^ 2) =
      Real.exp (-(Real.pi * u) / 2) * Real.exp (-(Real.pi * u) / 2) := by
    rw [← Real.exp_add, hudef]
    congr 1
    ring
  have hpoly : |(-32 * Real.pi ^ 3 * y ^ 5 + 112 * Real.pi ^ 2 * y ^ 3 -
      54 * Real.pi * y : ℝ)| ≤
      |y| * (32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u +
        54 * Real.pi) := by
    have hfact : (-32 * Real.pi ^ 3 * y ^ 5 + 112 * Real.pi ^ 2 * y ^ 3 -
        54 * Real.pi * y : ℝ) =
        y * (-32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u -
          54 * Real.pi) := by
      rw [hudef]
      ring
    rw [hfact, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg y)
    apply abs_le.2
    have hcube : (0 : ℝ) ≤ Real.pi ^ 3 * u ^ 2 :=
      mul_nonneg (pow_nonneg Real.pi_pos.le 3) (sq_nonneg u)
    constructor
    · nlinarith [hcube, hu0, hpi3]
    · nlinarith [hcube, hu0, hpi3]
  rw [ctW4d, abs_mul, abs_of_pos (Real.exp_pos _), hsplit]
  have hBnn : (0 : ℝ) ≤ 32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u +
      54 * Real.pi := by positivity
  have hexp_nn : 0 ≤ Real.exp (-(Real.pi * u) / 2) := (Real.exp_pos _).le
  calc |(-32 * Real.pi ^ 3 * y ^ 5 + 112 * Real.pi ^ 2 * y ^ 3 -
      54 * Real.pi * y : ℝ)| *
      (Real.exp (-(Real.pi * u) / 2) * Real.exp (-(Real.pi * u) / 2)) ≤
      (|y| * (32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u +
        54 * Real.pi)) *
      (Real.exp (-(Real.pi * u) / 2) * Real.exp (-(Real.pi * u) / 2)) := by
        apply mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = (|y| * Real.exp (-(Real.pi * u) / 2)) *
        ((32 * Real.pi ^ 3 * u ^ 2 + 112 * Real.pi ^ 2 * u +
          54 * Real.pi) * Real.exp (-(Real.pi * u) / 2)) := by ring
    _ ≤ 1 * 4056 := by
        apply mul_le_mul hApart hB (by positivity)
        norm_num
    _ = 4056 := by norm_num

/-- Absolute bound for the `H`-profile derivative via the cylinder split. -/
private theorem etw9_dH_bound (y : ℝ) : |etw8_dH y| ≤ 255 := by
  have h16 : etw8_dH y = (ctW4d y - 3 * ctW0d y) / 16 := by
    have := etw8_dH_cylinder y
    linarith
  rw [h16]
  have h4 := etw9_K4 y
  have h0 := etw9_K0 y
  have htri : |ctW4d y - 3 * ctW0d y| ≤ |ctW4d y| + 3 * |ctW0d y| := by
    have h1 : ctW4d y - 3 * ctW0d y = ctW4d y + -(3 * ctW0d y) := by ring
    rw [h1]
    have h := abs_add_le (ctW4d y) (-(3 * ctW0d y))
    rw [abs_neg, abs_mul, show |(3 : ℝ)| = 3 by norm_num] at h
    exact h
  rw [abs_div, show |(16 : ℝ)| = 16 by norm_num]
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
  linarith

/-- Continuity of the physical first-derivative series on the open window. -/
private theorem etw9_physd_contOn
    {mP K : ℕ} {Λ : ℝ}
    (S : Mode4FerrersRegularEvenProlateSolution mP K Λ)
    (hm : 2 ≤ mP) (hK : 3 ≤ K)
    (hsep : ∀ q ≥ K,
      (31 / 24 : ℝ) * mode4JacobiG mP ≤
        mode4JacobiIndex q * (mode4JacobiIndex q + 1) - 20)
    (hΛ : Λ ≤ 20) :
    ContinuousOn
      (mode4PhysicalFerrersFirstDerivativeSeries mP S.coefficients)
      (Set.Ioo (-(Real.sqrt mP)) (Real.sqrt mP)) := by
  have ha2 : Summable (fun q : ℕ =>
      (((q + 1 : ℕ) : ℝ) ^ 2) * |S.coefficients q|) :=
    mode4RecurrenceRow_polynomiallyWeighted_abs_summable_of_tail_splice
      mP K Λ hm hK hsep hΛ S.coefficients S.tail_splice 2
  have hmR : (0 : ℝ) < (mP : ℝ) := by
    have : (0 : ℕ) < mP := by omega
    exact_mod_cast this
  have hlam0 : (0 : ℝ) < Real.sqrt mP := Real.sqrt_pos.2 hmR
  intro y hy
  set t : ℝ := y / Real.sqrt mP with htdef
  have ht : t ∈ Set.Ioo (-1 : ℝ) 1 := by
    rw [htdef]
    constructor
    · rw [neg_lt, ← neg_div]
      rw [div_lt_one hlam0]
      linarith [hy.1]
    · rw [div_lt_one hlam0]
      exact hy.2
  set r : ℝ := (|t| + 1) / 2 with hrdef
  have hr0 : 0 < r := by
    rw [hrdef]
    positivity
  have hr1 : r < 1 := by
    rw [hrdef]
    have := abs_lt.2 ⟨ht.1, ht.2⟩
    linarith
  have htr : t ∈ Set.Ioo (-r) r := by
    rw [hrdef]
    have h1 : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    constructor
    · have := neg_abs_le t
      linarith [abs_nonneg t]
    · have := le_abs_self t
      linarith
  have hder := mode4FerrersFirstDerivativeSeries_hasDerivAt_of_mem_Ioo
    S.coefficients r hr0 hr1 ha2 t htr
  have hcontAt : ContinuousAt
      (mode4FerrersFirstDerivativeSeries S.coefficients) t :=
    hder.continuousAt
  have hphys : mode4PhysicalFerrersFirstDerivativeSeries mP
      S.coefficients = fun z : ℝ =>
      (Real.sqrt mP)⁻¹ *
        mode4FerrersFirstDerivativeSeries S.coefficients
          (z / Real.sqrt mP) := rfl
  rw [hphys]
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.mul continuousAt_const
  rw [htdef] at hcontAt
  have hf : ContinuousAt (fun z : ℝ => z / Real.sqrt mP) y := by
    fun_prop
  have hcomp := ContinuousAt.comp
    (f := fun z : ℝ => z / Real.sqrt mP) hcontAt hf
  simpa [Function.comp] using hcomp

/-- Generic a.e.-strong measurability for a non-top filtered comb built from
a window-continuous weight. -/
private theorem etw9_comb_asm (k : ℕ) (W : ℝ → ℝ)
    (hWcont : ContinuousOn W
      (Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ)))) :
    AEStronglyMeasurable (fun x : ℝ =>
      ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          ((n : ℝ) + 1) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
          lambda_m (selectedFerrersPreAnchorIndex k)),
        (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
          W ((n : ℝ) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))))
      MeasureTheory.volume := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  have hlam_eq : lam = Real.sqrt ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, etw5_lambda_m_eq k]
  have hsum_swap : (fun x : ℝ =>
      ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
        (n : ℝ) * (Real.exp x / lam) *
          W ((n : ℝ) * (Real.exp x / lam))) =
      fun x : ℝ =>
        ∑ n ∈ Finset.Icc 1 (k + 2),
          if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
            (n : ℝ) * (Real.exp x / lam) *
              W ((n : ℝ) * (Real.exp x / lam))
          else 0 := by
    funext x
    rw [Finset.sum_filter]
  rw [hsum_swap]
  have hn_asm : ∀ n ∈ Finset.Icc 1 (k + 2),
      AEStronglyMeasurable (fun x : ℝ =>
        if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))
        else 0) MeasureTheory.volume := by
    intro n hn
    simp only [Finset.mem_Icc] at hn
    set P : Set ℝ := {x : ℝ | ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam}
      with hPdef
    have hPmeas : MeasurableSet P := by
      rw [hPdef]
      apply measurableSet_le
      · fun_prop
      · exact measurable_const
    have hind : (fun x : ℝ =>
        if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))
        else 0) = P.indicator (fun x : ℝ =>
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))) := by
      funext x
      rw [Set.indicator_apply]
      rfl
    rw [hind]
    rw [aestronglyMeasurable_indicator_iff hPmeas]
    apply ContinuousOn.aestronglyMeasurable _ hPmeas
    have harg_cont : Continuous (fun x : ℝ =>
        (n : ℝ) * (Real.exp x / lam)) := by
      fun_prop
    apply ContinuousOn.mul harg_cont.continuousOn
    apply ContinuousOn.comp hWcont harg_cont.continuousOn
    intro x hx
    rw [hPdef, Set.mem_setOf_eq] at hx
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    have hupos : 0 < Real.exp x / lam := by positivity
    constructor
    · nlinarith
    · rw [← hlam_eq]
      nlinarith
  have := Finset.aestronglyMeasurable_sum (Finset.Icc 1 (k + 2))
    (f := fun (n : ℕ) (x : ℝ) =>
      if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
        (n : ℝ) * (Real.exp x / lam) *
          W ((n : ℝ) * (Real.exp x / lam))
      else 0) hn_asm
  have hsumeq : (fun x : ℝ =>
      ∑ n ∈ Finset.Icc 1 (k + 2),
        if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))
        else 0) =
      ∑ n ∈ Finset.Icc 1 (k + 2),
        fun x : ℝ =>
          if ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam then
            (n : ℝ) * (Real.exp x / lam) *
              W ((n : ℝ) * (Real.exp x / lam))
          else 0 := by
    funext x
    simp [Finset.sum_apply]
  rw [hsumeq]
  exact this

/-- Crude value bound for the non-top filtered comb. -/
private theorem etw9_comb_crude (k : ℕ) (W : ℝ → ℝ) (K : ℝ)
    (hK : ∀ y ∈ Set.Ioo (0 : ℝ)
      (lambda_m (selectedFerrersPreAnchorIndex k)), |W y| ≤ K)
    (hKnn : 0 ≤ K) (x : ℝ) :
    |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
        lambda_m (selectedFerrersPreAnchorIndex k)),
      (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        W ((n : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))| ≤
      K * lambda_m (selectedFerrersPreAnchorIndex k) ^ 2 /
        (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set u : ℝ := Real.exp x / lam with hudef
  have hu : 0 < u := by rw [hudef]; positivity
  have hterm : ∀ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
      ((n : ℝ) + 1) * u ≤ lam),
      |(n : ℝ) * u * W ((n : ℝ) * u)| ≤ lam * K := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1
    have hnu_pos : 0 < (n : ℝ) * u := by nlinarith
    have hnu_lt : (n : ℝ) * u < lam := by nlinarith [hn.2]
    have hnu_le : (n : ℝ) * u ≤ lam := hnu_lt.le
    rw [abs_mul, abs_of_pos hnu_pos]
    calc (n : ℝ) * u * |W ((n : ℝ) * u)| ≤ (n : ℝ) * u * K :=
        mul_le_mul_of_nonneg_left (hK _ ⟨hnu_pos, hnu_lt⟩) hnu_pos.le
      _ ≤ lam * K := mul_le_mul_of_nonneg_right hnu_le hKnn
  have hcard : (((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
      ((n : ℝ) + 1) * u ≤ lam)).card : ℝ) ≤ lam / u := by
    have hsub : (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * u ≤ lam) ⊆
        Finset.Icc 1 (Nat.floor (lam / u)) := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      refine ⟨hn.1.1, ?_⟩
      apply Nat.le_floor
      rw [le_div_iff₀ hu]
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1
      nlinarith [hn.2]
    calc (((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * u ≤ lam)).card : ℝ) ≤
        ((Finset.Icc 1 (Nat.floor (lam / u))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (Nat.floor (lam / u) : ℝ) := by
          rw [Nat.card_Icc]
          simp
      _ ≤ lam / u := Nat.floor_le (by positivity)
  calc |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
      ((n : ℝ) + 1) * u ≤ lam),
      (n : ℝ) * u * W ((n : ℝ) * u)| ≤
      ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * u ≤ lam),
        |(n : ℝ) * u * W ((n : ℝ) * u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * u ≤ lam), lam * K :=
      Finset.sum_le_sum hterm
    _ = (((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * u ≤ lam)).card : ℝ) * (lam * K) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (lam / u) * (lam * K) := by
      apply mul_le_mul_of_nonneg_right hcard
      positivity
    _ = K * lam ^ 2 / u := by
      field_simp

/-- The inverse square-root weight integrates to at most `2√λ` over the
log window. -/
private theorem etw9_inv_sqrt_integral (k : ℕ) :
    (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      (Real.sqrt (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) ≤
      2 * Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos _).le
  have hptw : ∀ x : ℝ, (Real.sqrt (Real.exp x / lam))⁻¹ =
      Real.sqrt lam * Real.exp (-(x / 2)) := by
    intro x
    have hsq : Real.sqrt (Real.exp x / lam) =
        Real.exp (x / 2) / Real.sqrt lam := by
      have h1 : Real.exp x / lam =
          (Real.exp (x / 2) / Real.sqrt lam) ^ 2 := by
        have he : (Real.exp (x / 2)) ^ 2 = Real.exp x := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
        have hl : (Real.sqrt lam) ^ 2 = lam := Real.sq_sqrt hlam.le
        rw [div_pow, he, hl]
      rw [h1, Real.sqrt_sq (by positivity)]
    rw [hsq]
    rw [inv_div, Real.exp_neg]
    rw [div_eq_mul_inv]
  have hcongr : (∫ x in (0 : ℝ)..L,
      (Real.sqrt (Real.exp x / lam))⁻¹) =
      ∫ x in (0 : ℝ)..L, Real.sqrt lam * Real.exp (-(x / 2)) := by
    apply intervalIntegral.integral_congr
    intro x _
    exact hptw x
  rw [hcongr]
  have hFTC : (∫ x in (0 : ℝ)..L,
      Real.sqrt lam * Real.exp (-(x / 2))) =
      (-2 * Real.sqrt lam * Real.exp (-(L / 2))) -
        (-2 * Real.sqrt lam * Real.exp (-(0 / 2))) := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t : ℝ => -2 * Real.sqrt lam * Real.exp (-(t / 2)))
    · intro x _
      have hexp : HasDerivAt (fun t : ℝ => Real.exp (-(t / 2)))
          (-(1 / 2) * Real.exp (-(x / 2))) x := by
        have hlin : HasDerivAt (fun t : ℝ => -(t / 2))
            (-(1 / 2) : ℝ) x := by
          simpa using ((hasDerivAt_id x).div_const 2).neg
        have := (Real.hasDerivAt_exp (-(x / 2))).comp x hlin
        convert this using 1
        ring
      have := hexp.const_mul (-2 * Real.sqrt lam)
      convert this using 1
      ring
    · apply Continuous.intervalIntegrable
      fun_prop
  rw [hFTC]
  have hexp_pos := Real.exp_pos (-(L / 2))
  have hexp0 : Real.exp (-(0 / 2 : ℝ)) = 1 := by
    norm_num
  rw [hexp0]
  have hs := Real.sqrt_nonneg lam
  nlinarith [hexp_pos]

/-- **The explicit-`H` comb integral in log coordinates.**  The additive-log
integral of the weighted majorant is exactly the committed `u`-integral,
after cutting at `u = 1` and substituting on each branch. -/
private theorem etw9_H_integral (k : ℕ) (D : ℝ)
    (hD : (∫ t in Icc
        (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹
        (lambda_m (selectedFerrersPreAnchorIndex k)),
      (Real.sqrt t)⁻¹ *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k)) t) ≤ D) :
    IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k))
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) ∧
    (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k))
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) ≤
      D := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlam : (0 : ℝ) < lam := by linarith
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hLlog : L = Real.log ((k + 2 : ℕ) : ℝ) := rfl
  have hlamsq : lam * lam = ((k + 2 : ℕ) : ℝ) := by
    rw [hlamdef, etw5_lambda_m_eq k]
    exact Real.mul_self_sqrt (by positivity)
  set x0 : ℝ := Real.log lam with hx0def
  have hx0_nn : 0 ≤ x0 := Real.log_nonneg hlam1
  have hx0_le : x0 ≤ L := by
    rw [hx0def, hLlog, ← hlamsq]
    apply Real.log_le_log hlam
    nlinarith
  have hu_at : ∀ x : ℝ, Real.exp x / lam = Real.exp x / lam := fun _ => rfl
  have humap : ∀ x : ℝ, HasDerivAt (fun t : ℝ => Real.exp t / lam)
      (Real.exp x / lam) x := by
    intro x
    simpa using (Real.hasDerivAt_exp x).div_const lam
  have hu0 : Real.exp (0 : ℝ) / lam = lam⁻¹ := by
    rw [Real.exp_zero, one_div]
  have hux0 : Real.exp x0 / lam = 1 := by
    rw [hx0def, Real.exp_log hlam]
    field_simp
  have huL : Real.exp L / lam = lam := by
    rw [hLlog, Real.exp_log (by positivity : (0:ℝ) < ((k+2:ℕ):ℝ)),
      ← hlamsq]
    field_simp
  -- branch integrands
  set g1 : ℝ → ℝ := fun t =>
    (Real.sqrt t)⁻¹ * (hbCv1 / 8 * t ^ 2 + hbKG / 2 * t +
      4 * hbCvC / (lam ^ 2 * t)) with hg1def
  set g2 : ℝ → ℝ := fun t => (Real.sqrt t)⁻¹ * (2 * hbCgC / t ^ 2)
    with hg2def
  have hg1cont : ContinuousOn g1 (Set.Icc lam⁻¹ 1) := by
    rw [hg1def]
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
      · exact Real.continuous_sqrt.continuousOn
      · intro t ht
        have h1 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
        exact (Real.sqrt_pos.2 h1).ne'
    · apply ContinuousOn.add
      · fun_prop
      · apply ContinuousOn.div continuousOn_const
        · fun_prop
        · intro t ht
          have h1 : 0 < t := lt_of_lt_of_le (by positivity) ht.1
          positivity
  have hg2cont : ContinuousOn g2 (Set.Icc (1 : ℝ) lam) := by
    rw [hg2def]
    apply ContinuousOn.mul
    · apply ContinuousOn.inv₀
      · exact Real.continuous_sqrt.continuousOn
      · intro t ht
        have h1 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
        exact (Real.sqrt_pos.2 h1).ne'
    · apply ContinuousOn.div continuousOn_const
      · fun_prop
      · intro t ht
        have h1 : (0 : ℝ) < t := lt_of_lt_of_le one_pos ht.1
        positivity
  have hinvlam_le : lam⁻¹ ≤ 1 := by
    rw [inv_le_one_iff₀]
    right
    exact hlam1
  -- x-integrand agrees with the branch compositions off the cut point
  have hbr1 : ∀ x ∈ Set.uIoc (0 : ℝ) x0,
      Real.sqrt (Real.exp x / lam) *
        hbMaj lam (Real.exp x / lam) =
      (Real.exp x / lam) * g1 (Real.exp x / lam) := by
    intro x hx
    rw [Set.uIoc_of_le hx0_nn] at hx
    have hule : Real.exp x / lam ≤ 1 := by
      rw [div_le_one hlam]
      calc Real.exp x ≤ Real.exp x0 := Real.exp_le_exp.2 hx.2
        _ = lam := by rw [hx0def, Real.exp_log hlam]
    have hupos : 0 < Real.exp x / lam := by positivity
    rw [hbMaj, if_pos hule, hg1def]
    have hsq := Real.mul_self_sqrt hupos.le
    have hs0 : 0 < Real.sqrt (Real.exp x / lam) := Real.sqrt_pos.2 hupos
    have hkey : (Real.exp x / lam) *
        (Real.sqrt (Real.exp x / lam))⁻¹ =
        Real.sqrt (Real.exp x / lam) := by
      have hsq2 : Real.sqrt (Real.exp x / lam) ^ 2 =
          Real.exp x / lam := Real.sq_sqrt hupos.le
      have hprod : lam * Real.sqrt (Real.exp x / lam) ^ 2 =
          Real.exp x := by
        rw [hsq2]
        field_simp
      field_simp
      linarith [hprod]
    calc Real.sqrt (Real.exp x / lam) *
        (hbCv1 / 8 * (Real.exp x / lam) ^ 2 +
          hbKG / 2 * (Real.exp x / lam) +
          4 * hbCvC / (lam ^ 2 * (Real.exp x / lam))) =
        ((Real.exp x / lam) * (Real.sqrt (Real.exp x / lam))⁻¹) *
          (hbCv1 / 8 * (Real.exp x / lam) ^ 2 +
            hbKG / 2 * (Real.exp x / lam) +
            4 * hbCvC / (lam ^ 2 * (Real.exp x / lam))) := by
          rw [hkey]
      _ = (Real.exp x / lam) *
          ((Real.sqrt (Real.exp x / lam))⁻¹ *
            (hbCv1 / 8 * (Real.exp x / lam) ^ 2 +
              hbKG / 2 * (Real.exp x / lam) +
              4 * hbCvC / (lam ^ 2 * (Real.exp x / lam)))) := by
          ring
  have hbr2 : ∀ x ∈ Set.uIoc x0 L,
      Real.sqrt (Real.exp x / lam) *
        hbMaj lam (Real.exp x / lam) =
      (Real.exp x / lam) * g2 (Real.exp x / lam) := by
    intro x hx
    rw [Set.uIoc_of_le hx0_le] at hx
    have hugt : 1 < Real.exp x / lam := by
      rw [lt_div_iff₀ hlam, one_mul]
      calc lam = Real.exp x0 := by rw [hx0def, Real.exp_log hlam]
        _ < Real.exp x := Real.exp_lt_exp.2 hx.1
    have hupos : 0 < Real.exp x / lam := by positivity
    rw [hbMaj, if_neg (not_le.2 hugt), hg2def]
    have hsq := Real.mul_self_sqrt hupos.le
    have hs0 : 0 < Real.sqrt (Real.exp x / lam) := Real.sqrt_pos.2 hupos
    have hkey : (Real.exp x / lam) *
        (Real.sqrt (Real.exp x / lam))⁻¹ =
        Real.sqrt (Real.exp x / lam) := by
      have hsq2 : Real.sqrt (Real.exp x / lam) ^ 2 =
          Real.exp x / lam := Real.sq_sqrt hupos.le
      have hprod : lam * Real.sqrt (Real.exp x / lam) ^ 2 =
          Real.exp x := by
        rw [hsq2]
        field_simp
      field_simp
      linarith [hprod]
    calc Real.sqrt (Real.exp x / lam) *
        (2 * hbCgC / (Real.exp x / lam) ^ 2) =
        ((Real.exp x / lam) * (Real.sqrt (Real.exp x / lam))⁻¹) *
          (2 * hbCgC / (Real.exp x / lam) ^ 2) := by
          rw [hkey]
      _ = (Real.exp x / lam) *
          ((Real.sqrt (Real.exp x / lam))⁻¹ *
            (2 * hbCgC / (Real.exp x / lam) ^ 2)) := by
          ring
  -- substitution on each piece
  have humap_cont : ContinuousOn (fun t : ℝ => Real.exp t / lam)
      (Set.uIcc (0 : ℝ) x0) := by fun_prop
  have humap_cont2 : ContinuousOn (fun t : ℝ => Real.exp t / lam)
      (Set.uIcc x0 L) := by fun_prop
  have humapD1 : ∀ x ∈ Set.Ioo (min (0 : ℝ) x0) (max (0 : ℝ) x0),
      HasDerivWithinAt (fun t : ℝ => Real.exp t / lam)
        (Real.exp x / lam) (Set.Ioi x) x := fun x _ =>
    (humap x).hasDerivWithinAt
  have humapD2 : ∀ x ∈ Set.Ioo (min x0 L) (max x0 L),
      HasDerivWithinAt (fun t : ℝ => Real.exp t / lam)
        (Real.exp x / lam) (Set.Ioi x) x := fun x _ =>
    (humap x).hasDerivWithinAt
  have humap_cont' : ContinuousOn (fun x : ℝ => Real.exp x / lam)
      (Set.uIcc (0 : ℝ) x0) := humap_cont
  have himg1 : (fun t : ℝ => Real.exp t / lam) '' Set.uIcc (0 : ℝ) x0 ⊆
      Set.Icc lam⁻¹ 1 := by
    rintro - ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hx0_nn] at hx
    constructor
    · rw [le_div_iff₀ hlam]
      calc lam⁻¹ * lam = 1 := inv_mul_cancel₀ hlam.ne'
        _ = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp x := Real.exp_le_exp.2 hx.1
    · rw [div_le_one hlam]
      calc Real.exp x ≤ Real.exp x0 := Real.exp_le_exp.2 hx.2
        _ = lam := by rw [hx0def, Real.exp_log hlam]
  have himg2 : (fun t : ℝ => Real.exp t / lam) '' Set.uIcc x0 L ⊆
      Set.Icc (1 : ℝ) lam := by
    rintro - ⟨x, hx, rfl⟩
    rw [Set.uIcc_of_le hx0_le] at hx
    constructor
    · rw [le_div_iff₀ hlam, one_mul]
      calc lam = Real.exp x0 := by rw [hx0def, Real.exp_log hlam]
        _ ≤ Real.exp x := Real.exp_le_exp.2 hx.1
    · rw [div_le_iff₀ hlam]
      calc Real.exp x ≤ Real.exp L := Real.exp_le_exp.2 hx.2
        _ = lam * lam := by
            rw [hLlog, Real.exp_log (by positivity :
              (0:ℝ) < ((k+2:ℕ):ℝ)), ← hlamsq]
  have hsub1 := intervalIntegral.integral_comp_smul_deriv''
    (f := fun t : ℝ => Real.exp t / lam)
    (f' := fun x : ℝ => Real.exp x / lam) (g := g1)
    humap_cont humapD1
    (by fun_prop)
    (hg1cont.mono himg1)
  have hsub2 := intervalIntegral.integral_comp_smul_deriv''
    (f := fun t : ℝ => Real.exp t / lam)
    (f' := fun x : ℝ => Real.exp x / lam) (g := g2)
    humap_cont2 humapD2
    (by fun_prop)
    (hg2cont.mono himg2)
  simp only [] at hsub1 hsub2
  rw [hu0, hux0] at hsub1
  rw [hux0, huL] at hsub2
  -- piecewise integrability of the original integrand
  have hL0 : (0 : ℝ) ≤ L := le_trans hx0_nn hx0_le
  have hint1 : IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lam) * hbMaj lam (Real.exp x / lam))
      MeasureTheory.volume 0 x0 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx0_nn]
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := fun x : ℝ => (Real.exp x / lam) * g1 (Real.exp x / lam))
    · apply MeasureTheory.IntegrableOn.mono_set
        (t := Set.Icc (0 : ℝ) x0) _ Set.Ioc_subset_Icc_self
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.comp (hg1cont) (by fun_prop)
      intro x hx
      apply himg1
      exact Set.mem_image_of_mem _ (by
        rw [Set.uIcc_of_le hx0_nn]; exact hx)
    · intro x hx
      exact (hbr1 x (by rw [Set.uIoc_of_le hx0_nn]; exact hx)).symm
    · exact measurableSet_Ioc
  have hint2 : IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lam) * hbMaj lam (Real.exp x / lam))
      MeasureTheory.volume x0 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hx0_le]
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := fun x : ℝ => (Real.exp x / lam) * g2 (Real.exp x / lam))
    · apply MeasureTheory.IntegrableOn.mono_set
        (t := Set.Icc x0 L) _ Set.Ioc_subset_Icc_self
      apply ContinuousOn.integrableOn_compact isCompact_Icc
      apply ContinuousOn.mul (by fun_prop)
      apply ContinuousOn.comp (hg2cont) (by fun_prop)
      intro x hx
      apply himg2
      exact Set.mem_image_of_mem _ (by
        rw [Set.uIcc_of_le hx0_le]; exact hx)
    · intro x hx
      exact (hbr2 x (by rw [Set.uIoc_of_le hx0_le]; exact hx)).symm
    · exact measurableSet_Ioc
  constructor
  · exact hint1.trans hint2
  -- value chain
  have hval1 : (∫ x in (0 : ℝ)..x0,
      Real.sqrt (Real.exp x / lam) * hbMaj lam (Real.exp x / lam)) =
      ∫ t in lam⁻¹..(1 : ℝ), g1 t := by
    rw [← hsub1]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hx
    have := hbr1 x hx
    simpa [smul_eq_mul] using this
  have hval2 : (∫ x in x0..L,
      Real.sqrt (Real.exp x / lam) * hbMaj lam (Real.exp x / lam)) =
      ∫ t in (1 : ℝ)..lam, g2 t := by
    rw [← hsub2]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with x
    intro hx
    have := hbr2 x hx
    simpa [smul_eq_mul] using this
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hint1 hint2
  rw [← hsplit, hval1, hval2]
  -- identify with the committed set integral
  set f : ℝ → ℝ := fun t => (Real.sqrt t)⁻¹ * hbMaj lam t with hfdef
  have hf1 : Set.EqOn f g1 (Set.Ioc lam⁻¹ 1) := by
    intro t ht
    simp only [hfdef, hg1def, hbMaj]
    rw [if_pos ht.2]
  have hf2 : Set.EqOn f g2 (Set.Ioc (1 : ℝ) lam) := by
    intro t ht
    simp only [hfdef, hg2def, hbMaj]
    rw [if_neg (not_le.2 ht.1)]
  have hfint1 : IntervalIntegrable f MeasureTheory.volume lam⁻¹ 1 := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hinvlam_le]
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := g1)
    · exact (hg1cont.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    · exact fun t ht => (hf1 ht).symm
    · exact measurableSet_Ioc
  have hfint2 : IntervalIntegrable f MeasureTheory.volume 1 lam := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hlam1]
    apply MeasureTheory.IntegrableOn.congr_fun
      (f := g2)
    · exact (hg2cont.integrableOn_compact isCompact_Icc).mono_set
        Set.Ioc_subset_Icc_self
    · exact fun t ht => (hf2 ht).symm
    · exact measurableSet_Ioc
  have hgv1 : (∫ t in lam⁻¹..(1 : ℝ), g1 t) = ∫ t in lam⁻¹..(1 : ℝ), f t := by
    rw [intervalIntegral.integral_of_le hinvlam_le,
      intervalIntegral.integral_of_le hinvlam_le]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    exact fun t ht => (hf1 ht).symm
  have hgv2 : (∫ t in (1 : ℝ)..lam, g2 t) = ∫ t in (1 : ℝ)..lam, f t := by
    rw [intervalIntegral.integral_of_le hlam1,
      intervalIntegral.integral_of_le hlam1]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    exact fun t ht => (hf2 ht).symm
  rw [hgv1, hgv2]
  have hadj := intervalIntegral.integral_add_adjacent_intervals
    hfint1 hfint2
  rw [hadj]
  have hinvlam_le' : lam⁻¹ ≤ lam := le_trans hinvlam_le hlam1
  rw [intervalIntegral.integral_of_le hinvlam_le']
  rw [← MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact hD

/-- Generic integrability of a weighted non-top comb from window continuity
and a window bound. -/
private theorem etw9_piece_integrable (k : ℕ) (W : ℝ → ℝ) (K : ℝ)
    (hWcont : ContinuousOn W
      (Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ))))
    (hK : ∀ y ∈ Set.Ioo (0 : ℝ)
      (lambda_m (selectedFerrersPreAnchorIndex k)), |W y| ≤ K)
    (hKnn : 0 ≤ K) :
    IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) *
              (Real.exp x /
                lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            W ((n : ℝ) *
              (Real.exp x /
                lambda_m (selectedFerrersPreAnchorIndex k)))|)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) := by
  set lam : ℝ := lambda_m (selectedFerrersPreAnchorIndex k) with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef, etw5_lambda_m_eq k]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlam : (0 : ℝ) < lam := by linarith
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos _).le
  rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
  apply MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const (Real.sqrt lam * (K * lam ^ 2 * lam)))
  · apply AEStronglyMeasurable.mul
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · have := (etw9_comb_asm k W hWcont).norm
      have heq : (fun x : ℝ => ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter
          (fun n : ℕ => ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))‖) =
          fun x : ℝ => |∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
            (n : ℝ) * (Real.exp x / lam) *
              W ((n : ℝ) * (Real.exp x / lam))| := by
        funext x
        rw [Real.norm_eq_abs]
      rw [heq] at this
      exact this.restrict
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
      with x hx
    have hcrude := etw9_comb_crude k W K hK hKnn x
    have hupos : 0 < Real.exp x / lam := by positivity
    have hexp1 : (1 : ℝ) ≤ Real.exp x := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 hx.1.le
    have hu_ge : lam⁻¹ ≤ Real.exp x / lam := by
      rw [inv_eq_one_div]
      gcongr
    have hinv_le : (Real.exp x / lam)⁻¹ ≤ lam := by
      have h := one_div_le_one_div_of_le
        (by positivity : (0 : ℝ) < lam⁻¹) hu_ge
      rwa [one_div, one_div, inv_inv] at h
    have hcomb_le : |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
        (n : ℝ) * (Real.exp x / lam) *
          W ((n : ℝ) * (Real.exp x / lam))| ≤ K * lam ^ 2 * lam := by
      calc |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))| ≤
          K * lam ^ 2 / (Real.exp x / lam) := hcrude
        _ = K * lam ^ 2 * (Real.exp x / lam)⁻¹ := by
            rw [div_eq_mul_inv]
        _ ≤ K * lam ^ 2 * lam := by
            apply mul_le_mul_of_nonneg_left hinv_le
            positivity
    have hsq_le : Real.sqrt (Real.exp x / lam) ≤ Real.sqrt lam := by
      apply Real.sqrt_le_sqrt
      have h := etw6_u_le k ⟨hx.1.le, hx.2⟩
      have hle : lam = Real.sqrt ((k + 2 : ℕ) : ℝ) := by
        rw [hlamdef, etw5_lambda_m_eq k]
      rw [hle]
      exact h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc Real.sqrt (Real.exp x / lam) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          ((n : ℝ) + 1) * (Real.exp x / lam) ≤ lam),
          (n : ℝ) * (Real.exp x / lam) *
            W ((n : ℝ) * (Real.exp x / lam))| ≤
        Real.sqrt lam * (K * lam ^ 2 * lam) := by
          apply mul_le_mul hsq_le hcomb_le (abs_nonneg _)
            (Real.sqrt_nonneg _)
      _ = Real.sqrt lam * (K * lam ^ 2 * lam) := rfl

/-- **The 3B consumer applied to one χ-inclusive defect derivative.** -/
private theorem etw9_gd_consumer (k : ℕ) (gd : ℝ → ℝ)
    (hgd_cont : ContinuousOn gd
      (Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ))))
    (Kgd : ℝ) (hKgd0 : 0 ≤ Kgd)
    (hKgd : ∀ y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)), |gd y| ≤ Kgd)
    (CE : ℝ) (hCE : 0 ≤ CE)
    (hE : (∫ y in Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ)),
      ((Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 2 - y ^ 2) * gd y ^ 2) ≤
      CE / ((k + 2 : ℕ) : ℝ)) :
    (∫ x in (0 : ℝ)..Real.log ((k + 2 : ℕ) : ℝ),
      Real.sqrt (Real.exp x / Real.sqrt ((k + 2 : ℕ) : ℝ)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter
            (fun n : ℕ => ((n : ℝ) + 1) *
              (Real.exp x / Real.sqrt ((k + 2 : ℕ) : ℝ)) ≤
              Real.sqrt ((k + 2 : ℕ) : ℝ)),
          ((n : ℝ) * (Real.exp x / Real.sqrt ((k + 2 : ℕ) : ℝ))) *
            gd ((n : ℝ) *
              (Real.exp x / Real.sqrt ((k + 2 : ℕ) : ℝ)))|) ≤
      2 * Real.sqrt ((1 / 2) * Real.log (((k + 2 : ℕ) : ℝ) + 1)) *
        Real.sqrt (CE + 1) := by
  set m : ℕ := k + 2 with hmdef
  have hmR : (0 : ℝ) < ((m : ℕ) : ℝ) := by positivity
  set lam : ℝ := Real.sqrt ((m : ℕ) : ℝ) with hlamdef
  have hlam : 0 < lam := Real.sqrt_pos.2 hmR
  set E0 : ℝ := (CE + 1) / ((m : ℕ) : ℝ) with hE0def
  have hE0pos : 0 < E0 := by rw [hE0def]; positivity
  have hgd_half_cont : ContinuousOn gd (Ioo (0 : ℝ) lam) := by
    apply hgd_cont.mono
    intro y hy
    exact ⟨by linarith [hy.1, hlam], hy.2⟩
  have hIntFull : IntegrableOn
      (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo (-lam) lam) MeasureTheory.volume := by
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const (lam ^ 2 * Kgd ^ 2))
    · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioo
      apply ContinuousOn.mul (by fun_prop)
      exact hgd_cont.pow 2
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo]
        with y hy
      rw [Real.norm_eq_abs]
      have hgdb := hKgd y hy
      have hy2 : y ^ 2 ≤ lam ^ 2 := by
        rcases hy with ⟨h1, h2⟩
        nlinarith
      have habs2 : gd y ^ 2 ≤ Kgd ^ 2 := by
        have hsq := sq_abs (gd y)
        nlinarith [abs_nonneg (gd y)]
      rw [abs_of_nonneg (by nlinarith [sq_nonneg (gd y)])]
      nlinarith [sq_nonneg (gd y), sq_nonneg y]
  have hIntHalf : IntegrableOn
      (fun y : ℝ => (lam ^ 2 - y ^ 2) * gd y ^ 2)
      (Ioo (0 : ℝ) lam) MeasureTheory.volume := by
    apply hIntFull.mono_set
    intro y hy
    exact ⟨by linarith [hy.1, hlam], hy.2⟩
  have hEhalf : (∫ y in Ioo (0 : ℝ) lam,
      (lam ^ 2 - y ^ 2) * gd y ^ 2) ≤ E0 := by
    have hmono : (∫ y in Ioo (0 : ℝ) lam,
        (lam ^ 2 - y ^ 2) * gd y ^ 2) ≤
        ∫ y in Ioo (-lam) lam, (lam ^ 2 - y ^ 2) * gd y ^ 2 := by
      apply MeasureTheory.setIntegral_mono_set hIntFull
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo]
          with y hy
        simp only [Pi.zero_apply]
        have h1 : y ^ 2 ≤ lam ^ 2 := by
          rcases hy with ⟨h1, h2⟩
          nlinarith
        nlinarith [sq_nonneg (gd y)]
      · apply HasSubset.Subset.eventuallyLE
        intro y hy
        exact ⟨by linarith [hy.1, hlam], hy.2⟩
    calc (∫ y in Ioo (0 : ℝ) lam, (lam ^ 2 - y ^ 2) * gd y ^ 2) ≤
        ∫ y in Ioo (-lam) lam, (lam ^ 2 - y ^ 2) * gd y ^ 2 := hmono
      _ ≤ CE / ((m : ℕ) : ℝ) := hE
      _ ≤ E0 := by
          rw [hE0def]
          gcongr
          linarith
  have hcons := sturm_weighted_consumer_nonTop_sqrtLog_bound
    m (by omega) gd hgd_half_cont E0 hE0pos hIntHalf hEhalf
  have hsqrtE0 : Real.sqrt E0 =
      Real.sqrt (CE + 1) / Real.sqrt ((m : ℕ) : ℝ) := by
    rw [hE0def, Real.sqrt_div (by linarith : (0 : ℝ) ≤ CE + 1)]
  have hsm : Real.sqrt ((m : ℕ) : ℝ) ≠ 0 := hlam.ne'
  calc (∫ x in (0 : ℝ)..Real.log ((m : ℕ) : ℝ),
      Real.sqrt (Real.exp x / Real.sqrt ((m : ℕ) : ℝ)) *
        |∑ n ∈ (Finset.Icc 1 m).filter
            (fun n : ℕ => ((n : ℝ) + 1) *
              (Real.exp x / Real.sqrt ((m : ℕ) : ℝ)) ≤
              Real.sqrt ((m : ℕ) : ℝ)),
          ((n : ℝ) * (Real.exp x / Real.sqrt ((m : ℕ) : ℝ))) *
            gd ((n : ℝ) *
              (Real.exp x / Real.sqrt ((m : ℕ) : ℝ)))|) ≤
      2 * Real.sqrt ((m : ℕ) : ℝ) *
        (Real.sqrt ((1 / 2) * Real.log (((m : ℕ) : ℝ) + 1)) *
          Real.sqrt E0) := hcons
    _ = 2 * Real.sqrt ((1 / 2) * Real.log (((m : ℕ) : ℝ) + 1)) *
        Real.sqrt (CE + 1) := by
        rw [hsqrtE0]
        field_simp

/-- The window `L¹` mass of the representative equals the global mass of the
zero extension, and it is interval-integrable. -/
private theorem etw10_rep_l1 (k : ℕ) (Bp : ℝ) (hBp : 0 ≤ Bp)
    (hpkt : ∀ y : ℝ, ‖selectedFerrersLemma73SourcePacket k y‖ ≤ Bp) :
    IntervalIntegrable (fun x : ℝ =>
      ‖selectedFerrersAbelLogRepresentative k x‖) MeasureTheory.volume
      0 (L_m (selectedFerrersPreAnchorIndex k)) ∧
    (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      ‖selectedFerrersAbelLogRepresentative k x‖) =
      ∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖ := by
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos _).le
  set R : ℝ := Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) * Bp *
    (((sourcePositiveIndexFinset
      (selectedFerrersPreAnchorIndex k)).card : ℝ) + 1) with hRdef
  have hint : IntervalIntegrable (fun x : ℝ =>
      ‖selectedFerrersAbelLogRepresentative k x‖) MeasureTheory.volume
      0 L := by
    rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
    apply MeasureTheory.Integrable.mono'
      (MeasureTheory.integrable_const R)
    · exact (etw6_rep_asm k).norm
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
        with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact etw6_rep_bound k Bp hBp hpkt x ⟨hx.1.le, hx.2⟩
  refine ⟨hint, ?_⟩
  have hnorm_ind : (fun x : ℝ =>
      ‖selectedFerrersAbelLogZeroExtension k x‖) =
      (Set.Icc (0 : ℝ) L).indicator
        (fun x => ‖selectedFerrersAbelLogRepresentative k x‖) := by
    funext x
    rw [selectedFerrersAbelLogZeroExtension,
      norm_indicator_eq_indicator_norm]
  rw [hnorm_ind, MeasureTheory.integral_indicator measurableSet_Icc,
    MeasureTheory.integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hL0]

/-- Interval integrability of the strict-top defect integrand. -/
private theorem etw10_top_integrable (k : ℕ) (P : ℝ) (hP : 0 ≤ P)
    (hder : ∀ y : ℝ, 0 < y →
      y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
      ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P) :
    IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
        ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
              selectedFerrersPaperLambda k ∧
            selectedFerrersPaperLambda k <
              ((n : ℝ) + 1) *
                (Real.exp x / selectedFerrersPaperLambda k)),
          (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) :
            ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) *
                (Real.exp x / selectedFerrersPaperLambda k))‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) := by
  set lam : ℝ := selectedFerrersPaperLambda k with hlamdef
  have hlam_eq : lam = lambda_m (selectedFerrersPreAnchorIndex k) := rfl
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef, selectedFerrersPaperLambda]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlam : (0 : ℝ) < lam := by linarith
  set L : ℝ := L_m (selectedFerrersPreAnchorIndex k) with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos _).le
  set Ptot : ℝ := P + 4 * 255 with hPtotdef
  have hPtot0 : 0 ≤ Ptot := by rw [hPtotdef]; linarith
  rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
  apply MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const
      (Real.sqrt lam * (((k + 2 : ℕ) : ℝ) * (lam * Ptot))))
  · apply AEStronglyMeasurable.mul
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · apply Measurable.aestronglyMeasurable
      apply Measurable.norm
      have hswap : (fun x : ℝ =>
          ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
              (n : ℝ) * (Real.exp x / lam) < lam ∧
              lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
            (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
              deriv (fun t => selectedFerrersLemma73SourcePacket k t -
                (4 : ℂ) * explicitCCMLimitH t)
                ((n : ℝ) * (Real.exp x / lam))) =
          fun x : ℝ =>
            ∑ n ∈ Finset.Icc 1 (k + 2),
              if (n : ℝ) * (Real.exp x / lam) < lam ∧
                  lam < ((n : ℝ) + 1) * (Real.exp x / lam) then
                (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
                  deriv (fun t => selectedFerrersLemma73SourcePacket k t -
                    (4 : ℂ) * explicitCCMLimitH t)
                    ((n : ℝ) * (Real.exp x / lam))
              else 0 := by
        funext x
        rw [Finset.sum_filter]
      rw [hswap]
      apply Finset.measurable_sum
      intro n _
      have hcond : MeasurableSet {x : ℝ |
          (n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam)} := by
        rw [Set.setOf_and]
        exact (measurableSet_lt (by fun_prop) measurable_const).inter
          (measurableSet_lt measurable_const (by fun_prop))
      apply Measurable.ite hcond _ measurable_const
      have harg : Measurable (fun x : ℝ =>
          (n : ℝ) * (Real.exp x / lam)) := by fun_prop
      exact (Complex.measurable_ofReal.comp harg).mul
        ((measurable_deriv _).comp harg)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc]
      with x hx
    have hupos : 0 < Real.exp x / lam := by positivity
    have hterm : ∀ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        (n : ℝ) * (Real.exp x / lam) < lam ∧
        lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
        ‖(((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t)
            ((n : ℝ) * (Real.exp x / lam))‖ ≤ lam * Ptot := by
      intro n hn
      simp only [Finset.mem_filter, Finset.mem_Icc] at hn
      set y : ℝ := (n : ℝ) * (Real.exp x / lam) with hydef
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1.1
      have hy0 : 0 < y := by rw [hydef]; nlinarith
      have hylt : y < lam := hn.2.1
      have hyne : y ≠ lambda_m (selectedFerrersPreAnchorIndex k) := by
        rw [← hlam_eq]
        exact hylt.ne
      have hpktDiff : DifferentiableAt ℝ
          (selectedFerrersLemma73SourcePacket k) y :=
        etw_packet_differentiableAt_of_pos_ne k hy0
          (by rw [selectedFerrersPreAnchorPair_lambda_eq k, ← hlam_eq]
              exact hylt.ne)
      have hHDiff : DifferentiableAt ℝ
          (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y :=
        ((etw8_H_hasDerivAt y).const_mul (4 : ℂ)).differentiableAt
      have hsub : deriv (fun t =>
          selectedFerrersLemma73SourcePacket k t -
          (4 : ℂ) * explicitCCMLimitH t) y =
          deriv (selectedFerrersLemma73SourcePacket k) y -
            deriv (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y :=
        deriv_sub hpktDiff hHDiff
      have hHval : deriv (fun t : ℝ => (4 : ℂ) * explicitCCMLimitH t) y =
          (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ) :=
        ((etw8_H_hasDerivAt y).const_mul (4 : ℂ)).deriv
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hy0, hsub, hHval]
      have hDbound : ‖deriv (selectedFerrersLemma73SourcePacket k) y -
          (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ ≤ Ptot := by
        calc ‖deriv (selectedFerrersLemma73SourcePacket k) y -
            (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ ≤
            ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ +
              ‖(4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ := by
              have h1 : deriv (selectedFerrersLemma73SourcePacket k) y -
                  (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ) =
                  deriv (selectedFerrersLemma73SourcePacket k) y +
                    -((4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)) := by ring
              rw [h1]
              calc ‖deriv (selectedFerrersLemma73SourcePacket k) y +
                  -((4 : ℂ) * ((etw8_dH y : ℝ) : ℂ))‖ ≤
                  ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ +
                    ‖-((4 : ℂ) * ((etw8_dH y : ℝ) : ℂ))‖ :=
                  norm_add_le _ _
                _ = ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ +
                    ‖(4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ := by
                    rw [norm_neg]
          _ ≤ Ptot := by
              rw [hPtotdef]
              have h1 := hder y hy0 hyne
              have h2 : ‖(4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ =
                  4 * |etw8_dH y| := by
                rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
                norm_num
              have h3 := etw9_dH_bound y
              linarith [h1, h2.le, h2.ge]
      calc y * ‖deriv (selectedFerrersLemma73SourcePacket k) y -
          (4 : ℂ) * ((etw8_dH y : ℝ) : ℂ)‖ ≤ y * Ptot :=
          mul_le_mul_of_nonneg_left hDbound hy0.le
        _ ≤ lam * Ptot := mul_le_mul_of_nonneg_right hylt.le hPtot0
    have hsum_le : ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
        (n : ℝ) * (Real.exp x / lam) < lam ∧
        lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
        (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
          deriv (fun t => selectedFerrersLemma73SourcePacket k t -
            (4 : ℂ) * explicitCCMLimitH t)
            ((n : ℝ) * (Real.exp x / lam))‖ ≤
        ((k + 2 : ℕ) : ℝ) * (lam * Ptot) := by
      calc ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
          (n : ℝ) * (Real.exp x / lam) < lam ∧
          lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
          (((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) * (Real.exp x / lam))‖ ≤
          ∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)),
            ‖(((n : ℝ) * (Real.exp x / lam) : ℝ) : ℂ) *
              deriv (fun t => selectedFerrersLemma73SourcePacket k t -
                (4 : ℂ) * explicitCCMLimitH t)
                ((n : ℝ) * (Real.exp x / lam))‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam)), lam * Ptot :=
          Finset.sum_le_sum hterm
        _ = ((((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / lam) < lam ∧
            lam < ((n : ℝ) + 1) * (Real.exp x / lam))).card : ℝ)) *
            (lam * Ptot) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k + 2 : ℕ) : ℝ) * (lam * Ptot) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          have hcard : ((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
              (n : ℝ) * (Real.exp x / lam) < lam ∧
              lam < ((n : ℝ) + 1) * (Real.exp x / lam))).card ≤
              (Finset.Icc 1 (k + 2)).card :=
            Finset.card_le_card (Finset.filter_subset _ _)
          have hicc : (Finset.Icc 1 (k + 2)).card = k + 2 := by
            rw [Nat.card_Icc]
            omega
          calc ((((Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
              (n : ℝ) * (Real.exp x / lam) < lam ∧
              lam < ((n : ℝ) + 1) * (Real.exp x / lam))).card : ℝ)) ≤
              ((Finset.Icc 1 (k + 2)).card : ℝ) := by
                exact_mod_cast hcard
            _ = ((k + 2 : ℕ) : ℝ) := by rw [hicc]
    have hsq_le : Real.sqrt (Real.exp x / lam) ≤ Real.sqrt lam := by
      apply Real.sqrt_le_sqrt
      rw [hlam_eq]
      have h := etw6_u_le k ⟨hx.1.le, hx.2⟩
      rw [← etw5_lambda_m_eq k] at h
      exact h
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    apply mul_le_mul hsq_le hsum_le (norm_nonneg _) (Real.sqrt_nonneg _)

/-- Interval integrability of the weighted `Q`-comb part alone. -/
private theorem etw10_p2_integrable (k : ℕ) (Bp P : ℝ)
    (hBp : 0 ≤ Bp) (hP : 0 ≤ P)
    (hpkt : ∀ y : ℝ, ‖selectedFerrersLemma73SourcePacket k y‖ ≤ Bp)
    (hder : ∀ y : ℝ, 0 < y →
      y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
      ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P) :
    IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
          etw_Q k (((n : ℕ) : ℝ) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) := by
  set i := selectedFerrersPreAnchorIndex k with hidef
  set lam : ℝ := lambda_m i with hlamdef
  have hlam : 0 < lam := by
    rw [hlamdef, hidef, etw5_lambda_m_eq k]
    apply Real.sqrt_pos.2
    positivity
  set L : ℝ := L_m i with hLdef
  have hL0 : (0 : ℝ) ≤ L := (logLength_pos i).le
  set card : ℝ := ((sourcePositiveIndexFinset i).card : ℝ) with hcarddef
  have hcard0 : 0 ≤ card := by rw [hcarddef]; positivity
  set s4 : ℝ := Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) with hs4def
  have hs40 : 0 ≤ s4 := Real.sqrt_nonneg _
  have hu_cont : Continuous (fun x : ℝ => Real.exp x / lam) := by
    fun_prop
  have hQm : ∀ n : ℕ+, Measurable (fun x : ℝ =>
      etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))) := by
    intro n
    have harg : Measurable (fun x : ℝ =>
        ((n : ℕ) : ℝ) * (Real.exp x / lam)) :=
      (continuous_const.mul hu_cont).measurable
    exact (Complex.measurable_ofReal.comp harg).mul
      ((measurable_deriv _).comp harg)
  rw [intervalIntegrable_iff, Set.uIoc_of_le hL0]
  apply MeasureTheory.Integrable.mono'
    (MeasureTheory.integrable_const (s4 * (card * (lam * P))))
  · apply AEStronglyMeasurable.mul
    · apply Continuous.aestronglyMeasurable
      fun_prop
    · apply Measurable.aestronglyMeasurable
      apply Measurable.norm
      exact Finset.measurable_sum _ fun n _ => hQm n
  · have hae : ∀ᵐ x : ℝ
        ∂(MeasureTheory.volume.restrict (Set.Ioc (0 : ℝ) L)),
        ∀ n : ℕ+, ((n : ℕ) : ℝ) * (Real.exp x / lam) ≠ lam :=
      (etw6_ae_no_seam k).filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc, hae]
      with x hx hnoseam
    have hqsum : ‖∑ n ∈ sourcePositiveIndexFinset i,
        etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤
        card * (lam * P) := by
      calc ‖∑ n ∈ sourcePositiveIndexFinset i,
          etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ ≤
          ∑ n ∈ sourcePositiveIndexFinset i,
            ‖etw_Q k (((n : ℕ) : ℝ) * (Real.exp x / lam))‖ :=
          norm_sum_le _ _
        _ ≤ ∑ _n ∈ sourcePositiveIndexFinset i, lam * P := by
          apply Finset.sum_le_sum
          intro n _
          set y : ℝ := ((n : ℕ) : ℝ) * (Real.exp x / lam) with hydef
          have hnpos : (0 : ℝ) < ((n : ℕ) : ℝ) := by
            exact_mod_cast n.pos
          have hy0 : 0 < y := by rw [hydef]; positivity
          have hQval : etw_Q k y = ((y : ℝ) : ℂ) *
              deriv (selectedFerrersLemma73SourcePacket k) y := rfl
          rw [hQval, norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hy0]
          rcases le_or_gt y lam with hylt | hygt
          · exact mul_le_mul hylt (hder y hy0 (hnoseam n))
              (norm_nonneg _) hlam.le
          · rw [etw6_pkt_deriv_zero_of_gt k hygt, norm_zero, mul_zero]
            positivity
        _ = card * (lam * P) := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have hsq_le : Real.sqrt (Real.exp x / lam) ≤ s4 := by
      rw [hs4def]
      apply Real.sqrt_le_sqrt
      exact etw6_u_le k ⟨hx.1.le, hx.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul hsq_le hqsum (norm_nonneg _) hs40

/-- The derivative of an even-degree Legendre polynomial is odd. -/
private theorem etw11_legendre_deriv_odd (q : ℕ) (x : ℝ) :
    (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval (-x) =
      -(mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval x := by
  set Pq := mode4OrdinaryLegendrePolynomial (2 * q) with hPq
  have heven : (fun s : ℝ => Pq.eval (-s)) = fun s : ℝ => Pq.eval s := by
    funext s
    have := mode4OrdinaryLegendre_even q s
    rw [mode4OrdinaryLegendre, mode4OrdinaryLegendre] at this
    exact this
  have h1 : HasDerivAt (fun s : ℝ => Pq.eval (-s))
      (Pq.derivative.eval (-x) * (-1)) x :=
    (Pq.hasDerivAt (-x)).comp x (hasDerivAt_neg x)
  have h2 : HasDerivAt (fun s : ℝ => Pq.eval s)
      (Pq.derivative.eval x) x := Pq.hasDerivAt x
  rw [heven] at h1
  have := h1.unique h2
  linarith

/-- The physical first-derivative series is odd. -/
private theorem etw11_physd_odd (mP : ℕ) (a : ℕ → ℝ) (y : ℝ) :
    mode4PhysicalFerrersFirstDerivativeSeries mP a (-y) =
      -mode4PhysicalFerrersFirstDerivativeSeries mP a y := by
  have hterm : ∀ q : ℕ,
      mode4FerrersFirstDerivativeTerm a q (-(y / Real.sqrt mP)) =
      -mode4FerrersFirstDerivativeTerm a q (y / Real.sqrt mP) := by
    intro q
    show (-1 : ℝ) ^ q * a q *
        (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval
          (-(y / Real.sqrt mP)) = _
    rw [etw11_legendre_deriv_odd]
    show _ = -((-1 : ℝ) ^ q * a q *
      (mode4OrdinaryLegendrePolynomial (2 * q)).derivative.eval
        (y / Real.sqrt mP))
    ring
  have hphys : mode4PhysicalFerrersFirstDerivativeSeries mP a (-y) =
      (Real.sqrt mP)⁻¹ *
        mode4FerrersFirstDerivativeSeries a (-y / Real.sqrt mP) := rfl
  have hphys' : mode4PhysicalFerrersFirstDerivativeSeries mP a y =
      (Real.sqrt mP)⁻¹ *
        mode4FerrersFirstDerivativeSeries a (y / Real.sqrt mP) := rfl
  rw [hphys, hphys']
  have hser : mode4FerrersFirstDerivativeSeries a (-y / Real.sqrt mP) =
      -mode4FerrersFirstDerivativeSeries a (y / Real.sqrt mP) := by
    have hna : -y / Real.sqrt mP = -(y / Real.sqrt mP) := by ring
    rw [hna]
    show (∑' q : ℕ, mode4FerrersFirstDerivativeTerm a q
        (-(y / Real.sqrt mP))) = _
    rw [tsum_congr hterm, tsum_neg]
    rfl
  rw [hser]
  ring

private theorem etw11_abs_sub_le (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  have h := abs_add_le a (-b)
  rw [abs_neg] at h
  have heq : a - b = a + -b := by ring
  rw [heq]
  exact h

/-- Scalar assembly algebra for the pointwise majorant. -/
private theorem etw12_pointwise_algebra
    (sq isq hbM HBv S4v S0v J4v J0v TPv p q lm2 c4v c0v X : ℝ)
    (hsq : 0 ≤ sq) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (h8 : X ≤ HBv + ((1 / 4) * S4v + (3 / 4) * S0v +
      (1 / 4) * p * J4v + (3 / 4) * q * J0v) + TPv)
    (hHB : HBv ≤ hbM)
    (hb4 : sq * J4v ≤ c4v * lm2 * isq)
    (hb0 : sq * J0v ≤ c0v * lm2 * isq) :
    sq * X ≤ sq * hbM + (1 / 4) * (sq * S4v) + (3 / 4) * (sq * S0v) +
      ((1 / 4) * p * c4v + (3 / 4) * q * c0v) * lm2 * isq +
      sq * TPv := by
  have hstep := mul_le_mul_of_nonneg_left h8 hsq
  have e1 : sq * (HBv + ((1 / 4) * S4v + (3 / 4) * S0v +
      (1 / 4) * p * J4v + (3 / 4) * q * J0v) + TPv) =
      sq * HBv + (1 / 4) * (sq * S4v) + (3 / 4) * (sq * S0v) +
      (1 / 4) * p * (sq * J4v) + (3 / 4) * q * (sq * J0v) +
      sq * TPv := by ring
  rw [e1] at hstep
  have hH := mul_le_mul_of_nonneg_left hHB hsq
  have h4' := mul_le_mul_of_nonneg_left hb4
    (by positivity : (0 : ℝ) ≤ (1 / 4) * p)
  have h0' := mul_le_mul_of_nonneg_left hb0
    (by positivity : (0 : ℝ) ≤ (3 / 4) * q)
  have e2 : (1 / 4) * p * (c4v * lm2 * isq) +
      (3 / 4) * q * (c0v * lm2 * isq) =
      ((1 / 4) * p * c4v + (3 / 4) * q * c0v) * lm2 * isq := by ring
  linarith [hstep, hH, h4', h0', e2]

/-! ### S3e: the master budget rate -/

set_option maxHeartbeats 12000000 in
/-- **The derivative budget grows at most like `(k+2)^{1/4} √log`.**  This is
the discharged form of the open supplier
`W5_LOG_DERIVATIVE_BUDGET_BOUNDED`: uniform boundedness is replaced by the
honest rate, exactly as the b1 fork ordered. -/
private theorem etw10_budget_rate
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
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
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k in Filter.atTop,
      selectedFerrersAbelLogDerivativeBudget k ≤
        A * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
  classical
  obtain ⟨Dtr, hDtr0, hDtrs⟩ := etw4_Dtr
  obtain ⟨DH, hDH0, hDHs⟩ := explicitH_derivative_comb_budget
  have hmode' : ∀ᶠ k in Filter.atTop,
      (∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2) ∧
      (∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2) := by
    filter_upwards [hmode] with k hk
    exact ⟨fun x hx => (hk x hx).1, fun x hx => (hk x hx).2⟩
  obtain ⟨Al1, Bl1, hAl1, hBl1, hl1ev⟩ :=
    selectedFerrersAbelLogZeroExtension_l1_rate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hθlin : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2)| ≤ (Cθ + 57) * ((k + 2 : ℕ) : ℝ) ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2)| ≤ (Cθ + 57) * ((k + 2 : ℕ) : ℝ) := by
    have hevC : ∀ᶠ k : ℕ in Filter.atTop, Cθ ≤ ((k : ℕ) : ℝ) :=
      Filter.Tendsto.eventually_ge_atTop
        (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
    filter_upwards [hθ, hevC] with k hk hkC
    have hpi315 : Real.pi < 3.15 := Real.pi_lt_d2
    have hm1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast this
    constructor
    · have h1 := abs_le.1 hk.1
      rw [abs_le]
      constructor
      · nlinarith [h1.1, Real.pi_pos.le, hm1, hCθ]
      · nlinarith [h1.2, Real.pi_pos.le, hpi315, hm1, hCθ]
    · have h1 := abs_le.1 hk.2
      rw [abs_le]
      constructor
      · nlinarith [h1.1, Real.pi_pos.le, hm1, hCθ]
      · nlinarith [h1.2, Real.pi_pos.le, hpi315, hm1, hCθ]
  have hTopEv := selectedFerrersDefectEdgeTopBudget_bound_of_modeChiThetaRates
    C0 C4 Cχ (Cθ + 57) hC0 hC4 hmode hχ hθlin
  set CE0 : ℝ := (2 * Real.pi) * (2 * C0) ^ 2 *
      (Real.sqrt (2 * Real.pi) / Real.pi) +
    Cθ * (2 * 1 + 2 * (2 * C0)) * (2 * C0) + (2 * Dtr) * (2 * C0)
    with hCE0def
  set CE4 : ℝ := (18 * Real.pi) * (2 * C4) ^ 2 *
      (Real.sqrt (18 * Real.pi) / Real.pi) +
    Cθ * (2 * 533 + 2 * (2 * C4)) * (2 * C4) + (2 * Dtr) * (2 * C4)
    with hCE4def
  have hCE00 : 0 ≤ CE0 := by
    rw [hCE0def]
    have := Real.pi_pos
    positivity
  have hCE40 : 0 ≤ CE4 := by
    rw [hCE4def]
    have := Real.pi_pos
    positivity
  set Etop : ℝ := 2 * (5373952 * Real.sqrt 2032129 + 1) with hEtopdef
  have hEtop0 : 0 ≤ Etop := by rw [hEtopdef]; positivity
  set A : ℝ := (Bl1 + Al1) / 2 + DH +
    (1 / 2) * Real.sqrt (CE4 + 1) + (3 / 2) * Real.sqrt (CE0 + 1) +
    2040 * Cχ + Etop with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    positivity
  refine ⟨A, hA0, ?_⟩
  have hmode0 : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarZero k *
            (selectedFerrersPreAnchorPair k).h0 x -
          ((parabolicCylinderD 0 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C0 / (selectedFerrersPaperLambda k) ^ 2 :=
    hmode.mono fun k hk x hx => (hk x hx).1
  have hmode4 : ∀ᶠ k in Filter.atTop,
      ∀ x ∈ Set.Icc (-(selectedFerrersPaperLambda k))
          (selectedFerrersPaperLambda k),
        ‖centerAnchorScalarFour k *
            (selectedFerrersPreAnchorPair k).h4 x -
          ((parabolicCylinderD 4 (projectCylinderArgument x) : ℝ) : ℂ)‖ ≤
            C4 / (selectedFerrersPaperLambda k) ^ 2 :=
    hmode.mono fun k hk x hx => (hk x hx).2
  have hE0ev := etw4_energy0_ev C0 Cχ Cθ Dtr hC0 hDtr0 hmode0 hχ hθ
    (fun lamv => (hDtrs lamv).1)
  have hE4ev := etw4_energy4_ev C4 Cχ Cθ Dtr hC4 hDtr0 hmode4 hχ hθ
    (fun lamv => (hDtrs lamv).2)
  have hevC : ∀ᶠ kk : ℕ in Filter.atTop, Cθ ≤ ((kk : ℕ) : ℝ) :=
    Filter.Tendsto.eventually_ge_atTop
      (tendsto_natCast_atTop_atTop (R := ℝ)) Cθ
  have hev71 : ∀ᶠ kk : ℕ in Filter.atTop, 71 ≤ kk :=
    Filter.eventually_ge_atTop 71
  filter_upwards [hχ, hE0ev, hE4ev, etw4_hLambda_ev Cθ hθ,
    etw4_hchi2_ev Cχ hχ, etw5_pktDeriv_bound_ev Cθ hθ, hl1ev, hTopEv,
    hθ, hevC, hev71]
    with k hkχ hkE0 hkE4 hkΛ hkχ2 hkP hkl1 hkTop hkθ hkC hk71
  have hmR : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
  set lam : ℝ := Real.sqrt ((k + 2 : ℕ) : ℝ) with hlamdef
  have hlam : 0 < lam := Real.sqrt_pos.2 hmR
  have hlam1 : (1 : ℝ) ≤ lam := by
    rw [hlamdef]
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlam_eq : lambda_m (selectedFerrersPreAnchorIndex k) = lam := by
    rw [etw5_lambda_m_eq k, hlamdef]
  have hpaper_eq : selectedFerrersPaperLambda k = lam := by
    rw [selectedFerrersPaperLambda, hlamdef]
  obtain ⟨Bp, hBp0, hBp⟩ := etw6_pkt_bound k
  obtain ⟨P, hP0, hP⟩ := hkP
  have hP' : ∀ y : ℝ, 0 < y →
      y ≠ lambda_m (selectedFerrersPreAnchorIndex k) →
      ‖deriv (selectedFerrersLemma73SourcePacket k) y‖ ≤ P := hP
  have hreduced := etw7_budget_reduced k Bp P hBp0 hP0 hBp hP'
  obtain ⟨hint_rep, heq_rep⟩ := etw10_rep_l1 k Bp hBp0 hBp
  have hint_p1 : IntervalIntegrable (fun x : ℝ =>
      (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) :=
    hint_rep.const_mul _
  have hint_p2 := etw10_p2_integrable k Bp P hBp0 hP0 hBp hP'
  have hsplit : (∫ x in
      (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      ((1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
        Real.sqrt (Real.exp x /
          lambda_m (selectedFerrersPreAnchorIndex k)) *
          ‖∑ n ∈ sourcePositiveIndexFinset
              (selectedFerrersPreAnchorIndex k),
            etw_Q k (((n : ℕ) : ℝ) *
              (Real.exp x /
                lambda_m (selectedFerrersPreAnchorIndex k)))‖)) =
      (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖) +
      ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        Real.sqrt (Real.exp x /
          lambda_m (selectedFerrersPreAnchorIndex k)) *
          ‖∑ n ∈ sourcePositiveIndexFinset
              (selectedFerrersPreAnchorIndex k),
            etw_Q k (((n : ℕ) : ℝ) *
              (Real.exp x /
                lambda_m (selectedFerrersPreAnchorIndex k)))‖ :=
    intervalIntegral.integral_add hint_p1 hint_p2
  have hp1val : (∫ x in
      (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖) ≤
      (Bl1 + Al1) / 2 := by
    rw [intervalIntegral.integral_const_mul, heq_rep]
    have h1 := hkl1
    have hsq1 : (1 : ℝ) ≤ Real.sqrt (selectedFerrersPaperLambda k) := by
      rw [hpaper_eq]
      apply Real.one_le_sqrt.mpr
      exact hlam1
    have h2 : Al1 / Real.sqrt (selectedFerrersPaperLambda k) ≤ Al1 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    linarith
  -- eigenvalue absolute windows for the flux machinery
  have hmk : ((k : ℕ) : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (k : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hm73 : (73 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (73 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hsq4 : (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 = ((k + 2 : ℕ) : ℝ) ^ 2 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hmR.le]
  have hpi4 : Real.pi ≤ 4 := Real.pi_le_four
  have habs_bound : ∀ μv : ℝ, 0 ≤ μv → μv ≤ 18 * Real.pi →
      ∀ Λv : ℝ, |Λv + mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * μv| ≤ Cθ →
      |Λv + mode4JacobiG (k + 2)| ≤ (Real.sqrt ((k + 2 : ℕ) : ℝ)) ^ 4 := by
    intro μv hμ0 hμ18 Λv hΛv
    rw [hsq4]
    have h1 := (abs_le.1 hΛv).1
    have h2 := (abs_le.1 hΛv).2
    rw [abs_le]
    constructor
    · have hmul : 0 ≤ ((k + 2 : ℕ) : ℝ) * μv := by positivity
      nlinarith [hkC, hmk]
    · have hmul : ((k + 2 : ℕ) : ℝ) * μv ≤ ((k + 2 : ℕ) : ℝ) * (72 : ℝ) := by
        apply mul_le_mul_of_nonneg_left _ hmR.le
        nlinarith
      nlinarith [hkC, hmk, hm73, hmul, h2]
  have hθabs0 := habs_bound (2 * Real.pi) (by positivity)
    (by nlinarith [Real.pi_pos]) _ hkθ.1
  have hθabs4 := habs_bound (18 * Real.pi) (by positivity)
    (by nlinarith [Real.pi_pos]) _ hkθ.2
  obtain ⟨M0, hM0nn, hM0⟩ := etw5_dseries_bound
    (selectedFerrersPreAnchorSolution0 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.1 hθabs0
  obtain ⟨M4, hM4nn, hM4⟩ := etw5_dseries_bound
    (selectedFerrersPreAnchorSolution4 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.2 hθabs4
  -- full-window derivative-series bounds from parity
  have hM0full : ∀ y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)),
      |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y| ≤ M0 := by
    intro y hy
    rcases lt_trichotomy y 0 with hneg | hzero | hpos
    · have hodd := etw11_physd_odd (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients (-y)
      rw [neg_neg] at hodd
      rw [hodd, abs_neg]
      exact hM0 (-y) ⟨by linarith, by linarith [hy.1]⟩
    · subst hzero
      have hodd := etw11_physd_odd (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients 0
      rw [neg_zero] at hodd
      have hzero : mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients 0 = 0 := by
        linarith [hodd]
      rw [hzero, abs_zero]
      exact hM0nn
    · exact hM0 y ⟨hpos, hy.2⟩
  have hM4full : ∀ y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)),
      |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y| ≤ M4 := by
    intro y hy
    rcases lt_trichotomy y 0 with hneg | hzero | hpos
    · have hodd := etw11_physd_odd (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients (-y)
      rw [neg_neg] at hodd
      rw [hodd, abs_neg]
      exact hM4 (-y) ⟨by linarith, by linarith [hy.1]⟩
    · subst hzero
      have hodd := etw11_physd_odd (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients 0
      rw [neg_zero] at hodd
      have hzero : mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients 0 = 0 := by
        linarith [hodd]
      rw [hzero, abs_zero]
      exact hM4nn
    · exact hM4 y ⟨hpos, hy.2⟩
  -- gd continuity and bounds
  have hctW0d_cont : Continuous ctW0d :=
    continuous_iff_continuousAt.mpr fun x =>
      (ctW0d_hasDerivAt x).continuousAt
  have hctW4d_cont : Continuous ctW4d :=
    continuous_iff_continuousAt.mpr fun x =>
      (ctW4d_hasDerivAt x).continuousAt
  have hphysd0_cont := etw9_physd_contOn
    (selectedFerrersPreAnchorSolution0 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.1
  have hphysd4_cont := etw9_physd_contOn
    (selectedFerrersPreAnchorSolution4 k) (by omega) (by omega)
    (selectedFerrersPreAnchorSeparation k) hkΛ.2
  have hgd0_cont : ContinuousOn (etw4_gd0 k)
      (Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ))) := by
    have heq : etw4_gd0 k = fun y : ℝ =>
        ((selectedFerrersPreAnchorPair k).chi2 *
          (centerAnchorScalarZero k).re /
          (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization) *
          mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution0 k).coefficients y -
        (selectedFerrersPreAnchorPair k).chi2 * ctW0d y := rfl
    rw [heq]
    exact (continuousOn_const.mul hphysd0_cont).sub
      (continuousOn_const.mul hctW0d_cont.continuousOn)
  have hgd4_cont : ContinuousOn (etw4_gd4 k)
      (Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
        (Real.sqrt ((k + 2 : ℕ) : ℝ))) := by
    have heq : etw4_gd4 k = fun y : ℝ =>
        ((selectedFerrersPreAnchorPair k).chi0 *
          (centerAnchorScalarFour k).re /
          (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization) *
          mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
            (selectedFerrersPreAnchorSolution4 k).coefficients y -
        (selectedFerrersPreAnchorPair k).chi0 * ctW4d y := rfl
    rw [heq]
    exact (continuousOn_const.mul hphysd4_cont).sub
      (continuousOn_const.mul hctW4d_cont.continuousOn)
  set c0 : ℝ := (selectedFerrersPreAnchorPair k).chi2 *
    (centerAnchorScalarZero k).re /
    (selectedFerrersPreAnchorSolution0 k).physicalL2Normalization
    with hc0def
  set c4 : ℝ := (selectedFerrersPreAnchorPair k).chi0 *
    (centerAnchorScalarFour k).re /
    (selectedFerrersPreAnchorSolution4 k).physicalL2Normalization
    with hc4def
  set Kgd0 : ℝ := |c0| * M0 + 2 * 8 with hKgd0def
  set Kgd4 : ℝ := |c4| * M4 + 2 * 4056 with hKgd4def
  have hKgd0nn : 0 ≤ Kgd0 := by
    rw [hKgd0def]
    positivity
  have hKgd4nn : 0 ≤ Kgd4 := by
    rw [hKgd4def]
    positivity
  have hgd0_bound : ∀ y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)), |etw4_gd0 k y| ≤ Kgd0 := by
    intro y hy
    have heq : etw4_gd0 k y = c0 *
        mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution0 k).coefficients y -
        (selectedFerrersPreAnchorPair k).chi2 * ctW0d y := rfl
    rw [heq, hKgd0def]
    have h1 := hM0full y hy
    have h2 := etw9_K0 y
    have h3 := hkχ2.2
    have htri := etw11_abs_sub_le
      (c0 * mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y)
      ((selectedFerrersPreAnchorPair k).chi2 * ctW0d y)
    rw [abs_mul, abs_mul] at htri
    have hb1 : |c0| * |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution0 k).coefficients y| ≤
        |c0| * M0 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hb2 : |(selectedFerrersPreAnchorPair k).chi2| * |ctW0d y| ≤
        2 * 8 := by
      apply mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
    linarith
  have hgd4_bound : ∀ y ∈ Set.Ioo (-(Real.sqrt ((k + 2 : ℕ) : ℝ)))
      (Real.sqrt ((k + 2 : ℕ) : ℝ)), |etw4_gd4 k y| ≤ Kgd4 := by
    intro y hy
    have heq : etw4_gd4 k y = c4 *
        mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
          (selectedFerrersPreAnchorSolution4 k).coefficients y -
        (selectedFerrersPreAnchorPair k).chi0 * ctW4d y := rfl
    rw [heq, hKgd4def]
    have h1 := hM4full y hy
    have h2 := etw9_K4 y
    have h3 := hkχ2.1
    have htri := etw11_abs_sub_le
      (c4 * mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y)
      ((selectedFerrersPreAnchorPair k).chi0 * ctW4d y)
    rw [abs_mul, abs_mul] at htri
    have hb1 : |c4| * |mode4PhysicalFerrersFirstDerivativeSeries (k + 2)
        (selectedFerrersPreAnchorSolution4 k).coefficients y| ≤
        |c4| * M4 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    have hb2 : |(selectedFerrersPreAnchorPair k).chi0| * |ctW4d y| ≤
        2 * 4056 := by
      apply mul_le_mul h3 h2 (abs_nonneg _) (by norm_num)
    linarith
  -- consumer values for the two defect combs
  have hcons0 := etw9_gd_consumer k (etw4_gd0 k) hgd0_cont Kgd0 hKgd0nn
    hgd0_bound CE0 hCE00 hkE0
  have hcons4 := etw9_gd_consumer k (etw4_gd4 k) hgd4_cont Kgd4 hKgd4nn
    hgd4_bound CE4 hCE40 hkE4
  -- committed H budget at this window
  have hsqrt2lam : Real.sqrt 2 ≤
      lambda_m (selectedFerrersPreAnchorIndex k) := by
    rw [hlam_eq, hlamdef]
    apply Real.sqrt_le_sqrt
    have : (2 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  obtain ⟨hbMajPt, hbMajInt⟩ :=
    hDHs (lambda_m (selectedFerrersPreAnchorIndex k)) hsqrt2lam
  obtain ⟨hHint, hHval⟩ := etw9_H_integral k DH hbMajInt
  -- piece integrabilities
  have hgd4_cont' : ContinuousOn (etw4_gd4 k)
      (Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ))) := by
    apply hgd4_cont.mono
    intro y hy
    exact ⟨by linarith [hy.1, hlam], hy.2⟩
  have hgd0_cont' : ContinuousOn (etw4_gd0 k)
      (Set.Ioo (0 : ℝ) (Real.sqrt ((k + 2 : ℕ) : ℝ))) := by
    apply hgd0_cont.mono
    intro y hy
    exact ⟨by linarith [hy.1, hlam], hy.2⟩
  have hgd4_bound' : ∀ y ∈ Set.Ioo (0 : ℝ)
      (lambda_m (selectedFerrersPreAnchorIndex k)),
      |etw4_gd4 k y| ≤ Kgd4 := by
    intro y hy
    rw [hlam_eq, hlamdef] at hy
    exact hgd4_bound y ⟨by linarith [hy.1, hlam], hy.2⟩
  have hgd0_bound' : ∀ y ∈ Set.Ioo (0 : ℝ)
      (lambda_m (selectedFerrersPreAnchorIndex k)),
      |etw4_gd0 k y| ≤ Kgd0 := by
    intro y hy
    rw [hlam_eq, hlamdef] at hy
    exact hgd0_bound y ⟨by linarith [hy.1, hlam], hy.2⟩
  have hg4int := etw9_piece_integrable k (etw4_gd4 k) Kgd4
    hgd4_cont' hgd4_bound' hKgd4nn
  have hg0int := etw9_piece_integrable k (etw4_gd0 k) Kgd0
    hgd0_cont' hgd0_bound' hKgd0nn
  set Cjunk : ℝ := ((1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| *
      4056 + (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| * 8) *
    lambda_m (selectedFerrersPreAnchorIndex k) ^ 2 with hCjunkdef
  have hCjunk0 : 0 ≤ Cjunk := by
    rw [hCjunkdef]
    have hlm : (0 : ℝ) ≤ lambda_m (selectedFerrersPreAnchorIndex k) := by
      rw [etw5_lambda_m_eq k]
      positivity
    positivity
  have hjcont : Continuous (fun x : ℝ => Cjunk *
      (Real.sqrt (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) := by
    apply Continuous.mul continuous_const
    apply Continuous.inv₀
    · fun_prop
    · intro x
      apply (Real.sqrt_pos.2 _).ne'
      rw [hlam_eq]
      positivity
  have hjint : IntervalIntegrable (fun x : ℝ => Cjunk *
      (Real.sqrt (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) :=
    hjcont.intervalIntegrable _ _
  have htopint := etw10_top_integrable k P hP0 hP'
  -- the five-piece majorant
  set idx := selectedFerrersPreAnchorIndex k with hidxdef
  have hL0 : (0 : ℝ) ≤ L_m (selectedFerrersPreAnchorIndex k) :=
    (logLength_pos _).le
  have hGint : IntervalIntegrable (fun x : ℝ =>
      Real.sqrt (Real.exp x /
          lambda_m (selectedFerrersPreAnchorIndex k)) *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k))
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) +
      (1 / 4) * (Real.sqrt (Real.exp x /
          lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd4 k ((n : ℝ) * (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)))|) +
      (3 / 4) * (Real.sqrt (Real.exp x /
          lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x /
            lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd0 k ((n : ℝ) * (Real.exp x /
              lambda_m (selectedFerrersPreAnchorIndex k)))|) +
      Cjunk * (Real.sqrt (Real.exp x /
        lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ +
      Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
        ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
              selectedFerrersPaperLambda k ∧
            selectedFerrersPaperLambda k <
              ((n : ℝ) + 1) *
                (Real.exp x / selectedFerrersPaperLambda k)),
          (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) :
            ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) *
                (Real.exp x / selectedFerrersPaperLambda k))‖)
      MeasureTheory.volume 0 (L_m (selectedFerrersPreAnchorIndex k)) :=
    (((hHint.add (hg4int.const_mul _)).add
      (hg0int.const_mul _)).add hjint).add htopint
  -- pointwise a.e. domination of the Q-part by the majorant
  have hmono : (∫ x in
      (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        ‖∑ n ∈ sourcePositiveIndexFinset (selectedFerrersPreAnchorIndex k),
          etw_Q k (((n : ℕ) : ℝ) *
            (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖) ≤
      ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k))
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) +
      (1 / 4) * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd4 k ((n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))|) +
      (3 / 4) * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd0 k ((n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))|) +
      Cjunk * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ +
      Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
        ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
              selectedFerrersPaperLambda k ∧
            selectedFerrersPaperLambda k <
              ((n : ℝ) + 1) *
                (Real.exp x / selectedFerrersPaperLambda k)),
          (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) :
            ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) *
                (Real.exp x / selectedFerrersPaperLambda k))‖ := by
    apply intervalIntegral.integral_mono_ae_restrict hL0 hint_p2 hGint
    have hns : ∀ᵐ x : ℝ
        ∂(MeasureTheory.volume.restrict
          (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))),
        ∀ n : ℕ+, ((n : ℕ) : ℝ) *
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠
          lambda_m (selectedFerrersPreAnchorIndex k) :=
      (etw6_ae_no_seam k).filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
    have hne0 : ∀ᵐ x : ℝ
        ∂(MeasureTheory.volume.restrict
          (Set.Icc (0 : ℝ) (L_m (selectedFerrersPreAnchorIndex k)))),
        x ≠ 0 := by
      apply Filter.Eventually.filter_mono
        (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self)
      filter_upwards [MeasureTheory.measure_eq_zero_iff_ae_notMem.1
        (MeasureTheory.measure_singleton (0 : ℝ))] with x hx
      exact hx
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc, hns,
      hne0] with x hxIcc hnoseam hxne
    have hx : x ∈ Set.Ioc (0 : ℝ)
        (L_m (selectedFerrersPreAnchorIndex k)) :=
      ⟨lt_of_le_of_ne hxIcc.1 (Ne.symm hxne), hxIcc.2⟩
    have h8 := etw8_qcomb_split k hx hnoseam
    have hu0 : 0 < Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k) := by
      have : (0 : ℝ) < lambda_m (selectedFerrersPreAnchorIndex k) := by
        rw [etw5_lambda_m_eq k]
        positivity
      positivity
    have hsq0 : 0 ≤ Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := Real.sqrt_nonneg _
    have hsqne : Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≠ 0 := (Real.sqrt_pos.2 hu0).ne'
    have hstep := mul_le_mul_of_nonneg_left h8 hsq0
    have h2 : (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) = Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := by
      have h3 : (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) = Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) :=
        (Real.mul_self_sqrt hu0.le).symm
      calc (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) =
          (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) := by rw [← h3]
        _ = ((Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) * Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := by ring
        _ = 1 * Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := by rw [inv_mul_cancel₀ hsqne]
        _ = Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) := one_mul _
    have h4 : Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ = (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ := by
      calc Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ =
          ((Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ := by rw [h2]
        _ = (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) := by ring
        _ = (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ := by
            rw [mul_inv_cancel₀ hu0.ne', mul_one]
    have hidgen : ∀ c : ℝ, Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * (c / (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) =
        c * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ := by
      intro c
      calc Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * (c / (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) = c * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) * ((Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) := by
            rw [div_eq_mul_inv]; ring
        _ = c * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹ := by rw [h4]
    have humem : (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ∈ Icc
        (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹
        (lambda_m (selectedFerrersPreAnchorIndex k)) := by
      constructor
      · have hexp1 : (1 : ℝ) ≤ Real.exp x := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.2 hxIcc.1
        rw [div_eq_mul_inv]
        calc (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ =
            1 * (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ := (one_mul _).symm
          _ ≤ Real.exp x * (lambda_m (selectedFerrersPreAnchorIndex k))⁻¹ := by
              apply mul_le_mul_of_nonneg_right hexp1
              rw [etw5_lambda_m_eq k]
              positivity
      · have h := etw6_u_le k hxIcc
        rw [← etw5_lambda_m_eq k] at h
        exact h
    have hb1 := mul_le_mul_of_nonneg_left
      (hbMajPt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) humem) hsq0
    have hcr4 := etw9_comb_crude k ctW4d 4056
      (fun y _ => etw9_K4 y) (by norm_num) x
    have hcr0 := etw9_comb_crude k ctW0d 8
      (fun y _ => etw9_K0 y) (by norm_num) x
    have hb4 := mul_le_mul_of_nonneg_left hcr4 hsq0
    have hb0 := mul_le_mul_of_nonneg_left hcr0 hsq0
    rw [hidgen] at hb4 hb0
    rw [hCjunkdef]
    exact etw12_pointwise_algebra _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      hsq0 (abs_nonneg _) (abs_nonneg _) h8
      (hbMajPt _ humem) hb4 hb0
  -- split the majorant integral into its five pieces
  have h12 := hHint.add (hg4int.const_mul (1 / 4 : ℝ))
  have h123 := h12.add (hg0int.const_mul (3 / 4 : ℝ))
  have h1234 := h123.add hjint
  rw [intervalIntegral.integral_add h1234 htopint,
    intervalIntegral.integral_add h123 hjint,
    intervalIntegral.integral_add h12 (hg0int.const_mul (3 / 4 : ℝ)),
    intervalIntegral.integral_add hHint (hg4int.const_mul (1 / 4 : ℝ))]
    at hmono
  -- values of the five pieces
  have hV1 : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        hbMaj (lambda_m (selectedFerrersPreAnchorIndex k))
          (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k))) ≤ DH := hHval
  have hV2 : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      (1 / 4 : ℝ) * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd4 k ((n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))|)) ≤
      (1 / 4) * (2 * Real.sqrt ((1 / 2) *
        Real.log (((k + 2 : ℕ) : ℝ) + 1)) * Real.sqrt (CE4 + 1)) := by
    rw [intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 1 / 4)
    exact hcons4
  have hV3 : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      (3 / 4 : ℝ) * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
        |∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            ((n : ℝ) + 1) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) ≤
            lambda_m (selectedFerrersPreAnchorIndex k)),
          (n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            etw4_gd0 k ((n : ℝ) * (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))|)) ≤
      (3 / 4) * (2 * Real.sqrt ((1 / 2) *
        Real.log (((k + 2 : ℕ) : ℝ) + 1)) * Real.sqrt (CE0 + 1)) := by
    rw [intervalIntegral.integral_const_mul]
    apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 3 / 4)
    exact hcons0
  have hV4 : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Cjunk * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) ≤
      Cjunk * (2 * Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))) := by
    rw [intervalIntegral.integral_const_mul]
    exact mul_le_mul_of_nonneg_left (etw9_inv_sqrt_integral k) hCjunk0
  have hV5 : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
        ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
              selectedFerrersPaperLambda k ∧
            selectedFerrersPaperLambda k <
              ((n : ℝ) + 1) *
                (Real.exp x / selectedFerrersPaperLambda k)),
          (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) :
            ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) *
                (Real.exp x / selectedFerrersPaperLambda k))‖) ≤ Etop := by
    have heq : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        Real.sqrt (Real.exp x / selectedFerrersPaperLambda k) *
        ‖∑ n ∈ (Finset.Icc 1 (k + 2)).filter (fun n : ℕ =>
            (n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) <
              selectedFerrersPaperLambda k ∧
            selectedFerrersPaperLambda k <
              ((n : ℝ) + 1) *
                (Real.exp x / selectedFerrersPaperLambda k)),
          (((n : ℝ) * (Real.exp x / selectedFerrersPaperLambda k) : ℝ) :
            ℂ) *
            deriv (fun t => selectedFerrersLemma73SourcePacket k t -
              (4 : ℂ) * explicitCCMLimitH t)
              ((n : ℝ) *
                (Real.exp x / selectedFerrersPaperLambda k))‖) = selectedFerrersDefectEdgeTopBudget k := rfl
    rw [heq]
    have hlp1 : (1 : ℝ) ≤ selectedFerrersPaperLambda k := by
      rw [hpaper_eq]
      exact hlam1
    have hs1 : (1 : ℝ) ≤ Real.sqrt (selectedFerrersPaperLambda k) := by
      apply Real.one_le_sqrt.mpr hlp1
    have hden : (1 : ℝ) ≤ selectedFerrersPaperLambda k *
        Real.sqrt (selectedFerrersPaperLambda k) := by
      nlinarith
    calc selectedFerrersDefectEdgeTopBudget k ≤
        2 * (5373952 * Real.sqrt 2032129 + 1) /
          (selectedFerrersPaperLambda k * Real.sqrt (selectedFerrersPaperLambda k)) := hkTop
      _ ≤ 2 * (5373952 * Real.sqrt 2032129 + 1) := by
          apply div_le_self (by positivity) hden
      _ = Etop := by rw [hEtopdef]
  -- junk constant collapses to `1020 Cχ`
  have hCjunk_le : Cjunk ≤ 1020 * Cχ := by
    rw [hCjunkdef]
    have hp := hkχ.1
    have hq := hkχ.2
    rw [abs_sub_comm (1 : ℝ)] at hp hq
    rw [hpaper_eq] at hp hq
    have hlm2 : (0 : ℝ) < lam ^ 2 := by positivity
    have hlmeq : lambda_m (selectedFerrersPreAnchorIndex k) = lam := hlam_eq
    rw [hlmeq]
    have hkey : ((1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| *
        4056 + (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| * 8) ≤
        1020 * (Cχ / lam ^ 2) := by
      nlinarith [hp, hq]
    calc ((1 / 4) * |(selectedFerrersPreAnchorPair k).chi0 - 1| * 4056 +
        (3 / 4) * |(selectedFerrersPreAnchorPair k).chi2 - 1| * 8) *
        lam ^ 2 ≤ (1020 * (Cχ / lam ^ 2)) * lam ^ 2 := by
          apply mul_le_mul_of_nonneg_right hkey hlm2.le
      _ = 1020 * Cχ := by
          field_simp
  have hV4' : (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
      Cjunk * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) ≤
      2040 * Cχ * Real.sqrt lam := by
    have hs0 : (0 : ℝ) ≤ Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k)) :=
      Real.sqrt_nonneg _
    have hstep2 : Cjunk * (2 * Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))) ≤
        (1020 * Cχ) * (2 * Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))) := by
      apply mul_le_mul_of_nonneg_right hCjunk_le (by positivity)
    have hlmeq : lambda_m (selectedFerrersPreAnchorIndex k) = lam := hlam_eq
    rw [hlmeq] at hstep2
    calc (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        Cjunk * (Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))⁻¹) ≤
        Cjunk * (2 * Real.sqrt (lambda_m (selectedFerrersPreAnchorIndex k))) := hV4
      _ = Cjunk * (2 * Real.sqrt lam) := by rw [hlam_eq]
      _ ≤ (1020 * Cχ) * (2 * Real.sqrt lam) := hstep2
      _ = 2040 * Cχ * Real.sqrt lam := by ring
  -- the log comparison and unit factors
  have hm2R : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
    have : (2 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hlogpos : (0 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlogcmp : Real.sqrt ((1 / 2) *
      Real.log (((k + 2 : ℕ) : ℝ) + 1)) ≤
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    apply Real.sqrt_le_sqrt
    have h1 : ((k + 2 : ℕ) : ℝ) + 1 ≤ ((k + 2 : ℕ) : ℝ) ^ 2 := by
      nlinarith
    have h2 : Real.log (((k + 2 : ℕ) : ℝ) + 1) ≤
        Real.log (((k + 2 : ℕ) : ℝ) ^ 2) :=
      Real.log_le_log (by linarith) h1
    have h3 : Real.log (((k + 2 : ℕ) : ℝ) ^ 2) =
        2 * Real.log ((k + 2 : ℕ) : ℝ) := by
      rw [Real.log_pow]
      norm_num
    linarith
  have hF1 : (1 : ℝ) ≤ Real.sqrt lam := by
    apply Real.one_le_sqrt.mpr hlam1
  have hF2 : (1 : ℝ) ≤
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    apply Real.one_le_sqrt.mpr
    linarith
  have hFF : (1 : ℝ) ≤ Real.sqrt lam *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    nlinarith
  have hsqlam_eq : Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) =
      Real.sqrt lam := by rw [hlamdef]
  -- per-term majorization by the common factor
  have hT1 : DH ≤ DH * (Real.sqrt lam *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
    le_mul_of_one_le_right hDH0 hFF
  have hTl1 : (Bl1 + Al1) / 2 ≤ ((Bl1 + Al1) / 2) * (Real.sqrt lam *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
    le_mul_of_one_le_right (by linarith) hFF
  have hT5 : Etop ≤ Etop * (Real.sqrt lam *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
    le_mul_of_one_le_right hEtop0 hFF
  have hkeyF : Real.sqrt ((1 / 2) *
      Real.log (((k + 2 : ℕ) : ℝ) + 1)) ≤
      Real.sqrt lam * Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    calc Real.sqrt ((1 / 2) * Real.log (((k + 2 : ℕ) : ℝ) + 1)) ≤
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := hlogcmp
      _ = 1 * Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) :=
        (one_mul _).symm
      _ ≤ Real.sqrt lam *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hF1 (Real.sqrt_nonneg _)
  have hT2 : (1 / 4) * (2 * Real.sqrt ((1 / 2) *
      Real.log (((k + 2 : ℕ) : ℝ) + 1)) * Real.sqrt (CE4 + 1)) ≤
      ((1 / 2) * Real.sqrt (CE4 + 1)) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
    have h := mul_le_mul_of_nonneg_right hkeyF
      (Real.sqrt_nonneg (CE4 + 1))
    nlinarith [h]
  have hT3 : (3 / 4) * (2 * Real.sqrt ((1 / 2) *
      Real.log (((k + 2 : ℕ) : ℝ) + 1)) * Real.sqrt (CE0 + 1)) ≤
      ((3 / 2) * Real.sqrt (CE0 + 1)) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
    have h := mul_le_mul_of_nonneg_right hkeyF
      (Real.sqrt_nonneg (CE0 + 1))
    nlinarith [h]
  have hT4 : 2040 * Cχ * Real.sqrt lam ≤
      (2040 * Cχ) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
    have h1 : (0 : ℝ) ≤ 2040 * Cχ * Real.sqrt lam := by positivity
    have h := mul_le_mul_of_nonneg_left hF2 h1
    nlinarith [h]
  have hAsum : A * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) =
      ((Bl1 + Al1) / 2) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      DH * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      ((1 / 2) * Real.sqrt (CE4 + 1)) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      ((3 / 2) * Real.sqrt (CE0 + 1)) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      (2040 * Cχ) * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      Etop * (Real.sqrt lam *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
    rw [hsqlam_eq, hAdef]
    ring
  rw [hsqlam_eq, hAsum, ← hsqlam_eq]
  calc selectedFerrersAbelLogDerivativeBudget k ≤
      (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        ((1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖ +
          Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
              etw_Q k (((n : ℕ) : ℝ) *
                (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖)) := hreduced
    _ = (∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
        (1 / 2) * ‖selectedFerrersAbelLogRepresentative k x‖) +
        ∫ x in (0 : ℝ)..L_m (selectedFerrersPreAnchorIndex k),
          Real.sqrt (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)) *
            ‖∑ n ∈ sourcePositiveIndexFinset
                (selectedFerrersPreAnchorIndex k),
              etw_Q k (((n : ℕ) : ℝ) *
                (Real.exp x / lambda_m (selectedFerrersPreAnchorIndex k)))‖ := hsplit
    _ ≤ _ := by
        rw [hsqlam_eq]
        linarith [hp1val, hmono, hV1, hV2, hV3, hV4', hV5,
          hT1, hTl1, hT5, hT2, hT3, hT4]

/-! ### S4: the Fourier decay budget at the honest growing rate -/

set_option maxHeartbeats 2000000 in
/-- Mirror of the committed uniform closure with the discharged growing
derivative budget. -/
private theorem etw13_fourier_budget_rate
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
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
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ k in Filter.atTop,
      selectedFerrersAbelFourierDecayBudget k ≤
        A * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) := by
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
  obtain ⟨Abud, hAbud0, hbud⟩ := etw10_budget_rate C0 C4 Cχ Cθ
    hC0 hC4 hCχ hCθ hmode hχ hθ
  have hpi := Real.pi_pos
  refine ⟨2 * ((BL1 + AL1) +
      (Abud + (2 * AE + 2 * (CS + 132))) / (2 * Real.pi)),
    by positivity, ?_⟩
  filter_upwards [hL1, hends, hseam, hbud] with k hL1k hendsk hseamk hbudk
  have hs1 : (1 : ℝ) ≤ Real.sqrt (selectedFerrersPaperLambda k) := by
    apply Real.one_le_sqrt.mpr
    rw [selectedFerrersPaperLambda]
    have h1 : (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ k + 2 := Nat.le_add_left 1 (k + 1)
      exact_mod_cast this
    simpa using Real.one_le_sqrt.mpr h1
  have hs0 : (0 : ℝ) < Real.sqrt (selectedFerrersPaperLambda k) :=
    lt_of_lt_of_le one_pos hs1
  have hdrop : ∀ {c : ℝ}, 0 ≤ c →
      c / Real.sqrt (selectedFerrersPaperLambda k) ≤ c := fun {c} hc =>
    div_le_self hc hs1
  have hlameq : lambda_m (selectedFerrersPreAnchorIndex k) =
      selectedFerrersPaperLambda k :=
    selectedFerrersPaperLambda_eq_lambda_m k
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
  have hmass : (∫ x : ℝ, ‖selectedFerrersAbelLogZeroExtension k x‖) ≤
      BL1 + AL1 := by
    refine le_trans hL1k ?_
    have := hdrop hAL1
    linarith
  rw [selectedFerrersAbelFourierDecayBudget]
  have hF1' : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) := by
    apply Real.one_le_sqrt.mpr
    apply Real.one_le_sqrt.mpr
    have : (1 : ℕ) ≤ k + 2 := by omega
    exact_mod_cast this
  have hF2' : (1 : ℝ) ≤
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    apply Real.one_le_sqrt.mpr
    have hln : (0 : ℝ) ≤ Real.log ((k + 2 : ℕ) : ℝ) := by
      apply Real.log_nonneg
      have : (1 : ℕ) ≤ k + 2 := by omega
      exact_mod_cast this
    linarith
  have hFF' : (1 : ℝ) ≤ Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
      Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2) := by
    nlinarith
  have hc0 : (0 : ℝ) ≤ 2 * AE + 2 * (CS + 132) := by linarith
  have hsum : selectedFerrersAbelLogDerivativeBudget k +
      selectedFerrersAbelLogJumpBudget k ≤
      Abud * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        (2 * AE + 2 * (CS + 132)) := add_le_add hbudk hjump
  have hdiv : (selectedFerrersAbelLogDerivativeBudget k +
      selectedFerrersAbelLogJumpBudget k) / (2 * Real.pi) ≤
      (Abud * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        (2 * AE + 2 * (CS + 132))) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right hsum
    positivity
  have hcF : (2 * AE + 2 * (CS + 132)) ≤
      (2 * AE + 2 * (CS + 132)) * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
    le_mul_of_one_le_right hc0 hFF'
  have hmF : (BL1 + AL1) ≤ (BL1 + AL1) * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
    le_mul_of_one_le_right (by linarith) hFF'
  have hdiv2 : (Abud * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      (2 * AE + 2 * (CS + 132))) / (2 * Real.pi) ≤
      (Abud * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        (2 * AE + 2 * (CS + 132)) * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))) / (2 * Real.pi) := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hring : 2 * ((BL1 + AL1) +
      (Abud + (2 * AE + 2 * (CS + 132))) / (2 * Real.pi)) *
      ((Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))) =
      2 * ((BL1 + AL1) * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))) +
      2 * ((Abud * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        (2 * AE + 2 * (CS + 132)) * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2))) /
        (2 * Real.pi)) := by
    field_simp
  rw [hring]
  linarith [hmass, hdiv, hdiv2, hmF]

/-! ### S5: the public ledger assembly -/

set_option maxHeartbeats 4000000 in
/-- **The W5 rate-ledger assembly** (verdict 66362fe1,
GOAL058_SELECTED_FERRERS_W5_RATE_ASSEMBLY).  The production selected
projection tail decays, from exactly the frozen inputs: the family
crosswalk, the F72.6 mode rates, the χ-defect rates and the node-1
eigenvalue-defect rates.  All Sturm-energy instantiation, two-mode
recombination, explicit-`H`, seam and strict-top budgets and the squared
rate/bandwidth limit are internal; no new analytic supplier is assumed. -/
theorem selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
    (S : ProlateCanonicalSourceData)
    (hFamily : SelectedFerrersPreAnchorProductionFamilyCrosswalk S)
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
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
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    SelectedProjectionTailDecay S := by
  obtain ⟨AF, hAF0, hCb⟩ := etw13_fourier_budget_rate C0 C4 Cχ Cθ
    hC0 hC4 hCχ hCθ hmode hχ hθ
  obtain ⟨Cp, hCp0, hCpRate⟩ :=
    selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
      C0 C4 Cχ hC0 hC4 hCχ hmode hχ
  have hCenter := etw2_center_bound hCpRate
  have hM := selectedFerrersSourceScale_inverse_bounded C0 C4 Cχ hmode hχ
  have hpi := Real.pi_pos
  apply selectedProjectionTailDecay_of_firstOrderCoefficientRate S
  refine ⟨fun k => 8 * (AF *
      (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
        Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
      Cp / (4 * Real.pi)), fun k => by positivity, ?_, ?_⟩
  · -- eventual squared coefficient bound
    filter_upwards [hFamily, hCb, hCenter, hM] with k hkF hkB hkC hkM
    obtain ⟨hidx, htrial⟩ := hkF
    intro n hn
    set i' := selectedFerrersPreAnchorIndex k with hi'
    have hnPre : n ∉ modeSet i' := by
      rw [← hidx]
      exact hn
    have hn0 : n ≠ 0 := by
      intro h0
      apply hnPre
      rw [h0]
      simp only [modeSet, Finset.mem_Icc]
      omega
    have hL' : 0 < L_m i' := logLength_pos i'
    have hLeq : L_m (selectedPairIndex S k) = L_m i' := by
      rw [hidx]
    have hcoeffEq :
        physicalFourierCoefficient (selectedPairIndex S k)
          (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
            (S.source.eStar_memLp (selectedPairIndex S k))) n =
        physicalFourierCoefficient i'
          (gTrial_m i' (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k)) n :=
      etw2_coeff_transport hidx htrial _ _ n
    have hnormEq :
        ‖physicalFourierCoefficient i'
          (gTrial_m i' (prolateCombination (selectedFerrersPreAnchorPair k))
            (selectedFerrersPreAnchorPair_eStar_memLp k)) n‖ =
        ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ *
          ‖physicalFourierCoefficient i' (selectedFerrersEStarHm k) n‖ := by
      rw [etw2_gTrial_eq_smul k]
      simp only [physicalFourierCoefficient]
      rw [inner_smul_right, norm_mul]
    have henv := selectedFerrersEStarHm_physicalCoefficient_le k n hn0
    have hlameq := selectedFerrersPaperLambda_eq_lambda_m k
    have hlam1 := etw2_paperLambda_one_le k
    have hlam0 : (0 : ℝ) < selectedFerrersPaperLambda k := by linarith
    have hsqrt_le :
        Real.sqrt (lambda_m i') ≤ (selectedFerrersPaperLambda k) ^ 2 := by
      rw [← hlameq]
      have h1 : Real.sqrt (selectedFerrersPaperLambda k) ≤
          Real.sqrt ((selectedFerrersPaperLambda k) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith)
      rw [Real.sqrt_sq hlam0.le] at h1
      calc
        Real.sqrt (selectedFerrersPaperLambda k) ≤
            selectedFerrersPaperLambda k := h1
        _ ≤ (selectedFerrersPaperLambda k) ^ 2 := by nlinarith
    have hcenterProd :
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
            Real.sqrt (lambda_m i') ≤ Cp := by
      calc
        ‖selectedFerrersLemma73SourcePacket k 0‖ *
            Real.sqrt (lambda_m i') ≤
          (Cp / (selectedFerrersPaperLambda k) ^ 2) *
            (selectedFerrersPaperLambda k) ^ 2 := by
            apply mul_le_mul hkC hsqrt_le (Real.sqrt_nonneg _)
            positivity
        _ = Cp := by
            field_simp
    have hcomb :
        selectedFerrersAbelFourierDecayBudget k +
          ‖selectedFerrersLemma73SourcePacket k 0‖ *
            Real.sqrt (lambda_m i') / (4 * Real.pi) ≤
        AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
          Cp / (4 * Real.pi) := by
      apply add_le_add hkB
      apply div_le_div_of_nonneg_right hcenterProd
      positivity
    have hnabs : (0 : ℝ) < |(n : ℝ)| := by
      rw [abs_pos]
      exact_mod_cast hn0
    have hnormFinal :
        ‖physicalFourierCoefficient (selectedPairIndex S k)
          (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
            (S.source.eStar_memLp (selectedPairIndex S k))) n‖ ≤
        8 * (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
          Cp / (4 * Real.pi)) * Real.sqrt (L_m i') / |(n : ℝ)| := by
      rw [hcoeffEq, hnormEq]
      calc
        ‖(selectedFerrersLemma73SourceScale k)⁻¹‖ *
            ‖physicalFourierCoefficient i' (selectedFerrersEStarHm k) n‖
            ≤ 8 * ((selectedFerrersAbelFourierDecayBudget k +
                ‖selectedFerrersLemma73SourcePacket k 0‖ *
                  Real.sqrt (lambda_m i') / (4 * Real.pi)) *
                Real.sqrt (L_m i') / |(n : ℝ)|) := by
              apply mul_le_mul hkM henv (norm_nonneg _) (by norm_num)
        _ ≤ 8 * ((AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
                Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
                Cp / (4 * Real.pi)) *
                Real.sqrt (L_m i') / |(n : ℝ)|) := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 8)
              apply div_le_div_of_nonneg_right _ hnabs.le
              exact mul_le_mul_of_nonneg_right hcomb (Real.sqrt_nonneg _)
        _ = 8 * (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
                Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
                Cp / (4 * Real.pi)) * Real.sqrt (L_m i') / |(n : ℝ)| := by
              ring
    have hCfin0 : (0 : ℝ) ≤ 8 * (AF *
        (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
        Cp / (4 * Real.pi)) := by positivity
    rw [hLeq]
    calc
      ‖physicalFourierCoefficient (selectedPairIndex S k)
          (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
            (S.source.eStar_memLp (selectedPairIndex S k))) n‖ ^ 2
          ≤ (8 * (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
              Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
              Cp / (4 * Real.pi)) *
              Real.sqrt (L_m i') / |(n : ℝ)|) ^ 2 := by
            apply sq_le_sq' _ hnormFinal
            have hnn2 : (0 : ℝ) ≤ 8 * (AF *
                (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
                  Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
                Cp / (4 * Real.pi)) *
                Real.sqrt (L_m i') / |(n : ℝ)| := by positivity
            have hnn : (0 : ℝ) ≤
                ‖physicalFourierCoefficient (selectedPairIndex S k)
                (gTrial_m (selectedPairIndex S k) (selectedProlateTrial S k)
                  (S.source.eStar_memLp (selectedPairIndex S k))) n‖ :=
              norm_nonneg _
            linarith
      _ = (8 * (AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
            Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
            Cp / (4 * Real.pi))) ^ 2 * L_m i' / (n : ℝ) ^ 2 := by
            rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt hL'.le, sq_abs]
  · -- the squared-rate/bandwidth limit
    have hband_eq : ∀ᶠ k : ℕ in Filter.atTop,
        (fun k : ℕ => (8 * (AF *
          (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
            Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
          Cp / (4 * Real.pi))) ^ 2 *
          (physicalFourierBandwidth (selectedPairIndex S k))⁻¹) k =
        (fun k : ℕ => (8 * (AF *
          (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
            Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) +
          Cp / (4 * Real.pi))) ^ 2 *
          (physicalFourierBandwidth (selectedFerrersPreAnchorIndex k))⁻¹)
          k := by
      filter_upwards [hFamily] with k hkF
      obtain ⟨hidx, -⟩ := hkF
      simp only [hidx]
    rw [Filter.tendsto_congr' hband_eq]
    have hbw : ∀ k : ℕ,
        physicalFourierBandwidth (selectedFerrersPreAnchorIndex k) =
        (2 * Real.pi * ((k + 3 : ℕ) : ℝ)) /
          Real.log ((k + 2 : ℕ) : ℝ) := by
      intro k
      rw [physicalFourierBandwidth]
      have hN : ((selectedFerrersPreAnchorIndex k).N + 1 : ℕ) = k + 3 :=
        rfl
      have hL : L_m (selectedFerrersPreAnchorIndex k) =
          Real.log ((k + 2 : ℕ) : ℝ) := rfl
      rw [hN, hL]
    set D0 : ℝ := 8 * (AF + Cp / (4 * Real.pi)) with hD0def
    have hD00 : 0 ≤ D0 := by
      rw [hD0def]
      positivity
    -- real-variable limit `(log x + 2)² / √x → 0`
    have hreal : Filter.Tendsto (fun x : ℝ =>
        (Real.log x + 2) ^ (2:ℕ) / x ^ ((1:ℝ)/2))
        Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun x : ℝ =>
          Real.log x ^ (2:ℕ) / x ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
        have h := isLittleO_log_rpow_rpow_atTop ((2:ℕ) : ℝ)
          (by norm_num : (0:ℝ) < 1/2)
        have h2 := h.tendsto_div_nhds_zero
        have hcong : ∀ᶠ x : ℝ in Filter.atTop,
            Real.log x ^ (((2:ℕ):ℝ)) / x ^ ((1:ℝ)/2) =
            Real.log x ^ (2:ℕ) / x ^ ((1:ℝ)/2) := by
          filter_upwards [] with x
          rw [Real.rpow_natCast]
        exact Filter.Tendsto.congr' hcong h2
      have h1 : Filter.Tendsto (fun x : ℝ =>
          Real.log x / x ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
        have h := isLittleO_log_rpow_atTop (by norm_num : (0:ℝ) < 1/2)
        exact h.tendsto_div_nhds_zero
      have h0 : Filter.Tendsto (fun x : ℝ => 4 / x ^ ((1:ℝ)/2))
          Filter.atTop (nhds 0) := by
        apply Filter.Tendsto.div_atTop tendsto_const_nhds
        exact tendsto_rpow_atTop (by norm_num)
      have hsum : Filter.Tendsto (fun x : ℝ =>
          Real.log x ^ (2:ℕ) / x ^ ((1:ℝ)/2) +
          4 * (Real.log x / x ^ ((1:ℝ)/2)) +
          4 / x ^ ((1:ℝ)/2)) Filter.atTop (nhds 0) := by
        have := (h2.add ((h1.const_mul 4))).add h0
        simpa using this
      apply hsum.congr'
      filter_upwards [Filter.eventually_gt_atTop (0:ℝ)] with x hx
      have hxp : (0:ℝ) < x ^ ((1:ℝ)/2) := Real.rpow_pos_of_pos hx _
      field_simp
      ring
    have hnat : Filter.Tendsto (fun k : ℕ => ((k + 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have heq : (fun k : ℕ => ((k + 2 : ℕ) : ℝ)) =
          fun k : ℕ => ((k : ℕ) : ℝ) + 2 := by
        funext k
        push_cast
        ring
      rw [heq]
      exact Filter.tendsto_atTop_add_const_right _ 2
        tendsto_natCast_atTop_atTop
    have hcomp := hreal.comp hnat
    have hlim := hcomp.const_mul (D0 ^ 2 / (2 * Real.pi))
    rw [mul_zero] at hlim
    apply squeeze_zero' (g := fun k : ℕ => D0 ^ 2 / (2 * Real.pi) *
      ((Real.log ((k + 2 : ℕ) : ℝ) + 2) ^ (2:ℕ) /
        ((k + 2 : ℕ) : ℝ) ^ ((1:ℝ)/2)))
    · filter_upwards [] with k
      have hb := hbw k
      rw [hb]
      have hm2 : (2 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) := by
        have : (2 : ℕ) ≤ k + 2 := by omega
        exact_mod_cast this
      have hlog0 : (0 : ℝ) < Real.log ((k + 2 : ℕ) : ℝ) := by
        apply Real.log_pos
        linarith
      have hinv0 : (0 : ℝ) ≤ ((2 * Real.pi * ((k + 3 : ℕ) : ℝ)) /
          Real.log ((k + 2 : ℕ) : ℝ))⁻¹ := by
        apply inv_nonneg.2
        apply div_nonneg _ hlog0.le
        positivity
      positivity
    · -- eventual dominating bound
      filter_upwards [Filter.eventually_ge_atTop 0] with k _hk
      set m : ℝ := ((k + 2 : ℕ) : ℝ) with hmdef
      have hm2 : (2 : ℝ) ≤ m := by
        rw [hmdef]
        have : (2 : ℕ) ≤ k + 2 := by omega
        exact_mod_cast this
      have hm0 : (0 : ℝ) < m := by linarith
      have hlog0 : (0 : ℝ) ≤ Real.log m := Real.log_nonneg (by linarith)
      have hsqm : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 hm0
      have hF1 : (1 : ℝ) ≤ Real.sqrt (Real.sqrt m) := by
        apply Real.one_le_sqrt.mpr
        apply Real.one_le_sqrt.mpr
        linarith
      have hF2 : (1 : ℝ) ≤ Real.sqrt (Real.log m + 2) := by
        apply Real.one_le_sqrt.mpr
        linarith
      have hFF : (1 : ℝ) ≤ Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2) := by nlinarith
      have hCk_le : 8 * (AF * (Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2)) + Cp / (4 * Real.pi)) ≤
          D0 * (Real.sqrt (Real.sqrt m) *
            Real.sqrt (Real.log m + 2)) := by
        rw [hD0def]
        have hcp : Cp / (4 * Real.pi) ≤ (Cp / (4 * Real.pi)) *
            (Real.sqrt (Real.sqrt m) * Real.sqrt (Real.log m + 2)) :=
          le_mul_of_one_le_right (by positivity) hFF
        nlinarith [hcp]
      have hCk0 : (0 : ℝ) ≤ 8 * (AF * (Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2)) + Cp / (4 * Real.pi)) := by
        positivity
      have hsq := pow_le_pow_left₀ hCk0 hCk_le 2
      have hF2eq : (D0 * (Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2))) ^ 2 =
          D0 ^ 2 * (Real.sqrt m * (Real.log m + 2)) := by
        have h1 : (Real.sqrt (Real.sqrt m)) ^ 2 = Real.sqrt m :=
          Real.sq_sqrt (Real.sqrt_nonneg m)
        have h2 : (Real.sqrt (Real.log m + 2)) ^ 2 = Real.log m + 2 :=
          Real.sq_sqrt (by linarith : (0:ℝ) ≤ Real.log m + 2)
        calc (D0 * (Real.sqrt (Real.sqrt m) *
            Real.sqrt (Real.log m + 2))) ^ 2 =
            D0 ^ 2 * ((Real.sqrt (Real.sqrt m)) ^ 2 *
              (Real.sqrt (Real.log m + 2)) ^ 2) := by ring
          _ = D0 ^ 2 * (Real.sqrt m * (Real.log m + 2)) := by
              rw [h1, h2]
      rw [hF2eq] at hsq
      have hbwk := hbw k
      rw [hbwk]
      have hk3 : ((k + 3 : ℕ) : ℝ) = m + 1 := by
        rw [hmdef]
        push_cast
        ring
      rw [hk3]
      have hlogpos : (0 : ℝ) < Real.log m := by
        apply Real.log_pos
        linarith
      have hinv_eq : ((2 * Real.pi * (m + 1)) / Real.log m)⁻¹ =
          Real.log m / (2 * Real.pi * (m + 1)) := by
        rw [inv_div]
      rw [hinv_eq]
      -- chain of scalar bounds
      have hb1 : (8 * (AF * (Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2)) + Cp / (4 * Real.pi))) ^ 2 *
          (Real.log m / (2 * Real.pi * (m + 1))) ≤
          (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
            (Real.log m / (2 * Real.pi * (m + 1))) := by
        apply mul_le_mul_of_nonneg_right hsq
        positivity
      have hb2 : (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
          (Real.log m / (2 * Real.pi * (m + 1))) ≤
          (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
            ((Real.log m + 2) / (2 * Real.pi * m)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply div_le_div₀ (by positivity) (by linarith)
          (by positivity) (by nlinarith [Real.pi_pos])
      have hsm : Real.sqrt m * Real.sqrt m = m := Real.mul_self_sqrt hm0.le
      have hb3 : (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
          ((Real.log m + 2) / (2 * Real.pi * m)) =
          D0 ^ 2 / (2 * Real.pi) *
            ((Real.log m + 2) ^ (2:ℕ) / Real.sqrt m) := by
        field_simp
        nlinarith [hsm, sq_nonneg (Real.log m + 2)]
      have hrpow : Real.sqrt m = m ^ ((1:ℝ)/2) := by
        rw [Real.sqrt_eq_rpow]
      calc (8 * (AF * (Real.sqrt (Real.sqrt m) *
          Real.sqrt (Real.log m + 2)) + Cp / (4 * Real.pi))) ^ 2 *
          (Real.log m / (2 * Real.pi * (m + 1))) ≤
          (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
            (Real.log m / (2 * Real.pi * (m + 1))) := hb1
        _ ≤ (D0 ^ 2 * (Real.sqrt m * (Real.log m + 2))) *
            ((Real.log m + 2) / (2 * Real.pi * m)) := hb2
        _ = D0 ^ 2 / (2 * Real.pi) *
            ((Real.log m + 2) ^ (2:ℕ) / Real.sqrt m) := hb3
        _ = D0 ^ 2 / (2 * Real.pi) *
            ((Real.log m + 2) ^ (2:ℕ) / m ^ ((1:ℝ)/2)) := by
            rw [hrpow]
    · simpa [Function.comp] using hlim

#print axioms selectedProjectionTailDecay_of_selectedFerrersW5RateLedger
#print axioms etw13_fourier_budget_rate
#print axioms etw10_budget_rate

/-! ### S6: public quantitative export (verdict REQ-2026-08-26-J) -/

/-- **Public Abel-budget rate export.**  A thin wrapper around the internal
`etw13_fourier_budget_rate`: it re-exports the already-kernel-green
quantitative decay budget for the N2 consumer.  No W5 analysis is reopened;
no existing declaration is touched. -/
theorem selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates
    (C0 C4 Cχ Cθ : ℝ) (hC0 : 0 ≤ C0) (hC4 : 0 ≤ C4) (hCχ : 0 ≤ Cχ)
    (hCθ : 0 ≤ Cθ)
    (hmode : ∀ᶠ k in Filter.atTop,
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
    (hχ : ∀ᶠ k in Filter.atTop,
      |1 - (selectedFerrersPreAnchorPair k).chi0| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2 ∧
        |1 - (selectedFerrersPreAnchorPair k).chi2| ≤
          Cχ / (selectedFerrersPaperLambda k) ^ 2)
    (hθ : ∀ᶠ k in Filter.atTop,
      |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 0 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (2 * Real.pi)| ≤ Cθ ∧
        |mode4ClassicalEvenEigenvalue (mode4JacobiG (k + 2)) 2 +
          mode4JacobiG (k + 2) - ((k + 2 : ℕ) : ℝ) * (18 * Real.pi)| ≤
          Cθ) :
    ∃ AF : ℝ, 0 ≤ AF ∧ ∀ᶠ k in Filter.atTop,
      selectedFerrersAbelFourierDecayBudget k ≤
        AF * (Real.sqrt (Real.sqrt ((k + 2 : ℕ) : ℝ)) *
          Real.sqrt (Real.log ((k + 2 : ℕ) : ℝ) + 2)) :=
  etw13_fourier_budget_rate C0 C4 Cχ Cθ hC0 hC4 hCχ hCθ hmode hχ hθ

#print axioms selectedFerrersAbelFourierDecayBudget_rate_of_modeChiThetaRates

end Q3.RouteB.D0Pstar
