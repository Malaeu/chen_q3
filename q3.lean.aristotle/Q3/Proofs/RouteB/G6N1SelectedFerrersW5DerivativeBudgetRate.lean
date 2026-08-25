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

end Q3.RouteB.D0Pstar
