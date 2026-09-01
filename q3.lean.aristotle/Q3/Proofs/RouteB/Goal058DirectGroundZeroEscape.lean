import Q3.Proofs.RouteB.CenteredXiZeroNonzero
import Q3.Proofs.RouteB.GenericZeroTransfer

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-!
# Goal 058 — direct tracked-ground ZeroEscape consumer

This theorem is the terminal consumer for one exact family.  It bypasses the
older six-slot conditional roof: entire approximants with real zero sets and
locally uniform convergence to `centeredXi` on the centered critical strip
already imply `Q3.RH` through the checked Hurwitz/ZeroEscape interface.

It does not construct the family or supply any sector floor, residual rate,
compact envelope, or normalization theorem.
-/

/-- One entire real-zero family converging locally uniformly to `centeredXi`
on the centered critical strip implies the project RH proposition. -/
theorem rh_of_real_zero_family_tendsto_centeredXi
    (F : ℕ → ℂ → ℂ)
    (hzeros : ∀ k, ZerosRealOn Set.univ (F k))
    (hentire : ∀ k, Differentiable ℂ (F k))
    (hconv : TendstoLocallyUniformlyOn
      F centeredXi Filter.atTop centeredCriticalStrip) :
    Q3.RH := by
  have hXi_ne : centeredXi ≠ 0 := by
    intro hzero
    exact centeredXi_zero_ne_zero (congrFun hzero 0)
  have happroach :
      ZerosApproachOn centeredCriticalStrip F centeredXi :=
    zerosApproachOn_of_tendstoLocallyUniformlyOn
      (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
      (fun _ hz => hz) hentire
      differentiable_centeredXi hconv hXi_ne
  have hreal : ZerosRealOn centeredCriticalStrip centeredXi :=
    zerosRealOn_of_zerosApproachOn
      centeredCriticalStrip F centeredXi hzeros happroach
  apply rh_iff_centeredXi_zeros_real.mpr
  intro z hz hzstrip
  exact hreal z hzstrip hz

#print axioms rh_of_real_zero_family_tendsto_centeredXi

end Q3.RouteB
