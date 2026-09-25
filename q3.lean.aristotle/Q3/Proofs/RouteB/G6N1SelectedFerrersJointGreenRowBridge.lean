import Q3.Proofs.RouteB.G6N1SelectedFerrersFiniteCCMSourceRow
import Q3.Proofs.RouteB.EStarWindowedMellinCrosswalk

set_option linter.mathlibStandardSet false
set_option relaxedAutoImplicit false
set_option autoImplicit false

open Complex MeasureTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Q3.RouteB.D0Pstar

open Q3.RouteB

/-!
# Selected Ferrers coefficient to its window Mellin coordinate

This module removes the finite projection from a selected coefficient and
retains its exact normalizer. The further equality with a paired-window Mellin
sum is not established here.

No coefficient row is replaced by an arbitrary unit vector.
-/

private lemma selectedFerrers_inner_V_P_eq
    (i : PairIndex) (x : H_m i) {n : ℤ}
    (hn : n ∈ modeSet i) :
    inner ℂ (V_n_m i n) ((P_m_N i x : H_m i)) =
      inner ℂ (V_n_m i n) x := by
  classical
  rw [coe_P_m_N_apply_eq_sum_inner_V_n_m_smul, inner_sum]
  simp_rw [inner_smul_right,
    orthonormal_iff_ite.mp (V_n_m_orthonormal i), mul_ite, mul_one,
    mul_zero]
  rw [Finset.sum_ite_eq (modeSet i) n
    (fun r => inner ℂ (V_n_m i r) x), if_pos hn]

private lemma selectedFerrers_c_n_eq_smul_inner
    (i : PairIndex) (h : ℝ → ℂ)
    (hLp : MemLp (E_star h) 2 (dStar.restrict (I_m i)))
    (hNz : TrialNonzero i h hLp) {n : ℤ}
    (hn : n ∈ modeSet i) :
    c_n i h hLp hNz n =
      ((sTrial_m_N i h hLp hNz : ℝ) : ℂ) *
        inner ℂ (V_n_m i n) (gTrial_m i h hLp) := by
  unfold c_n kTrial_m_N
  rw [Submodule.coe_smul, inner_smul_right]
  congr 1
  exact selectedFerrers_inner_V_P_eq i _ hn

/-- The literal selected coefficient equals the normalizer times the
unprojected source pairing at every carrier index. This is a source-specific
intermediate, not the paired-window integral formula. -/
theorem selectedFerrersFiniteCCMRow_eq_normalizedUnprojectedInner
    (P : CCMLemma73PreAnchorPort selectedFerrersPreAnchorData)
    (k : ℕ)
    (j : CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N) :
    selectedFerrersFiniteCCMRow P k j =
      ((sTrial_m_N ((selectedFerrersCofinalSourceData P).index k)
          (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
          ((selectedFerrersCofinalSourceData P).eStar_memLp k)
          ((selectedFerrersCofinalSourceData P).trialNonzero k) : ℝ) : ℂ) *
        inner ℂ
          (V_n_m ((selectedFerrersCofinalSourceData P).index k)
            (ccmModeFinite ((selectedFerrersCofinalSourceData P).index k).N j))
          (gTrial_m ((selectedFerrersCofinalSourceData P).index k)
            (prolateCombination ((selectedFerrersCofinalSourceData P).pair k))
            ((selectedFerrersCofinalSourceData P).eStar_memLp k)) := by
  let i := (selectedFerrersCofinalSourceData P).index k
  let h := prolateCombination ((selectedFerrersCofinalSourceData P).pair k)
  have hn : ccmModeFinite i.N j ∈ modeSet i := by
    unfold modeSet
    exact Finset.mem_Icc.mpr (ccmModeFinite_range i.N j)
  simpa only [selectedFerrersFiniteCCMRow_apply] using
    selectedFerrers_c_n_eq_smul_inner i h
      ((selectedFerrersCofinalSourceData P).eStar_memLp k)
      ((selectedFerrersCofinalSourceData P).trialNonzero k) hn

#print axioms selectedFerrersFiniteCCMRow_eq_normalizedUnprojectedInner

end Q3.RouteB.D0Pstar
