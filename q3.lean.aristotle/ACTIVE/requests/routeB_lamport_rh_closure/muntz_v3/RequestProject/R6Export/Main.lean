/-
Provenance source: q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/muntz_r6/RequestProject/Main.lean
Provenance SHA-256: 58f5f30907c64494416301539414270f64e51864d2b4570ed70bd471446efb92
exported verbatim, imports renamed only
Export date: 2026-07-31
-/

import Mathlib
import RequestProject.R6Export.RiemannBoundaryCellBridge

open MeasureTheory Set Filter Complex
open scoped BigOperators ENNReal NNReal Topology

namespace EStarMuntzZeroMassContinuation.R6Export

noncomputable def Estar (h : ℝ → ℂ) (u : ℝ) : ℂ :=
  Real.sqrt u * ∑' n : ℕ+, h (n * u)

noncomputable def Mellin (k : ℝ → ℂ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi (0 : ℝ), k u * (u : ℂ) ^ (s - 1)

noncomputable def Gwin (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (Λ⁻¹) Λ, Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rminus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioo (0 : ℝ) (Λ⁻¹), Estar h u * (u : ℂ) ^ (s - 1)

noncomputable def Rplus (h : ℝ → ℂ) (Λ : ℝ) (s : ℂ) : ℂ :=
  ∫ u in Set.Ioi Λ, Estar h u * (u : ℂ) ^ (s - 1)

/-- The corrected point-value convention for the zeta--Mellin product. -/
noncomputable def ZetaMellinReg (h : ℝ → ℂ) (w : ℂ) : ℂ :=
  if w = 1 then deriv (Mellin h) 1 else riemannZeta w * Mellin h w

/-- T1's pointwise tail statement, valid when the support begins at zero. -/
theorem Estar_eq_zero_of_gt
    (h : ℝ → ℂ) (b u : ℝ) (hb : 0 ≤ b)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0) (hu : b < u) :
    Estar h u = 0 := by
  unfold Estar
  suffices ∀ n : ℕ+, h (n * u) = 0 by simp [this]
  intro n
  apply hsupp
  simp only [Set.mem_Icc, not_and_or]
  right
  have hn : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast n.prop
  nlinarith

/-- T2: zero mass bounds all positive-mesh dilation sums uniformly. -/
theorem dilation_sum_bounded_of_zeroMass
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) :
    ∃ C : ℝ, ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ‖∑' n : ℕ+, h ((n : ℝ) * u)‖ ≤ C := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsupp0 : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0 := by
    intro v hv
    apply hsupp
    intro hvab
    apply hv
    exact ⟨ha.le.trans hvab.1, hvab.2⟩
  refine ⟨(K : ℝ) * b + (‖h 0‖ + (K : ℝ) * b) + ‖h b‖, ?_⟩
  intro u hu
  exact riemannBoundaryCellBridge_zeroMass h b hb K hsupp0
    (fun x _ y _ => hlip x y) hlip.continuous.measurable hmass u hu.1

/-- T2's stated corollary for `Estar`. -/
theorem Estar_bounded_by_sqrt_of_zeroMass
    (h : ℝ → ℂ) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (K : NNReal)
    (hsupp : ∀ v, v ∉ Set.Icc a b → h v = 0)
    (hlip : LipschitzWith K h)
    (hmass : ∫ v in Set.Ioi (0 : ℝ), h v = 0) :
    ∃ C : ℝ, ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      ‖Estar h u‖ ≤ C * Real.sqrt u := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hsupp0 : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0 := by
    intro v hv
    apply hsupp
    intro hvab
    apply hv
    exact ⟨ha.le.trans hvab.1, hvab.2⟩
  refine ⟨(K : ℝ) * b + (‖h 0‖ + (K : ℝ) * b) + ‖h b‖, ?_⟩
  intro u hu
  change ‖_root_.Estar h u‖ ≤ _
  exact riemannBoundaryCellBridge_Estar h b hb K hsupp0
    (fun x _ y _ => hlip x y) hlip.continuous.measurable hmass u hu

/-- The obstruction at the requested removable singularity. Mathlib's
`riemannZeta` has an assigned finite value at `1`; multiplying the literal
function by a function with a simple zero therefore has the wrong point value. -/
theorem zeta_product_not_continuousAt_of_simple_zero
    (M : ℂ → ℂ) (d : ℂ) (hM0 : M 1 = 0)
    (hMderiv : HasDerivAt M d 1) (hd : d ≠ 0) :
    ¬ ContinuousAt (fun w : ℂ => riemannZeta w * M w) 1 := by
  intro hcont
  have hslope : Tendsto (slope M 1) (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds d) :=
    hasDerivAt_iff_tendsto_slope.mp hMderiv
  have hprod : Tendsto (fun w : ℂ => riemannZeta w * M w)
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds d) := by
    have hmul := riemannZeta_residue_one.mul hslope
    have heq : (fun w : ℂ => (w - 1) * riemannZeta w * slope M 1 w) =ᶠ[
        nhdsWithin 1 ({1}ᶜ : Set ℂ)] (fun w => riemannZeta w * M w) := by
      have hmem : ∀ᶠ w : ℂ in nhdsWithin 1 ({1}ᶜ : Set ℂ), w ∈ ({1}ᶜ : Set ℂ) :=
        self_mem_nhdsWithin
      filter_upwards [hmem] with w hw
      have hw1 : w - 1 ≠ 0 := sub_ne_zero.mpr hw
      simp only [slope, hM0, vsub_eq_sub, sub_zero, smul_eq_mul]
      field_simp
    simpa using hmul.congr' heq
  have hzero : Tendsto (fun w : ℂ => riemannZeta w * M w)
      (nhdsWithin 1 ({1}ᶜ : Set ℂ)) (nhds 0) := by
    convert hcont.tendsto.mono_left inf_le_left using 1
    simp [hM0]
  exact hd (tendsto_nhds_unique hprod hzero)

/-- Shifted form of `zeta_product_not_continuousAt_of_simple_zero`, at the
point `s = 1/2` occurring in the requested declaration T4. -/
theorem shifted_zeta_product_not_continuousAt_of_simple_zero
    (M : ℂ → ℂ) (d : ℂ) (hM0 : M 1 = 0)
    (hMderiv : HasDerivAt M d 1) (hd : d ≠ 0) :
    ¬ ContinuousAt (fun s : ℂ => riemannZeta (s + (1 : ℂ) / 2) * M (s + (1 : ℂ) / 2))
        ((1 : ℂ) / 2) := by
  intro hs
  apply zeta_product_not_continuousAt_of_simple_zero M d hM0 hMderiv hd
  have hg : ContinuousAt (fun w : ℂ => w - (1 : ℂ) / 2) 1 :=
    continuousAt_id.sub continuousAt_const
  have hgt : Tendsto (fun w : ℂ => w - (1 : ℂ) / 2) (nhds 1) (nhds ((1 : ℂ) / 2)) := by
    convert hg.tendsto using 1 <;> norm_num
  have hc := hs.tendsto.comp hgt
  change Tendsto (fun w : ℂ => riemannZeta w * M w) (nhds 1)
    (nhds (riemannZeta 1 * M 1))
  convert hc using 1 <;> norm_num [Function.comp_def]

end EStarMuntzZeroMassContinuation.R6Export
