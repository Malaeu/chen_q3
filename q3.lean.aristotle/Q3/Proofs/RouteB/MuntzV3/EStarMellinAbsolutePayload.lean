/-
Production port source: ACTIVE/requests/routeB_lamport_rh_closure/muntz_v3/RequestProject/MuntzV3EStarMellinAbsolutePayload.lean
Source SHA-256: 1f460d77a2404cbec83b739a188092e175cc73545fd8b31f5c493f62fafa6d89
Body copied byte-for-byte; import path rewritten only.
Port date: 2026-08-06
-/

import Q3.Proofs.RouteB.MuntzV3.Core

open scoped BigOperators Topology ENNReal
open Set Filter MeasureTheory Complex Asymptotics

namespace EStarMuntzZeroMassContinuation

private lemma mellinConvergent_base_exactClass
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) :
    MellinConvergent h p := by
  let C : ℝ := ‖h 0‖ + (K : ℝ) * |b|
  have hbabs : 0 ≤ |b| := hb.trans (le_abs_self b)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact add_nonneg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg K) hbabs)
  have hbound_Ico : ∀ u ∈ Set.Ico (0 : ℝ) b, ‖h u‖ ≤ C := by
    intro u hu
    have hb' : 0 < b := lt_of_le_of_lt hu.1 hu.2
    have hdist := hlip.dist_le_mul u hu 0 ⟨le_rfl, hb'⟩
    calc
      ‖h u‖ ≤ dist (h u) (h 0) + ‖h 0‖ := by
        rw [dist_eq_norm]
        exact norm_le_norm_sub_add _ _
      _ ≤ (K : ℝ) * dist u 0 + ‖h 0‖ := by gcongr
      _ ≤ (K : ℝ) * |b| + ‖h 0‖ := by
        gcongr
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hu.1, abs_of_pos hb']
        exact hu.2.le
      _ = C := by simp [C, add_comm]
  have hbound_ae : ∀ᵐ u : ℝ, ‖h u‖ ≤ C := by
    have hb_ae : ∀ᵐ u : ℝ, u ≠ b := by simp [ae_iff, measure_singleton]
    filter_upwards [hb_ae] with u hub
    by_cases hu : u ∈ Set.Icc (0 : ℝ) b
    · exact hbound_Ico u ⟨hu.1, lt_of_le_of_ne hu.2 hub⟩
    · simpa [hsupp u hu] using hC
  have hlocal : LocallyIntegrableOn h (Set.Ioi 0) := by
    apply (locallyIntegrableOn_const C).mono hmeas.aestronglyMeasurable
    filter_upwards [hbound_ae] with u hu
    simpa [Real.norm_eq_abs, abs_of_nonneg hC] using hu
  have htop : h =O[atTop] (fun x : ℝ => x ^ (-(p.re + 1))) := by
    apply (isBigO_zero (fun x : ℝ => x ^ (-(p.re + 1))) atTop).congr'
    · filter_upwards [eventually_gt_atTop b] with x hx
      symm
      apply hsupp
      simp only [Set.mem_Icc, not_and_or]
      exact Or.inr (not_le.mpr hx)
    · rfl
  have hbot : h =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
    rw [isBigO_iff]
    refine ⟨C, ?_⟩
    by_cases hbpos : 0 < b
    · filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds (Iio_mem_nhds hbpos)] with u hu hub
      simpa [Real.norm_eq_abs, abs_of_nonneg hC] using
        hbound_Ico u ⟨hu.le, hub⟩
    · filter_upwards [self_mem_nhdsWithin] with u hu
      have hout : u ∉ Set.Icc (0 : ℝ) b := by
        simp only [Set.mem_Icc, not_and_or]
        exact Or.inr (not_le.mpr (lt_of_le_of_lt (not_lt.mp hbpos) hu))
      simpa [hsupp u hout] using hC
  exact mellinConvergent_of_isBigO_rpow hlocal htop (by linarith)
    hbot (by linarith)

private lemma mellin_base_lintegral_ne_top
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) :
    (∫⁻ v : ℝ, ‖(v : ℂ) ^ (p - 1) • h v‖ₑ
      ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤ := by
  have hconv := mellinConvergent_base_exactClass h b K hb hmeas hsupp hlip p hp
  change IntegrableOn (fun v : ℝ => (v : ℂ) ^ (p - 1) • h v) (Set.Ioi 0) at hconv
  exact (hasFiniteIntegral_iff_enorm.mp hconv.2).ne

private lemma mellin_dilate_aestronglyMeasurable
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) (n : ℕ+) :
    AEStronglyMeasurable
      (fun u : ℝ => (u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u))
      (volume.restrict (Set.Ioi 0)) := by
  have hnpos : 0 < ((n : ℕ) : ℝ) := by positivity
  have hconv := (MellinConvergent.comp_mul_left hnpos).2
    (mellinConvergent_base_exactClass h b K hb hmeas hsupp hlip p hp)
  change IntegrableOn
    (fun u : ℝ => (u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u))
    (Set.Ioi 0) at hconv
  exact hconv.1

private lemma mellin_dilate_lintegral_eq
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) (n : ℕ+) :
    (∫⁻ u : ℝ, ‖(u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u)‖ₑ
      ∂(volume.restrict (Set.Ioi 0))) =
      ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-p.re)) *
        (∫⁻ v : ℝ, ‖(v : ℂ) ^ (p - 1) • h v‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) := by
  let a : ℝ := ((n : ℕ) : ℝ)
  have ha : 0 < a := by positivity
  have hbase := mellinConvergent_base_exactClass h b K hb hmeas hsupp hlip p hp
  change IntegrableOn (fun v : ℝ => (v : ℂ) ^ (p - 1) • h v) (Set.Ioi 0) at hbase
  have hscaled := (MellinConvergent.comp_mul_left ha).2
    (mellinConvergent_base_exactClass h b K hb hmeas hsupp hlip p hp)
  change IntegrableOn
    (fun u : ℝ => (u : ℂ) ^ (p - 1) • h (a * u))
    (Set.Ioi 0) at hscaled
  have hnorm :
      Set.EqOn
        (fun u : ℝ => ‖(u : ℂ) ^ (p - 1) • h (a * u)‖)
        (fun u : ℝ => a ^ (1 - p.re) *
          ‖((a * u : ℝ) : ℂ) ^ (p - 1) • h (a * u)‖)
        (Set.Ioi 0) := by
    intro u hu
    change ‖(u : ℂ) ^ (p - 1) • h (a * u)‖ =
      a ^ (1 - p.re) * ‖((a * u : ℝ) : ℂ) ^ (p - 1) • h (a * u)‖
    rw [norm_smul, norm_smul,
      norm_cpow_eq_rpow_re_of_pos hu,
      norm_cpow_eq_rpow_re_of_pos (mul_pos ha hu)]
    simp only [sub_re, one_re]
    rw [Real.mul_rpow ha.le hu.le]
    have hexp : (1 - p.re) + (p.re - 1) = 0 := by ring
    have hcancel : a ^ (1 - p.re) * a ^ (p.re - 1) = 1 := by
      rw [← Real.rpow_add ha, hexp]
      simp
    calc
      u ^ (p.re - 1) * ‖h (a * u)‖ =
          (a ^ (1 - p.re) * a ^ (p.re - 1)) *
            (u ^ (p.re - 1) * ‖h (a * u)‖) := by rw [hcancel, one_mul]
      _ = a ^ (1 - p.re) *
          (a ^ (p.re - 1) * u ^ (p.re - 1) * ‖h (a * u)‖) := by ring
  have hreal :
      (∫ u in Set.Ioi (0 : ℝ),
          ‖(u : ℂ) ^ (p - 1) • h (a * u)‖) =
        a ^ (-p.re) *
          ∫ v in Set.Ioi (0 : ℝ), ‖(v : ℂ) ^ (p - 1) • h v‖ := by
    rw [setIntegral_congr_fun measurableSet_Ioi hnorm]
    rw [MeasureTheory.integral_const_mul]
    rw [integral_comp_mul_left_Ioi
      (fun v : ℝ => ‖(v : ℂ) ^ (p - 1) • h v‖) 0 ha]
    simp only [mul_zero, smul_eq_mul]
    rw [← mul_assoc]
    congr 1
    rw [← Real.rpow_neg_one a]
    have hexp : (1 - p.re) + (-1) = -p.re := by ring
    rw [← Real.rpow_add ha, hexp]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hscaled]
  rw [← ofReal_integral_norm_eq_lintegral_enorm hbase]
  rw [hreal, ENNReal.ofReal_mul (Real.rpow_nonneg ha.le _)]

private lemma ennreal_pnat_rpow_mul_tsum_ne_top
    (a : ℝ) (ha : 1 < a) (C : ENNReal) (hC : C ≠ ⊤) :
    (∑' n : ℕ+, ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-a)) * C) ≠ ⊤ := by
  by_cases hC0 : C = 0
  · simp [hC0]
  · have hsum : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) := by
      exact Real.summable_nat_rpow.mpr (by linarith : -a < -1)
    have hsum' : Summable (fun n : ℕ+ => (n : ℝ) ^ (-a)) :=
      hsum.comp_injective Subtype.coe_injective
    have hsum'' :
        ∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a)) =
          ENNReal.ofReal (∑' n : ℕ+, (n : ℝ) ^ (-a)) := by
      exact ((ENNReal.ofReal_tsum_of_nonneg
        fun _ => Real.rpow_nonneg (Nat.cast_nonneg _) _) hsum').symm
    have hfinite :
        ENNReal.ofReal (∑' n : ℕ+, (n : ℝ) ^ (-a)) ≠ ⊤ :=
      ENNReal.ofReal_ne_top
    rw [show
      (∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a)) * C) =
          (∑' n : ℕ+, ENNReal.ofReal ((n : ℕ) ^ (-a))) * C from
        ENNReal.tsum_mul_right]
    rw [hsum'']
    exact ENNReal.mul_ne_top hfinite hC

/-- Absolute convergence of the positive-dilate Mellin payload for the exact v3 class. -/
theorem eStarMellinAbsolute_payload_of_IccZero_IcoLipschitz
    (h : ℝ → ℂ) (b : ℝ) (K : NNReal) (hb : 0 ≤ b)
    (hmeas : Measurable h)
    (hsupp : ∀ v, v ∉ Set.Icc (0 : ℝ) b → h v = 0)
    (hlip : LipschitzOnWith K h (Set.Ico (0 : ℝ) b))
    (p : ℂ) (hp : 1 < p.re) :
    (∀ n : ℕ+,
      AEStronglyMeasurable
        (fun u : ℝ =>
          (u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u))
        (volume.restrict (Set.Ioi 0))) ∧
    (∑' n : ℕ+,
      ∫⁻ u : ℝ,
        ‖(u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u)‖ₑ
        ∂(volume.restrict (Set.Ioi 0))) ≠ ⊤ := by
  refine ⟨fun n => mellin_dilate_aestronglyMeasurable
    h b K hb hmeas hsupp hlip p hp n, ?_⟩
  rw [show
      (fun n : ℕ+ => ∫⁻ u : ℝ,
        ‖(u : ℂ) ^ (p - 1) • h (((n : ℕ) : ℝ) * u)‖ₑ
          ∂(volume.restrict (Set.Ioi 0))) =
      (fun n : ℕ+ => ENNReal.ofReal (((n : ℕ) : ℝ) ^ (-p.re)) *
        (∫⁻ v : ℝ, ‖(v : ℂ) ^ (p - 1) • h v‖ₑ
          ∂(volume.restrict (Set.Ioi 0)))) from
    funext (fun n => mellin_dilate_lintegral_eq
      h b K hb hmeas hsupp hlip p hp n)]
  exact ennreal_pnat_rpow_mul_tsum_ne_top p.re hp _
    (mellin_base_lintegral_ne_top h b K hb hmeas hsupp hlip p hp)

#print axioms eStarMellinAbsolute_payload_of_IccZero_IcoLipschitz

end EStarMuntzZeroMassContinuation
