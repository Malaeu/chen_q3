import Mathlib
import aristotle_output.d1524982_aristotle

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

local notation "digamma" => (_root_.digamma)
lemma Gamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.Gamma z := by
  apply (Complex.differentiableAt_Gamma z ?_).continuousAt
  intro m
  intro h
  have hzpos : 0 < z.re := hz
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
  have : z.re ≠ -(m : ℝ) := by nlinarith
  exact this (by simpa using congrArg Complex.re h)

lemma Complex.continuousOn_Gamma_of_re_pos {S : Set ℂ} (hS : S ⊆ {z | 0 < z.re}) :
    ContinuousOn Complex.Gamma S := by
  intro z hz
  exact (Gamma_continuousAt_of_re_pos (hS hz)).continuousWithinAt

lemma Gamma_differentiableOn_right_half_plane :
    DifferentiableOn ℂ Complex.Gamma {z | 0 < z.re} := by
  intro z hz
  have hz' : ∀ m : ℕ, z ≠ -m := by
    intro m h
    have hzpos : 0 < z.re := hz
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
    have : z.re ≠ -(m : ℝ) := by nlinarith
    exact this (by simpa using congrArg Complex.re h)
  exact (Complex.differentiableAt_Gamma z hz').differentiableWithinAt

lemma derivGamma_bounded_on_compact (K : Set ℂ) (hK : IsCompact K)
    (hK_pos : K ⊆ {z | 0 < z.re}) :
    ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨0, ?_⟩
    intro z hz
    simpa [hKempty] using hz
  have hKnonempty : K.Nonempty := by
    simpa [Set.nonempty_iff_ne_empty] using hKempty
  have hS_open : IsOpen ({z | 0 < z.re} : Set ℂ) := by
    simpa using isOpen_lt continuous_const Complex.continuous_re
  have hdiff : DifferentiableOn ℂ (deriv Complex.Gamma) {z | 0 < z.re} := by
    exact (DifferentiableOn.deriv Gamma_differentiableOn_right_half_plane hS_open)
  have hcont : ContinuousOn (fun z => ‖deriv Complex.Gamma z‖) K := by
    exact (hdiff.continuousOn.mono hK_pos).norm
  obtain ⟨z0, hz0, hz0max⟩ := hK.exists_isMaxOn hKnonempty hcont
  refine ⟨‖deriv Complex.Gamma z0‖, ?_⟩
  intro z hz
  exact hz0max hz

lemma gamma_norm_lower_bound_on_compact (K : Set ℂ) (hK : IsCompact K)
    (hK_pos : K ⊆ {z | 0 < z.re}) :
    ∃ c > 0, ∀ z ∈ K, c ≤ ‖Complex.Gamma z‖ := by
  classical
  by_cases hKempty : K = ∅
  · refine ⟨1, by norm_num, ?_⟩
    intro z hz
    simpa [hKempty] using hz
  have hKnonempty : K.Nonempty := by
    simpa [Set.nonempty_iff_ne_empty] using hKempty
  have hcont : ContinuousOn (fun z => ‖Complex.Gamma z‖) K := by
    intro z hz
    exact (Gamma_continuousAt_of_re_pos (hK_pos hz)).norm.continuousWithinAt
  obtain ⟨z0, hz0, hz0min⟩ := hK.exists_isMinOn hKnonempty hcont
  have hnez : Complex.Gamma z0 ≠ 0 :=
    Complex.Gamma_ne_zero_of_re_pos (hK_pos hz0)
  have hpos : 0 < ‖Complex.Gamma z0‖ := by
    have hne : ‖Complex.Gamma z0‖ ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hnez)
    exact lt_of_le_of_ne (norm_nonneg _) (by simpa using hne.symm)
  refine ⟨‖Complex.Gamma z0‖, hpos, ?_⟩
  intro z hz
  exact hz0min hz

lemma tendstoUniformlyOn_div_of_bounds {ι : Type*} {F G : ι → ℂ → ℂ}
    {f g : ℂ → ℂ} {l : Filter ι} {K : Set ℂ}
    (hF : TendstoUniformlyOn F f l K)
    (hG : TendstoUniformlyOn G g l K)
    (hc : ∃ c > 0, ∀ z ∈ K, c ≤ ‖g z‖)
    (hM : ∃ M, ∀ z ∈ K, ‖f z‖ ≤ M) :
    TendstoUniformlyOn (fun n z => F n z / G n z) (fun z => f z / g z) l K := by
  classical
  rcases hc with ⟨c, hcpos, hcg⟩
  rcases hM with ⟨M, hMf⟩
  let M' : ℝ := max M 1
  have hM'pos : 0 < M' := by
    have : (1 : ℝ) ≤ M' := by exact le_max_right _ _
    exact lt_of_lt_of_le zero_lt_one this
  have hMf' : ∀ z ∈ K, ‖f z‖ ≤ M' := by
    intro z hz
    exact le_trans (hMf z hz) (le_max_left _ _)
  have hF' := (Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity
    Metric.uniformity_basis_dist).1 hF
  have hG' := (Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity
    Metric.uniformity_basis_dist).1 hG
  refine (Filter.HasBasis.tendstoUniformlyOn_iff_of_uniformity
    Metric.uniformity_basis_dist).2 ?_
  intro ε hε
  let M'' : ℝ := M' + ε * c / 4
  have hM''pos : 0 < M'' := by
    dsimp [M'']
    nlinarith [hM'pos, hε, hcpos]
  have hF1 := hF' (ε * c / 4) (by nlinarith [hε, hcpos])
  have hG1 := hG' (ε * c * c / (4 * M'')) (by
    have hpos1 : 0 < ε * c := mul_pos hε hcpos
    have hpos2 : 0 < ε * c * c := mul_pos hpos1 hcpos
    have hden : 0 < (4 * M'') := by nlinarith [hM''pos]
    exact div_pos hpos2 hden)
  have hG0 := hG' (c / 2) (by nlinarith [hcpos])
  filter_upwards [hF1, hG1, hG0] with n hF1n hG1n hG0n z hzK
  have hF1n' : ‖F n z - f z‖ < ε * c / 4 := by
    simpa [Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using hF1n z hzK
  have hG1n' : ‖G n z - g z‖ < ε * c * c / (4 * M'') := by
    simpa [Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using hG1n z hzK
  have hG0n' : ‖G n z - g z‖ < c / 2 := by
    simpa [Set.mem_setOf_eq, dist_eq_norm, norm_sub_rev] using hG0n z hzK
  have hGz : c ≤ ‖g z‖ := hcg z hzK
  have hGnz : c / 2 ≤ ‖G n z‖ := by
    have htriangle : ‖g z‖ ≤ ‖G n z‖ + ‖G n z - g z‖ := by
      have h := norm_add_le (G n z) (g z - G n z)
      have h' : ‖g z‖ ≤ ‖G n z‖ + ‖g z - G n z‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
      simpa [norm_sub_rev] using h'
    have : c - ‖G n z - g z‖ ≤ ‖G n z‖ := by linarith [htriangle, hGz]
    have : c / 2 ≤ ‖G n z‖ := by nlinarith [this, hG0n']
    exact this
  have hGnz' : G n z ≠ 0 := by
    have : (0 : ℝ) < ‖G n z‖ := lt_of_lt_of_le (by nlinarith [hcpos]) hGnz
    exact (norm_ne_zero_iff.mp (ne_of_gt this))
  have hgz' : g z ≠ 0 := by
    have : (0 : ℝ) < ‖g z‖ := lt_of_lt_of_le hcpos hGz
    exact (norm_ne_zero_iff.mp (ne_of_gt this))
  have hFbound : ‖f z‖ ≤ M' := hMf' z hzK
  have hFbound' : ‖F n z‖ ≤ M'' := by
    have htri : ‖F n z‖ ≤ ‖f z‖ + ‖F n z - f z‖ := by
      have := norm_add_le (f z) (F n z - f z)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have hsum : ‖f z‖ + ‖F n z - f z‖ ≤ M' + ε * c / 4 := by
      nlinarith [hFbound, hF1n']
    simpa [M''] using le_trans htri hsum
  have hG1n'' : ‖g z - G n z‖ < ε * c * c / (4 * M'') := by
    simpa [norm_sub_rev] using hG1n'
  have hsplit :
      F n z / G n z - f z / g z =
        (F n z - f z) / g z + F n z * (g z - G n z) / (G n z * g z) := by
    field_simp [hGnz', hgz', sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    ring
  have hterm1 : ‖(F n z - f z) / g z‖ < ε / 4 := by
    have hgzpos : 0 < ‖g z‖ := lt_of_lt_of_le hcpos hGz
    have h' : ‖F n z - f z‖ < (ε / 4) * ‖g z‖ := by
      nlinarith [hF1n', hGz]
    have h'' :
        ‖g z‖⁻¹ * ‖F n z - f z‖ < ‖g z‖⁻¹ * ((ε / 4) * ‖g z‖) := by
      exact mul_lt_mul_of_pos_left h' (inv_pos.mpr hgzpos)
    have h''' : ‖g z‖⁻¹ * ‖F n z - f z‖ < ε / 4 := by
      have hgzne : ‖g z‖ ≠ 0 := ne_of_gt hgzpos
      simpa [mul_comm, mul_left_comm, mul_assoc, hgzne] using h''
    simpa [div_eq_mul_inv, norm_div, mul_comm, mul_left_comm, mul_assoc] using h'''
  have hden : ‖G n z * g z‖ ≥ (c / 2) * c := by
    have h1 : c / 2 ≤ ‖G n z‖ := hGnz
    have h2 : c ≤ ‖g z‖ := hGz
    have : (c / 2) * c ≤ ‖G n z‖ * ‖g z‖ := by nlinarith [h1, h2]
    simpa [norm_mul, mul_comm, mul_left_comm, mul_assoc] using this
  have hterm2 : ‖F n z * (g z - G n z) / (G n z * g z)‖ ≤ ε / 2 := by
    have hnum : ‖F n z‖ * ‖g z - G n z‖ ≤ M'' * (ε * c * c / (4 * M'')) := by
      have hFle : ‖F n z‖ ≤ M'' := hFbound'
      have hGle : ‖g z - G n z‖ ≤ ε * c * c / (4 * M'') := le_of_lt hG1n''
      have hM''nonneg : 0 ≤ M'' := le_of_lt hM''pos
      exact mul_le_mul hFle hGle (by exact norm_nonneg _) hM''nonneg
    have hden_inv : (1 / ‖G n z * g z‖) ≤ (1 / ((c / 2) * c)) := by
      exact one_div_le_one_div_of_le (by nlinarith [hcpos]) hden
    have hnum_nonneg : 0 ≤ M'' * (ε * c * c / (4 * M'')) := by
      have hM''nonneg : 0 ≤ M'' := le_of_lt hM''pos
      have hdenpos : 0 ≤ ε * c * c / (4 * M'') := by
        have : 0 < ε * c * c / (4 * M'') := by
          have hpos1 : 0 < ε * c := mul_pos hε hcpos
          have hpos2 : 0 < ε * c * c := mul_pos hpos1 hcpos
          have hden : 0 < (4 * M'') := by nlinarith [hM''pos]
          exact div_pos hpos2 hden
        exact le_of_lt this
      exact mul_nonneg hM''nonneg hdenpos
    have hden_nonneg : 0 ≤ ‖G n z * g z‖ := by exact norm_nonneg _
    have hbound1 :
        ‖F n z‖ * ‖g z - G n z‖ / ‖G n z * g z‖ ≤
          (M'' * (ε * c * c / (4 * M''))) / ‖G n z * g z‖ := by
      simpa [div_eq_mul_inv] using
        (mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hden_nonneg))
    have hbound2 :
        (M'' * (ε * c * c / (4 * M''))) / ‖G n z * g z‖ ≤
          (M'' * (ε * c * c / (4 * M''))) / ((c / 2) * c) := by
      have := mul_le_mul_of_nonneg_left hden_inv hnum_nonneg
      simpa [div_eq_mul_inv] using this
    have hbound :
        ‖F n z * (g z - G n z) / (G n z * g z)‖ ≤
          (M'' * (ε * c * c / (4 * M''))) / ((c / 2) * c) := by
      have : ‖F n z * (g z - G n z) / (G n z * g z)‖ =
          ‖F n z‖ * ‖g z - G n z‖ / ‖G n z * g z‖ := by
        simp [norm_div, norm_mul, mul_comm, mul_left_comm, mul_assoc]
      exact le_trans (by simpa [this] using hbound1) hbound2
    have hbound' : (M'' * (ε * c * c / (4 * M''))) / ((c / 2) * c) = ε / 2 := by
      field_simp [M'', hcpos.ne', mul_comm, mul_left_comm, mul_assoc]
      ring
    simpa [hbound'] using hbound
  have hmain : ‖F n z / G n z - f z / g z‖ < ε := by
    have hsum : ‖(F n z - f z) / g z‖ + ‖F n z * (g z - G n z) / (G n z * g z)‖ < ε := by
      nlinarith [hterm1, hterm2]
    have : ‖F n z / G n z - f z / g z‖ ≤
        ‖(F n z - f z) / g z‖ + ‖F n z * (g z - G n z) / (G n z * g z)‖ := by
      have := norm_add_le ((F n z - f z) / g z)
        (F n z * (g z - G n z) / (G n z * g z))
      simpa [hsplit] using this
    exact lt_of_le_of_lt this hsum
  have hmain' : dist (f z / g z) (F n z / G n z) < ε := by
    simpa [dist_comm, dist_eq_norm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hmain
  exact hmain'

lemma digammaSeq_differentiableOn (n : ℕ) :
    DifferentiableOn ℂ (fun z => digammaSeq z n) {z | 0 < z.re} := by
  intro z hz
  have h_term : ∀ k ∈ Finset.range (n + 1),
      DifferentiableAt ℂ (fun z => 1 / (z + k : ℂ)) z := by
    intro k hk
    have hz' : z ≠ -(k : ℂ) := by
      intro h
      have hzpos : 0 < z.re := hz
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.cast_nonneg k)
      have : z.re ≠ -(k : ℝ) := by nlinarith
      exact this (by simpa using congrArg Complex.re h)
    have hz'' : z + (k : ℂ) ≠ 0 := by
      exact add_eq_zero_iff_eq_neg.not.mpr hz'
    have h_diff : DifferentiableAt ℂ (fun z => z + (k : ℂ)) z :=
      differentiableAt_id.add_const _
    have h_inv : DifferentiableAt ℂ (fun z => (z + (k : ℂ))⁻¹) z :=
      h_diff.inv (by simpa using hz'')
    simpa [one_div] using h_inv
  have h_sum : DifferentiableAt ℂ
      (fun z => ∑ k ∈ Finset.range (n + 1), 1 / (z + k : ℂ)) z :=
    DifferentiableAt.fun_sum h_term
  have h_const : DifferentiableAt ℂ (fun _ => (Real.log n : ℂ)) z :=
    differentiableAt_const _
  have h_sub : DifferentiableAt ℂ (fun z => (Real.log n : ℂ) -
      ∑ k ∈ Finset.range (n + 1), 1 / (z + k : ℂ)) z :=
    h_const.sub h_sum
  simpa [digammaSeq] using h_sub.differentiableWithinAt

lemma digammaSeq_tendstoLocallyUniformlyOn_of_derivGamma_bounded (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re}) (hS_open : IsOpen S)
    (h_deriv_bd : ∀ K : Set ℂ, IsCompact K → K ⊆ S →
      ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M) :
    TendstoLocallyUniformlyOn (fun n z => digammaSeq z n) digamma Filter.atTop S := by
  have h_gamma :
      TendstoLocallyUniformlyOn (fun n z => Complex.GammaSeq z n) Complex.Gamma Filter.atTop S :=
    GammaSeq_tendstoLocallyUniformlyOn_v9 S hS hS_open
  have h_deriv :
      TendstoLocallyUniformlyOn (fun n z => deriv (fun w => Complex.GammaSeq w n) z)
        (deriv Complex.Gamma) Filter.atTop S :=
    deriv_GammaSeq_tendstoLocallyUniformlyOn S hS hS_open
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact hS_open).2 ?_
  intro K hK hK_compact
  have h_gamma_K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hS_open).1 h_gamma K hK hK_compact
  have h_deriv_K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hS_open).1 h_deriv K hK hK_compact
  have h_gamma_lb : ∃ c > 0, ∀ z ∈ K, c ≤ ‖Complex.Gamma z‖ :=
    gamma_norm_lower_bound_on_compact K hK_compact (by intro z hz; exact hS (hK hz))
  have h_deriv_bd_K : ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M :=
    h_deriv_bd K hK_compact hK
  have h_div_K : TendstoUniformlyOn
      (fun n z => (deriv (fun w => Complex.GammaSeq w n) z) / (Complex.GammaSeq z n))
      (fun z => (deriv Complex.Gamma z) / (Complex.Gamma z)) Filter.atTop K :=
    tendstoUniformlyOn_div_of_bounds h_deriv_K h_gamma_K h_gamma_lb h_deriv_bd_K
  have h_eq : ∀ᶠ n in Filter.atTop,
      Set.EqOn (fun z => (deriv (fun w => Complex.GammaSeq w n) z) / (Complex.GammaSeq z n))
        (fun z => digammaSeq z n) K := by
    refine Filter.eventually_atTop.mpr ?_
    refine ⟨1, ?_⟩
    intro n hn z hzK
    have hz' : ∀ k ≤ n, z ≠ -k := by
      intro k hk
      intro h
      have hzpos : 0 < z.re := hS (hK hzK)
      have hk0 : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (Nat.cast_nonneg k)
      have : z.re ≠ -(k : ℝ) := by nlinarith
      exact this (by simpa using congrArg Complex.re h)
    exact (digammaSeq_eq_deriv_div_GammaSeq z n hn hz').symm
  exact TendstoUniformlyOn.congr h_div_K h_eq

theorem deriv_digamma_eq_trigamma_of_derivGamma_bounded {z : ℂ} (hz : 0 < z.re)
    (h_deriv_bd : ∀ K : Set ℂ, IsCompact K → K ⊆ {z | 0 < z.re} →
      ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M) :
    deriv digamma z = trigamma z := by
  let S : Set ℂ := {z | 0 < z.re}
  have hS_open : IsOpen S := by
    simpa using isOpen_lt continuous_const Complex.continuous_re
  have hS_sub : S ⊆ {z | 0 < z.re} := by
    intro z hz; exact hz
  have h_loc : TendstoLocallyUniformlyOn (fun n z => digammaSeq z n) digamma Filter.atTop S :=
    digammaSeq_tendstoLocallyUniformlyOn_of_derivGamma_bounded S hS_sub hS_open h_deriv_bd
  have h_diff : ∀ᶠ n in Filter.atTop, DifferentiableOn ℂ (fun z => digammaSeq z n) S :=
    Filter.Eventually.of_forall (fun n => digammaSeq_differentiableOn n)
  have h_loc_deriv :
      TendstoLocallyUniformlyOn (fun n z => deriv (fun w => digammaSeq w n) z)
        (deriv digamma) Filter.atTop S :=
    TendstoLocallyUniformlyOn.deriv h_loc h_diff hS_open
  have h_deriv_at :
      Filter.Tendsto (fun n => deriv (fun w => digammaSeq w n) z) Filter.atTop
        (nhds (deriv digamma z)) :=
    h_loc_deriv.tendsto_at (by simpa [S] using hz)
  have h_trigamma :
      Filter.Tendsto (fun n => deriv (fun w => digammaSeq w n) z) Filter.atTop
        (nhds (trigamma z)) :=
    deriv_digammaSeq_tendsto_trigamma z hz
  exact tendsto_nhds_unique h_deriv_at h_trigamma

theorem deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z := by
  refine deriv_digamma_eq_trigamma_of_derivGamma_bounded hz ?_
  intro K hK hKsub
  exact derivGamma_bounded_on_compact K hK hKsub

-- Archimedean density (uses digamma from v16/d1524982).
def a (xi : ℝ) : ℝ := Real.log Real.pi - (digamma (1 / 4 + Complex.I * Real.pi * xi)).re

/-- Imaginary part of one term is negative (z has positive re/im). -/
lemma im_one_div_sq_add_nat_neg {z : ℂ} (n : ℕ) (hz : 0 < z.re) (hzi : 0 < z.im) :
    (1 / (z + n)^2).im < 0 := by
  norm_num [sq, Complex.normSq, Complex.div_im]
  exact add_neg
    (mul_neg_of_pos_of_neg (div_pos (by positivity) (by positivity))
      (div_neg_of_neg_of_pos (by linarith) (by positivity)))
    (mul_neg_of_neg_of_pos (div_neg_of_neg_of_pos (by linarith) (by positivity))
      (div_pos (by positivity) (by positivity)))

/-- Trigamma series is summable for Re z > 0. -/
lemma summable_trigamma_series {z : ℂ} (hz : 0 < z.re) :
    Summable (fun n : ℕ => 1 / (z + n)^2) := by
  -- Compare with 1/n^2.
  have h_comparison : ∃ N : ℕ, ∀ n ≥ N, ‖1 / (z + n)^2‖ ≤ 1 / n^2 := by
    norm_num [Complex.normSq, Complex.sq_norm]
    exact ⟨Nat.ceil (2 * |z.re| + 2 * |z.im| + 1), fun n hn =>
      inv_anti₀
        (sq_pos_of_pos <| Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| by
          rintro rfl; norm_num at hn; linarith [abs_nonneg z.re, abs_nonneg z.im])
        (by cases abs_cases z.re <;> cases abs_cases z.im <;>
          nlinarith [Nat.ceil_le.mp hn])⟩
  have h_abs_summable : Summable (fun n : ℕ => ‖1 / (z + n)^2‖) := by
    rw [← summable_nat_add_iff h_comparison.choose]
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n =>
      h_comparison.choose_spec _ (Nat.le_add_left _ _))
      (by
        simpa using
          summable_nat_add_iff h_comparison.choose |>.2
            (Real.summable_one_div_nat_pow.2 one_lt_two))
  exact h_abs_summable.of_norm

lemma im_trigamma_eq_tsum_im {z : ℂ} (hz : 0 < z.re) :
    (trigamma z).im = ∑' n : ℕ, (1 / (z + n)^2).im := by
  have hsum : Summable (fun n : ℕ => 1 / (z + n)^2) := summable_trigamma_series hz
  simpa [trigamma] using (Complex.im_tsum hsum)

/-- Imaginary part of trigamma is negative for z with positive re/im. -/
theorem im_trigamma_neg {z : ℂ} (hz : 0 < z.re) (hzi : 0 < z.im) :
    (trigamma z).im < 0 := by
  rw [im_trigamma_eq_tsum_im hz]
  have hsum : Summable (fun n : ℕ => (1 / (z + n)^2).im) := by
    have hsum' : Summable (fun n : ℕ => (1 : ℂ) / (z + n)^2) :=
      summable_trigamma_series hz
    simpa using (Complex.imCLM.summable hsum')
  have hsum_neg : Summable (fun n : ℕ => -(1 / (z + n)^2).im) := by
    simpa using hsum.neg
  have hpos : 0 < ∑' n : ℕ, -(1 / (z + n)^2).im := by
    refine Summable.tsum_pos hsum_neg ?_ 0 ?_
    · intro n
      exact neg_nonneg.mpr (le_of_lt (im_one_div_sq_add_nat_neg n hz hzi))
    · exact neg_pos.mpr (im_one_div_sq_add_nat_neg 0 hz hzi)
  have hneg : 0 < -(∑' n : ℕ, (1 / (z + n)^2).im) := by
    have htsum :
        ∑' n : ℕ, -(1 / (z + n)^2).im = -∑' n : ℕ, (1 / (z + n)^2).im := by
      exact tsum_neg (f := fun n : ℕ => (1 / (z + n)^2).im)
    have hpos' := hpos
    rw [htsum] at hpos'
    exact hpos'
  nlinarith

-- Derivative of Re(digamma).
lemma deriv_re_digamma (xi : ℝ) :
    deriv (fun t : ℝ => (digamma (1 / 4 + Complex.I * Real.pi * t)).re) xi =
    -Real.pi * (deriv (fun z : ℂ => digamma z) (1 / 4 + Complex.I * Real.pi * xi)).im := by
  convert HasDerivAt.deriv _ using 1
  have h_chain :
      HasDerivAt (fun t : ℝ => digamma (1 / 4 + Complex.I * Real.pi * t))
        (deriv (fun z : ℂ => digamma z) (1 / 4 + Complex.I * Real.pi * xi) *
          Complex.I * Real.pi) xi := by
    have h_chain :
        HasDerivAt (fun t : ℝ => digamma (1 / 4 + Complex.I * Real.pi * t))
          (deriv (fun z : ℂ => digamma z) (1 / 4 + Complex.I * Real.pi * xi) *
            (Complex.I * Real.pi)) xi := by
      have h_diff :
          DifferentiableAt ℂ (fun z : ℂ => digamma z)
            (1 / 4 + Complex.I * Real.pi * xi) := by
        refine' DifferentiableAt.div _ _ _
        · have h_diff :
            AnalyticAt ℂ (deriv Complex.Gamma)
              (1 / 4 + Complex.I * Real.pi * xi) := by
            have h_diff : AnalyticAt ℂ Complex.Gamma
                (1 / 4 + Complex.I * Real.pi * xi) := by
              refine' DifferentiableOn.analyticAt _ _
              exact {z : ℂ | 0 < z.re}
              · intro z hz
                exact Complex.differentiableAt_Gamma _ (by contrapose! hz; aesop) |>
                  DifferentiableAt.differentiableWithinAt
              · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re)
                  (by norm_num)
            exact h_diff.deriv
          exact h_diff.differentiableAt
        · refine' Complex.differentiableAt_Gamma _ _
          norm_num [Complex.ext_iff]
          exact fun m hm => by linarith
        · exact Complex.Gamma_ne_zero_of_re_pos (by norm_num [Complex.add_re, Complex.mul_re])
      convert HasDerivAt.comp xi h_diff.hasDerivAt
        (HasDerivAt.add (hasDerivAt_const _ _)
          (HasDerivAt.mul (hasDerivAt_const _ _) (hasDerivAt_id _ |> HasDerivAt.ofReal_comp)))
        using 1
      norm_num
    simpa only [mul_assoc] using h_chain
  rw [hasDerivAt_iff_tendsto_slope_zero] at *
  convert Complex.continuous_re.continuousAt.tendsto.comp h_chain using 2
  norm_num; ring
  norm_num [Complex.ext_iff]

-- Derivative of a(xi).
lemma deriv_a_eq {xi : ℝ} (hxi : 0 < xi) :
    deriv a xi =
      Real.pi * (deriv (fun z : ℂ => digamma z) (1 / 4 + Complex.I * Real.pi * xi)).im := by
  have h_chain :
      deriv a xi = -deriv (fun t : ℝ => (digamma (1 / 4 + Complex.I * Real.pi * t)).re) xi := by
    unfold a
    rw [deriv_const_sub]
  have h_chain' :
      deriv (fun t : ℝ => (digamma (1 / 4 + Complex.I * Real.pi * t)).re) xi =
        -Real.pi * (deriv (fun z : ℂ => digamma z)
          (1 / 4 + Complex.I * Real.pi * xi)).im := by
    convert deriv_re_digamma xi using 1
  aesop

lemma continuousOn_a : ContinuousOn a (Ici 0) := by
  refine' ContinuousOn.sub _ _
  · exact continuousOn_const
  · have h_analytic : ∀ z : ℂ, 0 < z.re → AnalyticAt ℂ (fun z => digamma z) z := by
      intro z hz
      have h_analytic : AnalyticAt ℂ (fun z => deriv Complex.Gamma z / Complex.Gamma z) z := by
        have h_gamma_analytic : AnalyticAt ℂ Complex.Gamma z := by
          refine' DifferentiableOn.analyticAt _ _
          exact {w : ℂ | 0 < w.re}
          · have h_gamma_diff : ∀ w : ℂ, 0 < w.re → DifferentiableAt ℂ Complex.Gamma w := by
              intro w hw
              apply_rules [Complex.differentiableAt_Gamma]
              exact fun m => ne_of_apply_ne Complex.re <| by norm_num; linarith
            exact fun w hw => DifferentiableAt.differentiableWithinAt (h_gamma_diff w hw)
          · exact IsOpen.mem_nhds (isOpen_lt continuous_const Complex.continuous_re) hz
        have h_deriv_gamma_analytic : AnalyticAt ℂ (deriv Complex.Gamma) z := by
          apply_rules [AnalyticAt.deriv, h_gamma_analytic]
        exact h_deriv_gamma_analytic.div h_gamma_analytic (Complex.Gamma_ne_zero_of_re_pos hz)
      exact h_analytic
    exact continuousOn_of_forall_continuousAt fun x hx =>
      Complex.continuous_re.continuousAt.comp
        (h_analytic _ (by norm_num [Complex.ext_iff]) |> fun h => h.continuousAt) |>
        ContinuousAt.comp <| Continuous.continuousAt <| by continuity

/-- a'(xi) < 0 for xi > 0. -/
theorem deriv_a_neg {xi : ℝ} (hxi : 0 < xi) : deriv a xi < 0 := by
  have hzre : 0 < (1 / 4 + Complex.I * Real.pi * xi).re := by
    have hre : (1 / 4 + Complex.I * Real.pi * xi).re = (1 / 4 : ℝ) := by
      simp [mul_assoc]
    nlinarith [hre]
  have hzim : 0 < (1 / 4 + Complex.I * Real.pi * xi).im := by
    have him : (1 / 4 + Complex.I * Real.pi * xi).im = Real.pi * xi := by
      simp [mul_assoc]
    have hpos : 0 < Real.pi * xi := mul_pos Real.pi_pos hxi
    nlinarith [him, hpos]
  calc
    deriv a xi = Real.pi * (deriv digamma (1 / 4 + Complex.I * Real.pi * xi)).im :=
      deriv_a_eq hxi
    _ = Real.pi * (trigamma (1 / 4 + Complex.I * Real.pi * xi)).im := by
      congr 1
      exact congrArg Complex.im (deriv_digamma_eq_trigamma hzre)
    _ < 0 := by
      exact mul_neg_of_pos_of_neg Real.pi_pos (im_trigamma_neg hzre hzim)

/-- a is strictly decreasing on (0, +infty). -/
theorem strictAntiOn_a : StrictAntiOn a (Set.Ioi 0) := by
  apply strictAntiOn_of_deriv_neg (D := Set.Ioi 0)
  · exact convex_Ioi 0
  · exact continuousOn_a.mono Set.Ioi_subset_Ici_self
  · intro x hx
    have hx' : 0 < x := by simpa using hx
    exact deriv_a_neg hx'
