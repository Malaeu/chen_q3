import Mathlib
import Q3.Basic.Defs
import aristotle_output.d1524982_aristotle

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

noncomputable section

namespace Q3

lemma digamma_eq_root : Q3.digamma = _root_.digamma := rfl

lemma Gamma_continuousAt_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    ContinuousAt Complex.Gamma z := by
  apply (Complex.differentiableAt_Gamma z ?_).continuousAt
  intro m
  intro h
  have hzpos : 0 < z.re := hz
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Nat.cast_nonneg m)
  have : z.re ≠ -(m : ℝ) := by nlinarith
  exact this (by simpa using congrArg Complex.re h)

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
  have hS_open : IsOpen {z : ℂ | 0 < z.re} := by
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

lemma digammaSeq_tendstoLocallyUniformlyOn_of_derivGamma_bounded (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re}) (hS_open : IsOpen S)
    (h_deriv_bd : ∀ K : Set ℂ, IsCompact K → K ⊆ S →
      ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M) :
    TendstoLocallyUniformlyOn (fun n z => _root_.digammaSeq z n) Q3.digamma Filter.atTop S := by
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
        (fun z => _root_.digammaSeq z n) K := by
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
  have h_eq' : TendstoUniformlyOn (fun n z => _root_.digammaSeq z n)
      (fun z => (deriv Complex.Gamma z) / (Complex.Gamma z)) Filter.atTop K :=
    TendstoUniformlyOn.congr h_div_K h_eq
  simpa [Q3.digamma] using h_eq'

lemma digammaSeq_tendsto_Q3_digamma (z : ℂ) (hz : 0 < z.re) :
    Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop (nhds (Q3.digamma z)) := by
  let S : Set ℂ := {z | 0 < z.re}
  have hS_open : IsOpen S := by
    simpa using isOpen_lt continuous_const Complex.continuous_re
  have hS_sub : S ⊆ {z | 0 < z.re} := by
    intro z hz
    exact hz
  have h_deriv_bd :
      ∀ K : Set ℂ, IsCompact K → K ⊆ S →
        ∃ M, ∀ z ∈ K, ‖deriv Complex.Gamma z‖ ≤ M := by
    intro K hK hKsub
    exact derivGamma_bounded_on_compact K hK (by simpa [S] using hKsub)
  have h_loc :
      TendstoLocallyUniformlyOn (fun n z => _root_.digammaSeq z n) _root_.digamma
        Filter.atTop S :=
    digammaSeq_tendstoLocallyUniformlyOn_of_derivGamma_bounded S hS_sub hS_open h_deriv_bd
  have h_point :
      Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop
        (nhds (_root_.digamma z)) :=
    h_loc.tendsto_at (by simpa [S] using hz)
  simpa [digamma_eq_root] using h_point

lemma digammaSeq_eq_split (z : ℂ) (n : ℕ) :
    _root_.digammaSeq z n =
      (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ)) +
        ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ) - 1 / (z + k)) := by
  -- Expand digammaSeq and regroup the finite sums.
  simp [digammaSeq, Finset.sum_add_distrib, sub_eq_add_neg,
    add_comm, add_left_comm, add_assoc]

lemma sum_range_inv_eq_harmonic (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / (k + 1 : ℂ))) = (harmonic n : ℂ) := by
  -- Coerce the rational harmonic sum to ℂ.
  simp [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

lemma sum_range_inv_eq_harmonic_real (n : ℕ) :
    (∑ k ∈ Finset.range n, (1 / (k + 1 : ℂ))) = ((harmonic n : ℝ) : ℂ) := by
  -- Cast via ℝ to align with real asymptotics.
  simpa using (sum_range_inv_eq_harmonic n)

lemma digamma_series_summable (z : ℂ) (hz : ∀ n : ℕ, z + n ≠ 0) :
    Summable (fun n : ℕ => (1 / (n + 1 : ℂ) - 1 / (z + n))) := by
  -- Comparison with a p-series: |term n| ≤ C / n^2 for large n.
  let term : ℕ → ℂ := fun n => (1 / (n + 1 : ℂ) - 1 / (z + n))
  have h_term :
      ∀ n : ℕ, term n = (z - 1) / ((n + 1) * (z + n)) := by
    intro n
    have h1 : (n + 1 : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero n
    have h2 : (z + n) ≠ 0 := by
      exact hz n
    dsimp [term]
    calc
      (1 / (n + 1 : ℂ) - 1 / (z + n))
          = ((1 : ℂ) * (z + n) - (n + 1 : ℂ) * 1) / ((n + 1 : ℂ) * (z + n)) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (div_sub_div (a := (1 : ℂ)) (b := (n + 1 : ℂ))
                (c := (1 : ℂ)) (d := (z + n)) h1 h2)
      _ = (z - 1) / ((n + 1) * (z + n)) := by
            ring_nf
  let N : ℕ := Nat.ceil (2 * ‖z‖) + 1
  have h_bound :
      ∀ n : ℕ, n ≥ N →
        ‖term n‖ ≤ (2 * ‖z - 1‖) / (n ^ 2 : ℝ) := by
    intro n hn
    have hn' : (Nat.ceil (2 * ‖z‖) : ℕ) ≤ n := by
      exact Nat.le_trans (Nat.le_succ _) hn
    have hN : (2 * ‖z‖ : ℝ) ≤ n := by
      have h1 : (2 * ‖z‖ : ℝ) ≤ (Nat.ceil (2 * ‖z‖) : ℝ) := by
        exact Nat.le_ceil (2 * ‖z‖)
      exact le_trans h1 (by exact_mod_cast hn')
    have hnorm_n : ‖(n : ℂ)‖ = (n : ℝ) := by
      simp
    have h_lower : (n : ℝ) / 2 ≤ ‖z + n‖ := by
      have htri : ‖(n : ℂ)‖ ≤ ‖z + n‖ + ‖z‖ := by
        simpa [sub_eq_add_neg] using (norm_sub_le (z + n) z)
      have htri' : (n : ℝ) ≤ ‖z + n‖ + ‖z‖ := by
        simpa [hnorm_n] using htri
      have hmid : (n : ℝ) - ‖z‖ ≤ ‖z + n‖ := by linarith
      have hmid' : (n : ℝ) / 2 ≤ (n : ℝ) - ‖z‖ := by nlinarith [hN]
      exact le_trans hmid' hmid
    have h_term_norm :
        ‖term n‖ = ‖z - 1‖ / ((n + 1) * ‖z + n‖) := by
      have hnnorm : ‖(n + 1 : ℂ)‖ = (n + 1 : ℝ) := by
        simpa using (Complex.norm_natCast (n + 1))
      simp [h_term n, hnnorm, mul_comm]
    have hnn : (n : ℝ) ≤ (n + 1 : ℝ) := by nlinarith
    calc
      ‖term n‖
          = ‖z - 1‖ / ((n + 1) * ‖z + n‖) := h_term_norm
      _ ≤ ‖z - 1‖ / ((n : ℝ) * ((n : ℝ) / 2)) := by
        have hden : (n : ℝ) * ((n : ℝ) / 2) ≤ (n + 1) * ‖z + n‖ := by
          have h1 : (n : ℝ) * ((n : ℝ) / 2) ≤ (n : ℝ) * ‖z + n‖ := by
            exact mul_le_mul_of_nonneg_left h_lower (by positivity)
          have h2 : (n : ℝ) * ‖z + n‖ ≤ (n + 1) * ‖z + n‖ := by
            exact mul_le_mul_of_nonneg_right hnn (by positivity)
          exact le_trans h1 h2
        have hn1 : (1 : ℕ) ≤ n := by
          have hN1 : (1 : ℕ) ≤ N := by
            simpa [N] using Nat.succ_le_succ (Nat.zero_le (Nat.ceil (2 * ‖z‖)))
          exact Nat.le_trans hN1 hn
        have hpos : 0 < (n : ℝ) * ((n : ℝ) / 2) := by
          have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
          nlinarith [hnpos]
        have hnum : 0 ≤ ‖z - 1‖ := by exact norm_nonneg _
        exact (div_le_div_of_nonneg_left hnum hpos hden)
      _ = (2 * ‖z - 1‖) / (n ^ 2 : ℝ) := by ring_nf
  have h_series :
      Summable (fun n : ℕ => (2 * ‖z - 1‖) / (n ^ 2 : ℝ)) := by
    exact Summable.mul_left _ (Real.summable_nat_pow_inv.2 one_lt_two)
  have h_series_shift :
      Summable (fun n : ℕ => (2 * ‖z - 1‖) / ((n + N) ^ 2 : ℝ)) := by
    simpa using (summable_nat_add_iff N).2 h_series
  have h_tail : Summable (fun n : ℕ => ‖term (n + N)‖) := by
    refine Summable.of_nonneg_of_le
      (f := fun n : ℕ => (2 * ‖z - 1‖) / ((n + N) ^ 2 : ℝ))
      (g := fun n : ℕ => ‖term (n + N)‖) ?_ ?_ h_series_shift
    · intro n
      exact norm_nonneg _
    · intro n
      have hge : n + N ≥ N := Nat.le_add_left _ _
      simpa using h_bound (n + N) hge
  have h_norm : Summable (fun n : ℕ => ‖term n‖) :=
    (summable_nat_add_iff N).1 h_tail
  have h_sum : Summable term := Summable.of_norm h_norm
  simpa [term] using h_sum

lemma digammaSeq_tendsto_series (z : ℂ) (hz : ∀ n : ℕ, z + n ≠ 0) :
    Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop
      (nhds ((-Real.eulerMascheroniConstant : ℝ) +
        ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (z + n)) : ℂ)) := by
  let term : ℕ → ℂ := fun n => (1 / (n + 1 : ℂ) - 1 / (z + n))
  have h_term_sum : Summable term := digamma_series_summable z hz
  have h_term_tendsto :
      Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), term k) Filter.atTop
        (nhds (∑' n : ℕ, term n)) := by
    exact (h_term_sum.hasSum.tendsto_sum_nat).comp (Filter.tendsto_add_atTop_nat 1)
  have h_harm_shift :
      Filter.Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log ((n : ℝ) + 1))
        Filter.atTop (nhds Real.eulerMascheroniConstant) := by
    refine (Real.tendsto_harmonic_sub_log.comp (Filter.tendsto_add_atTop_nat 1)).congr ?_
    intro n
    simp [Function.comp, Nat.cast_add, Nat.cast_one]
  have h_log_shift :
      Filter.Tendsto (fun n : ℕ => Real.log ((n : ℝ) + 1) - Real.log n) Filter.atTop (nhds 0) :=
    Real.tendsto_log_nat_add_one_sub_log
  have h_harm_log :
      Filter.Tendsto (fun n : ℕ => (harmonic (n + 1) : ℝ) - Real.log n) Filter.atTop
        (nhds Real.eulerMascheroniConstant) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_harm_shift.add h_log_shift
  have h_log_harm_real :
      Filter.Tendsto (fun n : ℕ => Real.log n - (harmonic (n + 1) : ℝ)) Filter.atTop
        (nhds (-Real.eulerMascheroniConstant)) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h_harm_log.neg
  have h_log_harm :
      Filter.Tendsto (fun n : ℕ => Complex.ofReal (Real.log n - (harmonic (n + 1) : ℝ)))
        Filter.atTop (nhds ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) :=
    Filter.Tendsto.ofReal h_log_harm_real
  have h_first :
      Filter.Tendsto (fun n : ℕ =>
        (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ))) Filter.atTop
        (nhds ((-Real.eulerMascheroniConstant : ℝ) : ℂ)) := by
    refine h_log_harm.congr ?_
    intro n
    calc
      Complex.ofReal (Real.log n - (harmonic (n + 1) : ℝ))
          = (Real.log n : ℂ) - ((harmonic (n + 1) : ℝ) : ℂ) := by
              simp [Complex.ofReal_sub]
      _ = (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ)) := by
              have hsum :
                  ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ)) =
                    ((harmonic (n + 1) : ℝ) : ℂ) := by
                simpa using (sum_range_inv_eq_harmonic_real (n + 1))
              rw [← hsum]
  have h_sum :
      Filter.Tendsto
          (fun n : ℕ =>
            (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), (1 / (k + 1 : ℂ)) +
              ∑ k ∈ Finset.range (n + 1), term k)
          Filter.atTop
          (nhds ((-Real.eulerMascheroniConstant : ℝ) +
            ∑' n : ℕ, term n : ℂ)) := by
    simpa using h_first.add h_term_tendsto
  refine h_sum.congr ?_
  intro n
  simpa [term] using (digammaSeq_eq_split z n).symm

lemma digamma_eq_series_of_tendsto (z : ℂ) (hz : ∀ n : ℕ, z + n ≠ 0)
    (h_tendsto : Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop
      (nhds (Q3.digamma z))) :
    Q3.digamma z =
      ((-Real.eulerMascheroniConstant : ℝ) +
        ∑' n : ℕ, (1 / (n + 1 : ℂ) - 1 / (z + n)) : ℂ) := by
  have h_series := digammaSeq_tendsto_series z hz
  exact tendsto_nhds_unique h_tendsto h_series

lemma re_digamma_eq_sum_of_tendsto (z : ℂ) (hz : ∀ n : ℕ, z + n ≠ 0)
    (h_tendsto : Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop
      (nhds (Q3.digamma z))) :
    (Q3.digamma z).re =
      -Real.eulerMascheroniConstant +
        ∑' n : ℕ, ((1 / (n + 1 : ℂ) - 1 / (z + n)).re) := by
  let term : ℕ → ℂ := fun n => (1 / (n + 1 : ℂ) - 1 / (z + n))
  have h_series := digamma_eq_series_of_tendsto z hz h_tendsto
  have hsum : Summable term := digamma_series_summable z hz
  have hre : ((∑' n : ℕ, term n).re) = ∑' n : ℕ, (term n).re := by
    simpa using (Complex.re_tsum hsum)
  have hcast : ((-Real.eulerMascheroniConstant : ℝ) : ℂ).re =
      -Real.eulerMascheroniConstant := by simp
  have h_re : (Q3.digamma z).re =
      ((-Real.eulerMascheroniConstant : ℝ) : ℂ).re + (∑' n : ℕ, term n).re := by
    simpa [term] using (congrArg Complex.re h_series)
  calc
    (Q3.digamma z).re =
        ((-Real.eulerMascheroniConstant : ℝ) : ℂ).re + (∑' n : ℕ, term n).re := h_re
    _ = -Real.eulerMascheroniConstant + ∑' n : ℕ, (term n).re := by
        rw [hcast, hre]

end Q3

end
