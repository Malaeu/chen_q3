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

/-- One-step right-half-plane recurrence for the Q3 digamma function.

This local form avoids adding a new Gamma-functional-equation dependency to
the Step33 endpoint backend. It is proved from the already checked
`digammaSeq` convergence surface and a telescoping finite-sum identity. -/
lemma digamma_add_one_of_re_pos (z : ℂ) (hzpos : 0 < z.re) :
    Q3.digamma (z + 1) = Q3.digamma z + z⁻¹ := by
  have hz1pos : 0 < (z + 1).re := by
    simp [Complex.add_re]
    linarith
  have htz := digammaSeq_tendsto_Q3_digamma z hzpos
  have htz1 := digammaSeq_tendsto_Q3_digamma (z + 1) hz1pos
  have h_diff : ∀ n : ℕ,
      _root_.digammaSeq (z + 1) n - _root_.digammaSeq z n =
        z⁻¹ - (z + ((n : ℂ) + 1))⁻¹ := by
    intro n
    unfold digammaSeq
    have htel := Finset.sum_range_sub'
      (fun x => (z + (x : ℂ))⁻¹) (n + 1)
    simp [one_div, add_comm, add_left_comm, Finset.sum_range_succ] at htel ⊢
    exact htel
  have h_limit : Filter.Tendsto
      (fun n : ℕ => z⁻¹ - (z + ((n : ℂ) + 1))⁻¹)
      Filter.atTop (nhds z⁻¹) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simp [sub_eq_add_neg, add_comm, add_left_comm]
    refine Filter.Tendsto.inv_tendsto_atTop ?_
    rw [Filter.tendsto_atTop_atTop]
    intro r
    refine ⟨Nat.ceil (max r 0 + ‖z‖ + 2), ?_⟩
    intro n hn
    have hnreal : max r 0 + ‖z‖ + 2 <= (n : ℝ) := by
      exact le_trans (Nat.le_ceil _) (by exact_mod_cast hn)
    have hnorm_n : ‖(n : ℂ)‖ = (n : ℝ) := by simp
    have hle : max r 0 + 1 <= ‖z + ((n : ℂ) + 1)‖ := by
      have htri : ‖(n : ℂ)‖ <= ‖z + ((n : ℂ) + 1)‖ + ‖z + 1‖ := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
          norm_sub_le (z + ((n : ℂ) + 1)) (z + 1)
      have hz1norm : ‖z + 1‖ <= ‖z‖ + 1 := by
        simpa using norm_add_le z (1 : ℂ)
      have hmid : (n : ℝ) <= ‖z + ((n : ℂ) + 1)‖ + (‖z‖ + 1) := by
        linarith
      linarith
    have hrle : r <= max r 0 + 1 := by
      have : r <= max r 0 := le_max_left _ _
      linarith
    exact le_trans hrle hle
  have h_limit_diff : Filter.Tendsto
      (fun n : ℕ => _root_.digammaSeq (z + 1) n - _root_.digammaSeq z n)
      Filter.atTop (nhds z⁻¹) := by
    simpa [h_diff] using h_limit
  have h_sub : Q3.digamma (z + 1) - Q3.digamma z = z⁻¹ :=
    tendsto_nhds_unique (Filter.Tendsto.sub htz1 htz) h_limit_diff
  exact sub_eq_iff_eq_add'.mp h_sub

/-- Finite right-shift recurrence for the Q3 digamma function on the
right half-plane. -/
lemma digamma_add_nat_of_re_pos (z : ℂ) (N : ℕ) (hzpos : 0 < z.re) :
    Q3.digamma (z + (N : ℂ)) =
      Q3.digamma z + (Finset.range N).sum (fun m : ℕ => (z + (m : ℂ))⁻¹) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hzNpos : 0 < (z + (N : ℂ)).re := by
        simp [Complex.add_re]
        have hNnonneg : (0 : ℝ) <= N := by exact_mod_cast Nat.zero_le N
        linarith
      calc
        Q3.digamma (z + ((N + 1 : ℕ) : ℂ))
            = Q3.digamma (z + (N : ℂ) + 1) := by
              congr 1
              norm_num [Nat.cast_add, Nat.cast_one]
              ring
        _ = Q3.digamma (z + (N : ℂ)) + (z + (N : ℂ))⁻¹ :=
              digamma_add_one_of_re_pos (z + (N : ℂ)) hzNpos
        _ = Q3.digamma z +
              (Finset.range (N + 1)).sum (fun m : ℕ => (z + (m : ℂ))⁻¹) := by
              rw [ih]
              simp [Finset.sum_range_succ, add_assoc]

/-- The concrete 16-step recurrence requested by the shifted-digamma
rectangular endpoint route. -/
theorem digamma_shift16_recurrence_of_re_pos (z : ℂ) (hzpos : 0 < z.re) :
    Q3.digamma z =
      Q3.digamma (z + (16 : ℂ)) -
        (Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹) := by
  have h := digamma_add_nat_of_re_pos z 16 hzpos
  exact eq_sub_of_add_eq h.symm

/-- Rectangular interval glue for the 16-step shifted-digamma route.

Generated endpoint rows can prove a rectangle for `Q3.digamma (z+16)` and a
rectangle for the finite inverse sum. Lean then checks the recurrence and the
componentwise subtraction arithmetic. -/
theorem digamma_interval_of_shift16_rect
    (z : ℂ)
    (reLower reUpper imLower imUpper shiftedReLower shiftedReUpper shiftedImLower
      shiftedImUpper invReLower invReUpper invImLower invImUpper : ℝ)
    (hzpos : 0 < z.re)
    (hShiftReLower : shiftedReLower <= (Q3.digamma (z + (16 : ℂ))).re)
    (hShiftReUpper : (Q3.digamma (z + (16 : ℂ))).re <= shiftedReUpper)
    (hShiftImLower : shiftedImLower <= (Q3.digamma (z + (16 : ℂ))).im)
    (hShiftImUpper : (Q3.digamma (z + (16 : ℂ))).im <= shiftedImUpper)
    (hInvReLower :
      invReLower <=
        ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).re)
    (hInvReUpper :
      ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).re <=
        invReUpper)
    (hInvImLower :
      invImLower <=
        ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).im)
    (hInvImUpper :
      ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).im <=
        invImUpper)
    (hReLower : reLower <= shiftedReLower - invReUpper)
    (hReUpper : shiftedReUpper - invReLower <= reUpper)
    (hImLower : imLower <= shiftedImLower - invImUpper)
    (hImUpper : shiftedImUpper - invImLower <= imUpper) :
    reLower <= (Q3.digamma z).re ∧ (Q3.digamma z).re <= reUpper ∧
      imLower <= (Q3.digamma z).im ∧ (Q3.digamma z).im <= imUpper := by
  let invSum : ℂ := (Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)
  have hrec := digamma_shift16_recurrence_of_re_pos z hzpos
  have hReEq :
      (Q3.digamma z).re =
        (Q3.digamma (z + (16 : ℂ))).re - invSum.re := by
    change (Q3.digamma z).re =
      (Q3.digamma (z + (16 : ℂ))).re -
        ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).re
    simpa [sub_eq_add_neg] using congrArg Complex.re hrec
  have hImEq :
      (Q3.digamma z).im =
        (Q3.digamma (z + (16 : ℂ))).im - invSum.im := by
    change (Q3.digamma z).im =
      (Q3.digamma (z + (16 : ℂ))).im -
        ((Finset.range 16).sum (fun m : ℕ => (z + (m : ℂ))⁻¹)).im
    simpa [sub_eq_add_neg] using congrArg Complex.im hrec
  constructor
  · rw [hReEq]
    linarith
  constructor
  · rw [hReEq]
    linarith
  constructor
  · rw [hImEq]
    linarith
  · rw [hImEq]
    linarith

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

/-- Imaginary-part companion to `re_digamma_eq_sum_of_tendsto`.

Unlike the real-part formula, the Euler-Mascheroni constant drops out after
taking imaginary parts.  This gives the Step33 shifted-digamma rectangular
receiver a semantic series surface for future generated `Im ψ(z)` interval
payloads without introducing any numerical oracle. -/
lemma im_digamma_eq_sum_of_tendsto (z : ℂ) (hz : ∀ n : ℕ, z + n ≠ 0)
    (h_tendsto : Filter.Tendsto (fun n : ℕ => _root_.digammaSeq z n) Filter.atTop
      (nhds (Q3.digamma z))) :
    (Q3.digamma z).im =
        ∑' n : ℕ, ((1 / (n + 1 : ℂ) - 1 / (z + n)).im) := by
  let term : ℕ → ℂ := fun n => (1 / (n + 1 : ℂ) - 1 / (z + n))
  have h_series := digamma_eq_series_of_tendsto z hz h_tendsto
  have hsum : Summable term := digamma_series_summable z hz
  have him : ((∑' n : ℕ, term n).im) = ∑' n : ℕ, (term n).im := by
    simpa using (Complex.im_tsum hsum)
  have hcast : ((-Real.eulerMascheroniConstant : ℝ) : ℂ).im = 0 := by
    simp
  have h_im : (Q3.digamma z).im =
      ((-Real.eulerMascheroniConstant : ℝ) : ℂ).im + (∑' n : ℕ, term n).im := by
    simpa [term] using (congrArg Complex.im h_series)
  calc
    (Q3.digamma z).im =
        ((-Real.eulerMascheroniConstant : ℝ) : ℂ).im + (∑' n : ℕ, term n).im := h_im
    _ = ∑' n : ℕ, (term n).im := by
        rw [hcast, him]
        simp

/-- Bound a real `tsum` from a finite prefix and a signed tail interval.

This small generic receiver is used by generated digamma component rows: the
generator proves rational bounds for the finite prefix and a separate tail
interval, while Lean checks the safe `sum_range + shifted_tail = tsum` split. -/
theorem real_tsum_bounds_of_sum_range_tail_interval
    {f : Nat -> Real} (N : Nat)
    (prefixLower prefixUpper tailLower tailUpper : Real)
    (hf : Summable f)
    (hPrefixLower : prefixLower <= (Finset.range N).sum f)
    (hPrefixUpper : (Finset.range N).sum f <= prefixUpper)
    (hTailLower : tailLower <= ∑' n : Nat, f (n + N))
    (hTailUpper : (∑' n : Nat, f (n + N)) <= tailUpper) :
    prefixLower + tailLower <= ∑' n : Nat, f n ∧
      (∑' n : Nat, f n) <= prefixUpper + tailUpper := by
  have hsplit :
      (Finset.range N).sum f + (∑' n : Nat, f (n + N)) =
        ∑' n : Nat, f n := by
    simpa using (hf.sum_add_tsum_nat_add N)
  constructor
  · rw [← hsplit]
    linarith
  · rw [← hsplit]
    linarith

/-- Bound a real `tsum` from a finite prefix and an absolute tail radius. -/
theorem real_tsum_bounds_of_sum_range_tail_abs
    {f : Nat -> Real} (N : Nat) (prefixLower prefixUpper tailRadius : Real)
    (hf : Summable f)
    (hPrefixLower : prefixLower <= (Finset.range N).sum f)
    (hPrefixUpper : (Finset.range N).sum f <= prefixUpper)
    (hTail : |∑' n : Nat, f (n + N)| <= tailRadius) :
    prefixLower - tailRadius <= ∑' n : Nat, f n ∧
      (∑' n : Nat, f n) <= prefixUpper + tailRadius := by
  have hTailLower : -tailRadius <= ∑' n : Nat, f (n + N) :=
    (abs_le.mp hTail).1
  have hTailUpper : (∑' n : Nat, f (n + N)) <= tailRadius :=
    (abs_le.mp hTail).2
  simpa [sub_eq_add_neg] using
    real_tsum_bounds_of_sum_range_tail_interval
      (f := f) N prefixLower prefixUpper (-tailRadius) tailRadius hf
      hPrefixLower hPrefixUpper hTailLower hTailUpper

/-- A single complex norm-tail majorant supplies absolute tail radii for both
real and imaginary digamma series components.

Generated endpoint rows can prove one nonnegative complex majorant and reuse it
for the Re/Im component receivers without duplicating tail proof data. -/
theorem digamma_series_tail_re_im_abs_of_complex_norm_tail
    (z : Complex) (N : Nat) (tailRadius : Real)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hTailNorm :
      (∑' n : Nat,
          ‖1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))‖) <= tailRadius) :
    |∑' n : Nat,
        (1 / (((n + N : Nat) : Complex) + 1) -
          1 / (z + ((n + N : Nat) : Complex))).re| <= tailRadius ∧
      |∑' n : Nat,
        (1 / (((n + N : Nat) : Complex) + 1) -
          1 / (z + ((n + N : Nat) : Complex))).im| <= tailRadius := by
  let term : Nat -> Complex := fun n : Nat =>
    1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))
  have hComplex : Summable term := by
    simpa [term] using digamma_series_summable z hz
  have hTailComplex : Summable (fun n : Nat => term (n + N)) := by
    simpa [term, Nat.cast_add, add_assoc] using
      (summable_nat_add_iff N).2 hComplex
  have hNormSum :
      ‖∑' n : Nat, term (n + N)‖ <=
        ∑' n : Nat, ‖term (n + N)‖ := by
    exact norm_tsum_le_tsum_norm hTailComplex.norm
  have hNormTail :
      ∑' n : Nat, ‖term (n + N)‖ <= tailRadius := by
    simpa [term, Nat.cast_add, add_assoc] using hTailNorm
  have hReAbs :
      |(∑' n : Nat, term (n + N)).re| <= tailRadius :=
    (Complex.abs_re_le_norm _).trans (hNormSum.trans hNormTail)
  have hImAbs :
      |(∑' n : Nat, term (n + N)).im| <= tailRadius :=
    (Complex.abs_im_le_norm _).trans (hNormSum.trans hNormTail)
  have hReTsum :
      ((∑' n : Nat, term (n + N)).re) =
        ∑' n : Nat, (term (n + N)).re := by
    simpa using (Complex.re_tsum hTailComplex)
  have hImTsum :
      ((∑' n : Nat, term (n + N)).im) =
        ∑' n : Nat, (term (n + N)).im := by
    simpa using (Complex.im_tsum hTailComplex)
  constructor
  · change |∑' n : Nat, (term (n + N)).re| <= tailRadius
    rw [← hReTsum]
    exact hReAbs
  · change |∑' n : Nat, (term (n + N)).im| <= tailRadius
    rw [← hImTsum]
    exact hImAbs

/-- Bound the complex norm tail of the digamma series from a generated
termwise majorant.

This is the proof-data landing surface one level below
`digamma_series_tail_re_im_abs_of_complex_norm_tail`: generated rows can prove
`‖tailTerm n‖ <= g n` and a rational bound on `∑' g n`, while Lean supplies the
summability and `tsum` monotonicity bridge. -/
theorem digamma_series_tail_norm_le_of_norm_le_tsum_bound
    (z : Complex) (N : Nat) (g : Nat -> Real) (tailRadius : Real)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hg : Summable g)
    (hTerm :
      ∀ n : Nat,
        ‖1 / (((n + N : Nat) : Complex) + 1) -
          1 / (z + ((n + N : Nat) : Complex))‖ <= g n)
    (hSum : (∑' n : Nat, g n) <= tailRadius) :
    (∑' n : Nat,
        ‖1 / (((n + N : Nat) : Complex) + 1) -
          1 / (z + ((n + N : Nat) : Complex))‖) <= tailRadius := by
  let term : Nat -> Complex := fun n : Nat =>
    1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))
  have hComplex : Summable term := by
    simpa [term] using digamma_series_summable z hz
  have hTailComplex : Summable (fun n : Nat => term (n + N)) := by
    simpa [term, Nat.cast_add, add_assoc] using
      (summable_nat_add_iff N).2 hComplex
  have hTerm' : ∀ n : Nat, ‖term (n + N)‖ <= g n := by
    intro n
    simpa [term, Nat.cast_add, add_assoc] using hTerm n
  have hLe :
      (∑' n : Nat, ‖term (n + N)‖) <= ∑' n : Nat, g n := by
    exact Summable.tsum_le_tsum hTerm' hTailComplex.norm hg
  have hLe' :
      (∑' n : Nat,
          ‖1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))‖) <=
        ∑' n : Nat, g n := by
    simpa [term, Nat.cast_add, add_assoc] using hLe
  exact hLe'.trans hSum

/-- Generated-facing interval receiver for the imaginary part of the digamma
series.

The conclusion is an interval for `(Q3.digamma z).im`; generated rows supply a
finite prefix enclosure for the semantic series and a signed tail interval.
No Euler-Mascheroni or `log π` constant is involved. -/
theorem im_digamma_interval_of_series_prefix_tail_interval
    (z : ℂ) (N : Nat)
    (lower upper prefixLower prefixUpper tailLower tailUpper : Real)
    (hzpos : 0 < z.re)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hPrefixLower :
      prefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).im))
    (hPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).im) <=
        prefixUpper)
    (hTailLower :
      tailLower <=
        ∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).im)
    (hTailUpper :
      (∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).im) <=
        tailUpper)
    (hLower : lower <= prefixLower + tailLower)
    (hUpper : prefixUpper + tailUpper <= upper) :
    lower <= (Q3.digamma z).im ∧
      (Q3.digamma z).im <= upper := by
  let term : Nat -> Real := fun n : Nat =>
    (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).im
  have hComplex : Summable (fun n : Nat =>
      1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))) :=
    digamma_series_summable z hz
  have hTerm : Summable term := by
    exact Complex.imCLM.summable hComplex
  have hTsum :=
    real_tsum_bounds_of_sum_range_tail_interval
      (f := term) N prefixLower prefixUpper tailLower tailUpper hTerm
      (by simpa [term] using hPrefixLower)
      (by simpa [term] using hPrefixUpper)
      (by simpa [term, Nat.cast_add, add_assoc] using hTailLower)
      (by simpa [term, Nat.cast_add, add_assoc] using hTailUpper)
  have hDig :
      (Q3.digamma z).im = ∑' n : Nat, term n := by
    simpa [term] using
      im_digamma_eq_sum_of_tendsto z hz
        (digammaSeq_tendsto_Q3_digamma z hzpos)
  constructor
  · rw [hDig]
    exact hLower.trans hTsum.1
  · rw [hDig]
    exact hTsum.2.trans hUpper

/-- Absolute-tail variant of
`im_digamma_interval_of_series_prefix_tail_interval`. -/
theorem im_digamma_interval_of_series_prefix_tail_abs
    (z : ℂ) (N : Nat)
    (lower upper prefixLower prefixUpper tailRadius : Real)
    (hzpos : 0 < z.re)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hPrefixLower :
      prefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).im))
    (hPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).im) <=
        prefixUpper)
    (hTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).im| <=
        tailRadius)
    (hLower : lower <= prefixLower - tailRadius)
    (hUpper : prefixUpper + tailRadius <= upper) :
    lower <= (Q3.digamma z).im ∧
      (Q3.digamma z).im <= upper := by
  exact
    im_digamma_interval_of_series_prefix_tail_interval
      z N lower upper prefixLower prefixUpper (-tailRadius) tailRadius
      hzpos hz hPrefixLower hPrefixUpper
      (abs_le.mp hTail).1 (abs_le.mp hTail).2
      (by simpa [sub_eq_add_neg] using hLower) hUpper

/-- Generated-facing interval receiver for the real part of the digamma
series.

The real component carries the `-γ` constant.  Generated rows may prove a
separate Euler-Mascheroni interval and combine it with prefix/tail bounds for
the semantic digamma series. -/
theorem re_digamma_interval_of_series_prefix_tail_interval
    (z : ℂ) (N : Nat)
    (lower upper gammaLower gammaUpper prefixLower prefixUpper tailLower
      tailUpper : Real)
    (hzpos : 0 < z.re)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hPrefixLower :
      prefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).re))
    (hPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).re) <=
        prefixUpper)
    (hTailLower :
      tailLower <=
        ∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).re)
    (hTailUpper :
      (∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).re) <=
        tailUpper)
    (hLower : lower <= -gammaUpper + prefixLower + tailLower)
    (hUpper : -gammaLower + prefixUpper + tailUpper <= upper) :
    lower <= (Q3.digamma z).re ∧
      (Q3.digamma z).re <= upper := by
  let term : Nat -> Real := fun n : Nat =>
    (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).re
  have hComplex : Summable (fun n : Nat =>
      1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))) :=
    digamma_series_summable z hz
  have hTerm : Summable term := by
    exact Complex.reCLM.summable hComplex
  have hTsum :=
    real_tsum_bounds_of_sum_range_tail_interval
      (f := term) N prefixLower prefixUpper tailLower tailUpper hTerm
      (by simpa [term] using hPrefixLower)
      (by simpa [term] using hPrefixUpper)
      (by simpa [term, Nat.cast_add, add_assoc] using hTailLower)
      (by simpa [term, Nat.cast_add, add_assoc] using hTailUpper)
  have hDig :
      (Q3.digamma z).re =
        -Real.eulerMascheroniConstant + ∑' n : Nat, term n := by
    simpa [term] using
      re_digamma_eq_sum_of_tendsto z hz
        (digammaSeq_tendsto_Q3_digamma z hzpos)
  constructor
  · rw [hDig]
    calc
      lower <= -gammaUpper + prefixLower + tailLower := hLower
      _ <= -Real.eulerMascheroniConstant + ∑' n : Nat, term n := by
        linarith [hGammaUpper, hTsum.1]
  · rw [hDig]
    calc
      -Real.eulerMascheroniConstant + ∑' n : Nat, term n <=
          -gammaLower + prefixUpper + tailUpper := by
        linarith [hGammaLower, hTsum.2]
      _ <= upper := hUpper

/-- Absolute-tail variant of
`re_digamma_interval_of_series_prefix_tail_interval`. -/
theorem re_digamma_interval_of_series_prefix_tail_abs
    (z : ℂ) (N : Nat)
    (lower upper gammaLower gammaUpper prefixLower prefixUpper tailRadius : Real)
    (hzpos : 0 < z.re)
    (hz : ∀ n : Nat, z + n ≠ 0)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hPrefixLower :
      prefixLower <=
        (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).re))
    (hPrefixUpper :
      (Finset.range N).sum (fun n : Nat =>
          (1 / ((n : Complex) + 1) - 1 / (z + (n : Complex))).re) <=
        prefixUpper)
    (hTail :
      |∑' n : Nat,
          (1 / (((n + N : Nat) : Complex) + 1) -
            1 / (z + ((n + N : Nat) : Complex))).re| <=
        tailRadius)
    (hLower : lower <= -gammaUpper + prefixLower - tailRadius)
    (hUpper : -gammaLower + prefixUpper + tailRadius <= upper) :
    lower <= (Q3.digamma z).re ∧
      (Q3.digamma z).re <= upper := by
  exact
    re_digamma_interval_of_series_prefix_tail_interval
      z N lower upper gammaLower gammaUpper prefixLower prefixUpper
      (-tailRadius) tailRadius hzpos hz hGammaLower hGammaUpper
      hPrefixLower hPrefixUpper (abs_le.mp hTail).1 (abs_le.mp hTail).2
      (by simpa [sub_eq_add_neg] using hLower) hUpper

/-- Mathlib's bracketing sequences give a proof-safe interval for the
Euler-Mascheroni constant at every finite index.  Numerical rows can choose a
concrete index and then discharge the remaining finite/log arithmetic
separately. -/
theorem eulerMascheroniConstant_interval_of_seq (n : Nat) :
    Real.eulerMascheroniSeq n <= Real.eulerMascheroniConstant ∧
      Real.eulerMascheroniConstant <= Real.eulerMascheroniSeq' n := by
  exact
    ⟨le_of_lt (Real.eulerMascheroniSeq_lt_eulerMascheroniConstant n),
      le_of_lt (Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n)⟩

/-- Exact width of Mathlib's elementary Euler-Mascheroni bracket.

This is a diagnostic fact for tight Step33 endpoint constants: using only
`eulerMascheroniSeq` / `eulerMascheroniSeq'` gives a gap
`log (n + 1) - log n`, so very narrow generated endpoint intervals require an
accelerated constant backend rather than a huge finite index. -/
theorem eulerMascheroniSeq_interval_width
    (n : Nat) (hn : n ≠ 0) :
    Real.eulerMascheroniSeq' n - Real.eulerMascheroniSeq n =
      Real.log (n + 1 : Real) - Real.log (n : Real) := by
  rw [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq']
  simp [hn]

/-- Turn explicit exponential comparisons around `π` into a logarithmic
interval for `log π`.  This keeps the numerical `exp`/`π` witnesses outside
the semantic digamma series proof. -/
theorem log_pi_interval_of_exp_bounds
    (lower upper piLower piUpper : Real)
    (hExpLower : Real.exp lower <= piLower)
    (hPiLower : piLower <= Real.pi)
    (hPiUpper : Real.pi <= piUpper)
    (hPiUpperExp : piUpper <= Real.exp upper) :
    lower <= Real.log Real.pi ∧ Real.log Real.pi <= upper := by
  constructor
  · exact
      (Real.le_log_iff_exp_le Real.pi_pos).mpr
        (hExpLower.trans hPiLower)
  · exact
      (Real.log_le_iff_le_exp Real.pi_pos).mpr
        (hPiUpper.trans hPiUpperExp)

/-- Assemble independent `γ` and `log π` intervals into the constant interval
needed by the Step22 Omega real-series endpoint receiver. -/
theorem neg_eulerMascheroni_sub_log_pi_intervalCert
    (lower upper gammaLower gammaUpper logPiLower logPiUpper : Real)
    (hGammaLower : gammaLower <= Real.eulerMascheroniConstant)
    (hGammaUpper : Real.eulerMascheroniConstant <= gammaUpper)
    (hLogPiLower : logPiLower <= Real.log Real.pi)
    (hLogPiUpper : Real.log Real.pi <= logPiUpper)
    (hLower : lower <= -gammaUpper - logPiUpper)
    (hUpper : -gammaLower - logPiLower <= upper) :
    lower <= -Real.eulerMascheroniConstant - Real.log Real.pi ∧
      -Real.eulerMascheroniConstant - Real.log Real.pi <= upper := by
  constructor
  · have hActualLower :
        -gammaUpper - logPiUpper <=
          -Real.eulerMascheroniConstant - Real.log Real.pi := by
      linarith
    exact hLower.trans hActualLower
  · have hActualUpper :
        -Real.eulerMascheroniConstant - Real.log Real.pi <=
          -gammaLower - logPiLower := by
      linarith
    exact hActualUpper.trans hUpper

/-- Variant using Mathlib's Euler-Mascheroni bracketing sequence directly for
the `γ` part.  This is useful for diagnosing whether a proposed generated
constant interval is even feasible before building a sharper acceleration
engine. -/
theorem neg_eulerMascheroni_sub_log_pi_intervalCert_of_seq
    (n : Nat) (lower upper logPiLower logPiUpper : Real)
    (hLogPiLower : logPiLower <= Real.log Real.pi)
    (hLogPiUpper : Real.log Real.pi <= logPiUpper)
    (hLower : lower <= -Real.eulerMascheroniSeq' n - logPiUpper)
    (hUpper : -Real.eulerMascheroniSeq n - logPiLower <= upper) :
    lower <= -Real.eulerMascheroniConstant - Real.log Real.pi ∧
      -Real.eulerMascheroniConstant - Real.log Real.pi <= upper := by
  have hgamma := eulerMascheroniConstant_interval_of_seq n
  exact
    neg_eulerMascheroni_sub_log_pi_intervalCert
      lower upper (Real.eulerMascheroniSeq n) (Real.eulerMascheroniSeq' n)
      logPiLower logPiUpper hgamma.1 hgamma.2 hLogPiLower hLogPiUpper
      hLower hUpper

end Q3

end
