import Q3.Proofs.RouteB.TwoSidedNormalizedBControl
import Q3.Proofs.RouteB.SafeBridgeFalsifiers

set_option linter.mathlibStandardSet false

open Filter Topology
open scoped Topology

noncomputable section
namespace Q3.RouteB

variable {𝕜 E : Type*} [NormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Exact algebraic normalization identity. The arbitrary parameter later named
`W` is only a supplied error majorant; no Route-B detector is defined here. -/
theorem normalize_scalar_error_identity
    (b : 𝕜) (F X : E) (hb : b ≠ 0) :
    b⁻¹ • F - X = b⁻¹ • (F - b • X) := by
  rw [smul_sub, smul_smul]
  simp [hb]

theorem norm_normalized_error_eq
    (b : 𝕜) (F X : E) (hb : b ≠ 0) :
    ‖b⁻¹ • F - X‖ = ‖b‖⁻¹ * ‖F - b • X‖ := by
  rw [normalize_scalar_error_identity b F X hb, norm_smul, norm_inv]

theorem normalized_tracking_error_le
    (b : 𝕜) (F X : E) (A R W eps : ℝ)
    (hb : b ≠ 0) (hR : 0 ≤ R) (hrecip : ‖b‖⁻¹ ≤ R)
    (habsolute : ‖F - b • X‖ ≤ A * (W + eps)) :
    ‖b⁻¹ • F - X‖ ≤ A * (R * W + R * eps) := by
  rw [norm_normalized_error_eq b F X hb]
  have hmul := mul_le_mul hrecip habsolute (norm_nonneg _) hR
  calc
    ‖b‖⁻¹ * ‖F - b • X‖ ≤ R * (A * (W + eps)) := hmul
    _ = A * (R * W + R * eps) := by ring

/-- Relative decay of both supplied error channels gives uniform convergence
of the normalized family on the supplied set. -/
theorem tendstoUniformlyOn_normalized_tracking_of_relative_rates
    {ι α : Type*} {l : Filter ι} [NeBot l]
    (F : ι → α → E) (X : α → E) (b : ι → 𝕜)
    (A : ℝ) (R W eps : ι → ℝ) (K : Set α)
    (hb : ∀ᶠ i in l, b i ≠ 0)
    (hR : ∀ᶠ i in l, 0 ≤ R i)
    (hrecip : ∀ᶠ i in l, ‖b i‖⁻¹ ≤ R i)
    (habsolute : ∀ᶠ i in l, ∀ z ∈ K,
      ‖F i z - b i • X z‖ ≤ A * (W i + eps i))
    (hW : Tendsto (fun i => R i * W i) l (𝓝 0))
    (heps : Tendsto (fun i => R i * eps i) l (𝓝 0)) :
    TendstoUniformlyOn (fun i z => (b i)⁻¹ • F i z) X l K := by
  have hmajorant : Tendsto
      (fun i => A * (R i * W i + R i * eps i)) l (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (hW.add heps)
  rw [Metric.tendstoUniformlyOn_iff]
  intro epsilon hepsilon
  have hsmall : ∀ᶠ i in l,
      A * (R i * W i + R i * eps i) < epsilon :=
    (tendsto_order.1 hmajorant).2 epsilon hepsilon
  filter_upwards [hb, hR, hrecip, habsolute, hsmall] with
    i hbi hRi hreci habsi hsmalli
  intro z hz
  rw [dist_eq_norm, norm_sub_rev]
  exact (normalized_tracking_error_le
    (b i) (F i z) (X z) A (R i) (W i) (eps i)
    hbi hRi hreci (habsi z hz)).trans_lt hsmalli

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']

/-- Direct receiver for the already-proved H4c1 two-sided normalized `b`
control. It requires relative rates for the supplied `W` and residual channel. -/
theorem tendstoUniformlyOn_normalized_tracking_of_two_sided_b
    {ι α : Type*} {l : Filter ι} [NeBot l]
    (F : ι → α → E') (X : α → E')
    (scale b W eps : ι → ℝ) (A c_b C_b q_b : ℝ) (K : Set α)
    (hcb : 0 < c_b)
    (hscale : ∀ᶠ i in l, 0 < scale i)
    (hlower : ∀ᶠ i in l, c_b ≤ |b i| * scale i ^ (-q_b))
    (hupper : ∀ᶠ i in l, |b i| * scale i ^ (-q_b) ≤ C_b)
    (habsolute : ∀ᶠ i in l, ∀ z ∈ K,
      ‖F i z - b i • X z‖ ≤ A * (W i + eps i))
    (hW : Tendsto
      (fun i => (c_b⁻¹ * scale i ^ (-q_b)) * W i) l (𝓝 0))
    (heps : Tendsto
      (fun i => (c_b⁻¹ * scale i ^ (-q_b)) * eps i) l (𝓝 0)) :
    TendstoUniformlyOn (fun i z => (b i)⁻¹ • F i z) X l K := by
  obtain ⟨hb, _, hrecip⟩ :=
    two_sided_normalized_b_control_eventually
      scale b c_b C_b q_b hcb hscale hlower hupper
  have hR : ∀ᶠ i in l, 0 ≤ c_b⁻¹ * scale i ^ (-q_b) := by
    filter_upwards [hscale] with i hsi
    exact mul_nonneg (inv_nonneg.mpr hcb.le) (Real.rpow_nonneg hsi.le _)
  have hrecip' : ∀ᶠ i in l,
      ‖b i‖⁻¹ ≤ c_b⁻¹ * scale i ^ (-q_b) := by
    simpa [Real.norm_eq_abs] using hrecip
  exact tendstoUniformlyOn_normalized_tracking_of_relative_rates
    F X b A (fun i => c_b⁻¹ * scale i ^ (-q_b)) W eps K
    hb hR hrecip' habsolute hW heps

/-- After the reciprocal `b` factor is applied, the polynomial exponent no
longer contains `q_b`; relative detector decay needs a strictly stronger
margin unless additional information on `q_b` is supplied. -/
theorem relative_normalized_rate_exponent_neg_iff
    {r_alpha r_Delta : ℝ} :
    (1 + r_alpha - r_Delta) / 2 < 0 ↔
      r_Delta - r_alpha > 1 := by
  constructor <;> intro h <;> linarith

theorem safe_margin_does_not_imply_relative_rate_margin :
    ∃ q_b r_alpha r_Delta : ℝ,
      r_Delta - r_alpha > 2 * q_b + 1 ∧
      ¬ (1 + r_alpha - r_Delta) / 2 < 0 := by
  refine ⟨-1, 0, 0, ?_, ?_⟩ <;> norm_num

theorem lowerProductB_recip_mul_self_eq_one (n : ℕ) :
    |lowerProductB n|⁻¹ * lowerProductB n = 1 := by
  have hpos : 0 < (n : ℝ) + 1 := by positivity
  rw [lowerProductB, abs_of_pos (one_div_pos.mpr hpos)]
  field_simp

/-- Detector decay and the existing normalized lower-product plant do not by
themselves imply decay after division by `b`. -/
theorem detector_decay_does_not_imply_relative_decay :
    Tendsto lowerProductB atTop (𝓝 0) ∧
      ¬ Tendsto
        (fun n : ℕ => |lowerProductB n|⁻¹ * lowerProductB n)
        atTop (𝓝 0) := by
  refine ⟨lowerProductB_tendsto_zero, ?_⟩
  intro hzero
  have hone : Tendsto
      (fun n : ℕ => |lowerProductB n|⁻¹ * lowerProductB n)
      atTop (𝓝 1) := by
    convert (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)) using 1
    ext n
    exact lowerProductB_recip_mul_self_eq_one n
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this

#print axioms norm_normalized_error_eq
#print axioms normalized_tracking_error_le
#print axioms tendstoUniformlyOn_normalized_tracking_of_relative_rates
#print axioms tendstoUniformlyOn_normalized_tracking_of_two_sided_b
#print axioms relative_normalized_rate_exponent_neg_iff
#print axioms safe_margin_does_not_imply_relative_rate_margin
#print axioms detector_decay_does_not_imply_relative_decay

end Q3.RouteB
