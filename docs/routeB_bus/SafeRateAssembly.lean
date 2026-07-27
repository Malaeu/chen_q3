import Mathlib

set_option linter.mathlibStandardSet false

open Filter
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- The cofinal-filter version of the Contract-v2 rate core.  Once the exact
spectral inputs produce the displayed squared envelope, strict exponent margin
forces the nonnegative detector to zero.  `[NeBot l]` rules out a vacuous
bottom-filter witness. -/
theorem safe_rate_cofinal_square_core
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale W : ι → ℝ) (C q_b r_alpha r_Delta : ℝ)
    (hscale : Tendsto scale l atTop)
    (hC : 0 ≤ C)
    (hmargin : r_Delta - r_alpha > 2 * q_b + 1)
    (hW0 : ∀ᶠ i in l, 0 ≤ W i)
    (hWsq : ∀ᶠ i in l,
      (W i) ^ 2 ≤
        (C * (scale i) ^
          (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2) :
    Tendsto W l (𝓝 0) := by
  let p : ℝ := q_b + (1 + r_alpha - r_Delta) / 2
  have hp : p < 0 := by
    dsimp [p]
    linarith
  have hpow : Tendsto (fun i => (scale i) ^ p) l (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (neg_pos.mpr hp)).comp hscale
    convert h using 1
    ext i
    congr 1
    linarith
  have hupper : Tendsto (fun i => C * (scale i) ^ p) l (𝓝 0) := by
    simpa using tendsto_const_nhds.mul hpow
  have hscale_pos : ∀ᶠ i in l, 0 < scale i := by
    filter_upwards [(tendsto_atTop.1 hscale) 1] with i hi
    linarith
  have hbound : ∀ᶠ i in l, W i ≤ C * (scale i) ^ p := by
    filter_upwards [hW0, hWsq, hscale_pos] with i hWi hsq hsi
    have huppi : 0 ≤ C * (scale i) ^ p :=
      mul_nonneg hC (Real.rpow_nonneg hsi.le p)
    exact (sq_le_sq₀ hWi huppi).mp hsq
  exact squeeze_zero' hW0 hbound hupper

/-- The complete generic rate package: the strict Contract-v2 margin both
makes the exponent negative and, through the cofinal squared envelope, forces
the detector to zero.  Exact Route-B constants are intentionally hypotheses. -/
theorem safe_rate_generic_package
    {ι : Type*} {l : Filter ι} [NeBot l]
    (scale W : ι → ℝ) (C q_b r_alpha r_Delta : ℝ)
    (hscale : Tendsto scale l atTop)
    (hC : 0 ≤ C)
    (hmargin : r_Delta - r_alpha > 2 * q_b + 1)
    (hW0 : ∀ᶠ i in l, 0 ≤ W i)
    (hWsq : ∀ᶠ i in l,
      (W i) ^ 2 ≤
        (C * (scale i) ^
          (q_b + (1 + r_alpha - r_Delta) / 2)) ^ 2) :
    q_b + (1 + r_alpha - r_Delta) / 2 < 0 ∧
      Tendsto W l (𝓝 0) := by
  constructor
  · linarith
  · exact safe_rate_cofinal_square_core scale W C q_b r_alpha r_Delta
      hscale hC hmargin hW0 hWsq

#print axioms safe_rate_cofinal_square_core
#print axioms safe_rate_generic_package

end Q3.RouteB
