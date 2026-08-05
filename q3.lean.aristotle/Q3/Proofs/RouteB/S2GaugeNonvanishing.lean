import Q3.Proofs.RouteB.CenteredXiZeroNonzero

set_option linter.mathlibStandardSet false

open Complex Filter Topology

noncomputable section

namespace Q3.RouteB

/-!
# S2 gauge: the zero-free multiplier relating `riemannZeta` and `riemannXi`

`SlotS2` (see `CanonicalRHRouteSkeleton.lean`) asks for a multiplier `gamma` that is
**nonvanishing on the open centered strip**, with `D.limit = c * centeredXi * gamma`.
The Müntz branch produces `riemannZeta * Mellin h`, while the roof consumes `centeredXi`.
The classical completion supplies the bridge, and this file pins it:

* `xiGauge s = (1/2) * s * (s - 1) * Gammaℝ s`, where `Gammaℝ s = π ^ (-s/2) * Γ (s/2)`;
* `riemannXi s = xiGauge s * riemannZeta s` on the open strip;
* `xiGauge` has no zeros there, and neither does its centered form.

Address: `G6 · SlotS2 · S2-L2` (gauge) and `S2-L4'` (anchored limit).
Route B remains `CHALLENGER / NOT_RH`; nothing here promotes a route or claims RH.
-/

/-- The gauge relating `riemannZeta` to `riemannXi`: the archimedean factor
`Gammaℝ` together with the pole-clearing polynomial `s(s-1)/2`. -/
def xiGauge (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * s * (s - 1) * Gammaℝ s

/-- On the open critical strip the gauge is zero-free.  The strip must be **open**:
`s * (s - 1)` vanishes exactly at the two boundary points `s = 0` and `s = 1`. -/
theorem xiGauge_ne_zero_of_mem_strip {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    xiGauge s ≠ 0 := by
  have hs_ne_zero : s ≠ 0 := by
    intro h; subst s; norm_num at hs0
  have hs_ne_one : s - 1 ≠ 0 := by
    refine sub_ne_zero.mpr ?_
    intro h; subst s; norm_num at hs1
  have hGamma : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos hs0
  unfold xiGauge
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs_ne_zero) hs_ne_one) hGamma

/-- The gauge does what its name says: it turns `riemannZeta` into `riemannXi`
on the open critical strip. -/
theorem riemannXi_eq_xiGauge_mul_riemannZeta
    {s : ℂ} (hs0 : 0 < s.re) (hs1 : s.re < 1) :
    riemannXi s = xiGauge s * riemannZeta s := by
  have hs_ne_zero : s ≠ 0 := by
    intro h; subst s; norm_num at hs0
  have hs_ne_one : s ≠ 1 := by
    intro h; subst s; norm_num at hs1
  rw [riemannXi_eq_completedRiemannZeta hs_ne_zero hs_ne_one,
    completedRiemannZeta_eq_Gamma_mul_riemannZeta hs0, xiGauge]
  ring

/-- The gauge in the centered coordinate `s = 1/2 + I * z` used by Route B. -/
def centeredGauge (z : ℂ) : ℂ :=
  xiGauge ((1 / 2 : ℂ) + Complex.I * z)

/-- Membership in the centered strip gives the two strict bounds on `Re s`. -/
theorem re_bounds_of_mem_centeredCriticalStrip {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    0 < ((1 / 2 : ℂ) + Complex.I * z).re ∧ ((1 / 2 : ℂ) + Complex.I * z).re < 1 := by
  have hz' : |z.im| < 1 / 2 := hz
  rw [centered_argument_re]
  constructor <;> cases' abs_lt.mp hz' with hlo hhi <;> linarith

/-- The centered gauge is zero-free on the open centered strip: exactly the
nonvanishing demanded by `SlotS2`. -/
theorem centeredGauge_ne_zero_of_mem_strip {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    centeredGauge z ≠ 0 := by
  obtain ⟨h0, h1⟩ := re_bounds_of_mem_centeredCriticalStrip hz
  exact xiGauge_ne_zero_of_mem_strip h0 h1

/-- The centered identity `centeredXi = centeredGauge * riemannZeta ∘ (1/2 + I z)`. -/
theorem centeredXi_eq_centeredGauge_mul_riemannZeta
    {z : ℂ} (hz : z ∈ centeredCriticalStrip) :
    centeredXi z = centeredGauge z * riemannZeta ((1 / 2 : ℂ) + Complex.I * z) := by
  obtain ⟨h0, h1⟩ := re_bounds_of_mem_centeredCriticalStrip hz
  exact riemannXi_eq_xiGauge_mul_riemannZeta h0 h1

/-!
## S2-L4' — an anchored locally uniform limit keeps the anchor value

Generic, with no Route-B structure in the statement, so it cannot drift with the project.
Applied at `z = 0` with `F = selectedFamily C`, `S = centeredCriticalStrip` and
`a = centeredXi 0`, it turns `SlotAnchor` plus `centeredXi_zero_ne_zero` into `D.limit 0 ≠ 0`,
which is the nonzero constant `c` required by `SlotS2`.
-/

theorem limit_eq_anchor {F : ℕ → ℂ → ℂ} {L : ℂ → ℂ} {S : Set ℂ} {z a : ℂ}
    (hconv : TendstoLocallyUniformlyOn F L atTop S) (hz : z ∈ S)
    (hanchor : ∀ k, F k z = a) : L z = a := by
  have h1 : Tendsto (fun k => F k z) atTop (𝓝 (L z)) := hconv.tendsto_at hz
  simp only [hanchor] at h1
  exact (tendsto_nhds_unique tendsto_const_nhds h1).symm

/-- Consumer form: an anchored locally uniform limit on the centered strip is
nonzero at the anchor, because `centeredXi 0 ≠ 0` is proved. -/
theorem limit_at_zero_ne_zero {F : ℕ → ℂ → ℂ} {L : ℂ → ℂ}
    (hconv : TendstoLocallyUniformlyOn F L atTop centeredCriticalStrip)
    (hanchor : ∀ k, F k 0 = centeredXi 0) : L 0 ≠ 0 := by
  have hmem : (0 : ℂ) ∈ centeredCriticalStrip := by
    show |(0 : ℂ).im| < 1 / 2
    norm_num
  rw [limit_eq_anchor hconv hmem hanchor]
  exact centeredXi_zero_ne_zero

end Q3.RouteB
