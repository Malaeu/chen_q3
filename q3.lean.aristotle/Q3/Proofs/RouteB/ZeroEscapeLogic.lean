import Mathlib

set_option linter.mathlibStandardSet false

open Filter Set
open scoped Topology

noncomputable section

namespace Q3.RouteB

/-- Every zero of `f` in `S` is real. -/
def ZerosRealOn (S : Set ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ S, f z = 0 → z.im = 0

/-- Each zero of the limit in `S` is approached by zeros of the approximants.
The finite initial segment is deliberately ignored. -/
def ZerosApproachOn
    (S : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ) : Prop :=
  ∀ z ∈ S, f z = 0 →
    ∃ w : ℕ → ℂ,
      Tendsto w atTop (𝓝 z) ∧
      ∀ᶠ n in atTop, F n (w n) = 0

/-- The logical core of ZeroEscape: a limit zero approached by real zeros is
real.  The analytic Rouché/Hurwitz theorem is isolated in `ZerosApproachOn`;
it is not assumed to have been proved by this lemma. -/
theorem zerosRealOn_of_zerosApproachOn
    (S : Set ℂ) (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (hF : ∀ n, ZerosRealOn Set.univ (F n))
    (htransfer : ZerosApproachOn S F f) :
    ZerosRealOn S f := by
  intro z hzS hzf
  obtain ⟨w, hw, hwzero⟩ := htransfer z hzS hzf
  have hwim : ∀ᶠ n in atTop, (w n).im = 0 := by
    filter_upwards [hwzero] with n hn
    exact hF n (w n) (Set.mem_univ _) hn
  have him_to_z : Tendsto (fun n => (w n).im) atTop (𝓝 z.im) :=
    Complex.continuous_im.continuousAt.tendsto.comp hw
  have hwim_eq :
      (fun n => (w n).im) =ᶠ[atTop] (fun _ : ℕ => (0 : ℝ)) := hwim
  have him_to_zero : Tendsto (fun n => (w n).im) atTop (𝓝 0) :=
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
      hwim_eq.symm
  exact tendsto_nhds_unique him_to_z him_to_zero

/-- The scalar estimate in H3 plus H4 decay gives an error tending to zero.
This is the order-theoretic local-uniform-convergence core, independent of the
still-open object and compact-uniformity crosswalks. -/
theorem tendsto_zero_of_detector_bound
    (A : ℝ) (d W eps : ℕ → ℝ)
    (hd : ∀ n, 0 ≤ d n)
    (hbound : ∀ n, d n ≤ A * W n + eps n)
    (hW : Tendsto W atTop (𝓝 0))
    (heps : Tendsto eps atTop (𝓝 0)) :
    Tendsto d atTop (𝓝 0) := by
  have hright : Tendsto (fun n => A * W n + eps n) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hW).add heps
  exact squeeze_zero hd hbound hright

#print axioms zerosRealOn_of_zerosApproachOn
#print axioms tendsto_zero_of_detector_bound

end Q3.RouteB
