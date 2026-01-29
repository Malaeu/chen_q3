# Aristotle request: fix two lemmas in project format

Goal: Provide Lean proofs that compile in our project for the two lemmas below.

Constraints:
- Use only Mathlib/Lean 4; do not introduce new axioms.
- Avoid ambiguous `integral_rpow_mul_exp_neg_rpow` (prefer Real version or a proof that does not rely on it).
- No `sorry` or `exact?`.
- Keep statements exactly as written.

Please output Lean code for these two lemmas:

```lean
import Mathlib
import Mathlib.Topology.UniformSpace.UniformConvergence

open scoped Real
open scoped Pointwise
open scoped BigOperators
open Real Complex MeasureTheory Set

lemma GammaSeq_uniform_bound_integrable (a b : ℝ) (ha : 0 < a) :
    MeasureTheory.IntegrableOn
      (fun x : ℝ => Real.exp (-x) * (if x ≤ 1 then x ^ (a - 1) else x ^ (b - 1)))
      (Set.Ioi 0) := by
  -- proof

lemma TendstoLocallyUniformlyOn_div {ι : Type*} [Preorder ι] {F : ι → ℂ → ℂ}
    {f : ℂ → ℂ} {G : ι → ℂ → ℂ} {g : ℂ → ℂ} {S : Set ℂ}
    (hf : TendstoLocallyUniformlyOn F f Filter.atTop S)
    (hg : TendstoLocallyUniformlyOn G g Filter.atTop S)
    (hf_cont : ContinuousOn f S)
    (hg_cont : ContinuousOn g S)
    (hg_ne_zero : ∀ z ∈ S, g z ≠ 0) :
    TendstoLocallyUniformlyOn (fun i z => F i z / G i z) (fun z => f z / g z)
      Filter.atTop S := by
  -- proof
```

Notes:
- The proofs can follow the standard route: local uniform convergence + continuity + lower bound on `g` on a neighborhood.
- Use `Metric.tendstoLocallyUniformlyOn_iff` if convenient.
