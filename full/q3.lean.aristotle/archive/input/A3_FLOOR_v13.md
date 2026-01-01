# A3_FLOOR v13: Prove deriv_digamma_eq_trigamma (remove axiom)

## Goal
Prove the lemma

```lean
theorem deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z := by
  -- no sorry
```

This removes the last axiom used in `A3_FLOOR_v11_fixed.lean`.

---

## Setup (Lean)

```lean
import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set

set_option maxHeartbeats 0
set_option maxRecDepth 4000

noncomputable section

-- Definitions used across A3_FLOOR

def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2

-- Digamma partial sums (from v8)
noncomputable def digammaSeq (z : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + k)

lemma digammaSeq_deriv (z : ℂ) (n : ℕ) (hz : ∀ k ≤ n, z ≠ -k) :
    deriv (fun z => digammaSeq z n) z = ∑ k ∈ Finset.range (n + 1), 1 / (z + k)^2 := by
  unfold digammaSeq
  convert HasDerivAt.deriv (HasDerivAt.const_sub _ <| HasDerivAt.sum fun i hi => ?_) using 1
  congr!
  any_goals exact Finset.range (n + 1)
  rotate_left; rotate_left
  use fun i => fun x => 1 / (x + i)
  use fun i => -1 / (z + i) ^ 2
  · simpa [div_eq_mul_inv] using HasDerivAt.inv
      (HasDerivAt.add (hasDerivAt_id z) (hasDerivAt_const _ _))
      (show (z + i : ℂ) ≠ 0 from by
        exact fun h => hz i (Finset.mem_range_succ_iff.mp hi) <| by
          linear_combination' h)
  · norm_num
  · norm_num [neg_div]

lemma deriv_digammaSeq_tendsto_trigamma (z : ℂ) (hz : 0 < z.re) :
    Filter.Tendsto (fun n => deriv (fun z => digammaSeq z n) z) Filter.atTop (nhds (trigamma z)) := by
  -- From v8: partial sums of trigamma converge.
  have h_partial_sums : Filter.Tendsto (fun n : ℕ => ∑ k ∈ Finset.range (n + 1), (1 / (z + k)^2)) Filter.atTop (nhds (∑' k : ℕ, (1 / (z + k)^2))) := by
    refine' (Summable.hasSum _ |> HasSum.tendsto_sum_nat |> Filter.Tendsto.comp <| Filter.tendsto_add_atTop_nat 1)
    have h_abs_conv : Summable (fun k : ℕ => ‖(1 / (z + k)^2 : ℂ)‖) := by
      have h_bound : ∀ k : ℕ, k ≥ 1 → ‖(1 / (z + k)^2 : ℂ)‖ ≤ 1 / (k : ℝ)^2 := by
        norm_num [Complex.normSq, Complex.norm_def]
        exact fun k hk => inv_anti₀ (by positivity) (by
          rw [Real.sq_sqrt (by nlinarith)]
          nlinarith [show (k : ℝ) ≥ 1 by exact_mod_cast hk])
      rw [← summable_nat_add_iff 1]
      exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => h_bound _ le_add_self)
        (by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_pow.2 one_lt_two)
    exact h_abs_conv.of_norm
  convert h_partial_sums using 2
  convert digammaSeq_deriv z ‹_› _ using 1
  exact fun k hk => ne_of_apply_ne Complex.re <| by norm_num; linarith
```

---

## Targets

### Target 1: digammaSeq_tendsto_digamma
Prove that the digamma partial sums converge to digamma for Re z > 0.
You may use `Complex.GammaSeq` and `Complex.GammaSeq_tendsto_Gamma` from Mathlib.

```lean
lemma digammaSeq_tendsto_digamma (z : ℂ) (hz : 0 < z.re) :
    Filter.Tendsto (fun n => digammaSeq z n) Filter.atTop (nhds (digamma z)) := by
  -- expected: use GammaSeq and log-derivative identity
  -- no sorry
  sorry
```

### Target 2: deriv_digamma_eq_trigamma
Use locally uniform convergence (or another method) to pass derivatives to the limit.

```lean
theorem deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z := by
  -- Outline:
  -- 1) digammaSeq_tendsto_digamma
  -- 2) deriv_digammaSeq_tendsto_trigamma
  -- 3) apply TendstoLocallyUniformlyOn.deriv or another lemma to commute deriv + limit
  -- no sorry
  sorry
```

---

## Notes / Hints

- See `Mathlib/Analysis/Complex/LocallyUniformLimit.lean` for:
  `TendstoLocallyUniformlyOn.deriv` and `hasSum_deriv_of_summable_norm`.
- If easier: first show locally uniform convergence of `digammaSeq` on compacta of `{z | 0 < z.re}`.
- Keep scope minimal and avoid heavy Gamma product expansions.

