# A3_FLOOR v17: digammaSeq local uniform limit + deriv_digamma_eq_trigamma

## Goal
Prove local uniform convergence of `digammaSeq` to `digamma`, then use it to prove
`deriv_digamma_eq_trigamma` on `Re z > 0`.

## Context Files (available in repo)
- `full/q3.lean.aristotle/aristotle_output/d1524982_aristotle.lean`
  (GammaSeq local uniform convergence + deriv_GammaSeq_tendstoLocallyUniformlyOn
   + deriv_digammaSeq_tendsto_trigamma)
- `full/q3.lean.aristotle/aristotle_output/383828ff_aristotle.lean`
  (digammaSeq_eq_logDeriv_GammaSeq)
- `full/q3.lean.aristotle/A3_FLOOR_v8_monotonicity.lean`
  (definitions + deriv_digammaSeq_tendsto_trigamma)

## Definitions (from v8/v13)
```lean
noncomputable def digamma (z : ℂ) : ℂ := (deriv Complex.Gamma z) / (Complex.Gamma z)
noncomputable def trigamma (z : ℂ) : ℂ := ∑' n : ℕ, 1 / (z + n)^2
noncomputable def digammaSeq (z : ℂ) (n : ℕ) : ℂ := (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + k)
```

## Lemma already proven (v15)
```lean
lemma digammaSeq_eq_logDeriv_GammaSeq {z : ℂ} {n : ℕ}
    (hn : n ≠ 0) (hz : ∀ k ≤ n, z ≠ -k) :
    digammaSeq z n = logDeriv (fun w => Complex.GammaSeq w n) z
```

## Known convergence lemmas (v13)
```lean
lemma GammaSeq_tendstoLocallyUniformlyOn_v9 (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re}) (hS_open : IsOpen S) :
    TendstoLocallyUniformlyOn (fun n z => Complex.GammaSeq z n) Complex.Gamma Filter.atTop S

lemma deriv_GammaSeq_tendstoLocallyUniformlyOn (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re}) (hS_open : IsOpen S) :
    TendstoLocallyUniformlyOn (fun n z => deriv (fun w => Complex.GammaSeq w n) z)
      (deriv Complex.Gamma) Filter.atTop S

lemma deriv_digammaSeq_tendsto_trigamma (z : ℂ) (hz : 0 < z.re) :
    Filter.Tendsto (fun n => deriv (fun z => digammaSeq z n) z) Filter.atTop (nhds (trigamma z))
```

## Target 1: local uniform convergence of digammaSeq
```lean
lemma digammaSeq_tendstoLocallyUniformlyOn (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re}) (hS_open : IsOpen S) :
    TendstoLocallyUniformlyOn (fun n z => digammaSeq z n) digamma Filter.atTop S := by
  -- Hint: use logDeriv_tendsto + digammaSeq_eq_logDeriv_GammaSeq
  -- and GammaSeq_tendstoLocallyUniformlyOn_v9, Gamma_ne_zero_of_re_pos
```

## Target 2: deriv_digamma_eq_trigamma
```lean
theorem deriv_digamma_eq_trigamma {z : ℂ} (hz : 0 < z.re) :
    deriv digamma z = trigamma z := by
  -- Use: digammaSeq_tendstoLocallyUniformlyOn + TendstoLocallyUniformlyOn.deriv
  -- then compare with deriv_digammaSeq_tendsto_trigamma
```

## Hints
- Use `Complex.logDeriv_tendsto` from `Mathlib.Analysis.Complex.LocallyUniformLimit`.
- For `Gamma` nonzero on `Re z > 0`, use `Complex.Gamma_ne_zero_of_re_pos`.
- Pointwise convergence via logDeriv, then upgrade to locally uniform if possible,
  or directly use `TendstoLocallyUniformlyOn.deriv` from the locally uniform convergence of
  `digammaSeq` on open sets.

## Request Automated Lemmas
If needed, generate helper lemmas:
1. `digammaSeq_eq_logDeriv_GammaSeq`-style rewrite on a compact set.
2. A lemma turning `logDeriv_tendsto` into `TendstoUniformlyOn` on compact subsets.
