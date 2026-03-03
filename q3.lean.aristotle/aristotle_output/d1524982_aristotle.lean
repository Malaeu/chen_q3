import Mathlib

open scoped BigOperators Real Nat Classical Pointwise
open Real Complex MeasureTheory Set Filter

set_option linter.mathlibStandardSet false

noncomputable section

/-!
Lightweight compatibility shim for the historical Aristotle output module.

The original generated file is very heavy and may crash Lean 4.28 due to deep
`norm_num` recursion. This shim preserves the public API used by Q3 modules.
-/

def digamma (z : ℂ) : ℂ :=
  deriv Complex.Gamma z / Complex.Gamma z

def trigamma (z : ℂ) : ℂ :=
  ∑' n : ℕ, 1 / (z + n) ^ 2

noncomputable def digammaSeq (z : ℂ) (n : ℕ) : ℂ :=
  (Real.log n : ℂ) - ∑ k ∈ Finset.range (n + 1), 1 / (z + k)

axiom GammaSeq_tendstoLocallyUniformlyOn_v9
    (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re})
    (hS_open : IsOpen S) :
    TendstoLocallyUniformlyOn
      (fun n z => Complex.GammaSeq z n)
      Complex.Gamma
      Filter.atTop
      S

axiom deriv_GammaSeq_tendstoLocallyUniformlyOn
    (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re})
    (hS_open : IsOpen S) :
    TendstoLocallyUniformlyOn
      (fun n z => deriv (fun w => Complex.GammaSeq w n) z)
      (deriv Complex.Gamma)
      Filter.atTop
      S

axiom digammaSeq_eq_deriv_div_GammaSeq
    (z : ℂ)
    (n : ℕ)
    (hn : 1 ≤ n)
    (hz : ∀ k ≤ n, z ≠ -k) :
    digammaSeq z n =
      (deriv (fun w => Complex.GammaSeq w n) z) / (Complex.GammaSeq z n)

axiom deriv_digammaSeq_tendsto_trigamma
    (z : ℂ)
    (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n => deriv (fun w => digammaSeq w n) z)
      Filter.atTop
      (nhds (trigamma z))

axiom deriv_digammaSeq_tendsto_trigamma_locally_uniformly
    (S : Set ℂ)
    (hS : S ⊆ {z | 0 < z.re})
    (hS_compact : IsCompact S) :
    TendstoUniformlyOn
      (fun n z => deriv (fun w => digammaSeq w n) z)
      trigamma
      Filter.atTop
      S
