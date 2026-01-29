# Q_Lipschitz_on_W_K (clean bridge v2)

## Goal
Prove the following Lean statement (no `sorry`/`exact?`).

```lean
import Q3.Basic.Defs
import Q3.Clean.AxiomsTier1

open scoped BigOperators Real Classical Pointwise
open MeasureTheory

noncomputable section

namespace Q3.Proofs.QLipschitzBridgeV2

/-- Sup of a_star on [-K, K]. -/
def M_a (K : ℝ) : ℝ := sSup (Q3.a_star '' Set.Icc (-K) K)

/-- Lipschitz constant for Q on W_K. -/
def L_Q (K : ℝ) : ℝ := 2 * K * M_a K + Q3.W_sum K

/-- Sup norm of difference on [-K, K]. -/
def sup_norm_diff (K : ℝ) (Φ Ψ : ℝ → ℝ) : ℝ :=
  sSup (Set.image (fun x => |Φ x - Ψ x|) (Set.Icc (-K) K))

/-- Main goal. -/
theorem Q_Lipschitz_on_W_K (K : ℝ) (hK : K > 0) :
    ∀ Φ Ψ : ℝ → ℝ, Φ ∈ Q3.W_K K → Ψ ∈ Q3.W_K K →
      |Q3.Q Φ - Q3.Q Ψ| ≤ L_Q K * sup_norm_diff K Φ Ψ := by
  -- fill proof

end Q3.Proofs.QLipschitzBridgeV2
```

## Available lemmas/axioms (use these explicitly)
- `Q3.Clean.a_star_pos`, `Q3.Clean.a_star_continuous`,
  `Q3.Clean.a_star_bdd_on_compact`
- `Q3.w_Q_nonneg` and basic tsum lemmas (`Summable.tsum_sub`, `Summable.tsum_le_tsum`)
- `Set.Ioo_subset_Icc_self`, `ContinuousOn.integrableOn_Icc`,
  `MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero`,
  `MeasureTheory.setIntegral_mono_on`, `norm_integral_le_integral_norm`

## Proof outline (high level)
1. From `W_K`, get `ContinuousOn` on `Icc` and support in `Icc`.
2. Arch term: rewrite to set integral on `Icc`, bound by `M_a * 2K * sup_norm_diff`.
3. Prime term: bound termwise by `W_sum * sup_norm_diff` using finiteness of nodes.
4. Combine by triangle inequality and ring algebra to get `L_Q * sup_norm_diff`.

## Policy
- Use `suffices` where possible to reduce goals.
- Avoid `exact?` and heavy `aesop`.
- Keep the proof explicit and Lean-friendly.
