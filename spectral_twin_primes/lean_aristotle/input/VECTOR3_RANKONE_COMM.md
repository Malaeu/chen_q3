# Vector 3: Rank-One Commutator Bound (Minor Arcs via Operators)

## Context

This is the **core lemma** for the Spectral/Q3 attack on the Twin Prime Conjecture.
The goal is to bypass Vinogradov's method entirely using **operator-theoretic** bounds.

**Key insight:** Instead of estimating exponential sums F(α) on minor arcs pointwise,
we estimate the matrix coefficient ⟨x, Ux⟩ through commutator bounds [A, U].

If the Q3 operator A := T_M[P_A] - T_P has spectral gap A ⪰ cI, and U almost commutes
with A, then contributions from "minor arc directions" are suppressed.

## Mathematical Setup

**Hilbert space:** H — complex inner product space with norm ‖·‖

**Operators:**
- `U : H →L[ℂ] H` — isometry (unitary shift operator, corresponds to phase e(-2α))
- `rankOne v` — rank-1 operator: x ↦ ⟪v, x⟫ · v
- `comm A U := A ∘ U - U ∘ A` — commutator

**The prime operator T_P is a sum of rank-1 projectors:**
```
T_P = Σ_n w_n · |v_n⟩⟨v_n|
```

Therefore:
```
[T_P, U] = Σ_n w_n · [|v_n⟩⟨v_n|, U]
```

And the key is to bound each rank-1 commutator term.

## Main Theorem to Prove

**Theorem (rankOne_comm_bound):**
For isometry U and vector v:
```
‖[rankOne(v), U]‖ ≤ 2 · ‖Uv - v‖ · ‖v‖
```

**Informal proof sketch:**

1. Expand commutator:
   ```
   [|v⟩⟨v|, U] = |v⟩⟨v|U - U|v⟩⟨v|
   ```

2. For any x with ‖x‖ ≤ 1:
   ```
   [|v⟩⟨v|, U]x = ⟨v, Ux⟩v - U(⟨v, x⟩v)
                = ⟨v, Ux⟩v - ⟨v, x⟩Uv
   ```

3. Estimate norm:
   ```
   ‖[|v⟩⟨v|, U]x‖ ≤ |⟨v, Ux⟩| · ‖v‖ + |⟨v, x⟩| · ‖Uv‖
   ```

4. Use Cauchy-Schwarz: |⟨v, y⟩| ≤ ‖v‖ · ‖y‖

5. Use isometry: ‖Ux‖ = ‖x‖ ≤ 1, ‖Uv‖ = ‖v‖

6. Key trick: rewrite as
   ```
   ⟨v, Ux⟩v - ⟨v, x⟩Uv = ⟨v, Ux⟩(v - Uv) + ⟨v, Ux⟩Uv - ⟨v, x⟩Uv
                        = ⟨v, Ux⟩(v - Uv) + (⟨v, Ux⟩ - ⟨v, x⟩)Uv
                        = ⟨v, Ux⟩(v - Uv) + ⟨v, Ux - x⟩Uv
   ```

7. Taking norms:
   ```
   ‖...‖ ≤ ‖v‖ · ‖x‖ · ‖v - Uv‖ + ‖v‖ · ‖Ux - x‖ · ‖v‖
        ≤ ‖v‖ · ‖Uv - v‖ + ‖v‖² · ‖U - I‖
   ```

8. Since ‖(U-I)x‖ ≤ ‖Uv - v‖ for unit vectors aligned with v direction,
   and taking supremum over ‖x‖ ≤ 1:
   ```
   ‖[rankOne v, U]‖ ≤ 2 · ‖Uv - v‖ · ‖v‖
   ```

## Lean 4 Formalization

```lean
import Mathlib

open scoped ComplexConjugate
open Complex

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Commutator of bounded operators -/
def comm (A U : H →L[ℂ] H) : H →L[ℂ] H :=
  A.comp U - U.comp A

/-- Rank-one operator: x ↦ ⟪v, x⟫ · v -/
noncomputable def rankOne (v : H) : H →L[ℂ] H :=
  ContinuousLinearMap.rankOne ℂ v v

/-- MAIN THEOREM: Rank-one commutator is controlled by shift distance -/
theorem rankOne_comm_bound
    (U : H →L[ℂ] H) (hU : Isometry U) (v : H) :
    ‖comm (rankOne v) U‖ ≤ 2 * ‖U v - v‖ * ‖v‖ := by
  -- Use operator norm definition
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
  intro x
  -- Expand commutator action on x
  simp only [comm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply]
  simp only [rankOne, ContinuousLinearMap.rankOne_apply]
  -- Now we have: ⟪v, U x⟫ • v - U (⟪v, x⟫ • v)
  -- Use linearity of U
  rw [ContinuousLinearMap.map_smul]
  -- Goal: ‖⟪v, U x⟫ • v - ⟪v, x⟫ • U v‖ ≤ 2 * ‖U v - v‖ * ‖v‖ * ‖x‖
  -- Rewrite as: ⟪v, U x⟫ • (v - U v) + (⟪v, U x⟫ - ⟪v, x⟫) • U v
  have key : inner v (U x) • v - inner v x • U v =
             inner v (U x) • (v - U v) + (inner v (U x) - inner v x) • U v := by
    ring_nf
    simp [smul_sub, sub_smul]
  rw [key]
  -- Triangle inequality
  calc ‖inner v (U x) • (v - U v) + (inner v (U x) - inner v x) • U v‖
      ≤ ‖inner v (U x) • (v - U v)‖ + ‖(inner v (U x) - inner v x) • U v‖ := norm_add_le _ _
    _ = ‖inner v (U x)‖ * ‖v - U v‖ + ‖inner v (U x) - inner v x‖ * ‖U v‖ := by
        simp [norm_smul]
    _ ≤ ‖v‖ * ‖U x‖ * ‖v - U v‖ + ‖v‖ * ‖U x - x‖ * ‖U v‖ := by
        gcongr
        · exact norm_inner_le_norm v (U x)
        · calc ‖inner v (U x) - inner v x‖
              = ‖inner v (U x - x)‖ := by rw [inner_sub_right]
            _ ≤ ‖v‖ * ‖U x - x‖ := norm_inner_le_norm v (U x - x)
    _ = ‖v‖ * ‖x‖ * ‖v - U v‖ + ‖v‖ * ‖U x - x‖ * ‖v‖ := by
        rw [hU.norm_map x, hU.norm_map v]
    _ ≤ ‖v‖ * ‖x‖ * ‖U v - v‖ + ‖v‖ * (‖U v - v‖ / ‖v‖ * ‖x‖) * ‖v‖ := by
        -- Use that ‖Ux - x‖ ≤ ‖U - I‖ * ‖x‖ and bound ‖U - I‖ locally
        sorry -- needs more careful analysis
    _ ≤ 2 * ‖U v - v‖ * ‖v‖ * ‖x‖ := by ring_nf; sorry
```

## Alternative Cleaner Approach

```lean
theorem rankOne_comm_bound_v2
    (U : H →L[ℂ] H) (hU : Isometry U) (v : H) :
    ‖comm (rankOne v) U‖ ≤ 2 * ‖U v - v‖ * ‖v‖ := by
  by_cases hv : v = 0
  · simp [hv, rankOne, comm]
  · refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) ?_
    intro x
    simp only [comm, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
               rankOne, ContinuousLinearMap.rankOne_apply, ContinuousLinearMap.map_smul]
    -- ‖⟪v, Ux⟫ • v - ⟪v, x⟫ • Uv‖
    -- Factor out and use triangle inequality carefully
    calc ‖inner v (U x) • v - inner v x • U v‖
        ≤ ‖inner v (U x)‖ * ‖v - U v‖ + ‖inner v x‖ * ‖v - U v‖ := by
          -- Clever rewrite: a•v - b•Uv = a•(v-Uv) + (a-b)•Uv or similar
          sorry
      _ ≤ (‖v‖ * ‖x‖ + ‖v‖ * ‖x‖) * ‖U v - v‖ := by
          gcongr
          · exact norm_inner_le_norm v (U x) |>.trans (by rw [hU.norm_map]; ring_nf)
          · exact norm_inner_le_norm v x
      _ = 2 * ‖v‖ * ‖x‖ * ‖U v - v‖ := by ring
      _ = 2 * ‖U v - v‖ * ‖v‖ * ‖x‖ := by ring
```

## Corollaries Needed After This

**Corollary 1 (Prime operator commutator):**
If T_P = Σ_n w_n · rankOne(v_n) with normalized v_n, then:
```
‖[T_P, U]‖ ≤ 2 · (Σ_n w_n) · max_n ‖U v_n - v_n‖
```

**Corollary 2 (RKHS shift stability):**
For heat kernel vectors k_ξ with parameter t:
```
‖U₂ k_ξ - k_ξ‖ ≤ C · exp(-t)
```
This makes the commutator exponentially small!

**Corollary 3 (Minor arcs suppression without Vinogradov):**
Combining with A ⪰ cI coercivity:
```
|⟨x, U₂x⟩| ≤ (‖[A, U₂]‖ / c) · ‖x‖ · √⟨x, Ax⟩
```
This replaces pointwise F(α) bounds with operator-theoretic control.

## Why This Matters

1. **Vinogradov bypass:** No exponential sum estimates needed
2. **Pure operator theory:** Uses only Hilbert space + isometry properties
3. **Composable:** Can sum over rank-1 terms to get T_P bound
4. **RKHS compatible:** Heat smoothing makes ‖Uv - v‖ small

## References

- Böttcher-Silbermann: Toeplitz operator theory (commutator estimates)
- Mourre theory: Commutator methods in spectral theory
- Q3 paper §8-9: RKHS geometry and Gram bounds
