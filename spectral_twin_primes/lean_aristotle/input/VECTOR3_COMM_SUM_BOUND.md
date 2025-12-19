# Vector 3 Task #2: Commutator Sum Bound

## Context

This is the **second building block** for the Spectral/Q3 attack on Twin Primes.
After proving `rankOne_comm_bound` (Task #1), we need linearity + triangle inequality.

**Goal:** Show that ‖[Σ Aᵢ, U]‖ ≤ Σ ‖[Aᵢ, U]‖

This combines with Task #1 to give:
```
‖[T_P, U]‖ = ‖[Σ wₙ·rankOne(vₙ), U]‖
           ≤ Σ wₙ · ‖[rankOne(vₙ), U]‖
           ≤ Σ wₙ · 2·‖Uvₙ - vₙ‖·‖vₙ‖
```

## Mathematical Setup

**Hilbert space:** H — complex inner product space with norm ‖·‖

**Operators:**
- `A, U : H →L[ℂ] H` — bounded linear operators
- `comm A U := A ∘ U - U ∘ A` — commutator

## Theorems to Prove

### Lemma 1: comm_add
Commutator is additive in first argument:
```
[A₁ + A₂, U] = [A₁, U] + [A₂, U]
```

### Lemma 2: comm_sum
Commutator distributes over finite sums:
```
[Σᵢ Aᵢ, U] = Σᵢ [Aᵢ, U]
```

### Lemma 3: opNorm_sum_le
Triangle inequality for operator norms:
```
‖Σᵢ Tᵢ‖ ≤ Σᵢ ‖Tᵢ‖
```

### Theorem: comm_sum_bound (MAIN GOAL)
Combining the above:
```
‖[Σᵢ Aᵢ, U]‖ ≤ Σᵢ ‖[Aᵢ, U]‖
```

## Lean 4 Formalization

```lean
import Mathlib

open scoped ComplexConjugate
open Complex

namespace Vector3Task2

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {ι : Type} [DecidableEq ι]

/-- Commutator of bounded operators -/
def comm (A U : H →L[ℂ] H) : H →L[ℂ] H :=
  A.comp U - U.comp A

/-- Commutator is additive in first argument -/
lemma comm_add (A₁ A₂ U : H →L[ℂ] H) :
    comm (A₁ + A₂) U = comm A₁ U + comm A₂ U := by
  simp only [comm]
  ext x
  simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
             ContinuousLinearMap.add_apply]
  ring

/-- Commutator distributes over finite sums -/
lemma comm_sum (U : H →L[ℂ] H) (s : Finset ι) (Ai : ι → (H →L[ℂ] H)) :
    comm (∑ i in s, Ai i) U = ∑ i in s, comm (Ai i) U := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, comm]
    ext x
    simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, comm_add, ih, Finset.sum_insert ha]

/-- Triangle inequality for operator norms of finite sums -/
lemma opNorm_sum_le (s : Finset ι) (Ti : ι → (H →L[ℂ] H)) :
    ‖∑ i in s, Ti i‖ ≤ ∑ i in s, ‖Ti i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    calc ‖Ti a + ∑ i in s, Ti i‖
        ≤ ‖Ti a‖ + ‖∑ i in s, Ti i‖ := norm_add_le _ _
      _ ≤ ‖Ti a‖ + ∑ i in s, ‖Ti i‖ := by linarith

/-- MAIN THEOREM: Commutator norm of sum bounded by sum of norms -/
theorem comm_sum_bound (U : H →L[ℂ] H) (s : Finset ι) (Ai : ι → (H →L[ℂ] H)) :
    ‖comm (∑ i in s, Ai i) U‖ ≤ ∑ i in s, ‖comm (Ai i) U‖ := by
  rw [comm_sum U s Ai]
  exact opNorm_sum_le s (fun i => comm (Ai i) U)

end Vector3Task2
```

## Why This Matters

1. **Linearity:** Commutator behaves well under sums
2. **Triangle inequality:** Standard but essential for bounds
3. **Composition:** Directly feeds into Task #3 (T_P bound)

## Next Step (Task #3)

After this, combine with `rankOne_comm_bound`:
```
‖[T_P, U]‖ = ‖[Σ wₙ·rankOne(vₙ), U]‖
           ≤ Σ wₙ · ‖[rankOne(vₙ), U]‖      (this theorem)
           ≤ Σ wₙ · 2·‖Uvₙ - vₙ‖·‖vₙ‖      (Task #1)
           ≤ 2ε · Σ wₙ                       (RKHS stability)
```

## References

- Böttcher-Silbermann: Toeplitz operator theory
- Mathlib: ContinuousLinearMap, Finset.induction_on
- Q3 paper §8-9: RKHS geometry
