# A3 Cap Combine Lemma

## Goal
Prove that when the RKHS trace-cap bound holds, the Toeplitz operator satisfies both the positivity floor and operator norm bound required by the A3-lock.

## Definitions

```lean
-- Toeplitz operator from symbol P_A
noncomputable def ToeplitzOp (P_A : ℝ → ℝ) : (ℝ → ℝ) →L[ℝ] (ℝ → ℝ) := sorry

-- Operator norm
noncomputable def op_norm (T : (ℝ → ℝ) →L[ℝ] (ℝ → ℝ)) : ℝ := ‖T‖

-- Symbol is Lipschitz
def IsLip (P_A : ℝ → ℝ) : Prop := LipschitzWith 1 P_A

-- Symbol has positive minimum
def HasPosFloor (P_A : ℝ → ℝ) (c₀ : ℝ) : Prop := ∀ θ, P_A θ ≥ c₀

-- Positive semidefinite operator bound
def IsPSD (T : (ℝ → ℝ) →L[ℝ] (ℝ → ℝ)) (c : ℝ) : Prop :=
  ∀ f : ℝ → ℝ, ⟪T f, f⟫ ≥ c * ⟪f, f⟫

-- Trace-cap hypothesis (RKHS bound)
def TraceCap (T : (ℝ → ℝ) →L[ℝ] (ℝ → ℝ)) (ρ : ℝ) : Prop := op_norm T ≤ ρ
```

## Main Lemma to Prove

```lean
/-- Combining trace-cap with symbol floor yields A3-lock prerequisites -/
lemma cap_combine (P_A : ℝ → ℝ) (c₀ ρ : ℝ)
    (hLip : IsLip P_A)
    (hFloor : HasPosFloor P_A c₀)
    (hc₀ : c₀ > 0)
    (hTraceCap : TraceCap (ToeplitzOp P_A) ρ) :
    IsPSD (ToeplitzOp P_A) c₀ ∧ op_norm (ToeplitzOp P_A) ≤ max ρ ‖P_A‖_∞ := by
  sorry

/-- Specialization: When ρ ≤ c₀/4, the A3-lock closes -/
lemma a3_lock_from_cap (P_A : ℝ → ℝ) (c₀ ρ : ℝ)
    (hLip : IsLip P_A)
    (hFloor : HasPosFloor P_A c₀)
    (hc₀ : c₀ > 0)
    (hρ : ρ ≤ c₀ / 4)
    (hTraceCap : TraceCap (ToeplitzOp P_A) ρ) :
    IsPSD (ToeplitzOp P_A) c₀ ∧
    op_norm (ToeplitzOp P_A) ≤ c₀ / 4 + ‖P_A‖_∞ := by
  sorry
```

## Proof Sketch

### For cap_combine:

1. **Positivity (PSD bound)**:
   - For any f with ‖f‖₂ = 1:
   - ⟨T_{P_A} f, f⟩ = ∫_𝕋 P_A(θ) |f(θ)|² dθ
   - Since P_A(θ) ≥ c₀ for all θ: ⟨T_{P_A} f, f⟩ ≥ c₀ · ∫ |f|² = c₀
   - Therefore T_{P_A} ⪰ c₀ · I

2. **Operator norm bound**:
   - From trace-cap: ‖T_{P_A}‖_op ≤ ρ
   - Also: ‖T_{P_A}‖_op ≤ ‖P_A‖_∞ (by Rayleigh quotient)
   - Combined: ‖T_{P_A}‖_op ≤ max(ρ, ‖P_A‖_∞)

### For a3_lock_from_cap:

Apply cap_combine with the stronger hypothesis ρ ≤ c₀/4.

## Dependencies

This lemma combines:
- Lemma a3.two-scale (two-scale selection)
- Lemma a3.lip-floor (Lipschitz symbol with positive floor)
- The trace-cap inequality from RKHS contraction

## Notes

- The key insight: trace-cap gives operator norm, symbol floor gives PSD
- These are the two prerequisites for A3-lock
- The Lipschitz condition ensures controlled behavior under discretization
- Use spectral theory: T_{P_A} ⪰ c₀ I ⟺ λ_min(T_{P_A}) ≥ c₀
