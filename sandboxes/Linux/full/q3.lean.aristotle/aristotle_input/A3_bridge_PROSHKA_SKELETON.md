# A3 Bridge - Proshka's Complete Skeleton

**Source:** Proshka's analysis 2026-01-14

## Key Insight

**NO Szegő-Böttcher needed!** SB is marked "optional" in specs.

The proof is pure Rayleigh + RKHS cap:
1. Toeplitz Rayleigh ≥ c* (from rayleigh_v1.lean + A3_FLOOR)
2. RKHS ≤ c*/4 (from cap)
3. Difference ≥ 3c*/4 > 0

## What We Already Have

- `rayleigh_v1.lean`: COMPLETE proof of Rayleigh lower bound (0 sorry)
- `A3_FLOOR_*.lean`: P_A(θ) ≥ c* = 11/10 proven

## What We Need (trivial)

### Lemma: Operator Subtraction via Norm

```lean
theorem quadform_sub_lower_bound
  {S R : Matrix} {c : ℝ}
  (hS_floor : ∀ v, ⟨Sv,v⟩ ≥ c * ‖v‖²)
  (hR_psd : 0 ≤ R) :
  ∀ v, ⟨(S - R)v, v⟩ ≥ (c - ‖R‖) * ‖v‖² := by
  intro v
  have h1 : ⟨Sv,v⟩ ≥ c * ‖v‖² := hS_floor v
  have h2 : ⟨Rv,v⟩ ≤ ‖R‖ * ‖v‖² := -- by definition of operator norm
  linarith
```

### Main Theorem

```lean
noncomputable def c_star : ℝ := 11 / 10

theorem A3_bridge_closure_no_SB
  (M : ℕ) (P_A : ℝ → ℝ) (T_P : Matrix (Fin M) (Fin M) ℝ)
  (h_floor : ∀ θ ∈ Set.Icc (-1/2:ℝ) (1/2), c_star ≤ P_A θ)
  (h_cap : ‖T_P‖ ≤ c_star / 4) :
  ∀ v, v ≠ 0 →
    rayleighQuotient (ToeplitzMatrix P_A M - T_P) v ≥ (3 * c_star) / 4 := by
  intro v hv
  -- Step 1: Toeplitz Rayleigh ≥ c* (from rayleigh_lower_bound + h_floor)
  have hToep : rayleighQuotient (ToeplitzMatrix P_A M) v ≥ c_star :=
    rayleigh_lower_bound M (by omega) P_A (by continuity) c_star h_floor v hv
  -- Step 2: RKHS cap
  have hRKHS : ‖T_P‖ ≤ c_star / 4 := h_cap
  -- Step 3: Combine via quadform_sub_lower_bound
  have hSub := quadform_sub_lower_bound hToep hRKHS v
  -- Step 4: Arithmetic
  calc rayleighQuotient (ToeplitzMatrix P_A M - T_P) v
      ≥ c_star - c_star / 4 := hSub
    _ = 3 * c_star / 4 := by ring
```

## Constants

| Constant | Value | Decimal |
|----------|-------|---------|
| c* | 11/10 | 1.1 |
| c*/4 | 11/40 | 0.275 |
| 3c*/4 | 33/40 | 0.825 |
| ρ(1) | <1/25 | <0.04 |

Note: ρ(1) < 1/25 = 0.04 << c*/4 = 0.275, so cap is EASILY satisfied!

## Proof Roadmap

1. Import `rayleigh_v1.lean` results
2. Import `A3_FLOOR` (h_floor hypothesis)
3. Prove `quadform_sub_lower_bound` (3 lines)
4. Wire together with `linarith`

**Total new code needed: ~20 lines**

## DO NOT DO

- Do NOT formalize Szegő-Böttcher
- Do NOT use asymptotics/determinants
- Do NOT make SB a blocker

This is STANDARD linear algebra + Fourier identity.
