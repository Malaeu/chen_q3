# A3 Archimedean Floor at K=1

## Goal
Prove that with explicit parameter choices B=1/3, r=1/32, t_sym=3/50, the Archimedean floor c_arch(1) > 0.1878.

## Definitions

```lean
-- Parameters for K=1
noncomputable def B_K1 : ℝ := 1/3
noncomputable def r_K1 : ℝ := 1/32
noncomputable def t_sym_K1 : ℝ := 3/50

-- Archimedean density base value
-- a(0) = log(π) - Re(ψ(1/4)) = γ + π/2 + log(π) + 3·log(2) ≥ 5.117
noncomputable def a_zero : ℝ := Real.log Real.pi + Real.eulerMasconst + Real.pi/2 + 3 * Real.log 2

-- Core infimum estimate: m_r ≥ a(0) - 20π·r
noncomputable def m_r_lower (r : ℝ) : ℝ := a_zero - 20 * Real.pi * r

-- Symbol supremum bound: M_B ≤ 11/2
noncomputable def M_B_upper : ℝ := 11/2

-- Lipschitz constant upper bound
noncomputable def L_A_upper (B t : ℝ) : ℝ := M_B_upper / (4 * Real.pi^2 * t) + 10 / (4 * Real.pi^2 * t)^(3/2)

-- Core lower bound formula (from Lemma a3-core-lower-bound)
noncomputable def core_lower (B r t m_r M_B : ℝ) : ℝ :=
  2 * m_r * r * (1 - r/B) * Real.exp(-4 * Real.pi^2 * t * r^2) -
  M_B / (4 * Real.pi^2 * t * r) * Real.exp(-4 * Real.pi^2 * t * r^2)

-- Archimedean floor
noncomputable def c_arch_K1 : ℝ :=
  core_lower B_K1 r_K1 t_sym_K1 (m_r_lower r_K1) M_B_upper - Real.pi * L_A_upper B_K1 t_sym_K1
```

## Main Theorem to Prove

```lean
/-- Archimedean floor at K=1 is positive: c_arch(1) ≥ 1346209/7168000 > 0.1878 -/
theorem a3_k1_floor : c_arch_K1 ≥ 1346209 / 7168000 := by
  sorry

/-- As a corollary, c_arch(1) > 0.1878 -/
theorem a3_k1_floor_decimal : c_arch_K1 > 1878 / 10000 := by
  have h := a3_k1_floor
  calc c_arch_K1 ≥ 1346209 / 7168000 := h
    _ > 1878 / 10000 := by norm_num
```

## Proof Sketch

1. **Substitute explicit parameters**: B = 1/3, r = 1/32, t_sym = 3/50

2. **Use auxiliary bounds**:
   - a(0) ≥ 5.117 (from digamma identity and rational bounds on γ, π, log 2)
   - m_r ≥ a(0) - 20π·r ≥ 5.117 - 20π/32 ≈ 3.15
   - M_B ≤ 11/2 = 5.5 (from digamma bounds on [-1/3, 1/3])

3. **Compute the exponential factor**:
   - exp(-4π²·t_sym·r²) = exp(-4π²·(3/50)·(1/32)²) = exp(-4π²·3/(50·1024))
   - This is close to 1 because the exponent is small (~-0.023)

4. **Evaluate core contribution**:
   - 2·m_r·r·(1 - r/B) = 2·(5.117 - 20π/32)·(1/32)·(1 - 3/32) ≈ 0.18
   - Subtract tail: M_B/(4π²·t_sym·r) ≈ (5.5)/(4π²·3/50·1/32) ≈ 0.007
   - Subtract Lipschitz penalty: π·L_A ≈ small

5. **Combine with rational arithmetic** to get c_arch(1) ≥ 1346209/7168000.

## Notes

- This is a numerical verification lemma - all computations are rational
- Use `norm_num` for rational arithmetic
- The exact fraction 1346209/7168000 comes from the paper
- Euler's constant γ ≥ 577/1000 and log 2 ≥ 17/25 give rational lower bounds
