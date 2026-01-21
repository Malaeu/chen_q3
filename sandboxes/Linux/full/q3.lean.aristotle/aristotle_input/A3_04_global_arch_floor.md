# A3 Global Archimedean Floor

## Goal
Prove that the archimedean margin c_arch(K) has a uniform positive lower bound for all K ≥ 1.

## Definitions

```lean
-- Archimedean symbol margin (definition depends on K)
noncomputable def c_arch (K : ℝ) : ℝ := sorry -- defined via A3 parameter schedule

-- Global floor constant
noncomputable def c_star : ℝ := ⨅ K ∈ Set.Ici (1 : ℝ), c_arch K

-- M(K) = discretization threshold (increases with K)
noncomputable def M_threshold (K : ℝ) : ℕ := sorry

-- Modulus of continuity (non-decreasing in h)
noncomputable def omega_PA (h : ℝ) : ℝ := sorry

-- Szegő-Böttcher gap function
noncomputable def gap (K : ℝ) : ℝ := 4 * omega_PA (Real.pi / M_threshold K)
```

## Main Lemma to Prove

```lean
/-- Global archimedean floor: c_arch(K) ≥ c* > 0 for all K ≥ 1 -/
lemma global_arch_floor (K : ℝ) (hK : K ≥ 1) : c_arch K ≥ c_star := by
  sorry

/-- c* equals c_arch(1) (the infimum is attained at K=1) -/
lemma c_star_eq_c_arch_one : c_star = c_arch 1 := by
  sorry

/-- c* > 0 (from the K=1 floor theorem) -/
lemma c_star_pos : c_star > 0 := by
  sorry

/-- Combined: uniform lower bound -/
theorem a3_global_arch_floor (K : ℝ) (hK : K ≥ 1) : c_arch K ≥ c_arch 1 ∧ c_arch 1 > 0 := by
  sorry
```

## Key Monotonicity Lemma

```lean
/-- c_arch(K) is monotone non-decreasing in K -/
lemma c_arch_mono : Monotone (fun K => if K ≥ 1 then c_arch K else 0) := by
  sorry
```

## Proof Sketch

### Step 1: Monotonicity of c_arch(K)

1. **The gap g(K) = C_SB · ω_{P_A}(π/M(K))** where:
   - C_SB = 4 (Szegő-Böttcher constant)
   - M(K) is the discretization threshold (increases with K)

2. **ω_{P_A}(h) is non-decreasing in h** (modulus of continuity property)

3. **h = π/M(K) decreases as K increases** (because M(K) increases)

4. **Therefore g(K) is non-increasing in K**

5. **c_arch(K) = min_ξ P_A(ξ) - g(K)** is non-decreasing in K
   - The symbol minimum is constant
   - The gap subtracted gets smaller

### Step 2: Infimum at K=1

Since c_arch(K) is monotone non-decreasing for K ≥ 1:
- c* = inf_{K≥1} c_arch(K) = lim_{K→1⁺} c_arch(K) = c_arch(1)

### Step 3: Positivity of c*

From Theorem a3_k1_floor: c_arch(1) ≥ 1346209/7168000 > 0.1878 > 0

Therefore c* = c_arch(1) > 0.

## Notes

- The monotonicity follows from the "direction sanity check" in the paper
- Use `Monotone.iInf_le` for the infimum bound
- The key insight: larger K means larger M(K), smaller h, smaller modulus, smaller gap, larger c_arch
- This prevents the margin from degenerating as K → ∞
