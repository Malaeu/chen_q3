# Aristotle Proof Variant Analysis: weight_sum_bound

## Summary Statistics

| Version | Lines | nlinarith | positivity | aesop | norm_num | have | Recommended |
|---------|-------|-----------|------------|-------|----------|------|-------------|
| **v1_copy1** | **197** | 9 | 25 | **1** | 30 | 35 | ✅ SHORTEST |
| v4_copy4 | 212 | 9 | 23 | 2 | 30 | 28 | ✅ STABLE |
| v6_copy6 | 221 | 11 | 23 | 2 | 34 | 34 | ✅ STABLE |
| v0_original | 222 | 10 | 32 | 11 | 36 | 41 | ❌ too much aesop |
| v2_copy2 | 229 | 9 | 24 | 6 | 37 | 31 | - |
| v3_copy3 | 240 | 10 | 24 | 3 | 32 | 34 | - |
| v5_copy5 | 242 | 11 | 23 | 3 | 38 | 34 | ❌ longest |

---

## Proshka Analysis (2026-01-15)

### Key Insight: Differences are in Proof-Engineering, Not Math

All 7 variants share the same mathematical skeleton:
1. `log n ≤ √n` for n ≥ 3
2. `log(n)/n^{10.5} ≤ 1/n^{10}`
3. Tail bound via p-series → ζ(2) → π-sandwich

### Why v1 is 23% Shorter than v5

**v1 uses `suffices` for early goal reduction:**
- Reduces goal first, then proves simpler target
- Avoids infrastructure duplication

**v5 uses "have ladder" pattern:**
- Builds up context step by step
- Repeats summability/nonnegativity proofs
- More `convert`, `ring_nf`, `field_simp`

### `aesop` Analysis

| Usage | Meaning | Example |
|-------|---------|---------|
| 1-2 calls | Glue for boilerplate | v1, v4, v6 ✅ |
| 10+ calls | Proof search noise | v0 ❌ |

Heavy `aesop` means:
- Slower compilation
- Less auditable
- More fragile to Mathlib changes

### ζ(2) Detour: Necessary?

All variants use `hasSum_zeta_two` (ζ(2) = π²/6), but this is **overkill** for `< 0.001`.

**π-free alternative (more stable):**
```
∑_{n≥3} 2log(n)/n^{10.5} ≤ ∑_{n≥3} 2/n^{10}
                        ≤ (2/3^8) * ∑_{n≥3} 1/n^2
                        ≤ 2/6561 * 1
                        ≈ 0.0003 < 0.001
```

No π dependencies → survives API changes.

---

## Patterns to Extract (Proshka Recommendations)

### 1. `log_le_sqrt_nat` (ROI: HIGH)

Currently each variant proves this differently via:
- `Real.log_le_sub_one_of_pos`
- `Real.log_two_lt_d9`

Extract to `Q3/Utils/LogBounds.lean`:
```lean
lemma log_le_sqrt_nat {n : ℕ} (hn : 3 ≤ n) : Real.log n ≤ Real.sqrt n := by
  -- one canonical proof
```

### 2. `tsum_subtype_ge_eq_nat_add` (ROI: HIGH)

All variants rebuild `Equiv.ofBijective` for:
```
∑' n : {k // 3 ≤ k}, f n = ∑' m : ℕ, f (m + 3)
```

Extract as utility lemma.

### 3. Summable obligations (ROI: MEDIUM)

Common forms that get re-proven:
- `Summable (fun n => 1/(n+c)^p)`
- `Summable` after `mul_left`
- `Summable` after `Subtype` restriction

### 4. `exact?` → Explicit lemmas (ROI: HIGH for stability)

`exact?` is a search hole. For long-term maintainability, replace with explicit lemma names.

---

## Variant Recommendations

### For Human Readability: v1
- Shortest (197 lines)
- Clear `suffices` structure
- Minimal `aesop`
- ⚠️ Has `exact?` patterns

### For API Stability: v4 or v6
- Moderate length
- No exotic tactics (`simp +zetaDelta` etc.)
- Less "searchy" proof structure

### For Maximum Stability: π-free rewrite
- Remove ζ(2) dependency entirely
- Use crude but sufficient bounds
- Most robust to Mathlib changes

---

## Future Aristotle Prompt Policy

Based on this analysis, include in prompts:

```markdown
## Policy
1. **AVOID:** `exact?`, heavy `aesop` (>2 calls)
2. **PREFER:** `suffices` for goal reduction
3. **USE:** explicit lemmas over search tactics
4. **SKIP:** ζ(2)/π unless precision required
```

---

## Key Lemmas Used Across Versions

| Mathlib Lemma | Purpose | Stability |
|---------------|---------|-----------|
| `Real.log_le_sub_one_of_pos` | Bound log by linear | ✅ stable |
| `Real.log_two_lt_d9` | log 2 < 0.7 | ⚠️ naming convention |
| `Real.sqrt_eq_rpow` | √n = n^{1/2} | ✅ stable |
| `hasSum_zeta_two` | ∑ 1/n² = π²/6 | ✅ stable but overkill |
| `summable_nat_add_iff` | Shift summation index | ✅ stable |
| `Real.rpow_add` | n^a · n^b = n^{a+b} | ✅ stable |

---

## Conclusions

1. **v1 is best for readability** (shortest, clearest structure)
2. **v4/v6 best for stability** (less search, more explicit)
3. **π-free version would be best overall** (not yet implemented)
4. **Extract utilities** to reduce future Aristotle output size
5. **Update prompt policy** to guide toward v1-style proofs

---

Generated: 2026-01-15
Analysis by: Claude + Proshka
Job IDs: fb91fbb3, ee8bc919, 78a7d870, e648f487, caf3e4c0, ba71a35a, c020a6a2
