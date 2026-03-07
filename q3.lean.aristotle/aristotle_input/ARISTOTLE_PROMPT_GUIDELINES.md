# Aristotle Prompt Guidelines

Based on analysis of 7 weight_sum_bound variants (2026-01-15).
Source: Proshka analysis + empirical data.

## Tactic Policy

### AVOID (or strictly limit)

| Tactic | Why | Alternative |
|--------|-----|-------------|
| `exact?` | Useful for local search, but can be fragile if left everywhere | Explicit lemma names when stable |
| `aesop` (heavy) | Proof search noise, slow, unauditable | `simp`, `linarith`, `nlinarith`, `gcongr` |
| `simp +zetaDelta` | Obscure, fragile | Explicit subtype handling |
| Long `have` chains | Duplicates infrastructure | `suffices` for goal reduction |

### PREFER

```lean
-- Goal reduction (v1 pattern - shortest proof)
suffices h : simpler_goal by
  exact this_follows_from h

-- Explicit tactics
nlinarith [Real.pi_gt_three, Real.pi_le_four]
positivity
gcongr
```

## Structural Guidelines

### 1. Use `suffices` for early goal reduction

**Good (v1 pattern):**
```lean
lemma tail_bound : ∑' n, f n < 0.001 := by
  suffices h : ∑' n, g n < 0.001 by
    exact tsum_le_tsum ... h
  -- now prove simpler goal
```

**Avoid (v5 pattern):**
```lean
lemma tail_bound : ∑' n, f n < 0.001 := by
  have h1 : ... := by ...
  have h2 : ... := by ...
  have h3 : ... := by ...
  have h4 : ... := by ...
  -- lots of infrastructure duplication
```

### 2. Factor reindexing into utilities

Instead of rebuilding `Equiv.ofBijective` every time:

```lean
-- Define once in Utils
lemma tsum_subtype_ge_eq_nat_add (c : ℕ) (f : ℕ → ℝ) :
    ∑' n : {k : ℕ // c ≤ k}, f n = ∑' m : ℕ, f (m + c) := by
  -- one-time proof
```

### 3. Provide utility lemmas in prompt

If you have standard lemmas, tell Aristotle to use them:

```markdown
## Available Lemmas (use these, don't reprove)

- `log_le_sqrt_nat {n : ℕ} (hn : 3 ≤ n) : Real.log n ≤ Real.sqrt n`
- `tsum_subtype_ge3_eq_nat_add3 (f : ℕ → ℝ) : ∑' n : {k // 3 ≤ k}, f n = ∑' m, f (m+3)`
- `summable_one_div_pow_add (c : ℕ) (p : ℝ) (hp : 1 < p) : Summable (fun n => 1/(n+c)^p)`
```

### 4. Consider π-free bounds

For tail sum estimates, ζ(2) = π²/6 is overkill when you only need `< 0.001`.

**π-free approach:**
```lean
-- Instead of: hasSum_zeta_two + nlinarith [pi_gt_three, pi_le_four]
-- Use: direct comparison

∑_{n≥3} 1/n^{10} ≤ (1/3^8) * ∑_{n≥3} 1/n^2
                 ≤ (1/3^8) * 1
                 = 1/6561 < 0.0002
```

More stable: no π dependencies, survives API changes.

## Prompt Template

```markdown
# [Title]

## Goal
Prove: [exact Lean statement]

## Available Lemmas
[List any utilities you want Aristotle to use]

## Proof Strategy
[High-level outline: 3-5 steps]

## Policy
- Use `suffices` for goal reduction
- `exact?` is allowed for local search if it helps the prover close the goal
- Prefer explicit lemma names in the final cleaned patch when stable
- Minimize `aesop` - prefer `nlinarith`, `positivity`, `gcongr`
- No π/ζ(2) unless necessary - prefer direct bounds

## Definitions
[Full Lean definitions, not LaTeX references]
```

## Metrics (from 7 variants)

| Metric | v1 (best) | v5 (worst) | Target |
|--------|-----------|------------|--------|
| Lines | 197 | 242 | < 200 |
| `aesop` | 1 | 3 | ≤ 2 |
| `have` | 35 | 34 | ≤ 30 |
| `suffices` | yes | no | yes |

## Key Utility Lemmas to Extract

1. **`log_le_sqrt_nat`** - `log n ≤ √n` for n ≥ 3
2. **`tsum_subtype_ge_eq_nat_add`** - reindex {n // c ≤ n} ↔ ℕ
3. **`summable_one_div_pow_add`** - Summable (1/(n+c)^p)
4. **`tail_sum_crude_bound`** - ∑_{n≥N} 1/n^p ≤ 1/(N^{p-1}*(p-1))

---

Generated: 2026-01-15
Based on: Proshka analysis of weight_sum_bound variants
