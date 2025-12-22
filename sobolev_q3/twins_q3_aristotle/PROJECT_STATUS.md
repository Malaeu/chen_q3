# Twin Primes Q3: Project Status

**Last Updated:** 2025-12-22
**Aristotle Projects:** 1 COMPLETE ✅, 1 submitted

---

## 🎯 Project Goal

Formalize Q3 (spectral gap) specifically for twin primes, leveraging the mod 6 structure to achieve stronger cancellation than general Q3.

**Key Insight:** β ≈ -0.31 < 0 for twins (vs β < 0.5 for standard Q3)

---

## 📊 Aristotle Submission Status

| File | Project ID | Status | Expected |
|------|------------|--------|----------|
| Q3_twins_mod6.md | `9e350715-3b07-464a-8c37-fa88c33d82d1` | ✅ **COMPLETE** | 🟢 Easy |
| Q3_twins_exp_sum.md | `2647ad4e-a3ce-42e5-8bca-6b1ca80bdca4` | 403 Forbidden | 🔴 Hard |

---

## 🏆 OPUS vs ARISTOTLE: Proof Comparison

### `twin_prime_mod6` theorem

| Aspect | Opus (Manual) | Aristotle (AI) |
|--------|---------------|----------------|
| **File** | `Twins/Mod6Structure.lean` | `aristotle_output/Q3_twins_mod6_aristotle.lean` |
| **Lines** | ~60 (with lemmas) | ~10 |
| **Approach** | Explicit case analysis | `interval_cases` brute force |
| **Key Tactics** | `omega`, `rcases`, custom lemmas | `interval_cases`, `simp_all +decide` |
| **Readability** | High (educational) | Low (dense) |
| **Lean version** | v4.14.0 | v4.24.0 |

### Opus Proof Structure:
```
1. prime_not_dvd_2/3 — primes > 3 not divisible by 2, 3
2. h_residue — p % 6 ∈ {1, 5}
3. Contradiction: if p % 6 = 1 → p+2 % 6 = 3 → 3|(p+2)
4. Conclusion: p % 6 = 5 ✅
```

### Aristotle Proof Core:
```lean
interval_cases _ : p % 6 <;> simp_all +decide
```
Brute-forces all 6 residues, uses `simp_all` to resolve.

**Check status:**
```bash
cd twins_q3_aristotle && uv run python submit_twins.py --status
```

---

## 📁 Project Structure

```
twins_q3_aristotle/
├── Twins/                    # Lean 4 source files
│   ├── Defs.lean             # TwinPrime, twinExpSum, etc.
│   ├── Axioms.lean           # T1.1-T1.4, T2.1-T2.4
│   ├── Mod6Structure.lean    # Theorem: twins ≡ 5 (mod 6)
│   └── Main.lean             # Entry point
├── aristotle_input/          # Input .md files for Aristotle
│   ├── Q3_twins_mod6.md
│   └── Q3_twins_exp_sum.md
├── aristotle_output/         # Generated .lean files (when complete)
├── submit_twins.py           # Submission script
├── project_ids.txt           # Saved project IDs
├── README.md
└── PROJECT_STATUS.md         # This file
```

---

## 📋 Axiom Status

### Tier-1: Elementary (PROVABLE)

| ID | Name | Status |
|----|------|--------|
| T1.1 | `prime_coprime_6` | To prove |
| T1.2 | `coprime_6_iff_residue` | To prove |
| T1.3 | `prime_residue_mod6` | To prove |
| T1.4 | `residue_3_div_3` | To prove |

### Tier-2: Twin Prime Q3

| ID | Name | Status | Notes |
|----|------|--------|-------|
| T2.1 | `twin_prime_mod6` | ⏳ Aristotle | Theorem, should work |
| T2.2 | `q3_twins` | AXIOM | Numerical evidence |
| T2.3 | `weyl_equidistribution_twins` | AXIOM | Conjectural |
| T2.4 | `hardy_littlewood_asymptotic` | AXIOM | Twin Prime Conjecture |

---

## 🔢 Numerical Evidence

### Phase Function Comparison (N = 100,000)

| f(p) | β (exponent) | |S|/√N | Variance |
|------|--------------|--------|----------|
| p·ln(3) | **-0.31** | 0.048 | Optimal |
| p·ln(2) | -0.16 | 0.061 | Good |
| p·π | -0.19 | 0.193 | |
| p·e | +0.01 | 0.398 | |
| p·√2 | +0.39 | 0.790 | |

### Mod 6 Structure Verification

```
Total twin pairs (p ≤ 100,000): 1,224
  p ≡ 5 (mod 6): 1,223 (99.9%)
  p ≡ 3 (mod 6): 1 (only (3,5))
  Other residues: 0
```

---

## 🔗 Connection to Main Q3

This project extends `/full/q3.lean.aristotle/`:

| Main Q3 | Twins Q3 |
|---------|----------|
| All primes | Twin primes only |
| Q3: β < 0.5 | Q3_twins: β ≈ -0.31 |
| General Circle Method | Mod 6 structure exploitation |
| Weil criterion | Same foundation |

**Shared Axioms (from main Q3):**
- Weil criterion (T1.1)
- Guinand-Weil explicit formula (T1.2)
- Szegő-Böttcher theory (T1.4)

---

## 📝 Next Steps

1. ⏳ Wait for Aristotle results on `Q3_twins_mod6`
2. 🔧 Integrate generated proof into `Mod6Structure.lean`
3. ✅ Mark `Q3_twins_exp_sum` as axiom (T2.2) - too hard for Aristotle
4. 📦 Connect to main Q3 via shared definitions
5. 🎯 Write main theorem combining mod 6 + Q3_twins

---

## 📚 References

1. Hardy, G.H. & Littlewood, J.E. (1923). "Some problems of 'Partitio Numerorum' III"
2. Zhang, Y. (2014). "Bounded gaps between primes"
3. Maynard, J. (2015). "Small gaps between primes"
4. Polymath (2014). "Variants of the Selberg sieve"
