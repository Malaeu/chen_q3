# Formalization Stats (Snapshot)

Last updated: 2026-01-14
Scope: Q3 Lean codebase (regex counts of declarations in .lean files).

Notes:
- Counts are approximate (regex-based).
- Declarations counted: lemma, theorem, def, abbrev, structure, instance.
- Line counts include comments and whitespace; nonempty excludes blank lines.

---

## 🎯 Grand Total

| Source | Lines | Theorems | Lemmas | Defs | Total Decls |
|--------|-------|----------|--------|------|-------------|
| **Q3/** (core) | 17,081 | 196 | 356 | 280 | 853 |
| **aristotle_output/** | 11,201 | 92 | 262 | 286 | 648 |
| **A3_FLOOR*** | 2,901 | 14 | 74 | 22 | 110 |
| **TOTAL** | **31,183** | **302** | **692** | **588** | **1,611** |

## Δ vs previous snapshot

| Source | Lines Δ | Theorems Δ | Lemmas Δ | Defs Δ | Total Decls Δ |
|--------|---------|------------|----------|--------|----------------|
| **Q3/** (core) | +31 | -1 | +2 | +0 | +1 |
| **aristotle_output/** | +85 | +1 | +3 | +8 | +12 |
| **A3_FLOOR*** | +0 | +0 | +0 | +0 | +0 |
| **TOTAL** | +116 | +0 | +5 | +8 | +13 |

*Previous TOTAL line count was a rough estimate (~48,000); recompute gives 31,183.

---

## 📊 Contribution Breakdown

### 🤖 Aristotle (AI-generated)

| File | Lines | Source |
|------|-------|--------|
| HatInterpolation.lean | 339 | `bcec962f` - hat interpolation proof |
| A1_density_hat_chain.lean | 237 | `e90d4213` - full A1 chain |
| sandbox_test_result.lean | 49 | `c33c6672` - sandbox test |
| + 35 other output files | 10,491 | Various experiments |

**Total Aristotle contribution: 11,201 lines (~36% of project)**

### 📐 A3_FLOOR (Numerical Analysis)

| File | Lines | Thm/Lemmas |
|------|-------|------------|
| A3_FLOOR_v22_stage4_floor.lean | 878 | 27 |
| A3_FLOOR_v20_bounds_core.lean | 852 | 22 |
| A3_FLOOR_v19_monotonicity.lean | 504 | 19 |
| A3_FLOOR_v16_deriv_digamma_eq_trigamma.lean | 328 | 10 |
| A3_FLOOR_COMBINED.lean | 333 | 10 |
| A3_FLOOR_THEOREM.lean | 6 | 0 |

**Total A3_FLOOR: 2,901 lines, 88 theorems/lemmas**
*Proves: P_A(θ) ≥ c* = 11/10 ∀θ*

### 👨‍💻 Manual/Human-written (Q3/ core)

| Category | Files | Lines | Thm/Lemmas |
|----------|-------|-------|------------|
| Axioms/Main | 2 | 713 | 12 |
| Proofs/ | 44 | 8,846 | 321 |
| Archive/ | 20 | 4,568 | 146 |
| DigammaSeries | 2 | 2,571 | 48 |
| Other | 28 | 4,849 | 166 |

---

## Key Modules (Detailed)

```
Q3/Proofs/A1_density.lean
  lines: 1421 (nonempty 1346), namespaces: 0
  lemma 29 | theorem 1 | def 10

Q3/Proofs/HatInterpolation.lean
  lines: 339 (nonempty 315), namespaces: 1
  lemma 11 | theorem 1 | def 1

Q3/Proofs/Q_Lipschitz.lean
  lines: 290 (nonempty 246), namespaces: 1
  lemma 10 | theorem 2 | def 8

Q3/Proofs/RKHS_contraction.lean
  lines: 371 (nonempty 343), namespaces: 0
  lemma 5 | theorem 2 | def 8 | abbrev 1 | instance 1

Q3/Proofs/Bridge.lean
  lines: 512 (nonempty 460), namespaces: 1
  lemma 12 | theorem 5 | def 2

Q3/Proofs/A3_bridge_v3_uniform.lean
  lines: 98 (nonempty 75), namespaces: 1
  lemma 1 | theorem 2

Q3/Proofs/Q_nonneg_bridge_v2.lean
  lines: 74 (nonempty 56), namespaces: 1
  theorem 2
```

## Aggregate Totals

```
Q3/Proofs (44 files)
  lines: 8846 (nonempty 7589), namespaces: 37
  lemma 220 | theorem 101 | def 148 | abbrev 1 | structure 1 | instance 1

Q3 total (76 files)
  lines: 17081 (nonempty 14768), namespaces: 60
  lemma 356 | theorem 196 | def 280 | abbrev 8 | structure 8 | instance 5
```

---

## 🏆 Axiom Closure Progress

| Axiom | Status | Proof Source |
|-------|--------|--------------|
| A1_density_WK | ✅ PROVEN | Aristotle + HatInterpolation |
| Q_Lipschitz_on_W_K | ✅ PROVEN | Manual + bridges |
| RKHS_contraction | ✅ PROVEN | Manual + rescaling |
| A3_bridge_axiom | ❌ OPEN | Waiting for Rayleigh |
| Q_nonneg_on_atoms | ❌ OPEN | Depends on A3 |

**Current: 5/9 Tier-2 axioms closed**

---

## Regenerate Script

```bash
# Quick stats
echo "=== Q3 Stats ===" && \
find Q3 -name "*.lean" | xargs wc -l | tail -1 && \
echo "theorems: $(grep -r '^theorem' Q3 --include='*.lean' | wc -l)" && \
echo "lemmas: $(grep -r '^lemma' Q3 --include='*.lean' | wc -l)" && \
echo "defs: $(grep -r '^def\|^noncomputable def' Q3 --include='*.lean' | wc -l)"

# Aristotle output
echo "=== Aristotle ===" && \
find aristotle_output -name "*.lean" | xargs wc -l | tail -1

# A3_FLOOR
echo "=== A3_FLOOR ===" && \
find . -maxdepth 1 -name "A3_FLOOR*.lean" | xargs wc -l | tail -1
```

---

*Update this file after major proof completions or axiom closures.*
