# Formalization Stats (Snapshot)

Last updated: 2026-01-21
Scope: Q3 Lean codebase - **ONLY code in proof chain counted**

Notes:
- Counts are from `./scripts/contribution_stats.sh`
- Aristotle contribution = files actually USED in proof chain (not experiments)
- Line counts include comments and whitespace

---

## 🎯 Q3/ Codebase Summary

| Metric | Count |
|--------|-------|
| **Total lines** | 25,137 |
| Theorems | 262 |
| Lemmas | 548 |
| Definitions | 303 |

---

## 📊 Contribution Breakdown (ACCURATE)

### Summary Table

| Source | Lines | % of Q3/ |
|--------|-------|----------|
| **Aristotle (in proof chain)** | 5,131 | 20% |
| **Human/Manual** | 20,773 | 82% |
| **TOTAL Q3/** | **25,137** | 100% |

### 🤖 Aristotle Contribution Details

**A) Files integrated into Q3/Proofs/ (Aristotle-generated):**

| File | Lines |
|------|-------|
| A1_density.lean | 1,748 |
| A1_density_main.lean | 895 |
| RKHS_contraction.lean | 371 |
| HatInterpolation.lean | 339 |
| Digamma_Aristotle.lean | 298 |
| off_diag_exp_sum.lean | 170 |
| A3_bridge.lean | 149 |
| W_sum_finite.lean | 122 |
| Q_nonneg_on_atoms.lean | 110 |
| node_spacing.lean | 105 |
| S_K_small.lean | 57 |
| **SUBTOTAL** | **4,364** |

**B) Files imported from aristotle_output/:**

| File | Lines |
|------|-------|
| d1524982_aristotle.lean | 767 |
| **SUBTOTAL** | **767** |

**TOTAL ARISTOTLE IN PROOF CHAIN: 5,131 lines**

### 🧪 Aristotle Experiments (NOT in proof chain)

| Metric | Count |
|--------|-------|
| Total aristotle_output/ files | 72 |
| Total aristotle_output/ lines | 18,440 |
| Used in proof chain | 767 |
| **Unused (experiments)** | **17,673** |

---

## 📁 Q3/Proofs/A1prime/ (New Module)

| File | Lines | Description |
|------|-------|-------------|
| A1_density_fixed_t0.lean | 401 | Main A1 density theorem (fixed t₀) |
| HeatError.lean | 329 | Heat kernel error bounds |
| HatInterpBounded.lean | 189 | Hat interpolation with bounds |
| **TOTAL** | **919** | |

---

## 📈 DB Statistics

Database: `aristotle_db/aristotle_proofs.db`

| Metric | Count |
|--------|-------|
| Documents | 44 |
| Lemmas/Theorems | 555 |
| Specs | 9 |

---

## 🏆 Axiom Status

| Axiom | Status |
|-------|--------|
| a_star_pos | ✅ CLOSED |
| a_star_continuous | ✅ CLOSED |
| a_star_bdd_on_compact | ✅ CLOSED |
| a_star_even | ✅ CLOSED |
| A1_density_WK | ✅ CLOSED |
| Q_Lipschitz_on_W_K | ✅ CLOSED |
| RKHS_contraction | ✅ CLOSED |
| P_A_continuous | ✅ CLOSED |
| Schur_test | ⚪ EXTERNAL |
| Weil_criterion | ⚪ EXTERNAL |
| Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom | ❌ OPEN |

**Current: 6 axioms (3 standard + 3 project)**
**Remaining closable: 1**

---

## 🔧 Regenerate Stats

```bash
cd /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle
./scripts/contribution_stats.sh
```

---

*Update this file after major proof completions or axiom closures.*
