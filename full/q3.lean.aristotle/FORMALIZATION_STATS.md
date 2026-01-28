# Formalization Stats (Snapshot)

Last updated: 2026-01-28
Scope: Q3 Lean codebase - **ONLY code in proof chain counted**

Notes:
- Counts are from `./scripts/contribution_stats.sh`
- Axiom status updated 2026-01-26; line counts last generated 2026-01-24
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
| a_star_linear_growth | ⚪ EXTERNAL |
| A1_density_WK | ✅ CLOSED |
| Q_Lipschitz_on_W_K | ✅ CLOSED |
| RKHS_contraction | ✅ CLOSED |
| P_A_continuous | ✅ CLOSED |
| Weil_criterion_tau0 | ⚪ EXTERNAL |
| PrimeCert.prime_b_grid_val_le_margin | ❌ OPEN (cert) |
| PrimeCert.prime_margin_Lipschitz_on_Brange | ❌ OPEN (cert) |

**Current: 7 axioms (4 standard + 3 project)**
**Remaining closable: 2 (PrimeCert certificates)**

---

## 🔧 Regenerate Stats

```bash
cd /Users/emalam/Documents/GitHub/chen_q3/full/q3.lean.aristotle
./scripts/update_formalization_stats.sh
```

---

*Update this file after major proof completions or axiom closures.*

## Raw Script Output (auto)

<!-- stats:start -->
```
╔════════════════════════════════════════════════════════════════╗
║              Q3 CONTRIBUTION STATISTICS                        ║
╚════════════════════════════════════════════════════════════════╝

Date: Sat Jan 24 14:14:46 CET 2026

═══ Section 1: Total Q3/ Codebase ═══
  Total lines:       27800
  Theorems:            287
  Lemmas:              623
  Definitions:         333

═══ Section 2: Aristotle Contribution (IN PROOF CHAIN) ═══

A) Aristotle-generated files in Q3/Proofs/:
    1748  Q3/Proofs/A1_density.lean
     895  Q3/Proofs/A1_density_main.lean
     149  Q3/Proofs/A3_bridge.lean
     298  Q3/Proofs/Digamma_Aristotle.lean
     339  Q3/Proofs/HatInterpolation.lean
     110  Q3/Proofs/Q_nonneg_on_atoms.lean
     371  Q3/Proofs/RKHS_contraction.lean
      57  Q3/Proofs/S_K_small.lean
     122  Q3/Proofs/W_sum_finite.lean
     105  Q3/Proofs/node_spacing.lean
     170  Q3/Proofs/off_diag_exp_sum.lean
   ─────
    4364  SUBTOTAL (integrated into Q3/Proofs/)

B) Aristotle files imported from aristotle_output/:
     767  aristotle_output/d1524982_aristotle.lean
   ─────
     767  SUBTOTAL (imported)

╔══════════════════════════════════════════════════════════════╗
║  TOTAL ARISTOTLE IN PROOF CHAIN:  5131 lines              ║
╚══════════════════════════════════════════════════════════════╝

═══ Section 3: Human/Manual Contribution ═══
  Q3/ total:                 27800
  - Aristotle integrated: 4364
  ─────────────────────────
  Human-written in Q3/:   23436

═══ Section 4: Aristotle Experiments (NOT in proof chain) ═══
  Total aristotle_output/ files:       72
  Total aristotle_output/ lines:    18440
  Used in proof chain:           767
  Unused (experiments):          17673

═══ Section 5: Q3/Proofs/A1prime/ (New Module) ═══
  Files:
     401  A1_density_fixed_t0.lean
     189  HatInterpBounded.lean
     329  HeatError.lean
   ─────
     919  TOTAL A1prime/

═══ SUMMARY ═══

  ┌─────────────────────────────────────────────────────────┐
  │ Source                    │   Lines │   % of Q3/       │
  ├─────────────────────────────────────────────────────────┤
  │ Aristotle (in proof)      │    5131 │  18%             │
  │ Human/Manual              │   23436 │  84%             │
  ├─────────────────────────────────────────────────────────┤
  │ TOTAL Q3/                 │   27800 │ 100%             │
  └─────────────────────────────────────────────────────────┘

  Aristotle experiments (not used): 17673 lines

═══ Done ═══
```
<!-- stats:end -->
