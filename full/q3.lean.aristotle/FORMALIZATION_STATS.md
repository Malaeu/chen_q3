# Formalization Stats (Snapshot)

Last updated: 2026-01-21
Scope: Q3 Lean codebase (regex counts of declarations in .lean files).

Notes:
- Counts are approximate (regex-based).
- Declarations counted: lemma, theorem, def, abbrev, structure, instance.
- Line counts include comments and whitespace; nonempty excludes blank lines.

---

## 🎯 Grand Total

| Source | Lines | Theorems | Lemmas | Defs | Total Decls |
|--------|-------|----------|--------|------|-------------|
| **Q3/** (core) | 25,137 | 262 | 548 | 303 | 1,113 |
| **aristotle_output/** | 18,440 | ~130 | ~400 | ~400 | ~930 |
| **A3_FLOOR*** | 673 | 14 | 74 | 22 | 110 |
| **TOTAL** | **44,250** | **~406** | **~1,022** | **~725** | **~2,153** |

## Δ vs previous snapshot (2026-01-16)

| Source | Lines Δ | Theorems Δ | Lemmas Δ | Defs Δ | Total Decls Δ |
|--------|---------|------------|----------|--------|----------------|
| **Q3/** (core) | +6,920 | +63 | +156 | +15 | +234 |
| **aristotle_output/** | +3,114 | +17 | +44 | +31 | +92 |
| **A3_FLOOR*** | -2,232 | +0 | +0 | +0 | +0 |
| **TOTAL** | **+7,802** | **+80** | **+200** | **+46** | **+326** |

*Previous TOTAL line count was 36,448; current is 44,250.*

---

## 📊 Contribution Breakdown

### 🤖 Aristotle (AI-generated)

| Category | Files | Lines |
|----------|-------|-------|
| Total aristotle_output/ | 72 | 18,440 |

**Top Aristotle files by size:**
| File | Lines |
|------|-------|
| A1_density_main_aristotle.lean | 852 |
| d1524982_aristotle.lean | 767 |
| A1_density_bridge_v4_aristotle.lean | 644 |
| A1_FINAL_COMPLETE.lean | 553 |
| A1_density_hat_full_v1_aristotle.lean | 544 |

**Total Aristotle contribution: 18,440 lines (~42% of project)**

### 📐 A3_FLOOR (Numerical Analysis)

| File | Lines | Description |
|------|-------|-------------|
| A3_Floor_Main.lean | ~878 | Main floor theorem |
| A3_Floor_Bounds.lean | ~852 | Bound computations |
| Other A3_FLOOR*.lean | ~673 | Supporting files |

**Proves: P_A(θ) ≥ c* = 11/10 ∀θ**

### 👨‍💻 Manual/Human-written (Q3/ core)

| Category | Lines | Thm/Lemmas |
|----------|-------|------------|
| Q3/Proofs/ | ~12,000 | ~450 |
| Q3/Archive/ | ~5,000 | ~150 |
| Q3/ other | ~8,137 | ~210 |
| **Total Q3/** | **25,137** | **810** |

---

## 📈 DB Statistics

Database: `aristotle_db/aristotle_proofs.db`

| Metric | Count |
|--------|-------|
| Documents | 44 |
| Lemmas/Theorems | 555 |
| Specs | 9 |

### Document Status
| Status | Count |
|--------|-------|
| proven | 40 |
| in_progress | 4 |

---

## 🏆 Axiom Closure Progress

| Axiom | Status | Proof Source |
|-------|--------|--------------|
| a_star_pos | ✅ CLOSED | positivity (2026-01-21) |
| a_star_continuous | ✅ CLOSED | Mathlib Gamma continuity |
| a_star_bdd_on_compact | ✅ CLOSED | continuous + compact |
| a_star_even | ✅ CLOSED | Mathlib Gamma_conj (2026-01-20) |
| A1_density_WK | ✅ CLOSED | Aristotle + HatInterpolation |
| Q_Lipschitz_on_W_K | ✅ CLOSED | Manual + bridges |
| RKHS_contraction | ✅ CLOSED | Manual + rescaling |
| P_A_continuous | ✅ CLOSED | A3_Floor_Main |
| Schur_test | ⚪ EXTERNAL | Classical (L2 vs L∞ insight) |
| Weil_criterion | ⚪ EXTERNAL | Classical literature |
| Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom | ❌ OPEN | Blocked: AtomCone_K_fixed gap |

**Current: 6 axioms total (3 standard + 3 project)**
- Standard: `propext`, `Classical.choice`, `Quot.sound`
- Project: `Weil_criterion`, `Schur_test`, `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`

**Remaining closable: 1** (`Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom`)

---

## Regenerate Script

```bash
cd /media/chirurgie/hdd01/Soft/GitHub/chen_q3/full/q3.lean.aristotle

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

# DB stats
python3 aristotle_db/parse_lean.py list-docs | wc -l
python3 aristotle_db/parse_lean.py list-lemmas | wc -l
```

---

*Update this file after major proof completions or axiom closures.*
