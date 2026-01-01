# PROOF MAP: A3_FLOOR New Kernel Approach

**Created:** 2025-12-28
**Status:** IN PROGRESS (Stage 2/4, conditional)
**Primary File:** [A3_FLOOR_ROADMAP.md](A3_FLOOR_ROADMAP.md) ← **ALWAYS CHECK THIS FOR CURRENT STATUS**

---

## EXECUTIVE SUMMARY

```
NEW KERNEL APPROACH (A3_FLOOR)
═══════════════════════════════════════════════════════════════
Target: P_A(θ) ≥ c_* = 11/10 for all θ ∈ [-1/2, 1/2]

Method: Digamma/Trigamma analysis
  a(ξ) = log π - Re(ψ(1/4 + iπξ))

Chain: im_trigamma_neg → deriv_a_neg → strictAntiOn_a → bounds → P_A

Status: STAGE 2/4 (Monotonicity, conditional)
═══════════════════════════════════════════════════════════════
```

---

## ⚠️ IMPORTANT: OLD vs NEW APPROACH

| Aspect | OLD (PROOF_MAP.md) | NEW (this file) |
|--------|-------------------|-----------------|
| Strategy | RKHS_contraction ‖T_P‖ < 1 | A3_FLOOR P_A ≥ 11/10 |
| Key operator | T_P (prime operator) | P_A (Archimedean sum) |
| Analysis | Schur test, off-diagonal | Trigamma, digamma |
| Constants | c_* = 1.5 | c_* = 11/10 |
| Files | RKHS_*.lean | A3_FLOOR_*.lean |
| **Priority** | LOW (old approach) | **HIGH (current focus)** |

---

## STAGE 1: Trigamma Foundations ✅ COMPLETE

**File:** `A3_FLOOR_v3_trigamma_foundations.lean`
**Aristotle ID:** f86d36da

### Proven Lemmas (HIGH PRIORITY for DB):

| Lemma | Status | Description | DB Priority |
|-------|--------|-------------|-------------|
| `im_trigamma_neg` | ✅ | Im(ψ''(z)) < 0 for Im(z) > 0 | **HIGH** |
| `trigamma_summable` | ✅ | Series Σ 1/(z+n)² converges | **HIGH** |
| `digamma_add_one` | ✅ | ψ(z+1) = ψ(z) + 1/z | **HIGH** |
| `deriv_a_eq` | ✅ | a'(ξ) = π·Im(ψ'(1/4+iπξ)) | **HIGH** |
| `continuousOn_a` | ✅ | a continuous on [0,∞) | **HIGH** |

### Key Tactics Used:
- `Complex.im_tsum` - for Im(tsum) = tsum(Im)
- `Summable.of_nonneg_of_le` - comparison tests
- `AnalyticAt.differentiableAt` - analyticity → differentiability

---

## STAGE 2: Monotonicity ⏳ IN PROGRESS

**Files:**
- `A3_FLOOR_v6_deriv_foundations.lean` (23KB)
- `A3_FLOOR_v7_repeat.lean` (16KB)
- `A3_FLOOR_v8_monotonicity.lean` (15KB)
- `A3_FLOOR_v11_fixed.lean` (local, lake-checked)

**Current Working File:** `A3_FLOOR_v11_fixed.lean` ← **conditional (axioms for deriv_digamma_eq_trigamma)**
**Aristotle IDs:** v9 be2b9846 (opaque defs, wrong sign), v11 e81da2b4 (one hole, fixed locally)

### Proven Lemmas:

| Lemma | Version | Status | DB Priority |
|-------|---------|--------|-------------|
| `trigamma_add_one` | v6,v7,v8 | ✅ | **HIGH** |
| `diff_digamma_trigamma_add_one` | v6,v7,v8 | ✅ | **HIGH** |
| `trigamma_tendsto_zero` | v6,v7,v8 | ✅ | **HIGH** |
| `trigamma_tendsto_zero_complex` | v8 | ✅ | **HIGH** |
| `deriv_digamma_add_one` | v8 | ✅ | **HIGH** |
| `digammaSeq` (definition) | v8 | ✅ | MEDIUM |
| `digammaSeq_deriv` | v8 | ✅ | MEDIUM |
| `deriv_digammaSeq_tendsto_trigamma` | v8 | ✅ | MEDIUM |

### TARGET LEMMAS (correct sign):

| Lemma | Status | Why Needed | DB Priority |
|-------|--------|------------|-------------|
| `deriv_a_neg` | ✅ (conditional) | correct sign: a'(ξ) < 0 for ξ > 0 | **CRITICAL** |
| `strictAntiOn_a` | ✅ (conditional) | a strictly decreasing on (0,∞) | **CRITICAL** |

**Blocking issues (must resolve before Stage 2 is complete):**
1. `deriv_digamma_eq_trigamma` is still assumed (axiom) in `A3_FLOOR_v11_fixed.lean`.
2. Replace axiom with a proven lemma (likely from a focused Aristotle run).

### Proof Chain:
```
deriv_a_eq + im_trigamma_neg → deriv_a_neg
deriv_a_neg + continuousOn_a → strictAntiOn_a
```

---

## STAGE 3: Numerical Bounds ⬚ TODO

**File:** `A3_FLOOR_bounds.lean` (to be created)

| Lemma | Status | Value | DB Priority |
|-------|--------|-------|-------------|
| `a_half_bound` | ⬚ | a(1/2) ≥ 0.68 | **HIGH** |
| `a_three_half_bound` | ⬚ | a(3/2) ≥ -0.45 | **HIGH** |
| `a_five_half_bound` | ⬚ | a(5/2) ≥ -1.00 | **HIGH** |
| `w_bounds` | ⬚ | w(1/2), w(1), w(2) | **HIGH** |
| `tail_bound` | ⬚ | Tail T ≤ 10⁻⁵ | **HIGH** |

---

## STAGE 4: Final Theorem ⬚ TODO

**File:** `A3_FLOOR_THEOREM.lean` (to be created)

| Theorem | Status | Description | DB Priority |
|---------|--------|-------------|-------------|
| `P_A_ge_c_star` | ⬚ | P_A(θ) ≥ 11/10 ∀θ | **CRITICAL** |

### Assembly:
```
strictAntiOn_a + numerical_bounds + tail_bound
    → g_bounds
    → P_A = 2π Σ g(θ+m) ≥ c*
    → A3 FLOOR PROVEN!
```

---

## DATABASE PRIORITY GUIDE

### HIGH PRIORITY (Import First)

These files contain **essential lemmas** for the new kernel:

1. `A3_FLOOR_v3_trigamma_foundations.lean` ← Stage 1
2. `A3_FLOOR_v6_deriv_foundations.lean` ← Stage 2
3. `A3_FLOOR_v8_monotonicity.lean` ← Stage 2 (new lemmas)
4. `A3_FLOOR_COMBINED.lean` (if exists)

### MEDIUM PRIORITY (Import Second)

Supporting definitions and auxiliary lemmas:

1. `A3_FLOOR_v7_repeat.lean` ← duplicates but different tactics
2. `UNIFORM_ARCH_FLOOR_defs.lean` ← definitions

### LOW PRIORITY (Skip or Import Last)

Old approach files - NOT needed for new kernel:

1. `RKHS_contraction*.lean` ← OLD approach
2. `off_diag_exp_sum*.lean` ← OLD approach
3. `S_K_small*.lean` ← OLD approach
4. `node_spacing*.lean` ← OLD approach (different context)

### EXCLUDE (Don't Import)

Files that are superseded or incorrect:

1. Any file with `c_* = 1.5` ← wrong constant
2. Files using mean-modulus approach ← incorrect method

---

## ARISTOTLE VERSION HISTORY

| Version | ID | Status | Result |
|---------|------|--------|--------|
| v3 | f86d36da | ✅ COMPLETE | trigamma_foundations |
| v4 | 73f35bb5 | ✅ COMPLETE | digamma series |
| v5 | 5c9cbf80 | ✅ COMPLETE | diff_digamma_trigamma |
| v6 | da9fe6a2 | ✅ COMPLETE | deriv_foundations (23KB!) |
| v7 | 74219d5a | ⚠️ REPEAT | re-proved same lemmas |
| v8 | 028f042c | ✅ COMPLETE | new lemmas (digammaSeq) |
| **v9** | **be2b9846** | **⚠️ CONDITIONAL** | **Opaque defs + missing deriv_digamma_eq_trigamma** |
| **v11** | **e81da2b4** | ✅ COMPLETE | one hole fixed locally in `A3_FLOOR_v11_fixed.lean` |

---

## CONSTANTS

| Constant | Value | Meaning | Source |
|----------|-------|---------|--------|
| c_* | **11/10 = 1.1** | Archimedean floor | NEW KERNEL |
| z₀ | 1/4 + iπξ | Base point for a(ξ) | Definition |
| ξ range | (0, ∞) | Domain for a | Definition |
| θ range | [-1/2, 1/2] | Domain for P_A | Theorem |

⚠️ OLD constant c_* = 1.5 is from DIFFERENT approach (RKHS). Don't confuse!

---

## QUICK STATUS CHECK

```bash
# Check Aristotle v9 status
cd /Users/emalam/Documents/GitHub/chen_q3
source .venv/bin/activate
python ~/.claude/skills/aristotle/scripts/status.py be2b9846
```

---

## DEPENDENCIES DIAGRAM

```
                    ┌─────────────────────┐
                    │   im_trigamma_neg   │ ← Stage 1
                    │   (Im(ψ'') < 0)     │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │     deriv_a_eq      │ ← Stage 1
                    │ (a' = π·Im(ψ'))     │
                    └──────────┬──────────┘
                               │
                    ┌──────────▼──────────┐
                    │    deriv_a_neg      │ ← Stage 2 (correct sign)
                    │    (a' < 0)         │
                    └──────────┬──────────┘
                               │
          ┌────────────────────┼────────────────────┐
          │                    │                    │
┌─────────▼─────────┐ ┌────────▼────────┐ ┌────────▼────────┐
│  strictAntiOn_a   │ │ numerical_bounds│ │   tail_bound    │
│  (a decreasing)   │ │  (a values)     │ │   (T ≤ 10⁻⁵)    │
└─────────┬─────────┘ └────────┬────────┘ └────────┬────────┘
          │                    │                    │
          └────────────────────┼────────────────────┘
                               │
                    ┌──────────▼──────────┐
                    │   P_A_ge_c_star     │ ← Stage 4 FINAL
                    │  (P_A ≥ 11/10)      │
                    └─────────────────────┘
```

---

**Last Updated:** 2025-12-28
**Next Action:** Prove `deriv_digamma_eq_trigamma` (remove axiom), then proceed to Stage 3
