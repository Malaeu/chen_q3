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

Status: STAGE 4/4 DONE (A3_FLOOR proven)
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

## STAGE 2: Monotonicity ✅ DONE

**Files:**
- `A3_FLOOR_v19_monotonicity.lean` (full proof, no axioms)
- `A3_FLOOR_v16_deriv_digamma_eq_trigamma.lean` (core lemma)

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
| `deriv_a_neg` | ✅ | correct sign: a'(ξ) < 0 for ξ > 0 | **CRITICAL** |
| `strictAntiOn_a` | ✅ | a strictly decreasing on (0,∞) | **CRITICAL** |

### Proof Chain:
```
deriv_a_eq + im_trigamma_neg → deriv_a_neg
deriv_a_neg + continuousOn_a → strictAntiOn_a
```

---

## STAGE 3: Numerical Bounds ✅ DONE

**File:** `A3_FLOOR_v20_bounds_core.lean`

| Lemma | Status | Value | DB Priority |
|-------|--------|-------|-------------|
| `a_half_bound` | ✅ | a(1/2) ≥ 5/8 | **HIGH** |
| `a_three_half_bound` | ✅ | a(3/2) ≥ -1/2 | **HIGH** |
| `a_five_half_bound` | ✅ | a(5/2) ≥ -21/20 | **HIGH** |
| `a_one_bound` | ✅ | a(1) ≥ -1/50 | **HIGH** |
| `a_two_bound` | ✅ | a(2) ≥ -2 | **HIGH** |
| `a_three_bound` | ✅ | a(3) ≥ -3 | **HIGH** |
| `w_bounds` | ✅ | w(1/2), w(1), w(3/2), w(2) | **HIGH** |
| `tail_bound` | ✅ | Tail = 0 (support of w, |ξ|>3) | **HIGH** |

---

## STAGE 4: Final Theorem ✅ DONE

**File:** `A3_FLOOR_v22_stage4_floor.lean`

| Theorem | Status | Description | DB Priority |
|---------|--------|-------------|-------------|
| `P_A_ge_c_star` | ✅ | P_A(θ) ≥ 11/10 ∀θ | **CRITICAL** |

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
2. `A3_FLOOR_v16_deriv_digamma_eq_trigamma.lean` ← Stage 2
3. `A3_FLOOR_v19_monotonicity.lean` ← Stage 2
4. `A3_FLOOR_v20_bounds_core.lean` ← Stage 3
5. `A3_FLOOR_v22_stage4_floor.lean` ← Stage 4

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
│  (a decreasing)   │ │  (a values)     │ │ (T=0 by support)│
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

**Last Updated:** 2026-01-12
**Next Action:** интеграция A3_FLOOR в основной chain и зачистка устаревших заметок.

<!-- AUTO-STATUS:BEGIN -->
Auto status (DB snapshot): 2026-01-12 18:54

Doc status (A3_FLOOR + Q3_DigammaRemainder):
| doc_id | status | lines |
| --- | --- | --- |
| A3_FLOOR_v3 | proven | 201 |
| A3_FLOOR_v6 | proven | 313 |
| A3_FLOOR_v8 | proven | 291 |
| A3_FLOOR_v16 | proven | 329 |
| A3_FLOOR_v19 | proven | 505 |
| A3_FLOOR_v20_core | proven | 853 |
| A3_FLOOR_v20_manual | missing | 0 |
| A3_FLOOR_v21_manual | missing | 0 |
| A3_FLOOR_v22_stage4 | proven | 879 |
| A3_FLOOR_THEOREM | missing | 0 |
| Q3_DigammaRemainder | proven | 2084 |

Counts: missing=3, proven=8
Generated by scripts/update_status.py
<!-- AUTO-STATUS:END -->
