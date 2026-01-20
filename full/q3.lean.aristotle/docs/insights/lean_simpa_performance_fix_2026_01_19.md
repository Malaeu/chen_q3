# Lean `simpa` Performance Killer: 13h Hang → 8s Build

**Date:** 2026-01-19  
**File:** `Q3/Proofs/Rayleigh_Q_identification.lean`  
**Impact:** Build hung at step [7378/7385] for 13+ hours

---

## Problem Detection

**Symptoms:**
- `lake build Q3.Main` hangs indefinitely at specific step
- Even `set_option maxHeartbeats 50000000` doesn't help
- CPU at 100% but no progress

**How to identify:**
```bash
# Check which file is stuck
lake build 2>&1 | tail -10

# Look for:
# [7378/7385] Building Q3.Proofs.Rayleigh_Q_identification
# (no progress for minutes/hours)
```

---

## Root Cause

**Killer pattern:**
```lean
-- BAD: causes infinite typeclass unification
have hsum_base :
    HasSum (fun n : ℤ =>
        ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
      (∫ x, g B t x) :=
  simpa using MeasureTheory.Integrable.hasSum_intervalIntegral (μ := volume)
    (f := fun x => g B t x) (y := (-1/2 : ℝ)) hint
```

**Why it hangs:**
- `simpa using X` tries to unify the goal with `X` via simplification
- MeasureTheory + interval integrals have deep typeclass hierarchies
- Lean spends exponential time trying all unification paths
- `synthInstance.maxHeartbeats` limits don't help because it's not instance synthesis

---

## Solution

**Replace `simpa using` with explicit `convert`:**

```lean
-- GOOD: finishes in milliseconds
have hsum_base :
    HasSum (fun n : ℤ =>
        ∫ x in (-1/2 : ℝ) + (n : ℝ)..(-1/2 : ℝ) + (n : ℝ) + 1, g B t x)
      (∫ x, g B t x) := by
  have h := MeasureTheory.Integrable.hasSum_intervalIntegral (μ := volume)
    (f := fun x => g B t x) (y := (-1/2 : ℝ)) hint
  convert h using 2
```

**Why it works:**
- `have h := X` assigns without unification
- `convert h using 2` allows shallow structural differences
- Lean doesn't explore deep typeclass paths

---

## Related Fixes (Same Session)

### 1. Missing namespace opens
```lean
-- Add at file top:
open MeasureTheory Set
```
Without this: `Integrable`, `EqOn`, `volume` unrecognized.

### 2. Integer vs Real coercion for `continuous_add_right`
```lean
-- BAD: m is ℤ, continuous_add_right expects ℝ
(continuous_g B t).comp (continuous_add_right m)

-- GOOD: explicit cast
(continuous_g B t).comp (continuous_add_right (m : ℝ))
```

### 3. Set interval syntax
```lean
-- BAD: [[a, b]] parses as List (List ℝ)
EqOn f g [[(-1/2 : ℝ), (1/2 : ℝ)]]

-- GOOD: explicit Set.uIcc
EqOn f g (Set.uIcc (-1/2 : ℝ) (1/2 : ℝ))
```

### 4. `tsum_subtype_eq_of_support_subset` direction
```lean
-- WRONG direction:
(tsum_subtype_eq_of_support_subset hsupport)

-- RIGHT: need .symm
(tsum_subtype_eq_of_support_subset hsupport).symm
```

### 5. `conv_lhs + ext n` failure
```lean
-- BAD: "function or arrow expected" error
conv_lhs => 
  ext n
  rw [h_factor n]

-- GOOD: use Finset.sum_congr
have h_sum_eq : (∑ n : Nodes K, f n) = (∑ n : Nodes K, g n) :=
  Finset.sum_congr rfl (fun n _ => h_factor n)
rw [h_sum_eq]
```

---

## Performance Results

| Metric | Before | After |
|--------|--------|-------|
| Build time | 13+ hours (hung) | ~8 seconds |
| Heartbeats | 50M (still timeout) | 4M (success) |
| File builds | No | Yes |

---

## Quick Detection Checklist

When a Lean file hangs:

1. **Search for `simpa using` with MeasureTheory types**
   ```bash
   grep -n "simpa using.*Integrable\|simpa using.*HasSum\|simpa using.*Measure" file.lean
   ```

2. **Check if goal involves:**
   - `HasSum` / `Summable`
   - `Integrable` / `intervalIntegrable`
   - `MeasureTheory.Measure`
   - Complex typeclass chains

3. **Fix pattern:**
   ```lean
   -- From:
   X := simpa using lemma args
   
   -- To:
   X := by
     have h := lemma args
     convert h using N  -- N = 1, 2, or 3
   ```

---

## Final heartbeat settings

```lean
-- After all fixes, these are sufficient:
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 50000
```

---

## Files Modified

- `Q3/Proofs/Rayleigh_Q_identification.lean` (lines 32-33, 167-184, 310-413, 529, 571-576)

## Commit

After fix, full build passes:
```bash
lake build Q3.Main  # [7385/7385] in ~15 seconds total
```
