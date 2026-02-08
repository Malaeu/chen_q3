---
tags: [proof, axiom, error, subagent, steering, pipeline]
priority: medium
last_updated: 2026-02-08
---

# Lean Debugging Guide: From 13h Hang to 8s Build

**Date:** 2026-01-19  
**Case Study:** `Q3/Proofs/Rayleigh_Q_identification.lean`

---

## PART 1: DIAGNOSTIC WORKFLOW

### Step 1: Identify the Hanging File

```bash
# Run build and watch output
lake build Q3.Main 2>&1 | tee build.log

# If it hangs, check last line:
tail -1 build.log
# Output: [7378/7385] Building Q3.Proofs.Rayleigh_Q_identification

# Check if process is actually working or stuck:
top -p $(pgrep -f "lean.*Rayleigh")
# If CPU 100% but no disk I/O for minutes → stuck in elaboration
```

### Step 2: Binary Search for Problem Location

**Method: Comment out half the file**

```lean
-- Step 2a: Comment out bottom half of theorems
-- If builds → problem is in bottom half
-- If hangs → problem is in top half

-- Step 2b: Narrow down to specific theorem
-- Keep bisecting until you find the exact theorem

-- Step 2c: Within the theorem, bisect the proof
theorem problematic_theorem : Goal := by
  step1
  step2
  -- comment from here
  step3  
  step4
  sorry  -- temporary placeholder
```

### Step 3: Isolate the Proof Step

```lean
-- Create minimal test file
-- test_hang.lean:

import Q3.Proofs.SomePrerequisite

-- Copy ONLY the problematic theorem with minimal context
theorem test_theorem : Goal := by
  -- paste suspected problematic tactic here
  sorry

-- Run: lake env lean test_hang.lean
-- Faster iteration than full build
```

### Step 4: Check Heartbeats Consumption

```lean
-- Add before the problematic proof:
set_option trace.profiler true in
theorem test : Goal := by
  problematic_tactic
  sorry

-- Or use maxHeartbeats to find threshold:
set_option maxHeartbeats 100000 in  -- 100k - very fast
set_option maxHeartbeats 1000000 in -- 1M - normal
set_option maxHeartbeats 10000000 in -- 10M - slow
set_option maxHeartbeats 0 in -- infinite - DANGEROUS, only for testing
```

### Step 5: Trace Specific Systems

```lean
-- Trace typeclass instance resolution (most common culprit):
set_option trace.Meta.synthInstance true in

-- Trace unification:
set_option trace.Meta.isDefEq true in

-- Trace simp lemmas being tried:
set_option trace.Meta.Tactic.simp true in

-- Trace all:
set_option trace.all true in  -- WARNING: massive output
```

---

## PART 2: COMMON PERFORMANCE KILLERS

### Killer #1: `simpa using` with Complex Types

**BAD:**
```lean
have h : HasSum (fun n => ∫ x in a..b, f n x) (∫ x, g x) :=
  simpa using MeasureTheory.Integrable.hasSum_intervalIntegral hint
```

**WHY:** `simpa` tries to unify goal with lemma output through simp. With deep typeclass hierarchies (MeasureTheory, integrals), this explores exponentially many paths.

**GOOD:**
```lean
have h : HasSum (fun n => ∫ x in a..b, f n x) (∫ x, g x) := by
  have h := MeasureTheory.Integrable.hasSum_intervalIntegral hint
  convert h using 2  -- "using N" limits unification depth
```

**Detection:**
```bash
grep -n "simpa using.*Integrable\|simpa using.*HasSum\|simpa using.*Measure" *.lean
```

### Killer #2: `exact?` / `apply?` in Complex Goals

**BAD:**
```lean
theorem foo : ComplexGoal := by
  exact?  -- searches entire library
```

**WHY:** Searches all lemmas in scope, tries unification with each.

**GOOD:**
```lean
-- Use Explore agent to find lemma name first:
-- "Search Mathlib for lemmas about X"
-- Then use explicit:
theorem foo : ComplexGoal := specific_lemma arg1 arg2
```

### Killer #3: Heavy `simp` without Arguments

**BAD:**
```lean
simp  -- tries ALL simp lemmas
simp only []  -- same problem
```

**GOOD:**
```lean
simp only [specific_lemma1, specific_lemma2]
simp only [mul_comm, add_assoc]  -- list exactly what you need
```

**Detection:**
```bash
grep -n "^\s*simp\s*$\|simp only \[\]" *.lean
```

### Killer #4: `aesop` without Bounds

**BAD:**
```lean
aesop  -- unbounded search
```

**GOOD:**
```lean
aesop (options := { maxRuleApplications := 100 })
-- Or better: just don't use aesop for complex goals
```

### Killer #5: `decide` on Large Finite Types

**BAD:**
```lean
-- If n is large:
example : (Fin 1000000).card = 1000000 := by decide
```

**GOOD:**
```lean
example : (Fin 1000000).card = 1000000 := Fintype.card_fin _
```

---

## PART 3: TYPE ERROR DEBUGGING

### Error: "unknown identifier"

**Diagnosis:**
```lean
-- Check what's in scope:
#check identifierName

-- Check if namespace is open:
open SomeNamespace in
#check identifierName
```

**Common fixes:**
```lean
-- Add opens at file top:
open MeasureTheory Set Real in
-- Now: Integrable, EqOn, volume, pi work without prefix
```

### Error: "type mismatch" with coercions

**Diagnosis:**
```lean
-- See actual types:
#check (expression : expectedType)

-- See what Lean inferred:
example : _ := expression  -- hover to see inferred type
```

**Common fix - explicit casts:**
```lean
-- BAD: m is ℤ, function expects ℝ
continuous_add_right m

-- GOOD:
continuous_add_right (m : ℝ)

-- Or use ↑ notation:
continuous_add_right ↑m
```

### Error: "function expected" in conv

**BAD:**
```lean
conv_lhs => 
  ext n
  rw [h_factor n]
```

**GOOD:**
```lean
-- Use Finset.sum_congr instead:
have h_eq : (∑ n, f n) = (∑ n, g n) :=
  Finset.sum_congr rfl (fun n _ => h_factor n)
rw [h_eq]
```

### Error: "failed to synthesize instance"

**Diagnosis:**
```lean
-- Check what instance is needed:
#check (inferInstance : InstanceType)

-- Trace instance search:
set_option trace.Meta.synthInstance true in
example : Goal := by exact problematic_term
```

**Common fixes:**
```lean
-- Provide instance explicitly:
haveI : SomeInstance := constructInstance
exact lemma_needing_instance

-- Or use @-notation:
@lemma_name explicitInstance args
```

---

## PART 4: PROOF STEP DEBUGGING

### Tactic: See Goal State

```lean
theorem foo : Goal := by
  step1
  trace "{goal}"  -- prints current goal
  step2
  sorry
```

### Tactic: Check Intermediate Types

```lean
theorem foo : Goal := by
  have h : IntermediateType := someExpr
  -- Now check: does h have the type you expect?
  show FinalGoal  -- makes goal explicit
  sorry
```

### Tactic: Unfold Definitions Manually

```lean
theorem foo : f x = y := by
  unfold f  -- see what f expands to
  -- or:
  simp only [f]  -- same effect
  sorry
```

### Tactic: Check Lemma Signature

```lean
-- Before using a lemma:
#check @lemma_name
-- See exact signature with all implicit args

-- Use with explicit args if inference fails:
@lemma_name Type1 inst1 arg1 arg2
```

---

## PART 5: BUILD SYSTEM DEBUGGING

### Check Single File

```bash
# Fast - just typecheck:
lake env lean Q3/Proofs/SomeFile.lean

# With timing:
time lake env lean Q3/Proofs/SomeFile.lean

# With verbose output:
lake env lean -v Q3/Proofs/SomeFile.lean
```

### Check Dependencies

```bash
# See what a file imports:
grep "^import" Q3/Proofs/SomeFile.lean

# Find circular imports:
lake env lean --print-deps Q3/Main.lean | sort | uniq -d
```

### Clean and Rebuild

```bash
# Clean build artifacts:
lake clean

# Rebuild from scratch:
lake build Q3.Main

# Just one file:
lake build Q3.Proofs.SomeFile
```

### Check Axiom Count (Project-Specific)

```bash
# Our script:
./scripts/check_axioms.sh

# Manual:
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3'
```

---

## PART 6: CASE STUDY - THIS FIX

### Initial Symptoms
- Build hung at step [7378/7385] for 13+ hours
- `set_option maxHeartbeats 50000000` didn't help
- CPU 100% on lean process

### Diagnostic Steps Taken

1. **Identified file:** `Rayleigh_Q_identification.lean`
2. **Binary searched:** Found `integral_P_A_eq_arch_term` theorem
3. **Bisected proof:** Found `hsum_base` step
4. **Traced:** `set_option trace.Meta.synthInstance true` showed endless instance search
5. **Identified pattern:** `simpa using MeasureTheory.Integrable.hasSum_intervalIntegral`

### Fixes Applied

| Problem | Solution |
|---------|----------|
| `simpa using` hang | `have h := ...; convert h using 2` |
| Missing `Integrable` | `open MeasureTheory Set` |
| `continuous_add_right m` type | `continuous_add_right (m : ℝ)` |
| `[[a, b]]` parsed as List | `Set.uIcc a b` |
| `tsum_subtype` wrong direction | Add `.symm` |
| `conv_lhs + ext` error | `Finset.sum_congr rfl (fun n _ => ...)` |

### Results

| Metric | Before | After |
|--------|--------|-------|
| Build time | 13+ hours (hung) | ~8 seconds |
| Heartbeats | 50M (timeout) | 4M (success) |
| File builds | No | Yes |

### Final Settings

```lean
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 50000
```

---

## QUICK REFERENCE CARD

```
HANG DEBUGGING:
1. lake build 2>&1 | tail    → which file?
2. Binary search (comment half) → which theorem?
3. Bisect proof → which tactic?
4. trace.Meta.synthInstance → what's looping?

COMMON FIXES:
- simpa using X  →  have h := X; convert h using N
- simp           →  simp only [lemma1, lemma2]
- exact?         →  find lemma manually, use exact
- aesop          →  nlinarith, positivity, ring, omega

TYPE ERRORS:
- unknown identifier    →  open Namespace
- type mismatch        →  explicit cast (x : Type)
- instance not found   →  haveI or @-notation

FAST ITERATION:
- lake env lean file.lean    (single file)
- test_file.lean with sorry  (minimal reproduction)
```
