# Q3 Formalization Workflow Checklist

**Purpose:** Ensure every change follows our Philosophy of Proof.
**Reference:** See `PHILOSOPHY_OF_PROOF.md` for full rationale.

---

## Before EVERY Commit

### Step 1: Build Passes
```bash
cd full/q3.lean.aristotle
lake build Q3.Main
```
- [ ] Build completes with no errors
- [ ] Only warnings are acceptable (no `sorry` in main chain)

### Step 2: Axiom Audit
```bash
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | grep -v "^info:"
```

**Expected axioms (11 total):**
```
Standard Lean (3):
  - propext
  - Classical.choice
  - Quot.sound

Level 1 - Classical (6):
  - Q3.Weil_criterion
  - Q3.Schur_test
  - Q3.a_star_pos
  - Q3.a_star_bdd_on_compact
  - Q3.a_star_continuous
  - Q3.a_star_even

Level 2 - Q3 Paper (2):
  - P_A_continuous
  - Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom
```

**Checklist:**
- [ ] Count matches expected (11 total)
- [ ] No UNKNOWN axioms appeared
- [ ] If count DECREASED → document in commit message (progress!)
- [ ] If count INCREASED → STOP and justify in `PHILOSOPHY_OF_PROOF.md`

### Step 3: No Circular Dependencies
```bash
# Each axiom should only depend on itself + Standard Lean
lake env lean -c 'import Q3.Main; #print axioms Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom'
# Should show: [propext, Classical.choice, Q3.Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom, Quot.sound]
```
- [ ] Axioms don't depend on other Q3 axioms (no hidden chains)

### Step 4: Philosophy Compliance Questions

Answer these before committing:

1. **Did you add a new `axiom`?**
   - [ ] NO → proceed
   - [ ] YES → Is it justified? Add to `PHILOSOPHY_OF_PROOF.md` with:
     - Mathematical statement
     - Citation (paper section or literature)
     - Why it can't be a theorem yet

2. **Did you convert an axiom to a theorem?**
   - [ ] YES → Great! Document in commit message
   - [ ] Update `PROJECT_ASCII.md` status

3. **Did you add `sorry`?**
   - [ ] NO → proceed
   - [ ] YES, but NOT in main chain → OK for development
   - [ ] YES, in main chain → STOP, this breaks verification

4. **Does any new code hide complexity?**
   - [ ] NO → proceed
   - [ ] YES → Refactor to be explicit

---

## Commit Message Template

```
[Category] Brief description

Changes:
- List specific changes

Axiom Status:
- Added: (none / list new axioms with justification)
- Removed: (none / list axioms now proven as theorems)
- Total: 11 (or new count)

Philosophy Check: ✓
```

**Categories:**
- `[Proof]` - Changes to proof structure
- `[Bridge]` - New bridge file connecting axiom to proof
- `[Theorem]` - Axiom converted to theorem
- `[Docs]` - Documentation only
- `[Refactor]` - Code reorganization, no logic change

---

## Weekly Axiom Health Report

Run weekly to track progress:

```bash
#!/bin/bash
echo "=== Q3 Axiom Health Report ==="
echo "Date: $(date)"
echo ""
echo "Main theorem axioms:"
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | grep -E "Q3\." | wc -l
echo ""
echo "Full list:"
lake env lean -c 'import Q3.Main; #print axioms Q3.Main.RH_of_Weil_and_Q3' 2>&1 | grep -E "Q3\."
```

Save output to `reports/axiom_health_YYYY-MM-DD.txt` for tracking.

---

## Red Flags (STOP and Review)

### 🚨 STOP if you see:

1. **New axiom without citation**
   ```lean
   axiom some_thing : P  -- NO CITATION = RED FLAG
   ```

2. **Axiom depending on another Q3 axiom**
   ```
   #print axioms Q3.New_axiom
   → includes Q3.Other_axiom  -- RED FLAG: hidden dependency
   ```

3. **`sorry` in main proof chain**
   ```lean
   theorem RH_of_Weil_and_Q3 : RH := by
     ...
     sorry  -- RED FLAG: breaks verification
   ```

4. **Axiom count increased without explanation**
   - Was 12, now 15 → WHERE DID 3 COME FROM?

5. **Circular reasoning**
   ```lean
   axiom A : P → Q
   axiom B : Q → P  -- Together they prove nothing
   ```

---

## Green Flags (Good Progress)

### ✅ Celebrate when:

1. **Axiom converted to theorem**
   - Axiom count decreased
   - `#print axioms` shows fewer Q3.* dependencies

2. **Bridge closed**
   - `sorry` count in bridge file → 0
   - Logic connects axiom to usage

3. **Mathlib integration**
   - Axiom replaced with Mathlib theorem
   - No custom assumption needed

---

## Quick Reference Card

```
╔════════════════════════════════════════════════════════════════╗
║                    Q3 PHILOSOPHY QUICK CHECK                   ║
╠════════════════════════════════════════════════════════════════╣
║                                                                ║
║  ✅ GOOD:                      ❌ BAD:                         ║
║  • theorem X := ...            • axiom X (no citation)         ║
║  • axiom X -- [Paper §3.2]     • sorry in main chain           ║
║  • hypothesis h : P            • hidden dependencies           ║
║  • explicit reduction          • "trust me bro"                ║
║                                                                ║
║  COMMANDS:                                                     ║
║  • lake build Q3.Main                                          ║
║  • #print axioms Q3.Main.RH_of_Weil_and_Q3                    ║
║                                                                ║
║  CURRENT: see PROJECT_ORCHESTRATOR.md (counts + tiers)         ║
║                                                                ║
╚════════════════════════════════════════════════════════════════╝
```

---

## Changelog

| Date | Axiom Count | Change |
|------|-------------|--------|
| 2026-01-13 | 10 | Closed arch/prime Lipschitz + RKHS contraction |
| ... | ... | ... |

---

*Follow this checklist religiously. Talia is watching.* 😄
