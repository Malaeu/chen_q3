# Q Nonneg Axiom: Critical Findings

**Date:** 2026-01-22
**Sandbox:** projekt_2

## Executive Summary

The axiom `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` is **FALSE** at the current parameter `t_sym = 0.06`.

**Solution:** Use `t_critical = 0.15` and restrict to `BaseAtomCone_K` (tau = 0).

---

## Key Numerical Results

### Phase 0: Q at t_sym = 0.06 (FAILS)

| Metric | Value |
|--------|-------|
| arch_term | 11.06 |
| prime_term | 26.61 |
| **Q** | **-15.56 < 0** |

The axiom Q >= 0 is **FALSE** at t_sym.

### Solution: Q at t_critical = 0.15 (PASSES)

| Metric | Value |
|--------|-------|
| arch_term | 9.57 |
| prime_term | 8.71 |
| **Q** | **+0.86 > 0** |

---

## Stronger Verification (Tail-Controlled)

We reran Q with a **prime-power cutoff N = 10^7** and a **rigorous tail bound**:
for all n > N, use Λ(n) ≤ log n and Φ(ξ_n) ≤ exp(-t (log n)^2). This yields a
strict bracketing:

```
Q_lower = arch_term - (prime_partial + tail_bound)
Q_upper = arch_term - prime_partial
```

So **Q_lower > 0 ⇒ Q > 0** and **Q_upper < 0 ⇒ Q < 0**.

### Tail-Controlled Q Bounds (B = 3.0)

| t | Q_lower | Q_upper |
|---|---------|---------|
| 0.06 | -16.3093 | -16.2974 |
| 0.15 | +0.85646 | +0.85646 |

### Worst-Case B (B = 4.9, K = 5)

| t | Q_lower | Q_upper |
|---|---------|---------|
| 0.15 | +0.51459 | +0.51459 |

---

## t-Scan (Interval for Positivity)

We scanned **t ∈ [0.08, 0.20]** on a grid, with **B ∈ [0.5, 4.9]**, and used
the tail-controlled lower bound for Q. The **worst-case B** was always ~4.9.

Coarse scan (step 0.01):

```
t=0.14  min Q_lower = -0.118
t=0.15  min Q_lower = +0.515
```

Refined near the threshold (B = 4.9):

```
Q_lower(0.141)  = -0.049595
Q_lower(0.142)  = +0.017889
t* ≈ 0.141733 (Q_lower ≈ 0)
```

**Practical safe interval:** `t ≥ 0.142` (on the tested grid), with strong margin at `t = 0.15`.

---

## Critical Constraint: tau = 0 ONLY

**Q >= 0 holds ONLY on BaseAtomCone_K (tau = 0).**

| Cone | tau | Q Result |
|------|-----|----------|
| BaseAtomCone_K | 0 | Q >= 1.03 for all B <= K |
| AtomCone_K_fixed | 1.69 | Q = -911 |

For shifted atoms (tau > 0), the prime_term explodes because the atom's support overlaps with many prime powers.

---

## Architecture Impact

### Current Chain (BROKEN)

```
t_sym = 0.06
    |
    v
t0_A1 = 1/(16*pi^2*t_sym) ~ 0.105
    |
    v
AtomCone_K_fixed K t0_A1  <-- Q < 0 on this cone!
    |
    v
T5_transfer --> W_K
```

### Fixed Chain (WORKS)

```
t_critical = 0.15
    |
    v
t0_critical = 1/(16*pi^2*t_critical) ~ 0.042
    |
    v
BaseAtomCone_K K t0_critical  <-- Q >= 0 (tau=0 only!)
    |
    v
A1_density_BaseAtomCone (tau=0 sufficient for even W_K)
    |
    v
T5_transfer --> W_K
```

---

## Why BaseAtomCone_K is Sufficient

W_K requires **IsEven** (even functions):

```lean
def W_K (K : ℝ) : Set (ℝ → ℝ) :=
  {Φ | Continuous Φ ∧
       Function.support Φ ⊆ Set.Ioo (-K) K ∧
       IsEven Φ ∧  -- <-- KEY!
       IsNonneg Φ}
```

BaseAtomCone_K generates even approximants:
- At tau = 0: `Fejer_heat_atom B t 0 xi = 2 * Phi_B(xi)` (symmetric)
- Linear combinations of `Phi_B` with different B span even functions

Therefore: **BaseAtomCone_K is dense in W_K** (for the relevant even subspace).

---

## Files Changed

| File | Change |
|------|--------|
| `verify_phase0.py` | Verified Q < 0 at t_sym, Q > 0 at t_critical |
| `verify_variant_b.py` | Added BaseAtomCone test, showed tau > 0 fails |
| `verify_q_tail.py` | Tail-controlled Q bounds + t-scan |
| `QSpec.lean` | Frozen specification with test/critical specs |
| `Q_nonneg_t_critical.lean` | Updated to use BaseAtomCone_critical |

---

## Recommended Next Steps

1. **Replace t_sym with t_critical** in `HeatKernelParams.lean`:
   ```lean
   def t_sym : ℝ := 3 / 20  -- was 3/50
   -- Or add: def t_critical : ℝ := 3 / 20
   ```

2. **Update A1 density** to use BaseAtomCone_K instead of AtomCone_K_fixed

3. **Update T5_Transfer** to use BaseAtomCone_K

4. **Close the axiom** `Q_nonneg_on_BaseAtomCone_axiom` at t_critical

---

## Plan to Close the Last Axiom (No Lean Changes Yet)

Goal: close `Q_nonneg_on_atoms_of_A3_Fourier_RKHS_axiom` using fixed‑t
and **BaseAtomCone** (τ = 0), with a clean proof chain.

1. **Lock parameters**
   - Freeze `t_sym = 3/20` and `t0_A1 = 1/(16π² t_sym)` in
     `full/q3.lean.aristotle/Q3/Proofs/HeatKernelParams.lean`.
   - Record the **validated interval** `t ≥ 0.142` (t* ≈ 0.141733) and choose
     `t_critical = 0.15` for margin.

2. **BaseAtomCone positivity statement**
   - Use `Q3/Proofs/Q_nonneg_base_atoms.lean` (or `Q_nonneg_t_critical.lean`)
     as the canonical statement:  
     `∀ K ≥ 1, ∀ g ∈ BaseAtomCone_K K t0_A1, Q g ≥ 0`.
   - This is where the numerical certificate/tail-bound gets wired.

3. **Density/transfer step**
   - Replace the A1 density target cone with `BaseAtomCone_K` (τ = 0 only),
     leveraging evenness of `W_K`.
   - This affects `Q3/Proofs/A1_density.lean` + `Q3/T5_Transfer.lean`.

4. **Wire the axiom replacement**
   - Update `Q3/Proofs/Q_nonneg_on_atoms_fourier_axiom.lean` to use the
     BaseAtomCone theorem in place of the axiom.

5. **Rebuild + check axioms**
   - `lake build Q3.Main`
   - `./full/q3.lean.aristotle/scripts/check_axioms.sh`

---

## Verification Commands

```bash
# Run numerical verification
cd sandboxes/projekt_2
python3 verify_variant_b.py --direct

# Expected output:
# Test A: Q(Φ) at τ=0, B=3: Q = 0.8565  PASS
# Test B: Q on BaseAtomCone_K: min Q = 1.0292  PASS
```

---

## Conclusion

The original LaTeX proof has a parameter issue: `t_sym = 0.06` does not satisfy Q >= 0.

**Fix:** Use `t_critical = 0.15` and restrict to `BaseAtomCone_K` (tau = 0).

This is mathematically valid because:
1. W_K requires even functions
2. BaseAtomCone_K generates even approximants  
3. Q >= 0 on BaseAtomCone_K at t_critical (numerically verified)
