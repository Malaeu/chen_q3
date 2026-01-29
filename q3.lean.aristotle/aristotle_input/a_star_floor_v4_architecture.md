# Architecture Analysis: How to Fix the Chain

## Current situation
The Q3 proof chain has a symbol mismatch:

```
A3_bridge_rayleigh_from_weight_sum
    requires: h_rayleigh_lower_bound for ToeplitzMatrix(..., a_star)

A3_FLOOR
    proves: P_A_ge_c_star for P_A (different function!)
```

## Option 1: Prove a_star ≥ c_star directly
**Approach:** Show that inf_{ξ} a_star(ξ) ≥ 11/10

**Pros:**
- Simplest chain modification
- Uses existing ToeplitzMatrix definition

**Cons:**
- May not be true! Need to check digamma asymptotics
- a(ξ) → 0 as ξ → ∞ (digamma growth cancels log π)

**Verdict:** Likely FALSE — a_star probably goes to 0 at infinity.

## Option 2: Change ToeplitzMatrix to use P_A
**Approach:** Modify the chain to use ToeplitzMatrix(..., P_A B t) instead of a_star

**Pros:**
- P_A_ge_c_star is already proven
- Mathematically more correct (P_A is the actual symbol)

**Cons:**
- Need to verify P_A works with existing Toeplitz theory
- P_A depends on parameters B, t

**Verdict:** Potentially correct approach

## Option 3: Use Fourier ToeplitzEntry instead of sampling
**Approach:** Replace ToeplitzMatrix (sampling) with ToeplitzEntry (Fourier coefficients)

**Pros:**
- rayleigh_lower_bound already proven for this in rayleigh_v1.lean
- Classical Toeplitz theory applies directly

**Cons:**
- Need to change many files
- May affect other parts of the chain

**Verdict:** Major refactor but mathematically clean

## Option 4: Prove equivalence for specific symbols
**Approach:** Show that for a_star specifically, Rayleigh bound holds

**Pros:**
- Minimal changes to existing code
- May use special properties of a_star

**Cons:**
- Need custom proof for a_star

**Verdict:** Worth exploring

## Recommendation
Analyze:
1. What is lim_{ξ→∞} a_star(ξ)? If > 1.1, Option 1 works.
2. If not, Option 2 (use P_A) is likely correct path.

## Key question for Aristotle
Which option is mathematically correct for the Q3 paper?
What does the LaTeX say about which symbol to use?
