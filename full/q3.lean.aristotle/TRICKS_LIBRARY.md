# Tricks Library - Q3 Lean Formalization

Knowledge base of tactics, patterns, workarounds, and insights discovered during axiom closure.

## Tags
- `#tactic` - Working tactic combinations
- `#workaround` - Lean/Mathlib limitation bypasses
- `#pattern` - Recurring proof patterns
- `#pitfall` - Traps to avoid
- `#bridge` - Theorem connection techniques
- `#mathlib` - Useful Mathlib lemmas

---

## 2026-01-16 | Iteration 1 | A3_bridge_axiom investigation

### #pitfall: a_star vs P_A symbol mismatch
**Context:** Trying to close A3_bridge_axiom by wiring proven A3_bridge_rayleigh_Fourier
**Problem:** `A3_bridge_data` uses sampling Toeplitz with `a_star` symbol, but proven version uses Fourier Toeplitz with `P_A` symbol. These are mathematically DIFFERENT:
- `a_star(ξ) → -∞` as |ξ| → ∞ (no global floor!)
- `P_A(θ)` is periodized windowed symbol with floor ≥ c* = 11/10

**Solution:** Cannot bridge directly. Need to refactor chain to use Fourier formulation:
1. Use `A3_bridge_data_rayleigh_Fourier` instead of `A3_bridge_data`
2. Prove Rayleigh-Q identification (tex Theorem 3.3)
**Files:**
- `Q3/Axioms.lean:428` - old A3_bridge_data (sampling)
- `Q3/Proofs/P_A_Toeplitz_bridge.lean:63` - new A3_bridge_data_rayleigh_Fourier (Fourier)
- `docs/insights/a_star_vs_p_a_dossier.md` - analysis

### #bridge: Rayleigh-Q identification (Theorem 3.3)
**Context:** Need to connect proven Rayleigh bounds to Q ≥ 0 on atoms
**Problem:** Rayleigh quotient bound is on matrices, Q functional is on test functions
**Solution:** tex Theorem 3.3 shows: `⟨(T_M[P_A] - T_P^{(M)}) 1, 1⟩ = Q(Φ_{B,t})`
- For constant polynomial p≡1, Rayleigh quotient equals Q on the Fejér×heat atom
- This bridges matrix bounds → functional positivity
**File:** `full/sections/A3/rayleigh_bridge.tex:66-96`

### #pattern: Type mismatch blocks axiom closure
**Context:** Proven theorem exists but with different type signature
**Problem:** Chain uses `A3_bridge_data K` but proven version provides `A3_bridge_data_rayleigh_Fourier K`
**Solution:** Either:
1. Add type conversion lemma (if mathematically equivalent)
2. Refactor chain to use new type (if mathematically different)
In this case: types are mathematically different (sampling vs Fourier) → need option 2.

