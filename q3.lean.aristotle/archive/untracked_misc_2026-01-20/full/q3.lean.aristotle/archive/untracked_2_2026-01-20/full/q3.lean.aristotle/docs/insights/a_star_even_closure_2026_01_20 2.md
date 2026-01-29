# a_star_even Closure via Mathlib Gamma_conj

**Date:** 2026-01-20
**Status:** CLOSED (axiom → theorem)
**Impact:** Axiom count: 11 → 10

## Summary

Successfully closed the `a_star_even` axiom using Mathlib's `Complex.Gamma_conj` lemma.

## Mathematical Background

The axiom stated: `a_star(-ξ) = a_star(ξ)` (evenness of archimedean kernel).

Where:
- `a_star(ξ) = 2π(log π - Re(ψ(1/4 + iπξ)))`
- `ψ(z) = Γ'(z)/Γ(z)` is the digamma function

## Proof Strategy

1. **Conjugation symmetry of argument:**
   - `z(ξ) = 1/4 + iπξ`
   - `z(-ξ) = 1/4 - iπξ = conj(z(ξ))`

2. **Gamma conjugation (Mathlib):**
   - `Complex.Gamma_conj`: `Γ(z̄) = Γ(z)̄`

3. **Derivative conjugation:**
   - Using `HasDerivAt.conj_conj` from Mathlib
   - If `star ∘ f ∘ star = f`, then `deriv f (star z) = star (deriv f z)`
   - Since `Gamma` satisfies this, we get `Γ'(z̄) = Γ'(z)̄`

4. **Digamma conjugation:**
   - `ψ(z̄) = Γ'(z̄)/Γ(z̄) = Γ'(z)̄/Γ(z)̄ = ψ(z)̄`

5. **Real part extraction:**
   - `Re(ψ(z̄)) = Re(conj(ψ(z))) = Re(ψ(z))`
   - Therefore `a_star(-ξ) = a_star(ξ)`

## Key Mathlib Lemmas Used

- `Complex.Gamma_conj`: `Γ(conj z) = conj (Γ z)`
- `Complex.Gamma_ne_zero`: `Γ(z) ≠ 0` when `z ≠ -n` for natural `n`
- `Complex.differentiableAt_Gamma`: Gamma differentiable away from poles
- `HasDerivAt.conj_conj`: Derivative of `star ∘ f ∘ star`
- `Complex.conj_re`: `Re(conj z) = Re(z)`

## Files Modified

1. **Created:** `Q3/Proofs/A_Star_Properties.lean`
   - Contains `a_star_even_thm` and supporting lemmas

2. **Modified:** `Q3/Axioms.lean`
   - Changed `axiom a_star_even` to `theorem a_star_even := a_star_even_thm`
   - Added import for `A_Star_Properties`

3. **Modified:** `Q3/AxiomsTheorems.lean`
   - Added import and re-export of `a_star_even`

## Remaining a_star Axioms

Still as axioms (potential future work):
- `a_star_pos`: Requires digamma bounds (harder)
- `a_star_continuous`: Should be doable via DigammaSeries.lean
- `a_star_bdd_on_compact`: Follows from continuity

## Lessons Learned

1. **Check existing project lemmas first:** `DigammaSeries.lean` had useful building blocks
2. **Mathlib `star` = complex conjugation:** Use `star_def` to convert
3. **`HasDerivAt.conj_conj` is powerful:** Gives derivative conjugation for free
4. **Argument domain matters:** `Re(1/4 + iπξ) = 1/4 > 0` avoids all Gamma poles

## Verification

```bash
echo 'import Q3.Main
#print axioms Q3.Main.RH_of_Weil_and_Q3' | lake env lean --stdin
```

Result: `a_star_even` no longer in axiom list (10 axioms total).
