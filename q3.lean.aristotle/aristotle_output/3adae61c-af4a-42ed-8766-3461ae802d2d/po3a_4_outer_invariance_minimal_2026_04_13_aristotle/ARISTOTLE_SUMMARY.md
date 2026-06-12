# Summary of changes for run 3adae61c-af4a-42ed-8766-3461ae802d2d
# PO3a.4 — Outer-Invariance Minimal Bridge: Formalization Complete

## File created
`RequestProject/PO3a4.lean` — a fully proven Lean 4 formalization of the outer-invariance rigidity theorem.

## What was proved

### Core algebraic lemma (`rank_one_vanishing`)
In a real inner product space, if `a ≠ 0`, `d ≠ 0`, and the rank-1 operator equation
```
∀ v, -⟪c, v⟫ • a + ⟪d, v⟫ • (s • a - b) = 0
```
holds, then there exist scalars `λ, μ` with `b = λ • a`, `c = μ • d`, and `λ + μ = s`.

### Outer-invariance rigidity theorem (`outer_invariance_rigidity`)
Given vectors `hp, xp, hm, xm` in a real inner product space and continuous linear maps `Ustar : E →L[ℝ] F`, `Vstar : E →L[ℝ] G` (the adjoint outer operators, **not** assumed to be the identity), if:
1. `Ustar` is injective on `span{hp, xp}`,
2. `Vstar` is injective on `span{hm, xm}`,
3. `hp ≠ 0` and `hm ≠ 0`,
4. The receiver `K = -|Ustar hp⟩⟨Vstar xm| + |s · Ustar hp - Ustar xp⟩⟨Vstar hm| = 0`,

then `xp = λ • hp`, `xm = μ • hm`, and `λ + μ = s`.

This confirms the key claim: the real outer-factor case collapses back to the identity-outer scalar rigidity once the outer operators are locally injective.

### Helper lemmas
- `exists_inner_ne_zero`: a nonzero vector has nonzero inner product with some vector.
- `mem_span_of_inner_vanishing`: if `⟪c, v⟫ = 0` whenever `⟪d, v⟫ = 0` and `d ≠ 0`, then `c = μ • d`.
- `proportional_of_injective_on_span`: injectivity on a span transfers proportionality from images back to originals.

## Proof strategy
The proof of `rank_one_vanishing` proceeds by:
1. Specializing the operator equation to vectors orthogonal to `d`, deducing `⟪c, v⟫ = 0` for all `v ⊥ d`.
2. Concluding `c = μ • d` by the orthogonal complement argument.
3. Substituting back and using `d ≠ 0` to extract the remaining scalar relation.

The `outer_invariance_rigidity` theorem applies `rank_one_vanishing` to the images under `Ustar` and `Vstar`, then uses injectivity to pull the proportionality relations back to the original vectors.

## Design notes
- The theorem is stated for abstract real inner product spaces with continuous linear maps, not assuming `U = V = I`.
- The sign-split structure `H = H₊ ⊕ H₋` is implicit: the codomain types `F` and `G` of `Ustar` and `Vstar` play the roles of `H₊` and `H₋`.
- All proofs are fully machine-verified with no `sorry` and only standard axioms.