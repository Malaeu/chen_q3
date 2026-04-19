# PO3a-A0 — двумерная телескопическая экстракция дефекта

## Address

- Main address: `PO3a-A0`
- Related: `PO3a-A`, `PO3a.4`, `H-bridge.11`

## Why this is the right next Aristotle task

We already have a good local shell for killing false `(+,-)` exact-sum profile
ansatzes by anti-diagonal defects.

The next reusable structural step is not numerical and not manuscript-specific:
we need a clean abstract theorem saying that a two-variable defect decomposes
into

1. one corner term,
2. one row-strip term,
3. one column-strip term,
4. one bulk mixed-difference term.

This is the exact bridge needed for the later `PO3a-A` route:

\[
D = \text{corner} + \text{row strip} + \text{column strip} + \text{bulk}.
\]

Once this abstract theorem is formalized, we can later plug in the real defect
\(D_{a,N}\) and identify the bulk term with the real candidate kernel.

## Exact task

Work over an additive commutative group `A`.

Let

```lean
D : ℕ → ℕ → A
```

and define the zero-based corner / first differences / mixed difference by

```lean
c      : A := D 0 0
α (r)  : A := D (r + 1) 0 - D r 0
β (s)  : A := D 0 (s + 1) - D 0 s
K r s  : A := D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s
```

The target theorem should be a clean exact identity of the form

```lean
D m n
  =
    c
    + ∑ r in Finset.range m, α r
    + ∑ s in Finset.range n, β s
    + ∑ r in Finset.range m, ∑ s in Finset.range n, K r s
```

for all `m n : ℕ`.

You may package `c`, `α`, `β`, `K` either as local `let` definitions inside
the theorem or as separate definitions if that makes the final Lean cleaner.

## Preferred theorem target

Something close to:

```lean
theorem po3_double_telescoping_zero_based
    {A : Type*} [AddCommGroup A]
    (D : ℕ → ℕ → A) (m n : ℕ) :
    D m n =
      D 0 0
        + ∑ r in Finset.range m, (D (r + 1) 0 - D r 0)
        + ∑ s in Finset.range n, (D 0 (s + 1) - D 0 s)
        + ∑ r in Finset.range m,
            ∑ s in Finset.range n,
              (D (r + 1) (s + 1) - D (r + 1) s - D r (s + 1) + D r s)
```

If you find a cleaner equivalent shape, that is fine, as long as the theorem is
exact and directly usable later.

## Optional step-ahead corollary

If convenient, also provide a shifted version for a tail defect:

```lean
theorem po3_double_telescoping_shifted
    {A : Type*} [AddCommGroup A]
    (D : ℕ → ℕ → A) (N m n : ℕ) :
    D (m + N + 1) (n + N + 1)
      = ...
```

where the right-hand side uses the corresponding corner / row / column / mixed
differences based at `N + 1`.

This corollary is optional. The zero-based theorem is the main target.

## Proof strategy preference

The expected proof is elementary:

1. telescope in the first variable,
2. telescope the base row in the second variable,
3. telescope the first-variable increment again in the second variable,
4. rearrange finite sums.

Please keep the proof short and explicit.

## Policy

- Keep the theorem small and standalone.
- Do not introduce manuscript-specific constants.
- Do not mix this with RKHS or A3_FLOOR material.
- `exact?` is acceptable if it helps close a local step, but explicit final code
  is preferred when stable.

## Desired output

Please provide:

1. the exact Lean theorem statement,
2. a short proof sketch,
3. Lean 4 code for the theorem,
4. if the shifted corollary is easy, include it too.
