# Sub-agent request: isolate the `Herglotz/Bochner` route for `PSD-pd`

## Goal

Do **not** try to prove RH, and do **not** revive the rejected broad-cone or
uniform-gap routes.

The live blocker is the corrected theorem:

```text
PSD-pd: prove that for every finite pre-packet family {g_i} in the dense
packet space, the matrix
  [K_Q(g_i,g_j)]_{i,j}
with
  K_Q(g_i,g_j) := Q^\star(t; g_i * \widetilde{g_j})
is positive semidefinite.
```

Your task is to isolate the **Herglotz/Bochner** version of this route as a
small exact theorem package.

## Exact target

Return one clean theorem stack that would reduce `PSD-pd` to a positive-definite
sequence / measure representation.

The package must include:

1. one exact main theorem statement for the route;
2. 2-4 helper lemmas in a sensible dependency order;
3. a short proof skeleton explaining why the package implies PSD of every
   finite Toeplitz section `[K_Q(g_i,g_j)]`;
4. the first genuinely blocked local lemma if the whole package is still too
   large.

## Real local context

The corrected packet side in the current Q3 manuscript is:

```text
Psi_c(x) := sum_{j=-M}^M c_j g(x - j Δ)
h := g * \widetilde g
kappa_m := Q^\star(t; h(· - mΔ))
K_Q(g_i,g_j) := Q^\star(t; g_i * \widetilde{g_j})
```

and the exact packet-Rayleigh identity already recorded in the draft is:

```text
Q^\star(t; Psi_c * \widetilde{Psi_c})
  = sum_{i,j=-M}^M kappa_{i-j} c_i \overline{c_j}.
```

So the live mathematical question is:

```text
when can one show that the sequence (kappa_m) is positive-definite
in the Herglotz/Bochner sense, hence all finite Toeplitz sections are PSD?
```

## Constraints

- Stay strictly inside the corrected positive-definite route.
- Do not widen the target to positivity on all even compactly supported bumps.
- Do not resurrect:
  - the old shifted `A1'` mainline,
  - the naive family `Phi_{B,t} |p|^2` as a dense closure family,
  - any theorem shape with one uniform positive gap on the dense packet family.
- No `sorry` or `admit`.
- `exact?` is acceptable only if it closes a small local algebraic step and the
  resulting statement is still honest.

## Preferred deliverable style

Prefer one of the following:

1. a Lean-oriented theorem package with exact theorem statements, or
2. a math note with exact statement names and theorem text that can be moved
   into `Main_closure.tex` / `INSIGHTS.md` without ambiguity.

If you cannot give the full package, return only the **first blocked local
lemma** and explain exactly why it is the next honest target.

## Guidance

The live route should look like some variant of:

```text
representation of (kappa_m) as Fourier coefficients of a positive measure
=> every finite Toeplitz section [kappa_{i-j}] is PSD
=> PSD-pd on the exact dense pre-packet family.
```

The answer is useful only if it stays narrow and exact.
