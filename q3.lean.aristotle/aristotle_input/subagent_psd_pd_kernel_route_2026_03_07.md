# Sub-agent request: isolate the `prime-factorization / kernel` route for `PSD-pd`

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

Your task is to isolate the **prime-factorization / kernel** version of this
route as a small exact theorem package.

## Exact target

Return one clean theorem stack that would prove `PSD-pd` directly from a
decomposition of the packet kernel into Archimedean and prime pieces on the
same exact dense pre-packet family.

The package must include:

1. one exact main theorem statement for the route;
2. 2-5 helper lemmas in a sensible dependency order;
3. a short proof skeleton explaining how the Archimedean and prime pieces are
   controlled to yield PSD of every finite matrix `[K_Q(g_i,g_j)]`;
4. the first genuinely blocked local lemma if the full package is still too
   large.

## Real local context

The current corrected packet side in Q3 is:

```text
Psi_c(x) := sum_{j=-M}^M c_j g(x - j Δ)
h := g * \widetilde g
kappa_m := Q^\star(t; h(· - mΔ))
K_Q(g_i,g_j) := Q^\star(t; g_i * \widetilde{g_j})
```

and the manuscript already records the packet-symbol decomposition:

```text
kappa_m
  = ∫ a(ξ) h(ξ - mΔ) dξ
    - sum_n w(n) h(ξ_n - mΔ)

S_{g,Δ}(θ) = A_{g,Δ}(θ) - P_{g,Δ}(θ).
```

The old centered A3/RKHS machinery controls a different object:
one centered window with a special Toeplitz/Rayleigh package.
Your task is **not** to reuse that theorem by wishful analogy, but to say what
new kernel-level theorem package would be required on the packet side.

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
exact kernel decomposition on the packet family
=> Archimedean PSD contribution + prime-side factorization/control
=> PSD of the full packet kernel
=> PSD-pd on the exact dense pre-packet family.
```

The answer is useful only if it stays narrow and exact.
