# Proshka prompt: first `Q_\zeta`-core adapter (2026-03-15)

## Mission

We now have a thin project-level `Q_\zeta`-core:

- it is **not** a third RH route;
- it is the canonical explicit-form / Weil quadratic-operator layer above the
  live routes;
- its two current backends are:
  `H-bridge` as the primary operator backend and
  `PSD-pd` as the strict finite-shadow / certificate backend.

We want you to work on the **first real adapter theorem** inside this core.

## Do not do

Please do **not**:

- propose a new RH architecture;
- restart a rank/basis hunt;
- revive the dead raw identity
  `w_{rs}(a)=\kappa(a)q_{rs}`;
- spend effort on repo bookkeeping, prompt packing, or finite bookkeeping.

Assume the local agent will handle:

- control-plane sync;
- exact formula extraction from notes/manuscript;
- finite compression bookkeeping;
- context assembly and deterministic checks.

Your job is the structural math only.

## Exact target

Work inside the already-frozen filtered geometry:

```tex
\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N},
\qquad
B_{M,N}=S_{a,M,N}^*J_aS_{a,M,N}=\Delta_{M,N}^*\Delta_{M,N}.
```

The live defect is

```tex
D_{a,M,N}
:=
S_{a,M,N}^*G_g[a]S_{a,M,N}
-\kappa(a)\,\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}.
```

The current project belief is:

- `(+,-)` is the stable anchor;
- `(++)` is the only hard family;
- rank/basis stories are diagnostics only;
- the best structural guess is explicit boundary/cap correction with a moving
  Toeplitz-Hankel / commutator / near-edge matrix shadow.

## What we want from you

Please attack the **first `Q_\zeta`-core adapter theorem**:

```tex
M^{+-}(a)=\kappa_{+-}(a)\widetilde Q^{+-}+E_a^{+-},
```

and tell us whether the right theorem shape is:

1. exact filtered identity, i.e. `E_a^{+-}=0`;
2. explicit corrected identity with a transparent boundary/cap term;
3. something weaker but still theorem-grade.

Then tell us how the same-sign block should differ:

```tex
M^{++}(a)-\kappa_{+-}(a)\widetilde Q^{++}
=
H_a^{\mathrm{ss}}+C_a^{\mathrm{cap}}.
```

## Deliverables

Return one compact note with exactly these outputs:

1. A theorem-shape for the first adapter:
   `(+,-)` exact or exact-plus-explicit-correction.
2. A blockwise cancellation table:
   which terms should vanish in `(+,-)` and which survive only in `(++)`.
3. One algebraic starting formula:
   preferably at the infinite-tail level
   `\mathcal D_{a,N}=S_{a,\infty,N}^*G_g[a]S_{a,\infty,N}
   -\kappa(a)\Delta_N^*Q_\infty\Delta_N`.
4. Your best explicit candidate decomposition:
   boundary / commutator / Toeplitz-Hankel / cap.
5. A kill list:
   which current sub-thoughts should be abandoned immediately.

## Preferred style

Please prefer:

- explicit operator identities;
- sign-sensitive explanations (`(+,-)` versus `(++)`);
- formulas stable under `M`;
- theorem content, not numerical fitting language.

## One-sentence summary

We are not asking for a new route; we are asking for the first theorem-grade
adapter that turns the current `Q_\zeta`-core from coordination language into
actual mathematics.
