# Route Kill Registry

Manual companion to the auto proof graph.

Purpose:

- keep a short ledger of route-level dead ends;
- record the exact obstruction that killed a theorem shape;
- prevent silent resurrection of already-killed branches;
- make rollback to the last real branch point explicit.

This file is manual on purpose.
`ACTIVE/graphs/PROOF_GRAPH.md` is auto-oriented around formal dependencies,
while this registry tracks **route-level mathematical kills**.

## Operational rule

When a live route dies, write five things:

1. route / theorem shape that died;
2. exact obstruction or kill criterion;
3. where the kill was recorded;
4. rollback target;
5. next live branch.

## Current route graph status

| Route / theorem shape | Status | Kill / live reason | Rollback target | Next branch / note |
| --- | --- | --- | --- | --- |
| `S-pd` compact scalar route | killed as public mainline | pointwise compact target `W_K(u) >= 0` is not an honest public route once `\Xi_K \neq \varnothing`; see `PROJECT_ORCHESTRATOR.md` gate table | `T0-pd` public cone pivot | `H-bridge` primary route |
| `SF-pd` same-family Rayleigh bridge | killed as public mainline | naive Rayleigh family is too large and would force false broad local positivity; see `PROJECT_ORCHESTRATOR.md` gate table | `packet-Rayleigh-pd` exact identity retained only as background | `H-bridge` primary route |
| `A3-pd` uniform packet-symbol floor on full dense dictionary | killed as theorem shape | collapsing packets destroy any uniform positive floor on the full dense family; see `PROJECT_ORCHESTRATOR.md` gate table | `PSD-pd` certificate backend | `H-bridge` primary route |
| raw identity `w_{rs}(a)=\kappa(a)q_{rs}` | killed as theorem shape | raw Toeplitz-vs-Weil mismatch is structural, with incompatible diagonal behavior; see `PROJECT_ORCHESTRATOR.md` current frontier item 12 | filtered two-sided tail package | `PO2` mixed-block attack |
| shared rank/basis hunt for filtered defect | killed as theorem language | basis/rank stories are diagnostics only, not admissible theorem content in the reset route | `Q_zeta` filtered defect calculus | `PO2` mixed-block attack |
| generic bridge `\ell^1`-Cauchy-tail vanishing `\Rightarrow` tail moments | killed as `PO2` subroute | a half-shifted-lattice / Gamma-ratio mechanism gives a nonzero `\ell^1` simple-Cauchy sum vanishing on all sufficiently large integers, so generic momentization is false and cannot remain on the critical path | actual structured pole geometry `Y_a=\{x_\gamma,x_\gamma-1\}` | remaining first wall: prove a `Y_a`-specific no-counterexample lemma |
| single-Gamma rotated transport `H_a(z)\Gamma(1-iz)^{-k}` | killed as `PO2` subroute | it damps only the upper half of `i\mathbb R`; on the lower half reflection gives `\Gamma(1+t)^{-1}=(\sin \pi t/\pi)\Gamma(-t)`, so the factor blows up like `\exp(k|t|\log|t|)` on generic negative `t`, while the naive symmetric Gamma pair gives only polynomial control | structured `\xi`-regularizer boundary pattern for `H_a` | remaining `PO2` wall: `Y_a`-specific no-counterexample lemma or a genuinely two-sided transport / uniqueness theorem |
| `H-bridge` filtered route through `PO2 -> PO3 -> ... -> H4` | live | current first proof-critical gate is `PO2`: cross-sign bulk exactness | n/a | active in `PHASE_MONITOR.md` |

## Current live rollback point

If the current `PO2` attack dies, the rollback target is not “back to H4”.
It is the last real branch point already frozen in `PROJECT_ORCHESTRATOR.md`:

- live branch A: `H-bridge` primary route;
- live branch B: `PSD-pd` fallback certificate backend.

So a true `PO2` route-kill means:

1. record the exact mixed-block obstruction;
2. mark `H-bridge` as killed in its current theorem shape;
3. rollback to the branch point `H-bridge vs PSD-pd`;
4. activate `PSD-pd` as the main live route.

## Re-entry rule

A killed route can be reopened only if there is a new explicit ingredient that
directly attacks the old kill certificate. “Maybe another basis” or “maybe a
different rank fit” is not enough.
