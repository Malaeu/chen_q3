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
| finite shifted-Gamma transport family `\prod \Gamma(\alpha_j-iz)^{-u_j}\prod \Gamma(\beta_\ell+iz)^{-v_\ell}` | killed as `PO2` subroute family | upper and lower `|t|\log|t|` coefficients have opposite sign, controlled by the imbalance `U-V`; if balanced, the transport drops to at most `O(t)` and cannot cancel the `(\pi/a)|t|\log|t|` growth of `H_a` | structured `\xi`-regularizer boundary pattern for `H_a` | remaining `PO2` wall: `Y_a`-specific sparse-lattice exclusion or a genuinely non-Gamma two-sided transport / uniqueness theorem |
| naive direct De Micheli--Viano application after translating the tail to positive half-integers | killed as routine `PO2` subroute | the cited theorem packet is written for one simple pole in `\Re z>0`, with only a finite-pole extension indicated by the authors; our normalized receiver `R_N(z)=R(z+N+1/2)` has a countably infinite simple-pole set `Y_a=\{x_\gamma,x_\gamma-1\}` shifted by `N+1/2`, so the bridge is not a routine Carlson-class check | minimal shift receiver `R(m)=0` on the tail | next live branch: either prove an infinite-pole extension for the `\ell^1` simple-Cauchy class, or return to the direct structured shift-uniqueness theorem |
| `D3c` compactness extraction of a nonzero one-sided limit from the normalized direct divisor tower | killed as `PO2` subroute | on an infinite-support counterexample, any normalization with uniform `\ell^1` coefficient control forces every fixed packet coefficient to tend to `0` by the Gamma-growth comparison `\prod_{j=1}^k(x-N-j)=(-1)^k\Gamma(k+N+1-x)/\Gamma(N+1-x)`; hence the natural tightness/compactness regime cannot produce a nonzero one-sided limit on `X_a` | direct divisor tower split `D2/D3` in the `PO2` note | next live branch: direct paired-support divisor-rigidity `D2`, unless a genuinely new non-`\ell^1` extraction mechanism appears |
| `D3e4` finite-anchor `\ell^2` Gibbs tightness for the normalized direct divisor tower | killed as `PO2` subroute | for any two fixed nonzero support points `y>y'`, the Gibbs weights satisfy `W_k(y)/W_k(y') \sim C(y,y') k^{2(y-y')}` by the same Gamma-product asymptotic; therefore every fixed support point farther to the right eventually dominates every fixed support point to its left, and on any unbounded nonzero support every finite packet `E` satisfies `\nu_k(E)\to 0` | direct divisor tower split `D2/D3` in the `PO2` note | next live branch: direct paired-support divisor-rigidity `D2`, unless a genuinely new noncompact extraction mechanism appears |
| finite-anchor / absolute no-escape for the one-sided transform-side Gamma tower inside `PO3-square.2d` | killed as `PO3-square.2d` subroute | the same Gamma-ratio asymptotic forces every fixed finite packet to lose all absolute mass to farther-right support points on any unbounded support, so absolute-weight tightness cannot be the honest engine of the infinite-support wall | transform-side wall `PO3-square.2d1` | next live branch: signed rightmost-dominance versus mirror suppression, formal shell `PO3-square.2d2` and analytic burden `PO3-square.2d3` |
| generic short-interval `S(T)` literature as a closure tool for `D2g30d` | killed as `PO2` subroute | the live enemy after `D2g29e` is a deterministic logarithmic spike `S(T+u)-S(T-u)\gtrsim \log T` on prescribed windows of radius `u\asymp (\log T)/T^2`; Korolev-type results are existence/omega statements on short intervals, while Selberg/Fujii-style technology is averaged and does not yield a deterministic exclusion theorem on this supertiny mesh | `D2g30c/D2g30d` logarithmic microcluster packet | next live branch: `D2g31` structural reduction to compressed-gap cascade (`D2f3`) or bounded Hermite-captured genuine packet |
| `H-bridge` filtered route through `PO2 -> PO3 -> ... -> H4` | live | `PO2` now hands off in admissible form via `D2g33`; current first proof-critical gate is `PO3`: cross-sign boundary cancellation | n/a | active in `PHASE_MONITOR.md` |

## Current live rollback point

If the current `PO3` attack dies, the rollback target is not “back to H4”.
It is the last real branch point already frozen in `PROJECT_ORCHESTRATOR.md`:

- live branch A: `H-bridge` primary route;
- live branch B: `PSD-pd` fallback certificate backend.

So a true `PO3` route-kill means:

1. record the exact surviving non-cap cross-sign boundary obstruction;
2. mark `H-bridge` as killed in its current theorem shape;
3. rollback to the branch point `H-bridge vs PSD-pd`;
4. activate `PSD-pd` as the main live route.

## Re-entry rule

A killed route can be reopened only if there is a new explicit ingredient that
directly attacks the old kill certificate. “Maybe another basis” or “maybe a
different rank fit” is not enough.
