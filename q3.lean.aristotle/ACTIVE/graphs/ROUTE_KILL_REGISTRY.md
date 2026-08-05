# Route Kill Registry

> **FROZEN 2026-08-05 — migrated to `knowledge.db`.**
> All 15 table rows and the live `PO3-square.2d3` criterion now live in
> `q3.lean.aristotle/aristotle_db/knowledge.db` (table `kill`, `unit_type` in
> `route`/`criterion`). Query with `./orchestrator/kb.py search <term>`;
> record new kills with `./orchestrator/kb.py add`, **not** by editing this file.
> Kept read-only for provenance; `./orchestrator/kb.py census` compares it against the DB.

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
| `G6·S2` fixed Müntz window installed as canonical `Pstar` | killed as theorem shape (Proshka verdict 2026-08-05, `KILL_FIXED_WINDOW_MUNTZ_AS_CANONICAL_PSTAR_SURROGATE`) | `Pstar` is already source-locked to `centeredPstarFamily D.kTrial` (`D0CanonicalApproximation.lean`), built from the finite D0 coefficient row over the source prolate trial `hTrial_m`. The free `Pstar` field of `CanonicalApproximation` is **interface polymorphism, not an inheritance mechanism**: instantiating a new `C` resets every roof premise (H2a, `Theorem510RealZeroBridge`, anchor, S1, Montel, same-parent cofinality) and inherits none of them. Choosing PL2 *after* inspecting the Mellin-zero discriminator is a post-hoc object switch — C09 precommit failure + C10 surrogate failure, with a C04 same-coordinates/two-laws warning | D0 canonical family `centeredPstarFamily D.kTrial` on the existing cofinal `(m,N)` path (nothing to roll back: the canonical route was never left) | `G6_S2_D0_SELECTED_FAMILY_MUNTZ_SAME_FAMILY_CROSSWALK` — prove the existing D0 selected family admits the source Müntz representation on the same cofinal path, retaining finite-`N` Galerkin error, normalization, coordinate/phase and H2b provenance. Kill order: 0 same-family/H2b provenance → 1 anchor sanity → 2 uniform `Rminus` for `hTrial_{m_k}` → 3 `Rplus` scale → 4 assembly. Survivors kept: `S2GaugeNonvanishing.lean` (generic in `C`), the 1468-window scan as `FIXED_WINDOW_S2_NONVANISHING_OBSTRUCTION_NOT_UNIVERSAL`, PL2 as ratified falsifier |

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

## Live kill criterion under watch

This is not a killed route yet.  It is the current `PO3-square.2d3` test that
would kill the unconditional endpoint-row absolute-mass route if realized.

Route / theorem shape:

- `PO3-square.2d3.absolute-row-mass-control` as an unconditional consequence
  of only `Y_a={x_gamma,x_gamma-1}` and `|c_gamma|=O(gamma^-3)`.

Exact obstruction:

- a required endpoint row `rho`, a subsequence `k_n`, and exterior support
  points `y_{k_n}\in Y_a\setminus P_{k_n}` such that
  `Lambda_{k_n}(xi_{k_n})(y_{k_n}-xi_{k_n})` stays bounded while
  `|c_{y_{k_n}} A_{I_{k_n,rho}}(y_{k_n})|`
  remains comparable to `M_{k_n}|m_{k_n,rho}(xi_{k_n})|`.

If this occurs, the selected endpoint-adaptive packet is not exhaustive and
Hermite/Vandermonde residue capture cannot be used at this node.  The current
live branch is therefore the conditional theorem
`EndpointRowAbsoluteMassControl_from_packet_isolation`: prove exhaustive
packet isolation, or promote the obstruction above to a route kill.

Sharper split:

- the unconditional `o(D_{k,rho})` absolute-mass route is not the next target;
  zero counting plus `|c_gamma|=O(gamma^-3)` gives only a log-loss row-mass
  bound;
- `MirrorRowSmall` should be pursued through
  `EndpointRowLogMassMirrorControl`, requiring
  `eta_{k,rho} log(2+xi_k)->0` plus far mirror-tail control;
- the remaining kill criterion is `RowClusterExhaustion`: kill the fixed
  finite Vandermonde packet route if there is either one omitted
  bounded-local-coordinate exterior competitor with comparable row
  contribution, or an unbounded number of comparable row-scale support points
  outside the selected finite packet.

Latest correction:

- fixed finite `RowClusterExhaustion` is no longer the active unconditional
  theorem shape.  The active row-error target is
  `ThresholdExhaustivePacketRowError`: choose `delta_k` with
  `delta_k log(2+xi_k)->0` and include every row-effective point with
  normalized endpoint-row contribution at least `delta_k` of the row scale;
- this threshold packet closes the omitted row-effective `A`-mass by the
  `O(log xi_k)` zero-counting bound, but it may have variable size;
- the new live kill criterion is `VariableComparablePacketCapture`: kill the
  fixed finite Vandermonde route if every admissible threshold gives
  `|P_k(delta_k)|->infty`, or if the endpoint-row matrix for the threshold
  packet is too ill-conditioned, i.e.
  `sigma_min^+(V_k)` fails to dominate the normalized row error
  `max_p |epsilon_{k,rho_p}|`;
- if the threshold packet is bounded and separated, the existing finite
  Vandermonde/Hermite branch remains the next consumer.

Stable-projection refinement:

- the variable-packet consumer is now frozen as
  `po3_variable_comparable_packet_capture_of_stable_projection`;
- the live route survives if the selected endpoint rows provide a projection
  onto the expected Vandermonde/Hermite kernel with
  `||q-Proj q|| <= C_k ||V_k q||` and `C_k ||epsilon_k|| -> 0`;
- kill this capture branch if the packet matrix has the wrong kernel
  dimension, if the kernel is not the expected Vandermonde/Hermite line, or if
  the conditioning loses to the row error;
- in row-sup norm bookkeeping, the kill criterion must include the
  `sqrt(r_k)` loss unless the stability theorem is stated in a compatible
  `ell_infty` norm.

Bounded-separated branch:

- the active surviving branch is
  `EndpointRowsStableProjection_boundedSeparated`: bounded threshold packet,
  separated exponential local nodes, endpoint-row convergence to the
  rectangular Vandermonde block, and compactness of the corresponding
  nonzero singular gap;
- kill the current finite/Hermite capture step if the threshold packets are
  necessarily growing and no quantitative singular-gap theorem is available;
- kill the bounded-separated branch if no subsequence has separated
  exponential nodes, or if the real endpoint rows fail to converge to the
  expected `z_i^p` row model;
- clustered bounded packets are not killed immediately, but they require a
  separate confluent/Hermite renormalization and proof that amplified row
  errors still tend to zero.

Orientation-safe endpoint-row limit:

- do not kill the route merely because the right-edge later-base row gives
  `exp(+p t)` instead of `exp(-p t)`;
- the safe theorem uses `exp(-alpha_p t)`, with `alpha_p` determined by
  `Theta_{k,p}/Lambda_k`;
- record a route-kill only if the required endpoint rows fail the local tube,
  theta-slope, or second-order smallness hypotheses, or if a right-edge proof
  incorrectly requires earlier-base lower extensions unavailable from the
  frozen wall identity.

Endpoint orientation split:

- the right-edge later-base lower-truncation branch is not killed by the sign
  change; it should use fractional exponents `0<=beta<=1` and generalized
  Vandermonde rows `exp(beta t_i)`;
- kill only the false right-edge integer-row theorem shape asking for
  `alpha=-p` with integer `p>1`, because lower truncation can remove at most
  one full long-side logarithmic slope;
- left-edge upper extension remains valid for arbitrary fixed integer rows
  `p>=0`, subject to the endpoint-row product-asymptotic estimates.

Fractional right-edge Vandermonde condition:

- with `beta_j=j/(n-1)`, the right-edge row matrix is ordinary Vandermonde in
  `y_i=exp(t_i/(n-1))`;
- bounded-separated right-edge capture requires separation of these actual
  fractional nodes;
- route-kill the bounded-separated right-edge branch if the fractional nodes
  collapse and no confluent/Hermite stable projection replacement is supplied;
- separation in a different coordinate, such as only `exp(-t_i)`, is not the
  canonical certificate unless it is explicitly shown to imply separation of
  `exp(t_i/(n-1))` on the active compact set.

Stable adaptive shifts reconciliation:

- generic future-slope-adapted shifts are a support packet, not a new escape
  from the orientation-safe/fractional endpoint-row pipeline;
- after stable rows are selected, the live kill criterion is row-error
  conditioning: kill the capture branch if the normalized shifted errors do
  not satisfy `C_k ||epsilon_k|| -> 0`;
- if only component row errors are controlled, include the
  `sqrt(r_k) max_rho |epsilon_{k,rho}|` loss before comparing to the stable
  projection constant.

## Re-entry rule

A killed route can be reopened only if there is a new explicit ingredient that
directly attacks the old kill certificate. “Maybe another basis” or “maybe a
different rank fit” is not enough.
