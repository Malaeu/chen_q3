# PROJECT ORCHESTRATOR - Q3

Updated: 2026-03-08

## Role

This file is the single source of truth for:

- gate-state,
- current frontier,
- active milestone,
- hard blockers,
- decision ledger.

It is **not** a session log and **not** a microtask queue.

## Mainline Chain

`T0-pd -> H-bridge -> H4 -> RH`

- `T0-pd`: Guinand--Weil crosswalk with the corrected positive-definite target cone.
- `corrected cone`: local/global positive-definite Weil cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- `H-bridge`: Suzuki/Yoshida generalized form-pair bridge
  `H1^f -> H2^f -> H3^f -> H4^f`.
- `H4`: Suzuki Theorem 1.4 endpoint
  `0 \notin \sigma_p(G_g[a])` for every `a>0`.

Fallback corrected-cone route:

- `A1-pd`: density of the centered autocorrelation family
  `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.
- `packet-Rayleigh-pd`: exact finite Toeplitz quadratic-form identity on the
  same autocorrelation packet family `\Psi * \widetilde\Psi`.
- `PSD-pd`: positive semidefiniteness of the packet kernel
  `K_Q(g_i,g_j):=\mathcal Q(g_i * \widetilde{g_j})` on that same dense
  pre-packet space.
- `A2 closure`: continuity transfer on the corrected local cone.
- `LF-pd`: inductive-limit lift from all `\mathcal W_K^{pd}` to `\mathcal W^{pd}`.
- `G6`: Weil linkage from positivity on `\mathcal W^{pd}` to RH.

Broad-cone route status:

- old `W_K / \mathcal W` route is now **background only**;
- it may still produce reusable local lemmas,
- but it is no longer the public RH contract.

## Precedence Rule

If files disagree, resolve conflicts in this order:

1. `PROJECT_ORCHESTRATOR.md`
2. `docs/PAPER_MAINLINE_TRACKER.md`
3. `IMPLEMENTATION_PLAN.md`
4. `docs/INSIGHTS.md`

Interpretation:

- `PROJECT_ORCHESTRATOR.md` decides gate-state and frontier.
- `docs/PAPER_MAINLINE_TRACKER.md` decides manuscript typing and dependency map.
- `IMPLEMENTATION_PLAN.md` decides only the current execution queue.
- `docs/INSIGHTS.md` is non-normative and never overrides the other three.

## Current Compiled Route

Compiled Lean route still exported today:

`Q3.Main -> Q3.RH_of_shifted_atom_route -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`

Current `#print axioms Q3.Main.RH_of_Weil_and_Q3`:

- standard: `propext`, `Classical.choice`, `Quot.sound`
- project/classical: `Q3.Weil_criterion`
- project/scalar placeholder: `Q3.prime_term_le_at_t_critical_axiom`

Interpretation after `T0.1`:

- this route is structurally useful,
- it remains compiled to preserve local theorem payloads,
- but it is a **background broad-cone export**, not the public mainline contract.

## Gate Table

| Gate | Meaning | Status | Exit criterion |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk | `done` | normalization remains locked |
| `T0.1` | target-cone audit | `done` | one binary verdict written: `pivot required` |
| `T0-pd` | corrected public target cone | `done` | control docs + manuscript use the positive-definite cone as the public RH target |
| `S-pd` | scalar compact spectral route `W_K(u)\ge0` | `rejected as public mainline route` | retained only as a correct diagnostic compact-truncation package `S1/S2/S3/S4`; rejected because `a_K^*\in L^1` forces `\widehat{a_K^*}(u)\to0` while the finite cosine prime sum recurs near its full positive mass whenever `\Xi_K\neq\varnothing` |
| `A1-pd` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | `frozen theorem block` | pre-square density route + autocorrelation continuity prove `\overline{\mathcal G_K^{pd}}=\mathcal W_K^{pd}` |
| `packet-Rayleigh-naive` | naive quadratic-form bridge on `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` | `background candidate` | keep only as an auxiliary identity; do not reuse it as the public closure family |
| `SF-pd` | same-family bridge through `\mathcal G_{K,\mathrm{Ray}}^{pd}` | `rejected as mainline route` | rejected because the naive Rayleigh family is too large and would force false broad local positivity |
| `packet-Rayleigh-pd` | exact Toeplitz form on autocorrelation packets `\Psi_c * \widetilde{\Psi_c}` | `frozen theorem block` | identify `\mathcal Q(\Psi_c * \widetilde{\Psi_c})` with the finite symbol integral `\frac{1}{2\pi}\int S_J(\theta)|p_c(\theta)|^2\,d\theta` on each admissible dictionary |
| `A3-pd` | uniform packet-symbol floor on the dense packet family | `rejected as theorem shape` | rejected because dense packet dictionaries admit collapsing packets `\Psi_\Delta`, so no uniform `c_K>0` can hold on the full family |
| `PSD-pd` | PSD of the packet kernel `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | `fallback constructive route` | finite-dictionary positivity via explicit coefficient bounds on `\alpha_m,\beta_m`, yielding `S_J=A_J-P_J\ge0` on each admissible block |
| `H-bridge` | Suzuki/Yoshida generalized form-pair bridge `(G_g[a],J_a)` from Q3 finite sections to the RH-equivalent operator criterion | `active primary live route` | freeze the two-sided filtered tail package `\mathcal P_{M,N}, \Delta_{M,N}, B_{M,N}, \widetilde Q_{M,N}` and close `H1^f -> H2^f -> H3^f -> H4^f` |
| `centered A3/RKHS` | positivity engine on centered packets | `done as analytic input` | supplies the model estimates that must be upgraded to packet-kernel positivity |
| `A2-pd` | continuity on the corrected local cone | `done as inherited input` | continuity explicitly restricted to `\mathcal W_K^{pd}` in the paper contract |
| `LF-pd` | LF lift on `\mathcal W^{pd}` | `blocked` | local positivity on every `\mathcal W_K^{pd}` is available |
| `G6` | Weil linkage to RH | `frozen` | available once positivity on `\mathcal W^{pd}` is honest |

## Current Frontier

- `T0.1` is closed with verdict `pivot required`.
- The broad target cone `W_K / \mathcal W` is too wide for the honest Weil interface.
- Current `G1.6` Aristotle work stays background only. It may still land local support lemmas,
  but it no longer determines the architectural frontier.
New live frontier:
  1. promote the Suzuki/Yoshida generalized form-pair bridge to the primary
     live route in its final filtered-tail form:
     `H1^f` exact filtered bulk intertwining
     -> `H2^f` Suzuki tail/cap reduction
     -> `H3^f` filtered gap transfer
     -> `H4^f` RH via Suzuki Theorem 1.4;
     the active finite object is now
     `\widetilde Q_{M,N}:=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`
     on the two-sided tail space `\mathcal P_{M,N}`,
     with exact metric pullback
     `S_{a,M,N}^*J_aS_{a,M,N}=B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`;
  2. freeze the compact scalar package `S1/S2/S3/S4` only as a correct
     diagnostic reduction, and reject its pointwise target `W_K(u)\ge0` as a
     public compact mainline whenever `\Xi_K\neq\varnothing`;
  3. treat the finite-dictionary packet package only as fallback discretization /
     verification after the scalar-route obstruction;
  4. keep `A1-pd` frozen as the dense corrected-cone input on `\mathcal G_K^{pd}`;
  4. keep the naive Rayleigh family
     `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}`
     background-only after the local-bump obstruction;
  5. freeze exact packet-Rayleigh on autocorrelation packets
     `\Psi_c * \widetilde{\Psi_c}`;
  6. reject `A3-pd` in the old uniform-gap sense on the dense packet dictionary;
  7. reject the literal `Route P` theorem shape
     `prime-block PSD factorization or Hilbert lift -> Archimedean domination`
     on packet space;
  8. keep `Herglotz/Bochner` as the clean diagnostic equivalence route;
 9. freeze the strict `P1--P8` theorem package as the fallback packet route;
10. keep finite admissible dictionary positivity as the immediate fallback constructive target:
     exact finite symbol `S_J(\theta)=A_J(\theta)-P_J(\theta)`,
     explicit coefficient bounds on `\alpha_m,\beta_m`,
     Poisson-regularized verification, and explicit error budget,
     with a new full-kernel operator package kept as fallback;
11. keep Gershgorin only as a sparse finite-block lemma, not as the dense theorem.
  12. move the active blocker away from the already-frozen theorem package `S1/S2/S3/S4`
     to the raw-entry reduction of the exact two-sided filtered bulk match:
     freeze the raw Section 8 operator
     `Q_M^{raw}=T_M[P_A]-\Pi_M`,
     `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
     and the exact raw entries
     `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle
      = A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
     `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
     with Q3-side normalization fixed by `\kappa_{A3}=1`,
     and
     `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`,
     and keep the raw identity
     `w_{rs}(a)=\kappa(a)q_{rs}`
     only as a diagnostic mismatch layer:
     the raw Q3 matrix is Toeplitz with constant diagonal while the Suzuki raw
     Weil matrix in the `\chi_n[a]` basis has diagonal growth of order
     `\log|n|`;
     the live bulk target is therefore the direct filtered match on the two
     families `(+,+)` and `(+,-)`;
  13. isolate the finite-dimensional Suzuki cap as the second and only other
     live brick after the bulk match:
     positivity of the cap matrix is a separate finite-dimensional problem.

## Active Milestone

Turn the strongest reusable finite Q3 block into a proof-ready Suzuki bridge:

1. keep `\mathcal W_K^{pd}` and `\mathcal W^{pd}` fixed in control docs and manuscript,
2. freeze the compact scalar package `S1/S2/S3/S4` only as a rejected public
   compact-truncation route and diagnostic formal reduction,
3. make the theorem stack
   `H1^f exact filtered bulk intertwining -> H2^f Suzuki tail/cap reduction -> H3^f filtered gap transfer -> H4^f Suzuki Theorem 1.4`
   the primary live route,
4. freeze the symmetric two-sided filtered tail package as the exact
   preferred `H1^f` geometry:
   `\mathcal P_{M,N}`, `\Delta_{M,N}`, `\phi_n^\pm[a]`, `S_{a,M,N}`,
   `B_{M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
   `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`,
4a. strongest current engineering refinement of `H1`:
    keep the finite-prime semilocal layer only as a basis/Gram engine,
    with packet states `\eta_m^{(S,a)}`, semilocal spaces `E_{a,M}^{(S)}`,
    Gram matrix `\Gamma_{a,M}^{(S)}`, and normalized synthesis
    `\widetilde S_{a,M}^{(S)}` feeding the same Suzuki pair-intertwining target,
4b. preferred first-pass refinement of `H1^f`:
    use the symmetric filtered Volterra bridge
    `J_a=(I_0^{(a)})^*I_0^{(a)}`,
    with `1+z` on the positive tail and `1+z^{-1}` on the negative tail,
    so that the exact pullback metric is
    `B_{M,N}=S_{a,M,N}^*J_aS_{a,M,N}=\Delta_{M,N}^*\Delta_{M,N}`,
    and the exact finite comparison object is
    `\widetilde Q_{M,N}=\Delta_{M,N}^*Q_{M+1}\Delta_{M,N}`,
4c. current implementation brick inside `H1^f`:
    the raw entry formula is now extracted in the raw-compressed notation:
    `Q_M^{raw}=T_M[P_A]-\Pi_M`,
    `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
    and
    `q_{rs}=\langle Q_M^{raw}e_s,e_r\rangle
     = A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
    `\lambda_n=(2\Lambda(n)/\sqrt n)\Phi_{B,t}(\xi_n)`,
    with `\kappa_{A3}=1`;
    in the filtered bridge the ambient raw finite block is
    `Q_{M+1}^{raw}`,
    and
    `w_{rs}(a)=W(\chi_s[a]*\widetilde{\chi_r[a]})`,
    then keep the raw identity
    `w_{rs}(a)=\kappa(a)q_{rs}`
    only as a rejected diagnostic theorem shape;
    the active work is no longer plain exact equality, but the filtered bulk
    classifier on the two primary families:
    `M_{mn}^{++}(a)=\kappa(a)\widetilde q_{mn}^{++}+F_a^{++}` and
    `M_{mn}^{+-}(a)=\kappa(a)\widetilde q_{mn}^{+-}+F_a^{+-}`,
    with diagnostic outcomes
    `exact / exact+structured small-rank correction / dead`;
    current executable checks strongly favor the middle class:
    in the canonical run `a=1.25, M=4, zeros=20`,
    the `++` residual has rank-2 relative residual `~6.32e-3` and the `+-`
    residual has rank-2 relative residual `~1.99e-3`,
    while low-mode support tests remain large and therefore do not support a
    pure low-mode-only defect,
    with the remaining filtered blocks
    `(-+), (--)`
    becoming formal consequences of Hermitian symmetry,
5. keep `A1-pd` frozen on the dense autocorrelation packet family `\mathcal G_K^{pd}` as auxiliary/fallback infrastructure,
5. keep exact packet-Rayleigh frozen on `\Psi_c * \widetilde{\Psi_c}`,
6. keep the naive centered Rayleigh family
   `\mathcal G_{K,\mathrm{Ray}}^{pd}` background-only after the obstruction,
7. keep the packet-symbol decomposition
   `S_{g,\Delta}=A_{g,\Delta}-P_{g,\Delta}` only as fallback packet notation,
8. reject the old `A3-pd` uniform-floor route on the dense packet family,
9. reject the literal `Route P` theorem shape
   `prime-block PSD factorization or Hilbert lift -> Archimedean domination`,
10. make `PSD-pd` explicit as the fallback packet-kernel theorem
   `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense
   translation-compatible packet subspace,
11. freeze the strict `P1--P8` chain:
   exact packet sesquilinear identity
   -> Toeplitz reduction
   -> desired prime-factorization (rejected by obstruction)
   -> full sequence split `\kappa=\alpha-\beta`
   -> Toeplitz/Herglotz criterion
   -> finite-dictionary `P7` package
   -> `PSD-pd`,
12. record the two surviving strategy families under the fallback packet route
    (Herglotz/Bochner versus direct full-kernel PSD),
13. keep the finite-dictionary `P7` package as the immediate fallback constructive target:
    `S_J=A_J-P_J\ge0` on each admissible packet block, driven by explicit
    coefficient bounds on `\alpha_m,\beta_m`, with Poisson-regularized finite
    symbols retained as verification device and a new full-kernel operator
    package as fallback,
14. keep Gershgorin only as a sparse finite-block lemma and not as the dense
    public theorem,
15. freeze the canonical centered half-atom
    `g_{δ,t_0,0}=\Lambda_\delta\rho_{t_0}` as the first pilot packet,
    together with the compact test case `K=0.2`, `J={0,1}`, `Δ=0.15`,
    where prime collisions vanish and the finite symbol reduces to the
    Archimedean gap `\alpha_0>2|\alpha_1|`,
16. keep `Herglotz/Bochner` as the secondary diagnostic / equivalence route,
17. keep Aristotle `G1.6` as background lemma-mining only,
18. make the next honest theorem task explicit at the matrix-element level:
    compare the four filtered tail blocks
    `(++), (+-), (-+), (--)`
    of
    `[ \langle G_g[a]\phi_n^\sigma[a],\phi_m^\tau[a]\rangle ]`
    with the corresponding blocks of `\kappa(a)\widetilde Q_{M,N}`,
19. keep the Suzuki generalized form-pair package
    `H1^f -> H2^f -> H3^f -> H4^f` frozen as the strongest alternative operator route,
    with `H1^f` exact filtered bulk intertwining as the only real missing
    bridge theorem; the second and only other live brick after that is the
    finite-dimensional Suzuki cap.

## Hard Blockers

- `A1'` is a density theorem on the broad restriction cone `R_K`; it does not feed
  the corrected positive-definite mainline directly.
- No proof yet closes the pre-square density route that would prove `A1-pd`.
- The naive Rayleigh family `\mathcal G_{K,\mathrm{Ray}}^{pd}` is too large to serve
  as the mainline closure family: on compacts `K<\pi` it would combine with the full
  quadratic-form meaning of Lemma 8.8 and A3 positivity to force false broad local
  positivity on even nonnegative bumps.
- Exact packet-Rayleigh on autocorrelation packets is now the honest theorem shape,
  but no proof yet establishes positive semidefiniteness of the associated packet
  kernel `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on the same dense
  pre-packet space.
- `Herglotz/Bochner` explains what `PSD-pd` means, but it does not yet provide a
  project-local constructive proof.
- The literal packet-level `prime-block PSD factorization or Hilbert lift`
  theorem shape is false on dense packet spaces: the packet prime block is not
  positive semidefinite in general.
- The compact scalar package
  `S1 exact compact spectral identity -> S2 scalar compact criterion -> S3 corrected compact positivity -> S4 corrected global closure`
  is mathematically correct as a compact-truncation reduction, but it is no longer
  a viable public mainline once `\Xi_K\neq\varnothing`: `a_K^*\in L^1` implies
  `\widehat{a_K^*}(u)\to0`, while the finite cosine prime sum recurs arbitrarily
  close to its full positive mass.
- The primary remaining theorem package is now:
  `H1^f` exact filtered bulk intertwining
  -> `H2^f` Suzuki tail/cap reduction
  -> `H3^f` filtered gap transfer
  -> `H4^f` Suzuki Theorem 1.4;
  the fallback packet package remains:
  exact packet sesquilinear identity
  -> prime-block obstruction
  -> Toeplitz/Herglotz spectral criterion for the full sequence
  -> finite admissible dictionary positivity
     `S_J(\theta)=A_J(\theta)-P_J(\theta)\ge0`
     driven by explicit bounds on `\alpha_m,\beta_m`
     and verified through Poisson-regularized finite symbols / explicit error budget
     (with measure-level/full-symbol language retained only as secondary diagnostic notation)
     or a new operator package for the full kernel
  -> `PSD-pd`.
- The Suzuki/Yoshida generalized form-pair bridge is now the strongest live route:
  `H1^f` exact filtered bulk intertwining
  -> `H2^f` Suzuki tail/cap reduction
  -> `H3^f` filtered gap transfer
  -> `H4^f` RH via Suzuki Theorem 1.4.
  Until `H1^f` is concretely built, the route remains incomplete, but it is now
  the primary live frontier.
- The canonical centered half-atom pilot already shows that this finite-symbol
  criterion is genuinely nonvacuous on sparse compact dictionaries, while still
  falling far short of dense closure.
- On dense packet dictionaries with arbitrarily fine translates, a uniform lower
  bound of the form `Q^\star(t;\Psi * \widetilde\Psi)\ge c_K\|c\|_2^2` is impossible:
  packets `\Psi_\Delta=g-g(\cdot-\Delta)` collapse to zero and force
  `Q^\star(t;\Psi_\Delta * \widetilde{\Psi_\Delta})\to0` by A2 continuity.
- The broad-cone compiled route in Lean still exists and may generate useful local
  lemmas, but it cannot be used as public evidence for RH after `T0.1`.
- The compiled Lean route still inherits `Q3.prime_term_le_at_t_critical_axiom`.

## Read-Only Support Docs

These files may be updated as snapshots, but they are no longer part of the active control plane:

- `docs/CHAIN_STATUS.md`
- `ACTIVE/MAIN_CHAIN_DEPS.md`

Legacy narrative surfaces are reference-only:

- centered/T5 route,
- Acceptance Gate material,
- `τ = 0` / PrimeCert / PathB status narratives,
- archived D3/IND/AB branches.

## Decision Ledger

- 2026-03-06: active compiled route reset from legacy `τ = 0` narrative to shifted-atom route.
- 2026-03-07: same-repo reset chosen; no new physical repo.
- 2026-03-07: control plane fixed to 4 canonical files:
  `PROJECT_ORCHESTRATOR.md`,
  `IMPLEMENTATION_PLAN.md`,
  `docs/PAPER_MAINLINE_TRACKER.md`,
  `docs/INSIGHTS.md`.
- 2026-03-07: gate chain fixed as
  `T0 -> G0 -> G1 -> G2 -> G3 -> G4 -> G5 -> G6 -> RH`.
- 2026-03-07: `G2` and `G3` split cleanly:
  `G2` chooses and freezes `G_K`,
  `G3` proves positivity on that exact `G_K`.
- 2026-03-07: `G0` closed and verified across control docs, manuscript, Lean narrative, and builds.
- 2026-03-08: `P7` sharpened from measure-level/full-symbol wording to the
  finite admissible dictionary package: exact finite symbol `S_J`, Poisson
  regularization, and explicit error budget.
- 2026-03-07: `G1.1-G1.6` prepared the broad-cone support-upgrade branch and moved the
  Aristotle `W_K` packet into background-only status.
- 2026-03-07: a reviewed target-cone reset note raised a stronger blocker:
  current `W_K / \mathcal W` may be too broad for honest Weil positivity.
- 2026-03-07: `T0.1` audit closed with verdict `pivot required`.
  Public mainline now pivots to the positive-definite / convolution-square cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- 2026-03-07: the corrected-cone theorem blocks `A1-pd` and `packet-Rayleigh`
  were refined further: they currently target two different centered families,
  so the live knife-edge is now the same-family bridge `SF-pd`.
- 2026-03-07: pushing the naive same-family route one step further exposed a
  contradiction: the family `\Phi_{B,t}|p|^2` is too large to serve as the
  closure family, because on `K<\pi` it overgenerates broad local positivity.
- 2026-03-07: the honest corrected theorem package is now:
  `A1-pd` on dense autocorrelation packets,
  exact packet-Rayleigh on `\Psi_c * \widetilde{\Psi_c}`,
  and the new hard theorem `A3-pd` asserting positivity of the packet symbol
  `S_{g,\Delta}` on that same exact family.
- 2026-03-07: pushing `A3-pd` one step further shows that the old theorem shape
  is too strong on a dense packet dictionary: the exact packet identity survives,
  but a uniform packet-symbol floor / uniform positive gap cannot hold on the full
  family.
- 2026-03-07: the public frontier therefore pivots again from `A3-pd` to
  `PSD-pd`: prove positive semidefiniteness of the packet kernel
  `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace.
- 2026-03-07: the stronger packet-space audit shows that the literal
  `prime-block PSD factorization or Hilbert lift -> Archimedean domination`
  theorem shape is false on dense packet dictionaries. The active constructive
  route is now direct PSD of the full kernel `K_Q`, with `Herglotz/Bochner`
  kept only as diagnostic equivalence language.
- 2026-03-08: the strict packet theorem package is now frozen as
  `P1 -> P2 -> P4 -> P5 -> P6 -> P7.3 -> P7.4 -> P7.5 -> P7.6 -> PSD-pd`,
  where the immediate constructive target is finite admissible dictionary
  positivity `S_J(\theta)=A_J(\theta)-P_J(\theta)\ge0`.
- 2026-03-08: Poisson regularization is retained only as a finite verification
  device with explicit error budget, while measure-level/full-symbol language
  is demoted to secondary Herglotz-style notation.
- 2026-03-08: the live quantitative frontier sharpened further:
  explicit packet bounds on `\alpha_m,\beta_m` now drive the finite-dictionary
  package through inequalities `(C1)` / `(C1')`, while Poisson regularization
  stays only a verification device and Gershgorin stays sparse-only.
- 2026-03-08: the canonical centered half-atom
  `g_{δ,t_0,0}=\Lambda_\delta\rho_{t_0}` is now the first explicit pilot
  packet. On the compact `K=0.2` with dictionary `J={0,1}`, `Δ=0.15`, prime
  collisions vanish for `\delta<0.0124`, reducing positivity to a strictly
  positive Archimedean gap.
- 2026-03-08: the compact scalar route `W_K(u)\ge0` is rejected as a public
  mainline on any compact with active nodes: `a_K^*\in L^1` forces
  `\widehat{a_K^*}(u)\to0`, while the finite cosine prime sum over `\Xi_K`
  returns arbitrarily close to its full positive mass. The package
  `S1/S2/S3/S4` is kept only as a correct diagnostic compact-truncation reduction.
- 2026-03-08: Suzuki/Yoshida operator nondegeneracy in the generalized
  form-pair shape `(G_g[a],J_a)` is promoted from alternative pivot to the
  primary live route. The naive raw-operator / plain-`L^2` gap transfer is
  rejected; the real missing brick is `H1`, the construction of `S_{a,M}` and
  `J_a`.
- 2026-03-08: the one-sided filtered Volterra bridge is superseded by the
  symmetric two-sided filtered tail package
  `\mathcal P_{M,N}, \Delta_{M,N}, B_{M,N}, \widetilde Q_{M,N}`.
  After extracting the exact raw-compressed Section 8 formula
  `Q_M^{raw}=T_M[P_A]-\Pi_M`,
  `\Pi_M=(2M+1)T_P^{Ray}(t,M)=\iota_M^*T_P^{Ray}(t)\iota_M`,
  and
  `q_{rs}=A_{r-s}-\sum \lambda_n e^{2\pi i(s-r)\xi_n}`,
  the raw identity `w_{rs}(a)=\kappa(a)q_{rs}` is now rejected as an exact
  theorem shape, because the raw Q3 matrix is Toeplitz with constant diagonal
  while the Suzuki raw Weil matrix on the `\chi_n[a]` basis has logarithmically
  growing diagonal. The live bulk theorem is therefore the direct filtered
  match on `(++),(+-)`, the filtered four-block package remains the derived
  consequence layer, and the only second live brick after that is the
  finite-dimensional Suzuki cap.
