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

`T0-pd -> compact spectral route -> A2 closure -> LF-pd -> G6 -> RH`

- `T0-pd`: Guinand--Weil crosswalk with the corrected positive-definite target cone.
- `corrected cone`: local/global positive-definite Weil cone
  `\mathcal W_K^{pd} / \mathcal W^{pd}`.
- `compact spectral route`: exact compact spectral identity plus the scalar
  criterion
  `W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)\ge0`
  on every compact.
- `A2 closure`: continuity transfer on the corrected local cone.
- `LF-pd`: inductive-limit lift from all `\mathcal W_K^{pd}` to `\mathcal W^{pd}`.
- `G6`: Weil linkage from positivity on `\mathcal W^{pd}` to RH.

Fallback packet route:

- `A1-pd`: density of the centered autocorrelation family
  `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.
- `packet-Rayleigh-pd`: exact finite Toeplitz quadratic-form identity on the
  same autocorrelation packet family `\Psi * \widetilde\Psi`.
- `PSD-pd`: positive semidefiniteness of the packet kernel
  `K_Q(g_i,g_j):=\mathcal Q(g_i * \widetilde{g_j})` on that same dense
  pre-packet space.

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
| `S-pd` | scalar compact spectral route `W_K(u)\ge0` | `active` | the exact stack `S1/S2/S3/S4` is frozen, and the live blocker is the scalar inequality `W_K(u)\ge0` on every compact |
| `A1-pd` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | `frozen theorem block` | pre-square density route + autocorrelation continuity prove `\overline{\mathcal G_K^{pd}}=\mathcal W_K^{pd}` |
| `packet-Rayleigh-naive` | naive quadratic-form bridge on `\mathcal G_{K,\mathrm{Ray}}^{pd}=\operatorname{cone}\{\Phi_{B,t}|p|^2\}` | `background candidate` | keep only as an auxiliary identity; do not reuse it as the public closure family |
| `SF-pd` | same-family bridge through `\mathcal G_{K,\mathrm{Ray}}^{pd}` | `rejected as mainline route` | rejected because the naive Rayleigh family is too large and would force false broad local positivity |
| `packet-Rayleigh-pd` | exact Toeplitz form on autocorrelation packets `\Psi_c * \widetilde{\Psi_c}` | `frozen theorem block` | identify `\mathcal Q(\Psi_c * \widetilde{\Psi_c})` with the finite symbol integral `\frac{1}{2\pi}\int S_J(\theta)|p_c(\theta)|^2\,d\theta` on each admissible dictionary |
| `A3-pd` | uniform packet-symbol floor on the dense packet family | `rejected as theorem shape` | rejected because dense packet dictionaries admit collapsing packets `\Psi_\Delta`, so no uniform `c_K>0` can hold on the full family |
| `PSD-pd` | PSD of the packet kernel `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | `fallback constructive route` | finite-dictionary positivity via explicit coefficient bounds on `\alpha_m,\beta_m`, yielding `S_J=A_J-P_J\ge0` on each admissible block |
| `centered A3/RKHS` | positivity engine on centered packets | `done as analytic input` | supplies the model estimates that must be upgraded to packet-kernel positivity |
| `A2-pd` | continuity on the corrected local cone | `done as inherited input` | continuity explicitly restricted to `\mathcal W_K^{pd}` in the paper contract |
| `LF-pd` | LF lift on `\mathcal W^{pd}` | `blocked` | local positivity on every `\mathcal W_K^{pd}` is available |
| `G6` | Weil linkage to RH | `frozen` | available once positivity on `\mathcal W^{pd}` is honest |

## Current Frontier

- `T0.1` is closed with verdict `pivot required`.
- The broad target cone `W_K / \mathcal W` is too wide for the honest Weil interface.
- Current `G1.6` Aristotle work stays background only. It may still land local support lemmas,
  but it no longer determines the architectural frontier.
- New live frontier:
  1. make the scalar compact spectral route primary:
     exact compact spectral identity
     -> scalar criterion `W_K(u)\ge0`
     -> corrected compact positivity on `\mathcal W_K^{pd}`;
  2. treat the finite-dictionary packet package only as fallback discretization /
     verification for that scalar route;
  3. keep `A1-pd` frozen as the dense corrected-cone input on `\mathcal G_K^{pd}`;
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

## Active Milestone

Turn the corrected theorem package into a proof-ready compact spectral stack:

1. keep `\mathcal W_K^{pd}` and `\mathcal W^{pd}` fixed in control docs and manuscript,
2. freeze the scalar compact spectral weight
   `W_K(u)=\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)`,
  3. make the theorem stack
     `S1 exact compact spectral identity -> S2 spectral positivity criterion -> S3 corrected compact positivity -> S4 corrected global closure`
   the primary constructive route,
4. keep `A1-pd` frozen on the dense autocorrelation packet family `\mathcal G_K^{pd}` as auxiliary/fallback infrastructure,
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
17. keep Aristotle `G1.6` as background lemma-mining only.

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
- The primary remaining theorem package is now:
  scalar compact spectral identity
  -> scalar compact criterion `W_K(u)\ge0`
  -> corrected compact positivity on `\mathcal W_K^{pd}`;
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
- 2026-03-08: the scalar compact spectral route is now primary:
  exact compact spectral identity
  -> scalar inequality `W_K(u)\ge0`
  -> corrected compact positivity.
  The finite-dictionary packet package remains active only as fallback
  discretization / verification for that scalar route.
