# Paper Mainline Tracker

Updated: 2026-03-08

## Role

This file is the source of truth for:

- section-to-gate map,
- theorem-to-gate typing,
- manuscript notation contract,
- conditional statement inventory,
- unresolved paper-facing dependencies.

It is **not** the execution queue and **not** the master gate-state file.

## Live Notation Contract

| Symbol | Meaning | Status |
| --- | --- | --- |
| `R_K` | broad restriction cone `C^+_{\mathrm{even}}([-K,K])` | auxiliary |
| `B_K` | broad ambient class of even, compactly supported tests in `[-K,K]` | auxiliary ambient space |
| `\widetilde\psi(x)=\overline{\psi(-x)}` | reflected conjugate test | active notation |
| `\mathcal W_{K,0}^{pd}` | seed set of local convolution squares `\psi*\widetilde\psi` with `\operatorname{supp}\psi\subset[-K/2,K/2]` | active public target seed |
| `\mathcal W_K^{pd}` | local positive-definite / convolution-square Weil cone | active public target |
| `\mathcal W^{pd} = \varinjlim_{K>0}\mathcal W_K^{pd}` | global positive-definite Weil cone | active public target |
| `\mathcal P_K(t_0)` | pre-square packet span built from shifted Fej\'er$\times$heat atoms | active approximation engine |
| `\mathcal G_K^{pd}` | dense autocorrelation packet family `\operatorname{cone}\{\Psi*\widetilde\Psi:\Psi\in\mathcal P_K(t_0)\}` | active density family |
| `\mathcal G_{K,\mathrm{Ray}}^{pd}` | naive centered Rayleigh family `\operatorname{cone}\{\Phi_{B,t,p}=\Phi_{B,t}|p|^2\}` | background candidate; too large for closure |
| `a_K^*` | compact truncation `a^*1_{[-K,K]}` | active spectral notation |
| `\Xi_K` | active positive prime nodes on `[0,K]` | active spectral notation |
| `W_K(u)` | scalar compact spectral weight `\widehat{a_K^*}(u)-\sum_{\xi_n\in\Xi_K}(2\Lambda(n)/\sqrt n)\cos(u\xi_n)` | diagnostic compact-truncation object; rejected as public frontier once `\Xi_K\neq\varnothing` |
| `S_{g,\Delta}(\theta)` | packet Toeplitz symbol built from `\kappa_m=\mathcal Q(h(\cdot-m\Delta))` | structural object; no longer the public theorem target by itself |
| `K_Q(g_i,g_j)` | packet kernel `\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | active hard-theorem object |
| `\varphi_{a,j}` | nonorthogonal packet states in `L^2(-a,a)` used to build the Suzuki bridge | active candidate notation |
| `\Gamma_{a,M}` | packet Gram matrix `[ \langle \varphi_{a,i},\varphi_{a,j}\rangle ]` | active candidate notation |
| `G_g[a], J_a, E_{a,M}, S_{a,M}` | Suzuki/Yoshida generalized form-pair bridge data | active primary operator notation |
| `I_0^{(a)}, U_a, M_{1+z}, \Delta_+, B_M, \widetilde Q_M` | filtered Volterra bridge data with explicit pullback metric `B_M=T_M[|1+z|^2]=\Delta_+^*\Delta_+` and filtered finite section `\widetilde Q_M=\Delta_+^*Q_{M+1}\Delta_+` | active preferred H1 notation |
| `S(B)` | finite prime set `\{p: p\le e^{2\pi B}\}` feeding the semilocal engineering layer | active auxiliary operator notation |
| `\eta_m^{(S,a)}` | semilocal cyclic/Jacobi packet states used only as a basis/Gram engine for `H1` | active engineering notation |
| `\Gamma_{a,M}^{(S)}` | semilocal Gram matrix `[ \langle \eta_i^{(S,a)},\eta_j^{(S,a)}\rangle ]` | active engineering notation |
| `E_{a,M}^{(S)}, S_{a,M}^{(S)}, \widetilde S_{a,M}^{(S)}` | semilocal-assisted synthesis data for the candidate `H1` bridge | active engineering notation |

Lean compatibility note:

- live Lean still exports the old broad names `W_K` and `Weil_cone`;
- after the `T0.1` audit these are frozen broad-cone exports, not the public
  paper contract.

## Gate Map

| Gate | Meaning | Paper status | Main paper dependencies |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk | done | `sections/T0.tex`, `sections/Weil_linkage.tex` |
| `T0.1` | target-cone audit | done, verdict `pivot required` | audit memo + control plane |
| `T0-pd` | corrected positive-definite target cone | done in docs/manuscript | `sections/scope_notation.tex`, `sections/Notation/qstar_contract.tex`, `sections/Main_closure.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
| `S-pd` | scalar compact spectral route through `W_K(u)` | rejected compact-truncation route | `sections/Main_closure.tex`, `sections/Weil_pack.tex`, `sections/introduction.tex`, `sections/abstract.tex` |
| `A1-pd` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | frozen theorem block | `sections/A1prime.tex`, `sections/Main_closure.tex` |
| `packet-Rayleigh-naive` | identify `Q^\star(t;\Phi_{B,t,p})` with the controlled Toeplitz/RKHS quadratic form on the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}` | background candidate | `sections/Main_closure.tex`, `sections/Weil_pack.tex` |
| `SF-pd` | same-family bridge through the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}` | rejected as mainline route | historical note only |
| `packet-Rayleigh-pd` | exact finite Toeplitz form on autocorrelation packets `\Psi_c * \widetilde{\Psi_c}` with finite symbol `S_J` on each admissible dictionary | frozen theorem block | `sections/Main_closure.tex`, `sections/Weil_pack.tex` |
| `A3-pd` | uniform packet-symbol floor on the dense packet family | rejected-too-strong route | `sections/Main_closure.tex`, `sections/scope_notation.tex` |
| `PSD-pd` | positive semidefiniteness of the packet kernel `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | active fallback route; finite-dictionary reduction and coefficient-bounding package explicit | `sections/Main_closure.tex`, `sections/scope_notation.tex`, `sections/introduction.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
| `H-bridge` | Suzuki/Yoshida generalized form-pair bridge `H1 -> H2 -> H3 -> H4` | active primary live route | `sections/Main_closure.tex`, `docs/insights/suzuki_form_pair_bridge_2026_03_08.md` |
| `centered A3/RKHS` | positivity on centered packets | reusable input | `sections/A3/*`, `sections/RKHS/*`, `sections/Main_closure.tex` |
| `A2-pd` | continuity on the corrected cone | inherited input | `sections/A2.tex`, `sections/Main_closure.tex` |
| `LF-pd` | LF lift from all `\mathcal W_K^{pd}` to `\mathcal W^{pd}` | skeleton available, still conditional | `sections/Main_closure.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
| `G6` | Weil linkage to RH | available once corrected-cone positivity is honest | `sections/Weil_linkage.tex` |

## Section-To-Gate Map

| Section | Gate role | Typing status | Note |
| --- | --- | --- | --- |
| `sections/T0.tex` | `T0` | aligned | normalization locked |
| `sections/A1prime.tex` | auxiliary density on `R_K`; source material for `A1-pd` only indirectly | auxiliary | no longer the mainline RH density theorem |
| `sections/A2.tex` | continuity input for corrected local closure | aligned via ambient space | continuity on the broad ambient compact-support class feeds `\mathcal W_K^{pd}` |
| `sections/A3/*` | centered positivity engine | aligned | should feed the exact centered packet family, not a broad shifted cone |
| `sections/RKHS/*` | prime-control input for centered positivity | aligned | same role as before, but now on the corrected target |
| `sections/Main_closure.tex` | corrected-cone packaging plus operator-pivot audit | aligned after compact-spectral obstruction | Suzuki/Yoshida `H-bridge` is now the primary live route; scalar compact package is diagnostic-only; packet route remains fallback |
| `sections/Weil_pack.tex` | dependency summary for corrected route | aligned after `T0.1` | broad-cone route demoted; scalar spectral route primary |
| `sections/Weil_linkage.tex` | `G6` on the corrected cone | aligned after `T0.1` | RH theorem must remain conditional on corrected local positivity |
| `sections/T5/*` | broad-cone LF skeleton only | archived/read-only | reference, not mainline |

## Theorem Typing Inventory

| Statement | Current typing | Required typing after `T0.1` | Status |
| --- | --- | --- | --- |
| A1' density (`thm:A1-density`, `a1:thm:A1-local-density`) | theorem on `R_K` | auxiliary theorem on `R_K` only | aligned after pivot |
| packet-density definition (`def:pd-packet-cone`) | pre-square packet span plus dense autocorrelation family | definitions of `\mathcal P_K(t_0)` and `\mathcal G_K^{pd}` | aligned |
| `A1-pd` (`thm:A1-pd`) | theorem target on `\mathcal W_K^{pd}` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | aligned as theorem block |
| `packet-Rayleigh-naive` (`lem:packet-rayleigh-identification`) | theorem target on `\mathcal G_{K,\mathrm{Ray}}^{pd}` | naive quadratic-form bridge on an overlarge family | background candidate only |
| `packet-Rayleigh-pd` (`thm:packet-rayleigh-pd`) | theorem target on `\mathcal G_K^{pd}` | exact Toeplitz form on autocorrelation packets | aligned as theorem block |
| `A3-pd` (`prop:a3-pd-too-strong`) | old theorem target on the same dense packet family `\mathcal G_K^{pd}` | uniform packet-symbol floor on dense packets | rejected-too-strong route |
| `S1/S2/S3/S4` (`def:compact-spectral-weight`, `prop:compact-spectral-identity`, `prop:compact-spectral-positivity`, `thm:compact-spectral-closure`, `cor:compact-spectral-global-closure`) | theorem package on the corrected local/global cone | compact-truncation scalar reduction through `W_K(u)` | frozen as a correct diagnostic package; rejected as the live public route once `\Xi_K\neq\varnothing` |
| `PSD-pd` (`thm:PSD-pd`) | theorem target on a dense translation-compatible packet subspace behind `\mathcal G_K^{pd}` | positive semidefiniteness / corrected compact positivity through the strict finite-dictionary `P7` package, explicit bounds on `\alpha_m,\beta_m`, and the canonical half-atom pilot | active fallback blocker; pursue through the strict `P1–P8` chain with finite-symbol `P7.3`--`P7.6`, coefficient inequalities `(C1)/(C1')`, canonical pilot positivity, and Poisson verification as backup if `H1` stalls |
| A2 continuity | theorem on ambient admissible compact tests | inherited input on `\mathcal W_K^{pd}` | aligned |
| conditional main positivity (`thm:Main-positivity`) | positivity on corrected global cone | conditional on centered packet density in `\mathcal W_K^{pd}` | aligned after pivot |
| local closure proposition | compact closure from a dense positive family inside `\mathcal W_K^{pd}` | theorem on `\mathcal W_K^{pd}` | aligned after pivot |
| Weil criterion (`thm:Weil-criterion`) | theorem on `\mathcal W^{pd}` | theorem on the corrected positive-definite cone | aligned after pivot |
| RH theorem (`thm:RH`) | conditional | must stay conditional until `A1-pd` and `LF-pd` close | aligned after pivot |

## Conditional Statements Inventory

These statements must stay explicitly conditional after the pivot:

- the informal main result in `sections/introduction.tex`,
- `thm:Main-positivity` in `sections/Main_closure.tex`,
- `thm:weil-sufficiency-pack` in `sections/Weil_pack.tex`,
- `thm:RH` in `sections/Weil_linkage.tex`.

Any wording implying unconditional positivity on the corrected cone before
`PSD-pd` is closed is now a bug. Any wording implying that a uniform packet-symbol
floor on the full dense packet family is the live theorem shape is also a bug.

## Target-Cone Audit Result

`T0.1` is complete after the 2026-03-07 audit pass:

- live Lean and paper were compared against the classical Weil interface;
- the current broad cone `W_K / \mathcal W` was judged too wide;
- the public manuscript contract has pivoted to the positive-definite /
  convolution-square cone `\mathcal W_K^{pd} / \mathcal W^{pd}`;
- broad-cone `G1-G3` work is now background-only until it can be reused under the corrected contract.

Detailed memo:

- `docs/insights/target_cone_audit_2026_03_07.md`

## Lean Crosswalk

Current compiled Lean route:

`Q3.Main -> RH_of_shifted_atom_route -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`

Interpretation rule after `T0.1`:

- current Lean exports on `Weil_cone` remain structurally useful,
- but they are frozen broad-cone exports, not the public mainline target,
- no theorem-name rewrite is required yet,
- Lean renames or narrowing come only after the corrected cone contract is fully frozen.

## Unresolved Dependencies

1. Freeze the compact spectral obstruction in the paper-facing dependency map:
   `W_K(u)\ge0` cannot be the public compact mainline once `\Xi_K\neq\varnothing`,
   because `a_K^*\in L^1` forces `\widehat{a_K^*}(u)\to0` while the finite cosine
   prime sum returns arbitrarily close to its full positive mass.
2. Freeze the Suzuki/Yoshida generalized form-pair bridge as the primary live route:
   `H1` exact/asymptotic intertwining through `S_{a,M}` and `J_a`
   -> `H2` Galerkin/recovery
   -> `H3` kernel-exclusion transfer
   -> `H4` Suzuki RH criterion.
   The honest blocker there is `H1`, not a raw operator-gap theorem.
3. Candidate construction of `S_{a,M}` and `J_a` in RKHS/Gram language:
   choose packet states `\varphi_{a,j}` in `L^2(-a,a)`,
   define `E_{a,M}=\operatorname{span}\{\varphi_{a,j}:|j|\le M\}`,
   use raw synthesis
   `S_{a,M}(\sum c_j e^{ij\theta})=\sum c_j\varphi_{a,j}`,
   and let `J_a` be the Gram-pullback metric, i.e. matrix `\Gamma_{a,M}^{-1}`
   in the packet basis, so that `S_{a,M}^*J_aS_{a,M}=I`.
   The next theorem task is then the kernel-matrix comparison
   `[ \langle G_g[a]\varphi_{a,j},\varphi_{a,k}\rangle ]=
   \kappa(a)(T_M[P_A]-T_P^{(M)})+R_{a,M}`.
   The strongest current refinement is finite-prime semilocal:
   use the packet basis `\eta_m^{(S,a)}` coming from cyclic/Jacobi machinery,
   with semilocal Gram matrix `\Gamma_{a,M}^{(S)}` and normalized synthesis
   `\widetilde S_{a,M}^{(S)}`, but keep this strictly as `H1` engineering
   infrastructure and not as a separate RH endgame.
   Preferred first-pass refinement:
   use the filtered Volterra bridge
   `J_a=(I_0^{(a)})^*I_0^{(a)}`,
   `I_0^{(a)}S_{a,M}=U_aM_{1+z}|_{P_M}`,
   with explicit pullback metric
   `B_M=S_{a,M}^*J_aS_{a,M}=T_M[|1+z|^2]=\Delta_+^*\Delta_+`,
   and filtered finite section
   `\widetilde Q_M=\Delta_+^*Q_{M+1}\Delta_+`,
   so the real comparison target becomes
   `S_{a,M}^*G_g[a]S_{a,M}=\kappa(a)\widetilde Q_M+F_{a,M}`.
4. Pre-square density theorem on `C_c^\infty([-K/2,K/2])` strong enough to feed
   `A1-pd` through autocorrelation continuity if the fallback packet route is needed.
5. `A1-pd`: proof of density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.
6. Exact packet-Rayleigh theorem on autocorrelation packets
   `\Psi_c * \widetilde{\Psi_c}` with finite symbols `S_J` on admissible dictionaries.
7. Naive packet-Rayleigh on `\mathcal G_{K,\mathrm{Ray}}^{pd}` is too large to serve
   as the closure family; this must remain background-only.
8. Reject the old `A3-pd` route as too strong on a dense packet dictionary.
9. `PSD-pd`: prove positive semidefiniteness of the packet kernel
   `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense
   translation-compatible packet subspace feeding `\mathcal G_K^{pd}`.
10. Record the prime-block obstruction on packet space:
   standalone PSD factorization of the packet prime block is false on dense
   packet dictionaries containing an active node.
11. Freeze the strict packet theorem package:
   `P1` exact packet sesquilinear identity
   -> `P2` Toeplitz reduction on translation packet dictionaries
   -> `P3` desired prime-factorization theorem shape
   -> `P4` prime-block obstruction
   -> `P5` full sequence split `\kappa=\alpha-\beta`
   -> `P6` Toeplitz/Herglotz criterion
   -> `P7.3` exact finite symbol identity
   -> `P7.4` finite-symbol domination `S_J\ge0`
   -> `P7.5` Poisson-regularized verification
   -> `P7.6` explicit error-budget criterion
   -> `PSD-pd`.
12. Freeze the concrete finite-dictionary bounding package:
   packet geometry `R_g,R_h`
   -> Archimedean bounds `A1--A4` on `\alpha_m`
   -> prime-mass bounds `P1--P3` on `\beta_m`
   -> finite-symbol envelope `(C0)`
   -> explicit sufficient inequalities `(C1)/(C1')`
   -> sparse regime `(C2)/(C2')`.
13. Freeze the canonical centered half-atom pilot:
    `g_{δ,t_0,0}=\Lambda_\delta\rho_{t_0}`
    -> exact formulas for `\|g\|_1`, `\|h\|_1`, `\|h\|_\infty`
    -> lower bound `H_r\ge M_g(r/2)^2`
    -> pilot compact `K=0.2`, `J={0,1}`, `\Delta=0.15`
    -> vanishing `\beta_0=\beta_1=0` for `\delta<0.0124`
    -> positivity reduces to the Archimedean gap `\alpha_0>2|\alpha_1|`.
14. Keep `Herglotz/Bochner` only as the secondary diagnostic route:
   equivalence between positive-definite sequence, Toeplitz-section PSD, and
   positive measure representation for the packet coefficients.
15. Record Gershgorin diagonal dominance only as a sparse finite-block lemma;
    it must not be presented as the dense main theorem.
16. Treat finite-dictionary `P7` as the immediate fallback constructive target, now via
    explicit coefficient bounds on `\alpha_m,\beta_m`; any new full-kernel
    operator package is fallback-only.
17. Explicit LF statement phrased only on the corrected cone `\mathcal W^{pd}`.

## Background Broad-Cone Branch

The old broad-cone reset branch is not deleted, only demoted:

- `G1`: support upgrade from `R_K` to broad admissible `W_K`
- `G2`: exact admissible family inside broad `W_K`
- `G3`: positivity on that family

This branch may still land local support lemmas or construction templates, but it
is no longer the architectural driver of the RH route.
