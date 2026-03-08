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
| `S_{g,\Delta}(\theta)` | packet Toeplitz symbol built from `\kappa_m=\mathcal Q(h(\cdot-m\Delta))` | structural object; no longer the public theorem target by itself |
| `K_Q(g_i,g_j)` | packet kernel `\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | active hard-theorem object |

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
| `A1-pd` | density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}` | frozen theorem block | `sections/A1prime.tex`, `sections/Main_closure.tex` |
| `packet-Rayleigh-naive` | identify `Q^\star(t;\Phi_{B,t,p})` with the controlled Toeplitz/RKHS quadratic form on the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}` | background candidate | `sections/Main_closure.tex`, `sections/Weil_pack.tex` |
| `SF-pd` | same-family bridge through the naive family `\mathcal G_{K,\mathrm{Ray}}^{pd}` | rejected as mainline route | historical note only |
| `packet-Rayleigh-pd` | exact finite Toeplitz form on autocorrelation packets `\Psi_c * \widetilde{\Psi_c}` with finite symbol `S_J` on each admissible dictionary | frozen theorem block | `sections/Main_closure.tex`, `sections/Weil_pack.tex` |
| `A3-pd` | uniform packet-symbol floor on the dense packet family | rejected-too-strong route | `sections/Main_closure.tex`, `sections/scope_notation.tex` |
| `PSD-pd` | positive semidefiniteness of the packet kernel `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense translation-compatible packet subspace | active frontier; direct full-kernel PSD primary, `Herglotz/Bochner` secondary diagnostic, coefficient-bounding package now explicit | `sections/Main_closure.tex`, `sections/scope_notation.tex`, `sections/introduction.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
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
| `sections/Main_closure.tex` | corrected-cone packaging | aligned after `T0.1` | now conditional on `A1-pd` + exact packet-Rayleigh + `PSD-pd`, with the naive Rayleigh route kept background-only and the uniform-gap route rejected |
| `sections/Weil_pack.tex` | dependency summary for corrected route | aligned after `T0.1` | broad-cone route demoted |
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
| `PSD-pd` (`thm:PSD-pd`) | theorem target on a dense translation-compatible packet subspace behind `\mathcal G_K^{pd}` | positive semidefiniteness / corrected compact positivity through the strict finite-dictionary `P7` package and explicit bounds on `\alpha_m,\beta_m` | active blocker; pursue through the strict `P1–P8` chain with finite-symbol `P7.3`--`P7.6`, coefficient inequalities `(C1)/(C1')`, and Poisson verification as backup |
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

1. Pre-square density theorem on `C_c^\infty([-K/2,K/2])` strong enough to feed
   `A1-pd` through autocorrelation continuity.
2. `A1-pd`: proof of density of `\mathcal G_K^{pd}` in `\mathcal W_K^{pd}`.
3. Exact packet-Rayleigh theorem on autocorrelation packets
   `\Psi_c * \widetilde{\Psi_c}` with finite symbols `S_J` on admissible dictionaries.
4. Naive packet-Rayleigh on `\mathcal G_{K,\mathrm{Ray}}^{pd}` is too large to serve
   as the closure family; this must remain background-only.
5. Reject the old `A3-pd` route as too strong on a dense packet dictionary.
6. `PSD-pd`: prove positive semidefiniteness of the packet kernel
   `K_Q(g_i,g_j)=\mathcal Q(g_i * \widetilde{g_j})` on a dense
   translation-compatible packet subspace feeding `\mathcal G_K^{pd}`.
7. Record the prime-block obstruction on packet space:
   standalone PSD factorization of the packet prime block is false on dense
   packet dictionaries containing an active node.
8. Freeze the strict packet theorem package:
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
9. Freeze the concrete finite-dictionary bounding package:
   packet geometry `R_g,R_h`
   -> Archimedean bounds `A1--A4` on `\alpha_m`
   -> prime-mass bounds `P1--P3` on `\beta_m`
   -> finite-symbol envelope `(C0)`
   -> explicit sufficient inequalities `(C1)/(C1')`
   -> sparse regime `(C2)/(C2')`.
10. Keep `Herglotz/Bochner` only as the secondary diagnostic route:
   equivalence between positive-definite sequence, Toeplitz-section PSD, and
   positive measure representation for the packet coefficients.
11. Record Gershgorin diagonal dominance only as a sparse finite-block lemma;
    it must not be presented as the dense main theorem.
12. Treat finite-dictionary `P7` as the immediate constructive target, now via
    explicit coefficient bounds on `\alpha_m,\beta_m`; any new full-kernel
    operator package is fallback-only.
13. Explicit LF statement phrased only on the corrected cone `\mathcal W^{pd}`.

## Background Broad-Cone Branch

The old broad-cone reset branch is not deleted, only demoted:

- `G1`: support upgrade from `R_K` to broad admissible `W_K`
- `G2`: exact admissible family inside broad `W_K`
- `G3`: positivity on that family

This branch may still land local support lemmas or construction templates, but it
is no longer the architectural driver of the RH route.
