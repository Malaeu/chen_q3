# Paper Mainline Tracker

Updated: 2026-03-07

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
| `B_K` | broad ambient support cone of even, nonnegative, compactly supported tests in `[-K,K]` | auxiliary ambient space |
| `\mathcal W_K^{pd}` | local positive-definite / convolution-square Weil cone | active public target |
| `\mathcal W^{pd} = \bigcup_{K>0}\mathcal W_K^{pd}` | global positive-definite Weil cone | active public target |
| `\mathcal P_K` | future centered Fejér×heat / autocorrelation packet cone inside `\mathcal W_K^{pd}` | active but unresolved |

Lean compatibility note:

- live Lean still exports the old broad names `W_K` and `Weil_cone`;
- after the `T0.1` audit these are frozen broad-cone exports, not the public
  paper contract.

## Gate Map

| Gate | Meaning | Paper status | Main paper dependencies |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk | done | `sections/T0.tex`, `sections/Weil_linkage.tex` |
| `T0.1` | target-cone audit | done, verdict `pivot required` | audit memo + control plane |
| `T0-corr` | corrected positive-definite target cone | done in docs/manuscript | `sections/scope_notation.tex`, `sections/Notation/qstar_contract.tex`, `sections/Main_closure.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
| `A1-pd` | density of centered packets in `\mathcal W_K^{pd}` | active frontier | `sections/A1prime.tex`, `sections/Main_closure.tex` |
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
| `sections/Main_closure.tex` | corrected-cone packaging | aligned after `T0.1` | now conditional on `A1-pd` rather than on broad-cone `G1-G3` |
| `sections/Weil_pack.tex` | dependency summary for corrected route | aligned after `T0.1` | broad-cone route demoted |
| `sections/Weil_linkage.tex` | `G6` on the corrected cone | aligned after `T0.1` | RH theorem must remain conditional on corrected local positivity |
| `sections/T5/*` | broad-cone LF skeleton only | archived/read-only | reference, not mainline |

## Theorem Typing Inventory

| Statement | Current typing | Required typing after `T0.1` | Status |
| --- | --- | --- | --- |
| A1' density (`thm:A1-density`, `a1:thm:A1-local-density`) | theorem on `R_K` | auxiliary theorem on `R_K` only | aligned after pivot |
| A2 continuity | theorem on ambient admissible compact tests | inherited input on `\mathcal W_K^{pd}` | aligned |
| conditional main positivity (`thm:Main-positivity`) | positivity on corrected global cone | conditional on centered packet density in `\mathcal W_K^{pd}` | aligned after pivot |
| local closure proposition | compact closure from a centered packet cone `\mathcal P_K` | theorem on `\mathcal W_K^{pd}` | aligned after pivot |
| Weil criterion (`thm:Weil-criterion`) | theorem on `\mathcal W^{pd}` | theorem on the corrected positive-definite cone | aligned after pivot |
| RH theorem (`thm:RH`) | conditional | must stay conditional until `A1-pd` and `LF-pd` close | aligned after pivot |

## Conditional Statements Inventory

These statements must stay explicitly conditional after the pivot:

- the informal main result in `sections/introduction.tex`,
- `thm:Main-positivity` in `sections/Main_closure.tex`,
- `thm:weil-sufficiency-pack` in `sections/Weil_pack.tex`,
- `thm:RH` in `sections/Weil_linkage.tex`.

Any wording implying unconditional positivity on the corrected cone before
`A1-pd` closes is now a bug.

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

1. Exact theorem-level definition of the corrected cone `\mathcal W_K^{pd}`
   and its topology in the paper mainline.
2. `A1-pd`: density of centered Fejér×heat / autocorrelation packets in
   `\mathcal W_K^{pd}`.
3. Exact centered packet family `\mathcal P_K` to be used by both density and positivity.
4. Explicit LF statement phrased only on the corrected cone `\mathcal W^{pd}`.

## Background Broad-Cone Branch

The old broad-cone reset branch is not deleted, only demoted:

- `G1`: support upgrade from `R_K` to broad admissible `W_K`
- `G2`: exact admissible family inside broad `W_K`
- `G3`: positivity on that family

This branch may still land local support lemmas or construction templates, but it
is no longer the architectural driver of the RH route.
