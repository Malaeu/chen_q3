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
| `R_K` | restriction cone `C^+_{\mathrm{even}}([-K,K])` with the uniform norm | active |
| `W_K` | admissible support cone of even, nonnegative, compactly supported tests supported in `[-K,K]` | active |
| `G_K` | future exact admissible generator family inside `W_K` | active but unresolved |
| `\mathcal W = \bigcup_{K>0} W_K` | global Weil cone | active |

## Gate Map

| Gate | Meaning | Paper status | Main paper dependencies |
| --- | --- | --- | --- |
| `T0` | Guinand--Weil crosswalk locked | done | `sections/T0.tex`, `sections/Weil_linkage.tex` |
| `G0` | domain/type repair and narrative alignment | done | `sections/scope_notation.tex`, `sections/Notation/qstar_contract.tex`, `sections/A1prime.tex`, `sections/Main_closure.tex`, `sections/Weil_pack.tex`, `sections/Weil_linkage.tex` |
| `G1` | support upgrade from `R_K` to admissible `W_K` | active frontier | `sections/A1prime.tex`, `sections/Main_closure.tex` |
| `G2` | choose and freeze one exact admissible family `G_K` | unresolved | `sections/Main_closure.tex` |
| `G3` | prove positivity on that exact `G_K` | unresolved | `sections/Main_closure.tex`, `sections/A3/*`, `sections/RKHS/*` |
| `G4` | compact closure on each `W_K` | packaged but conditional | `sections/Main_closure.tex` |
| `G5` | LF lift from all `W_K` to `W` | skeleton available, still conditional | `sections/Main_closure.tex`, legacy T5 appendix as reference only |
| `G6` | Weil linkage to RH | available | `sections/Weil_linkage.tex`, `sections/Weil_pack.tex` |

## Section-To-Gate Map

| Section | Gate role | Typing status | Note |
| --- | --- | --- | --- |
| `sections/T0.tex` | `T0` | aligned | normalization locked |
| `sections/A1prime.tex` | `A1'` input for `G1` | must live on `R_K` | not yet a theorem on admissible `W_K` |
| `sections/A2.tex` | analytic input for `G4`/`G5` | theorem on `W_K` | continuity side is already on admissible tests |
| `sections/A3/*` | positivity ingredients feeding `G3` | centered/auxiliary | not yet positivity on a final admissible `G_K` |
| `sections/RKHS/*` | prime-control ingredients feeding `G3` | auxiliary | not yet a closure theorem by itself |
| `sections/Main_closure.tex` | `G1-G5` packaging | aligned after G0 | remains conditional on `G1-G5` |
| `sections/Weil_pack.tex` | `G6` dependency summary | aligned after G0 | exposes gate chain explicitly |
| `sections/Weil_linkage.tex` | `G6` | aligned but conditional | RH theorem must stay conditional on unresolved closure gates |
| `sections/T5/*` | legacy LF skeleton only | archived/read-only | reference, not mainline |

## Theorem Typing Inventory

| Statement | Current typing | Required typing after G0 | Status |
| --- | --- | --- | --- |
| A1' density (`thm:A1-density`, `a1:thm:A1-local-density`) | theorem on `R_K` | theorem on `R_K` | aligned after G0 |
| A2 continuity | theorem on admissible compact tests | theorem on `W_K` | aligned |
| conditional main positivity (`thm:Main-positivity`) | conditional closure on `W` | conditional on `G1-G5` with local closure on `W_K` explicit | aligned after G0 |
| compatibility reduction proposition | generic compact closure from an admissible `G_K` | should state `G4` on a common admissible `G_K` | aligned after G0 |
| Weil criterion (`thm:Weil-criterion`) | theorem on `W` | theorem on `W` | aligned |
| RH theorem (`thm:RH`) | conditional | must stay conditional until `G1-G5` close | aligned after G0.3 |

## Conditional Statements Inventory

These statements must stay explicitly conditional after the reset:

- the informal main result in `sections/introduction.tex`,
- `thm:Main-positivity` in `sections/Main_closure.tex`,
- `thm:weil-sufficiency-pack` in `sections/Weil_pack.tex`,
- `thm:RH` in `sections/Weil_linkage.tex`.

Any wording implying unconditional positivity on all of `W` before `G1-G3` is closed is a bug.

## G0 Result

`G0` is complete after the 2026-03-07 reset pass:

- `R_K`, `W_K`, and `G_K` are explicit in the active notation layer;
- active closure-facing theorems are typed as statements on `R_K`, `W_K`, or future `G_K`;
- active RH/closure claims remain conditional on unresolved gates;
- Lean-facing docstrings now state that the compiled route still inherits `Q3.prime_term_le_at_t_critical_axiom`.

## Lean Crosswalk

Current compiled Lean route:

`Q3.Main -> RH_of_shifted_atom_route -> PaperMainlineAtomRoute -> CompatibilityReduction -> Q_nonneg_t_critical`

Paper-facing Lean theorems already exported:

- `Q_phi_shift_pair_nonneg_t_critical`
- `Q_Fejer_heat_atom_nonneg_t_critical`
- `Q_nonneg_on_WK_tcritical_current_atom_route`
- `Q_nonneg_on_Weil_cone_current_atom_route`
- `RH_of_shifted_atom_route`

Interpretation rule:

- these names are structurally useful,
- but they are **not** yet evidence that `G3-G6` are mathematically closed,
- because the scalar layer still inherits `Q3.prime_term_le_at_t_critical_axiom`.

## Unresolved Dependencies

1. `G1`: there is no fixed support-upgrade theorem from `R_K` to admissible `W_K`.
2. `G2`: no exact admissible family `G_K` has been fixed as the unique mainline generator family.
3. `G3`: positivity is not yet proved on that exact `G_K`.

## Legacy Read-Only Surface

The following are retained for provenance only and do not drive the active paper map:

- centered/T5 route,
- Acceptance Gate narrative,
- `τ = 0` / PathB / PrimeCert closure stories,
- D3/IND/AB legacy branches,
- reproducibility/certificate appendices.
