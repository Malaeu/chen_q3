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

## Frozen G1.1 Statement

The first honest `G1` target is now frozen as a replacement theorem, not as a vague density slogan:

For every compact window `[-K,K]`, every `ε > 0`, and every finite nonnegative combination
`h` of shifted evenized Fejér×heat windows from the A1' restriction-level cone
(with fixed heat scale and admissible margin `|τ| + B ≤ K`), there exists an
admissible replacement `\widetilde h ∈ W_K` such that

- `||h - \widetilde h||_{L^\infty([-K,K])} < ε`,
- `\widetilde h` is even, nonnegative, and compactly supported in `[-K,K]`.

Consequent closure use:

- if `Φ ∈ W_K` and A1' gives a restriction-level approximant `h` with
  `||Φ - h||_{L^\infty([-K,K])} < ε`,
- then the replacement theorem gives `\widetilde h ∈ W_K` with
  `||h - \widetilde h||_{L^\infty([-K,K])} < ε`,
- hence `||Φ - \widetilde h||_{L^\infty([-K,K])} < 2ε`,
- and A2 yields `|Q^\star(t;Φ) - Q^\star(t;\widetilde h)| ≤ 2 L_Q(K) ε`.

This freezes `G1` without yet choosing the exact final family `G_K`; `G2` will
name `G_K` as the class of admissible replacements produced by this theorem.

## G1.2 Reuse Packet

The frozen `G1.1` statement now has a finite reuse packet.

Reusable local inputs

- `Q3/Proofs/A1_density.lean:70` — `Atom_eq_q3`
  bridges local `Atom` notation to `Q3.Fejer_heat_atom`.
- `Q3/Proofs/A1_density.lean:248` — `Atom_eq_zero_outside_open`
  gives the main support-vanishing step from the margin condition `|τ| + B ≤ K`.
- `Q3/Proofs/A1_density.lean:424` — `HeatKernel_LipschitzOn`
  supplies the local heat Lipschitz control used in the approximation budget.
- `Q3/Proofs/A1prime/HatInterpBounded.lean:31` — `hat_interpolation_approx_bounded`
  is the bounded-grid source for `δ`, `τ`, and `hmargin`.
- `Q3/Proofs/A1prime/HeatError.lean:29` — `FejerKernel_support_bound`
  is a clean support bookkeeping input on the Fejér side.
- `Q3/Proofs/A1prime/HeatError.lean:43` — `heat_error_bound`
  is the heat-side approximation brick.
- `Q3/Proofs/A1prime/HeatError.lean:101` — `total_atom_error`
  and `Q3/Proofs/A1prime/HeatError.lean:189` — `total_atom_error_even`
  package finite error accumulation, especially for evenized families.
- `Q3/Proofs/Q_Lipschitz.lean:278` — `Q_Lipschitz_on_W_K_thm`
  remains the admissible continuity input consumed only after the replacement lies in `W_K`.
- `Q3/T5_Transfer.lean:56` — `AtomCone_subset_W_K`
  is reusable as a downstream membership pattern.

Structure guidance only

- `Q3/Proofs/A1prime/A1_density_fixed_t0.lean:37` — `A1_density_WK_fixed_t0`
  may be mined only as a construction template for
  `hat interpolation -> support margin -> build admissible object -> sup-error`.
- `Q3/T5_Transfer.lean:78` — `T5_transfer_of_atoms`
  may be mined only as a closure skeleton once an admissible replacement theorem exists.

Do-not-reuse as active truth

- `Q3/AxiomsTheorems.lean:148` — `A1_density_WK`
  is legacy overpackaging and cannot serve as the honest post-reset `G1` theorem.
- Legacy prose in `Q3/T5_Transfer.lean` describing full closure on `W_K`
  remains archived/read-only.

Handoff to `G1.3`

- The next packet should split into:
  1. a support-preserving replacement lemma packet,
  2. an A2-facing error-budget packet.
- `G2` must stay blocked until that packet exists.

## G1.3 Packet

Prepared Aristotle-ready packet:

- `q3.lean.aristotle/aristotle_input/subagent_g1_support_replacement_2026_03_07.md`

Packet target:

- preferred: `atom_sum_mem_atomcone_fixed_of_margin`
- fallback: `atom_sum_mem_W_K_of_margin`

Interpretation:

- this packet extracts only the local admissible-membership brick buried in the old
  `hg_mem` block,
- it does not claim global density on `W_K`,
- it keeps `G2` and `G3` blocked until the resulting local theorem actually compiles.

## G1.4 Result Triage

The completed Aristotle project `c315e2a4-5923-44fa-a18c-4ed90cb08375` did not land.

Reason:

- the downloaded file does not compile as a real mainline patch,
- it redefines sandbox-local dummy objects (`Q3.W_K`, `Atom`, `IsEven`, `IsNonneg`)
  instead of using the real project context,
- so it cannot count as an admissible replacement theorem in the mainline.

Consequence:

- no patch from that file may be integrated,
- `G1` stays active,
- the next honest step is to extract the first blocked local theorem directly from the
  real `hg_mem` block and only then prepare a narrower sibling packet.

## G1.5 Blocker Extraction

The refreshed local theorem-shape search now targets the real support-membership block
inside `Q3/Proofs/A1prime/A1_density_fixed_t0.lean`.

Current preferred next statement:

- fallback-first route:
  `atom_sum_mem_W_K_of_margin`

Frozen exact Lean shape:

```lean
lemma atom_sum_mem_W_K_of_margin
    (K t0 δ : ℝ) (hK : K > 0) (ht0 : 0 < t0) (hδ : 0 < δ)
    (n : ℕ) (c : Fin n → ℝ) (τ : Fin n → ℝ)
    (hc_nonneg : ∀ i, 0 ≤ c i)
    (hmargin : ∀ i, |τ i| + δ ≤ K) :
    let g : ℝ → ℝ := fun x => ∑ i, c i * Atom δ t0 (τ i) x
    g ∈ Q3.W_K K := by
```

Interpretation:

- prove that the finite nonnegative atom sum built under the margin condition
  already lies in the admissible `W_K`,
- then use that theorem as the honest membership brick inside the stronger
  `AtomCone_K_fixed` statement,
- only after this lands do we reopen a stronger packet such as
  `atom_sum_mem_atomcone_fixed_of_margin`.
- workflow reset: `exact?` is advisory-only; the real rejection criteria are
  `sorry`/`admit`, non-compilation, or fake local replacements instead of real Q3 objects.

## Legacy Read-Only Surface

The following are retained for provenance only and do not drive the active paper map:

- centered/T5 route,
- Acceptance Gate narrative,
- `τ = 0` / PathB / PrimeCert closure stories,
- D3/IND/AB legacy branches,
- reproducibility/certificate appendices.
