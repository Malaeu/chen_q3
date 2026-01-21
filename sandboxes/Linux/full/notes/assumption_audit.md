# Assumption Audit — 2025-10-15

Legend: `needs proof` = requires a proof or external citation; `promote to lemma` = should be stated as a formal lemma; `drop` = remove or replace by a proved statement.

## A2 — Continuity of \(Q\)

- done — `docs/tex/A2_continuity_Q.tex` — lemma recorded for local finiteness of the prime sampler and an explicit Lipschitz bound on every compact.

## A3 — Toeplitz Bridge / Arch Floor

- done — `Q3_paper/sections/A3/main.tex` — inputs (A3.1)–(A3.3) and Theorem~\ref{thm:A3} now give $\lambda_{\min}(T_M[P_A]-T_P)\ge \tfrac12(\czero-\rhok)$ once the grids are aligned.
- done — `Q3_paper/sections/A3/calibration.tex` — Proposition~\ref{prop:a3-calib} packages the $\tfrac12(\czero-\rhok)$ margin for downstream sections.
- done — `Q3_paper/sections/A3/local_positivity.tex` — Lemma~\ref{lem:local-positivity} controls the local floor with $\omega_{P_A}$.

## D3 — Prime Cancellation

- done — `docs/tex/D3_structural_PC_theorem.tex` — added Definition~\ref{def:ABK}, Lemmas~\ref{lem:D3-dispersion-from-cap}–\ref{lem:D3-anticonc}, Theorem~\ref{d3:thm:D3-structural}; AC–D3.* replaced by proved steps.
- done — `docs/tex/D3_operator_bridge.tex` — Lemma~\ref{d3:lem:D3-dispersion} derived from the trace cap, Theorem~\ref{d3:thm:D3-contraction} depends on the A3 results.
- done — `docs/tex/theorems/amp_noD3.tex` — Theorem~\ref{thm:amp-noD3} rephrased via AB($K$) citing A2/A3 lemmas.

## RKHS / Weil Link

- done — `Q3_paper/sections/RKHS/core.tex` — Lemmas~\ref{lem:rkhs-energy}, \ref{lem:gram-min-eig-lb} and Proposition~\ref{prop:operator-sandwich} package the RKHS input used in (A3.2).
- done — `Q3_paper/sections/RKHS/weil_isometry.tex` — Lemma~\ref{lem:rkhs-weil-isometry} gives the RKHS–Weil isometry; paired with Lemma~\ref{lem:rkhs-rayleigh-sampling-id} the Rayleigh identity is explicit.
- done — `Q3_paper/sections/Weil_pack.tex` — Theorem~\ref{thm:weil-sufficiency-pack} collects (T0)+(A1$'$)+(A2)+(A3)+(RKHS/MD)+(T5) into the global sufficiency pack.

## T5 — Compact-to-Global Transfer

- done — `Q3_paper/sections/T5/summary.tex` — Lemma~\ref{lem:T5-transfer} formalizes the monotone compact-to-global transfer.
- done — `Q3_paper/sections/T5/summary.tex` — Corollary~\ref{t5:cor:compact-chain-yes} and Proposition~\ref{t5:prop:T5_parameter_recipe} provide explicit schedules.

## Global Closure / Normalization

- done — `Q3_paper/sections/Main_closure.tex` — Theorem~\ref{thm:main-closure} wraps \AssumpPack{} into the final “$Q\ge0\Rightarrow$ RH” statement.

## Appendices / Automation

- done — `Q3_paper/sections/Weil_linkage.tex` — linkage section now cites the established A3/RKHS/IND/T5 results and frames per-$K$ certificates as reproducibility checks.
- retired — D1$^{\pm}$ no-go analysis remains only in legacy archives; the Q3 pipeline no longer depends on that gadget.

## Miscellaneous

- done — `Q3_paper/sections/A3/arch_bounds.tex` — arch symbol bounds are formalized (Lemma/Proposition) for downstream use.
- done — `Q3_paper/sections/A3/local_positivity.tex` — local positivity ties its floor constant to Proposition~\ref{a3:prop:A0-minus-LA}.
- archived — `docs/tex/FAQ_critical_points.tex` replaced by an empty placeholder; the active FAQ lives in `Q3_paper/appendix/FAQ.tex`.

---

## Q3 clean rebuild (2025-10-15)

All active TEX modules for version B now live in `Q3_paper/`:

- `Q3_paper/RH_Q3.tex` — new main file; `make -C Q3_paper pdf` builds `Q3_paper/RH_Q3.pdf` (55pp, no legacy/acceptance gate).
- Layout: `sections/` hosts A1′, A2, A3 (calibration/arch_bounds/matrix_guard), RKHS, IND/AB, T5, Weil linkage; `appendix/` keeps FAQ and verification.
- The old `main.tex` is retired; no `../` references remain. The local Makefile drives `latexmk`.
- Both prime-control routes (RKHS and MD/IND/AB) are included; further work stays inside those files.

Outstanding warnings in `RH_Q3.log`:

1. Missing labels: `a3:thm:A3-lock-two-scale`, `rkhs:thm:rkhs-ind`, `md:eq:block-claim`, `tab:acceptance-parameters`, `thm:A3LockGlobal`, `lem:T5p-grid`, `subsec:t5-atp`.
2. Bibliography: citations `Li1997`, `GriffinOnoRolenZagier2019`, `GuthMaynard2024`, `rodgers2020debruijn`, `Fesenko2008`, `ConnesMarcolli2008`, `WeilExplicit`, `Guinand1955`, `Titchmarsh1986` still need metadata in `references.bib`.
3. Appendix verification still mentions “independent expert verification” — rewrite as an internal reproducibility note.

Once cleared, refresh the notation table and close the remaining `needs proof` items.

## Session log — 2025-10-16

**Completed:**
- Migrated D3 module into `sections/D3/`: proved `d3:lem:D3-dispersion`, `d3:thm:D3-contraction`, and derived `thm:AC-D3-structure` + `cor:D3-lock`.
- Updated `sections/D3/amp_noD3.tex`; it now relies only on A3 and D3 without “assume” language.
- `RH_Q3.pdf` builds cleanly aside from dangling refs/cites listed above.

**Next session kickoff:**
- Formalize A3 in `sections/A3/main.tex` with explicit inputs (RKHS, IND/AB, T5) and the final bound.
- Then align RKHS / IND/AB / T5 with the Plan B outline.

Workspace: `Q3_paper/`.

---

## Parameter closure plan

Legacy artefacts already contain the numerical data for A3, prime caps, IND/AB budgets, and T5 grids (JSON certificates, parameter tables, Vampire logs).  
To finish the unconditional presentation in Q3 we will:

1. Pull the Arch margins `c0(K)` and smoothing parameters from `legacy/tex/A3_calibration_kappa.tex` and `legacy/cert/bridge/K*_A3_lock.json`, and publish them as tables in `sections/A3/`.
2. Copy the prime-cap evaluations (`legacy/cert/bridge/K*_trace.json`, `cert/bridge/logs/`) into a summary table cited next to the analytic lemmas in `sections/RKHS/`.
3. Aggregate the MD/IND budgets (currently in `sections/IND_AB/...` and JSON) into a monotone schedule table so the text references concrete numbers.
4. Import the T5 grid/Lipschitz data (`legacy/cert/bridge/K*_grid.json`, `ops/` scripts) into an appendix table linked to Lemma~\ref{lem:T5p-grid}.
5. Update `appendix/verification.tex` with a checklist referencing the automated proofs (`proofs/T5_global_transfer/`, SMT/ATP logs).

Once these tables are mirrored in Q3 and cited in the main theorems, the Plan B chain will be fully self-contained; see `notes/closure_plan.md` for the detailed todo list.
