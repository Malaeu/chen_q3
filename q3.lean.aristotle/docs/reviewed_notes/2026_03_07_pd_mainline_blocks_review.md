# Reviewed Note

## Source

- raw file: `none (direct session note)`
- date: `2026-03-07`
- author / tool: `user note, reviewed against live repo`

## Status

- review status: `reviewed`
- scope: `math`
- safe for embeddings: `no`

## Core claim

This note sharpens the corrected-cone pivot into exact theorem blocks.
It says the live mainline should not stop at
`corrected cone -> A1-pd`,
but should freeze three exact mathematical interfaces:

- `T0-pd`: RH iff `Q^\star(t;\Phi) >= 0` on the corrected positive-definite cone;
- `A1-pd`: density of one exact centered packet cone `\mathcal P_K` in `\mathcal W_K^{pd}`;
- `packet-Rayleigh`: identify `Q^\star(t;\Psi * \widetilde{\Psi})` with the quadratic
  form already controlled by the centered Toeplitz/RKHS engine.

## Checked against repo

- Lean files:
  - `q3.lean.aristotle/Q3/Basic/Defs.lean`
  - `q3.lean.aristotle/Q3/Main.lean`
- TeX files:
  - `full/sections/scope_notation.tex`
  - `full/sections/Notation/qstar_contract.tex`
  - `full/sections/A1prime.tex`
  - `full/sections/Main_closure.tex`
  - `full/sections/Weil_pack.tex`
  - `full/sections/Weil_linkage.tex`
  - `full/sections/A3/rayleigh_bridge.tex`
  - `full/sections/RKHS/core.tex`
- control docs:
  - `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
  - `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
  - `IMPLEMENTATION_PLAN.md`

## What survived review

- The corrected target really should be phrased via convolution squares /
  positive-definite tests, not via the old broad `W_K` slogan.
- The exact local seed set
  `\mathcal W_{K,0}^{pd} = { \psi * \widetilde{\psi} : \operatorname{supp}\psi \subset [-K/2,K/2] }`
  matches the corrected Weil criterion route.
- The exact centered packet cone
  `\mathcal P_K = \operatorname{cone}{ \Phi_\Psi = \Psi * \widetilde{\Psi} }`
  is the right object to freeze as the common family for density and positivity.
- The inequality
  `||\psi * \widetilde{\psi} - \varphi * \widetilde{\varphi}||_\infty <= (||\psi||_1 + ||\varphi||_1) ||\psi - \varphi||_1`
  is the right continuity bridge from pre-square packet density to `A1-pd`.
- The current draft already contains the structural ingredients for packet-Rayleigh:
  `lem:a3-rayleigh-quotient` is the general quadratic pairing, while
  `thm:a3-rayleigh-identification` is the special case `p \equiv 1`.

## What was rejected or weakened

- Rejected: any suggestion that packet-Rayleigh is already proved in the exact
  packet form. It is now a frozen target theorem, not yet a closed theorem.
- Weakened: we do not introduce a second public packet symbol
  `\mathcal G_K^{pd}`. The repo keeps one canonical symbol `\mathcal P_K`
  for the packet cone to avoid notation churn.
- Weakened: no immediate Lean renames. The corrected contract is frozen first in
  manuscript + control docs; Lean narrowing stays a later task.

## Reusable theorem / lemma pointers

- `full/sections/A3/rayleigh_bridge.tex:63` — `lem:a3-rayleigh-quotient`
- `full/sections/A3/rayleigh_bridge.tex:79` — `thm:a3-rayleigh-identification`
- `full/sections/RKHS/core.tex:60` — `lem:rkhs-rayleigh-sampling-id`
- `full/sections/A1prime.tex` — exact packet cone `\mathcal P_K`, target theorem `A1-pd`,
  and autocorrelation continuity lemma
- `full/sections/Main_closure.tex` — target packet-Rayleigh theorem block

## Next action

- promote the theorem-block synthesis into `docs/INSIGHTS.md`
- refresh `q3_docs` so the new theorem blocks are searchable via embeddings
- make the next active task the proof skeleton behind `A1-pd`, not another broad-cone patch

## Notes

This note is now **superseded** by:

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/reviewed_notes/2026_03_07_same_family_bridge_review.md`

Reason:

- the newer review keeps the corrected-cone pivot,
- but replaces the weaker phrase
  `A1-pd + packet-Rayleigh`
  by the stricter and more accurate blocker:
  the same-family bridge between the dense family and the positive family.
