# Reviewed Note

## Source

- raw file: `q3.lean.aristotle/docs/incoming_notes/2026_03_07_target_cone_reset.md`
- date: `2026-03-07T19:18:28+01:00`
- author / tool: `incoming_notes ingestion`

## Status

- review status: `reviewed`
- scope: `math`
- safe for embeddings: `yes`

## Extracted files

- `q3.lean.aristotle/docs/incoming_notes/2026_03_07_target_cone_reset.md`

## Core claim

Этот note не спорит с локальным `G1/G2/G3` bridge, а бьёт глубже:
он утверждает, что current target cone в mainline задан слишком широко.
Live repo сейчас действительно работает с `W_K` как с cone even, nonnegative,
compactly supported tests in `[-K,K]`, тогда как note предлагает, что правильный
Weil target должен быть positive-definite / convolution-square cone.

После review surviving version такая:

- это **сильный architectural challenger**, а не автоматически принятый новый mainline;
- у него есть серьёзная локальная опора: `a(ξ)=log π - Re ψ(1/4+iπξ)` уходит в минус
  уже примерно после `|ξ| ≈ 1`, а active prime nodes на каждом fixed compact образуют
  дискретное конечное множество с ненулевыми зазорами;
- значит broad claim `Q >= 0` на всех even nonnegative compactly supported tests
  выглядит математически подозрительным и требует отдельного target-cone audit
  до дальнейшего расхода сил на closure inside current `W_K`.

## Checked against repo

- Lean files:
  - `q3.lean.aristotle/Q3/Basic/Defs.lean`
  - `q3.lean.aristotle/Q3/Axioms.lean`
  - `q3.lean.aristotle/Q3/Proofs/Q_nonneg_t_critical.lean`
- TeX files:
  - `full/sections/Main_closure.tex`
  - `full/sections/Weil_linkage.tex`
  - `full/sections/scope_notation.tex`
  - `full/sections/A3/symbol_floor.tex`
- control docs:
  - `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
  - `q3.lean.aristotle/docs/PAPER_MAINLINE_TRACKER.md`
  - `IMPLEMENTATION_PLAN.md`

## What survived review

- Live repo really does define `W_K` as a broad cone of even, nonnegative,
  compactly supported tests, not as a positive-definite/convolution-square cone.
- The note correctly identifies that this issue sits at the `T0/G6` target layer,
  not merely inside the local `G1/G2/G3` closure bridge.
- The local Archimedean sign heuristic survives strongly:
  using the project formula `a(ξ)=log π - Re ψ(1/4+iπξ)`, numerical checks in the
  root venv give
  `a(1.5) ≈ -0.405`, `a(2) ≈ -0.693`, `a(3) ≈ -1.098`.
- For fixed `K`, active prime nodes are finite and discrete, so there are real
  node-free gaps inside `[-K,K]`; sample checks give gap widths
  about `9.38e-06` near `1.55` for `K=1.6` and `7.60e-07` near `1.95` for `K=2.0`.
- Therefore the note gives a credible blocker to the slogan
  “positivity on all of current `W_K`”.
- As a pipeline comparison: the current reset-loop assumes the target cone is fixed
  and attacks `G1-G3`. This note says there may be a still-earlier blocker:
  current target cone itself may be wrong.

## What was rejected or weakened

- Not yet accepted as a full pipeline flip: we have not rebuilt the exact corrected
  cone and have not yet replaced the current Weil interface in paper or Lean.
- Weakened: the note speaks as if the corrected positive-definite cone is already
  fully identified and ready to substitute for `W_K`; that still needs a careful
  theorem-level audit.
- Weakened: “remove shifted A1′ from mainline immediately” is too aggressive as a
  repo action. First we need to verify the target-cone objection cleanly, then
  decide whether A1′ becomes legacy or stays as an auxiliary density theorem.

## Reusable theorem / lemma pointers

- `q3.lean.aristotle/Q3/Basic/Defs.lean:148` — live definition of `W_K`
- `q3.lean.aristotle/Q3/Axioms.lean:357` and `:448` — current AtomCone/A1′ packaging
  still wired to the broad `W_K`
- `full/sections/Main_closure.tex:9` — current paper-level `W_K` contract
- `full/sections/Weil_linkage.tex:3` — current theorem states positivity on the
  whole current Weil cone `\mathcal W`
- `full/sections/A3/symbol_floor.tex:18` and surrounding asymptotics — project
  Archimedean density `a(ξ)`
- `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` — current pipeline assumes target fixed

## Next action

- write a short target-cone audit synthesis into `docs/INSIGHTS.md`
- compare it against the current reset-loop and decide whether a pre-`G1`
  `T0/G6` audit task must become active
- keep the current Aristotle `G1.6` job as background work, but do not let it
  silently decide the mainline if the target-cone objection survives

## Notes

Best current interpretation:

- this note is important and real;
- it is not yet the new canonical theorem-chain;
- but it is strong enough that continuing `G1` blindly would be bad engineering.

Recommended project stance after review:

- add a high-priority target-cone audit before spending more narrative capital on
  the current `W_K`-based closure story,
- only after that decide whether the mainline stays
  `T0 -> G1 -> G2 -> G3 -> ...`
  or must be reset to a corrected positive-definite cone.
