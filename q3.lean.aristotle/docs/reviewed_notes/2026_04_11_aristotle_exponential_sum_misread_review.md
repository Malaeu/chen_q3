# Reviewed Note: Aristotle Exponential-Sum Misread

## Source

- raw file: `q3.lean.aristotle/docs/incoming_notes/7dac003e-0ac0-4246-a498-0ff7230530f2-aristotle.tar.gz`
- date: `2026-04-11`
- author / tool: `Aristotle`

## Status

- review status: `reviewed`
- scope: `math`
- safe for embeddings: `yes`

## Extracted files

- `q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/ARISTOTLE_SUMMARY.md`
- `q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/ExponentialSum.lean`
- `q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/Main.lean`

## Core claim

Этот пакет не закрывает наш живой arithmetic endpoint. Aristotle интерпретировал
запрос как стандартную задачу о конечных геометрических суммах
`\sum_{t=0}^{T-1} e^{2\pi i j \alpha t}` и формализовал:

1. равномерную boundedness геометрической суммы при `\alpha \notin \mathbb Z`;
2. затухание `\frac1T |S_\alpha(1,T)| \to 0`;
3. для фиксированного `H` затухание конечного усреднения по `j=1,\dots,H`.

Это hole-free toy result, но он не касается сумм по нетривиальным нулям ζ,
не касается shrinking-target пакета `D2g25/D2g26/D2g29`, и не даёт контроля
на частотах `j \lesssim T^2/\log T`.

## Checked against repo

- Lean files:
  - `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/ExponentialSum.lean`
- TeX files:
  - none
- control docs:
  - `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md`
  - `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md`
  - `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/INSIGHTS.md`

## What survived review

- The run is hole-free at the source level: no `sorry`, `admit`, or `exact?`
  markers appear in the extracted Lean files.
- The formalized statement in
  `RequestProject/ExponentialSum.lean` is a clean warmup lemma family for
  ordinary exponential sums over integer time.
- The run is still useful as a prompt-diagnostic example: malformed or
  underspecified arithmetic prompts get collapsed by Aristotle to the nearest
  textbook geometric-sum theorem.

## What was rejected or weakened

- Rejected as live-mainline progress: it does **not** address sums over zeta
  zeros, only sums over `t : Finset.range T`.
- Rejected as `D2g26` input: the theorem uses fixed finite `H`, while our live
  endpoint needs high-frequency control up to `H(T) \asymp T^2/\log T`.
- Rejected as `D2g29` input: there is no explicit-formula side, no prime-side
  localization, and no shrinking-target majorant.
- Therefore this note does **not** change the live frontier.

## Reusable theorem / lemma pointers

- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/ExponentialSum.lean:16` — `expSum_bound`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/ExponentialSum.lean:32` — `expSum_cesaro_tendsto_zero`
- `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/docs/incoming_notes/extracted/7dac003e_0ac0_4246_a498_0ff7230530f2_aristotle_tar/7dac003e-0ac0-4246-a498-0ff7230530f2_aristotle/RequestProject/ExponentialSum.lean:45` — `cesaro_mean_expSum_tendsto_zero`

## Next action

- Keep this as a reviewed historical memo and prompt-failure example.
- Do **not** promote it into control docs or the live theorem chain.
- If we query Aristotle again on this branch, force the prompt to state
  explicitly that the sum is over nontrivial zeta zeros `\gamma`, not over
  integers `t`, and that the target range is high-frequency `j \le H(T)`.

## Notes

Local `lake build` verification was started in the extracted mini-project, but
full dependency bootstrap was still running during this review pass. So the
source-level no-hole check is verified here; the summary claim “compiles” was
not independently completed to the end in this turn.
