# Comparator verification of ZF78 (zeta, Re s > 7/8)

Linux run, 2026-10-07, on the owner's request. This closes the verification boundary named in `DIRECT_Q3_THEOREM_TRANSFER.md` line 11 for the zeta statement only. It does not change the RH status. RH, SP, G1/G3 and the unshifted scalar reserve remain OPEN.

## Result

`leanprover/comparator` on `lean/ComparatorChallenges/QuasiRiemannHypothesis.json` of openai/math @ `adc7f1241b42e322a6451854ab7e4b4c146bf78a`:

```
Build completed successfully (7061 jobs).
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
EXIT 0
```

Log: `/mnt/hdd01/Soft/GitHub/openai-math-check/logs/comparator_qrh.log` (line 3024; sha256 `bafaf51e556d3c539b885c376be205de4f9a0f2fc9974e927162865be3db036f`). Wall time 1:15:03, peak RSS 7.3 GB. The only `sorry` warning in the whole log is the challenge stub (`QuasiRiemannHypothesis.lean:5`).

Verified statement (challenge file, sha256 `065f8c9a01d28db78c8b1bfc5083b535082a2d2aac2230d563f98b8caa812cc5`):

```lean
theorem OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) : riemannZeta s ≠ 0
```

Config (sha256 `46ebb7edc11f69536210f502b4bcbd36bbaf3f0872c16748b6c8ce43991bf320`): solution module `OAI.NumberTheory.DirichletL.Nonvanishing`, `permitted_axioms` = `propext`, `Quot.sound`, `Classical.choice`, `enable_nanoda: false`.

Per the comparator README, success guarantees: (1) the solution theorem has exactly the challenge statement, (2) it uses no axioms beyond `permitted_axioms`, (3) the Lean kernel accepts it.

## Setup

| Item | Value |
|---|---|
| Lean | v4.34.1 (project `lean-toolchain`) |
| Mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` (pinned; cache 8908 files from cache.mathlib.org) |
| comparator | tag v4.34.0, `d03acab154d269c06e60e4de7e4cc85deebff94b`, toolchain overridden to v4.34.1 |
| lean4export | tag v4.34.0, `076e8e57707e813375e8f9da8bf989799ace9680` (= comparator manifest pin), toolchain v4.34.1 |
| landrun | 0.1.18; kernel Landlock ABI v8, so only `--best-effort` (comparator itself passes it) |
| Work dir | `/mnt/hdd01/Soft/GitHub/openai-math-check/` (`RUNBOOK.md`, `logs/`) |

Steps: sparse checkout of `lean/`; `lake update` inside landrun (write access only to the project, a private HOME and cache; network open) — EXIT 0, compatibility patches applied (PNT, rellich-kondrachov, StrongPNT and ten lana-agents packages); then `lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json`. The solution was not built before the comparator run (README assumption 2).

## Trust boundary — what is NOT closed

1. Mathlib's definition of `riemannZeta` is trusted. Note `riemannZeta 1 = (γ − log 4π)/2 ≠ 0` by Mathlib convention; harmless for Re s > 7/8.
2. One kernel only: nanoda was not run (`enable_nanoda: false` in the OpenAI config).
3. Comparator README assumption 1 does not hold literally: `lakefile.lean` and the challenge are OpenAI's. The 335-line lakefile was audited by hand: `run_cmd` and `post_update` only run git clone/checkout/apply/rev-parse/remote on pinned URLs and commits with patches from `lean/patches/`. The 9-line challenge was read and matches the paper statement.
4. landrun ran in best-effort mode on Landlock ABI v8. Tested before the run: reading `$HOME` and writing `/tmp` denied, network blocked. Comparator's own sandbox grants read access to `/`.
5. Only the zeta challenge was run. Dirichlet 7/8, Hecke 7/8 and Siegel challenges were not. Q3's transfer note uses only the zeta statement.
6. The paper's own argument (16 677 lines of LaTeX) is not checked by this; only the Lean proof is.

## Consequence for Q3

ZF78 in `DIRECT_Q3_THEOREM_TRANSFER.md` moves from "external, statement inspection only" to "kernel-checked via comparator, modulo items 1–4 above". The derived consumers (CCM floor exponent 3/8+ε, Suzuki Ψ_(3/8) ≥ 0, tracking threshold a > 3/16) no longer depend on an unverified external premise. Q3 Lean is on v4.26.0, so the OAI declaration cannot be imported directly; a Lean consumer should take ZF78 as an explicit named hypothesis stated with Mathlib's `riemannZeta` (Q3 already reaches Mathlib's zeta through `Q3.rh_iff_mathlib`, `Q3/Proofs/RouteB/MathlibRiemannHypothesisBridge.lean`) and cite this file, not add a new `axiom`.
