# GOAL 057 · B3.0AM closeout — exact shifted odd-head Schur complement

Date: 2026-08-11
Route: `CHALLENGER_NOT_RH`
Result: `GOAL057_B3_0AM_SOURCE_WEIL_SHIFTED_ODD_HEAD_SCHUR_POSITIVITY_PROVED`

## What closed

The production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSourceWeilShiftedOddHeadSchur.lean`
constructs the literal low-odd-head compression of the actual shifted
source-Weil graph operator and eliminates the exact closed infinite odd tail.

At the explicit B3.0AK cutoff it proves:

1. the literal shifted head operator `S† A S` on Euclidean coefficients;
2. its exact pairing with the source-Weil shifted graph operator;
3. positivity of that head compression;
4. the pointwise quadratic estimate
   `⟪R† C⁻¹ R q, q⟫.re ≤ ⟪S† A S q, q⟫.re`;
5. the exact operator Schur complement `S† A S - R† C⁻¹ R`;
6. positivity of that exact Schur complement;
7. the exact decomposition of the head compression into the Schur complement
   plus the actual inverse-weighted correction.

Here `C` is the actual continuously invertible infinite-tail outer block and
`R` is the literal B3.0AL residual. No scalar inverse, raw residual norm, or
finite `N=480/960` surrogate is used.

## Why this child was selected

B3.0AL had already supplied the literal head synthesis, actual residual and
actual `R† C⁻¹ R` correction. Positivity of the full shifted source operator
on the graph vector `S q - C⁻¹ R q` gives the exact Schur inequality without
destroying the block relation or the infinite-tail topology. This was the
cheapest remaining local theorem before the genuine quantitative `c₀`
boundary.

## Validation

```text
Lean SHA-256:
  2e05eff5d21cb6da17f455c015eedf4f5cbc8b6117c898dbb30b57be82ebb1a5
Shape:
  9215 bytes, 222 newline-terminated lines, final LF
Public surface:
  2 definitions + 5 theorems
Private surface:
  2 theorems
Proof DB:
  9 / 9 declarations proven; 201 / 201 Route B files registered
Direct Lean:
  PASS
External production-import consumer:
  PASS for all seven public declarations
Negative scope judges:
  OddTailGradedResolventBound13 export absent; strict c>0 floor not derivable
Target build:
  PASS, 7816 jobs
Full build:
  PASS, 7817 jobs
Direct Q3/Main.lean:
  PASS
scripts/q3_check.sh:
  PASS
Orchestrator tests:
  102 / 102 PASS
SQLite integrity:
  knowledge.db, aristotle_proofs.db, observability.db all OK
Public axiom profile:
  propext, Classical.choice, Quot.sound
Forbidden tokens:
  no sorry, admit, axiom, unsafe, or native_decide
```

## Exact boundary

This child proves nonnegative Schur positivity only for the already-shifted
source-Weil graph operator. The shift is the large global
`sourceWeilLowerBoundConstant`; the result does **not** produce a strictly
positive `c₀` floor for the unshifted source form and does not prove a
cancellation-sensitive graded resolvent estimate.

Therefore `OddTailGradedResolventBound13`, the infinite constant odd floor,
the literal odd form-core theorem, selected `kTrial` operator-domain
membership, projection-leakage decay and the continuum numerator remain open.
The first coarse checkpoint and the ten-checkpoint ledger remain open at
`0 / 10`.

## Decision record

- Chosen: literal Euclidean low head, actual shifted source graph operator,
  exact infinite tail, actual outer inverse and the graph vector
  `S q - C⁻¹ R q`.
- **What was rejected and why:** relabeling semidefinite shifted positivity as
  a strict unshifted `c₀` floor; replacing `C⁻¹` by a scalar; replacing the
  infinite tail by `N=480/960`; or bounding the raw residual before the exact
  block cancellation. Each loses either the required constant, object, or
  cancellation.
- Feared failure: hidden double shifting, confusing positive semidefinite with
  a strict uniform floor, or promoting a finite Schur audit to an infinite
  theorem.
- Source of decision: local Codex cartography and direct Lean proof; no new
  Proshka call and no Aristotle submission.
- Next minimal step: construct the exact unshifted or `c₀`-shifted block
  comparison and prove a cancellation-sensitive strictly positive lower bound
  for its actual infinite-tail Schur complement.

## ACTIONS LOG

- reused B3.0AK actual infinite outer inverse and B3.0AL literal residual;
- proved one source-locked production Lean module;
- validated direct Lean, target/full builds, direct main, q3_check, external
  consumer, two negative scope judges, proof registry, 102 tests, SQLite and
  forbidden-token/axiom audits;
- preserved the unrelated PDF and dependency-local package state;
- made no Proshka call, Aristotle submission, N=480/N=960 run, route
  promotion, Bus 010 action, Goal 055 release, PX claim, or RH claim.

## Standing boundaries

`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4a1b OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
