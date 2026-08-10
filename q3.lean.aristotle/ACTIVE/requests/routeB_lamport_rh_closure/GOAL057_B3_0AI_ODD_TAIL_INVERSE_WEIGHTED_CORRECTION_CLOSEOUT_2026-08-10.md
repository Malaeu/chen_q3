# GOAL 057 · B3.0AI closeout — lawful inverse-weighted odd-tail correction

Date: 2026-08-10  
Route: `CHALLENGER_NOT_RH`  
Result: `GOAL057_B3_0AI_ODD_TAIL_INVERSE_WEIGHTED_CORRECTION_INTERFACE_PROVED`

## What closed

The new production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarOddTailInverseWeightedCorrection.lean`
isolates the dimension-neutral operator interface required by the surviving
resolvent-weighted Schur route.

For arbitrary complete complex Hilbert spaces it proves:

1. a positive continuously invertible bounded operator has a positive actual
   `ContinuousLinearMap.inverse`;
2. the inverse really solves the outer-block equation on every residual;
3. `R† ∘ C⁻¹ ∘ R` is a positive bounded correction;
4. its exact action and quadratic pairing use the actual inverse `C⁻¹`;
5. a bounded head operator splits exactly into its Schur complement plus that
   inverse-weighted correction, both as an operator and on quadratic values.

The construction is independent of finite dimension.  It does not use a
spectral theorem, finite diagonalization, or the unrelated mode-four PSWF
Jacobi Schur machinery.

## Why this child was selected

B3.0AH exposed the exact odd source-beta cancellation that must survive until
the outer inverse is applied.  The next ambiguity was whether Lean already had
a lawful generic interface for the actual correction, or whether the project
would again substitute the killed scalar-floor surrogate `d⁻¹ R†R`.

The smallest reusable child was therefore the exact generic operator seam.
This separates a closed algebraic/functional-analytic interface from the still
open source supplier: the literal infinite odd carrier, its outer block, and
proofs that this source operator is positive and continuously invertible.

## Validation

```text
Lean SHA-256:
  ad641d3c5bca57a3ba452d2ac80290428d17e739810fbeef06b7a707833b65cf
Shape:
  6669 bytes, 159 newline-terminated lines, final LF
Public surface:
  1 structure, 2 definitions, 8 theorems
Proof DB:
  10 parser-indexed declarations imported; repeat import idempotent
Direct Lean:
  PASS
Target build:
  PASS, 7747 jobs
Full build:
  PASS, 7817 jobs
Direct Q3/Main.lean:
  PASS
scripts/q3_check.sh:
  PASS
orchestrator tests:
  90 / 90 PASS
SQLite integrity:
  knowledge.db, aristotle_proofs.db, observability.db all OK
Public axiom profile:
  propext, Classical.choice, Quot.sound
External production-import consumer:
  PASS
Forbidden tokens:
  no sorry, admit, native_decide, axiom, or unsafe
```

Three semantic mutants fired:

- replacing `R† C⁻¹ R` by `R† R`;
- asking for inverse positivity without the invertibility supplier;
- reversing the adjoint/composition orientation.

The foreign staged patch remained byte-identical at
`291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b`.

## Exact boundary

This child does **not** construct or prove:

- the literal infinite odd tail Hilbert carrier for the source-Weil matrix;
- a bounded source outer-block operator on that carrier;
- positivity, coercivity, or continuous invertibility of that source block;
- source residual summability or a source beta envelope;
- an explicit bound on the actual source `R_out† C_out⁻¹ R_out`;
- `OddTailGradedResolventBound13`;
- Suzuki tail coercivity, a literal odd form core, or the constant odd floor;
- an associated source-Weil operator or selected `kTrial` domain statement;
- projection-leakage decay, the continuum numerator, `H4a1b`, or RH.

The finite `480 -> 960` nested-Schur PASS remains finite evidence only.
No checkpoint was decremented: `0 / 10` are closed.

## Decision record

- Chosen: the exact dimension-neutral positive/invertible outer-block interface
  and actual inverse-weighted correction.
- Rejected: the scalar-floor replacement `d⁻¹ R†R`, finite-dimensional
  diagonalization, importing the unrelated PSWF Jacobi Schur API by
  resemblance, and treating finite N=960 as an infinite supplier.
- Reason: the next source theorem must provide the real `C_out` and discharge
  positivity plus invertibility; the generic correction should not hide or
  manufacture those hypotheses.
- Next minimal step: construct the literal source odd-tail carrier and outer
  block, then prove the weakest source-derived positive/invertible supplier
  that instantiates this interface while preserving B3.0AH cancellation.
- Source of decision: local Codex cartography and direct Mathlib API proof; no
  new Proshka call.

## Standing boundaries

`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4a1b OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
