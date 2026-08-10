# GOAL 057 · B3.0AH closeout — exact odd-tail divided difference at m = 13

Date: 2026-08-10  
Route: `CHALLENGER_NOT_RH`  
Result: `GOAL057_B3_0AH_ODD_TAIL_DIVIDED_DIFFERENCE13_PROVED`

## What closed

The new production file
`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarOddTailDividedDifference13.lean`
proves the exact source algebra needed before any odd-tail norm estimate:

1. `ccmBetaScalar_neg`: the central-column source scalar is odd;
2. `ccmWeilOddEntry_eq_beta_dividedDifference`: for `0 < n < k`,
   `tau(k,n) - tau(k,-n)` is exactly
   `2 * (n*beta(k) - k*beta(n)) / (k^2 - n^2)`;
3. `sum_ccmWeilOddEntry_smul_eq_beta_cancellation`: an arbitrary finite
   corrected residual row in a real module splits exactly into its two
   source-beta moments before a norm is taken;
4. `ccmWeilOddEntry13_eq_beta_dividedDifference`: the literal `m = 13`
   specialization used by the G-LOWER odd sector.

The child consumes the existing exact source theorem
`CCMFiniteWeilSourceCommutator.ccmWeilTau_structured_offdiag`; it does not
reconstruct the source formula numerically or by a generated backend.

## Why this child was selected

The Phase-4 audit says that `OddTailGradedResolventBound13` must preserve the
divided-difference cancellation before applying norms.  The repository had the
generic off-diagonal beta theorem, but no public odd-sector collapse or
corrected-row sum identity.  Closing that seam first makes the next analytic
interface source-faithful and prevents a return to the killed raw-residual or
constant-floor surrogate.

The whole-repository preflight also found no existing infinite source CCM
operator or infinite outer-block inverse.  The mode-four Jacobi/Schur files are
about the PSWF recurrence and are not a supplier for the source-Weil odd
matrix.  They were therefore not reused by resemblance.

## Validation

```text
Lean SHA-256:
  60f186793a8f8bc4b58ebdee14245e905dfb126ca1ff8ffbc795f6e302c4ab97
Shape:
  5816 bytes, 145 newline-terminated lines, final LF
Public surface:
  2 definitions, 4 theorems, 0 private declarations
Proof DB:
  6 / 6 declarations imported; repeat import idempotent
Direct Lean:
  PASS
Target build:
  PASS, 7746 jobs
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

- replacing the odd difference by an odd sum;
- reversing `n*beta(k) - k*beta(n)`;
- deleting the `-k*beta(n)` term.

The foreign staged patch remained byte-identical at
`291e2387203c579f3f56bd5994daa7225c575c06a37fb3144b13e04e6d1b4f7b`.

## Exact boundary

This child does **not** prove:

- summability of the infinite corrected residual family;
- a source-derived beta envelope or moment-remainder bound;
- construction, positivity, or invertibility of an infinite outer block;
- a bound on `R_out* C_out^-1 R_out`;
- `OddTailGradedResolventBound13`;
- Suzuki tail coercivity or a literal odd form core;
- the constant odd floor;
- an associated source-Weil operator or selected `kTrial` domain statement;
- projection-leakage decay, the continuum numerator, `H4a1b`, or RH.

The finite `480 -> 960` nested-Schur PASS remains finite evidence only.
No checkpoint was decremented: `0 / 10` are closed.

## Decision record

- Chosen: expose the exact odd source-beta identity and the finite corrected-row
  cancellation before any norm.
- Rejected: entrywise absolute estimates, raw-residual comparison, importing
  the unrelated PSWF Jacobi Schur machinery, and promoting the finite N=960
  audit to an infinite theorem.
- Reason: the next live object is the inverse-weighted infinite outer
  correction; it must consume the exact cancellation rather than erase it.
- Next minimal step: define and preflight the infinite odd outer-block domain
  and the weakest positivity/invertibility hypotheses under which
  `R_out* C_out^-1 R_out` is a lawful bounded quadratic correction.
- Source of decision: local Codex cartography plus the archived Phase-4 code
  audit and completed finite nested-Schur report; no new Proshka call.

## Standing boundaries

`CHALLENGER_NOT_RH` · `BUS_010 VOID` · `GOAL_055 HOLD` · `H4a1b OPEN` ·
`N480 HOLD` · `PX_RH_CLAIM NOT_MADE`.
