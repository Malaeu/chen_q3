# Goal 058 selected fixed even-tail cutoff closeout

Date: 2026-09-01
Status: `CLOSED_KILLED_FIXED_TRANSFER`
Route: `CHALLENGER_NOT_RH`
`PX_RH_CLAIM: NOT_MADE`

## Exact result

The existing explicit source-Weil even-tail cutoff cannot be transferred to
the literal selected finite carrier through the premise `cutoff <= N`.
Lean proves, for every natural `k`,

```text
(selectedFerrersPreAnchorIndex k).N
  < sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k).
```

Consequently `cutoff <= N` is false on every selected Ferrers cell, not merely
on a subsequence and not merely eventually.

## Kernel and semantic evidence

```text
SOURCE_COMMIT: bed49f3a0646d2e7d7636ef1d1d7e0978b65d060
JOINT_TASK_SOURCE_PIN: 32cccfcd7717c1734044ac16ed97724d4a480a1b
SOURCE_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarSelectedFerrersEvenTailCutoffObstruction.lean
SOURCE_SHA256: d0485d312cc9dc5c9526c2047c9ceb55c4c26dbb28e499161acc01423d88db53
ADMISSION_COMMIT: 2db4c33daf7b55851cb2d793272c893bf4645eae
ATTESTATION_ID: ATTEST_GOAL058_SELECTED_FIXED_EVEN_TAIL_CUTOFF_OBSTRUCTION_20260901_V1
INDEPENDENT_REVIEW: ADMIT; HIGH=0; MEDIUM=0; semantic LOW=0
DIRECT_LEAN: PASS
TARGET_BUILD: PASS_7894_JOBS
AXIOMS: PROPEXT_CLASSICAL_CHOICE_QUOT_SOUND_ONLY
```

The semantic receipt and detached signature validate the universal quantifier,
strict direction, selected schedule `m = N = k+2`, common odd/even cutoff, and
the fixed-only scope.

## Ledger

```text
CLOSES:
  FIXED_SOURCE_WEIL_EVEN_TAIL_CUTOFF_LE_SELECTED_FERRERS_N
  FIXED_SOURCE_WEIL_EVEN_TAIL_DIRECT_TRANSFER_VIA_CUTOFF_LE_N

REMAINS_OPEN:
  ADAPTIVE_SELECTED_CUTOFF_DOMINATION_R_LE_N
  DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY
  SELECTED_RAYLEIGH_UPPER_ENVELOPE
  FINITE_EVEN_HEAD_CORRECTED_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

```text
AUTOPSY: dropped=LOCALIZATION; note=the explicit source-Weil cutoff starts strictly beyond the literal selected finite carrier on every selected Ferrers cell
```

## Next branch decision

The next local node is `DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY`.

This is selected before an adaptive-cutoff package because the exact consumer
needs a finite selected-`N` sector floor, while an adaptive construction adds a
new cutoff and the separate domination debt `R_k <= N_k`. The direct node asks
for the weakest form estimate on the carrier the consumer already owns.

The adaptive branch remains alive if the direct selected-`N` preflight finds a
source-faithful cancellation mechanism that must be expressed through a
cell-dependent cutoff. Neither branch removes the independent finite-head
corrected Schur-margin obligation.

No Route promotion or RH claim occurs.
