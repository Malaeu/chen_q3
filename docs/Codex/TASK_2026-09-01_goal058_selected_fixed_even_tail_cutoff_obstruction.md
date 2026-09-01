# Codex task — Goal 058 selected fixed even-tail cutoff obstruction

Date: 2026-09-01
Status: `KERNEL_GREEN_SOURCE_PACKAGE`
Parent: Goal 058 / selected reflection-even Arch-Prime floor
Source commit: `bed49f3a0646d2e7d7636ef1d1d7e0978b65d060`

## Exact outcome

Test the fixed-cutoff transfer premise exposed by the admitted explicit
source-Weil even-tail estimate.  The selected finite CCM carrier ends at mode
`i.N`; a transfer using the existing fixed cutoff would require

```text
sourceWeilEvenTailCutoff i ≤ i.N.
```

Prove, on every precommitted selected Ferrers cell, the strict opposite:

```text
(selectedFerrersPreAnchorIndex k).N <
  sourceWeilEvenTailCutoff (selectedFerrersPreAnchorIndex k).
```

Implementation path:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
D0PstarSelectedFerrersEvenTailCutoffObstruction.lean
```

## Exact theorem surface

```text
Q3.RouteB.D0Pstar.sourceW02AmbientContinuousSesquilinearForm_norm_lower
Q3.RouteB.D0Pstar.selectedFerrersPreAnchorIndex_N_lt_sourceWeilEvenTailCutoff
Q3.RouteB.D0Pstar.selectedFerrersPreAnchorIndex_not_cutoff_le_N
```

The first theorem proves

```text
2 * L_m i ≤ ‖sourceW02AmbientContinuousSesquilinearForm i‖
```

from the literal central W02 matrix entry and the unit central ambient mode.
The second and third theorems prove the strict cutoff obstruction and its exact
logical negation for every natural `k`.

## Dependency effect

```text
CLOSES:
  FIXED_SOURCE_WEIL_EVEN_TAIL_CUTOFF_LE_SELECTED_FERRERS_N
  FIXED_SOURCE_WEIL_EVEN_TAIL_DIRECT_TRANSFER_VIA_CUTOFF_LE_N

OPENS:
  ADAPTIVE_SELECTED_CUTOFF_DOMINATION_R_LE_N
  DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY
  SELECTED_RAYLEIGH_UPPER_ENVELOPE
  FINITE_EVEN_HEAD_CORRECTED_SCHUR_MARGIN_AT_EXACT_RAYLEIGH_SHIFT
```

The fixed-cutoff theorem itself remains valid.  What is closed is only the
attempt to transfer it into the selected finite carrier through the premise
`sourceWeilEvenTailCutoff i ≤ i.N`.

## Exact interpretation

The public cutoff `R` indexes the normalized physical mode pair
`±(R + 1)`.  Since `R > N` on every selected cell, the first physical mode of
that fixed tail lies outside the literal carrier `[-N, N]`.

The proof uses the exact selected schedule `m = N = k + 2`.  It first obtains

```text
W02(0,0) = 32 * sinh(L/4)^2 / L ≥ 2L,
```

then

```text
bandRadius ≥ exp(2L) = m^2,
cutoffScale ≥ 2L * (bandRadius + 1) > m,
cutoff ≥ cutoffScale.
```

## Non-goals

This task does not prove or claim:

- that every possible or adaptive cutoff lies beyond the carrier;
- an obstruction to `DIRECT_SELECTED_N_EVEN_TAIL_COERCIVITY`;
- a selected Rayleigh upper envelope;
- a selected-shift tail floor;
- a finite-head Schur margin or a full selected-sector floor;
- a complement floor, Route promotion, or RH.

## Verification

```text
direct Lean: PASS
target build: PASS (7894/7894 jobs)
full environment: PASS (378/378 current modules, 3442 declarations)
environment trust: sorryAx 0, nonstandard axioms 0
source scan: no sorry, admit, exact?, native_decide, unsafe, or new axiom
public axioms: [propext, Classical.choice, Quot.sound]
supplier preflight: CANDIDATE_ONLY; no exact existing supplier
git diff --check: PASS
independent semantic review: ADMIT; HIGH/MEDIUM/LOW 0
```

## Semantic quarantine

Kernel acceptance is not semantic admission.  Register one new
`KERNEL_GREEN` entry bound to the exact task blob, source commit/blob, theorem
IDs, consumer, scope, normalization, domain, and quantifiers.  Do not use the
result to close the fixed-cutoff branch in execution state until an independent
`q3_semantic_attestation.v1` receipt admits precisely this obstruction scope.

Route B remains `CHALLENGER / NOT_RH`; `PX_RH_CLAIM: NOT_MADE`.
