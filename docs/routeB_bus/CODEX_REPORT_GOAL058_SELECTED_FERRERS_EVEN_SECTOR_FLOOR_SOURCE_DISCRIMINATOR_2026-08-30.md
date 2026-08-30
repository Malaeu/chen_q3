# Goal 058 selected Ferrers even-sector floor source discriminator

```yaml
TASK_ID: GOAL058_SELECTED_FERRERS_EVEN_SECTOR_FLOOR_SOURCE_DISCRIMINATOR
DATE: 2026-08-30
BODY: CODEX
MODE: PAPER_AND_SOURCE_READ_ONLY
STATUS: KILL
RESULT: KILL_SELECTED_FERRERS_EVEN_SECTOR_FLOOR_ON_CURRENT_SOURCE_SHELF
TARGET: SELECTED_FERRERS_EVEN_SECTOR_FLOOR
SOURCE_VERDICT_COMMIT: 7b96eca0121087abdbc69f360d54c703c02fd0c8
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
CLOSES:
  - GOAL058_SELECTED_FERRERS_EVEN_SECTOR_FLOOR_SOURCE_DISCRIMINATOR
  - DIRECT_CURRENT_SHELF_SEARCH_FOR_SELECTED_FERRERS_EVEN_SECTOR_FLOOR
OPENS:
  - SELECTED_FERRERS_EVEN_SECTOR_FLOOR
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - DIRECT_SELECTED_WEIL_EVEN_COERCIVITY_AT_TRIAL_SHIFT
  - SELECTED_WEIL_EVEN_HEAD_TAIL_FESHBACH_COERCIVITY
NEXT_DEPENDENCY_ROOT: SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
```

## Decision

The current paper and Lean shelf contains no exact theorem supplying one fixed
`beta0 > 0`, eventually on the precommitted selected schedule, for the literal
reflection-even compression orthogonal to the exact even component of the
selected trial row at the exact selected Rayleigh shift.

The exact CCM source supplies matrix entries, Hermiticity/real symmetry,
centrosymmetry, reflection commutation and the structured commutator.  The
selected-source modules supply the literal row, reflection, Rayleigh value,
residual and conditional receivers.  None of these is a quantitative lower
bound.  The primary CCM and 2026 simple-even cards explicitly retain
simple-evenness of the truncated Weil form as an open condition; the analogous
prolate theorem concerns a different operator and cannot be transported to the
literal selected Weil matrix without a new analytic theorem.

## Exact missing theorem

For the selected port `P`, one needs a single `beta0 : Real` with `0 < beta0`
such that, eventually in `k`, every complex vector `x` on the carrier
`CCMModeFinite ((selectedFerrersCofinalSourceData P).index k).N` satisfying

```text
ccmComplexReflectionMatrix N *v x = x
```

and orthogonality to the exact even trial component

```text
star ((1/2) • (q_k + J_k *v q_k)) dot x = 0
```

satisfies

```text
beta0 * Re(star x dot x)
  <= Re(star x dot ((K_k - a_k I) *v x)),
```

where

- `K_k = sourceCCMFiniteMatrix ((selectedFerrersCofinalSourceData P).index k)`;
- `J_k = ccmComplexReflectionMatrix ((selectedFerrersCofinalSourceData P).index k).N`;
- `q_k = selectedFerrersFiniteCCMRow P k`;
- `a_k = selectedFerrersFiniteCCMRayleigh P k`.

The quantifier is eventual on the same selected cofinal schedule.  A per-cell
constant, a ground-eigenvalue shift, an unrestricted gap, or a theorem for the
prolate operator is not this contract.

## Shelf audit

- `CCMFiniteWeilSourceMatrix.lean` states its own boundary: no positivity or
  spectral claim.  It proves the literal finite matrix, symmetry and
  centrosymmetry.
- `CCMFiniteWeilSourceCommutator.lean` proves the exact structured commutator;
  it has no sign or uniform spectral-separation conclusion.
- `G6N1SelectedFerrersH2aSourceQuantities.lean` exposes `heven` as a hypothesis
  of the exact selected-source receiver and explicitly lists the even-sector
  floor among the remaining quantitative inputs.
- `G6N1SelectedFerrersWeightedResidualComplementFloor.lean` consumes the same
  fixed `beta0` in both sectors; it does not construct it.
- `G6N1SelectedFerrersGroundParityRealification.lean` derives evenness only
  from an already supplied ground-gap/sector-floor package.  It cannot be read
  backwards as a floor theorem.
- The pinned CCM usage cards call simple-evenness of `QW_lambda` an essential
  missing step.  The 2026 source card again labels it open for the Weil form and
  records the known simple-even result only for the prolate operator.
- The already closed odd-sector discriminator does not supply an even-sector
  theorem and is not reopened.

The required repository-first semantic search was run before this absence
decision.  The broad query overflowed its presentation budget, so the audit was
completed with narrower exact-identifier and source-file searches over the
named shelf; no supplier declaration was found.

## Strongest generic plant

Structure alone cannot imply a uniform even floor.  On `C^3`, let reflection
swap the first and third coordinates and fix the center.  Let the unit trial be
the center vector `q = e_1`, and for `delta > 0` let

```text
K_delta = diag(delta, 0, delta),   a_delta = <q,K_delta q> = 0.
```

Then `K_delta` is Hermitian, commutes with reflection, `q` is exactly even and
unit, and its residual is zero.  The even vector
`(e_0 + e_2)/sqrt(2)` is orthogonal to `q`, but its shifted energy is exactly
`delta`.  Along any schedule `delta_k -> 0`, every structural premise remains
true while no fixed positive `beta0` survives.  Therefore an independent
uniform coercivity input is load-bearing; symmetry, exact Rayleigh choice and
zero residual do not manufacture it.

## Reentry representations

1. **Direct even-form coercivity.**  Supply a primary theorem directly on the
   reflection-even subspace of the localized Weil form, restricted orthogonally
   to the exact selected even trial component, with the literal selected
   Rayleigh shift and a constant uniform on the selected schedule.  Then give
   the exact finite-source/metric crosswalk.
2. **Even head/tail Feshbach representation.**  Split the literal even
   compression into a source-defined finite head and high-mode tail; prove a
   uniform tail floor, an exact head lower bound at the selected shift, and a
   coupling estimate strong enough for a positive Schur-complement constant.
   All constants must be uniform on the same schedule.

Neither representation is present on the current shelf.  Reentry requires new
mathematics, not a receiver, numerical cell, changed family, or ground-shift
substitution.

## Closeout

This report kills only the current source-acquisition transaction.  It does not
refute the even-sector floor, close the eventual complement floor, establish a
simple even Weil ground state, promote Route B, or make an RH claim.  No Lean
file, numerical experiment, Aristotle request, or foreign mode-four path was
touched.

The next independent production input named by the consolidation graph is
`SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE`; selecting an executable attack
on it requires the next physical Goal 058 rerank and must not silently reimport
the killed Satz9/Fuchs transaction.
