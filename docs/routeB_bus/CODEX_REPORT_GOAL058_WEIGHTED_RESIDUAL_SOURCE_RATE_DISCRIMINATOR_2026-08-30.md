# Goal 058 weighted-residual source-rate discriminator

```yaml
TASK_ID: GOAL058_WEIGHTED_RESIDUAL_SOURCE_RATE_DISCRIMINATOR
DATE: 2026-08-30
BODY: CODEX
MODE: PAPER_AND_SOURCE_READ_ONLY
STATUS: KILL
RESULT: KILL_SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE_ON_CURRENT_SOURCE_SHELF
TARGET: SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
SOURCE_SELECTION_COMMIT: 93f66d31c6e942a248f6a9e9cc4bd2f23534fa11
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
CLOSES:
  - GOAL058_WEIGHTED_RESIDUAL_SOURCE_RATE_DISCRIMINATOR
  - CURRENT_SHELF_MODE_CHI_TO_WEIGHTED_RESIDUAL_SOURCE_RATE
OPENS:
  - SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
  - SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE
  - SELECTED_FERRERS_DERIVATIVE_LEVEL_SOURCE_CONTRACT
```

## Decision

The exact weighted-residual consumer remains

```text
sqrt(selectedFerrersFiniteCCMOddMass P k) *
  sqrt(selectedFerrersFiniteCCMResidualEnergy P k) -> 0
```

on the selected cofinal schedule.  The current Lean tree contains exact
identities and conditional receivers for this object, but no unconditional
source-rate supplier from the current mode/chi or source package.  The selected
current-shelf transaction is therefore `KILL`; the mathematical source rate is
not disproved and becomes a recheckable research debt.

## Strongest exact on-disk chain

The source object is already locked without a surrogate:

1. `selectedFerrersFiniteCCMCommutatorResidualDefect_eq_modeDiag_residual`
   identifies the literal commutator defect with the mode-weighted Rayleigh
   residual `D_k r_k` entrywise.
2. `selectedFerrersFiniteCCMCommutatorResidualDefectEnergy_eq_modeWeightedResidualEnergy`
   identifies the corresponding energies exactly.
3. `selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_commutatorRatio`
   proves the required consumer from decay of the exact weighted commutator
   ratio.
4. `selectedFerrersFiniteCCMWeightedResidual_tendsto_zero_of_logWeightedCommutatorEnergy_of_modeAndChiRates`
   combines the mode/chi center floor with the additional hypothesis
   `L_k * oddMass_k * GammaEnergy_k -> 0`.
5. `selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual`
   consumes the resulting weighted residual together with the independent
   sector-floor inputs.

Thus the receiver and all representation crosswalks are present.  The missing
mathematics is precisely a source theorem implying the additional scalar rate;
restating any of the five declarations above would add no delta.

## Why the current source inputs do not close it

The prior source-rate preflight
`H2A_4_1B_3C_1_0_SELECTED_FERRERS_LOG_WEIGHTED_COMMUTATOR_SOURCE_RATE_PREFLIGHT_2026-08-23.md`
already tested the same shelf and exact consumer.  Its result
`HMODE_HCHI_INSUFFICIENT_FOR_GAMMA_SOURCE_RATE` remains applicable:

- the known odd-mass estimate reduces sufficiency to a subcritical envelope
  for `GammaEnergy_k`;
- the current mode/chi contracts are value/Hilbert controls, not the required
  derivative or mode-weighted defect control;
- the exact archimedean estimate becomes circular through the unknown
  mode-weighted energy of the selected row;
- absolute W02 and prime estimates are supercritical;
- the cancellation-preserving oscillatory prime estimate is absent.

The present repository-first searches found no newer theorem that changes one
of those premises.  Re-running the same search or formalizing another receiver
would violate the novelty rule.

## Plants and scope

The existing plants remain live:

- a zero beta moment does not control the mode-weighted residual;
- structural commutator cancellation cannot be replaced by componentwise
  absolute bounds;
- weighted-residual decay is load-bearing for the complement-floor receiver;
- weighted-residual decay does not imply raw residual decay after deleting the
  vanishing odd-mass weight.

These plants kill shortcuts only.  They do not prove that no alternative
derivative-level, oscillatory, resolvent, or direct consumer-specific source
interface can exist.

## Verification

- `./ask.sh` was run for the exact weighted-residual source rate, the
  log-weighted commutator source, and a mode-weighted finite-Riesz derivative
  rate; no new exact supplier was found.
- The research-dependency gate and its death-evidence plants passed.
- Direct Lean validation passed for the commutator-defect, center-floor and
  weighted-residual complement-floor modules.
- Observed public axiom profile: `propext`, `Classical.choice`, `Quot.sound`;
  no new axiom, `sorry`, Lean edit, numerical experiment, Aristotle request or
  reviewer dispatch was made.

## Reentry

Reentry requires a named novelty axis and one checked implication to the exact
consumer, for example:

1. a derivative/log-Sobolev source contract for the normalized selected row;
2. a cancellation-preserving oscillatory prime estimate at the selected scale;
3. a direct theorem for `L_k * oddMass_k * GammaEnergy_k -> 0`;
4. a strictly weaker consumer-specific estimate that still yields the eventual
   complement-floor receiver.

This closeout leaves physical Goal 058 open.  It does not supply either sector
floor, the eventual complement floor, ground tracking, Route promotion, or RH.
