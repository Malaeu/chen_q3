# Goal 058 consolidation — Block 2 closeout

```yaml
TASK_ID: GOAL058_CONSOLIDATION_BLOCK2
DATE: 2026-08-28
BODY: CODEX
STATUS: HOLD
SOURCE_TASK: docs/Codex/TASK_2026-08-28_goal058_consolidation.md
SOURCE_COMMIT: 56e144c49cae5f8c2dc80a09f6ca963a17dda88d
BASELINE_HEAD: 7eb60c2840b8fd7ae3ed324c03da4d7149974c45
RH_CLAIM: false
PX_RH_CLAIM: NOT_MADE
CLOSES:
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR_DEPENDENCY_MAP
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR_DEPENDENCY_MAP
OPENS:
  - SELECTED_FERRERS_ODD_SECTOR_FLOOR
  - SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
  - SELECTED_FERRERS_EVEN_SECTOR_FLOOR
  - SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
  - SELECTED_FERRERS_MODE_AND_CHI_RATE_INPUTS
  - SELECTED_FERRERS_EVENTUAL_RESIDUAL_FLOOR_RATIO_LT_ONE
```

## Decision

Both requested ropes remain `HOLD` in their exact consumer forms.  No weaker
floor, finite-prefix replacement, pointwise-only wrapper, independently chosen
subsequence or alternate family was added.

The production quantifier is eventual, not global over the discarded finite
prefix.  The existing theorem
`selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors`
already turns eventual hypotheses into pointwise data on one additive, strictly
monotone cofinal reindex.  Therefore strengthening either source obligation to
all natural indices would add cost without supplying a consumer need.

## Exact HOLD targets

### `SELECTED_FERRERS_ODD_SECTOR_FLOOR`

The missing source theorem must provide one fixed positive constant and the
eventual literal odd-sector inequality on the selected Ferrers family:

```text
exists beta0 : Real,
  0 < beta0 and
  eventually k atTop,
    for every x,
      ccmComplexReflectionMatrix (index k).N *v x = -x ->
      beta0 * Re(star x dot x) <=
        Re(star x dot
          ((sourceCCMFiniteMatrix (index k) -
            Rayleigh(k) * I) *v x)).
```

The exact Lean-shaped version is already exposed as `hodd` by
`selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual`.
No current declaration supplies this hypothesis for the selected family.

### `SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR`

The missing production conclusion must provide one fixed positive constant and
the eventual literal complement-floor predicate:

```text
exists beta : Real,
  0 < beta and
  eventually k atTop,
    complexTrialComplementFloor
      (sourceCCMFiniteMatrix (index k))
      (selectedFerrersFiniteCCMRow P k)
      (selectedFerrersFiniteCCMRayleigh P k)
      beta.
```

The exact receiver
`selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual`
already returns this predicate with `beta = beta0 / 2`, but only after receiving:

1. an eventual even-sector floor at the same fixed `beta0`;
2. an eventual odd-sector floor at the same fixed `beta0`;
3. decay of the selected odd mass;
4. the weighted residual rate
   `sqrt(oddMass k) * sqrt(residualEnergy k) -> 0`.

The generic theorem
`complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual` is the
finite-cell receiver beneath that result.  It is not a source theorem for the
selected family and does not discharge any of the four inputs above.

## Dependency graph

```text
SELECTED_FERRERS_MODE_AND_CHI_RATE_INPUTS
  -> P := selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates ...
  -> selectedFerrersFiniteCCMOddMass P -> 0

SELECTED_FERRERS_WEIGHTED_RESIDUAL_SOURCE_RATE
  -> sqrt(oddMass) * sqrt(residualEnergy) -> 0

SELECTED_FERRERS_EVEN_SECTOR_FLOOR
SELECTED_FERRERS_ODD_SECTOR_FLOOR
  -> selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual
  -> SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR

SELECTED_FERRERS_EVENTUAL_COMPLEMENT_FLOOR
SELECTED_FERRERS_ODD_SECTOR_FLOOR
SELECTED_FERRERS_EVENTUAL_RESIDUAL_FLOOR_RATIO_LT_ONE
selected schedule arithmetic: eventually 2 <= m and 1 <= N  [SUPPLIED]
  -> selectedFerrersTrackedGroundTail_exists_cofinal_reindex_of_eventually_sectorFloors
  -> one same-family cofinal tail with real zeros and pointwise tracking
```

The live odd-mass decay theorem is same-object locked: it constructs the
specific `P` shown above from the mode/chi inputs.  It does not supply odd-mass
decay for an arbitrary contextual `P`.  Likewise, no supplier was found for
`selectedFerrersTrackedGroundResidualFloorRatio P beta k < 1` eventually.
Weighted residual decay does not imply this ratio bound because vanishing odd
mass can mask residual growth; the ratio obligation therefore remains a
separate open input to the downstream tail reindex.  The elementary eventual
`m >= 2`, `N >= 1` schedule bounds are already supplied and are not an open
rope.

## Strongest attacks checked

- A generic H2A.1 receiver cannot be relabelled as a selected-family supplier.
- Odd-mass decay alone does not imply a complement floor; the repository carries
  a planted counterexample and the weighted residual is load-bearing.
- A global family over every `k` is not needed: the existing tail reindex consumes
  eventual data and preserves the selected index, pair and source scale.
- A global algebraic degree count from Block 1 does not imply either sector floor.
- A finite-cell numerical certificate cannot supply a cofinal eventual theorem.

## Search and validation receipts

- `ask.sh` found no exact supplier for either named target outside the task and
  progress documents.
- The live Lean tree, `knowledge.db`, `aristotle_proofs.db` and Cartographer were
  searched before deciding `HOLD`.
- No Lean file, assembly row or generated catalog is changed by this block.
- Route B remains `CHALLENGER / NOT_RH`; Goal 058 remains open;
  `PX_RH_CLAIM: NOT_MADE`.
