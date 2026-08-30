# Codex task — Goal 058 selected Ferrers odd-sector floor source discriminator

Date: 2026-08-30
Status: `ACTIVE_SOURCE_DISCRIMINATOR`
Parent: Goal 058 / selected Ferrers production floors

## Exact target

Determine whether the literal selected Ferrers family has one fixed positive
constant `beta0` and an eventual reflection-odd spectral floor at the exact
selected trial Rayleigh shift:

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

The exact Lean-shaped consumer is the `hodd` input of
`selectedFerrersFiniteCCMComplementFloor_eventually_of_sectorFloors_weightedResidual`.

## Why this is next

- R1 same-ground-family normality is closed as an executable program; its final
  proposed sign/Krein gate merged into the standing G3 nodal-count source gap.
- R2 moving Krylov/Feshbach is independently `KILL`.
- The odd-sector floor is still a direct consumer input and a dependency of the
  eventual complement floor.
- Current foreign uncommitted mode-four/G3 files are out of ownership and must
  not be edited, staged, or used as if committed suppliers.

## Required audit

1. Read the exact current Lean definitions of the selected index, literal CCM
   matrix, reflection-odd sector, and trial Rayleigh shift.
2. Query the shelf before naming any new object.
3. Audit existing source and primary literature for an exact odd-sector lower
   bound or an exact source crosswalk that implies it with a constant uniform in
   the selected cofinal schedule.
4. Check the metric, normalization, coordinate order, and quantifier crosswalk.
5. Use finite cells only as falsifying plants, never as a cofinal proof.

## Exact discriminator output

Return exactly one:

- `TRY_SELECTED_FERRERS_ODD_SECTOR_FLOOR_SOURCE` with a primary theorem,
  bibliographic pin, exact parameter crosswalk, theorem-sized Lean contract and
  two falsifying plants;
- `REPAIR_SELECTED_FERRERS_ODD_SECTOR_FLOOR_VIA_SOURCE_CROSSWALK` if the source
  theorem controls a different but exactly equivalent operator/metric and the
  adapter can be stated without adding a new analytic hypothesis;
- `KILL_SELECTED_FERRERS_ODD_SECTOR_FLOOR_ON_CURRENT_SOURCE_SHELF` if every
  candidate requires an unproved uniform gap, a changed family, a finite-cell
  numerical promotion, or a currently open G3/Route hypothesis.

## Boundaries

- Paper/source read-only until the discriminator is independently reviewed.
- Do not edit or stage foreign mode-four files or foreign control/map changes.
- Do not weaken `eventually`, change the selected family, assume the floor, or
  relabel a generic receiver as a source supplier.
- No Aristotle, Lean implementation, Route promotion, or RH claim before a
  source-ready `TRY`/`REPAIR` verdict.
