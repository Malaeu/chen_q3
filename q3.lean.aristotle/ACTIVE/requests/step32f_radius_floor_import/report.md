# Step32F radius-floor import report

## Status

Closed.

## Commit

Pending at report creation.

## Request

Generate and Lean-check concrete radius-floor imports for the active Step32F
coefficient blocks:

- primary `k=11`
- control `k=9`

The import should expose D/R penalized radius matrices, scalar radius floors,
positive remaining interval floors, and generic lower-bound adapters
parameterized by future analytic entrywise penalty-box proofs.

## Theorems and declarations added

Generator:

- `scripts/q3_psdpd_step32f_radius_floor_lean_data.py`

Lean module:

- `Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport`

For each of `primaryK11D`, `primaryK11R`, `controlK9D`, and `controlK9R`, the
module adds:

- `*PenaltyRadiusEntryRat`
- `*PenaltyRadiusRat`
- `*PenaltyRadius`
- `*PenaltyRadiusFloorRat`
- `*PenaltyRadiusFloor`
- `*IntervalFloorRat`
- `*IntervalFloor`
- `*PenaltyRadiusRat_nonneg`
- `*PenaltyRadius_nonneg`
- `*PenaltyRadiusTotalRat_eq`
- `*PenaltyRadiusTotal_le`
- `*PenaltyRadiusEnergy_le`
- `*IntervalFloorRat_pos`
- `*IntervalFloor_pos`
- `*MidpointLowerBound_with_radius_floor`
- `*LowerBound_of_penalty_box`

## Files touched

- `scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `Q3/Proofs/PSD_CenteredCoeffRadiusFloorImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_radius_floor_import/report.md`

## Commands run

- `python3 -m py_compile scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `python3 scripts/q3_psdpd_step32f_radius_floor_lean_data.py`
- `lake env lean Q3/Proofs/PSD_CenteredCoeffRadiusFloorImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport`
- `lake build Q3.Main`
- focused hole scan on the new generator and Lean import
- `git diff --check`
- `./scripts/check_axioms.sh`

## Compile status

Passed.

- Python generator compiles.
- Generator reruns and rewrites the Lean import.
- `PSD_CenteredCoeffRadiusFloorImport.lean` passes direct Lean checking.
- `Q3.Proofs.PSD_CenteredCoeffRadiusFloorImport` builds as an importable Lake module.
- `Q3.Main` builds.
- Focused hole scan on the new script and new Lean file has no hole markers.
- `git diff --check` passes.
- `check_axioms.sh` passes with the expected profile:
  3 standard Lean axioms and 2 documented project axioms.

## Notes

This node is a proof-data bridge, not the analytic enclosure proof.  The
generated lower-bound adapters require an `hbox` hypothesis:

```lean
Q3.Proofs.matrixEntrywiseAbsLe
  (Q3.Proofs.penaltyMatrix M Q tau)
  (Q3.Proofs.penaltyMatrix midpointM midpointQ tau)
  penaltyRadius
```

That is the correct next analytic obligation.

## Remaining blocker

The analytic penalty-box hbox proofs are not closed in this node.

## Next smallest theorem

Package the four generated D/R lower-bound adapters into active finite penalty
certificate wrappers for primary `k=11` and control `k=9`, parameterized by
the four analytic penalty-box hypotheses.
