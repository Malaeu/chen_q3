# Control κ=1 residual coverage

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH.

Completed exactly the missing300 originalκ=1 residual measurements: DH180 and plant120, among m121..300. The remaining60 mid plant measurements already existed and remain original receipts. No best-gap residual was substituted forκ=1.

|Check|Result|
|---|---|
|Missing-cell coverage|300/300; no duplicates or remainingcells|
|Source recipe|Unchanged mid engine,400bit,GL192,eightpanels|
|Quiet frame|Original ordered physical-row convention; native768bit twice MGS then floatQR|
|Baseline source minima|All match originalmetadata within originalfloatguard; all controls remain robustly negative|
|Maximum relative physical constraint residual|1.976e-15|
|Maximum Q orthogonality defect|6.55e-15|
|Minimum recorded row-MGS relative pivot|0.258003|
|Independent dual-span pilots|All6 pass at the same768bits; no source regeneration|
|Maximum row/null projector difference|4.87e-15|
|Maximum row/null δ difference|1.776e-15|

Dual-span pilots use the unchanged original Cauchy polynomial-null constructor on saved A arrays: DH121/200/300 and plant122/200/300. Plant121 was not missing and no local A was generated, so the first missing plant cell122 supplies the sixthpilot. The original last_null function discards its MGS pivot return; this is explicitly recorded rather than invented. Every new row-frame measurement retains its available minimum relativeMGS pivot.

The compact canonical measurement surface is `control_delta_missing.csv`; per-cellJSON preserves provenance, raw constraints, source and frame hashes, and fixed row identities. `control_delta_COVERAGE.json` binds the seven-cell baseline gate and records the existing plant60 receipts. `control_delta_dualspan.csv/json` and `control_delta_checks.json` document validation. Large A/Q/AQ arrays and compiled native code remain local.

The irregular plant120 subset is receipt-availability coverage, not a statistical cohort. Merge it with all existing coverage before any T4 world comparison. This work supplies no spike classification, new separator verdict, interval source bound, root/completeness enclosure, cofinal result or RH claim.
