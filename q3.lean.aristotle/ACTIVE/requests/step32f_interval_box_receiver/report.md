# Step32F interval box receiver report

- commit: pending
- request: continue the active Q3 proof-loop; close the next proof lock after
  the centered coefficient dictionary import.
- theorem added:
  - `Q3.Proofs.quadForm_pointwise_sub`
  - `Q3.Proofs.matrixEntrywiseAbsLe`
  - `Q3.Proofs.quadFormAbsRadius`
  - `Q3.Proofs.abs_quadForm_le_quadFormAbsRadius`
  - `Q3.Proofs.abs_quadForm_sub_le_quadFormAbsRadius`
- files touched:
  - `Q3/Proofs/PSD_PenaltyCertificate.lean`
  - `docs/INSIGHTS.md`
  - `ACTIVE/requests/step32f_interval_box_receiver/report.md`
- commands run:
  - `lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean`
  - `lake build Q3.Main`
  - `rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_PenaltyCertificate.lean ACTIVE/requests/step32f_interval_box_receiver/report.md`
  - `git diff --check`
  - `./scripts/check_axioms.sh`
- compile status:
  - `PSD_PenaltyCertificate.lean` passes.
  - `lake build Q3.Main` passes.
  - focused hole scan is clean.
  - `git diff --check` passes.
  - axiom check passes with the expected profile: 3 standard Lean axioms and
    2 documented project axioms.
- result:
  - Added a Lean-checked algebraic receiver proving that entrywise
    midpoint/radius bounds control quadratic-form perturbation by an explicit
    radius energy.
  - This avoids the false shortcut `analytic matrix = midpoint matrix` and
    prepares the interval-backed bridge into the existing penalty-certificate
    route.
- remaining blocker:
  - Need the penalty-form receiver that combines D/R/Q entrywise boxes with a
    midpoint lower-bound certificate and subtracts a checked radius-error term.
- next smallest theorem:
  - A `penaltyForm` perturbation bound over matrix and boundary-row radius
    boxes, feeding `FinitePenaltyLowerBoundCert`.
