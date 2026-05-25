# Step32F penalty radius receiver report

- commit: pending
- request: continue the active Q3 proof-loop after the interval box receiver;
  close the next algebraic receiver for the penalized form.
- theorem/definition names added:
  - `Q3.Proofs.penaltyMatrix`
  - `Q3.Proofs.penaltyForm_eq_quadForm_penaltyMatrix`
  - `Q3.Proofs.abs_penaltyForm_sub_quadForm_le_quadFormAbsRadius`
  - `Q3.Proofs.penaltyForm_lower_bound_of_midpoint_lower_bound_with_radius`
  - `Q3.Proofs.penaltyForm_lower_bound_of_midpoint_lower_bound_and_radius_floor`
- files touched:
  - `Q3/Proofs/PSD_PenaltyCertificate.lean`
  - `docs/INSIGHTS.md`
  - `ACTIVE/requests/step32f_penalty_radius_receiver/report.md`
- commands run:
  - `lake env lean Q3/Proofs/PSD_PenaltyCertificate.lean`
  - `lake build Q3.Main`
  - `rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_PenaltyCertificate.lean`
  - `git diff --check`
  - `./scripts/check_axioms.sh`
- compile status:
  - `PSD_PenaltyCertificate.lean` passes.
  - `lake build Q3.Main` passes.
  - focused Lean hole scan is clean.
  - `git diff --check` passes.
  - axiom check passes with the expected profile: 3 standard Lean axioms and
    2 documented project axioms.
- result:
  - The raw quadratic-form interval receiver now lifts to the actual
    `penaltyForm M Q tau` by identifying it with the quadratic form of
    `penaltyMatrix M Q tau`.
  - A midpoint lower bound with an explicit radius-energy margin now transfers
    to the analytic penalty form.
  - A generator-friendly scalar-radius-floor variant was added: midpoint lower
    bound `(floor + radFloor) * ||v||^2` plus
    `radiusEnergy <= radFloor * ||v||^2` implies the analytic lower bound
    `floor * ||v||^2`.
- remaining blocker:
  - Need generated/imported concrete radius-floor bounds for the active primary
    `k=11` and control `k=9` coefficient blocks.
- next smallest theorem/import node:
  - Add a finite-dimensional row-sum/radius-floor receiver proving
    `quadFormAbsRadius R v <= radFloor * euclideanEnergy v`, then generate the
    concrete active-block radius floors.
