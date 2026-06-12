# Step33A.1-A Endpoint Lean Emitter Report

- Schema: `q3_psdpd_step33_a_refined_subchunk_endpoint_lean_emitter.v11`
- Status: `blocked_missing_proof_safe_endpoint_bounds`
- Worklist: `q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21`
- Endpoint mode: `closed_form_shape_value_deriv_endpoint`
- Target Lean file: `/Users/emalam/Documents/GitHub/rh_lean_01_2026/q3.lean.aristotle/Q3/Proofs/PSD_CenteredCoeffRawOmegaAEndpointGeneratedImport.lean`
- Rows: `110`
- Endpoint facts open: `1320`
- Proof-safe closed fields: `0`
- Containment passing: `220/220`
- Omega failures: `0`
- ShapeSq failures: `0`
- Legacy corner direct-probe non-containments audit-only: `110`

## Theorem Targets

- `rawOmegaEndpointClosedFormBounds_generated`
- `rawShapeSqEndpointBounds_generated`
- `rawOmegaEndpointValueDerivIntervalCert_generated`

## Worst Rows

- Worst Omega: `primary_finite row=0 parent=1 split=10 sub=5`
  - margin: `2.039176797271670704864736798488E-31`
- Worst ShapeSq: `primary_finite row=0 parent=1 split=10 sub=7`
  - margin: `2.478193167974206360136582552343E-35`
  - consumed: `1.191859508354864942464679407312E-35`
  - radius: `3.670052676329071302601261959655E-35`
  - direct E^2 derivative probe contained by active E/E' corners: `False`

## Route Fork

The active v21 route proves shape endpoint facts for E and the checked closed-form E' receiver, then derives E^2 derivative bounds through ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals.

- A. prove the Omega and shape closed-form endpoint packages, then instantiate LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds
- A1. for shape anchors, use separate tight E(anchor) bounds plus the generated ShapeSqEndpointBounds_of_value_deriv_anchor_value_bounds wrapper
- B. fall back to direct E^2 derivative endpoint facts only if the closed-form E/E' route becomes too expensive
- C. add a stronger shape-specific monotonic/sign receiver if direct endpoint facts become too expensive

Codex recommendation: Use A plus A1 now: v21 corrected E/E' corner containment passes for all rows, keeps the shape derivative proof-source explicit, and lets shape anchors use tight E(anchor) bounds instead of direct E(anchor)^2 facts.

## Guard

- do not emit Lean from Arb/acb endpoint candidates
- do not call Step33A.1-A or A hbox closed from this report
- do not edit A CSV, ARadius, radius-floor, or LDL
- do not touch Q3.Main, H1, or PO3
