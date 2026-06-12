# Step33A.1-A Component Endpoint Worklist

- Schema: `q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.v21`
- Status: `component_endpoint_worklist_containment_passed_not_lean_proof`
- Receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds`
- Endpoint mode: `closed_form_shape_value_deriv_endpoint`
- Endpoint cert receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.toComponentIntervalCert`
- ShapeSq derivative reduction: `RawOmegaATaylorModelCertificate.deriv_centeredBSplineImagTransformRealClosedForm_sq`
- Local component endpoint cert: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert`
- Local component endpoint receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.toComponentIntervalCert`
- ShapeSq derivative interval receiver audit-only: `RawOmegaATaylorModelCertificate.shapeSqDeriv_interval_bounds_of_closedForm_value_deriv_intervals`
- ShapeSq derivative Icc receiver audit-only: `RawOmegaATaylorModelCertificate.shapeSqDeriv_interval_bounds_on_Icc_of_closedForm_value_deriv_intervals`
- Local component shape receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_anchor_deriv_interval_enclosures_shapeSq_closedForm_auto_differentiability`
- Omega endpoint cert: `RawOmegaATaylorModelCertificate.Step22OmegaEndpointIntervalCert`
- Local component Omega/shape receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentIntervalCert.of_omega_endpoint_cert_shapeSq_closedForm_auto_differentiability`
- Local component closed-form endpoint cert: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentClosedFormEndpointIntervalCert`
- Local component closed-form endpoint receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentClosedFormEndpointIntervalCert.toComponentIntervalCert`
- Local component closed-form endpoint status: `available_not_active_v19_row_target`
- Omega endpoint closed-form receiver: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_endpointValueDerivIntervalCert_of_closedForm_bounds`
- Omega closed-form endpoint bounds cert: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert`
- Omega closed-form endpoint bounds receiver: `RawOmegaATaylorModelCertificate.Step22OmegaClosedFormEndpointBoundsCert.toStep22OmegaEndpointIntervalCert`
- ShapeSq endpoint bounds cert: `RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert`
- ShapeSq endpoint bounds receiver: `RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals`
- ShapeSq endpoint bounds anchor-value receiver: `RawOmegaATaylorModelCertificate.ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals_anchorValueBounds`
- Local component direct endpoint from Omega/Shape receiver: `RawOmegaATaylorModelCertificate.LocalRawOmegaComponentDirectEndpointIntervalCert.of_omega_shape_endpoint_bounds`
- Omega derivative closed form: `RawOmegaATaylorModelCertificate.step22OmegaArchWeightDerivClosedForm`
- Omega derivative closed-form theorem: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_deriv_eq_closedForm`
- Omega derivative closed-form Icc theorem: `RawOmegaATaylorModelCertificate.step22OmegaArchWeight_deriv_eq_closedForm_on_Icc`
- Shape derivative closed form: `RawOmegaATaylorModelCertificate.centeredBSplineImagTransformRealClosedFormDerivClosedForm`
- Shape derivative closed-form theorem: `RawOmegaATaylorModelCertificate.centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm`
- Shape derivative closed-form Icc theorem: `RawOmegaATaylorModelCertificate.centeredBSplineImagTransformRealClosedForm_deriv_eq_closedForm_on_Icc`
- Rows: `110`
- Endpoint certs open: `110`
- Endpoint facts open: `1320`
- Containment comparisons passing: `220/220`
- Omega containment passing: `110`
- ShapeSq containment passing: `110`
- ShapeSq derivative formula closed by Lean: `110`
- ShapeSq derivative interval receiver closed by Lean: `110`
- ShapeSq derivative Icc receiver closed by Lean: `110`
- Local component shape receiver closed by Lean: `110`
- Omega endpoint cert surface closed by Lean: `110`
- Local component Omega/shape receiver closed by Lean: `110`
- Local component closed-form endpoint cert surface closed by Lean: `110`
- Omega endpoint closed-form receiver closed by Lean: `110`
- Omega closed-form endpoint bounds cert surface closed by Lean: `110`
- ShapeSq endpoint bounds cert surface closed by Lean: `110`
- ShapeSq endpoint bounds receiver closed by Lean: `110`
- ShapeSq endpoint bounds anchor-value receiver closed by Lean: `110`
- Local component direct endpoint from Omega/Shape receiver closed by Lean: `110`
- Omega derivative closed form closed by Lean: `110`
- Omega derivative closed-form Icc theorem closed by Lean: `110`
- Shape derivative closed form closed by Lean: `110`
- Shape derivative closed-form Icc theorem closed by Lean: `110`
- Proof-safe closed fields: `0`

## Worst Rows

- Worst Omega: `primary_finite row=0 parent=1 split=10 sub=5`
  - margin: `2.039176797271670704864736798488E-31`
  - consumed: `6.817578661313297665185095634297E-32`
  - radius: `2.720934663403000471383246361918E-31`
- Worst ShapeSq: `primary_finite row=0 parent=1 split=10 sub=7`
  - margin: `2.478193167974206360136582552343E-35`
  - consumed: `1.191859508354864942464679407312E-35`
  - radius: `3.670052676329071302601261959655E-35`

## Endpoint Obligations Per Row

```text
hOmegaDerivLower
hOmegaDerivUpper
hOmegaAnchorLower
hOmegaAnchorUpper
hShapeValueLower
hShapeValueUpper
hShapeDerivLower
hShapeDerivUpper
hShapeAnchorValueLower
hShapeAnchorValueUpper
hShapeSqAnchorLower
hShapeSqAnchorUpper
```

The shape-square derivative bounds are derived by
`ShapeSqEndpointBoundsCert.of_closedForm_value_derivClosedForm_intervals`
from the four corners of `2 * E * E'`.
The optional anchor-value receiver additionally derives
`E(anchor)^2` from tight one-point `E(anchor)` bounds.

## Generated Theorem Targets

- `rawOmegaEndpointClosedFormBounds_generated`
- `rawShapeSqEndpointBounds_generated`
- `rawOmegaEndpointValueDerivIntervalCert_generated`

## Guard

- diagnostic endpoint worklist only; not Lean proof data
- do not edit A CSV, ARadius, radius-floor, or LDL from this artifact
- do not route to Q3.Main, H1, or PO3
- shape derivative facts target the checked closed-form derivative receiver
- active shapeSq derivative facts are derived from closed-form E/E' endpoint intervals
- active v19 shape endpoint facts bound E and the checked closed-form E' receiver, then derive E^2 derivative bounds by four corners
- active v19 anchor-value facts can derive E(anchor)^2 from tight E(anchor) bounds by four corners
- direct E^2 derivative interval probes are audit-only sanity data
- legacy raw endpoint cert is audit-only; active v19 rows instantiate LocalRawOmegaComponentDirectEndpointIntervalCert through Omega/Shape packages
- Omega endpoint value/derivative facts target a single proof-bearing Step22OmegaEndpointIntervalCert per row
- Omega derivative facts should use the checked closed-form receiver before row-index theorem generation
- Omega derivative closed form is Lean-checked as -Im(trigamma(1/4 + i eta/2)) / 2
- Omega closed-form endpoint rows should first instantiate Step22OmegaClosedFormEndpointBoundsCert
- shape-square endpoint rows should instantiate ShapeSqEndpointBoundsCert via of_closedForm_value_deriv_intervals
- shape-square endpoint rows may instead instantiate the anchor-value receiver when tight E(anchor) bounds are available
- component endpoint rows should instantiate LocalRawOmegaComponentDirectEndpointIntervalCert via of_omega_shape_endpoint_bounds
- next proof steps are rawOmegaEndpointClosedFormBounds_generated, rawShapeSqEndpointBounds_generated, then rawOmegaEndpointValueDerivIntervalCert_generated
