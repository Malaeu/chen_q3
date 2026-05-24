# Step32F Prime shift coefficient receiver bridge report

## Status

Closed.

## Theorems and definitions added

- `centeredBSplinePrimeShiftPacketCoeffPairing`
- `centeredBSplinePrimeShiftPacketCoeffPairing_add_left`
- `centeredBSplinePrimeShiftPacketCoeffPairing_smul_left`
- `centeredBSplinePrimeShiftPacketCoeffPairing_add_right`
- `centeredBSplinePrimeShiftPacketCoeffPairing_smul_right`
- `centeredBSplinePrimeShiftPacketCoeffBilinearForm`
- `centeredBSplinePrimeShiftPacketCoeffPairing_basis_closed`
- `centeredBSplinePrimeShiftPacketCoeffKernelData`
- `centeredBSplinePrimeShiftPacketCoeffBilinearForm_synth_eq_quadForm`
- `centeredBSplinePrimeShiftPacketCoeffPairing_basis_correlation_closed`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_prime_coeff_receiver_bridge/report.md`

## Verification

Commands run:

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake build Q3.Main`
- `rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean || true`
- `./scripts/check_axioms.sh`

Compile status:

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed.
- `Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed.
- `Q3.Proofs.PSD_CenteredCardinalBSpline`: built successfully.
- `Q3.Main`: built successfully.
- Hole scan on touched Lean files: clean.
- Axiom check: passed, 5 total axioms, no new axioms.

## Result

The single-shift Prime-side coefficient receiver bridge is now available.  It
provides a real-bilinear coefficient-space form, identifies its basis entries
with the closed centered B-spline autocorrelation profile, packages the data as
`PacketKernelPairingData`, and exposes the synthesized real-vector quadratic
form through `quadForm`.

The theorem
`centeredBSplinePrimeShiftPacketCoeffPairing_basis_correlation_closed` connects
the receiver basis entry back to the actual translated-packet autocorrelation
integral using `CenteredBSplineAutocorrelationClosedForm_all`.

## Next smallest blocker

Assemble the finite Prime-side form by summing these single-shift receivers with
the prime weights used by the Step32 finite matrix contract.
