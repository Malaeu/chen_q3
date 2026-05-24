# Step32F finite Prime sum coefficient assembly report

## Status

Closed.

## Theorems and definitions added

- `centeredBSplineFinitePrimePacketCoeffPairing`
- `centeredBSplineFinitePrimeKernelProfile`
- `centeredBSplineFinitePrimePacketCoeffPairing_add_left`
- `centeredBSplineFinitePrimePacketCoeffPairing_smul_left`
- `centeredBSplineFinitePrimePacketCoeffPairing_add_right`
- `centeredBSplineFinitePrimePacketCoeffPairing_smul_right`
- `centeredBSplineFinitePrimePacketCoeffBilinearForm`
- `centeredBSplineFinitePrimePacketCoeffPairing_basis_closed`
- `centeredBSplineFinitePrimePacketCoeffKernelData`
- `centeredBSplineFinitePrimePacketCoeffBilinearForm_synth_eq_quadForm`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_finite_prime_sum_coeff_assembly/report.md`

## Verification

Commands run:

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake build Q3.Main`
- `rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

Compile status: passed.

Hole scan: clean for the checked files.

Axiom check: passed with the expected current count:

- 3 standard Lean axioms
- 2 project axioms:
  - `Q3.Weil_criterion`
  - `Q3.prime_term_le_at_t_critical_axiom`

## Result

The Prime-side coefficient receiver now supports a finite weighted sum of
positive and negative shifts:

```text
sum_n weight_n * (r_k((d - shift_n) / ell) + r_k((d + shift_n) / ell)).
```

This is the algebraic receiver needed for finite prime blocks, where concrete
prime terms provide `shift_n = r log p` and
`weight_n = log p / p^(r/2)`.

The assembled finite Prime form is bundled as `PacketKernelPairingData`, and its
quadratic form on synthesized real coefficient vectors is exposed through
`quadForm`.

## Next smallest blocker

Plug the already closed boundary data, Arch coefficient receiver, and finite
Prime receiver into a concrete centered-B-spline analytic/finite-matrix
contract.
