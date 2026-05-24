# Step32F Arch t-side integrability report

## Status

Closed.

The requested finite translated packet-sum theorem is now Lean-checked:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

## Theorems added in the closing node

- `centeredBSplineImagTransformClosedForm_continuous`
- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_norm_bound`
- `centeredBSplineArchIntegrandClosed_translatedPacketSum_continuous`
- `centeredBSplineArchIntegrand_translatedPacketSum_integrable`

## Existing prerequisites consumed

- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum`
- `a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree`
- `Q3.a_star_continuous`
- `Complex.norm_exp_I_mul_ofReal`
- `Complex.abs_re_le_norm`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_arch_t_integrability/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

## Compile status

Passed.

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed
- `Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`: passed
- `lake build Q3.Main`: passed
- touched Lean-file hole scan: no matches
- `check_axioms.sh`: passed; 5 axioms total, no `sorryAx`, no sorries in `Q3/`

## Does this close the requested theorem?

Yes.

The theorem:

```lean
theorem centeredBSplineArchIntegrand_translatedPacketSum_integrable
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (k : ℕ) (ell : ℝ) (coeffF : ι → ℂ) (centerF : ι → ℝ)
    (coeffG : κ → ℂ) (centerG : κ → ℝ)
    (hk : 0 < k) (hell : 0 < ell) :
    Integrable
      (centeredBSplineArchIntegrand
        (fun x : ℝ =>
          Finset.univ.sum fun i : ι =>
            coeffF i *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerF i) x)
        (fun x : ℝ =>
          Finset.univ.sum fun j : κ =>
            coeffG j *
              complexScaledTranslatedBump
                (fun y : ℝ => (centeredBSplineEta k y : ℂ)) ell (centerG j) x))
```

is closed.

## Does the result now feed `centeredBSplineArchPairing`?

Yes.  It provides the missing `t`-side `Integrable` hypothesis for finite
translated centered B-spline packet sums.  Together with the existing x-side
Laplace integrability lemmas, it is ready to feed the concrete
`centeredBSplineArchPairing_add_left/right` packet-span wiring.

## Remaining blocker

The next blocker is no longer Arch integrand L1.  The remaining Arch work is the
packet-span bilinearity/wiring step:

```lean
centeredBSplineArchPairing_add_left
centeredBSplineArchPairing_add_right
centeredBSplineArchPairing_smul_left
centeredBSplineArchPairing_smul_right
```

specialized to finite translated packet sums, then passed into:

```lean
centeredBSplinePacketTranslationArchData_ofPairing
```

## Next smallest theorem

A concrete packet-span bilinear wrapper, likely shaped as either:

```lean
centeredBSplineArchPairing_translatedPacketSum_add_left
```

or a bundled theorem that instantiates the four `map_add`/`map_smul` arguments
for finite translated packet sums.
