# Step32F Arch t-side integrability report

## Status

Partial progress.  The full target
`centeredBSplineArchIntegrand_translatedPacketSum_integrable` is not closed yet.

The finite packet-transform part of the node is closed.  The remaining blocker
is now the analytic sinc-tail integrability lemma for `a_star` with linear
growth.

## Theorems added

- `realSinc_eq_sinc`
- `realSinc_abs_le_one`
- `realSinc_le_inv_abs`
- `realSinc_abs_le_inv_abs`
- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_eq_sum`
- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_arch_t_integrability/node.md`
- `ACTIVE/requests/step32f_arch_t_integrability/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

## Compile status

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`: passed
- `Q3/Proofs/PSD_BSplineTranslationIdentities.lean`: passed
- `lake build Q3.Main`: passed
- touched Lean-file hole scan: no matches
- `check_axioms.sh`: passed; 5 axioms total, no `sorryAx`, no sorries in `Q3/`

## Does this close the requested theorem?

No.  It closes the finite packet-sum transform linearity and closed-form
rewriting needed by the requested theorem.

The remaining theorem is the decay/integrability core:

```lean
a_star_mul_realSinc_pow_integrable_of_pos_degree
```

or a local equivalent shaped around:

```lean
Integrable (fun t : ℝ =>
  Q3.a_star t *
    (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
```

for `0 < k` and `0 < ell`, with bounded cosine/phase finite-sum factors.

## Does the result now feed `centeredBSplineArchPairing`?

Not fully.  It provides the packet-sum transform identity needed to expand the
Arch integrand into finite pair terms.  The actual `centeredBSplineArchPairing`
additivity hypotheses still need the `t`-side `Integrable` proof.

## Next smallest theorem

Prove the sinc-tail integrability helper:

```lean
theorem a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    Integrable (fun t : ℝ =>
      Q3.a_star t *
        (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
```

Expected route:

1. use `Q3.a_star_linear_growth`;
2. use `realSinc_abs_le_one` near zero;
3. use `realSinc_abs_le_inv_abs` away from zero;
4. split compact/tail intervals;
5. compare the tail to an integrable rpow majorant using
   `integrableOn_add_rpow_Ioi_of_lt`.
