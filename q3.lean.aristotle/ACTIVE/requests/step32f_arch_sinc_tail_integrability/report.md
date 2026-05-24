# Step32F Arch sinc-tail integrability report

## Status

Closed.

The requested tail theorem is now Lean-checked:

```lean
a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
```

## Theorems added

- `realSinc_neg`
- `realSinc_continuous`
- `centeredBSplineImagTransformRealClosedForm_continuous`
- `centeredBSplineImagTransformRealClosedForm_neg`
- `a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_tail_bound`
- `a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree`

## Files touched

- `Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_arch_sinc_tail_integrability/node.md`
- `ACTIVE/requests/step32f_arch_sinc_tail_integrability/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

## Compile status

Passed.

Verification completed with:

- `lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean`
- `lake build Q3.Proofs.PSD_CenteredCardinalBSpline`
- `lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `lake build Q3.Main`
- `rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean`
- `./scripts/check_axioms.sh`

The hole scan found no `sorry`/`admit` in the touched Lean proof files.  The
axiom check passed with the expected 5 axioms: 3 standard Lean axioms and 2
documented project axioms.

## Does this close the requested theorem?

Yes.

The theorem:

```lean
theorem a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
    (k : ℕ) (ell : ℝ) (hk : 0 < k) (hell : 0 < ell) :
    Integrable (fun t : ℝ =>
      Q3.a_star t * (centeredBSplineImagTransformRealClosedForm k ell t) ^ 2)
```

is closed.

## Does it now feed `centeredBSplineArchIntegrand_translatedPacketSum_integrable`?

It closes the scalar analytic tail core needed by that theorem.

The packet-sum theorem is not yet added in this node.  It should now be the next
smallest target, using:

- `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum`
- bounded complex phases / cosines;
- finite sums;
- this new scalar tail integrability theorem.

## Remaining blocker

The remaining blocker is the finite packet lift:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

## Next smallest theorem

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

Expected proof route:

1. rewrite both packet transforms using
   `centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum`;
2. expand the finite product into finite pair terms;
3. bound phases/cosines by `1`;
4. dominate each pair term by a constant multiple of
   `a_star * centeredBSplineImagTransformRealClosedForm^2`;
5. apply
   `a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree`;
6. close by finite sums.
