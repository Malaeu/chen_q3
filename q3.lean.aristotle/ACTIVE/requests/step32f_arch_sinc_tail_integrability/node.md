# Codex request: Step32F Arch sinc-tail integrability

## Task

Prove the tail integrability theorem:

```lean
a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
```

or the closest local naming convention.

This is the next exact node after commit:

```text
97e58bc1 [MacOS][rh_clean] Add Arch packet transform bridge
```

Do not try to prove all of:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

in one step unless the tail theorem closes first.

## Context

The previous node closed the finite packet transform bridge:

```lean
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_eq_sum
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
```

and added sinc bounds:

```lean
realSinc_eq_sinc
realSinc_abs_le_one
realSinc_le_inv_abs
realSinc_abs_le_inv_abs
```

The remaining analytic lock is:

```text
a_star has linear growth
*
realSinc(c*t)^(2*k+2) has enough decay for 0 < k
->
Arch t-side integrability
```

The theorem is needed downstream for:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
centeredBSplineArchPairing
centeredBSplinePacketTranslationArchData_ofPairing
```

## Target file

Primary:

```text
Q3/Proofs/PSD_CenteredCardinalBSpline.lean
```

Only create a new file if the proof becomes structurally too large:

```text
Q3/Proofs/PSD_CenteredBSplineArchIntegrability.lean
```

Do not create unrelated files.

## Required first search

Search the repo for:

```text
a_star_linear_growth
a_star
centeredBSplineImagTransformRealClosedForm
centeredBSplineImagTransformClosedForm
centeredBSplineImagTransformProfile_eq_closedForm
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_closedForm_sum
realSinc_eq_sinc
realSinc_abs_le_one
realSinc_le_inv_abs
realSinc_abs_le_inv_abs
Real.sinc
Integrable
MeasureTheory.Integrable
intervalIntegrable
AEStronglyMeasurable
Filter.Tendsto
pow
norm_num
```

Then run local checks:

```lean
#check a_star_linear_growth
#check centeredBSplineImagTransformRealClosedForm
#check centeredBSplineImagTransformClosedForm
#check centeredBSplineImagTransformProfile_eq_closedForm
#check realSinc_abs_le_one
#check realSinc_abs_le_inv_abs
```

Use exact signatures found in the repo. Do not guess theorem types.

## Desired theorem shape

Prefer something like:

```lean
theorem a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
    {k : Nat} {ell : Real}
    (hk : 0 < k) (hell : 0 < ell) :
    Integrable (fun t : Real =>
      Q3.a_star t *
        (centeredBSplineImagTransformRealClosedForm k ell t)^2) := by
  ...
```

If the local Arch integrand uses absolute values or norms, use the local
expression exactly.

## Mathematical route

Use the positive-degree branch:

```lean
hk : 0 < k
hell : 0 < ell
```

Expected proof skeleton:

1. Rewrite `centeredBSplineImagTransformRealClosedForm` as:

```text
constant * realSinc(ell*t/(2*s_k))^(k+1)
```

2. Square it:

```text
constant^2 * realSinc(...)^(2*k+2)
```

3. Use `a_star_linear_growth`:

```text
|a_star t| <= C0 + C1 * |t|
```

4. Split the real line into compact and tail if needed.

5. On the tail use:

```lean
realSinc_abs_le_inv_abs
```

to dominate:

```text
|realSinc(c*t)|^(2*k+2) <= C / |t|^(2*k+2)
```

6. Since `0 < k`, we have `2*k+2 >= 4`, so the tail is integrable.

## Suggested helper lemmas if needed

Only add these if genuinely missing:

```lean
realSinc_pow_abs_tail_bound_of_pos_degree
linear_growth_mul_realSinc_pow_integrable_of_pos_degree
a_star_mul_realSinc_pow_integrable_of_pos_degree
centeredBSplineImagTransformRealClosedForm_sq_bound
```

Keep helper statements narrow. Do not overgeneralize.

Preferred fallback target if the full theorem blocks:

```lean
theorem a_star_mul_realSinc_pow_integrable_of_pos_degree
    {k : Nat} {c : Real}
    (hk : 0 < k) (hc : c != 0) :
    Integrable (fun t : Real =>
      |Q3.a_star t| * |realSinc (c*t)|^(2*k+2)) := by
  ...
```

Then instantiate it for `c = ell / (2 * bsplineScale k)`.

## Hard constraints

* No new `sorry`.
* No new `admit`.
* No new `axiom`.
* Do not touch `Q3.Main`.
* Do not weaken existing theorem statements.
* Do not create another receiver layer.
* Do not redo transform/profile proofs.
* Do not start Prime assembly.
* Do not start Step 33.
* Do not use numerical evidence as proof.

## Work loop

1. Inspect exact signatures.
2. Prove the generic sinc-tail helper if needed.
3. Prove:

```lean
a_star_mul_centeredBSplineImagTransformRealClosedForm_sq_integrable_of_pos_degree
```

4. If the theorem closes, try the immediate consumer:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

only if it is a small direct application. Otherwise stop and report.

5. Run:

```bash
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
lake build Q3.Main
```

6. Run checks:

```bash
rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
```

If a new file is created, include it in all checks.

## Return report

Write:

```text
ACTIVE/requests/step32f_arch_sinc_tail_integrability/report.md
```

with theorem names added, files touched, exact commands run, compile status,
whether the target is closed, whether it feeds the packet-sum Arch integrand,
remaining blocker, and next smallest theorem if blocked.
