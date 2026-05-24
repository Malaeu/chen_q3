# Codex request: Step32F Arch t-side integrability for translated packet sums

## Task

Prove the t-side Arch integrability theorem:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

or the closest local naming convention.

This is the next local Lean node after commit:

`6c823305 [MacOS][rh_clean] Add packet Laplace integrability`

Do not try to close all of Step 32F. Do not touch `Q3.Main`.

## Context

The previous commit added:

```lean
centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
```

This closes the x-side / Laplace-input layer for finite translated B-spline
packet sums.

The current target is the t-side Arch integrand layer:

```text
finite translated packet sum
-> imaginary-axis closed transform
-> Arch integrand is L1 in t
-> centeredBSplineArchPairing is well-defined on packet sums
```

This is needed before finishing the concrete Arch pairing linearity/bilinearity
proof consumed by:

```lean
centeredBSplinePacketTranslationArchData_ofPairing
PacketTranslationKernelData.ofPairing
realBilinearFormOfPairing
```

## Target files

Primary:

```text
Q3/Proofs/PSD_CenteredCardinalBSpline.lean
```

Secondary, only if the theorem naturally belongs there:

```text
Q3/Proofs/PSD_BSplineTranslationIdentities.lean
```

Do not create a new file unless imports become genuinely unmanageable.

## Required first search

Search the repo for:

```text
centeredBSplineArchIntegrand
centeredBSplineArchPairing
centeredBSplineArchPairing_scaledTranslated_closed
centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
centeredBSplineImagTransformProfile_eq_closedForm
centeredBSplineImagTransformClosedForm
centeredBSplineImagTransform_scaledTranslated_eq_closedForm
centeredBSplineImagTransform_scaledTranslated_pair_re_closedForm
centeredBSplineImagTransformRealClosedForm
realSinc
a_star_linear_growth
Integrable
MeasureTheory.Integrable
intervalIntegral
Finset.sum
complexBumpLaplace_add_of_integrable
```

Then run local checks:

```lean
#check centeredBSplineArchPairing
#check centeredBSplineArchPairing_scaledTranslated_closed
#check centeredBSplineTranslatedPacket_complexBumpLaplace_imag_integrable
#check centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
#check centeredBSplineImagTransformProfile_eq_closedForm
#check centeredBSplineImagTransform_scaledTranslated_eq_closedForm
#check centeredBSplineImagTransform_scaledTranslated_pair_re_closedForm
#check a_star_linear_growth
```

Use exact discovered signatures. Do not guess theorem types.

## Desired theorem shape

Prefer a theorem shaped like:

```lean
theorem centeredBSplineArchIntegrand_translatedPacketSum_integrable
    {k : Nat} {ell : Real} (hk : 0 < k) (hell : 0 < ell)
    (...) :
    Integrable (fun t : Real =>
      Q3.a_star t *
      <the Arch imaginary-axis packet-sum integrand>)
```

or whatever exact local Arch integrand definition already exists.

If the repo has a named function such as:

```lean
centeredBSplineArchIntegrand
```

then target:

```lean
Integrable (centeredBSplineArchIntegrand ...)
```

Do not invent a parallel Arch integrand if one already exists.

## Mathematical route

Use the positive-degree branch:

```lean
hk : 0 < k
hell : 0 < ell
```

Expected proof ingredients:

1. finite packet sum transforms are legal on the imaginary axis, using:

```lean
centeredBSplineTranslatedPacketSum_complexBumpLaplace_imag_integrable
```

2. rewrite the imaginary-axis transform using the closed form:

```lean
centeredBSplineImagTransformProfile_eq_closedForm
centeredBSplineImagTransform_scaledTranslated_eq_closedForm
```

3. reduce absolute value to a finite-sum bound times sinc-power decay.

4. use phase boundedness:

```text
|exp (I * t * u)| = 1
|cos (t * x)| <= 1
```

depending on the local expression.

5. use `a_star_linear_growth` to dominate the Arch weight by linear growth.

6. prove integrability from sinc-power decay.

For `0 < k`, the power is strong enough:

```text
realSinc(...)^(2*k+2)
```

decays faster than `1 / |t|^2` after multiplying by linear growth, at least away
from a compact interval. Use existing realSinc bounds if present; otherwise add
the smallest local helper.

## Suggested helper lemmas if needed

Only add these if they are genuinely missing:

```lean
realSinc_abs_le_one
realSinc_pow_decay_integrable_of_pos_degree
a_star_mul_realSinc_pow_integrable_of_pos_degree
centeredBSplineImagTransformClosedForm_abs_bound
centeredBSplineTranslatedPacketSum_imagTransform_abs_bound
```

Keep helper statements narrow. Do not overgeneralize.

## Obstruction wall comment

Add this near the final theorem:

```lean
/-
Q3 obstruction wall:
- wall: Matrix-identification / Prime-side-adjacent Arch form
- role: Step32F Arch t-side well-definedness
- input: x-side packet Laplace integrability, imaginary-axis sinc profile, a_star linear growth
- output: Arch integrand for finite translated B-spline packet sums is integrable in t
- reviewer question answered: is the Arch pairing an actual analytic L1 form on packet sums, rather than a formal profile wrapper?
-/
```

## Hard constraints

* No new `sorry`.
* No new `admit`.
* No new `axiom`.
* Do not touch `Q3.Main`.
* Do not weaken existing theorem statements.
* Do not create another receiver layer.
* Do not redo the sinc profile unless a tiny bound lemma is required.
* Do not start Prime assembly.
* Do not start Step 33.
* Do not use numerical evidence as proof.

## Work loop

1. Inspect exact signatures.
2. Identify the exact Arch integrand expression.
3. Prove the smallest single-packet or single-pair integrability helper if needed.
4. Lift to finite translated packet sums.
5. Prove:

```lean
centeredBSplineArchIntegrand_translatedPacketSum_integrable
```

6. Run:

```bash
lake env lean Q3/Proofs/PSD_CenteredCardinalBSpline.lean
lake env lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
lake build Q3.Main
```

7. Run hole/axiom checks:

```bash
rg -n "sorry|admit" Q3/Proofs/PSD_CenteredCardinalBSpline.lean Q3/Proofs/PSD_BSplineTranslationIdentities.lean
./scripts/check_axioms.sh
```

## Return report

Write:

```text
ACTIVE/requests/step32f_arch_t_integrability/report.md
```

with:

* theorem names added;
* files touched;
* exact commands run;
* compile status;
* whether `centeredBSplineArchIntegrand_translatedPacketSum_integrable` is closed;
* whether the result now feeds `centeredBSplineArchPairing`;
* remaining blocker, if any;
* next smallest theorem if blocked.
