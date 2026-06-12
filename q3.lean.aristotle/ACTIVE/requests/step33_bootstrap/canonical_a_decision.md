# CANONICAL_A_DECISION

Date: 2026-06-04.

Gate:

```text
Step33A.1-A canonical-A decision fork
```

## Decision

Chosen canonical A:

```text
transformed Step22-Omega Arch-sign A
```

Reason:

```text
Step32/Step33 analytic receiver A is the matrix generated from
centeredBSplineArchKernelProfile, hence from Q3.a_star.

The checked bridge identifies centeredBSplineArchKernelProfile with the
transformed Step22-Omega Arch-sign profile, not with the raw Step22
positive-axis payload.
```

## Evidence

Step32 matrix identification:

```lean
centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm
```

This identifies the centered B-spline Weil form with:

```text
quadForm (matrixSub ArchKernel.matrix PrimeKernel.matrix)
```

where `ArchKernel.matrix` is:

```lean
(centeredBSplineArchPacketCoeffKernelData k ell center hk hell).matrix
```

The Arch kernel profile is defined as:

```lean
centeredBSplineArchKernelProfile k ell x =
  ∫ t : ℝ, Q3.a_star t *
    (ell * cos(t*x) * centeredBSplineImagTransformRealClosedForm(k,ell,t)^2)
```

The active Step33 receiver proves:

```lean
primaryK11AnalyticA i j =
  centeredBSplineArchKernelProfile 11 primaryK11Ell
    (primaryK11Center j - primaryK11Center i)

controlK9AnalyticA i j =
  centeredBSplineArchKernelProfile 9 controlK9Ell
    (controlK9Center j - controlK9Center i)
```

The checked normalization theorem is:

```lean
centeredBSplineArchKernelProfile_eq_step22OmegaEtaTransformedProfileWithArchSign
```

This makes the analytic receiver equal to the transformed Step22-Omega
Arch-sign profile with `eta = 2*pi*xi`, Jacobian, transformed packet argument,
and Arch sign.

## Raw Step22 Status

Raw Step22 positive-axis A is the current finite PSD payload source, but local
search found no checked theorem:

```text
raw Step22 positive-axis A = centeredBSplineArchKernelProfile
```

The canonical-A audit also showed:

```text
DeltaA = A_transformed - A_raw
```

is full rank, not zero on `Qv = 0`, not `Q^T Q`, and not P0-like.

Therefore raw Step22 A cannot be used as canonical merely because it passes the
current PSD sanity checks.

## Consequence

The current finite PSD certificate is for the wrong A relative to the Step32
analytic receiver.

However, the first transformed-A recert feasibility dry-run also fails under
the existing split/P0 architecture:

```text
best primary joint ker(Q) minimum ≈ -9.4614e+01
best control joint ker(Q) minimum ≈ -9.3340e+01
```

Since `tau * Q^T Q` vanishes on `ker(Q)`, penalty weights cannot repair this.

## Next Action

Do not start A CSV / ARadius / radius-floor / LDL migration.

Next valid target:

```text
Search a new transformed-A finite PSD split/P0 model,
or prove a semantic receiver theorem changing Step33A back to raw Step22 A.
```

Current recommendation:

```text
Keep transformed Arch-sign A canonical unless a new Lean theorem proves raw
Step22 positive-axis A is the actual analytic Arch contribution.

Treat the current finite PSD contour as source-incompatible with the canonical
receiver.
```

## Superseding Diagnostic

The follow-up artifact:

```text
ACTIVE/requests/step33_bootstrap/canonical_a_kernel_obstruction.md
```

shows a stronger obstruction: with the current formula contract

```text
C = A - P
```

the transformed Arch-sign A makes `C` negative on `ker(Q)`:

```text
primary min(C|kerQ) ≈ -1.0166261779501350e+02
control min(C|kerQ) ≈ -1.0027231457492014e+02
```

Therefore the immediate next step is no longer a new `P0` split search.  First
resolve semantic sign/location:

```text
raw Step22 receiver
vs -transformed receiver/sign-corrected bridge
vs checked formula-contract sign change.
```

A `PRO_REVIEW_REQUEST` for this choice is in the active Step33 report.

External notation check:
DLMF §5.1 confirms `psi`/digamma notation for Gamma/Psi functions; the
canonical decision above is based on local Lean definitions, not on the
external source.
