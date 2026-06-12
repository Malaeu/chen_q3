# Step33A.1-A Semantic Assembler Sign Route

Date: 2026-06-04

## Louise Decision

```text
CHOSEN: S
```

Interpretation:

```text
B2 is not a local raw-Step22 hbox patch.
B2 becomes a subtheorem inside S.
```

The next route is an upstream semantic assembler/sign theorem.  Do not emit
new A payloads, do not mutate A CSV/`ARadius`/radius-floor/LDL, and do not
touch `Q3.Main`.

## Why S

Local checks say:

```text
B local raw-Step22 hbox theorem:
  blocked by ActiveCenteredCoeffEntryHboxCert unfolding to
  centeredBSplineArchKernelProfile.

C1 centeredA-P direct recert:
  blocked by negative C on ker(Q).

C2 regenerated D/R/radius-floor/LDL under the existing split shape:
  blocked by the same boundary-null negativity.
```

The finite PSD truth currently points to:

```text
rawStep22PositiveAxisA - P
```

not:

```text
centeredBSplineArchKernelProfile - P
```

Therefore the next theorem must be C-level and assembler-level.  Do not try to
prove:

```lean
rawStep22A = centeredBSplineArchKernelProfile
```

The checks indicate that this is false as a local receiver equality.

## Exact Theorem Shape

Preferred theorem shape:

```lean
theorem centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmega_sub_primeProfile
    (k ell : ℕ) (x : ℝ) :
    centeredBSplineFiniteWeilCProfile k ell x =
      step22PositiveAxisOmegaAProfile k ell x
        - centeredBSplinePrimeKernelProfile k ell x := by
  ...
```

Repo-real names may differ.  The theorem must identify the `C` profile consumed
by the finite Step33 Weil model, not merely an isolated `A` table.

If an A-level helper is needed:

```lean
theorem centeredBSplineFiniteWeilAProfile_eq_step22PositiveAxisOmega_throughAssembler
    (k ell : ℕ) (x : ℝ) :
    centeredBSplineFiniteWeilAProfile k ell x =
      step22PositiveAxisOmegaAProfile k ell x := by
  ...
```

Then the C-level theorem should follow from:

```text
C = A - P
```

## Step33A Adapter Target

After the C-level theorem is checked, add a receiver/adapter:

```lean
theorem activeCenteredCoeffEntryHboxCert_of_step22PositiveAxisOmegaA
    (...) :
    ActiveCenteredCoeffEntryHboxCert := by
  ...
```

This adapter may use:

```text
existing raw Step22 positive-axis A hbox
existing P hbox
existing P0 hbox
```

but only after the assembler theorem identifies that raw Step22 positive-axis A
is the finite model's Arch contribution.

## Failure Boundary

If the C-level theorem fails from definitions, then escalate to:

```text
C = current finite certificate convention is inconsistent with semantic assembler
```

Do not repair that by radius widening or generated payload mutation.

## 2026-06-05 Lean Reduction

Codex named the raw Step22 positive-axis Omega source in Lean:

```lean
step22PositiveAxisOmegaAProfile
step22PositiveAxisOmegaCProfile
```

Codex also named the current centered finite Weil C profile induced by the
existing assembler:

```lean
centeredBSplineFiniteWeilCProfile
```

Checked theorem:

```lean
centeredBSplineFiniteWeilCProfile_eq_step22PositiveAxisOmegaCProfile_iff_archProfile_eq
```

Meaning:

```text
On the existing centered assembler,

  centered finite C = raw Step22 positive-axis C

is equivalent to

  centeredBSplineArchKernelProfile = step22PositiveAxisOmegaAProfile.
```

This is exactly the local Arch equality that the route guard says not to prove
as a local hbox patch, and current numeric audits reject it as a false receiver
equality.

Therefore route S cannot mean:

```text
prove the raw Step22 C theorem against the existing centered C definition.
```

Route S must instead mean:

```text
identify or introduce the upstream finite Weil C assembler/contract whose Arch
contribution is raw Step22 positive-axis Omega, then bridge that contract into
Step33A without mutating A radii/payloads as a proof patch.
```

## 2026-06-05 Louise refinement -- route A inside S

Louise/Pro refinement:

```text
CHOSEN: A
```

Interpretation:

```text
Do not rewrite the existing centered contract C into rawOmegaC.
Do not migrate A to Q3.a_star.
Do not use -Q3.a_star scalar fitting.

Build/use a new upstream semantic receiver:
  raw Step22 positive-axis Omega Arch receiver
  + existing centered finite Prime receiver
  -> raw-Omega finite Weil representation
  -> FiniteWeilMatrixModel over step22PositiveAxisOmegaCMatrix.
```

Compiled route-A backend:

```lean
step22PositiveAxisOmegaWeilForm_eq_quadFormC_of_rawOmegaArchReceiver
step22PositiveAxisOmegaFiniteWeilMatrixModel_of_rawOmegaArchReceiver
Step22PositiveAxisOmegaFiniteWeilReceiver.toFiniteWeilMatrixModel
step22PositiveAxisOmegaRawArchKernelReceiver
step22PositiveAxisOmegaFiniteWeilKernelReceiver
```

Current next target:

```text
The finite PSD/penalty receiver over step22PositiveAxisOmegaCMatrix is now
compiled conditionally through primary/control raw-Omega analytic-boundary
nonnegativity theorems.

Next missing layer:
  primary/control raw-Omega D/R penalty-box hboxes
  with R_rawOmega = A_rawOmega - kappa * P0 and
  D_rawOmega = C_rawOmega - theta * R_rawOmega.
```
