# Step33A.1-A Raw Step22 Semantic Receiver Audit

Date: 2026-06-04

## Route

```text
Step33A.1-A
Arch-side A hbox
raw Step22 semantic receiver route B after Louise decision
```

Louise chose:

```text
B = prove/change Step33 receiver or assembler semantically to raw Step22 A
```

Candidate theorem proposed by Louise:

```lean
centeredBSplineStep33FiniteAProfile_eq_rawStep22PositiveAxisAProfile
centeredBSplineStep33CProfile_eq_rawStep22A_sub_primeProfile
```

## Local Lean Surface

The current active `A` receiver is not a raw Step22 profile.  It is hardwired
to the centered Arch profile:

```lean
primaryK11AnalyticA i j =
  centeredBSplineArchKernelProfile
    11 primaryK11Ell (primaryK11Center j - primaryK11Center i)

controlK9AnalyticA i j =
  centeredBSplineArchKernelProfile
    9 controlK9Ell (controlK9Center j - controlK9Center i)
```

Source:

```text
Q3/Proofs/PSD_CenteredCoeffBaseAHboxImport.lean
```

The underlying packet kernel data also uses the centered profile directly:

```lean
kernel := fun i j =>
  centeredBSplineArchKernelProfile k ell (center j - center i)
```

Source:

```text
Q3/Proofs/PSD_CenteredCardinalBSpline.lean
```

The active entry-hbox certificate consumes exactly that active analytic
receiver:

```lean
matrixEntrywiseAbsLe
  CenteredCoeffBaseHboxImport.primaryK11AnalyticA
  primaryK11A primaryK11ARadius
```

and similarly for control.

Source:

```text
Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

The formula contract is generic:

```lean
C := matrixSub B.A B.P
```

It does not contain a raw Step22 override.  A raw Step22 choice would have to
enter through the upstream `A` supplied to the analytic formula contract, not
through a local hbox lemma.

## Search Result

No Lean definition/theorem surface was found for:

```text
step22RawPositiveAxisAProfile
rawStep22PositiveAxisAProfile
Step22Omega_A_eq_centeredBSplineArchKernelProfile
```

The raw Step22 positive-axis producer currently exists as the Python generator
source and generated payload convention, not as a Lean semantic receiver for
`ActiveCenteredCoeffEntryHboxCert`.

## B_BLOCKED

The route-B theorem is not a local consequence of current definitions:

```lean
centeredBSplineStep33FiniteAProfile_eq_rawStep22PositiveAxisAProfile
```

would require changing or replacing the active analytic receiver/assembler.
It cannot be proved by unfolding the current Step33A objects, because those
objects unfold to:

```lean
centeredBSplineArchKernelProfile
```

not to the raw Step22 positive-axis payload.

The existing signed receiver prototype is also separate:

```lean
ActiveSignedAEntryHboxCert
ActiveSignedQ3AStarEntryHboxCert
```

and explicitly does not replace the current positive
`ActiveCenteredCoeffEntryHboxCert`.

## Conclusion

Route B is possible only as an upstream semantic contract change, with a new
Weil/Arch assembler theorem.  It is not a Step33A.1 local A-hbox proof.

Unless Louise supplies an exact upstream theorem rewriting the analytic
contract to raw Step22, the next route is not a local hbox proof.

```text
B2 = upstream raw-Step22 semantic assembler theorem
```

The older route-C wording must also be narrowed.  The follow-up non-mutating
sanity checks in:

```text
canonical_a_kernel_obstruction.md
transformed_a_recert_feasibility.md
```

show that `C = centeredA - P` is already negative on `ker(Q)`, and that
regenerating D/R/radius-floor/LDL under the existing split shape does not fix
the boundary-null obstruction.

Required next reviewer question:

```text
B is locally blocked by current Lean definitions.
C1/C2 centeredA-P recert routes are arithmetically blocked by ker(Q)
negativity.

Should Codex pursue:
  B2. exact upstream theorem that raw Step22 positive-axis A is the finite
      analytic receiver through the Weil/Arch assembler;
  S. exact semantic sign-location theorem that retargets Step33A through the
     sign-normalized Arch A used by the finite model?
```
