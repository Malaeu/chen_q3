# D0.3.0 — ExactOperatorRegistry decomposition contract

Status: `MATH_PROVED_DEFINITIONALLY / LEAN_INTERFACE_UNPINNED / NOT_RH`

## 1. Refined parent definition

`D0.3 ExactOperatorRegistry` is defined to be the following conjunction:

```text
D0.3a FormRepresentationOperator
AND D0.3b PeriodicScalingOperator
AND D0.3c FiniteFormRieszOperator
AND D0.3d PerturbedScalingCarrierSplit
AND D0.3e ProlateDifferentialExpression
AND D0.3f ProlateSelfadjointRealization
AND D0.3g CanonicalDetectorOperator
AND D0.3h OperatorNonconflationFirewall.
```

The assembly application is `D0.3i`.

This is a legal refinement of the former leaf “type `A_lambda`,
`D_log^(lambda,N)`, detector operators, and `PW_lambda` separately”: it makes
every previously implicit carrier/domain/inner-product slot explicit and adds
the finite Riesz operator needed to prevent the illegal alias
`WeilMat_(m,N)=A_m|E_(m,N)`.

## 2. Decomposition theorem

```text
D0.3
<-> D0.3a AND D0.3b AND D0.3c AND D0.3d
              AND D0.3e AND D0.3f AND D0.3g AND D0.3h.
```

Proof. The left side is the record defined in Section 1. Its eight fields are
exactly the eight conjuncts on the right. The forward direction is record
projection. The reverse direction is record construction. No analytic theorem
or source identity is used. QED.

## 3. Closure rule

The parent `D0.3` remains unproved unless all eight children and the explicit
assembly `D0.3i` are proved. A typed conditional interface does not prove its
hypotheses. A missing source domain or missing detector definition is not
filled by a pilot matrix.

Exit: `D0_3_DECOMPOSITION_LOCKED`

RH status: `NOT_RH`.
