# Гол 1 — SOFT_2_QuadraticDivisorTransfer

Status: `COMPLETE / SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED / NOT_RH`

## Deliverables

- Typed theorem and full proof:
  `SOFT_2_QUADRATIC_DIVISOR_TRANSFER_THEOREM_2026-07-13.md`.
- Kernel-checked divisor core:
  `Q3/Proofs/RouteB/QuadraticDivisorTransfer.lean`.
- Four executable plants:
  `validate_soft_2_quadratic_divisor_transfer.py` and
  `SOFT_2_QUADRATIC_DIVISOR_TRANSFER_PLANTS.json`.

## Plant verdicts

```text
P1 arbitrary unit phases       PASS: product invariant, theorem lives
P2 remove real-zero Q1         FIRED: (z-i)(z+i) on |Im z|<2
P3 target Xi'/Xi               FIRED: meromorphic log derivative is wrong type
P4 gamma_0 has a zero          FIRED on divisor equivalence
```

P4 precision note: a zero of a holomorphic multiplier adds a divisor point;
it cannot hide an existing zero of `Xi`. Thus P4 kills
`Div(Xi gamma_0)=Div(Xi)`, while the one-way implication
`Xi(z)=0 -> (Xi gamma_0)(z)=0` remains valid. The report does not manufacture
a false counterexample to the RH sub-conclusion.

## Validation

```text
lake env lean Q3/Proofs/RouteB/QuadraticDivisorTransfer.lean   PASS
python3 validate_soft_2_quadratic_divisor_transfer.py          PASS
holes (sorry/exact?/admit)                                     NONE
```

No linear reconstruction, critical-line zero sum, post-hoc gauge, numerical
phase proof, or RH import appears. Bus 010 was not created.
