# Гол 2 — SOFT_3Q1_DirectHermitianKernelPairingAndSharpLock

Status: `COMPLETE / SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_AND_SHARP_LOCKED / NOT_RH`

## SharpLock

D0.6 fixes `Xi(z)=xi(1/2+i z)`, hence `w=s-1/2=i z`. Transporting the
Mellin involution through this line gives

```text
F^sharp_Z(z)=conj(F(conj z)).
```

The `V_1` plant at `m=13`, `x=0.73` gives

```text
correct |B_1(x)|^2                =  0.3420117523
wrong B_1(x)conj(B_1(-x))         = -0.1849693784
relative difference               =  0.5269811307
even control difference           =  0
```

Thus the convention substitution fires
`SOFT_3Q1_SHARP_COORDINATE_MISMATCH` on the odd/non-even basis element and is
silent on an even `Xi`-type control, exactly as registered.

## Direct Fubini identity

The D0.6 negative exponent gives

```text
<F F^sharp,phi>
 = double-integral q(u)conj(q(v)) hat_phi_D06(u-v) du dv,
c_D0.6=1.
```

Absolute integrability is bounded by `||phi||_1 ||q||_1^2`, so Fubini is
legal. The sign `u-v` is derived, not fitted. A complex non-even synthetic
kernel separates `u-v` from `v-u` by relative difference `0.416825`.

Cross-check with a smooth compactly supported complex test whose real part
changes sign:

| cell | direct LHS | Fubini RHS | relative error |
|---|---|---|---:|
| `(13,120)` | `-0.2541649398 - 0.1619025592 i` | `-0.2541649398 - 0.1619025592 i` | `7.87e-15` |
| `(53,120)` | `-0.2553073182 - 0.1642715086 i` | `-0.2553073182 - 0.1642715086 i` | `7.99e-15` |

## Support-away plant against `Psi`

A bump supported in

```text
(15.1678223163, 19.9889424642)
```

lies strictly between the first two persisted sample nodes
`14.1347251417` and `21.0220396388`. Therefore the zero-sampling value is
exactly zero, while the direct real-axis product pairing is
`1.6869406075e-6`. The proposed `Psi` identity is killed with

```text
SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH.
```

## P1–P5 scoring

```text
P1 PASS   direct Fubini kernel identity
P2 FIRED  Psi support-away mismatch
P3 PASS   ZEO sharp is conjugation, not reflection
P4 PASS   sign-changing phi is legal without square decomposition
P5 OPEN   rank-one kernel convergence is the true next wall
```

Artifacts:

- theorem/proof: `SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_THEOREM_2026-07-13.md`;
- measurements: `SOFT_3Q1_KERNEL_PAIRING_CROSSCHECK.json`;
- runner: `soft_3q1_kernel_pairing_crosscheck.py`;
- validator: `validate_soft_3q1_kernel_pairing.py`.

The central identity never uses `Psi`. No RH claim or rank-one convergence
claim is made. Bus 010 was not created.
