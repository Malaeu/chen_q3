# SOFT_3Q1_DirectHermitianKernelPairingAndSharpLock

Status: `PROVED_FINITE_FUBINI_IDENTITY / SHARP_LOCKED / NOT_RH`

Authority: `SOFT_3Q1_PRO_VERDICT_PROSHKA_KERNEL_2026-07-13.md` and D0.6.

## 1. SharpLock from the one-line coordinate map

In Mellin coordinates put

```text
w=s-1/2.
```

D0.6 fixes `Xi(z)=xi(1/2+i z)` (line 137), hence literally

```text
w=i z,                     z=-i w.                  (1.1)
```

The source involution in the `w` variable is

```text
Ftilde^sharp_M(w)=conj(Ftilde(-conj w)).
```

Writing `F(z)=Ftilde(i z)` and substituting (1.1),

```text
F^sharp_Z(z)
 =Ftilde^sharp_M(i z)
 =conj(Ftilde(-conj(i z)))
 =conj(Ftilde(i conj z))
 =conj(F(conj z)).                                  (1.2)
```

Thus the ZEO-coordinate sharp is **conjugation**, not reflection. On the real
axis. Canonical grep-lock: `F^sharp_Z(z)=conj(F(conj z))`.

```text
F(x)F^sharp_Z(x)=|F(x)|^2.
```

Using `conj(F(-conj z))` in the `z` variable would double-apply the
coordinate reflection and produce `F(x)conj(F(-x))`.

### Non-even plant

Audit (1.2) on the D0.6 basis transform

```text
B_n(z)=2 L^(-1/2) sin(zL/2)/(z-2*pi*n/L),   n!=0.
```

For a generic real `x`, `B_n(x)^2` differs from `B_n(x)B_n(-x)`, so the wrong
sharp fires `SOFT_3Q1_SHARP_COORDINATE_MISMATCH`. An even control such as
`Xi` has `Xi(-x)=Xi(x)` and masks the error; it is therefore not a validator.

## 2. D0.6-native test transform

D0.6 line 37 fixes the negative exponent and no normalization constant:

```text
F(x)=integral_R q(u) exp(-i*x*u) du.
```

For a real-axis test `phi`, use the same native convention

```text
hat_phi_D06(y)=integral_R phi(x) exp(-i*x*y) dx.     (2.1)
```

No inverse transform is used, so the coefficient is

```text
c_D0.6=1.
```

## 3. Direct finite Fubini theorem

Let `q in L1(R)` have compact support and let `phi in C_c^infinity(I;C)`.
Define `F` by the D0.6 transform above. Then

```text
<F F^sharp_Z,phi>
 = integral_R |F(x)|^2 phi(x) dx
 = double-integral_(R^2)
     q(u) conj(q(v)) hat_phi_D06(u-v) du dv.         (3.1)
```

### Proof

On the real axis, (1.2) gives `F^sharp_Z(x)=conj(F(x))`. Expand:

```text
F(x)conj(F(x))
 = double-integral q(u)conj(q(v))
     exp(-i*x*u) exp(+i*x*v) du dv
 = double-integral q(u)conj(q(v))
     exp(-i*x*(u-v)) du dv.
```

The absolute triple integral is bounded by

```text
||phi||_1 ||q||_1^2 < infinity.
```

Tonelli/Fubini therefore permits exchanging the three integrals. The inner
`x` integral is exactly (2.1) at `u-v`, proving (3.1). The coefficient is one
and the sign is `u-v`; neither was fitted. QED.

The same proof applies to every finite packet `q_(m,N)` and, whenever
`q_inf` satisfies the displayed integrability hypothesis, to the target
kernel for `T=Xi gamma_0`.

## 4. What is not in (3.1)

`Psi` does not occur. The explicit formula produces a zero-sampling
functional; (3.1) is the value-product distribution on the real axis. A
support-away bump between two sampling nodes makes the zero-sampling side
zero while the direct integral remains nonzero. Hence

```text
Psi identity: SOFT_3Q1_ZERO_PRODUCT_TARGET_MISMATCH.
```

Sign-changing complex or real `phi` is legal in (3.1); positivity and a
square decomposition are unnecessary.

## 5. Next wall

The exact finite algebra is closed. The remaining crosswalk is rank-one
kernel convergence

```text
q_(m_j,N_j)(u)conj(q_(m_j,N_j)(v))
  -> c q_inf(u)conj(q_inf(v))
```

in a topology tested by `(u,v) -> hat_phi(u-v)`. This is not proved here.

Closeout:

```text
SOFT_3Q1_DIRECT_HERMITIAN_KERNEL_PAIRING_AND_SHARP_LOCKED
```

`NOT_RH`.
