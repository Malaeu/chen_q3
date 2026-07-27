# SOFT_2 — exact kTrial symmetry audit

Status: `REAL_CONJUGATION_SYMMETRY_LOCKED / INVERSION_SYMMETRY_NOT_LOCKED / NOT_RH`

Scope: only the already named D0.1/D0.5 objects.  No new packet, operator,
normalization, or selector is introduced.

## Exact consequence

For `(m,N) in TrialNonzero`, write

```text
k = kTrial_(m,N),
g(x)=k(exp(x)/lambda_m),
B(z)=integral_0^L_m g(x) exp(i z x) dx.
```

D0.5 fixes real source phases for `h_0,h_4`, forms `hTrial` with real
coefficients, applies the real starred-summation construction, projects, and
divides by a positive real norm.  D0.1 fixes the symmetric Fourier basis
`{V_n:-N<=n<=N}`, with

```text
conjugate(V_n)=V_(-n).
```

Thus `E_(m,N)` is stable under conjugation.  Uniqueness of the orthogonal
projection implies that `P_(m,N)` commutes with conjugation.  Consequently

```text
k is real almost everywhere,
c_(-n)=conjugate(c_n),
B(-conjugate(z))=conjugate(B(z)).                               (1)
```

On `B(0)!=0`, both `B(0)` and `Xi(0)` are real, so the SOFT_1 object
`H(z)=Xi(0)B(z)/B(0)` obeys the exact symmetry

```text
H(-conjugate(z))=conjugate(H(z)).
```

For real `x`, (1) says only

```text
B(-x)=conjugate(B(x)),
H(-x)=conjugate(H(x)).                                         (2)
```

This is Hermitian/conjugation symmetry, not pointwise reality.

## What is not locked

Neither D0.1 nor D0.5 proves

```text
k(u^-1)=k(u),
g(L_m-x)=g(x),
c_(-n)=c_n,
B(x) in R,
H(x) in R.
```

In particular, the implication in the informal P-PH1 prose
`B(-x)=conjugate(B(x)) => H(x) real` is false.  A SOFT_2 validator must not
promote C2 from (2).

Conditionally, an additional inversion symmetry `g(L-x)=g(x)` would imply

```text
exp(-i x L/2) B(x) in R,
arg H(x)=x*L/2=x*log(lambda_m) modulo pi.                       (3)
```

Even (3) is a systematic, m-dependent linear phase, so it triggers the
registered `C2_PHASE_FREE` judge in the present fork rather than the constant
phase judge.  The phase probe observes slopes close to `log(lambda_m)`, but
that numerical pattern is not promoted into the absent inversion theorem.

Source pins:

- `D0_1_EXACT_HILBERT_SPACE_AND_NORM.md`, SHA-256
  `72d9bc019e56bfeeddbef4b5ac345cf2d502b334a4d5c3aa23c4270b80ea087b`;
- `D0_5_GROUND_AND_TRIAL_TYPES.md`, SHA-256
  `9cb7a9e34d0d051fc78c9c7a69e71fc91e7c7722f3d8c9a5713469d4f3bd5547`.

Conclusion: `KTRIAL_REAL_CONJUGATION_SYMMETRY_ONLY`.  `NOT_RH`.
