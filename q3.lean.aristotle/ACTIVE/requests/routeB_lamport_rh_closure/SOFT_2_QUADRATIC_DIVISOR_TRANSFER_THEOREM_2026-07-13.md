# SOFT_2_QuadraticDivisorTransfer — typed theorem and proof

Status: `PROVED_AS_ABSTRACT_CONDITIONAL_ROOF / LEAN_DIVISOR_CORE_CHECKED / NOT_RH`

Authority: `SOFT_2Q_PRO_VERDICT_PROSHKA_QUADRATIC_2026-07-13.md`,
`CODEX DIRECTIVE`.

## 1. Types

Let

```text
S={z in C: |Im z|<1/2}
```

be a connected strip invariant under conjugation. Fix the D0.6 ZEO
involution

```text
F^sharp(z)=conj(F(conj z)).
```

Let `F_j:S->C` be holomorphic. Put

```text
T=Xi*gamma_0,
gamma_0 in O(S)^x,
H_j=F_j F_j^sharp,
H_T=T T^sharp.
```

The theorem inputs are:

```text
Q1  Z(F_j) subset R for every j;
Q2  {F_j} is locally bounded on S;
Q3  F_j(i/4)=A_* with fixed A_* != 0;
Q4  for every phi in C_c^infinity(I),
      <H_j,phi> -> c <H_T,phi>, with c>0;
Q4a I is a nonempty open real interval contained in S.
```

`Q4` is an ordinary real-axis distributional pairing. It is not a linear
pairing with `F_j`, not a zero sum, and not a pairing with `Xi'/Xi`.

## 2. Theorem

```text
SOFT_2_QuadraticDivisorTransfer

Q1+Q2+Q3+Q4  ==>  every zero of Xi in S is real.
```

The assertion is conditional: it proves no one of `Q1`--`Q4` for the project
family.

## 3. Proof

1. By `Q2` and Montel, every subsequence has a further subsequence
   `F_(j_k)` converging locally uniformly on `S` to a holomorphic `F`.
2. By `Q3`, `F(i/4)=A_*!=0`; hence `F` is not identically zero.
3. Each `F_(j_k)` is zero-free on each connected component of `S\R` by
   `Q1`. Hurwitz on the upper and lower components therefore gives
   `Z(F) subset R`.
4. Local-uniform convergence commutes with the fixed D0.6 involution, so
   `F_(j_k)^sharp -> F^sharp` and
   `F_(j_k)F_(j_k)^sharp -> FF^sharp` locally uniformly.
5. Testing this convergence on `I` and comparing with `Q4` gives the equality
   of distributions

   ```text
   FF^sharp = c TT^sharp  on I.
   ```

   Both sides are restrictions of holomorphic functions. Distributional
   uniqueness first gives pointwise equality on `I`; the identity theorem
   extends it to all of `S`.
6. Zeros of `F` are real. If `F^sharp(z)=0`, then
   `F(conj z)=0`, so `conj z` and therefore `z` are real. Thus every zero of
   `FF^sharp` is real.
7. Let `Xi(z_0)=0`. Since `T=Xi*gamma_0`, `T(z_0)=0`, hence

   ```text
   F(z_0)F^sharp(z_0)=c T(z_0)T^sharp(z_0)=0.
   ```

   Therefore `F(z_0)=0` or `F^sharp(z_0)=0`, and step 6 gives
   `Im z_0=0`. Every zero of `Xi` in `S` is real. QED.

The kernel-checked Lean file
`Q3/Proofs/RouteB/QuadraticDivisorTransfer.lean` proves the last divisor
arrow from the pointwise product identity and separately proves the
zero-free multiplier equivalence

```text
T(z)=0 <-> Xi(z)=0.
```

## 4. Exact role of `gamma_0` being zero-free

The forward RH implication in step 7 uses only
`Xi(z)=0 -> (Xi*gamma_0)(z)=0`; a zero of `gamma_0` cannot hide a zero of
`Xi`. Therefore plant P4 cannot honestly kill that one-way implication.

What zero-freeness locks is the **divisor equivalence**

```text
Div(Xi*gamma_0)|_S = Div(Xi)|_S,
```

including multiplicities. If `gamma_0` has a zero, it contributes an extra
divisor point and the equivalence fails. P4 is typed against this exact
divisor slot, while the RH sub-conclusion is recorded as still one-way valid.

## 5. Four planted validators

### P1 — arbitrary unit phases

For `|eta_j|=1`, set `G_j=eta_j F_j`. Then

```text
G_j^sharp=conj(eta_j)F_j^sharp,
G_jG_j^sharp=F_jF_j^sharp.
```

All hypotheses and the conclusion are unchanged. Result:
`P1_PHASE_GAUGE_THEOREM_LIVES`.

### P2 — delete real-zero roof

Use the symmetric strip `|Im z|<2` and

```text
F(z)=z-i,       F^sharp(z)=z+i,
FF^sharp=z^2+1.
```

The product identity and a nonzero anchor can hold, while `F` has the
nonreal zero `i`. Thus deleting `Q1` kills the general theorem. The wider
strip is necessary because the literal planted points `+/-i` lie outside the
project strip `|Im z|<1/2`; the rescaled in-strip version is
`z-/+i/4`. Result: `P2_REAL_ZERO_HYPOTHESIS_REQUIRED`.

### P3 — replace `TT^sharp` by `Xi'/Xi`

The target type is

```text
HolomorphicHermitianProduct(S,T,T^sharp).
```

`Xi'/Xi` is a meromorphic logarithmic derivative with poles at zeros and is
not a value-product `TT^sharp`. It cannot inhabit the target type. Result:
`P3_TARGET_LOG_DERIVATIVE_TYPECHECK_REJECTED` with
`SOFT_C2_TARGET_PRODUCT_MISMATCH`.

### P4 — allow a zero of `gamma_0`

Take `Xi=1`, `gamma_0(z)=z`, `T=z`. Then `Div(Xi)=0` but
`Div(T)=[0]`. The divisor equivalence fails exactly. Result:
`P4_GAMMA_ZERO_DIVISOR_EQUIVALENCE_KILLED`.

## 6. Forbidden-import audit

- no linear pairing with `F_j`;
- no phase reconstruction;
- no critical-line zero sum;
- no post-hoc `gamma_0=F/Xi`;
- no numerical phase evidence;
- no imported RH.

Success:

```text
SOFT_C2_QUADRATIC_DIVISOR_ROOF_LOCKED
```

Scope: abstract conditional roof plus Lean-checked divisor core. `NOT_RH`.
