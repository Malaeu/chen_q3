# D0.4 — ExactParitySectors

Status: `MATH_PROVED / SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Exit: `EXACT_PARITY_SECTORS_LOCKED`.

This leaf packages the exact inversion/parity structure already proved for the
canonical finite Weil carrier. It makes no global-bottom-three ordering,
strict-gap, simple-ground, or numerical parity-cleanliness claim.

## 1. Inversion on the full window

For `f in H_m=L2([lambda^-1,lambda],du/u)`, define

```text
(Inv_m f)(u)=f(u^-1)       a.e.
```

The interval is invariant under `u -> u^-1`, and Haar measure is invariant:

```text
integral |f(u^-1)|^2 du/u = integral |f(v)|^2 dv/v.
```

Consequently

```text
Inv_m^2=I,
Inv_m^*=Inv_m,
||Inv_m f||=||f||.
```

Thus `Inv_m` is a selfadjoint unitary involution on `H_m`.

## 2. Exact action on Fourier modes

With `x=log(lambda*u)` and `L=2 log(lambda)`, inversion sends

```text
x -> log(lambda/u)=L-x.
```

Therefore

```text
V_n_m(u^-1)
 = L^(-1/2) exp(2*pi*i*n*(L-x)/L)
 = V_-n_m(u).
```

The restriction of `Inv_m` to `E_m_N` is exactly the D0.3g involution
`R_m_N`.

## 3. Full and finite sectors

Define

```text
Hplus_m  = ker(Inv_m-I),
Hminus_m = ker(Inv_m+I),
Eplus_m_N  = E_m_N intersection Hplus_m,
Eminus_m_N = E_m_N intersection Hminus_m.
```

The spectral projections of the involution are

```text
Pplus=(I+Inv_m)/2,
Pminus=(I-Inv_m)/2.
```

They prove

```text
H_m=Hplus_m orthogonal_direct_sum Hminus_m.
```

On `E_m_N`, the explicit ON bases are

```text
Eplus:  V_0_m, (V_n_m+V_-n_m)/sqrt(2), 1<=n<=N;
Eminus: (V_n_m-V_-n_m)/sqrt(2),        1<=n<=N.
```

Hence

```text
E_m_N=Eplus_m_N orthogonal_direct_sum Eminus_m_N,
dim(Eplus_m_N)=N+1,
dim(Eminus_m_N)=N.
```

## 4. Reduction of the finite Weil carrier

D0.3g proves

```text
R_m_N Mfin_m_N=Mfin_m_N R_m_N.
```

Thus `Eplus_m_N` and `Eminus_m_N` reduce `Mfin_m_N`, and its restrictions
`Mplus_m_N`, `Mminus_m_N` are selfadjoint. Their ordered spectra are the exact
names `epsilon_plus_j(m,N)` and `epsilon_minus_j(m,N)`. The full ordered
spectrum uses `nu_j(m,N)`.

The only universal spectral statement here is the multiset union of the two
sector spectra. This leaf does not assert that the first three full ranks
alternate even/odd/even.

## 5. Parity-cleanliness firewall

The exact theorem concerns `Mfin_m_N=WeilOp_m_N` in the exact ON basis. It does
not certify:

- request-local floating-point parity blocks;
- `G_even`, static Schur `theta_j`, or their truncation errors;
- equality of `theta_j` and exact `nu_j`;
- absence of crossings as `(m,N)` varies;
- strict positivity of `epsilon_plus_2-epsilon_plus_1`.

## 6. Lamport proof

```text
<1>1. Haar invariance under u->u^-1 proves Inv_m is unitary; involutivity
      gives Inv_m^*=Inv_m.
<1>2. The centered log coordinate transforms as x->L-x, proving
      Inv_m V_n=V_-n exactly.
<1>3. The involution projections give the orthogonal full-space split.
<1>4. Symmetric/antisymmetric mode combinations give the finite ON bases and
      dimensions N+1 and N.
<1>5. D0.3g's exact commutation proves both finite sectors reduce Mfin_m_N.
<1>6. The explicit firewall rejects global ordering, strict gap, and pilot
      cleanliness overclaims.
```

Conclusion: `D0.4 = PROVED`. QED.

## 7. Planted falsifiers

- `UNCENTERED_INVERSION`: use `x->-x` instead of `x->L-x`; the phase is wrong.
- `WRONG_MAP`: use `u->lambda^2/u`; the window is not preserved.
- `MISSING_V0`: claim equal sector dimensions; the fixed mode makes them
  `N+1` and `N`.
- `WRONG_PARITY`: put `(V_n+V_-n)/sqrt(2)` in the odd sector.
- `GLOBAL_ORDER`: force full ranks to alternate even/odd/even.
- `PILOT_CLEANNESS`: transfer exact commutation to a numerical Schur build
  without an implementation crosswalk.

## 8. Explicit nonclaims

```text
NO_GLOBAL_BOTTOM_THREE_SECTOR_PATTERN
NO_STRICT_SECTOR_GAP
NO_SIMPLE_EVEN_GROUND
NO_PILOT_PARITY_CLEANNESS
NO_THETA_NU_EQUALITY
NO_H2_H4
NO_D0_ASSEMBLY
NO_RH
```
