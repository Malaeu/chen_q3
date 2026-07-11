# D0.3g — CanonicalFiniteWeilDetector

Status: `MATH_PROVED / SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Progress class: `REPRESENTATION_PROGRESS`.

Exit: `D03G_CANONICAL_WEILOP_LOCKED`.

## 1. Exact finite carrier

For every D0.1 index `(m,N)`, define

```text
Mfin_m_N := WeilOp_m_N : E_m_N -> E_m_N.
```

This is an architectural canonical name for the already proved D0.3c Riesz
operator, not a new operator formula. Its exact registry is:

```text
scalar field     = C
carrier          = E_m_N=span_C{V_n_m: |n|<=N}
dimension        = 2N+1
ordered ON basis = (V_-N_m,...,V_N_m)
Gram             = I_(2N+1)
inner product    = restriction of the standard H_m inner product
action           = unique Riesz action satisfying
                   BW_m_N(f,g)=<Mfin_m_N f,g>
matrix           = WeilMat_m_N in the ordered basis
domain           = all E_m_N
codomain         = E_m_N
selfadjoint      = yes, finite-dimensional standard inner product
parameter regime = every m>=2 and N>=1
```

No pilot implementation participates in this definition. The family is
two-parameter. The one-parameter symbol `M_lambda` remains undefined until an
exact selector/directed-family theorem is proved.

## 2. Parity involution

Define the complex-linear map

```text
R_m_N(V_n_m)=V_-n_m.
```

Because it permutes the D0.1 ON basis,

```text
R_m_N^2=I,
R_m_N^*=R_m_N,
||R_m_N f||=||f||.
```

Thus `R_m_N` is a selfadjoint unitary involution.

## 3. Exact commutation

D0.2 and the primary source give the matrix entries

```text
tau_(i,i)=a_i,
tau_(i,j)=(b_i-b_j)/(i-j)       when i!=j,
a_-j=a_j,
b_-j=-b_j.
```

For diagonal entries,

```text
tau_(-i,-i)=a_-i=a_i=tau_(i,i).
```

For `i!=j`,

```text
tau_(-i,-j)
 = (b_-i-b_-j)/((-i)-(-j))
 = (-b_i+b_j)/(-i+j)
 = (b_i-b_j)/(i-j)
 = tau_(i,j).
```

Hence `WeilMat_m_N` is centrosymmetric. If `J` is the reversal permutation
matrix of `R_m_N`, then

```text
J WeilMat_m_N J = WeilMat_m_N.
```

Equivalently,

```text
R_m_N Mfin_m_N = Mfin_m_N R_m_N.                     (3.1)
```

This is exact algebra, not the request-local numerical parity judge.

## 4. Orthogonal sectors

Define

```text
Eplus_m_N  = ker(R_m_N-I),
Eminus_m_N = ker(R_m_N+I).
```

An explicit ON basis is

```text
Eplus:  V_0_m and (V_n_m+V_-n_m)/sqrt(2), 1<=n<=N;
Eminus: (V_n_m-V_-n_m)/sqrt(2),           1<=n<=N.
```

Therefore

```text
E_m_N = Eplus_m_N orthogonal_direct_sum Eminus_m_N,
dim(Eplus_m_N)=N+1,
dim(Eminus_m_N)=N.
```

By (3.1), both sectors reduce `Mfin_m_N`. The restrictions

```text
Mplus_m_N  := Mfin_m_N restricted to Eplus_m_N,
Mminus_m_N := Mfin_m_N restricted to Eminus_m_N
```

are finite-dimensional selfadjoint operators.

## 5. Exact spectral namespaces

Order eigenvalues with algebraic multiplicity:

```text
nu_1(m,N) <= ... <= nu_(2N+1)(m,N)          full Mfin spectrum;
epsilon_plus_1(m,N) <= ... <= epsilon_plus_(N+1)(m,N);
epsilon_minus_1(m,N) <= ... <= epsilon_minus_N(m,N).
```

The orthogonal direct sum proves the multiset identity

```text
Spec(Mfin_m_N)
 = Spec(Mplus_m_N) multiset_union Spec(Mminus_m_N).    (5.1)
```

No global-rank interlacing pattern is asserted. In particular this leaf does
not assert

```text
nu_1=epsilon_plus_1,
nu_2=epsilon_minus_1,
nu_3=epsilon_plus_2.
```

For `N>=1`, the sector difference

```text
delta_plus_m_N := epsilon_plus_2(m,N)-epsilon_plus_1(m,N)
```

is well typed and nonnegative by ordering. Strict positivity, a uniform lower
bound, and equality with `nu_3-nu_1` are not claimed.

## 6. Provenance firewall

The canonical namespaces are disjoint:

```text
nu_j              exact full Mfin eigenvalues;
epsilon_plus_j    exact even-sector eigenvalues;
epsilon_minus_j   exact odd-sector eigenvalues;
theta_j           static-Schur/LadderLaw diagnostics;
pilotFullEig_j    optional historical name for pilot full-matrix values.
```

The historical `routeb_ladder_pilot.py` assigned `mu1,mu2,mu3` to the first
three full-matrix eigenvalues. The later `ladder_law_v1.py` assigned the same
names to static-Schur `theta` rows. Those meanings are not exact aliases and
are quarantined as pilot provenance. Numerical relative agreement cannot
create a theorem equality.

The following are forbidden in canonical theorem statements until separately
proved:

```text
theta_j = nu_j,
delta_plus_m_N = nu_3-nu_1,
M_lambda = Mfin_m_N,
Mfin_m_N = Dlog^(m,N),
Mfin_m_N = A_m,
Mfin_m_N = PW_lambda.
```

## 7. Lamport proof

```text
<1>1. D0.3c supplies the exact finite Riesz operator, ON basis, Gram identity,
      matrix action, and selfadjointness; architectural review ratifies its
      scoped name Mfin_m_N.
<1>2. Basis reversal proves R is a selfadjoint unitary involution.
<1>3. The exact source matrix identities prove centrosymmetry and RM=MR.
<1>4. The explicit plus/minus basis proves orthogonal sector decomposition and
      dimensions N+1 and N.
<1>5. Commutation makes the sectors reducing; finite restrictions are
      selfadjoint.
<1>6. Finite spectral theory defines nu and epsilon_plus/minus and proves the
      multiset union, without a global-rank pattern.
<1>7. The namespace ledger prevents static-Schur theta and historical pilot
      mu symbols from entering the canonical definition.
<1>8. These are exactly the five fields in D0.3g.0, so D0.3g.6 assembles the
      record.
```

Conclusion: `D0.3g = PROVED`. QED.

## 8. Planted falsifiers

- `GRAM`: replace the ON basis by duplicated `V_0,V_0`; Gram is not identity.
- `MATRIX_ACTION`: transpose one genuinely complex Hermitian sentinel entry;
  the coefficient law changes.
- `PARITY`: replace `R V_n=V_-n` by `R V_n=V_(1-n)`; the finite index set is
  not preserved at the boundary.
- `COMMUTATOR`: change one entry `tau_(N,N)` without changing
  `tau_(-N,-N)`; centrosymmetry and (3.1) fail.
- `SECTOR_DIMENSION`: delete `V_0`; the even dimension becomes wrong.
- `GLOBAL_ORDER`: force `nu_2=epsilon_minus_1`; a direct sum of two arbitrary
  ordered lists need not alternate.
- `THETA_ALIAS`: set `theta_j:=nu_j`; the provenance types reject it.
- `M_LAMBDA`: erase `N` from `Mfin_m_N`; the object no longer has an exact
  parameter regime.

## 9. Explicit nonclaims

```text
NO_M_LAMBDA
NO_GLOBAL_BOTTOM_THREE_SECTOR_PATTERN
NO_STRICT_SECTOR_GAP
NO_SIMPLE_EVEN_GROUND
NO_N_LAMBDA_SELECTOR
NO_FINITE_CONTINUUM_BRIDGE
NO_ZERO_PRODUCING_CROSSWALK
NO_THETA_NU_EQUALITY
NO_H1_H4
NO_RH
```
