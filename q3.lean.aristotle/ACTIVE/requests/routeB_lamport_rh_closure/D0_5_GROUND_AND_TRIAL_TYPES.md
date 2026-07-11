# D0.5 — ExactGroundEigenspaceAndTrialVectorTypes

Status: `MATH_PROVED / SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Exit: `GROUND_TRIAL_TYPES_LOCKED`.

This leaf defines the exact finite ground object and the exact prolate-derived
trial objects, while keeping their carriers and roles separate. It does not
assume a simple/even ground state, nonzero projected trial, or ground/trial
proximity.

## 1. Finite ground eigenspace

For the canonical finite selfadjoint carrier

```text
Mfin_m_N:E_m_N->E_m_N,
```

let

```text
groundValue_m_N := nu_1(m,N),
GroundSpace_m_N := ker(Mfin_m_N-groundValue_m_N*I).
```

Finite-dimensional spectral theory proves `GroundSpace_m_N` is nonzero. Define

```text
GroundUnit_m_N={xi in GroundSpace_m_N: ||xi||=1}.
```

This is generally a set, not a selected vector. The following remain open:

```text
dim(GroundSpace_m_N)=1;
GroundSpace_m_N subset Eplus_m_N;
groundValue_m_N=epsilon_plus_1(m,N);
a canonical phase for xi.
```

The exact sector bottoms exist separately:

```text
epsilon_plus_1(m,N),
epsilon_minus_1(m,N),
nu_1(m,N)=min(epsilon_plus_1(m,N),epsilon_minus_1(m,N)).
```

The last identity follows from the orthogonal direct-sum spectrum and does not
choose which sector wins or exclude equality.

## 2. Exact time-side prolate packet

Put `lambda=sqrt(m)` and `C_lambda=2*pi*lambda^2`. Let
`h_0_lambda,h_4_lambda` be the real, L2-normalized prolate eigenfunctions with
the source phase

```text
I_0_lambda=integral h_0_lambda>0,
I_4_lambda=integral h_4_lambda>0.
```

Define

```text
D_lambda=sqrt(I_0_lambda^2+I_4_lambda^2),
hTrial_m=(I_4_lambda*h_0_lambda-I_0_lambda*h_4_lambda)/D_lambda.
```

The source dictionary proves

```text
||hTrial_m||_L2=1,
integral hTrial_m=0.
```

This object lives in additive `Ktime_lambda=L2([-lambda,lambda],dx)` and is a
trial generator, not an eigenvector of `Mfin_m_N`.

## 3. Multiplicative and finite trial objects

Using the source's midpoint representative and starred summation map, define

```text
gTrial_m
 := E_star(hTrial_m) restricted to [lambda^-1,lambda] in H_m,
gTrial_m_N := P_m_N(gTrial_m) in E_m_N.
```

The endpoint midpoint convention changes pointwise boundary identities but not
the `H_m` vector or its orthogonal projection.

Define the nonzero locus

```text
TrialNonzero={ (m,N) : ||gTrial_m_N||>0 }.
```

Only on this locus define

```text
kTrial_m_N := gTrial_m_N/||gTrial_m_N||,
aTrial_m_N := <kTrial_m_N,Mfin_m_N kTrial_m_N>.
```

The exact scalar/phase normalization is packaged in D0.7. D0.5 merely records
the dependent type and the nonzero precondition instead of silently dividing
by zero.

## 4. Role separation

The objects have different roles:

```text
GroundSpace_m_N   exact bottom eigenspace of Mfin_m_N;
xi                a future selected unit ground vector, if selection is legal;
hTrial_m          additive prolate two-mode packet;
gTrial_m          multiplicative starred-sum window packet;
gTrial_m_N        finite orthogonal projection of gTrial_m;
kTrial_m_N        conditional normalized finite trial;
aTrial_m_N        Rayleigh value of kTrial_m_N.
```

Rayleigh-Ritz gives, on `TrialNonzero`,

```text
groundValue_m_N <= aTrial_m_N.
```

Equality holds exactly when `kTrial_m_N` belongs to `GroundSpace_m_N`; no such
membership is claimed. A small difference or small absolute Rayleigh value
does not select a ground vector.

The source paper's trial-to-ground approximation is explicitly a missing step.
The map `E_star` is not registered as unitary, and `PW_lambda`, `Mfin_m_N`, and
`Dlog^(m,N)` remain distinct operators.

## 5. Lamport proof

```text
<1>1. Finite selfadjoint spectral theory gives nu_1 and a nonzero ground
      eigenspace, without simplicity or parity.
<1>2. D0.4's orthogonal reduction gives sector bottoms and
      nu_1=min(epsilon_plus_1,epsilon_minus_1), without choosing a sector.
<1>3. The source dictionary defines the normalized two-prolate-mode hTrial and
      proves its integral is zero.
<1>4. The exact starred summation and D0.1 projection type gTrial and
      gTrial_m_N in their respective carriers.
<1>5. Restricting normalization to TrialNonzero makes kTrial and its Rayleigh
      value total on the declared dependent domain.
<1>6. Rayleigh-Ritz proves groundValue<=aTrial; equality is not assumed.
<1>7. The carrier/role ledger rejects ground/trial and operator conflations.
```

Conclusion: `D0.5 = PROVED`. QED.

## 6. Planted falsifiers

- `SIMPLE_GROUND`: use the zero matrix on `C^2`; its ground eigenspace has
  dimension two.
- `EVEN_GROUND`: use a parity-reduced diagonal matrix whose odd eigenvalue is
  lower than its even eigenvalue.
- `ZERO_TRIAL`: set `gTrial_m_N=0`; unconditional normalization must fail.
- `TRIAL_EQUALS_GROUND`: use `diag(0,2)` and trial `e_2`; its Rayleigh value is
  two while the ground value is zero.
- `CARRIER_ALIAS`: feed additive `hTrial_m` directly to `Mfin_m_N`; the types
  differ.
- `H4_INDEX`: replace `h_4<->chi_2` by `h_4<->chi_4`; the source dictionary
  rejects the index.
- `MIDPOINT_L2`: claim midpoint endpoint weights alter the L2 projection; a
  finite point set has measure zero.

## 7. Explicit nonclaims

```text
NO_SIMPLE_GROUND
NO_EVEN_GROUND
NO_GROUND_VECTOR_SELECTION
NO_UNCONDITIONAL_TRIAL_NORMALIZATION
NO_TRIAL_GROUND_IDENTITY
NO_GROUND_TRIAL_RATE
NO_OPERATOR_CONFLATION
NO_H2_H4
NO_D0_ASSEMBLY
NO_RH
```
