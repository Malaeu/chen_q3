# D0.1 — ExactHilbertSpaceAndNorm

Status: `MATH_PROVED / SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Progress class: `PROOF_PROGRESS`

This is the first child of the AND node `D0 ExactObjectFamily`. It fixes only
the parameter/index set, Hilbert space, measure, norm, Fourier modes, finite
subspace, orthogonal projection, and a.e. zero extension. It does not define
`QW`, choose a ground vector, prove simple-even, select `N(lambda)`, or assert
any convergence to `Xi`.

## 1. Leaf contract

### Statement

Let

```text
Lambda_int = {sqrt(m) : m in N and m >= 2},
I_fin      = {(m,N) : m >= 2 and N >= 1}.
```

For `(m,N) in I_fin`, put

```text
lambda_m = sqrt(m),
L_m      = 2 log(lambda_m) = log(m).
```

Then the following source-locked objects exist and have the stated exact
properties:

1. the complex Hilbert space

   ```text
   H_m = L2([lambda_m^-1,lambda_m], du/u);
   ```

2. the unitary coordinate map

   ```text
   kappa_m : L2([0,L_m],dx) -> H_m,
   (kappa_m f)(u) = f(log(lambda_m*u));
   ```

3. the orthonormal modes

   ```text
   U_(n,m)(x) = L_m^(-1/2) exp(2*pi*i*n*x/L_m),
   V_(n,m)    = kappa_m(U_(n,m));
   ```

4. the concrete finite subspace

   ```text
   E_(m,N) = span_C {V_(n,m) : -N <= n <= N},
   dim_C E_(m,N) = 2*N+1;
   ```

5. the orthogonal projection `P_(m,N) : H_m -> E_(m,N)`;
6. the a.e. zero extension `Z_m : H_m -> L2(R_+^*,du/u)`, which is an
   isometry, has essential support contained in the window, and satisfies

   ```text
   ||Z_m f||_1 <= sqrt(L_m) ||f||_2.
   ```

The set `Lambda_int` is cofinal in `(1,infinity)`. No diagonal schedule
`N=N(lambda)`, product-cofinal limit, or iterated-limit theorem is asserted.

### Type inventory

- scalar field: `C`;
- logarithm: the natural real logarithm;
- parameter grid: positive square roots `sqrt(m)`, `m>=2`;
- finite index: `N>=1`, retained in every finite object;
- source interval: `[0,L_m]` with Lebesgue measure `dx`;
- target interval: `[lambda_m^-1,lambda_m]` with multiplicative measure
  `d^*u=du/u`;
- inner product convention: antilinear in the first variable;
- support: essential support for `L2` classes; endpoint representatives are
  deferred to D0.7;
- topology locked here: Hilbert norm only; compact-substrip topology belongs
  to D0.6/H3.

### Parent contract

`D0.1` supplies exactly the first hypothesis of the proved definitional
contract

```text
D0.1 AND ... AND D0.8 -> D0.
```

It does not imply D0 by itself.

### Dependencies

- `D0.0 D0 decomposition contract`: mathematically proved by definition;
- the standard change-of-variables theorem;
- the elementary exponential integral;
- finite-dimensional subspaces of a Hilbert space are closed;
- the Archimedean property of `N`.

No RH-equivalent or RH-conditional theorem is imported.

### Two proof routes

1. Direct route: use `x=log(lambda*u)` to prove unitarity, then transport the
   elementary Fourier orthogonality calculation from `[0,L]`.
2. Source-plus-crosscheck route: source-pin `kappa,U_n,V_n,E_N`, then verify
   the normalizing constant, phase, and measure independently with planted
   counterexamples.

Route 1 is the accepted mathematical proof. Route 2 is the validation path.

## 2. Source lock

Primary local source:

```text
literature/zotero/H8ULBMAL/fulltext.md
```

Exact evidence:

- lines 108–112: `U_n(x)=L^(-1/2) exp(2*pi*i*n*x/L)`;
- lines 285–290: `lambda>1`, `L=2 log lambda`, the map `kappa`, and its
  isometry;
- lines 312–313: `d^*u=du/u`;
- lines 333–339: `V_n=kappa(U_n)`, the span, and finite-minimum statement;
- lines 702–704 and 734–735: the finite space spanned by `|n|<=N` and its
  orthonormal basis;
- lines 1015–1026: zero extension outside the multiplicative window.

Project narrowing and crosswalk:

- `docs/ROUTE_B_THEOREM_CONTRACT_v2.md:15,27,30` requires every finite object
  to retain N and fixes the working grid `lambda^2 in N`;
- `docs/ALPHA_DEMAND_AUDIT.md:39` records cofinal-subsequence sufficiency but
  leaves the Rouche theorem to PO-11;
- `docs/PEN_3_3_G04_OBJECT_DICTIONARY.md:169-228` uses the same Hilbert space,
  modes, projection, and explicit second index N.

The source is defined for all `lambda>1`. Restriction to `Lambda_int` is a
project choice, not a source theorem. The source alternates between `N in N`
and “positive integer”; this compiler fixes `N>=1` and avoids an `N=0`
convention fork.

## 3. Lamport proof

### Theorem D0.1

The objects in Section 1 satisfy every assertion of the leaf statement.

Proof.

`<1>1.` **The parameter window is legal and cofinal.**

For `m>=2`, `lambda_m=sqrt(m)>1`, hence

```text
L_m = 2 log(lambda_m) = log(m) > 0.
```

For every real `R>1`, choose an integer `m>R^2`. Then
`lambda_m=sqrt(m)>R`. Thus `Lambda_int` is cofinal. The concrete sequence
`m_j=j+2` gives `lambda_(m_j)->infinity`.

`<1>2.` **The logarithmic coordinate preserves the measure.**

Let

```text
phi_m(u)=log(lambda_m*u).
```

It maps `lambda_m^-1` to `0`, maps `lambda_m` to `L_m`, and has inverse
`u=exp(x)/lambda_m`. Differentiating gives

```text
dx = du/u.
```

`<1>3.` **`kappa_m` is unitary.**

For every `f in L2([0,L_m])`, change variables using `<1>2`:

```text
||kappa_m f||^2
 = integral_[lambda^-1,lambda] |f(log(lambda*u))|^2 du/u
 = integral_[0,L_m] |f(x)|^2 dx
 = ||f||^2.
```

The inverse is

```text
(kappa_m^-1 g)(x)=g(exp(x)/lambda_m).
```

Therefore `kappa_m` is a surjective isometry, hence unitary.

`<1>4.` **The modes `U_(n,m)` are orthonormal.**

With the inner product antilinear in the first variable,

```text
<U_(r,m),U_(n,m)>
 = L_m^-1 integral_0^L_m exp(2*pi*i*(n-r)*x/L_m) dx.
```

If `n=r`, the integral is `L_m`. If `n!=r`, the antiderivative has equal
endpoint values because `exp(2*pi*i*(n-r))=1`; the integral is zero. Hence the
inner product is the Kronecker delta.

`<1>5.` **The modes `V_(n,m)` are orthonormal.**

By definition `V_(n,m)=kappa_m U_(n,m)`. Unitarity from `<1>3` gives

```text
<V_(r,m),V_(n,m)>_H = <U_(r,m),U_(n,m)> = delta_(r,n).
```

`<1>6.` **The finite space has dimension `2N+1`.**

The family with indices `-N,...,N` contains `2N+1` vectors. If

```text
sum_(|n|<=N) c_n V_(n,m)=0,
```

take the inner product with `V_(k,m)`. Orthogonality gives `c_k=0` for every
`k`. Thus the family is linearly independent and is a basis of its declared
span. Consequently `dim_C E_(m,N)=2N+1`.

`<1>7.` **The orthogonal projection exists.**

`E_(m,N)` is finite-dimensional, so it is closed in `H_m`. The Hilbert-space
projection theorem therefore supplies a unique orthogonal projection
`P_(m,N)` onto it.

`<1>8.` **Zero extension is isometric and compactly supported a.e.**

For an `L2` representative `g`, define `Z_m g` to equal `g` in the window and
zero outside. Endpoint choices affect no `L2` class. Direct splitting of the
integral gives

```text
||Z_m g||_(L2(R_+^*)) = ||g||_(H_m),
ess_supp(Z_m g) subseteq [lambda_m^-1,lambda_m].
```

Since the multiplicative measure of the window is

```text
integral_[lambda^-1,lambda] du/u = 2 log(lambda_m)=L_m,
```

Cauchy–Schwarz yields

```text
||Z_m g||_1 <= sqrt(L_m) ||g||_2.
```

The constant is sharp: for `V_(0,m)=L_m^(-1/2)`, the `L2` norm is one and the
`L1` norm is `sqrt(L_m)`.

`<1>9.` **Support wording is exact.**

For arbitrary `g in H_m`, only containment of essential support is asserted;
equality would fail for `g=0` or a half-window indicator. If `g` is a nonzero
element of `E_(m,N)`, its continuous representative is a finite
trigonometric polynomial. Such a nonzero polynomial cannot vanish on an open
subinterval, so its essential support is the full window. This stronger fact
is recorded but not needed by D0.1.

`<1>10.` **The two-parameter firewall is preserved.**

Every finite object keeps `(m,N)`. This proof establishes cofinality only in
`m`/`lambda`. It neither selects `N(lambda)` nor equates diagonal, product,
and iterated convergence. Those are later D0.8/H3c obligations.

Steps `<1>1`–`<1>10` prove the exact leaf statement. QED.

## 4. Cheapest planted falsifiers

### F1 — wrong measure `du`

Set `lambda=e`, hence `L=2`, and take `f=1`. The source norm squared is `2`.
With `du/u` the transported norm squared is also `2`; with the planted measure
`du` it is `e-e^-1`, not `2`.

Expected code: `D0_1_MEASURE_PLANT_FIRES`.

### F2 — missing `L^(-1/2)`

For `lambda=e`, the unnormalized constant mode has norm squared `L=2`, not
one. The source-normalized mode has norm one.

Expected code: `D0_1_MODE_NORMALIZATION_PLANT_FIRES`.

### F3 — wrong coordinate `log(u)`

For `lambda=e`, the correct coordinate maps `(e^-1,1,e)` to `(0,1,2)`, while
`log(u)` maps it to `(-1,0,1)`. In particular the correct `V_1(1)` is
`-1/sqrt(2)`, whereas the planted coordinate gives `+1/sqrt(2)`.

Expected code: `D0_1_COORDINATE_PLANT_FIRES`.

### F4 — support overclaim

The zero vector and a half-window indicator disprove “every `H_m` element has
support exactly the full window.”

Expected code: `D0_1_SUPPORT_OVERCLAIM_PLANT_FIRES`.

## 5. Success and exclusions

Success condition:

```text
EXACT_HILBERT_SPACE_AND_NORM_LOCKED
```

Required validation:

```text
python3 validate_d0_1.py
python3 -m json.tool D0_1_CERTIFICATE.json
git diff --check
```

Not supplied here:

- `QW`, `QW_lambda`, or `QW^N_lambda` — D0.2;
- operator identities — D0.3/D0.8;
- parity theorem — D0.4/H2a;
- ground/trial selection — D0.5;
- transform convention — D0.6;
- endpoint/Dirichlet normalization — D0.7;
- `N(lambda)` or finite-to-continuum convergence — D0.8/H3c;
- H1–H4, D0 assembly, or RH.

Final leaf verdict:

```text
D0.1 = PROVED
EXACT_HILBERT_SPACE_AND_NORM_LOCKED
LEAN_INTERFACE_UNPINNED
NOT_RH
```
