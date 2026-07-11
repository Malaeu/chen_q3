# D0.6 — ExactTransformConvention

Status: `MATH_PROVED / SOURCE_LOCKED / LEAN_INTERFACE_UNPINNED / NOT_RH`

Progress class: `PROOF_PROGRESS`

Exit: `EXACT_TRANSFORM_CONVENTION_LOCKED`.

This leaf locks the a.e. zero extension, multiplicative Fourier transform,
Mellin half-density crosswalk, logarithmic centering phase, removable lattice
values, and compact-open topology. It proves a fixed-window evaluation
theorem. It does not supply the ground/trial crosswalk, a joint `N(lambda)`, a
uniform-in-`lambda` evaluation constant, H3, or RH.

## 1. Leaf contract

Fix `m>=2` and write

```text
lambda = sqrt(m),
L      = log(m)=2*log(lambda),
I_m    = [lambda^-1,lambda],
H_m    = L2(I_m,du/u).
```

Let `Z_m` be D0.1's a.e. zero extension. Then

```text
Z_m : H_m -> L1(R_+^*,du/u) intersection L2(R_+^*,du/u),
||Z_m f||_1 <= sqrt(L)||f||_2.
```

For `f in H_m` define the branch-free multiplicative Fourier transform

```text
T_m f(z)
  := integral_(0,infinity) (Z_m f)(u) exp(-i*z*log(u)) du/u
   = integral_(0,infinity) (Z_m f)(u) u^(-i*z) du/u.
```

The notation `u^(-i*z)` always means `exp(-i*z*log(u))` with the real logarithm
on `u>0`.

The target topology for later strip tracking is the compact-open topology on

```text
S={z in C: |Im(z)|<1/2}.
```

No endpoint value of an `L2` representative is defined by this leaf.

### Parent contract

D0.6 supplies the transform-convention component of the D0 AND record. It
consumes D0.1 and does not imply D0, H1, H3, or RH alone.

## 2. Entirety and differentiated formula

For `r>=0`, define

```text
(T_m f)^(r)(z)
 = integral (Z_m f)(u) (-i*log(u))^r u^(-i*z) du/u.
```

Proof. The extension is supported a.e. in the compact multiplicative interval
`I_m`, so `|log u|<=log lambda` there. On every compact `K subset C`, the
integrand and every displayed `z`-derivative are dominated by an integrable
multiple of `|Z_m f|`. Differentiation under the integral is therefore legal
for every order. Hence `T_m f` is entire and the formula holds. QED.

This is a theorem for every fixed `m` and `f`. It becomes H1 only after the
exact approximant family and all normalizations have been locked and shown to
be of this form.

## 3. Logarithmic coordinate and centering phase

For `g in L2([0,L],dx)`, D0.1 gives

```text
kappa_m(g)(u)=g(log(lambda*u)).
```

With `x=log(lambda*u)`, so `u=exp(x)/lambda` and `du/u=dx`, one obtains

```text
T_m(kappa_m g)(z)
 = lambda^(i*z) integral_0^L g(x) exp(-i*z*x) dx.       (3.1)
```

The phase `lambda^(i*z)` is forced by the centered coordinate. Omitting it
would correspond to `x=log u`, not D0.1's `x=log(lambda*u)`.

For

```text
V_n_m(u)=L^(-1/2) exp(2*pi*i*n*log(lambda*u)/L),
a_n=2*pi*n/L,
```

equation (3.1) simplifies to

```text
T_m V_n_m(z)
 = 2*L^(-1/2) sin(z*L/2)/(z-a_n).                     (3.2)
```

Every apparent lattice pole is removable. At `z=a_n`,

```text
T_m V_n_m(a_n)=sqrt(L)*(-1)^n.                        (3.3)
```

At another lattice point `a_ell`, `ell!=n`, the value is zero. Thus for a
finite vector `xi=sum_(|n|<=N)c_n V_n_m`, linearity gives the corresponding
finite sum of (3.2), with every lattice value interpreted by (3.3).

## 4. Mellin half-density crosswalk

Use the classical Mellin convention

```text
Mellin(g)(s)=integral_0^infinity g(u)u^(s-1)du.
```

For the half-density `Half(g)(u)=u^(1/2)g(u)`, direct exponent arithmetic gives

```text
F_mu(Half(g))(z)
 = integral u^(1/2)g(u)u^(-i*z)du/u
 = Mellin(g)(1/2-i*z).                                (4.1)
```

The sign is minus. Since this project defines

```text
Xi(z)=xi(1/2+i*z),
```

an identity `Mellin(g)=xi` would imply literally

```text
Xi(z)=F_mu(Half(g))(-z).                               (4.2)
```

Replacing `-z` by `z` requires a separately proved evenness/inversion theorem;
it is not a convention change.

If a packet `k=E(h)` already contains the half-density factor `u^(1/2)`, its
multiplicative transform is simply

```text
F_mu(k)(z)=Mellin(k)(-i*z),
```

when the right side is defined. Applying `Half` once more would be a double
half-shift.

## 5. Additive versus multiplicative Fourier transforms

The prolate dictionary uses the separate additive transform

```text
F_add(h)(y)=integral_R h(x) exp(2*pi*i*x*y) dx.
```

Its carrier is additive `L2(R,dx)` and its sign includes `+2*pi*i*x*y`.
The transform `T_m` uses the multiplicative group, Haar measure `du/u`, and
kernel `exp(-i*z*log u)`. These objects are not aliases. A bridge would require
a named log-coordinate unitary and the exact phase/frequency rescaling.

The pointwise midpoint representative in the prolate/Poisson dictionary is
also separate from D0.1's a.e. zero extension. Changing finitely many endpoint
values changes no `L1`/`L2` class and no transform integral, but can change a
pointwise boundary identity. D0.6 therefore proves no boundary normalization.

## 6. Compact-open topology and fixed-window bound

For `R>=0` and `0<=a<1/2`, let

```text
K_(R,a)={z: |Re(z)|<=R and |Im(z)|<=a},
p_(R,a)(G)=sup_(z in K_(R,a)) |G(z)|.
```

Every compact subset of `S` lies in some `K_(R,a)`, so these seminorms generate
the compact-open topology on `Hol(S)`.

On the support window,

```text
|u^(-i*z)|=exp(Im(z)*log(u))<=lambda^a
```

for `z in K_(R,a)`. Hence

```text
p_(R,a)(T_m f)
 <= lambda^a ||Z_m f||_1
 <= lambda^a sqrt(L)||f||_2.                           (6.1)
```

Thus `T_m:H_m->Hol(S)` is continuous for each fixed `m` in the compact-open
topology.

The constant in (6.1) depends on `m`. For `sigma>0`, the normalized constant
mode satisfies

```text
T_m V_0_m(i*sigma)
 = (lambda^sigma-lambda^(-sigma))/(sigma*sqrt(L)),
```

which diverges as `m->infinity`. Therefore D0.6 does not prove a
uniform-in-`m` evaluation theorem. H3b must use a weighted norm or an error
rate that absorbs the factor relevant to each compact.

Compact-open convergence is also weaker than uniform convergence on an
unbounded closed substrip. The functions `G_j(z)=z/j` converge uniformly on
every compact subset of `S`, but their supremum on every unbounded closed
substrip is infinite.

## 7. Source theorem firewall

The primary source proves the transform formula for finite vectors and states
a stronger closed-substrip convergence result for the explicit trial packet
`k_lambda`. It separately names trial-to-ground accuracy as a missing step.
Consequently D0.6 imports only:

- the multiplicative transform convention and finite-vector formula;
- compact-support entirety;
- the exact Mellin/half-density arithmetic;
- the topological definitions and elementary fixed-window estimate.

It does not import trial convergence as ground-vector convergence, does not
select `N(lambda)`, and does not use an RH-conditional zero statistic.

## 8. Lamport proof

```text
<1>1. D0.1 supplies Z_m in L1 intersection L2 and the sharp L1 bound.
<1>2. Define T_m with Haar measure du/u and exponent u^(-i*z).
<1>3. Compact log support permits differentiation under the integral to every
      order; hence T_m f is entire.
<1>4. The centered substitution x=log(lambda*u) proves (3.1), including the
      phase lambda^(i*z).
<1>5. Integrating each exponential mode proves (3.2); limits prove (3.3).
<1>6. Exponent arithmetic proves the half-density identity (4.1) and the
      project-sign crosswalk (4.2).
<1>7. Carrier, measure, and kernel types separate F_add from T_m.
<1>8. Compact containment and the support estimate prove (6.1), hence
      fixed-m compact-open continuity.
<1>9. The V_0 and z/j counterexamples reject uniform-in-m and global-strip
      overclaims.
<1>10. Therefore every statement in the D0.6 contract is proved, without
       supplying H3 or RH.
```

Conclusion: `D0.6 = PROVED`. QED.

## 9. Planted falsifiers

- `MEASURE`: for `1_I`, `T(0)=L`; using `du` gives
  `lambda-lambda^-1`.
- `SIGN`: at `z=2*pi/L`, the correct `u^(-i*z)` transform of `V_1` is
  `-sqrt(L)`; the planted `u^(+i*z)` transform is zero.
- `HALF_SHIFT`: `F_mu(u^(1/2)g)(z)` is `Mellin(g)(1/2-i*z)`, not
  `Mellin(g)(1/2+i*z)`.
- `CENTERING_PHASE`: omitting `lambda^(i*z)` changes a nonzero `V_0`
  transform at imaginary `z`.
- `REMOVABLE_POLE`: (3.2) must return `sqrt(L)(-1)^n` at its own lattice
  frequency, not infinity or zero.
- `TOPOLOGY`: `z/j` distinguishes compact-open convergence from uniform
  convergence on an unbounded closed substrip.
- `LAMBDA_UNIFORMITY`: `T_m V_0(i*sigma)` diverges with `m`.
- `REPRESENTATIVE`: a function supported at one endpoint represents zero in
  `L2` and has zero transform, despite a nonzero chosen point value.
- `TRIAL_GROUND`: the source's trial-family limit may not be relabelled as a
  ground-family theorem.

## 10. Explicit nonclaims

```text
NO_BOUNDARY_NORMALIZATION
NO_UNIFORM_IN_LAMBDA_EVALUATION
NO_GLOBAL_CLOSED_SUBSTRIP_TOPOLOGY
NO_TRIAL_GROUND_CROSSWALK
NO_N_LAMBDA_SCHEDULE
NO_H1_FAMILY_SELECTED
NO_H3
NO_D0_ASSEMBLY
NO_RH
```
