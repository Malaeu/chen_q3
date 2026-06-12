# Track B B2b: Fourier-PSD Probe for the Smooth Correction

Status: RP4/B2 diagnostic.  This is not a proof of E5', not a proof of RH,
and not a Lean proof file.

This note follows `docs/trackB/b2b_smooth_quadrature_probe.md`.  The previous
probe showed that the smooth correction has the right partial-summation shape,
but global explicit PNT bounds are too crude.  The other surviving route was:

```text
use the full explicit formula / zero-side PSD on the smooth correction family.
```

This note tests the minimal PSD eligibility question:

```text
Is H_v(a) = E_delta(a) * F_v(a)
positive definite, i.e. is its Fourier transform nonnegative?
```

If yes, Q3 zero-side PSD could apply directly.  If no, the direct zero-side
PSD route needs a signed decomposition or a different lift.

## D2 Normalization

Raw variable:

```text
a = r * log p,
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

For a correction eigenvector `v`, define:

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a),
H_v(a)     = E_delta(a) * F_v(a).
```

The finite packet model is built from positive shifts `a>=0` with the
symmetrized kernel

```text
r((D-a)/ell) + r((D+a)/ell).
```

The Fourier diagnostic therefore samples the even raw test:

```text
H_even(a) = H_v(|a|)
```

with convention:

```text
hat(f)(u) = integral_R f(a) exp(-2*pi*i*u*a) da.
```

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV receiver formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: Bochner/positive-definite Fourier criterion as the
  classical PSD mechanism behind convolution-square tests.  This is the same
  structural condition used by Cohn--Elkies LP bounds.  Source:
  https://arxiv.org/abs/math/0110009
- `UNCONDITIONAL / finite-dimensional linear algebra`: projected correction
  eigenvectors and sampled Fourier transforms in the current Step13 packet
  model.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Local Search Synthesis

Local `q3_docs` searches for:

```text
Fourier-positive positive definite cone Bochner Selberg correction zero-side PSD
Hermitian square Fourier nonnegative Q3 cone explicit formula receiver
Selberg error Fourier sign low band cone transport PSD
```

returned the active local contract:

- the public Q3 cone is the corrected positive-definite / convolution-square
  Weil cone;
- Q3 atom and Rayleigh bridges apply to atom/PD cone objects, not to arbitrary
  signed smooth tests;
- previous cone-transport notes already warned that the ordinary Selberg error
  has a low-band Fourier-positive window but is not globally Fourier-positive.

No local theorem says `E_delta(a)*F_v(a)` remains in the PD cone.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvfourier \
  --K 3.5 --ell 1.375 --schedule fixed \
  --receiver-delta 1 \
  --p0-na 401 --quad-na 4001 \
  --fourier-u-max 2 --fourier-nu 1001
```

The mode samples:

```text
hat(F_v)(u)
hat(E_delta * F_v)(u)
```

for the lower/upper/opnorm correction eigenvectors.

This is a numerical sign diagnostic, not an interval certificate.

## K = 3.5 Detailed Result

At:

```text
K = 3.5,
ell = 1.375,
delta = 1,
p0_na = 401,
quad_na = 4001,
u in [0,2],
```

the opnorm direction gives:

```text
correction opnorm ~= 0.2381603793

hat(F_v) min                   ~= -9.41e-11
hat(F_v) negative area fraction ~= 5.85e-12

hat(E_delta*F_v) min            ~= -0.4595384621
minimum near u                  ~= 0.932
first sampled negative u        ~= 0.034
negative area fraction          ~= 0.50602
hat(E_delta*F_v)(0)             ~= 0.08802
```

The tiny negative value for `hat(F_v)` is sampling/roundoff-level noise; the
profile itself passes the expected positive-definite sanity check.  Multiplying
by the Selberg correction destroys that sign completely.

The lower direction is similar:

```text
hat(F_v) min                    ~= -7.76e-11
hat(F_v) negative area fraction ~= 3.10e-12

hat(E_delta*F_v) min            ~= -0.4526395400
negative area fraction          ~= 0.49397
hat(E_delta*F_v)(0)             ~= -0.09324
```

## Four-K Compact Schedule

Using the same stable packet widths and receiver bandwidths as the previous
Track B schedule, with `p0_na=201`, `quad_na=2001`, and `u in [0,2]`:

```text
K=2.0, ell=0.75, delta=0.5:
  hat(F_v) min ~= 1.62e-12
  hat(F_v) negative area fraction ~= 0
  hat(E_delta*F_v) min ~= -0.660541
  negative area fraction ~= 0.5082
  first sampled negative u ~= 0.05

K=2.5, ell=1.375, delta=1.0:
  hat(F_v) min ~= -3.34e-11
  hat(F_v) negative area fraction ~= 1.88e-12
  hat(E_delta*F_v) min ~= -0.432771
  negative area fraction ~= 0.5076
  first sampled negative u ~= 0.05

K=3.0, ell=0.75, delta=0.5:
  hat(F_v) min ~= -3.89e-12
  hat(F_v) negative area fraction ~= 8.93e-15
  hat(E_delta*F_v) min ~= -1.10886
  negative area fraction ~= 0.4963
  first sampled negative u ~= 0

K=3.5, ell=1.375, delta=1.0:
  hat(F_v) min ~= -1.23e-10
  hat(F_v) negative area fraction ~= 1.42e-11
  hat(E_delta*F_v) min ~= -0.466895
  negative area fraction ~= 0.5059
  first sampled negative u ~= 0.035
```

The pattern is stable: the original packet autocorrelation behaves like a PD
test, while the Selberg correction product is strongly sign-changing in
Fourier space.

## Interpretation

This kills the direct zero-side PSD shortcut:

```text
H_v = E_delta * F_v is itself in the Q3 positive-definite cone.
```

It is not.  The sampled Fourier transform has roughly half its signed area in
the negative part over `[0,2]`.

This does not kill all explicit-formula routes.  What remains possible:

1. **Signed spectral decomposition**:
   Write `H_v = H_v^+ - H_v^-` in a controlled positive-definite basis and
   prove the negative spectral part is absorbed by existing margins.  This
   needs a new cone-aware theorem; naive positive/negative splitting is not
   allowed.

2. **Admissible lift**:
   Replace `E_delta*F_v` by a different convolution-square test that dominates
   the smooth correction and has small arch budget.  Earlier simple lift
   families failed, but this remains a route-level possibility.

3. **Certified finite Chebyshev ledger**:
   Since `clvquad` showed the partial-summation shape matches the object, build
   a finite `psi-x` staircase ledger for the smooth correction instead of
   relying on global explicit PNT or zero-side PSD.

## Verdict

`FATAL(direct PSD eligibility of E_delta*F_v)`.

`PARTIAL(F_v Fourier-positivity sanity passes)`.

`GAP(signed PD decomposition or finite Chebyshev ledger still needed)`.

This is not fatal for Track B.  It removes the simplest zero-side PSD shortcut
and leaves two real routes: a controlled signed PD decomposition, or a finite
smooth Chebyshev ledger.

## Proshka Audit Block

Claim:
The smooth correction test `H_v(a)=E_delta(a)F_v(a)` is not directly in the
positive-definite cone for the tested correction eigenvectors, even though
`F_v` itself passes the sampled Fourier-positive sanity check.

Point of blockage:
Q3 PSD applies to positive-definite / convolution-square tests.  The sampled
Fourier transform of `E_delta*F_v` has large negative mass: at `K=3.5`, the
opnorm direction has minimum about `-0.4595` and negative area fraction about
`0.506` on `u in [0,2]`.

What was tried:
Added `scripts/trackb_edge_operator_probe.py clvfourier`; sampled
`hat(F_v)` and `hat(E_delta*F_v)` for the correction lower/upper/opnorm
directions; ran detailed K=3.5 and compact K=2,2.5,3,3.5 schedules.

Minimal example:
At `K=3.5`, `ell=1.375`, `delta=1`, `p0_na=401`, `quad_na=4001`,
`hat(F_v)` has minimum about `-9.4e-11`, while
`hat(E_delta*F_v)` has minimum about `-0.4595` and negative area fraction about
`0.506`.

Question for Proshka:
Should Track B attempt a controlled signed positive-definite decomposition of
`E_delta*F_v`, or should it pivot to the finite smooth Chebyshev staircase
ledger as the next non-conditional route?
