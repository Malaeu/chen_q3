# Track B B2: Cone-Transport Probe

Status: B2 probe, not a proof.  This note records what survives after the
ordinary Selberg majorant failed as a PSD multiplier.

## Target

We want an unconditional route from the Selberg/CLV edge-strip pair to an
operator inequality on the corrected Q3 positive-definite cone:

```text
N^T (P_edge - P0_edge) N <= epsilon_K^CLV * N^T G N
```

or the corresponding two-sided bound, with exact D2 normalization.

## D2 Normalization

Raw-log Step13 variable:

```text
a = r * log p
I_K = [2K, 4K]
weight = log(p) / p^(r/2)
```

Q3 formal variable:

```text
xi_n = log n / (2*pi)
w_Q(n) = 2 * Lambda(n) / sqrt(n)
```

So raw `[2K,4K]` corresponds to `xi in [K/pi,2K/pi]`.

## Unconditional Transport Lemma Shape

Let

```text
E^+_{I,delta} = M^+_{I,delta,sym} - chi_{I,sym}
```

where `sym` means adding the reflected interval.  If a cone test `F` is a
Hermitian square / autocorrelation with nonnegative Fourier transform, and if
the support of `hat(F)` lies in a set on which

```text
hat(E^+_{I,delta}) >= 0,
```

then Plancherel gives

```text
int E^+_{I,delta}(x) F(x) dx
  = int hat(E^+_{I,delta})(u) hat(F)(u) du
  >= 0.
```

This would justify the one-sided transport

```text
int chi_{I,sym}(x) F(x) dx
  <=
int M^+_{I,delta,sym}(x) F(x) dx.
```

Source classification:

- `UNCONDITIONAL`: Selberg/Vaaler interval pair and Le-Vaaler `H0,J0,K0`
  formulas, already recorded in `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: Plancherel/Bochner positive-definite mechanism.  This is
  the same structural condition used in Cohn-Elkies linear programming:
  nonnegative Fourier transform is the positivity/PSD input.

This lemma is only useful if the actual Q3 cone supplies the required spectral
support, or if a CLV-derived error can be made nonnegative on the actual
spectral support of the packet cone.

## K=2 Error Transform Test

For `K=2`, raw interval `I=[4,8]`, and `delta=1`, sampling the symmetric
majorant error gives:

```text
hat(E^+_sym) min = -1.159899953539775   near u = -0.174814825185
hat(E^+_sym) max = 2.0                 at u = 0
negative sampled points = 196506 / 400001
```

So the Selberg error is not globally Fourier-positive.

However, the first negative point is near:

```text
u = 1/(12K).
```

For `K=2`, this is `1/24 = 0.041666666666666664`.

At the exact point `u0 = 1/(12K)` and `delta=1`:

```text
K=1: hat(E^+_sym)(u0) = 2.455041161752739e-16
K=2: hat(E^+_sym)(u0) = 2.6134320364850273e-16
K=3: hat(E^+_sym)(u0) = 2.667044795045808e-16
K=4: hat(E^+_sym)(u0) = 2.694009971536142e-16
K=8: hat(E^+_sym)(u0) = 2.7346601460568015e-16
```

The small nonzero values are numerical roundoff.  The cancellation is exact:

```text
sin(8*pi*K*u0) - sin(4*pi*K*u0) = 0,
cos(4*pi*K*u0) + cos(8*pi*K*u0) = 0.
```

Thus the ordinary Selberg error can only transport through an ultra-low-band
cone, roughly:

```text
supp hat(F) subset (-1/(12K), 1/(12K)).
```

This is a possible door, but not yet the Q3 cone.

## Delta Scan

For `K=2`, the first negative point of `hat(E^+_sym)` is:

```text
delta=0.005  first_neg=0.0049002   K*first=0.00980040
delta=0.01   first_neg=0.0096002   K*first=0.01920040
delta=0.02   first_neg=0.0184026   K*first=0.03680520
delta=0.04   first_neg=0.0336692   K*first=0.06733840
delta=0.05   first_neg=0.0401954   K*first=0.08039080
delta=0.075  first_neg=0.0416668   K*first=0.08333360
delta=0.1    first_neg=0.0416668   K*first=0.08333360
delta=0.25   first_neg=0.0416668   K*first=0.08333358
delta=0.5    first_neg=0.0416673   K*first=0.08333458
delta=1      first_neg=0.0416683   K*first=0.08333658
delta=2      first_neg=0.0416703   K*first=0.08334058
delta=4      first_neg=0.0416703   K*first=0.08334058
```

So increasing `delta` does not expand the positive transport band beyond
approximately `1/(12K)`.  This contradicts the naive hope that simply taking a
larger Selberg bandwidth would preserve the whole cone.

## Step13 Edge Proxy Scaling

Using the existing Step13 packet formulas, filtering the prime shifts to
`[2K,4K]`, and projecting to the boundary-null subspace gives the following
non-proof numerical proxy:

```text
K=1  opnorm_G(Pnu_edge^circ)=2.329913041354e-01
K=2  opnorm_G(Pnu_edge^circ)=4.416718760987e-01
K=3  opnorm_G(Pnu_edge^circ)=4.984733229295e-01
K=4  opnorm_G(Pnu_edge^circ)=9.715237551305e-01
```

Parameters:

```text
L=2K, ell=0.35, grid delta=0.5, k_spline=5
```

Interpretation:

- This is not a CLV certificate and not interval-certified.
- The edge fluctuation is not obviously decaying in this fixed packet
  normalization.
- The `K=4` jump warns that B3 cannot be claimed from the current finite proxy.

## Low-Band Capture Check

The low-band survivor would need the live packet cone to be spectrally
concentrated inside approximately:

```text
|u| < 1/(12K).
```

For the Step13 B-spline pilot with `ell=0.35` and `k_spline=5`, the scaled
single-correlation Fourier profile is

```text
hat(r_ell)(u)
  = ell/(s_k*c_k) * sinc(ell*u/s_k)^(2*k+2),
s_k = 3,
c_k = 0.3939255651755652,
hat(r_ell)(0) = 0.2961642426397752.
```

Numerical quadrature confirms total mass `int hat(r_ell)(u) du = 1`.  The mass
inside the Selberg-positive low band is:

```text
K=1  sigma=1/(12K)=0.08333333333333333   mass=0.04933002494217992
K=2  sigma=1/(12K)=0.041666666666666664  mass=0.02467651672634222
K=3  sigma=1/(12K)=0.027777777777777776  mass=0.016452432112490048
K=4  sigma=1/(12K)=0.020833333333333332  mass=0.012339697124628818
K=8  sigma=1/(12K)=0.010416666666666666  mass=0.006170028430304413
```

So the ordinary Selberg low-band window captures only a tiny part of the
current Step13 packet spectrum.  `LOW-BAND` is not a closure route for the
current packet unless we add a separate low-pass decomposition and an explicit
tail ledger.

## Current B2 Verdict

The B2 cone transport has three possible survivors:

1. `LOW-BAND`: prove the live cone has spectral support inside
   `(-1/(12K),1/(12K))`, or introduce a low-pass capture with an explicit tail
   ledger.
2. `PSD-CLV`: replace ordinary Selberg by a new CLV-derived object whose error
   has nonnegative Fourier transform on the actual cone spectrum.
3. `FINITE-OP`: abandon pointwise majorization for this step and certify the
   projected finite operator inequality directly, using CLV only to control
   tails or continuum error.

The current evidence rejects:

```text
ordinary Selberg majorant + unrestricted positive-definite cone
```

and makes `LOW-BAND` non-competitive for the current Step13 B-spline packet
without a new tail estimate.

It does not reject Track B as a whole.

## Proshka Update

Claim:
Selberg/CLV can transport through a positive-definite cone only if the
majorant error has nonnegative Fourier transform on the cone spectrum.  For the
ordinary interval pair this holds, at best, on an ultra-low band.

Point of blockage:
For `I=[2K,4K]`, the symmetric Selberg error has an exact zero at
`u=1/(12K)` and becomes negative immediately after in the `delta=1` experiment.
The current Step13 packet proxy does not supply compact spectral support inside
that band.

What was tried:
- Checked `hat(M^+_sym)` and `hat(M^+_sym-chi_sym)`.
- Identified the low-band window and the exact zero `u=1/(12K)`.
- Ran Step13 edge proxy scaling for `K=1..4`.
- Checked low-band capture for the current Step13 B-spline profile; at `K=2`
  the positive low band captures only about `2.47%` of the single-correlation
  spectral mass.

Minimal example:
`K=2`, raw `I=[4,8]`, `delta=1`.  A valid cone-transport theorem would need
`supp hat(F) subset (-1/24,1/24)` or a replacement majorant error that is
Fourier-nonnegative on the actual packet spectrum.
