# Track B B2b: Explicit-Formula Route and Cone-Transport Gap

Status: GAP(cone transport).  This is strategy and blocker documentation only.
It is not a proof of E5p, not a proof of RH, and not a Lean proof file.

## Goal

Use the unconditional Selberg/CLV interval technology from
`docs/trackB/clv_pair.md` to bound the edge defect

```text
Pnu_edge = P_edge - P0_edge
```

on the Q3 structured cross-correlation cone, without using RH or any
conditional zero-side theorem.

The preferred route is B2b:

```text
Hermitian square / Q_W-like test object
  -> Guinand-Weil explicit formula
  -> zero-side PSD already available in the Q3 cone
  -> one-sided prime-edge bound
```

## D2 Normalization

Step13 raw-log normalization:

```text
a = r * log p
weight = log(p) / p^(r/2)
edge I_K = [2K, 4K]
```

Q3 formal normalization:

```text
xi_n = log n / (2*pi)
prime_term(Phi) = sum_n w_Q(n) * Phi(xi_n)
even prime-comb convention = 2 * Lambda(n) / sqrt(n)
```

Thus raw-log `[2K,4K]` corresponds to
`xi in [K/pi, 2K/pi]`.  Any B2 theorem statement must say which variable is
used before constants are compared.

## Inputs Allowed

- `UNCONDITIONAL`: Selberg/Vaaler interval majorant-minorant.
- `UNCONDITIONAL`: Le-Vaaler explicit `H0,J0,K0` formulas and support.
- `UNCONDITIONAL`: CLV Gaussian subordination framework.
- `UNCONDITIONAL`: Q3 local PSD facts only where already proved or recorded as
  local finite certificates.

Forbidden:

- RH, GRH, pair-correlation, or zero-density assumptions.
- Fourier-quasicrystal transfer.
- de Branges positivity as an RH certificate.
- Treating RH-conditional prime-gap conclusions as theorem inputs.

## The Desired B2b Lemma Shape

For a packet vector `v` in the boundary-null cone, define the edge test
functional in raw-log coordinates by the Step13 form:

```text
F_v(a) =
  sum_ij v_i v_j *
    ( r_k((u_i-u_j-a)/ell) + r_k((u_i-u_j+a)/ell) ).
```

The measured edge fluctuation is:

```text
E_I(v)
  = sum_{p,r: r log p in I} log(p)/p^(r/2) * F_v(r log p)
    - integral_I e^(a/2) * F_v(a) da.
```

The target theorem shape is:

```text
|E_I(v)| <= epsilon_K^CLV * <v, G v>
```

or the one-sided variant required by the E5p ledger, with explicit
`epsilon_K^CLV` and no hidden normalization changes.

For `K=2`, the current measured proxy is:

```text
opnorm_G(Pnu_edge^circ) = 4.4167187609865910e-01
```

from `docs/trackB/k2_sanity_gap.md`.

## Why Plain B2a Is Blocked

The pre-B2 uncertainty gate is now explicit:

```text
docs/trackB/b2_uncertainty_tax_preflight.md
```

It gives a stronger reason to avoid naive B2a: hard Selberg/Vaaler
majorants/minorants of `[2K,4K]` pay at least `1/B_K` after imposing the
actual Fourier slack `B_K`.  Therefore the route

```text
CLV majorant * ||g||_infty
```

is `FATAL` whenever the mu-ledger requires `epsilon_K = o(1/B_K)`.

The pointwise split

```text
F_v = (F_v)_+ - (F_v)_-
```

is not a cone move.  Positive and negative parts do not preserve
bandlimitation, positive-definiteness, or the finite packet receiver.  Any
argument using this split is rejected unless it supplies a new
structure-preserving replacement.

## Why Plain Selberg-Insertion Is Also Blocked

The interval majorant satisfies the pointwise scalar inequality

```text
chi_I <= M^+_{I,delta}
```

but this does not imply an operator inequality on the signed
cross-correlation functional `F_v`.  The missing step is not pointwise
majorization of the interval; it is preservation of the Hermitian-square cone.

There is a concrete warning sign at `K=2`, `I=[4,8]`, `delta=1`.

For the symmetric edge majorant

```text
M^+_sym(x) = M^+_[4,8](x) + M^+_[-8,-4](x),
```

using the explicit Fourier formula in `docs/trackB/clv_pair.md`, numerical
sampling gives:

```text
hat(M^+_sym) min = -7.527308104448511   near u = -0.07851992148
hat(M^+_sym) max = 10.0                 at u = 0
negative sampled points = 196512 / 400001
```

So the ordinary Selberg interval majorant is not a Fourier-positive
multiplier.  It cannot be inserted as a PSD-preserving spectral cutoff without
an additional argument.

This is a B2 D2 failure if ignored.

## What Still Might Work

B2b remains viable only if one of the following replacements is found:

1. A Fourier-positive edge majorant with explicit support/error that still
   bounds the required edge functional.
2. A Hermitian-square lifting in which Selberg/CLV is applied to the full
   explicit-formula test object, and the resulting zero-side term is controlled
   by existing Q3 PSD certificates.
3. A Cauchy-Schwarz or square-function route that replaces the signed
   functional by a nonnegative square while keeping constants small enough for
   the mu-ledger.
4. A packet-specific finite operator inequality:

   ```text
   N^T (P_edge - P0_edge) N <= epsilon_K * N^T G N
   ```

   proved from the explicit CLV kernels, not from entrywise pointwise bounds.

The follow-up probe `docs/trackB/b2_cone_transport_probe.md` refines item 1:
it is enough for the majorant error `M^+-chi` to be Fourier-nonnegative on the
actual spectral support of the Hermitian-square cone.  Numerically, for the
ordinary Selberg error and `I=[2K,4K]`, the first zero/negative barrier is at
`u=1/(12K)`.  Thus the ordinary Selberg pair only supports an ultra-low-band
transport lemma, unless a different CLV object is found.

## Current Verdict

`B2-GAP(cone transport)`.

Fatal only for the naive route:

```text
Selberg pointwise majorant + signed cross-correlation
```

Not fatal yet for Track B:

```text
CLV + explicit formula + Hermitian-square/PSD receiver
```

The next work item is not another interval formula.  It is the cone-transport
lemma: identify a CLV-derived object that stays inside the Q3 Hermitian-square
receiver, or prove an explicit finite operator bound in the projected `G`
normalization.

Follow-up refinement:

- `docs/trackB/b2b_admissible_lift_audit.md` isolates the B2b missing lemma as
  an admissible lift:

  ```text
  edge prime <= lifted prime <= lifted arch <= P0_edge + epsilon_K <v,Gv>.
  ```

  The lift must be a corrected positive-definite/convolution-square Weil test
  before Q3 PSD can replace the RH-conditional zero-side step used in
  prime-gap explicit-formula arguments.

## Proshka Request

Claim:
The Selberg/Vaaler interval pair is unconditional and formula-correct, but the
ordinary interval majorant is not a PSD-preserving multiplier for the Q3
cross-correlation cone.

Point of blockage:
For `K=2`, `I=[4,8]`, `delta=1`, the symmetric Selberg majorant has
sign-changing Fourier transform; sampled minimum is about `-7.5273`.  Therefore
pointwise interval majorization does not transport to the Hermitian-square
operator order.

What was tried:
- Extracted the `M^\pm` formulas and `1/delta` L1 constants.
- Verified D2 raw-log versus `xi` scaling.
- Ran the Step13 `K=2` proxy and extracted
  `opnorm_G(Pnu_edge^circ) = 0.4416718760986591`.
- Sampled the symmetric majorant Fourier transform and found it is
  sign-changing.

Minimal example:
Raw-log edge `[4,8]`, `delta=1`,

```text
hat(M^+_[4,8])(u)
  = hat(chi_[4,8])(u) hat(J0)(u)
    + (e(-4u)+e(-8u)) hat(K0)(u)/2.
```

Symmetrize by adding the reflected interval `[-8,-4]`.  The resulting
Fourier transform is real but negative near `u=-0.07852`.  Find a replacement
that either preserves the Q3 Hermitian-square cone or gives a direct finite
operator inequality in the projected `G` normalization.
