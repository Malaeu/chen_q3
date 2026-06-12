# Track B / B1: Selberg-CLV Pair for the Edge Strip

Status: B1 formula card, strategy documentation only.  This does not prove
RH, does not prove E5', does not close Step33/L3, and does not modify Lean
proof files or `Q3.Main`.

Goal context:

- Track B goal: close the E5' edge defect using unconditional
  Beurling-Selberg / CLV technology.
- This B1 card records the explicit interval majorant/minorant for the edge
  strip and the exact D2 normalization checks that must be preserved before
  any B2 cone argument.
- Every theorem used below is marked `UNCONDITIONAL`.  Conditional RH inputs
  from prime-gap papers are only shape references, not allowed inputs.

Forbidden inputs for this goal:

- Fourier-quasicrystal transfer.
- de Branges positivity as an RH certificate.
- Any theorem whose statement requires RH, GRH, pair-correlation conjectures,
  or unproved convergence of a spectral model.

## Sources

1. `UNCONDITIONAL` Selberg-Beurling interval construction:
   Jeffrey D. Vaaler, "Some extremal functions in Fourier analysis",
   Bull. Amer. Math. Soc. 12 (1985), 183-216.
   AMS record:
   https://www.ams.org/bull/1985-12-02/S0273-0979-1985-15349-2/

2. `UNCONDITIONAL` explicit `H,J,K` interval pair and Fourier support:
   Thai Hoang Le and Jeffrey D. Vaaler, "Sums of products of fractional
   parts", Section 3.  The paper restates the Vaaler functions and proves the
   interval majorant/minorant lemma with support in `[-delta, delta]`.
   PDF:
   https://home.olemiss.edu/~leth/papers/fractional_parts.pdf

3. `UNCONDITIONAL` CLV Gaussian subordination framework:
   Emanuel Carneiro, Friedrich Littmann, Jeffrey D. Vaaler,
   "Gaussian subordination for the Beurling-Selberg extremal problem",
   Trans. Amer. Math. Soc. 365 (2013), 3493-3534.
   arXiv:
   https://arxiv.org/abs/1008.4969

4. Shape reference only, not an input:
   Carneiro-Milinovich-Soundararajan, "Fourier optimization and prime gaps",
   Comment. Math. Helv. 94 (2019), 533-568.
   The prime-gap theorem is RH-conditional, so it is forbidden as a theorem
   input here.  The only reusable lesson is the architecture "bandlimited
   extremal function + explicit formula".
   arXiv:
   https://arxiv.org/abs/1708.04122

## Fourier Convention

Use

```text
e(t) = exp(2*pi*i*t)
hat(f)(u) = integral_R f(x) e(-u*x) dx.
```

All variables in this card are real unless explicitly complexified.

## Edge Strip

For raw logarithmic variable `x = log n`, the Track B edge strip is

```text
I_K = [2*K, 4*K],
a = 2*K,
b = 4*K,
L = b - a = 2*K,
c = (a+b)/2 = 3*K.
```

D2 warning: Q3's formal prime nodes are usually

```text
xi_n = log n / (2*pi),
prime weight = 2*Lambda(n)/sqrt(n).
```

Therefore an interval written in raw `log n` variable becomes

```text
[2*K, 4*K] in x
  <=> [K/pi, 2*K/pi] in xi.
```

If a later experiment declares `[2*K,4*K]` directly in the `xi` variable, this
rescaling must not be applied.  This is a D2 gate, not a cosmetic convention.

## Base Vaaler Functions

Define

```text
K0(z) = (sin(pi*z)/(pi*z))^2,

H0(z) = (sin(pi*z)/pi)^2
        * ( sum_{m in Z} sgn(m) * (z-m)^(-2) + 2/z ),

J0(z) = (1/2) * H0'(z).
```

The functions are real entire on the real axis after the removable
singularities are filled in.  They have exponential type at most `2*pi`.

`UNCONDITIONAL` Vaaler inequality:

```text
|sgn(x) - H0(x)| <= K0(x)        for every real x.
```

Equivalently,

```text
H0(x) - K0(x) <= sgn(x) <= H0(x) + K0(x).
```

Fourier transforms needed for B1:

```text
hat(K0)(t) =
  1 - |t|,       if |t| <= 1,
  0,             if |t| >= 1.
```

For `J0`,

```text
hat(J0)(t) =
  pi*t*(1 - |t|)*cot(pi*t) + |t|,  if 0 < |t| < 1,
  1,                               if t = 0,
  0,                               if |t| >= 1.
```

The source states `hat(J0)` and `hat(K0)` are continuous and supported in
`[-1,1]`.

## Interval Majorant and Minorant

Let `I=[a,b]` with `a<b`, and let `delta>0`.  Define the normalized interval
indicator

```text
chi_I(x) = 1      if a < x < b,
           1/2    if x = a or x = b,
           0      otherwise.
```

Define

```text
M^-_{I,delta}(z)
  =  1/2 * H0(delta*(z-a))
   - 1/2 * H0(delta*(z-b))
   - 1/2 * K0(delta*(z-a))
   - 1/2 * K0(delta*(z-b)),

M^+_{I,delta}(z)
  =  1/2 * H0(delta*(z-a))
   - 1/2 * H0(delta*(z-b))
   + 1/2 * K0(delta*(z-a))
   + 1/2 * K0(delta*(z-b)).
```

`UNCONDITIONAL` Selberg-Vaaler interval theorem:

```text
M^-_{I,delta}(x) <= chi_I(x) <= M^+_{I,delta}(x)
```

for every real `x`.

Both functions are real entire, integrable on `R`, and have exponential type at
most `2*pi*delta`.

Exact `L1` errors:

```text
integral_R (M^+_{I,delta}(x) - chi_I(x)) dx = 1/delta,
integral_R (chi_I(x) - M^-_{I,delta}(x)) dx = 1/delta.
```

Equivalently,

```text
hat(M^+_{I,delta})(0) = L + 1/delta,
hat(M^-_{I,delta})(0) = L - 1/delta.
```

## Fourier Transforms

The useful identity is

```text
1/2*H0(delta*(z-a)) - 1/2*H0(delta*(z-b))
  = delta * integral_a^b J0(delta*(z-y)) dy.
```

Thus the central `H0`-difference is the convolution of `chi_I` with
`delta*J0(delta*x)`.

For `u != 0`,

```text
hat(chi_I)(u) = (e(-a*u) - e(-b*u)) / (2*pi*i*u),
```

and

```text
hat(chi_I)(0) = L.
```

Therefore, for every real `u`,

```text
hat(M^\pm_{I,delta})(u)
  = hat(chi_I)(u) * hat(J0)(u/delta)
    +/- (1/(2*delta)) * (e(-a*u) + e(-b*u)) * hat(K0)(u/delta).
```

Here `+` gives the majorant and `-` gives the minorant.  The support is exactly
inside `[-delta, delta]`.

This is the formula to use in B2.  It avoids a common false shortcut: replacing
the central `H0`-difference by a naively truncated interval Fourier transform
without the `hat(J0)(u/delta)` factor.

## K=2 Sanity Numbers

For the B1 gate with raw-log strip and `K=2`:

```text
I_2 = [4, 8],
a = 4,
b = 8,
L = 4.
```

The clean first bandwidth choice is `delta=1`.  Then

```text
type <= 2*pi,
supp hat(M^\pm) subset [-1,1],
hat(M^+)(0) = 5,
hat(M^-)(0) = 3,
one-sided L1 error = 1.
```

This validates the formula-level constants.  It does not yet validate the
Track B defect bound, because the measured Q3 cross-correlation defect artifact
for `K=2` was not located in the repo during this pass.

## D2 Guardrails for B2

Preflight gate before any B2a work:

```text
docs/trackB/b2_uncertainty_tax_preflight.md
```

That gate records the unavoidable Selberg/Vaaler hard-edge tax
`>= 1/B_K` once the cone receiver has Fourier slack `B_K`.  Therefore a naive
route of the form "CLV majorant times ||g||_infty" is `FATAL` whenever the
mu-ledger asks for `epsilon_K = o(1/B_K)`.

The D2 object is the exact explicit-formula split:

```text
Q(Phi) = arch_term(Phi) - prime_term(Phi).
```

In the Q3 notes and Lean skeleton, the prime side uses the weight/node form

```text
prime_term(Phi) = sum_n 2*Lambda(n)/sqrt(n) * Phi(log n/(2*pi)).
```

Any B2 use of the pair above must state which variable is being majorized:

1. Raw-log variable `x=log n`.
2. Q3 node variable `xi=log n/(2*pi)`.

Dropping the `2*pi` conversion silently is a D2 failure.

Second D2 guard: the Selberg majorant of the interval is not by itself an
admissible proof of the signed edge defect.  The actual defect has the shape

```text
sum_{n in edge} Lambda(n)/sqrt(n) * g(log n),
```

with `g` constrained by the structured cross-correlation cone.  The pointwise
split `g = g_+ - g_-` is not allowed as a bandlimited move: `g_+` and `g_-`
need not remain bandlimited.  This is the known B2a trap.

Therefore B2 should prefer the explicit-formula route:

```text
Hermitian square / Q_W-like form
  -> apply Selberg-CLV extremal function inside the Guinand-Weil formula
  -> use the existing zero-side PSD structure as the replacement for the
     RH-dependent zero-side positivity used in prime-gap applications.
```

This is the B2b route.  It is not proven here.

## Current Verdict

`B1-FORMULA-READY / GATED`.

What is ready:

- explicit interval pair `M^- <= chi_I <= M^+`;
- exact exponential type `2*pi*delta`;
- exact Fourier support `[-delta,delta]`;
- exact transforms through `hat(J0)` and `hat(K0)`;
- exact one-sided `L1` error `1/delta`;
- K=2 formula sanity constants.

Open gates before claiming B1 complete:

0. Run the B2-0 uncertainty-tax preflight in
   `docs/trackB/b2_uncertainty_tax_preflight.md`; if the mu-ledger target is
   `o(1/B_K)`, do not pursue naive B2a.
1. Locate or generate the measured Q3 cross-correlation edge defect for
   `K=2`, then compare it to the corresponding CLV/Selberg bound.
2. Freeze whether the edge interval is expressed in raw `log n` or in Q3
   `xi_n = log n/(2*pi)` coordinates for the next experiment.
3. In B2, prove the cone transport without replacing a structured signed
   cross-correlation by arbitrary positive/negative parts.

If gate 3 blocks, escalate to Proshka in the required format:

```text
claim:
  The Selberg-Vaaler pair gives an unconditional B2b explicit-formula
  one-sided prime-edge bound once the test object is a Hermitian square.
blocker:
  Need to preserve the Q3 cross-correlation cone and D2 normalization through
  the explicit formula without RH-dependent zero-side input.
tried:
  B2a positive/negative split rejected because g_+, g_- are not bandlimited.
  B1 interval pair verified with hat(J0)/hat(K0) support and L1 constants.
minimal example:
  K=2, I=[4,8] in raw log variable, delta=1, M^+ integral 5,
  M^- integral 3, support [-1,1].
question:
  What is the minimal Hermitian-square formulation that lets the existing
  zero-side PSD replace the RH conditional input in the CMS prime-gap scheme?
```
