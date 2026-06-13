# Track B Witness Cell62

Status: ZERO_CONSISTENT(pit is an S3 bookkeeping member) plus
GAP(zero-side eligibility remains analytic).  This is diagnostic evidence
only: not a proof of E5', not a Lean proof, and not a route mutation.

## Point

```text
K = 3.5
ell = 1.375
receiver_delta = 1
edge = [2K,4K] = [7,14]
cell = 62
first crossing a_w = 7.130987044271352
sampled minimum a_min ~= 7.28
```

## D2

Raw coordinate:

```text
a = r log p
xi = a / (2*pi)
```

The local witness density is

```text
S(a) = exp(-a/2) * (H'(a) - H(a)/2)
H(a) = (M^+_[2K,4K],delta(a) - 1_[2K,4K](a)) * F_v(a).
```

The four slots below are diagnostic labels for this local Stieltjes
product-rule density.  The zero-side PSD term is global, not a pointwise
scalar in this local formula.

## First Crossing Anatomy

At `a_w = 7.130987044271352`:

```text
S(a_w)                              ~= -5.66307e-8
arch_proxy_smooth_receiver(a_w)     ~= -1.15274e-1
-zero_PSD pointwise slot            =   0
prime_edge_hard_indicator_slot      ~= +1.15274e-1
boundary_jump_slot                  =   0
```

The first crossing is a near-total cancellation:

```text
|S| / (|arch_proxy| + |edge_slot|) ~= 2.45636e-7
```

Controls at `a_w`:

```text
full prime powers                         ~= -5.66307e-8
ordinary primes only                      ~= +4.62498e-3
p=2 only                                  ~= +1.13052e-2
exclude log n > a_w - 0.5                 ~= +1.24228e-2
exclude [a_w-delta,a_w+delta]             ~= +1.14187e-2
```

Verdict at first crossing:

```text
ZERO_CONSISTENT(a_local_first_crossing_edge_primes_confirmed)
```

## Minimum Addendum

The v5 addendum requires the same controls at the sampled minimum
`a_min ~= 7.28`.  This fails the corrected Fable prediction.

At `a_min = 7.28`:

```text
S(a_min)                            ~= -2.12171e-2
arch_proxy_smooth_receiver(a_min)   ~= -1.67043e-1
-zero_PSD pointwise slot            =   0
prime_edge_hard_indicator_slot      ~= +1.45826e-1
boundary_jump_slot                  =   0
```

The minimum is no longer a tiny cancellation:

```text
|S| / (|arch_proxy| + |edge_slot|) ~= 6.78146e-2
```

Controls at `a_min`:

```text
full prime powers                         ~= -2.12171e-2
ordinary primes only                      ~= -1.90030e-2
p=2 only                                  ~= -3.08213e-3
exclude log n > a_min - 0.5               ~= -2.18879e-3
exclude [a_min-delta,a_min+delta]         ~= -3.03605e-3
```

Therefore the negative region is not killed by removing the local/right edge
prime shifts after reselecting the diagnostic opnorm direction.  LEVEL 3
answered this protocol question with `NO`: freeze the full witness direction
and run prime-removal tests only as linear difference accounting in that fixed
direction.

## S1-FINAL Fixed-Direction Accounting

Protocol:

```text
direction = full correction opnorm witness, frozen
prime-removal tests = linear Rayleigh/accounting on the same direction
no reselect under prime-removal variants
```

D2: the band table below is additive for the fixed Rayleigh correction

```text
prime(M^+ - 1_edge) - continuum(M^+ - 1_edge) + boundary
```

It is not a literal pointwise prime-band decomposition of the local density
`S(a)`.

At `a_min = 7.28`, the local pointwise slot remains:

```text
S(a_min)                            ~= -2.12171e-2
arch_proxy_smooth_receiver(a_min)   ~= -1.67043e-1
prime_edge_hard_indicator_slot      ~= +1.45826e-1
boundary_jump_slot                  =   0
```

Fixed-direction additive Rayleigh table:

```text
minus_continuum_arch_model          ~= -1.65015
prime band [0, 2K-0.5]              ~= -0.986324   (143 shifts)
prime band [2K-0.5, 2K+0.5]         ~= +3.53058    (165 shifts)
prime band [2K+0.5, 4K]             ~= -0.655948   (73870 shifts)
boundary_slot                       =   0
total                               ~= +0.238160
full correction Rayleigh            ~= +0.238160
table reconstruction error          ~= 2.63e-12
```

The middle shoulder band `[2K-0.5,2K+0.5] = [6.5,7.5]` is the sign-selecting
positive mass in the fixed-direction Rayleigh accounting.  Its largest terms
are again ordinary primes just below the left edge:

```text
p=1093, log p ~= 6.9966814882, contribution ~= +0.210270
p=1091, log p ~= 6.9948499858, contribution ~= +0.209873
p=1087, log p ~= 6.9911768871, contribution ~= +0.209001
```

Fixed-direction prime-removal controls:

```text
full correction                      ~= +0.238160
ordinary primes only                 ~= +0.195353
p=2 powers only                      ~= -1.63440
exclude log n > a_min - 0.5          ~= -3.80080
exclude [a_min-delta,a_min+delta]    ~= -1.80707
```

So the fixed-direction linear accounting confirms that the edge shoulder
prime band is carrying the positive correction mass.  It does not by itself
explain the pointwise pit away.  S3 later decided that the pit is a legitimate
member of the B2b bookkeeping, not a decomposition residual.

Admissibility of the frozen direction:

```text
Q-functional 1                       ~= -3.55e-15
Q-functional 2                       ~= -3.55e-15
max |Qv|                             ~= 3.55e-15
G-norm squared                       ~= 1.000000000000001
finite packet status                 =  FINITE_PACKET_HERMITIAN_SQUARE_BY_CONSTRUCTION
global Q3 status                     =  DIAGNOSTIC_ONLY_NOT_A_LEAN_CERTIFICATE
```

Verdict for the pit:

```text
NOT_OUT_OF_CONE
FINITE_CONE_WITNESS
S3_BOOKKEEPING_MEMBER
```

S3 witness reconciliation:

```text
K = 3.5
a_min = 7.28
local S(a_min) ~= -2.12171e-2
global four-slot closure rel = 0
pit_accounting_verdict = NOT_A_BUG_BOOKKEEPING_MEMBER
```

## Scan

Coarse sampled scan on `[2K-0.2,2K+0.4] = [6.8,7.4]`, step `0.01`:

```text
negative sampled zone ~= [7.14,7.40]
minimum              ~= -2.12171e-2 at a ~= 7.28
```

Fine sampled scan around `a_min`, step `0.0005`:

```text
minimum ~= -2.12213e-2 at a ~= 7.278
```

Nearest prime-power logs to the first crossing are ordinary primes:

```text
log(1249) ~= 7.1300985101
log(1259) ~= 7.1380730340
log(1237) ~= 7.1204443724
```

The local prime-correction window remains ordinary-prime dominated; the top
contributions are primes just below the left edge:

```text
p=1093, log p ~= 6.9966814882, contribution ~= 0.210270
p=1091, log p ~= 6.9948499858, contribution ~= 0.209873
p=1087, log p ~= 6.9911768871, contribution ~= 0.209001
```

## Float Guard

At the addendum stop, `mpmath` was unavailable in both `.venv` and system
Python, and the `.venv` did not contain `pip`.  The named cancellation guard
was therefore run with Python `decimal` at precision `30`, recombining the
same float64 analytic atoms.  This checks the arithmetic of the named
cancellation, not source interval containment.

```text
a_w:
  centered64 ~= -5.66307198010672e-8
  decimal30  ~= -5.66307198023097e-8
  abs diff   ~= 1.24e-18

a_min:
  centered64 ~= -2.12171175273790e-2
  decimal30  ~= -2.12171175273790e-2
  abs diff   ~= 8.32e-18
```

Float-guard verdict:

```text
ZERO_CONSISTENT(float cancellation not responsible)
```

S1-FINAL installed `mpmath` into `.venv` via `ensurepip` plus `pip install
mpmath`.  A legal dps-30 recombine at `a_min=7.28` gives:

```text
mpmath30 S(a_min) ~= -0.0212171175273790354859108488959
```

## Prediction Ledger

```text
Fable prediction 1a: prime_edge dominates point value
Status: REFUTED

Corrected first-crossing statement:
edge primes decide the sign of an almost complete arch-vs-edge cancellation
Status: ZERO_CONSISTENT at a_w

Addendum statement:
minimum negativity also disappears without edge primes
Status: REFUTED

Corrected two-layer picture:
1. blade at a_w ~= 7.131: edge-prime sign selection CONFIRMED
2. pit at a_min ~= 7.28: survives prime controls, is finite-cone admissible,
   and is an S3 bookkeeping member rather than an arithmetic residual
Status: ZERO_CONSISTENT(pit bookkeeping)
```

## S1-FINAL Verdict

```text
ZERO_CONSISTENT(first crossing: edge-prime sign selection confirmed)
REFUTED(Fable corrected prediction: minimum = edge-prime)
ZERO_CONSISTENT(pit: finite-cone witness and S3 bookkeeping member)
```

The remaining Track B gap is not this pointwise pit.  It is proof-grade
admissible lift / zero-side PSD eligibility for the smoothed receiver.
