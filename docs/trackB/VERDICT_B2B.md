# Track B Verdict: S1 Witness To S3 B2b Gate

Status: GAP(B2b numerical gate not green).  This is strategy/diagnostic
documentation only: no Lean proof, no Q3.Main change, no route mutation, and
no RH/RH-conditional input.

## Verdict

```text
DONE verdict: B
B2b algebraic closure gate: ZERO_CONSISTENT
B2b PSD-eligibility gate: GAP
overall B2b gate: NOT GREEN
```

Reason: the four-term numerical decomposition closes to floating error on the
tested finite packet cone directions, but the smoothed zero-side proxy is not
nonnegative on all tested directions.  The failure is not an arithmetic
decomposition defect; it is an eligibility/PSD-slot defect.

## D2

Raw coordinate:

```text
a = r log p
xi = a / (2*pi)
edge = [2K,4K]
```

S3 checked finite packet Hermitian-square directions in `ker Q` using:

```text
prime_edge
  = arch_edge - zero_PSD_proxy - receiver_correction + boundary
```

where:

```text
prime_edge          = finite prime-power sum over [2K,4K]
arch_edge           = continuum edge matrix proxy
zero_PSD_proxy      = arch(M^+) - prime(M^+) for the smoothed receiver
receiver_correction = (prime(M^+) - prime_edge) - (arch(M^+) - arch_edge)
boundary            = 0 numerically because Qv ~= 0
```

The `zero_PSD_proxy` row is a numerical eligibility proxy, not a theorem input.

## Witness Card

Reference: `docs/trackB/WITNESS_cell62.md`.

Two-layer picture:

```text
blade at a_w ~= 7.130987:
  ZERO_CONSISTENT(edge-prime sign selection confirmed)

pit at a_min ~= 7.28:
  REFUTED(Fable corrected prediction: minimum=edge-prime)
  GAP(nature open; finite-cone witness, not outside cone)
```

S1-FINAL fixed-direction admissibility:

```text
Qv ~= (-3.55e-15, -3.55e-15)
||v||_G^2 ~= 1.000000000000001
finite packet status = FINITE_PACKET_HERMITIAN_SQUARE_BY_CONSTRUCTION
```

Fixed-direction Rayleigh accounting at `a_min=7.28`:

```text
minus_continuum_arch_model          ~= -1.65015
prime band [0, 2K-0.5]              ~= -0.986324
prime band [2K-0.5, 2K+0.5]         ~= +3.53058
prime band [2K+0.5, 4K]             ~= -0.655948
boundary_slot                       =   0
total                               ~= +0.238160
```

## S3 Gate Numbers

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvgate \
  --K 2 3 --schedule stable --grid-delta 0.5 --k-spline 5 \
  --p0-na 401 --receiver-delta 1 --test-count 10 --seed 1337
```

Summary:

```text
K=2:
  ell                         = 0.75
  cone tests                  = 10
  max closure relative error  = 9.92599e-17
  max |Qv|                    = 8.88178e-16
  min zero_PSD_proxy          = -8.66226e-4
  verdict                     = B2B_GATE_NOT_GREEN_ZERO_PSD_PROXY

K=3:
  ell                         = 0.75
  cone tests                  = 10
  max closure relative error  = 3.46669e-16
  max |Qv|                    = 2.22045e-15
  min zero_PSD_proxy          = -7.74361e-3
  verdict                     = B2B_GATE_NOT_GREEN_ZERO_PSD_PROXY
```

Worst rows:

```text
K=2, eig_lower:
  prime_edge                  ~= +0.328744
  arch_edge                   ~= +0.230245
  -zero_PSD_proxy             ~= +0.000866226
  -receiver_correction        ~= +0.0976330
  closure_rel                 ~= 5.55e-17

K=3, eig_upper:
  prime_edge                  ~= -0.953019
  arch_edge                   ~= -0.843746
  -zero_PSD_proxy             ~= +0.00774361
  -receiver_correction        ~= -0.117017
  closure_rel                 ~= 3.47e-16
```

## Status Dictionary

```text
PROVED: none
SKETCH: clvgate finite-packet numerical decomposition machinery
OPEN: analytic E5 attack and proof-grade zero-side eligibility mechanism
REFUTED: Fable corrected prediction that the sampled minimum is edge-prime
ZERO_CONSISTENT: algebraic decomposition closes on K=2,3 test directions
GAP: smoothed zero_PSD_proxy is negative on tested cone directions
```

## Input For Analytic E5 Attack

Worst-case enemy profile:

```text
1. blade near a_w ~= 7.131:
   sign is selected by ordinary edge primes near the left edge.
   top logs: log(1093), log(1091), log(1087).

2. pit near a_min ~= 7.28:
   not killed by prime-removal controls and not outside finite cone.
   S3 says the arithmetic split is consistent, so the next enemy is the
   smoothed zero-side eligibility/projection slot, not bookkeeping error.

3. K=3 stronger obstruction:
   min zero_PSD_proxy ~= -7.74e-3 on a tested cone direction.
   This is the current smallest numerical counter-signal to the naive B2b
   smoothed receiver route.
```

Next analytic question:

```text
Find a structure-preserving replacement for the smoothed zero-side slot:
signed PD decomposition, corrected cone projection, or a different receiver
whose zero-side term is genuinely PSD on the finite Hermitian-square cone.
```
