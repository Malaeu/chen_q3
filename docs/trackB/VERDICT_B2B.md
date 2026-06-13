# Track B Verdict: S1 Witness To S4 B2b Gate

Status: ZERO_CONSISTENT(S3 numerical closure gate green) plus
REFUTED(current smoothed receiver lift PSD eligibility) and OPEN(alternate
B2b admissible lift).  This is strategy/diagnostic documentation only: no Lean
proof, no Q3.Main change, no route mutation, and no RH/RH-conditional input.

## Verdict

```text
B2b closure verdict: GREEN under v5 numerical criterion
B2b algebraic closure gate: ZERO_CONSISTENT
B2b current smoothed-lift PSD eligibility: REFUTED
Route A small-negative-ledger for current family: REFUTED
B2b alternate admissible-lift status: OPEN
overall Track B status: OPEN, not proved
```

Reason: the four-term numerical decomposition closes to floating error on the
tested finite packet cone directions.  The smoothed zero-side proxy is not
nonnegative on all tested directions, and S4 confirms the stronger statement
that the current smoothed lift `Mplus*F_v` is sampled Fourier-negative by an
order-one margin.  That is a separate PSD-eligibility failure, not the v5 S3
closure criterion.

Pre-B2 route gate:

```text
docs/trackB/b2_uncertainty_tax_preflight.md
```

That gate kills naive B2a in the form "CLV majorant times ||g||_infty" whenever
the mu-ledger requires `epsilon_K = o(1/B_K)`.  It does not kill B2b; it is one
more reason B2b must preserve Hermitian-square / zero-side PSD structure
instead of paying the hard-edge scalar-mask tax.

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

## S4 Zero-Side Eligibility Audit

Reference: `docs/trackB/S4_ZERO_SIDE_ELIGIBILITY.md`.

```text
S4 verdict:
  B2B_S4_FATAL_NOT_PSD_ELIGIBLE

Scope:
  current smoothed receiver lift Mplus*F_v

Not affected:
  S3 closure gate remains B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC
```

Judge-before-player planted tests:

| K | positive plant `F_v` | min hat | negative plant `-F_v` | min hat | instrument |
| --- | --- | ---: | --- | ---: | --- |
| 2 | PASS | `-7.55e-13` | PASS | `-5.14477` | `S4_INSTRUMENT_VALID` |
| 3 | PASS | `+6.89e-12` | PASS | `-7.20072` | `S4_INSTRUMENT_VALID` |
| 3.5 | PASS | `-9.41e-11` | PASS | `-7.37385` | `S4_INSTRUMENT_VALID` |

Current lift failure:

| K | min hat `Mplus*F_v` | min hat `(Mplus-1_edge)*F_v` | S4 classification |
| --- | ---: | ---: | --- |
| 2 | `-1.68036` | `-0.412284` | `A_REAL_COUNTEREXAMPLE_TO_ELIGIBILITY` |
| 3 | `-2.67972` | `-0.449693` | `A_REAL_COUNTEREXAMPLE_TO_ELIGIBILITY` |
| 3.5 | `-2.44648` | `-0.459538` | `A_REAL_COUNTEREXAMPLE_TO_ELIGIBILITY` |

Meaning: the current smoothed zero-side lift is not PSD eligible.  This kills
that lift, not all B2b routes.  The remaining open route is to replace the
smoothed zero-side slot by a structure-preserving admissible lift, signed PD
decomposition, corrected cone projection, or finite ledger certificate.

## S5 Negative-Mass Ledger

Reference: `docs/trackB/S5_NEGATIVE_MASS_LEDGER.md`.

```text
S5.1 verdict:
  S5_NEGMASS_BUDGET_SIZED

Scope:
  current smoothed lift family L=Mplus*F_v and E=(Mplus-1_edge)*F_v

Consequence:
  Route A signed PSD ledger is refuted for this current family.
```

Summary:

| K | object | min hat | neg/L1 | q3-neg/L1 | negative width on `[0,2]` |
| --- | --- | ---: | ---: | ---: | ---: |
| 2 | `L` | `-1.68036` | `0.499632` | `0.499667` | `0.978` |
| 2 | `E` | `-0.412284` | `0.508842` | `0.522080` | `1.014` |
| 3 | `L` | `-2.67972` | `0.500130` | `0.500830` | `0.974` |
| 3 | `E` | `-0.449693` | `0.494477` | `0.486656` | `0.958` |
| 3.5 | `L` | `-2.44648` | `0.500021` | `0.500286` | `0.986` |
| 3.5 | `E` | `-0.459538` | `0.506019` | `0.513305` | `0.988` |

Route B correction:

```text
hat(L_proj)=max(hat(L),0) can repair PSD.
The danger is projection-loss / loss of physical edge-control, not loss of
Hermitian-square itself.
```

Route status after S5.1:

```text
A signed ledger: REFUTED_FOR_CURRENT_FAMILY
B spectral clipping: DEFERRED_BY_S5_NEGMASS_BUDGET_SIZED
C structure-first PSD lift: MAIN_OPEN_ROUTE, starts with C0 uncertainty-tax
D finite ledger: PARKED_LAST_ROUTE
```

## S2.5 Gap Anatomy

Source: `docs/trackB/b2b_explicit_formula_route_gap.md`.

| slot | status | why | failure class |
| --- | --- | --- | --- |
| arch | SKETCH/OPEN | Continuum matrices exist, but raw-log vs `xi=log n/(2*pi)` normalization must be frozen before theorem constants are compared. | normalization |
| zero_PSD | GAP | Q3 PSD applies only after the lifted test is proved corrected positive-definite / Hermitian-square. Ordinary Selberg insertion is not PSD-preserving. | sign / cone eligibility |
| prime | GAP | Pointwise `chi_I <= M+` does not give an operator inequality on signed `F_v`; `prime_edge <= lifted_prime` is the missing cone-transport lemma. | sign / cone transport |
| boundary | OPEN | No concrete boundary/cap counterterm is exhibited in the route-gap file. S3 has numeric `Qv~=0`, but proof-grade cap/boundary bookkeeping is not supplied. | cap/boundary bookkeeping |

Fable prediction check:

```text
boundary/cap as primary confirmed failure: NOT CONFIRMED BY THIS FILE
active documented failure: sign/cone transport + zero-side eligibility
```

## Witness Card

Reference: `docs/trackB/WITNESS_cell62.md`.

Two-layer picture:

```text
blade at a_w ~= 7.130987:
  ZERO_CONSISTENT(edge-prime sign selection confirmed)

pit at a_min ~= 7.28:
  REFUTED(Fable corrected prediction: minimum=edge-prime)
  NOT_A_BUG_BOOKKEEPING_MEMBER under S3 witness reconciliation
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
  closure verdict             = B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC
  eligibility status          = GAP_ZERO_PSD_PROXY_NEGATIVE_ON_TESTS

K=3:
  ell                         = 0.75
  cone tests                  = 10
  max closure relative error  = 3.46669e-16
  max |Qv|                    = 2.22045e-15
  min zero_PSD_proxy          = -7.74361e-3
  closure verdict             = B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC
  eligibility status          = GAP_ZERO_PSD_PROXY_NEGATIVE_ON_TESTS

K=3.5 witness reconciliation:
  witness a                   = 7.28
  local S(a)                  = -2.12171e-2
  global closure rel          = 0
  min zero_PSD_proxy          = -1.46782e-4
  pit verdict                 = NOT_A_BUG_BOOKKEEPING_MEMBER
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
OPEN: analytic E5 attack, alternate admissible lift, replacement zero-side slot
REFUTED: Fable corrected prediction that the sampled minimum is edge-prime
REFUTED: current smoothed receiver lift Mplus*F_v is PSD eligible
REFUTED: Route A small-negative-ledger for the current smoothed family
ZERO_CONSISTENT: algebraic decomposition closes on K=2,3 test directions and
  on the K=3.5 witness direction
GAP: exact mu-budget ratio absent from S5 inputs; route-gap file still lacks
  proof-grade cone transport/admissible lift for any replacement lift
```

## Input For Analytic E5 Attack

Worst-case enemy profile:

```text
1. blade near a_w ~= 7.131:
   sign is selected by ordinary edge primes near the left edge.
   top logs: log(1093), log(1091), log(1087).

2. pit near a_min ~= 7.28:
   not killed by prime-removal controls and not outside finite cone.
   S3 witness reconciliation says it is a bookkeeping member, not an
   arithmetic residual.  The next enemy is the smoothed zero-side
   eligibility/projection slot, not local pointwise negativity.

3. S4 stronger eligibility obstruction:
   sampled Fourier min of current `Mplus*F_v` is `-1.68036` at K=2,
   `-2.67972` at K=3, and `-2.44648` at K=3.5.
   This refutes the current smoothed receiver lift as a PSD zero-side object.

4. S5 negative-mass obstruction:
   the negative spectral part of `Mplus*F_v` occupies about half of the
   sampled spectral L1 mass on K=2,3,3.5.  This refutes the "small signed
   ledger" rescue for the current family.
```

Next analytic question:

```text
Run Route C0: decide whether PSD + bandlimit + edge-control is compatible with
the actual B_K and mu-budget before constructing a new direct PSD lift.
```
