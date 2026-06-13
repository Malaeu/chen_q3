# Track B S4: Zero-Side Eligibility Audit

Status: REFUTED(current smoothed receiver lift PSD eligibility) plus
OPEN(alternate B2b admissible lift).  This is a numerical diagnostic audit
only: no Lean proof, no Q3.Main change, no route mutation, and no RH-conditional
input.

## Verdict

```text
S3 closure gate:
  B2B_GATE_GREEN_NUMERICAL_DIAGNOSTIC

S4 zero-side eligibility gate:
  B2B_S4_FATAL_NOT_PSD_ELIGIBLE

Scope of the fatal result:
  current smoothed receiver lift Mplus*F_v

What remains open:
  alternate B2b lift, signed positive-definite decomposition, corrected cone
  projection, or finite Chebyshev/ledger route
```

This does not reopen B2a and does not change the S3 verdict.  S3 proved, as a
finite diagnostic, that the four-slot decomposition closes.  S4 asks a
different question: whether the smoothed zero-side object is actually eligible
for a PSD zero-side theorem.  The answer for the current lift is no.

## Command

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clveligibility \
  --K 2 3 3.5 --schedule stable --grid-delta 0.5 --k-spline 5 \
  --p0-na 401 --receiver-delta 1 --directions opnorm \
  --quad-na 4001 --fourier-u-max 2 --fourier-nu 1001 --psd-tol 1e-8
```

D2 convention:

```text
raw a = r log p
xi = a / (2*pi)
hat(f)(u) = int f(a) exp(-2*pi*i*u*a) da after even extension
```

The audit is sampled Fourier sign testing, not an interval-certified theorem.
The negative margins below are order-one, so the result is not a floating-floor
artifact.

## S4.0 Judge Before Player

The detector was checked on planted positive and planted negative objects
before testing the current lift.

| K | positive plant `F_v` | min hat | negative plant `-F_v` | min hat | instrument |
| --- | --- | ---: | --- | ---: | --- |
| 2 | PASS | `-7.55e-13` | PASS | `-5.14477` | `S4_INSTRUMENT_VALID` |
| 3 | PASS | `+6.89e-12` | PASS | `-7.20072` | `S4_INSTRUMENT_VALID` |
| 3.5 | PASS | `-9.41e-11` | PASS | `-7.37385` | `S4_INSTRUMENT_VALID` |

Interpretation: the positive finite-packet Hermitian-square profile is accepted
within `psd_tol=1e-8`, while the planted negative object is rejected with large
margin.  Therefore the detector is good enough for this S4 diagnostic.

## S4.1 Eligibility Inventory

| requirement | status | note |
| --- | --- | --- |
| Real/even test convention | ZERO_CONSISTENT | The audit uses the even cosine/Fourier convention recorded above. |
| D2 normalization | ZERO_CONSISTENT | Raw `a=r log p` and `xi=a/(2*pi)` are explicit in the runner output. |
| Finite packet Hermitian square | ZERO_CONSISTENT for `F_v` | The raw profile `F_v` passes the planted PSD check. |
| Smoothed lift Hermitian square | REFUTED for `Mplus*F_v` | Multiplication by the Selberg/Vaaler majorant is not PSD-preserving. |
| Correction object eligibility | REFUTED for `(Mplus-1_edge)*F_v` | The correction also has sampled negative Fourier values. |
| Exponential type / receiver support | SKETCH | Selberg receiver support is documented in `clv_pair.md`, but support alone does not imply PSD eligibility. |
| Explicit formula sign convention | ZERO_CONSISTENT for closure | S3 closure holds; sign convention is not the S4 failure. |
| Gamma/arch/cap bookkeeping | OPEN | Still needed for a proof-grade alternate lift, but not the present failure. |
| Q3 zero-side theorem object | GAP | The current smoothed object is not the theorem object because it is not PSD eligible. |

## S4.2 Four-Slot Table

Source for S2.5 route anatomy:
`docs/trackB/b2b_explicit_formula_route_gap.md`.

| slot | closure_status | zero_side_proxy_value | PSD_eligibility_status | failure_reason | repair_candidate |
| --- | --- | --- | --- | --- | --- |
| arch | `ZERO_CONSISTENT(S3 closure)` | n/a | n/a | Normalization/proof constants still need a theorem-grade raw-log vs `xi` freeze. | Freeze raw/xi theorem statement and compare constants only after lift is fixed. |
| zero_PSD | `ZERO_CONSISTENT(S3 closure)` | K=2 `-8.66e-4`; K=3 `-7.74e-3`; K=3.5 `-1.47e-4` | `PSD_INELIGIBLE_CERTIFIED` for sampled `Mplus*F_v` | `Mplus*F_v` has large negative sampled Fourier values; current lift is not PSD eligible. | Replace lift by signed PD decomposition, corrected cone projection, or finite Chebyshev/ledger certificate. |
| prime | `ZERO_CONSISTENT(S3 closure)` | finite prime sum closes | n/a | Pointwise `1_edge <= Mplus` does not imply operator order on signed cross-correlations. | Prove a cone-transport lemma only for a PSD-eligible lift, or avoid scalar majorants. |
| boundary | `ZERO_CONSISTENT(numeric Qv~=0)` | n/a | n/a | No concrete cap/boundary counterterm is the present failure; proof-grade bookkeeping is still open. | Re-audit cap/boundary only after a replacement lift changes the terms. |

Current lift Fourier audit:

| K | min hat `Mplus*F_v` | first negative u | min hat `(Mplus-1_edge)*F_v` | verdict |
| --- | ---: | ---: | ---: | --- |
| 2 | `-1.68036` | `0.080` | `-0.412284` | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE` |
| 3 | `-2.67972` | `0.000` | `-0.449693` | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE` |
| 3.5 | `-2.44648` | `0.038` | `-0.459538` | `B2B_S4_FATAL_NOT_PSD_ELIGIBLE` |

## S4.3 Negative Classification

Classification required by the S4 protocol:

```text
A_REAL_COUNTEREXAMPLE_TO_ELIGIBILITY
```

Meaning:

```text
The current smoothed receiver lift Mplus*F_v is a real sampled counterexample
to the PSD eligibility claim for that lift.
```

This is not a counterexample to all B2b strategies.  It kills the current
smoothed lift as the zero-side PSD theorem object.  It does not kill a different
admissible lift, a signed positive-definite decomposition, a corrected cone
projection, or a finite ledger route.

## S4.4 Final Gate

```text
B2B_S4_FATAL_NOT_PSD_ELIGIBLE
```

Do not claim Track B proof.  Do not treat S3 closure as failed.  Do not reopen
naive B2a.  The next mathematical object must be a structure-preserving
replacement for the smoothed zero-side slot.

## Status Dictionary

```text
PROVED: none
SKETCH: finite sampled Fourier eligibility detector with planted tests
OPEN: alternate B2b lift / signed PD decomposition / corrected cone projection
REFUTED: current smoothed receiver lift Mplus*F_v is PSD eligible
ZERO_CONSISTENT: S3 closure identity remains green; planted S4 detector works
GAP: proof-grade theorem constants and cap/boundary bookkeeping for any new lift
```
