# Track B B2b: Semi-Analytic Packet Derivative Enclosure

Status: RP4/B2 diagnostic and proof-generator refinement.  This is not a
proof of E5p, not a proof of RH, and not a Lean proof file.

This note follows `docs/trackB/b2b_signcert_prototype.md`.  The previous
prototype identified the next certificate shape:

```text
edge jump split + sign certificate for H_v'(a)-H_v(a)/2 on smooth pieces.
```

This note removes one source of sampling from that shape: the packet profile
`F_v` now has analytic B-spline derivatives in the probe.

## D2 Normalization

Raw variable:

```text
a = r * log p,
x = exp(a),
I_K = [2K, 4K].
```

Q3 variable:

```text
xi = a/(2*pi),
w_Q(n) = 2*Lambda(n)/sqrt(n).
```

Smooth correction:

```text
E_delta(a) = M^+_[2K,4K],delta(a) - 1_[2K,4K](a),
H_v(a) = E_delta(a) F_v(a),
phi_v(x) = x^(-1/2)H_v(log x).
```

For a smooth segment away from `2K` and `4K`:

```text
H_v'  = E_delta' F_v + E_delta F_v',
H_v'' = E_delta'' F_v + 2 E_delta' F_v' + E_delta F_v''.
```

The signed variation density and its derivative are:

```text
S(a)  = exp(-a/2) * (H_v'(a) - H_v(a)/2),
S'(a) = exp(-a/2) * (H_v''(a) - H_v'(a) + H_v(a)/4).
```

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler / CLV interval majorant formulas from
  `docs/trackB/clv_pair.md`.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL`: cardinal/centered B-spline derivative identity; the
  derivative of a spline is a lower-degree B-spline combination.
  Reference for the general B-spline derivative identity:
  https://en.wikipedia.org/wiki/B-spline
- `UNCONDITIONAL`: finite Chebyshev staircase `U_J` from
  `docs/trackB/b2b_finite_U_staircase_audit.md`.
- `UNCONDITIONAL`: elementary Stieltjes/BV bookkeeping.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap estimates.

## Probe Update

`scripts/trackb_edge_operator_probe.py clvsigncert` now computes:

```text
F_v'  via centered B-spline derivative,
F_v'' via centered B-spline second derivative,
S'(a) from H_v'', H_v', H_v.
```

The emitted smooth-segment fields include:

```text
profile_derivative_source = analytic_centered_b_spline_derivative
receiver_derivative_source = sampled_finite_difference
profile_derivative_max_abs
profile_second_derivative_max_abs
receiver_derivative_max_abs
receiver_second_derivative_max_abs
signed_density_derivative_max_abs
```

This is still not a proof certificate, because `E_delta'` and `E_delta''` are
currently sampled finite differences.  The point of the update is sharper
blocker localization: packet derivatives are no longer the main missing
analytic ingredient.

## Formula Check

The probe was checked against central finite differences for the K=3.5
opnorm direction.  On points in `[6.65,7.1]`, with finite-difference step
`h=1e-3`, the maximum absolute discrepancies were:

```text
F_v'  error ~= 3.18e-5
F_v'' error ~= 4.15e-4
```

For smaller `h`, the second-difference comparison degrades from floating-point
cancellation, so `h=1e-3` is the useful sanity scale here.

## K=3.5 Worklist After Semi-Analytic Packet Derivatives

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3.5 --ell 1.375 --schedule fixed --receiver-delta 1 \
  --p0-na 401 --ledger-cells 120 --cert-na 1601 --cells 58 59 61
```

Results:

```text
cell 58:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.067408
  signed-density derivative max: ~0.760459
  receiver second-derivative max: ~0.817577

cell 59:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.128763
  signed-density derivative max: ~0.490696
  receiver second-derivative max: ~2.239871

cell 61:
  recommendation: smooth_sign_cert_plus_explicit_jump_cert
  smooth side guards: ~0.022025 and ~0.007154
  signed-density derivative max: ~1.109430 and ~0.271333
  receiver second-derivative max: ~3.514500 and ~3.537610
```

Interpretation:

- The previous worklist classification survives the semi-analytic derivative
  rewrite.
- K=3.5 cells `58,59,61` remain the best first theorem-producing target.
- The smallest guard is still the right smooth side of cell `61`, about
  `0.007154`, so the receiver derivative enclosure must be tight enough there.

## K=3 Worklist After Semi-Analytic Packet Derivatives

Run:

```text
.venv/bin/python scripts/trackb_edge_operator_probe.py clvsigncert \
  --K 3 --ell 0.75 --schedule fixed --receiver-delta 0.5 \
  --p0-na 201 --ledger-cells 80 --cert-na 1601 --cells 35 36 39
```

Results:

```text
cell 35:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.058968
  signed-density derivative max: ~0.079419

cell 36:
  recommendation: smooth_sign_cert_candidate
  sampled sign guard: ~0.048085
  signed-density derivative max: ~0.097791

cell 39:
  recommendation: isolate_roots_then_sign_certify
  root bracket: [5.995196059570327, 5.995289794921890]
  signed-density derivative max: ~0.293905
```

Interpretation:

- K=3 cells `35,36` are still straightforward smooth sign candidates.
- K=3 cell `39` remains a single root-isolation subproblem; this is not caused
  by a packet-derivative sampling artifact.

## Refined Generator Contract

The theorem-producing generator should now split into two layers:

```text
Layer 1: packet profile certificate
  centered B-spline formulas for F_v, F_v', F_v'';
  finite support and polynomial pieces from the packet backend.

Layer 2: Selberg receiver certificate
  interval enclosures for E_delta, E_delta', E_delta'';
  combine with Layer 1 to bound S and S';
  certify sign stability or isolate roots.
```

Preferred next experiment:

```text
Derive and implement explicit derivative helpers for Vaaler H0/K0, then rerun
clvsigncert with receiver_derivative_source =
analytic_vaaler_polygamma_derivative.
```

Follow-up:

- `docs/trackB/b2b_receiver_derivative_enclosure.md` implements this
  experiment.  `clvsigncert` now reports
  `receiver_derivative_source = analytic_vaaler_polygamma_derivative`.  The
  remaining gap is proof-grade interval enclosure near Vaaler interpolation
  nodes, not sampled receiver differentiation.

## Verdict

`PARTIAL(packet-profile derivative sampling removed)`.

`GAP(Selberg receiver derivative enclosure still sampled)`.

`FATAL(treating semi-analytic sampled receiver guards as proof)`.

Track B remains active.

## Proshka Audit Block

Claim:
The selected `V_J` sign-certificate worklist no longer depends on sampled
packet-profile derivatives.  `F_v'` and `F_v''` are computed by analytic
centered B-spline derivative formulas; the remaining analytic gap is the
Selberg receiver derivative enclosure.

Point of blockage:
`E_delta'` and `E_delta''` are still sampled finite differences.  A proof
certificate needs explicit interval enclosures for the Vaaler/Selberg receiver
and its first two derivatives.

What was tried:
Added analytic centered B-spline derivative helpers to the Track B probe and
reran the K=3 and K=3.5 worklists.

Minimal example:
At K=3.5 cell `61`, after the jump split both smooth sides remain sampled
sign-stable.  The smaller guard is `~0.007154`, while the receiver
second-derivative sampled max is `~3.537610`; this is the tightest first
receiver-derivative enclosure target.

Question for Proshka:
Should we derive closed-form interval enclosures for the Vaaler `H0/K0`
derivatives from the trigamma/polygamma formulas, or switch to a finite
trigonometric/partial-fraction representation with rational interval bounds
for the receiver?
