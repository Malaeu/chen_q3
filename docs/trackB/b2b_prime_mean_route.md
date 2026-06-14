# Track B B2b: Ordinary-Prime Mean Route And Hilbert Spacing Barrier

Status: B2 theorem-shape audit.  This is not a proof certificate and does not
close E5p.  It tests whether a direct Montgomery--Vaughan / large-sieve mean
estimate can control the distributed ordinary-prime edge defect found in
`docs/trackB/b2b_finiteop_tail_probe.md` and
`docs/trackB/b2b_stability_schedule.md`.

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

The spacing probe below uses raw-log frequencies `lambda_p = log p`.  The Q3
gap is `delta_xi = delta_raw/(2*pi)`.

## Allowed Inputs

- `UNCONDITIONAL`: Montgomery--Vaughan Hilbert inequality, H. L. Montgomery
  and R. C. Vaughan, *Hilbert's Inequality*, J. London Math. Soc. (2) 8
  (1974), 73--82, DOI `10.1112/jlms/s2-8.1.73`.
  Source: https://doi.org/10.1112/jlms/s2-8.1.73
- `UNCONDITIONAL`: CLV Gaussian subordination / Beurling--Selberg extremal
  functions remain available from `docs/trackB/clv_pair.md`.  Source:
  Carneiro--Littmann--Vaaler, arXiv:1008.4969,
  https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL / finite enumeration`: the spacing and weight sums for a
  fixed K window are direct finite computations over prime-power shifts.

Not used as theorem inputs:

- Carneiro--Milinovich--Soundararajan prime-gap conclusions are conditional on
  RH.  Their Fourier-optimization setup remains a route analogy only, not an
  input theorem.  Source: https://arxiv.org/abs/1708.04122
- Recent work on weighted Montgomery--Vaughan constants, e.g. Yangjit
  arXiv:2203.14950, is useful context but does not remove the D2 spacing
  barrier for this edge problem.  Source: https://arxiv.org/abs/2203.14950

Forbidden inputs remain unchanged: no RH/GRH, no FQ-transfer, no de Branges
positivity, and no conditional prime-gap theorem.

## Candidate Generic Hilbert Route

For distinct raw frequencies `lambda_j`, Montgomery--Vaughan type Hilbert
control has the schematic form

```text
|sum_{j != k} x_j conj(y_k)/(lambda_j-lambda_k)|
  <= (pi/delta) ||x||_2 ||y||_2,

delta = min_{j != k} |lambda_j-lambda_k|.
```

If we apply this directly to the ordinary-prime edge nodes

```text
lambda_p = log p,     log p in [2K,4K],
```

then `delta` is controlled by the smallest neighboring log-prime gap near the
top of the window.  In the worst integer-node model,

```text
delta_raw >= log(1 + exp(-4K)),
```

so `pi/delta_raw` grows on the order of `exp(4K)`.  That is the wrong scale
for B3, which needs an error family of the form

```text
epsilon_K <= C * K^(-c),     c > 0.
```

This route also drops exactly the structure we cannot afford to drop:

- the corrected positive-definite / cross-correlation cone,
- compact-support live prime-shift filtering,
- the boundary-null `kerQ` constraints,
- any smoothing or averaging coming from CLV/Selberg receivers.

Therefore a separation-only Hilbert estimate is allowed mathematics, but not a
credible E5p closure mechanism.

## Spacing Probe

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py spacing \
  --K 2 2.5 3 3.5
```

The new `spacing` mode reports ordinary-prime log gaps in the raw edge
`[2K,4K]`, plus the separation-only Hilbert barrier `pi/min_gap`.

```text
K=2.0:
  ordinary primes = 413
  min raw log gap = 6.734006988e-4
  median raw log gap = 5.015821415e-3
  pi/min_gap = 4.665e3
  pi/median_gap = 6.263e2
  ordinary weight fraction = 0.9733

K=2.5:
  ordinary primes = 2432
  min raw log gap = 9.157509164e-5
  median raw log gap = 8.355528190e-4
  pi/min_gap = 3.431e4
  pi/median_gap = 3.760e3
  ordinary weight fraction = 0.9890

K=3.0:
  ordinary primes = 14833
  min raw log gap = 1.228878648e-5
  median raw log gap = 1.348520675e-4
  pi/min_gap = 2.556e5
  pi/median_gap = 2.330e4
  ordinary weight fraction = 0.9955

K=3.5:
  ordinary primes = 92934
  min raw log gap = 1.663240392e-6
  median raw log gap = 2.094846808e-5
  pi/min_gap = 1.889e6
  pi/median_gap = 1.500e5
  ordinary weight fraction = 0.9981
```

Compare this with the stability-filtered finite-op epsilons from
`docs/trackB/b2b_stability_schedule.md`:

```text
K=2.0:  epsilon ~= 0.1014
K=2.5:  epsilon ~= 0.4194
K=3.0:  epsilon ~= 0.1096
K=3.5:  epsilon ~= 0.2386
```

The generic separation constant is several orders of magnitude larger than the
actual projected finite defect.  It sees node crowding, not the structured
cross-correlation cancellation.

## Verdict

`GAP(generic Hilbert/large-sieve spacing control cannot close E5p)`.

What this kills:

```text
apply Montgomery--Vaughan directly to log-prime edge nodes
  -> use only min separation
  -> get B3 decay
```

The theorem is unconditional, but the transfer drops the cone.  The resulting
constant has the wrong scale.

## What Remains Viable

The next theorem shape must keep more structure than generic spacing.

1. Structured ordinary-prime mean estimate:

```text
R_K(F) =
  sum_{p: log p in [2K,4K]} (log p)/sqrt(p) * F(log p)
  - int_{2K}^{4K} e^(a/2) F(a) da

|R_K(F)| <= epsilon_K * <v,Gv>,
epsilon_K <= C*K^(-c),
```

where `F=F_v` is not arbitrary.  It must come from the boundary-null
B-spline/cross-correlation/positive-definite cone.

2. Smoothed CLV receiver:

Replace the hard interval by a CLV/Selberg bandlimited receiver and measure
whether the residual family has the predicted `C*exp(-alpha*delta*K)/delta`
tradeoff.  This keeps B2b alive because zero-side PSD may replace the RH
conditional step in the prime-gap analogy.

3. Different packet family:

The Step13 B-spline packet schedule did not give B3 decay under stability
filters.  A prolate/energy-concentration basis may be the right normalized
family before retrying finite-op decay.

## Concrete Next Experiment

Use the finite-op worst vectors as structured test functions and measure the
smoothed prime-mean residual after replacing `1_[2K,4K]` by CLV/Selberg
receivers at several bandwidths `delta`.

Minimal numerical target:

```text
K in {2.0, 2.5, 3.0, 3.5}
packet family = current stable candidates from b2b_stability_schedule.md
receivers = CLV/Selberg interval majorants at delta in {0.25, 0.5, 1.0, 2.0}
report:
  residual / <v,Gv>,
  arch-side cost,
  zero-side PSD eligibility,
  best epsilon_K(delta).
```

If the residual still tracks the separation barrier, this branch is fatal for
the current packet family.  If smoothing exposes decay, B2b becomes the active
route again.

## Proshka Audit Block

Claim:
A direct Montgomery--Vaughan / large-sieve estimate based only on log-prime
separation is unconditional but too crude for E5p.  Its constants grow like
`pi/min_gap`, numerically from `4.7e3` at K=2 to `1.9e6` at K=3.5, while the
actual finite projected epsilons are `O(1)`.

Point of blockage:
The generic theorem drops the corrected positive-definite cone and sees only
the smallest log spacing.  It does not see the structured cross-correlation
cancellation that makes the measured finite-op defect small.

What was tried:
- Local `q3_docs` search for ordinary-prime mean / large sieve / Hilbert
  routes.
- Primary-source check for Montgomery--Vaughan Hilbert inequality and CLV.
- Added `spacing` mode to `scripts/trackb_edge_operator_probe.py`.
- Ran K=2, 2.5, 3, 3.5 spacing diagnostics in D2 raw-log coordinates.

Minimal example:
At K=3.5, raw edge `[7,14]`, ordinary primes have

```text
min raw log gap ~= 1.663e-6,
pi/min_gap ~= 1.889e6,
ordinary weight fraction ~= 0.9981,
stable finite-op epsilon ~= 0.2386.
```

Question for Proshka:
What is the right structured ordinary-prime mean theorem for
boundary-null cross-correlation packets?  It must use smoothness/PSD/cone
structure beyond minimum separation, or we should switch the next experiment to
a prolate/energy-concentration packet basis.
