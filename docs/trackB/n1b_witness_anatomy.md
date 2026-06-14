# Track B N1b: Witness Anatomy

Status: ZERO_CONSISTENT(first crossing only) / superseded by v5 addendum.
This is not a proof of E5p, not a Lean proof, and not a route mutation.

Update: Track B v5 addendum found a second pathology at the sampled minimum
`a=7.28`.  The active witness card is now
`docs/trackB/WITNESS_cell62.md`; do not use this older first-crossing card as
permission to start S2.

## Target

The first sampled-negative point from N1 centered-form audit is

```text
K = 3.5
ell = 1.375
receiver_delta = 1
witness a = 7.130987044271352
edge = [2K,4K] = [7,14]
```

It lives in cell `62`, global mesh `18725`.  The goal of N1b is to document
what this witness is before any N2 smoothing can hide it.

## Inputs

- `UNCONDITIONAL`: finite-dimensional matrix/eigenvector diagnostics on the
  fixed Step13 packet model.
- `UNCONDITIONAL`: existing Selberg/Vaaler receiver formulas already recorded
  in `docs/trackB/clv_pair.md`.
- No RH/GRH, no Fourier-quasicrystal transfer, no de Branges positivity.
- Precision: ordinary `float64`; no `dps > 15`.

## Command

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvwitness \
  --K 3.5 --ell 1.375 --schedule fixed --grid-delta 0.5 --k-spline 5 \
  --receiver-delta 1 --p0-na 401 \
  --witness-a 7.130987044271352 \
  --scan-left 0.2 --scan-right 0.4 --scan-step 0.01 \
  --fine-radius 0.02 --fine-step 0.0005 --top 12
```

## D2

Raw coordinate:

```text
a = r log p
xi = a / (2*pi)
```

The local density inspected by `clvsigncert` is

```text
S(a) = exp(-a/2) * (H'(a) - H(a)/2)
H(a) = (M^+_[2K,4K],delta(a) - 1_[2K,4K](a)) * F_v(a).
```

The four named slots below are therefore diagnostic labels for this local
Stieltjes product-rule density.  The zero-side PSD term is global; it is not a
pointwise scalar in this local witness formula.

## Point Anatomy

At `a = 7.130987044271352`:

```text
S(a)                                 ~= -5.66307e-8
arch_proxy_smooth_receiver(a)        ~= -1.15274e-1
-zero_PSD pointwise slot             =   0
prime_edge_hard_indicator_slot(a)    ~= +1.15274e-1
boundary_jump_slot(a)                =   0
reconstruction error                 ~=  6.94e-18
```

So the point is not a deep negative well.  It is a near-perfect cancellation
between a negative smooth-receiver part and a positive hard-edge indicator
part, leaving a tiny negative residual.

Equivalently, the product-rule pieces are

```text
exp(-a/2) M+'(a) F_v(a)              ~= +1.17104e-2
exp(-a/2) (M^+(a)-1_I(a))*(F'_v-F_v/2)
                                      ~= -1.17104e-2
sum                                  ~= -5.66307e-8
```

## Localization Scan

Coarse sampled scan on `a in [2K-0.2, 2K+0.4] = [6.8,7.4]`, step `0.01`:

```text
finite samples             = 60
negative samples           = 27
negative sampled zone      ~= [7.14, 7.40]
coarse minimum             ~= -2.12171e-2 at a ~= 7.28
```

Local fine scan around the first witness, step `0.0005`:

```text
negative sampled zone      ~= [7.1309870443, 7.1509870443]
minimum in this fine window ~= -5.01028e-3 at a ~= 7.1509870443
```

The witness point itself is just the first crossing.  The deeper sampled
negative region is to its right.

Nearest prime-power logs to the witness are ordinary primes:

```text
log(1249) ~= 7.1300985101   distance ~= -8.88534e-4
log(1259) ~= 7.1380730340   distance ~= +7.08599e-3
log(1237) ~= 7.1204443724   distance ~= -1.05427e-2
```

Inside `[a-delta,a+delta]`, there are `408` prime-power shifts, of which
`390` are ordinary primes.  The top local prime-correction contributions are
ordinary primes just below the left edge:

```text
p=1093, log p ~= 6.9966814882, contribution ~= 0.210270
p=1091, log p ~= 6.9948499858, contribution ~= 0.209873
p=1087, log p ~= 6.9911768871, contribution ~= 0.209001
```

So the local prime geometry is an ordinary-prime shoulder at the edge, not a
`p=2` phenomenon and not a sparse prime-power exception.

## Controls

All controls reselect the same `clvsigncert` opnorm direction under the stated
prime-shift variant, then evaluate the same local density at the witness.

```text
full prime powers                         S(a_w) ~= -5.66307e-8
ordinary primes only (r=1)                S(a_w) ~= +4.62498e-3
p=2 only                                  S(a_w) ~= +1.13052e-2
exclude log n > a_w - 0.5                 S(a_w) ~= +1.24228e-2
exclude log n in [a_w-delta,a_w+delta]    S(a_w) ~= +1.14187e-2
```

The first witness disappears when the local/right edge prime shifts are
removed.  Some altered directions still develop negative zones farther right
in the coarse scan, so this is not a global no-negative theorem.

## Verdict

`ZERO_CONSISTENT(a_local_first_crossing_edge_primes_confirmed)`.

The registered Fable is confirmed in the local first-crossing sense: the
sampled-negative witness depends on the edge-prime configuration.  The more
precise anatomy is:

```text
enemy = edge ordinary-prime shoulder selecting a near-cancellation direction,
not = p=2-only,
not = a standalone boundary-jump defect,
not = direct zero-side PSD failure.
```

N2 smoothing is now allowed as a diagnostic next step for cell `61`, but the
N1b witness must remain attached to any N2 report so smoothing does not erase
the worst-case portrait.
