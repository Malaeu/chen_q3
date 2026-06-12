# Track B B2b: Packet-Scale Sweep for Finite-Op Decay

Status: B2 diagnostic.  This is not a proof certificate and does not close
E5'.  It tests whether the bad `FINITE-OP + CLV-tail` scale behavior in
`docs/trackB/b2b_finiteop_tail_probe.md` is caused by the fixed Step13 packet
choice `ell=0.35`.

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

The sweep stays in raw-log coordinates.  It changes only the packet width
`ell` and grid spacing used by the Step13 finite projected model.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finitesweep \
  --K 1 2 3 \
  --ell-values 0.25 0.35 0.5 0.75 1.0 \
  --grid-delta-values 0.5 \
  --p0-na 1001
```

The `finitesweep` mode reports the same finite projected certificate as
`finiteop` but without the prime-shift Rayleigh breakdown:

```text
lambda_min * G <= P_edge - P0_edge <= lambda_max * G.
```

It also reports:

```text
two_sided_epsilon = max(|lambda_min|, |lambda_max|),
epsilon_times_K,
epsilon_times_sqrt_K,
kerQ_dim,
eig_Gc_min,
eig_Gc_max,
G_condition.
```

`G_condition` is essential: a small `epsilon` in a nearly singular projected
metric is not a robust theorem route.

## Fixed Grid, Moderate Packet Widths

With `grid_delta=0.5`, `p0_na=1001`, `k_spline=5`:

```text
K=1:
  ell=0.25 -> epsilon ~= 0.281158, kerQ_dim=6
  ell=0.35 -> epsilon ~= 0.232991, kerQ_dim=6
  ell=0.50 -> epsilon ~= 0.188612, kerQ_dim=5
  ell=0.75 -> epsilon ~= 0.181593, kerQ_dim=4
  ell=1.00 -> epsilon ~= 0.064940, kerQ_dim=3

K=2:
  ell=0.25 -> epsilon ~= 0.633113, kerQ_dim=14
  ell=0.35 -> epsilon ~= 0.441668, kerQ_dim=14
  ell=0.50 -> epsilon ~= 0.170685, kerQ_dim=13
  ell=0.75 -> epsilon ~= 0.101434, kerQ_dim=12
  ell=1.00 -> epsilon ~= 0.105742, kerQ_dim=11

K=3:
  ell=0.25 -> epsilon ~= 0.736653, kerQ_dim=22
  ell=0.35 -> epsilon ~= 0.498483, kerQ_dim=22
  ell=0.50 -> epsilon ~= 0.145212, kerQ_dim=21
  ell=0.75 -> epsilon ~= 0.109653, kerQ_dim=20
  ell=1.00 -> epsilon ~= 0.110161, kerQ_dim=19
```

Interpretation:

- The fixed `ell=0.35` failure was partly a packet-scale artifact.
- Increasing `ell` from `0.35` to the `0.5..1.0` range dramatically lowers
  `epsilon` for K=2 and K=3.
- However the best non-degenerate values plateau near `0.10..0.11`, not at an
  evident `K^{-c}` decay.
- This still does not satisfy the B3 target `epsilon_K <= C*K^{-c}` in any
  meaningful scale-asymptotic sense.

## Very Wide Packets

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finitesweep \
  --K 1 2 3 \
  --ell-values 0.5 0.75 1.0 1.5 2.0 3.0 \
  --grid-delta-values 0.5 \
  --p0-na 1001
```

Very wide packets can force small `epsilon`, but they also collapse the live
dimension.

Examples:

```text
K=1, ell=1.5:
  epsilon ~= 0.021143
  kerQ_dim = 1

K=2, ell=3.0:
  epsilon ~= 0.021542
  kerQ_dim = 3

K=3, ell=5.5:
  epsilon ~= 0.009459
  kerQ_dim = 1
```

This is not an E5' route.  It is mostly a dimensional collapse of the projected
packet space.

## Grid Refinement Check

Command:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finitesweep \
  --K 2 3 \
  --ell-values 2.0 3.0 4.5 5.0 5.5 \
  --grid-delta-values 0.5 0.25 \
  --p0-na 1001
```

Refining the grid often destroys the apparent wide-packet gain because the
projected Gram metric becomes nearly singular and new modes enter.

Representative examples:

```text
K=2, ell=3.0:
  grid_delta=0.5  -> epsilon ~= 0.021542, kerQ_dim=3
  grid_delta=0.25 -> epsilon ~= 0.092936, kerQ_dim=7

K=3, ell=3.0:
  grid_delta=0.5  -> epsilon ~= 0.110132, kerQ_dim=11
  grid_delta=0.25 -> epsilon ~= 30.221617, kerQ_dim=23

K=3, ell=4.5:
  grid_delta=0.5  -> epsilon ~= 0.078960, kerQ_dim=5
  grid_delta=0.25 -> epsilon ~= 5.497681, kerQ_dim=11

K=3, ell=5.5:
  grid_delta=0.5  -> epsilon ~= 0.009459, kerQ_dim=1
  grid_delta=0.25 -> epsilon ~= 0.064818, kerQ_dim=3
```

The large refined-grid values also coincide with tiny `eig_Gc_min` values, so
the numerical certificate is probing modes that are nearly invisible in the
current projected `G` metric.

## Verdict

`PARTIAL(packet scale matters)`.

But this does not close E5':

```text
B2-GAP(normalized packet theorem or structured ordinary-prime mean estimate)
```

What this kills:

- The fixed `ell=0.35` data should not be used as a route-level impossibility
  proof.
- The very small wide-packet `epsilon` values should not be used as a proof
  route either; they are tied to low `kerQ_dim` and/or ill-conditioned `G`.

What remains:

1. Find a packet normalization/family with stable dimension and controlled
   `G_condition` where `epsilon_K` visibly decays.
2. Or keep the finite packet family fixed and prove a structured
   ordinary-prime mean estimate on the cross-correlation cone.

## Proshka Update

Claim:
Changing packet width can reduce the finite projected edge epsilon by a large
factor, but the only very small epsilons found so far come from dimension
collapse or ill-conditioned projected Gram modes.

Point of blockage:
We need a stable packet theorem.  A sweep over `ell` does not by itself give
the B3 target because the low epsilon regimes either have tiny `kerQ_dim` or
become unstable under grid refinement.

What was tried:
- Added `finitesweep` mode to `scripts/trackb_edge_operator_probe.py`.
- Swept K=1,2,3 over moderate `ell=0.25..1.0`.
- Swept very wide `ell` values up to near the support boundary.
- Repeated wide-packet checks with `grid_delta=0.25`.

Minimal example:
At K=2, `ell=0.75`, `grid_delta=0.5` gives a non-degenerate improvement
`epsilon≈0.101434` with `kerQ_dim=12`.  At K=2, `ell=3.0`,
`grid_delta=0.5` gives `epsilon≈0.021542`, but only `kerQ_dim=3`; refining to
`grid_delta=0.25` raises epsilon to `≈0.092936`.

Question for Proshka:
What is the correct normalized packet family for the E5' cone: fixed-width
packets, width proportional to K, or a two-scale family that separates
ordinary-prime mean control from boundary-null capture?
