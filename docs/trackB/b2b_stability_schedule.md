# Track B B2b/B3: Stability-Filtered Packet Schedule

Status: B2/B3 diagnostic.  This is not a proof certificate and does not close
E5'.  It converts the packet-scale sweep into a stability-filtered schedule:
for each K, choose the best finite projected edge epsilon only among packet
models whose projected Gram metric and boundary-null dimension are not
obviously degenerate.

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

No extra evenization factor is inserted into the raw Step13 prime weights.

## Allowed Inputs

- `UNCONDITIONAL / finite-dimensional linear algebra`: for every fixed packet
  model, the generalized eigenvalue computation certifies the finite projected
  inequality

  ```text
  lambda_min * G <= P_edge - P0_edge <= lambda_max * G.
  ```

- `UNCONDITIONAL`: CLV/Selberg tools from `docs/trackB/clv_pair.md` remain
  allowed for tail/continuum transfer only.  They are not used here to claim
  operator dominance.

Forbidden inputs remain unchanged: no RH/GRH, no FQ-transfer, no de Branges
positivity, and no RH-conditional prime-gap theorem as a theorem input.

## Local And External Search Synthesis

Local `q3_docs` search for normalized packet families pointed back to the
corrected positive-definite packet family:

```text
mathcal G_K^pd = cone{ Psi * tilde(Psi) : Psi in centered packet family }.
```

It also recalled an important negative: a uniform packet-symbol floor on the
whole dense packet dictionary is already rejected as too strong.  Therefore the
schedule must filter out low-dimensional or ill-conditioned packet artifacts.

External primary-source scan added no theorem input.  It only suggested two
possible next trick families:

- Montgomery--Vaughan Hilbert/mean-value technology for ordinary-prime mean
  estimates.
- Slepian--Pollak prolate concentration for a better normalized packet basis.

Neither is used below as a proof theorem.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finiteschedule \
  --K 2 2.5 3 3.5 \
  --ell-values 0.5 0.75 1.0 1.25 1.5 \
  --grid-delta-values 0.5 \
  --min-ker-dim 8 \
  --max-g-condition 20 \
  --min-g-eig 1e-4 \
  --p0-na 801
```

Filters:

```text
kerQ_dim >= 8,
G_condition <= 20,
eig_Gc_min >= 1e-4.
```

The selected schedule was:

```text
K=2.0:
  ell=0.75, epsilon=0.1014334152, kerQ_dim=12, G_condition=1.71

K=2.5:
  ell=1.25, epsilon=0.4228513828, kerQ_dim=14, G_condition=16.39

K=3.0:
  ell=0.75, epsilon=0.1096361089, kerQ_dim=20, G_condition=1.76

K=3.5:
  ell=1.25, epsilon=0.2407138913, kerQ_dim=22, G_condition=17.99
```

The log-log power fit over these selected points gives

```text
epsilon_K ~= C * K^(-c),
C ~= 0.08777,
c ~= -0.74438.
```

The fitted exponent is negative, so the stability-filtered schedule is not
evidence for B3 decay.  The selected epsilons are not monotone and do not
support `epsilon_K <= C*K^{-c}` with `c>0`.

## Dense Ell Check For Bad K

To test whether K=2.5 and K=3.5 were artifacts of a coarse `ell` grid, run:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py finiteschedule \
  --K 2.5 \
  --ell-values 0.5 0.625 0.75 0.875 1.0 1.125 1.25 1.375 1.5 1.75 2.0 \
  --grid-delta-values 0.5 \
  --min-ker-dim 8 --max-g-condition 50 --min-g-eig 1e-5 \
  --p0-na 801
```

and similarly for K=3.5.

Results:

```text
K=2.5:
  best stable candidate ell=1.375,
  epsilon=0.4193789770,
  kerQ_dim=13,
  G_condition=34.03.

K=3.5:
  best stable candidate ell=1.375,
  epsilon=0.2384863145,
  kerQ_dim=21,
  G_condition=39.71.
```

Increasing the continuum quadrature from `p0_na=801` to `1601` gives

```text
K=2.5, ell=1.375:
  epsilon=0.4193616007

K=3.5, ell=1.375:
  epsilon=0.2386078674
```

So the bad points are stable under this quadrature refinement.

## Verdict

`GAP(stability-filtered finite-op schedule does not give B3 decay)`.

This is not fatal for Track B, because it tests only one packet architecture.
But it kills the current hope:

```text
choose ell(K) inside the Step13 B-spline packet model
  -> get epsilon_K <= C*K^{-c}
```

under basic stability filters.

## Proshka Update

Claim:
The best stability-filtered packet schedule in the current Step13 B-spline
family does not show the required B3 decay.  Dense `ell` checks at K=2.5 and
K=3.5 preserve the obstruction.

Point of blockage:
The finite projected epsilon is not controlled by a simple packet-width
schedule.  Some K values have distributed ordinary-prime resonance that remains
large under stable packet choices.

What was tried:
- Added `finiteschedule` mode to `scripts/trackb_edge_operator_probe.py`.
- Filtered by `kerQ_dim`, `G_condition`, and `eig_Gc_min`.
- Swept K=2, 2.5, 3, 3.5 over moderate packet widths.
- Rechecked K=2.5 and K=3.5 on a denser `ell` grid.
- Verified the selected bad points with a finer `p0_na=1601` continuum
  quadrature.

Minimal example:
K=2.5, raw edge `[5,10]`, `ell=1.375`, `grid_delta=0.5`, `k_spline=5`:

```text
epsilon ~= 0.41936,
kerQ_dim = 13,
G_condition ~= 34.03.
```

This is stable under `p0_na=801 -> 1601`.

Question for Proshka:
Should the next trick be an ordinary-prime mean-value theorem for the
structured cross-correlation cone, or should we replace the Step13 B-spline
packet family by a prolate/energy-concentration basis before trying finite-op
decay again?
