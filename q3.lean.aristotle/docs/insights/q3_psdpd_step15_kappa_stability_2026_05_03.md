# Q3 PSD-pd Step 15 Kappa Stability (2026-05-03)

Status: in progress / numerical reconnaissance

Placement:

- This continues the fallback `PSD-pd` finite certificate route.
- It does not claim RH.
- It measures whether the Step 14 `kappa` split is an isolated numerical
  accident or a stable finite-level certificate signal.

Script:

```text
scripts/q3_psdpd_step15_kappa_stability.py
```

## Goal

For the same reduced Weil matrix

```math
C^\circ=N^\ast(A-P)N,
```

scan the split

```math
C=(A-\kappa P_0)-(P-\kappa P_0)
```

and record:

- the smallest grid `kappa` for which `R_kappa=A-kappa P0` is positive on the
  boundary-null finite space;
- the smallest viable `kappa` for which
  `lambda_max(S_kappa^circ,R_kappa^circ)<=1`;
- the margin
  `1-lambda_max(S_kappa^circ,R_kappa^circ)`;
- the worst-profile correlation against the first case in the run.

## Baseline parameters

```text
L=3.0
ell=0.35
delta=0.25
k_spline=5
arch_tmax=260
arch_nt=48001
p0_na=24001
kappa grid=1.0:0.25:14.0
```

Baseline CSV:

```text
docs/insights/q3_psdpd_step15_baseline.csv
```

Baseline results:

```text
lambda_min(Cc,Gc)       = 1.0106683705041208e-08
lambda_min(-P0c,Gc)     = 6.4214377234407894e-03
kappa_pd_min_grid       = 6.5
kappa_viable_min_grid   = 6.5
viable_rel_max          = 9.9999998083995689e-01
viable_margin           = 1.9160043107646629e-08
best_margin_kappa       = 6.5
best_margin             = 1.9160043107646629e-08
```

This sharpens Step 14: the first viable grid value is not `kappa=8`; on the
finer `0.25` grid it is already `kappa=6.5`.

## Sweep parameters

```text
L=3.0
ells=0.30,0.35,0.40,0.45,0.60
deltas=0.25
k_splines=3,5,7,9
arch_tmax=260
arch_nt=48001
p0_na=24001
kappa grid=1.0:0.25:16.0
```

Sweep CSV:

```text
docs/insights/q3_psdpd_step15_sweep.csv
```

## Sweep summary

Best viable margins:

| case | k_spline | ell | lambda_min(Cc,Gc) | kappa_viable | margin | profile_corr_abs |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 16 | 9 | 0.30 | `1.9647793435e-05` | 3.25 | `3.0226377556e-05` | `1.1362114965e-01` |
| 2 | 3 | 0.35 | `9.7412025814e-07` | 7.25 | `1.8437608165e-06` | `1.7489646727e-02` |
| 18 | 9 | 0.40 | `2.7293575480e-07` | 5.75 | `1.1317942177e-06` | `3.4958420256e-02` |
| 1 | 3 | 0.30 | `6.1015002643e-07` | 6.75 | `8.3698909947e-07` | baseline |
| 11 | 7 | 0.30 | `3.3993676785e-07` | 4.25 | `5.4267309235e-07` | `1.1443885887e-01` |
| 17 | 9 | 0.35 | `1.0855948206e-07` | 4.75 | `1.9670343332e-07` | `8.1364096927e-02` |

Lowest viable `kappa` values:

| case | k_spline | ell | kappa_viable | margin |
| ---: | ---: | ---: | ---: | ---: |
| 16 | 9 | 0.30 | 3.25 | `3.0226377556e-05` |
| 11 | 7 | 0.30 | 4.25 | `5.4267309235e-07` |
| 17 | 9 | 0.35 | 4.75 | `1.9670343332e-07` |
| 6 | 5 | 0.30 | 5.50 | `3.0425192810e-08` |
| 18 | 9 | 0.40 | 5.75 | `1.1317942177e-06` |
| 7 | 5 | 0.35 | 6.50 | `1.9160043108e-08` |

Failure cases on this sweep grid:

| case | k_spline | ell | lambda_min(Cc,Gc) | best_margin |
| ---: | ---: | ---: | ---: | ---: |
| 12 | 7 | 0.35 | `-4.7601841904e-09` | `-6.9104069134e-09` |
| 14 | 7 | 0.45 | `-6.3519896000e-09` | `-1.0251795413e-08` |
| 15 | 7 | 0.60 | `-3.2709246518e-08` | `-4.1899607783e-08` |
| 19 | 9 | 0.45 | `-8.2932562218e-07` | `-1.0136500304e-06` |
| 20 | 9 | 0.60 | `-4.0199860201e-06` | `-5.0982927424e-06` |

## Interpretation

The `kappa` split is not a one-point artifact:

- the baseline `k_spline=5, ell=0.35` finite level is viable at `kappa=6.5`;
- several nearby families have viable certificates;
- the best observed margin is much stronger:
  `k_spline=9, ell=0.30` gives margin about `3.0e-5`;
- smaller `ell=0.30` is consistently better in this sweep;
- wider bumps (`ell=0.45`, `ell=0.60`) often degrade or fail for smoother
  splines.

The margin is no longer uniformly knife-edge.  Step 14's baseline margin was
only around `1.9e-8`, but the `k_spline=9, ell=0.30` case produces a gap three
orders of magnitude larger.

The profile-correlation diagnostic is not yet decisive.  Correlations were
measured against the first sweep case (`k_spline=3, ell=0.30`), not against a
matched or aligned profile.  The low correlations across wide parameter
changes therefore show that the naive comparison is too crude; they do not yet
prove that the near-kernel is non-structural.

## Verdict

Step 15 upgrades the signal:

```math
\boxed{
\kappa\text{-viability has a real parameter region, not a single lucky point.}
}
```

The strongest current reconnaissance target is:

```text
k_spline=9, ell=0.30, delta=0.25, kappa=3.25
```

with:

```text
lambda_min(Cc,Gc) = 1.9647793435e-05
margin            = 3.0226377556e-05
```

This is the first genuinely healthy finite-level margin in the PSD-pd pilot.

## Next target

Step 16 should focus rather than broaden:

- refine around `k_spline=9`, `ell=0.25..0.35`, `delta=0.20..0.25`;
- replace one-baseline profile correlation by aligned/profile-family
  correlation;
- export worst vectors/profiles for the strongest viable cases;
- test quadrature stability on the best margin case;
- if the margin survives, start interval-certified Cholesky or certified
  generalized-eigenvalue bounds for that finite level.
