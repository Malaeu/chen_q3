# Q3 PSD-pd Step 16 Refine Candidate (2026-05-03)

Status: in progress / numerical reconnaissance

Placement:

- This continues the fallback `PSD-pd` finite certificate route.
- It does not claim RH.
- It refines the strongest Step 15 candidate and uses that candidate, not the
  first sweep case, as the profile-correlation baseline.

Script:

```text
scripts/q3_psdpd_step16_refine_candidate.py
```

Output:

```text
docs/insights/q3_psdpd_step16_refine.csv
docs/insights/q3_psdpd_step16_kappa_curve.csv
```

## Baseline from Step 15

Step 15 best candidate:

```text
k_spline=9
ell=0.30
delta=0.25
kappa=3.25
margin≈3.022638e-05
```

Step 16 reran this candidate on a finer `kappa` grid:

```text
kappa grid=2.50:0.025:4.25
arch_tmax=260
arch_nt=48001
p0_na=24001
```

Refined baseline result:

```text
lambda_min(Cc,Gc)     = 1.964779e-05
kappa_viable_min_grid = 3.075
viable_margin         = 3.0305236805e-05
profile_corr_to_best  = 1.0
```

The minimum viable grid value is therefore lower than the coarse Step 15
`kappa=3.25` signal.

## Kappa plateau

The baseline kappa curve was exported to:

```text
docs/insights/q3_psdpd_step16_kappa_curve.csv
```

On the tested interval, the certificate first becomes viable at:

```text
kappa=3.075
min_R_eucl=1.9590157794e-03
rel_max=9.9996969476e-01
margin=3.0305236805e-05
```

It stays viable through the end of the scan:

```text
kappa=4.25
min_R_eucl=1.2979982159e-01
rel_max=9.9997021699e-01
margin=2.9783005960e-05
```

Near the threshold:

| kappa | min_R_eucl | margin | pass |
| ---: | ---: | ---: | :--- |
| 3.000 | `-8.7402857074e-03` | none | false |
| 3.025 | `-5.1521174384e-03` | none | false |
| 3.050 | `-1.5854807700e-03` | none | false |
| 3.075 | ` 1.9590157794e-03` | `3.0305236805e-05` | true |
| 3.100 | ` 5.4807390507e-03` | `3.0293947679e-05` | true |
| 3.125 | ` 8.9790335782e-03` | `3.0282666405e-05` | true |
| 3.150 | ` 1.2453224262e-02` | `3.0271392976e-05` | true |
| 3.175 | ` 1.5902619405e-02` | `3.0260127384e-05` | true |

Interpretation:

```math
\boxed{
\text{This is a genuine kappa plateau on the tested grid, not a single point.}
}
```

## Quadrature stability

Quadrature checks for the same baseline:

| arch_tmax | arch_nt | p0_na | kappa_viable | margin | corr_to_best |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 220 | 36001 | 18001 | 3.075 | `3.0305235393e-05` | 1.0 |
| 260 | 48001 | 24001 | 3.075 | `3.0305236805e-05` | 1.0 |
| 320 | 64001 | 32001 | 3.075 | `3.0305237528e-05` | 1.0 |

The margin changes only in the seventh decimal place of the margin value.  This
is strong evidence that the Step 16 baseline is not a quadrature artifact at
this precision.

## Basis-neighborhood stability

The broad local sweep produced two visible branches.

### Same-profile branch

High correlation against the best baseline:

| k_spline | ell | delta | best_margin | corr_to_best |
| ---: | ---: | ---: | ---: | ---: |
| 7 | 0.30 | 0.25 | `5.4329699795e-07` | `0.9956827335` |
| 11 | 0.30 | 0.25 | `2.7266610939e-04` | `0.9948700348` |
| 7 | 0.28 | 0.25 | `5.5042354569e-06` | `0.9654868307` |
| 9 | 0.28 | 0.25 | `1.4626027957e-04` | `0.9624291641` |
| 11 | 0.28 | 0.25 | `1.0698540623e-03` | `0.9525925998` |
| 9 | 0.26 | 0.25 | `6.3298988499e-04` | `0.8493549516` |

This is the important stability signal: around `delta=0.25`, the worst profile
is stable under changes of spline degree and nearby `ell`.

### Different-profile/high-margin branch

Largest margins in the broad sweep:

| k_spline | ell | delta | best_margin | corr_to_best |
| ---: | ---: | ---: | ---: | ---: |
| 11 | 0.26 | 0.30 | `9.8876989678e-03` | `0.0243290235` |
| 11 | 0.28 | 0.30 | `5.7057794212e-03` | `0.0226547557` |
| 9 | 0.26 | 0.30 | `4.5103995317e-03` | `0.0264216867` |
| 11 | 0.30 | 0.30 | `3.0496885805e-03` | `0.0169499680` |

These are numerically attractive but profile-incompatible with the Step 15
baseline.  They may be a different finite-grid branch rather than the same
near-kernel.  They should not be mixed into the proof-grade path without a
separate profile autopsy.

## Interpretation

Step 16 answers the main questions:

- `kappa` plateau: yes, at least from `3.075` through `4.25` in this scan.
- Quadrature stability: yes, margin is stable across the tested Arch/P0 grids.
- Basis-neighborhood stability: yes on the same-profile branch near
  `delta=0.25`.
- Worst-profile stability: yes for neighboring spline degrees and nearby
  `ell` at `delta=0.25`; no for the high-margin `delta=0.30` branch, which
  appears to represent a different mode.

## Verdict

The best proof-grade candidate is now:

```text
k_spline=9
ell=0.30
delta=0.25
kappa=3.075
margin≈3.0305e-05
```

The strongest nearby same-profile alternative is:

```text
k_spline=11
ell=0.30
delta=0.25
margin≈2.7267e-04
profile_corr≈0.99487
```

Recommended next target:

```math
\boxed{
\text{Step 17: proof-grade interval certificate on the same-profile branch.}
}
```

Start with the `k_spline=9, ell=0.30, delta=0.25` baseline because the profile
chain is now understood; keep the `k_spline=11, ell=0.30, delta=0.25` case as
the higher-margin backup after a dedicated autopsy.
