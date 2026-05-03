# Step 19 -- Entry radii generator

## Goal

Generate entrywise radii for Step 18 `--mode radius`.

The target CSV format is:

```csv
matrix,i,j,rad
A,0,0,...
P,0,0,...
P0,0,0,...
Q,0,0,...
```

## Script

Added:

```text
scripts/q3_psdpd_step19_entry_radii.py
```

The script writes:

```text
docs/insights/q3_psdpd_step19_entry_radii.csv
```

for the primary `k_spline=11` candidate and can write alternative files via
`--out`.

## Radius Sources

| Matrix | Method | Proof-grade status |
|---|---|---|
| `P` | Arb ball finite prime-power evaluation | yes-candidate |
| `Q` | Arb ball exponential evaluation | yes-candidate |
| `P0` | quadrature drift radii | no, Step 20 target |
| `A` | quadrature drift radii | no, Step 21 target |

Dependency added:

```text
python-flint>=0.8.0
```

## Primary Candidate: `k_spline=11`

Parameters:

```text
L = 3.0
ell = 0.30
delta = 0.25
k_spline = 11
kappa = 3.25
theta = 1e-4
arb_prec = 512
```

Radius summary:

```text
max rad(A)  = 1.6431300764452317e-14  [drift]
max rad(P)  = 4.6880577983306349e-05  [Arb]
max rad(P0) = 1.2179468440010055e-05  [drift]
max rad(Q)  = 6.2725070069073189e-16  [Arb]
```

Step 18 radius-mode result:

```text
||rad(P)||_2      = 3.0710728558427041e-04
||rad(Dtheta)||_2 = 3.0713129925145362e-04

Dtheta safe_lower = -1.9201301543327764e-04
Rkappa safe_lower =  1.3543578189173180e-01
PASS              = False
```

Diagnosis:

The failure is not caused by the penalty method.  `R_kappa` still passes with
a large lower bound.  The blocker is the `P` radius.

The Arb finite-prime evaluation found a real discrepancy between the Arb
enclosure and the current float midpoint for the high-degree B-spline packet.
For example one maximal entry has

```text
index = (0, 9)
d     = -2.25
float P_ij midpoint = 0.3747039702295551
Arb P_ij value      = 0.3747508508075337...
radius around float = 4.688057798330635e-05
```

This points to numerical instability in the current power-basis
`centered_bspline` midpoint evaluation at degree `2*k_spline+1 = 23`.

Conclusion: the `k_spline=11` primary candidate is still mathematically
interesting, but it is not yet a proof-candidate in the current midpoint
format.  It needs either a stable B-spline midpoint builder or an upgraded
Step 18 contract that accepts certified midpoints as well as radii.

## Control Candidate: `k_spline=9`

Parameters:

```text
L = 3.0
ell = 0.30
delta = 0.25
k_spline = 9
kappa = 3.075
theta = 1e-5
arb_prec = 256
```

Radius CSV:

```text
docs/insights/q3_psdpd_step19_entry_radii_k9.csv
```

Radius summary:

```text
max rad(A)  = 1.8651746813702630e-14  [drift]
max rad(P)  = 6.0571326983620018e-07  [Arb]
max rad(P0) = 1.4818841709285380e-07  [drift]
max rad(Q)  = 6.2725070069073189e-16  [Arb]
```

Step 18 radius-mode result:

```text
||rad(P)||_2      = 2.7317882461153673e-06
||rad(Dtheta)||_2 = 2.7318079643689895e-06

Dtheta safe_lower = 1.0342884010260479e-05
Rkappa safe_lower = 1.9569368329134390e-03
PASS              = True
```

This gives the first live radius-mode pipeline:

```text
Step 19 radii -> Step 18 --mode radius -> PASS
```

with `P,Q` generated from Arb balls and `A,P0` still using drift radii.

## Verdict

Step 19 successfully built the entry-radius pipeline and exposed the next
real hardening target.

The immediate proof-candidate should temporarily fall back to
`k_spline=9`, because it passes the current radius contract.  The higher
margin `k_spline=11` branch should not be discarded, but it needs a stable
B-spline midpoint repair before interval certification can use its larger
margin safely.

## Next Move

Step 20 should target `P0` and midpoint stability:

1. Replace high-degree power-basis B-spline float evaluation with a stable
   piecewise/de Boor midpoint builder, or teach Step 18 to load certified
   midpoints from CSV.
2. Build proof-grade `P0` radii from compact-support
   B-spline/exponential-polynomial integrals.
3. Re-run the `k_spline=11` branch after midpoint stabilization.
