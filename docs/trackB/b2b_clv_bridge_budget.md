# Track B B2b/B3: CLV Receiver Bridge Budget

Status: B2/B3 diagnostic.  This is not a proof certificate and does not close
E5'.  It takes the bridge gap from
`docs/trackB/b2b_clv_receiver_probe.md` and turns it into an explicit budget:

```text
P(edge) <= P(M^+) + R_K(delta) * G
```

where

```text
R_K(delta) = max(0, -lambda_min_G(P(M^+) - P(edge))).
```

Then the naive scalar-majorant route has the total upper budget

```text
epsilon_total(K,delta)
  = R_K(delta) + || P(M^+) - P0(M^+) ||_G.
```

This is only a diagnostic.  It is not a theorem certificate.

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

The Selberg receiver is applied in raw `a` coordinates.  No Q3 evenization
factor is inserted into the Step13 raw prime weights.

## Allowed Inputs

- `UNCONDITIONAL`: Selberg--Vaaler interval majorant/minorant and exact
  `L1` error `1/delta`; see `docs/trackB/clv_pair.md`.
- `UNCONDITIONAL`: CLV Gaussian subordination / Beurling--Selberg framework.
  Source: https://arxiv.org/abs/1008.4969
- `UNCONDITIONAL / finite-dimensional linear algebra`: fixed projected packet
  eigenvalue diagnostics on `kerQ`.

Not used:

- RH/GRH.
- FQ-transfer.
- de Branges positivity.
- RH-conditional prime-gap conclusions.

## Local And External Search Synthesis

Local `q3_docs` search for

```text
Selberg CLV receiver bridge P(M+) P(edge) corrected cross-correlation cone
Fejer heat smoothing prime bridge operator cone receiver majorant
Carleson prime sampling cross-correlation cone Selberg majorant
```

returned Fejer/heat smoothing, RKHS/Carleson prime-sampling, corrected-cone
packaging, and earlier warnings that broad packet-Rayleigh families are too
large.  It did not return an existing theorem that supplies the structured
bridge

```text
P(edge) <= P(M^+) + R_K * G
```

with a B3-sized `R_K`.

External search re-confirmed the standard role of Beurling--Selberg/Selberg
majorants in large-sieve and bandlimited approximation arguments, but did not
identify a ready Loewner-order bridge for shifted packet matrices on our
corrected cross-correlation cone.  Those external facts are context only; no
new theorem input is used below.

## Probe Mode

Implementation:

```bash
.venv/bin/python scripts/trackb_edge_operator_probe.py clvrecv \
  --K 2 --ell 0.75 --grid-delta 0.5 \
  --receiver-delta 0.25 0.5 1 2 4 8 \
  --p0-na 801 --receiver-grid-nt 4001
```

The `clvrecv` mode now reports:

```text
bridge_R_plus
total_upper_budget_plus
```

where

```text
bridge_R_plus = max(0, -min eig_G(P(M+) - P(edge))),
total_upper_budget_plus = bridge_R_plus
  + ||P(M+) - P0(M+)||_G.
```

For K=3 and K=3.5, two extra large bandwidths were checked:

```text
delta in {16, 32}.
```

This tests the expected tradeoff:

- small/medium `delta`: strong CLV smoothing but huge bridge penalty;
- large `delta`: bridge penalty decreases, but the receiver approaches the
  hard edge and loses the smoothing advantage.

## Budget Table

Stable packet choices are the same as in
`docs/trackB/b2b_stability_schedule.md`.

### K=2, ell=0.75

```text
delta    smooth eps      bridge R+      total+
0.25     0.007980        4.126656       4.134636
0.50     0.005169        3.521058       3.526227
1.00     0.010258        2.353872       2.364129
2.00     0.088261        1.508693       1.596954
4.00     0.091185        0.827445       0.918630
8.00     0.100796        0.433800       0.534596
```

Hard-edge finite-op epsilon:

```text
0.101433
```

### K=2.5, ell=1.375

```text
delta    smooth eps      bridge R+      total+
0.25     0.024249        6.131640       6.155889
0.50     0.010285        5.001630       5.011915
1.00     0.001971        3.477253       3.479224
2.00     0.059549        2.020250       2.079799
4.00     0.048107        0.999850       1.047956
8.00     0.040426        0.326727       0.367154
```

Hard-edge finite-op epsilon:

```text
0.419379
```

### K=3, ell=0.75

```text
delta    smooth eps      bridge R+      total+
0.25     0.037810        13.856801      13.894611
0.50     0.006608        10.990057      10.996665
1.00     0.009512        7.531144       7.540656
2.00     0.091917        4.389146       4.481063
4.00     0.073125        2.496786       2.569910
8.00     0.046448        1.267392       1.313840
16.00    0.065803        0.658733       0.724536
32.00    0.042257        0.378201       0.420458
```

Hard-edge finite-op epsilon:

```text
0.109636
```

### K=3.5, ell=1.375

```text
delta    smooth eps      bridge R+      total+
0.25     0.026222        20.376024      20.402246
0.50     0.005161        18.655882      18.661042
1.00     0.001014        12.516487      12.517501
2.00     0.065048        7.334671       7.399719
4.00     0.079950        4.023837       4.103786
8.00     0.175523        2.055958       2.231481
16.00    0.207706        1.047550       1.255256
32.00    0.133079        0.617899       0.750978
```

Hard-edge finite-op epsilon:

```text
0.238486
```

## Best-Tested Scalar-Bridge Budget

Over the tested bandwidths:

```text
K=2.0:  best total+ ~= 0.534596 at delta=8
K=2.5:  best total+ ~= 0.367154 at delta=8
K=3.0:  best total+ ~= 0.420458 at delta=32
K=3.5:  best total+ ~= 0.750978 at delta=32
```

The log-log fit to these best-tested totals gives

```text
epsilon_total(K) ~= C*K^(-c),
C ~= 0.29767,
c ~= -0.52163.
```

The fitted decay exponent is negative.  This is not B3 evidence.

## Interpretation

The scalar-majorant route has a hard tradeoff:

```text
small delta:
  ||P(M+) - P0(M+)||_G is tiny,
  but R_K(delta) is huge.

large delta:
  R_K(delta) decreases,
  but the receiver loses the CLV smoothing advantage and drifts back toward
  the hard-edge finite-op problem.
```

Thus the bridge penalty eats the CLV win.  The naive theorem shape

```text
scalar Selberg majorant + bridge penalty R_K*G
```

does not produce the required `epsilon_K <= C*K^{-c}` on the current stable
packet family.

This does **not** kill Track B.  It kills only the scalar-majorant bridge
subroute.  The genuinely promising signal remains the small smoothed receiver
residual, which suggests that B2b must use the receiver as the primary
explicit-formula object rather than as a post-hoc majorant of the hard edge.

## Verdict

`FATAL(naive scalar Selberg hard-edge bridge, current packet family)`.

Track B remains active with the sharper target:

```text
Hermitian-square / explicit-formula route where M+ is primary
```

or a non-scalar structured correction that cancels the negative bridge modes
without paying `R_K`.

## Proshka Audit Block

Claim:
The naive scalar-majorant bridge

```text
P(edge) <= P(M+) + R_K(delta)*G
```

does not close E5' on the current stable packet family.  The best-tested
budgets over `delta` do not show B3 decay.

Point of blockage:
The bandwidth that makes the smoothed receiver residual tiny also makes
`R_K(delta)` huge.  Increasing `delta` reduces the bridge penalty only by
returning toward the hard-edge problem.

What was tried:
- Added `bridge_R_plus` and `total_upper_budget_plus` to `clvrecv`.
- Ran K=2,2.5,3,3.5 on stable packet choices from
  `b2b_stability_schedule.md`.
- Tested `delta in {0.25,0.5,1,2,4,8}`, plus `16,32` for K=3 and K=3.5.
- Ran local `q3_docs` search for existing Fejer/Carleson/receiver bridge
  theorem shapes.
- Ran a short external source search around Beurling--Selberg / large-sieve
  bridge machinery.

Minimal example:
At K=3.5, `ell=1.375`:

```text
delta=1:
  smooth eps ~= 0.001014
  R_K ~= 12.516487
  total ~= 12.517501

delta=32:
  smooth eps ~= 0.133079
  R_K ~= 0.617899
  total ~= 0.750978

hard-edge finite-op epsilon ~= 0.238486
```

Question for Proshka:
Can the B2b explicit-formula route be formulated so that the Selberg receiver
is the primary Hermitian-square test object, avoiding any separate
`P(edge) <= P(M+) + R_K*G` bridge?  If not, what structured correction can
cancel the negative bridge modes without paying the scalar `R_K` budget?
