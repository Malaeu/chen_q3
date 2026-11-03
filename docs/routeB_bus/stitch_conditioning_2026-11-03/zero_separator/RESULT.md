# Zero threshold and adaptive separators — literal even CCM

DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH. Base `435b7bb94c776851a7133757ba9bf59a2fbc0343`. All integer m=16..120, N=m, L=log m, dimension m+1. These are finite point calculations, not interval/source-sign certificates.

**At threshold zero**, the guarded resolved negative counts are:

| world | m | resolved negative count |
|---|---|---:|
| ζ | 16..120 | 0 |
| plant | 16..120 | 1 |
| DH | 16..50 | 0 |
| DH | 51..76 | 1 |
| DH | 77..120 | 2 |

This table does not assert exact source inertia where signs reach the arithmetic floor. `counts.csv` gives, for every m/world, literal signs of printed MP eigenvalues, guarded lower/upper counts, unresolved signs, precision heuristic and source SHA. ζ has unresolved near-zero signs in81 cells, plant in75, DH in28; printed negative counts can therefore differ from the resolved counts above. For example ζ120's printed minimum −5.73e−122 is unresolved, not a negative-direction finding. DH51 and53's negative point values are extremely small (≈−1.33e−47 and−1.18e−41); their roundoff-resolved signs do not pay quadrature/input uncertainty. See COUNT_REVIEW.md.

**Adaptive separation**, with r=dim J and λ_r the zero-based sorted full-A eigenvalue, was tested in all21153 nontrivial cutoff sectors (0<r<m+1):

| world | any κ>0 | κ≥1 |
|---|---|---|
| ζ | YES in105/105 cells | YES in105/105 cells |
| plant | YES in43/105 cells | NO_NUMERIC in105/105 cells |
| DH | YES in105/105 cells | YES at16..52 and54; NO at55..120;53 unresolved in baseline |

DH53's three float-floor sectors fail in a separate same-recipe MP120/GL128 and MP160/GL160 replay: δ≈1.24645e−11,4.04358e−14,7.44375e−17 versus λ_r≈1.01611e−23,5.26894e−29,4.45458e−35. They support **NO_REPLAY_SUPPORTED**. The original MP cache is unavailable at its pinned path, so reconstructed-recipe consistency is not presented as byte identity with that cache; baseline uncertainty remains visible.

The unrestricted κ>0 test is weak: low cutoffs can pass even in both indefinite controls. Restricting κ≥1 is an additional discriminator, not an implicit change to the question. A separator also coexists with negative DH directions at51,52,54: it does not imply positivity. Full all-m margins, representative κ and exact open-left/closed-right sector endpoints are in `separator_summary.csv`. The full scan is losslessly split/gzipped, with reconstruction instructions in METHOD.md. `degenerate_sectors.csv` separates q=0 (λ_r undefined) and J=0 (vacuous finite-positivity test); neither is counted as a nontrivial separator.

| ζ m | best κ≥1 sector | r | δ | λ_r | λ_r−δ |
|---:|---|---:|---:|---:|---:|
|24|(1.011715,1.048990]|16|.59169003|2.27276429|1.68107426|
|80|(.996617,1.013237] intersect κ≥1|45|.95850338|1.73150113|.77299776|
|120|(1.000683,1.008635]|64|.98397171|2.13956132|1.15558961|

**Sagging below C=2 is separate from becoming negative.** `kappa_one.csv` and `kappa_one_summary.json` classify every κ=1 level as nonpositive, positive below2, or at/above2. In ζ the positive-below2 cases are m=35,78,80,82,84,85,89,90,92,94,96,99,102,116,117. Every one of the105 ζ cells also has a κ≥1 passing sector with 0<λ_r<2; thus a universal floor2 is unnecessary for this finite separator test. Neither these levels nor the many other positive levels below2 are counted in n_-(A).

Validation: all315 cells and21153 sectors retained,829 shared-prefix residuals agree with the input packet within7.11e−15, and twelve768→1024-bit frame repeats preserve every sector classification. No interpolation Gram inverse or float rank heuristic is used. Independent bounded review is in REVIEW.md. All negative/failed cases remain numerical diagnostics; no cofinal claim, route-state or RH export follows.
