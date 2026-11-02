# Adaptive threshold on saved interpolation quiet spaces

**DIAGNOSTIC_NEVER_A_PROOF.** No new eigenproblems, matrix constructions or zero computations. Source: rh_clean @77c22cb60e70634d1c75ac75538e06cdf7db5f3b. Source JSON Git blobs were checked against the pinned repository files before reading. Scalar arithmetic uses200-digit Decimal.

Use μκ=δκ(1+10⁻⁶), N_A(μ)=#{λ_i<μ}, and zero-based λ_r, the first level after r lower eigenvalues. All84 original points are retained. The count includes the ground and every negative level. Strict counting means saturation is equivalent here to λ_(r−1)<μ≤λ_r; equality λ_r=μ is allowed. No equality boundary is numerically close in these data.

## Saturating sectors

Unlike the fixed power thresholds, the adaptive threshold **does saturate** on the following early sectors. Within each sector the interpolation subspace and δ are unchanged. The continuous endpoints are inherited zero-entry heights divided by Ω; the listed grid points are the actual saved samples.

|m|Saved κ values|Continuous κ sector (approximately)|r=N_A(μ)|δ|λ_r|λ_r/δ|
|---:|:---|:---|---:|---:|---:|---:|
|16|1.0,1.02|[1, 1.0366061]|12|1.36271876|2.28564356|1.67726726|
|16|1.04,1.06,1.08,1.1,1.12|(1.0366061, 1.1285158]|11|0.334108215|1.23682346|3.70186485|
|16|1.14,1.16,1.18|(1.1285158, 1.1949369]|10|0.117926486|0.142960182|1.21228221|
|24|1.02,1.04|(1.0117145, 1.0489897]|16|0.591690030|2.27276429|3.84114008|
|24|1.06,1.08,1.1|(1.0489897, 1.1163561]|15|0.223322024|0.417385180|1.86898351|
|32|1.0,1.02|[1, 1.0229743]|21|1.21381573|2.30665006|1.90032968|
|32|1.04|(1.0229743, 1.0485669]|20|0.532346472|0.970355081|1.82278860|
|40|1.0,1.02|[1, 1.0207732]|25|0.994272082|2.19035639|2.20297485|
|40|1.04|(1.0207732, 1.0577718]|24|0.549285345|0.750623135|1.36654499|

These are finite saturation checks at the saved residual scale. They do not establish an unbounded family with a controlled residual. The previous fixed-μ failures remain unchanged: the threshold used here is different.

## Every saved κ: count excess and L12 gap ratio

Each entry is **N_A(δ⁺)−r ; λ_r/δ**. Zero excess means saturation. Full δ, μ, r, λ_r and threshold margins are in scan.csv.

|κ|m16|m24|m32|m40|
|---:|:---|:---|:---|:---|
|1|0 ; 1.6772673|3 ; 0.84168051|0 ; 1.9003297|0 ; 2.2029748|
|1.02|0 ; 1.6772673|0 ; 3.8411401|0 ; 1.9003297|0 ; 2.2029748|
|1.04|0 ; 3.7018648|0 ; 3.8411401|0 ; 1.8227886|0 ; 1.3665450|
|1.06|0 ; 3.7018648|0 ; 1.8689835|1 ; 0.95555051|1 ; 0.72995130|
|1.08|0 ; 3.7018648|0 ; 1.8689835|1 ; 0.95555051|1 ; 0.72995130|
|1.1|0 ; 3.7018648|0 ; 1.8689835|1 ; 0.95555051|1 ; 0.72995130|
|1.12|0 ; 3.7018648|1 ; 0.12383599|1 ; 0.95555051|1 ; 0.082674975|
|1.14|0 ; 1.2122822|1 ; 0.12383599|1 ; 0.078003723|2 ; 0.0028576441|
|1.16|0 ; 1.2122822|1 ; 0.12383599|2 ; 0.0077418418|2 ; 0.0028576441|
|1.18|0 ; 1.2122822|1 ; 0.12383599|2 ; 0.0077418418|2 ; 0.00024742542|
|1.2|1 ; 0.074176951|2 ; 0.016746946|2 ; 0.00054352076|2 ; 0.00024742542|
|1.22|1 ; 0.074176951|2 ; 0.016746946|2 ; 0.00054352076|3 ; 0.000014788137|
|1.24|1 ; 0.074176951|2 ; 0.016746946|2 ; 0.00054352076|3 ; 0.000014788137|
|1.26|1 ; 0.074176951|2 ; 0.0016324262|3 ; 0.000012680934|4 ; 4.2186332e-7|
|1.28|1 ; 0.074176951|2 ; 0.0016324262|3 ; 0.000012680934|4 ; 4.2186332e-7|
|1.3|1 ; 0.074176951|2 ; 0.000046218665|3 ; 0.000012680934|4 ; 8.3035520e-9|
|1.32|1 ; 0.074176951|2 ; 0.000046218665|3 ; 2.2328192e-7|4 ; 3.0417406e-10|
|1.34|2 ; 0.0027657820|2 ; 0.000046218665|4 ; 8.1425210e-9|4 ; 3.0417406e-10|
|1.36|2 ; 0.0027657820|2 ; 0.000046218665|4 ; 8.1425210e-9|5 ; 6.2824193e-12|
|1.38|2 ; 0.000081538365|3 ; 0.0000012794435|4 ; 2.4501064e-10|5 ; 6.2824193e-12|
|1.4|2 ; 0.000081538365|3 ; 0.0000012794435|4 ; 2.4501064e-10|5 ; 6.8071143e-14|

## Checks and reproduction

The script checks sorted eigenvalues, N_A(μ)≥r and the exact scalar equivalence between count saturation and λ_(r−1)<μ≤λ_r for all84 rows. The1e−6 inflation changes no count; the nearest threshold-to-eigenvalue distance, relative to μ, is0.04445045. Input bytes and Git blobs are recorded in provenance.json. It imports only standard-library Decimal/JSON/CSV/hash utilities: there is no eigensolver or new linear algebra.

Run `python3 check.py` from any directory. It reads the four parent cell_m*.json files and writes scan.csv, saturation_windows.csv, provenance.json and this report. Numerical reliability inherits the parent SVD and independent polynomial-kernel validation; this postprocessing is not an interval certificate.
