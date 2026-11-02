# EDGE_LAW_v1

**DIAGNOSTIC_NEVER_A_PROOF. Route B: CHALLENGER / NOT_RH.**

The preregistered finite zeta prediction R in[3,5] passes all three new cells. The stronger explanation that the minimum consists only of an endpoint-jump tail is not supported: a substantial known-zero head and rational Fourier corrections remain. No asymptotic law or RH statement is established.

The task's source base is `8acecc1574740c5163c2a4e8ef75049f6df84313`. The existing ledger and source conventions are preserved; this addendum is integrated on top of the subsequent canon/mirror import and C/E diagnostics, without resetting rh_clean. Literal N=m and L=log m are used throughout. Each endpoint and Rayleigh quotient belongs to the same unit physical vector minimizing the form on J-perp, not the full-carrier ground.

## (i) New zeta cells

T=1.1*2πm/L; q counts positive zeros below T. R=lambda_min/[|f(L/2)|² log(T)/(πT)]. The sign of f is the saved modal sign convention; its square is invariant.

|m|q|T|lambda_min|f(L/2)|R|
|---:|---:|---:|---:|---:|---:|
|160|89|217.892166|4.78557635994e-16|1.24595586641e-7|3.91936171159|
|200|115|260.894294|5.81805177347e-23|4.35176720957e-11|4.52547949348|
|240|139|302.658311|2.34412716825e-25|−3.06872858322e-12|4.14316788910|

The main calculations use120dps/GL192, with row-scaled QR in the physical Gram metric. At m240,160dps/GL256 changes R relatively by4.22e-96 and lambda by2.75e-97. These are numerical checks, not interval eigenvalue/rank certificates. `zeta/` retains full modal vectors, rank/orthogonality diagnostics, predictions and reproducible code.

## (ii) Known-zero head versus tail

For the known real positive zeros, the correct contribution is2|F(gamma)|². Each head is evaluated directly. The independent finite tail prefix runs from T to400. The final column below is the **source balance** lambda minus the directly evaluated prefix through400, not an independently summed or certified infinite tail.

|m|head ≤T / lambda|evaluated (T,400] / lambda|source minus prefix400 / lambda|tail by source balance / lambda|
|---:|---:|---:|---:|---:|
|160|0.362035|0.434742|0.203223|0.637965|
|200|0.438243|0.319563|0.242194|0.561757|
|240|0.349236|0.324766|0.325999|0.650764|

Thus the finite evidence does not identify lambda with an endpoint-only tail. It also does not disprove an eventual selected-family asymptotic statement. Unknown zeros beyond the evaluated census are not silently treated as real or discarded. The source balance is reported separately precisely to avoid converting agreement with the arithmetic form into an independent infinite-zero-sum verification.

## (iii) DH controls and the quartet location

Matched means the **same integer q** as zeta at that m, not the same numerical height cutoff. Native means DH's original κ=1.1. The numerical census was extended from230 to310:67 line zeros plus one new off-line pair account for69 new upper-half-plane zeros, matching two discrete winding runs. This is a numerical count match, not an interval completeness certificate.

|m|mode|q|T|lambda_min|f(L/2)|R|
|---:|---|---:|---:|---:|---:|---:|
|160|matched|89|148.455954|−1.939493373|0.487555375|−761.014358|
|160|native|144|217.892166|−1.952697875|0.276406792|−3249.556165|
|200|matched|115|181.601008|−2.296414814|0.636470214|−621.738334|
|200|native|180|260.894294|−2.306044530|0.418517135|−1939.364905|
|240|matched|139|211.702970|−2.706944220|0.862999258|−451.399289|
|240|native|216|302.658311|−3.707861632|0.892043113|−775.568480|

The DH minima were selected from the full compressed numerical spectra and refined at120dps with saved separation and residual checks. Independent160dps/GL256 scalar source evaluations on the matched/native240 vectors agree relatively to2.07e-120/4.20e-119. This remains numerical minimum identification, not an interval spectral certificate.

The new off-line pair has sigma_right≈0.8695305796406431, gamma≈240.4046723514407. Its reflected quartet is outside the matched cutoffs and native160, but inside native200/240. All six vectors were independently reevaluated on the extended zero list through310, even where the producer originally used the older230 census.

For a quartet of multiplicity nu and F(gamma+i*delta)=a+ib, its signed energy is4nu(a²−b²), while its ordinary positive Gram energy is4nu(a²+b²). The metric correction is−8nu*b². The canonical special witness gives−4nu only because it has F=i; a generic normalized minimizing vector does not have that normalization.

**A mechanism prediction failed:** the first85.699 quartet remains the most negative one in five cells, but native240 switches to the new240.405 quartet. There:

- F(new pair)≈−0.0313157313+1.0126685667i;
- +4Re(F)²≈+0.0039227001;
- −4Im(F)²≈−4.1019905041;
- signed new-quartet contribution≈−4.0980678040;
- first85.699 quartet contribution≈−9.65460e-6.

The native240 source minimum is−3.7078616321. Its directly evaluated head is−3.7237983481, tail prefix(T,310] is+0.00110756069, and source minus prefix310 is+0.01482915527. The latter remains an uncomputed remainder. Individual quartet terms, their cutoff locations, ordinary Gram and metric correction are in `zero_side/dh_extended_quartets.csv` and `dh_extended.csv`.

## (iv) Exact identity, and what it does not imply

Write f=sum c_n phi_n, d_0=1,d_n=sqrt(2), b=L/2, omega_n=2πn/L. Away from the removable modal poles, the exact finite-carrier identity is

    F(t) = 2 f(b) sin(bt)/t + r_f(t),
    r_f(t) = 2 sin(bt)/(sqrt(L)t)
             * sum_(n=1)^m d_n c_n omega_n²/(t²−omega_n²).

For each finite block of real zeros, this gives the exact square expansion

    2 sum F² = 2 sum edge² + 4 sum edge*r_f + 2 sum r_f².

The cross term has no fixed sign. On(T,400], the endpoint/cross/remainder-square terms divided by the exact block sum are:

|m|endpoint²|cross|remainder²|
|---:|---:|---:|---:|
|160|0.398919|−0.803754|1.404835|
|200|0.339026|−0.593652|1.254627|
|240|0.226067|−0.566999|1.340932|

The identity and the finite-vector remainder bound were independently checked. The bound is m-dependent and too large to discard the remainder at T=1.1*Omega. For fixed f and cutoff tending far beyond Omega, replacing zero phases by their average and using leading zeta zero density gives2|f(b)|²[log(T/(2π))+1]/(πT), with leading coefficient2. That is an averaged far-tail model, **not** a uniform theorem along the moving m-dependent cutoff. It neither explains coefficient4 by itself nor refutes the observed[3,5] range.

**HYPOTHESIS / evidence / falsifier / handoff:** the numerical selected-family ratio survives; the tail-only explanation does not account for the measured head and cross terms. A source argument must control these terms at the moving cutoff rather than appeal only to the endpoint expansion. For DH, the new quartet causes an actual change of the native minimizing direction, while matching the smaller zeta density retains the older quartet. The signed complex evaluation data discriminate that mechanism; ordinary positive capacity alone does not. No positivity of the uncomputed zeta zero side is assumed.

## Artifacts and replay

`summary.csv` contains all nine new cells, directly evaluated heads/prefixes, and separately labeled source balances. `AGGREGATE_VALIDATION.json` independently checks normalization and R from the saved modal vectors. `zero_side/FORMULAS.md` gives the full conventions and finite bounds. Each subdirectory has its own report, predictions and replay scripts. The existing saved controls require `python3 ../ledger_diff/unpack_cells.py` from this directory on a fresh checkout (Python3.12+). New dense matrices are regenerated by the committed scripts; local source caches are intentionally not published.

After the subdirectory calculations, run `uv run --with mpmath python summarize.py`. `SHA256SUMS` binds the published artifacts. All failures and uncomputed remainders are retained; no route or proof status is promoted.
