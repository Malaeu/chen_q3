# Literal quiet-space conditioning

DIAGNOSTIC_NEVER_A_PROOF. Route B = CHALLENGER / NOT_RH.

Computed 315/315 world/m cells (all three cutoffs and every EDGE_ZERO sensitivity in each computed cell). Exact coverage and missing cells are in coverage.csv; no missing calculation is counted as a successful result.

The primary c=1/4 and secondary c=1/2 schedules make the full quiet residual small, but do not saturate the C=2 count on these cells. The unweighted raw capacity does not separate the planted world from ζ. The exact full Schur inertia identity survives the controls, including cases where the shortcut subtracting dimJ fails. This is not an arithmetic estimate or an RH argument. All m≤120 have L<16, outside the inherited shrinking-κ theorem’s stated large-L regime.

|world|cutoff|cells|J=0|σ resolved|λr statuses|
|---|---|---:|---:|---:|---|
|zeta|c_quarter|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|zeta|c_half|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|zeta|kappa_one|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|dh|c_quarter|105|11|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|dh|c_half|105|105|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|dh|kappa_one|105|0|105|{'CACHED_MP_VALUE': 40, 'REPLAY_MP_FULL_SPECTRUM': 65}|
|plant|c_quarter|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|plant|c_half|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|
|plant|kappa_one|105|0|105|{'REPLAY_MP_FULL_SPECTRUM': 105}|

For each computed cell conditioning.csv reports raw σ², 2σ²/λ_r, full δ=||AQ||, compressed norm, structural rank/dimJ, λ_r resolution, weak singular pair, included minimum gap and last-zero lookahead. Tiny uncached λ_r and unresolved weak σ retain explicit status; their ratios are blank. METHOD.md states the precision branches, normalization and source scope.

|ζ m|cut|dimJ|δ|N_A(2)−dimJ|σmin|λr|
|---:|---|---:|---:|---:|---:|---:|
|16|c_quarter|10|0.11792649|2|0.020292312|0.14296018|
|16|kappa_one|12|1.3627188|0|1.0427285|2.2856436|
|24|c_quarter|14|0.062832479|2|0.011951853|0.0077809225|
|24|kappa_one|17|2.9565294|-1|1.0982818|2.4884532|
|40|c_quarter|21|0.0094973898|4|0.0001083835|2.714016e-05|
|40|kappa_one|25|0.99427208|0|1.0344041|2.1903564|
|55|c_quarter|27|0.0012399132|6|6.7517407e-08|4.2799482e-08|
|55|kappa_one|33|1.2115118|0|1.0984357|2.414586|
|65|c_quarter|31|0.00044412554|7|8.6146183e-09|2.6719592e-10|
|65|kappa_one|38|1.4372878|0|1.1333951|2.7969649|
|77|c_quarter|37|0.00083130215|7|2.7120604e-10|7.6233502e-10|
|77|kappa_one|44|2.3952652|0|1.1017577|2.4591105|
|78|c_quarter|37|0.00039922888|8|3.1016881e-09|2.6190289e-10|
|78|kappa_one|44|1.1524115|1|0.92866814|1.9676416|
|80|c_quarter|38|0.00048820684|8|4.9303083e-09|2.754575e-10|
|80|kappa_one|45|0.95850338|1|0.8980283|1.7315011|
|120|c_quarter|53|5.896471e-06|11|9.9393158e-15|2.6720505e-17|
|120|kappa_one|65|4.7862934|-1|1.0292351|2.2354824|

Calibration: ζm24 κ=1 has dimJ17, δ=2.956529432>2, N_A(2)−dimJ=−1. The eliminated block contributes16 negatives, rather than17; S contributes0. The actual formula16+0−17=−1 holds. At m120 κ=1 the analogous deficit is also−1, while the primary quarter defect is11 with δ≈5.9e−6. Small δ alone does not remove the extra below-threshold complement levels.

The ζ pair111.0295355/111.8746592 enters the strict cut at m65 for c=1/4 (both in the same integer step), m55 for c=1/2 (both in the same step), and m77/m78 for κ=1. pair_111_entry.csv includes the nearby same-m halfspacing sensitivity runs. EDGE_ZERO uses exactly half mean spacing π/log(γ/(2π)), not the full mean. all_included_zero_gaps.csv reports every included distinct-height nearest gap, with the requested threshold0.3 flag.

At ζm24 quarter and half, the closest included gap is unchanged while σ differs by≈1.97e5. At m120 the corresponding σ values differ by≈1.38e17. Quarter2σ²/λr falls from≈.0367172 at m24 to1.76491e−7 at80 and7.39432e−12 at120. A global minimum-gap statistic does not encode the interpolation geometry. CARD_CONDITIONING.md gives this limited hypothesis, its falsifier and the analytic object to hand off.

paired_planted_index.csv compares each identical-window/identical-cutoff ζ and planted row. The finite observed count defect changes by+1, while N_A(2) changes−1 and dimJ changes−2; final totals are in summary.json. CARD_PLANTED_RELATIVE_INDEX.md states the falsifier and the limited scope. This does not make the true-world baseline defect zero.

The planted quarter σ at m120 is9.8497447e−15, compared with ζ9.9393158e−15; similar raw capacity is compatible with an indefinite added quartet. Same-κ DH has a different zero density and sometimes J=0: tall E is retained explicitly. The four supplied off-line quartets below230 and their two raw real conditions are all included when belowT. This comparison does not quietly replace DH by a density-matched world.

The remaining40 original tall-half blanks m80..119 were scheduled for the same MP200/240 method after its cheap120 pilot. Final method/status counts above and tall_acceptance.json state actual completion, agreement gates and diffuse/localized weak-coordinate checks; no A/eigenproblem or E/J/Schur data were changed.

The single tall-DH120half priority resolved σ≈1.24404677e−66 (q129>d121, J=0) in14.95CPU s. MP200/240 agree for the SAME frozen≈80-digit numerical zero inputs; this does not improve root accuracy or propagate root uncertainty. The rough80−66≈14-digit margin is not an enclosure. Its many receipt digits refer only to that fixed-decimal matrix. No inverse-F formula is used in the tall case.

Selected MP120 full-SVD replays agree with MP80 weak conditioning to5.37e−66 relative (DHm24quarter),4.78e−67 (ζm80quarter),3.11e−65 (ζm120quarter). Residuals and precision are in validation_120.json. The faster row-frame QR projectors differ from directly formed MP projectors by at most1.67e−15 on the selected checks. These are numerical consistency checks, not outward-rounded certificates.

Across 2659 complete-cut/sensitivity rows: {'NUMERIC_IDENTITY_PASS': 2659}. Maximum saved EQ residual 2.087e-15; maximum frame orthogonality residual 1.471e-13. Threshold-sign/radius guards remain in every row; a numerical pass is not an interval assertion.

adaptive_kappa_sectors.csv derives the rank sectors at signed thresholds m⁻² and m⁻⁴ from the same saved spectrum, with strict-cutoff endpoint conventions and unresolved count flags. It introduces no further eigenproblem. Full D/B/G/S and Q/U arrays are retained at selected cells, and every source matrix has its own metadata/hash in matrices/.

Replay: python3 scan.py --world zeta --m 16 24 80 120 --skip-existing (analogously dh/plant); python3 aggregate.py; python3 report.py. Checkpoint writes are atomic and skip checks validate parsing, identity and the matrix SHA. Environment/session interruption was recovered by resuming only missing cells. No prior A audit or route state was changed.
