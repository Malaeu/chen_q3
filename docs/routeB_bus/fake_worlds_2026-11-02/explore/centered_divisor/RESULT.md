# Centered divisor Gram on zeta J-perp

**DIAGNOSTIC_NEVER_A_PROOF.** The all-Lambda centered operator is preflight §7, equations(7.1)–(7.7). Its full floor compensator and full output continuum are retained. Each source uses literal N=m,L=log m and the κ=1.1 complement synthesis U.

The denominator is max absolute eigenvalue of UᵀqU, where q=A+(c*−4)I+P≥3 and c*=γ+log(8π)+π/2. P≥3 retains every prime power of exponent at least3. It is not the Rayleigh value of q on the maximizing Gram vector.

|m|rank U|Gtilde maximum|q norm|ratio|ratio/L|physical peak/Ω|modal peak/Ω|
|---:|---:|---:|---:|---:|---:|---:|---:|
|20|8|3.763607366|5.351561116|0.7032727992|0.2347582277|0.8898513419|0.9|
|40|18|11.48654947|6.3657223|1.804437726|0.4891560562|0.9405008543|0.95|
|60|29|26.00993198|6.988053557|3.72205676|0.9090726741|0.9846120965|0.9833333333|
|80|41|38.23915699|8.16830364|4.681407385|1.068320158|0.9506726726|0.95|
|120|64|39.90414498|8.756363562|4.557159453|0.9518887337|0.9813385706|0.9833333333|

The preregistered middle-band prediction fails: all top-vector peaks lie at0.89–0.985Ω, toward the upper modal band. The ratio/L varies from0.2348 to1.0683 across the prescribed range; the full table does not justify a stable proportional-to-L law. The later three values are closer, but selecting that subsequence would not establish the preregistered claim. No asymptotic growth or obstruction is inferred from these five cells.

Every full centered matrix is numerically positive: minimum eigenvalues range1.3657–1.6457. They exceed the independent N=1 contribution sum_(m/2<d≤m)Lambda(d)/d by0.585–0.887. The physical Fourier peaks were searched on[0,2Ω] using2001 samples and high-precision stationary-point refinement. The analytic triangle bound beyond2Ω is below the observed peak in every cell. A4001-point m120 repeat agrees; this is not a rigorous extremum enclosure.

The m120 rebuild at160dps changes the centered matrix by at most3.38e-98 entrywise and the ratio relatively by9.70e-101. It uses the same120-digit source A,U, so this checks evaluation precision rather than claiming160-digit source accuracy. Independent direct higher-power entries plus an SVD confirm the q denominator to relative3.39e-161.

An independent m6 mixed physical profile was checked by direct integration of the full output ||Z_N f−C_N f||², including the exponential output tail. Its all-Lambda sum agrees with the moment matrix within2.11e-81. N=1 gives norm exactly1 to working precision. The retained output tail is0.6775424 for that test, so truncating it would visibly fail.

Publication subset: PREDICTIONS.md, centered.py, validate.py, finalize.py, results.csv, validation.json, RESULT.md, and the six compact cell JSONs. Dense matrices are reproducible and omitted from publication; local compressed copies reside only in/tmp. Each compact cell retains the top physical vector, scalar diagnostics and source hashes.

Replay:
```bash
for m in 20 40 60 80 120; do uv run --with mpmath --with numpy centered.py "$m" 100; done
uv run --with mpmath --with numpy centered.py 120 100 1
uv run --with mpmath --with numpy centered.py 120 160 1
uv run --with mpmath --with numpy validate.py
uv run --with mpmath --with numpy finalize.py
```
