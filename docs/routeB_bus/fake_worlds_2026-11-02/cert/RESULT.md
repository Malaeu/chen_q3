# Finite DH negative Rayleigh check and projection envelope

**DIAGNOSTIC_NEVER_A_PROOF. Route B: CHALLENGER / NOT_RH.**

The requested fixed finite DH Rayleigh checks succeeded. The two saved dyadic vectors, evaluated directly with Arb, give strictly negative upper endpoints:

|literal m=N|outward Rayleigh enclosure|
|---:|---:|
|51|−1.32685772638906062688395e−47 ± 3.62e−71|
|55|−0.663920646081049791677195486330354903436092995093398739402280 ± 4.73e−61|

The implementation uses512-bit Arb/acb arithmetic and16 integration panels. Each witness coefficient is an explicitly saved integer divided by2^320. The actual squared norm is retained in the form and denominator; approximate unit normalization is never substituted. The approximate120dps matrix was used only to select the witness. `certify.py` verifies the saved witness from the literal source without loading a matrix, invoking an eigensolver, or trusting its quadrature.

The source is `dh_matrix.py` at `d26831357b6cb3b2b7d4a569d2031e454952b246`, SHA-256 `9554c27549fc0970391c06026d8bfb402ab1cfa3b2f1db3c0db6deeb92a39f00`, independently matched against the pinned remote bytes. All Dirichlet logarithmic-derivative coefficients are recomputed by the exact periodic recurrence in Arb, including non-prime-power integers. The odd arch kernel is e^(−3s/2)/(1−e^(−2s)); the signed constant is −c_D, c_D=γ+log(8π/5)−π/2; there is no pole. The n=m atom is zero because Q(L)=0.

For Q=2(1−s/L)Σc_n²cos(ω_ns)+ΣB_n sin(ω_ns), the integrand is regularized exactly: (2||f||²−Q)/s is evaluated with sinc, and s*j_D(s)=e^(−s/2)/(2*sinc(i*s)). This removes the apparent singularity at0 without dropping a near-zero interval. The callback is meromorphic, with nonfinite evaluation at poles, as required by acb.integral. The full arch tail is2||f||²[atanh(e^(−L/2))−atan(e^(−L/2))]. Integration and rounding errors are included in the output balls; every panel is checked finite with imaginary part containing0. The m51 ball width is explicitly checked below1e−49.

This establishes a negative direction in each of these two finite source forms. It does **not** certify the numerical value of the full minimum, establish that51 is the first negative m, certify DH zero locations or quiet-space ranks, or supply a cofinal conclusion.

## Projection-envelope diagnostic

Using the saved **native** κ=1.1 quiet spaces (not the density-matched spaces), the120dps inputs satisfy δ<R and give:

|m|δ|−R+δ²/(R−δ)|C_viol=R−δ²/(R−δ)−c_D|
|---:|---:|---:|---:|
|55|3.440790097e−8|−0.663920646081048008|0.0427677928792760393|
|80|1.078559230e−11|−1.24068701234965723|0.619534159147885262|
|120|6.853166574e−14|−1.58825368803550097|0.967100834833729005|

These are evaluations of canonical DH/Beurling(7.1), with positive c_D≈0.62115285320177196917. **The envelope remains diagnostic:** R,δ and the zero-derived spaces have not received outward-rounded certification. A certified negative Rayleigh upper must not be silently substituted for a certified full minimum or quiet residual. See `ENVELOPE.md` for the inputs and hashes.

## Replay

```bash
uv run --with python-flint python certify.py 51
uv run --with python-flint python certify.py 55
uv run --with mpmath python envelope.py
```

Run from this directory. `rayleigh_m51.json` and `rayleigh_m55.json` retain the enclosures, endpoints, radii, components, engine version and verifier/witness hashes. `CERT_REVIEW.md` records the separate implementation review. Import provenance and all14 source SHA-256 values are in `IMPORT_PROVENANCE.md` and `IMPORT_SHA256.json`; part D was committed as `a8f0df144461e9cd10c5149721fedb0448800acb`.

On a fresh checkout, restore the prior saved inputs for `envelope.py` with `python3 ../ledger_diff/unpack_cells.py` (Python3.12+). The fixed-vector Arb verifier itself needs only this directory's witness files and python-flint; it does not require that archive.
