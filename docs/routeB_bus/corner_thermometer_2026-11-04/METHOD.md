# Method and replay

Diagnostic, never a proof. The displayed scalar is the unchanged Suzuki formula pinned by prior Gate0. Pre-registration precedes every numerical run and fixes the sampling conventions.

## Stable scalar and antiderivative

Let α=[ψ(1/4)−logπ]/2 and C=(π²+8G)/4−8. Cancel the pole4/√m against the r0 Lerch term exactly. With S_j=Σ_{n<m}Λ(n)(log n)^(j−1)/√n,

Ψ(L)=4e^(L/2)+αL+C−LS1+S2−4Σ_{r≥1}e^(−(2r+1/2)L)/(4r+1)².

A continuous primitive, including the continuous prime-power knees, is

F(L)=8e^(L/2)+αL²/2+CL−[L²S1−2LS2+S3]/2+8Σ_{r≥1}e^(−(2r+1/2)L)/(4r+1)³.

Here S3=ΣΛ(n)(log n)²/√n. The primary mean is[F(logM)−F(log2)]/log(M/2). For the lower endpoint0 use F(0)=(7/2)ζ(3)+π³/8. Do not use a geometric-tail formula with a vanishing denominator at0.

After rK the positive remainder of the subtracted Ψ tail is at most

4e^(−(2K+5/2)L)/[(4K+5)²(1−e^(−2L))].

The primitive remainder has coefficient8 and denominator(4K+5)³ instead. The runner retains32terms below m64 and3terms thereafter. Constants in constants.h were rounded from80dps special-function values. The tail bounds do not certify elementary-function rounding or the accumulation of every operation.

## Exhaustive native pass

Compile without fast-math:

```bash
g++ -O3 -std=c++17 scripts/sieve.cpp -o /tmp/corner_sieve
g++ -O3 -std=c++17 scripts/thermometer.cpp -o /tmp/corner_thermometer
/tmp/corner_sieve /tmp/corner_primes.bin
/tmp/corner_thermometer /tmp/corner_primes.bin <output-directory> /tmp/corner_values.float64
```

The odd-only sieve emits all primes through10⁸ as native uint32 values; the execution host is little-endian. The runner generates each higher prime power once. Every integer m is evaluated before its own atom is inserted, maintaining n<m. It streams Kahan long-double sums, an extrema/top20 heap, strict record rows, log-bin minima/maxima and labelled means. G1 is checked as its three small m are encountered; any failure exits before the large range. The execution reported64 mantissa bits for long double. Other precision/platforms require their own checkpoint gate.

The native output file RECORD_MINIMA.csv was packed, without numeric transformation, into seven gzip CSV shards of at most100000data rows. Repeated headers are omitted by scripts/records.py during reconstruction. RECORDS_INDEX.json includes the full reconstructed SHA256. Local raw doubles are a storage conversion only; extrema and record comparisons use native long double before conversion.

## Independent checkpoints and refinement

scripts/checkpoints.py uses mpmath40dps and the original Catalan/Lerch formula, with separate compensated bucket sums over the shared prime file. It includes all prime powers by recurrence. Its frozen receipt does not read any native sum. The scripts record workspace defaults; set their ROOT/OUT/PF paths to your replay workspace if different.

scripts/refine.py starts from independently computed checkpoint sums, adds the missing primes/powers, and reevaluates the40-point global native guard band and the maximum±2 neighborhood using the original formula. It also checks both continuous uniform-t means from the independent S3 and order3 Lerch antiderivative. This bounded refinement improves point accuracy and ranking but is not an independent global interval scan.

G3 is not run: the suppliedγ²+1/4 denominator differs from Suzuki'sγ² kernel, and a truncated critical-line list cannot silently provide an unconditional complete zero representation/tail. The registered approximate reference0.0462 is retained, with that distinction stated in the result.

The supporting scripts require mpmath; plotting requires matplotlib; verification uses the Python standard library and mpmath. scripts/verify.py checks the saved gates, exact native record order/shard reconstruction, refinement ordering, interval of sampled m, counts and all packet hashes. Large local arrays are not committed. No Lean/Arb certificate, RH claim or route-state/export change is asserted.

## Addendum implementation

scripts/dh_thermometer.cpp implements the own-source DH Dirichlet-convolution sieve at MPFR192bits through10⁷. It builds high-precision logs via smallest-prime-factor recursion, initializes a(n)log n and processes all ascending proper divisors d. Residues of k modulo5 select multiplication by1,τ,−τ,−1 or0. τ is computed directly from its radical expression at192bits. No ζ prime support or pole is imported.

For an ordinary development environment compile with MPFR/GMP headers/libraries, e.g. `g++ -O3 -std=c++17 scripts/dh_thermometer.cpp -lmpfr -lgmp -o dh_thermometer`. This execution used the matching header in /workspace/stiffness/deps/gmpy2 and `-l:libmpfr.so.6 -lgmp`, without fast-math. Invoke `dh_thermometer <output-directory> <local-coefficient-double-file> <local-Psi-double-file>`. Dense MPFR coefficients and prefix sums feed the compensated native stream; exported double arrays are local storage and do not feed back. The own Γ tail uses32terms for m<64 and4terms thereafter, with the positive geometric remainder derived in ADD_SOURCE_REVIEW.md. Source constants in dh_constants.h were computed at80dps; all saved corners are checked through the independent60dps formula.

scripts/add_dh_checks.py validates the saved192bit prefix sums with60dps own Gamma/Lerch, recursively checks coefficient spots and independently builds small corners75,463. It compares all7grid A00 values with the separate row/diagonal engine, and checks the global native minimum's neighbors. Local paths in this script and the row scripts document this run; set them to your replay workspace as needed. No high-precision global second DH thermometer run is claimed.

scripts/add_second_rung.py computes only row0 and the diagonal at256bits, retaining Gamma, the ζ pole where appropriate, and all signed source atoms. Smallm16 is checked against the unchanged pinned full builder. The dense DH screen scripts cover every m2…2000/all j using float64 analytic formulas, then every raw ratio above.999999 receives≥256bit confirmation. Original seven-cell critical failures and first PSD/raw events also have320bit checks. Sparse-cell and full-row high-precision engines cross-check independently. Both row scripts use their own source's parity/conductor/pole data.

For s=|A0j|²/(A00Ajj), use raw s as requested but also retain A00,Ajj and determinant. The equivalent Schur-ratio criterion requires both diagonals>0. Negative diagonals may produce s<0 while the block fails PSD; zero diagonals need their range/off-diagonal condition. All summaries enforce that distinction. Point confirmations do not certify a uniform float-screen error bound or formal firstness.

The addendum prediction blob is checked separately in ADD_PREREGISTRATION.json. scripts/verify.py now checks the exact unchanged original Task A prediction prefix, while scripts/add_verify.py checks the full newly registered file and the addendum data. SHA256SUMS is regenerated for the combined packet. Original Task A compressed record shards remain unchanged; the DH55,052record rows are in ADD_DH_RECORD_MINIMA.csv.gz. Source-reviews and numerical gates are diagnostics only.
