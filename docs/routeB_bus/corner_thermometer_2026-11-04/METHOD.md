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
