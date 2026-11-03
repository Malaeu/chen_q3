# Q1 — bounded reproduction and normalization

**DIAGNOSTIC_NEVER_A_PROOF. Route B CHALLENGER / NOT_RH.**

**REPRODUCED for the three executed certificates below. The complete requested large-table audit is PARTIAL, not globally REPRODUCED.** No mathematical discrepancy was found in those executed certificates. No route-state change or RH claim follows.

| Exact published case | Actual replay | Verdict |
|---|---:|---|
| support±4/5, even, T200,N200 | λ_lower=1.0266618704919108500e−17 | REPRODUCED |
| support±4/5, odd, T200,N200 | λ_lower=1.1399115396618374143e−14 | REPRODUCED |
| semilocal P2, full length1.1147, odd degree61 witness | Q=−3.60762498685477970398e−8 | REPRODUCED |

Execution-protocol limitation: the successful runs used `python -I` and freshly staged reviewed code, but inherited `/workspace` cwd. An additional run with explicit fresh cwd was attempted for each case and timed out (150/150/120s); those repeats are NOT counted as successes. See `isolation_repeat/`. No foreign cwd was on the isolated Python module path.

Both lower replays finished in103s; each included a verified Cholesky residual≤7.191e−54 and the published infinite Legendre-tail bound. The upper replay finished in15s with matrix entry radius≈2.70e−435. `replay/` contains actual stdout and regenerated JSON. `published/` is separately labeled author data. Full lower-bound diagnostic fields are compared in `replay_comparison.json`.

An independent physical-form evaluation of the fixed P2 polynomial witness at80dps gives −3.6076249868547797039806802566e−8. The two witness runs use8 panels×24 and8 panels×32 Gauss nodes, with64 inner nodes (the polynomial correlation is integrated exactly up to rounding). Their difference is1.36152e−23. These independent numbers are numerical controls, not interval certificates. All signed pieces, the exact outside-window archimedean tail, and the negative odd pole are retained.

## Independent finite-carrier check

Both parity sectors, N24 (dimensions25even/24odd),80dps, physical-space source formulas, all prime powers. Quadrature8×48 repeated at8×64; displayed eigenvalues agree, with maximum difference below1.6e−80 in the reported60-digit numbers.

| m | full length logm | even finite minimum | odd finite minimum |
|---|---:|---:|---:|
|3|1.098612289|6.26828810738e−8|1.79192439207e−5|
|exp1.6|1.6|2.28112933899e−17|2.23834409328e−14|
|5|1.609437912|1.42011523673e−17|1.48003494946e−14|
|7|1.945910149|2.04968173945e−27|3.91389408992e−24|

These are **finite-subspace upper approximations**, not replacements for whole-window coercivity certificates; no N-convergence is claimed. In particular the naive Fourier N24 odd minimum for P2 remains positive at length1.1147 (7.7816e−6), whereas the degree61 Legendre witness is rigorously negative. The finite Fourier cutoff misses that direction. The independent fixed-witness physical check resolves the apparent mismatch without changing normalization.

## Scope remaining

- Full±31/32, T600,N460 both-parity saved receipts fetched and hashed; not rerun in this bounded quickcheck.
- P2 lower bracket endpoint and odd-before-even ordering: saved lower receipts fetched; not rerun. Upper negative endpoint reproduced. Thus locating the **first** flip inside the entire reported bracket is not independently complete here.
- P3 bracket: upper/even-lower receipts fetched, not rerun; odd-lower receipt is absent at the pinned tree (empty log only). This is a source-provenance gap, not a numerical refutation.
- P5 lower/upper receipts fetched; not rerun. Therefore the source's positivity extension through log7 is recorded as a source claim, not independently certified here.
- No whole-paper proof audit or certificate at arbitrary support is claimed.

`NORMALIZATION.md` resolves half-width/full-length, the Fourier2π factor, both poles, semilocal prime-base cutoff and carrier dimensions. Crucially31/16<log7: the source relies on its separate P5 certificate, not the±31/32 table alone.

Zhu v2 author is Xuefeng Zhu in abstract, HTML and PDF; the observed current records agree. The numerical8.9e−18 lower bound is Theorem1.2, based on Theorem1.1; arbitrary-complex extension is Corollary6.3. No author-identity conclusion is inferred from revision metadata.

Source hash checks:20/20 exact pinned Git blobs MATCH (`SOURCE_HASHES.json`). Executed staging copies differ only by one final newline; actual executed SHA256 and pinned SHA256 are both retained in `EXECUTED_CODE_HASHES.json`. Security and primary-source details are in `SOURCES.md`.
