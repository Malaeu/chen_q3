# Nested increment geometry

DIAGNOSTIC_NEVER_A_PROOF. This exploratory variable was registered before its numerical run in PREREGISTRATION.json. It uses the actual source screw function and needs no zero table or RH assumption to evaluate its entries.

For t≥0 let g(t)=−k[χ_(0,t)]/2, extended evenly. With α=1/2 for ζ and 3/2 for DH, the source indicator form is

`k[χ]=c t + 2 Σ_(j≥0)(1−exp(−(2j+α)t))/(2j+α)² − 2 Σ_(log n<t) b(n)(t−log n)/√n + pole(t)`.

Here c=−γ−log(8π)−π/2 for ζ and −γ−log(8π/5)+π/2 for DH. The pole is 32sinh²(t/4) for ζ and zero for DH. The archimedean series is evaluated with trigamma/dilogarithms. Ten independent source-integral checks agree to ≤8.49e−102 at 100 digits.

Fix a mesh Δ. The Gram entries of successive curve increments depend only on separation:

`h_k=2g(kΔ)−g((k−1)Δ)−g((k+1)Δ)`.

These Toeplitz matrices have nested principal prefixes. The innovation v_n is the squared distance of the newest increment from the span of preceding increments when the prefix is positive. Levinson recursion computes the corresponding Schur complement. For positive stationary prefixes, `v_n=v_(n−1)(1−a_n²)` is positive and nonincreasing. This is a general kernel property, not a special theorem about ζ. After positivity fails, subsequent signed pivots are not squared distances.

| Mesh | ζ prefixes | ζ first → last innovation | DH first negative prefix | Length | exp(length) |
|---|---:|---|---:|---:|---:|
| 1/64 | 350, all positive and nonincreasing | 0.0432990 → 0.00871794 | 275 | 4.296875 | 73.46984 |
| 1/128 | 701, all positive and nonincreasing | 0.0269579 → 0.00551493 | 484 | 3.78125 | 43.87085 |

The last grid points are 5.46875 and 5.4765625, respectively, both below log240=5.4806389. Results at 100 and 160 digits agree in all stored 70-digit innovation values and all signs; the reported zero precision differences mean equality at that serialization precision. Values from different meshes are different variables and are not compared as one sequence.

DH negativity is independently replayed by a stored coefficient vector against the direct Toeplitz quadratic form, not merely inferred from the recursion. The normalized negative Rayleigh values are −7.94653e−6 and −1.92529e−5; relative witness replay errors are below 3.50e−70. See VALIDATION.json and both negative_witness.json files. These are floating witnesses, not interval certificates.

This supplies a finite geometric discriminator of the requested kind: the nested increment innovations remain positive and decrease for ζ, whereas DH loses positive geometry. The onset is strongly mesh-dependent, so these runs do not locate a continuum first failure or reproduce the original nonnested A_m onset. Once a nested prefix is indefinite, later positive signed pivots do not restore positivity of the full prefix. No Weyl-radius identification, limiting positivity, cofinal claim, route-state change, or RH export follows.

Reproduce with Python and mpmath: `python innovation.py --dps 100`, `python innovation.py --dps 160`, then `python validate.py`. Full prefix CSVs, direct negative witnesses, source-integral checks and precision checks are retained.
