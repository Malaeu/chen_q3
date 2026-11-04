# B+ literal component assembly

Diagnostic only: CHALLENGER_NOT_RH. This extension imports the decomposition conventions from the owner-selected two-cores verdict, not its PAPER claims as established arithmetic suppliers. The verdict's actual Git blob is4663cd8ef05f3a54c48def00824442d640e0b4eb. B+ preregistration was remotely confirmed at44e89c1277dde897816b35c637fa7c926ed5d2c6 before these runs.

API: `core_components.build(m, world='zeta') -> (parts, meta)`. World accepts `zeta`, `dh`, or `DH`. The parts dictionary contains float64 matrices `H`, `B`, `A`, vector `p`, frequencies `omega`, the diagonal vector `W=1+omega**2`, and signed longdouble `coefficients=b(n)` indexed0..m-1 before division by sqrt(n). The physical basis has indices0..m. `core_components.corner(m, world)` returns a dictionary `H00,B00,p0,A00` from the direct n=0 formula and does not assemble full matrices. Run with BLAS1 or2; validation used1.

The decomposition is A=H+ppᵀ−B. H uses the complete appropriate gamma/archimedean branch, endpoint correction and analytic tail. In the pinned source notation, B has diagonal pd and off-diagonal

    -d_i*d_j/pi * (i*ps_i-j*ps_j)/(i*i-j*j).

H uses the positive divided difference of its own archimedean moment, with diagonal c+arch_diagonal+2*tail. Its n=0 diagonal is the direct pinned formula, including the distinct coefficient2 in its endpoint-square term. No terms are moved between the arithmetic and archimedean parts. At float precision, different parenthesizations of the displayed reconstruction can differ by a few ulps; this is recorded explicitly.

For zeta, alpha=1/2, c=−EulerGamma−log(8pi)−pi/2, tail=atanh(m^-1/2)+atan(m^-1/2), all prime powers are present, and

    p_j=sqrt(2/L)*d_j*sinh(L/4)/(omega_j**2+1/4).

This equals the unchanged source's pole vector. For DH, alpha=3/2, c=−EulerGamma−log(8pi/5)+pi/2, tail=atanh(m^-1/2)−atan(m^-1/2), and p is identically zero. DH b(n) is computed by the full triangular divisor recurrence

    b(n)=a(n)log(n)−sum_{d|n, 2<=d<n} b(d)*a(n/d),

with a(n) periodic mod5 as (0,1,tau,−tau,−1), tau=(sqrt(10−2sqrt(5))−2)/(sqrt(5)−1). A divisor sieve updates all multiples after each settled b(d). There is no Euler or prime-support assumption. In particular b_D(6)=(1+tau²)log(6)=1.9363560766210387864 at displayed precision. All signed nonzero coefficients enter the moments.

The existing `source_float.py`, `rayleigh_pinned.py`, and old `MANIFEST.json` were not rewritten. New code verifies the unchanged source_float SHA256627579485355b2907fbb34c3ab91ca09ac067b84cc65aa163f5d36207bbe313e and the original analytic source pin. The new extension manifest is `CORE_MANIFEST.json`.

`validate_core_components.py` executes the unchanged pinned source freshly at m80 and160,256 bits, in both worlds. It independently evaluates the arithmetic moment sums and pole at MPFR precision, then obtains H from the pinned A+B−ppᵀ. This checks all component matrices and coefficients, exact float matrix symmetry, direct corner components, W, pole norms, and DH's nonprime b6 and absent pole. Zeta reconstruction is also compared to unchanged source_float. Maximum component discrepancies in the final pass:

|m|world|H|B|p|A|
|---:|---|---:|---:|---:|---:|
|80|zeta|2.67e-15|6.67e-16|4.45e-16|2.45e-15|
|80|DH|1.78e-15|6.67e-16|0|1.78e-15|
|160|zeta|3.11e-15|6.67e-16|1.12e-16|2.95e-15|
|160|DH|2.67e-15|8.89e-16|0|2.67e-15|

An additional fresh MPFR comparison of EVERY coefficient through n3000, without constructing a large MP matrix, found maximum errors4.68e-19 for zeta and1.05e-17 for DH. See `core_coefficients_3000.json`.

Only after these comparisons passed, both worlds were assembled at m3000. Final BLAS1 assembly wall time was1.15s zeta and3.74s DH, peak RSS428.3MiB. Both worlds were finite and exactly symmetric. The source reconstruction discrepancy was at most1.78e-15. These benchmarks contain no eigensolver, planted form, C*, or detector computation.

The first development pass recorded last-bit asymmetry from applying the two diagonal basis factors in a different order above and below the diagonal. That source and complete observations are retained as `core_components_initial_rounding.py` and `core_initial_rounding_*`. The final code multiplies by one symmetric factor, so symmetry holds by arithmetic construction. No averaging, positivity modification, or eigenvalue clipping is used.

Final full validation plus benchmarks used9.77 CPU seconds; the preserved first pass used12.11 CPU seconds; the additional all-coefficient check used0.70 CPU seconds. Extension numerical work totals22.58 CPU seconds, below its180 CPU second budget. Python3.12.14, NumPy2.3.5, SciPy1.17.0, gmpy2 2.3.2, python-flint0.9.0. Longdouble has64 mantissa bits on this host; equal-to-double platforms fail closed and need another arithmetic promotion.

The builder performs no projection or normalization constraint. In particular it inserts no pole into DH. Physical pole-null Sobolev projection, literal-p comparison, B−Q, underweighting, all detectors, and high-precision DH witnesses belong to the downstream driver. Nothing here establishes a cofinal statement or RH.
