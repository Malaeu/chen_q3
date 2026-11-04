# Independent corner-thermometer review

DIAGNOSTIC_NOT_RH. Bounded analytic/implementation review; no exhaustive scan is repeated here. Numerical observations and checkpoint agreement do not certify positivity or prove RH. The prediction blob and preregistration remain unchanged.

## Stable exact explicit formula

Put L=log m, and define

`alpha=(digamma(1/4)−log pi)/2`,

`C=(pi²+8 Catalan)/4−8`,

`S1(L)=sum_(n≤exp L) Lambda(n)/sqrt(n)`,

`S2(L)=sum_(n≤exp L) Lambda(n)log(n)/sqrt(n)`,

`S3(L)=sum_(n≤exp L) Lambda(n)log²(n)/sqrt(n)`.

The Suzuki explicit formula used by the earlier source lock is exactly

`Psi(L)=4exp(L/2)+alpha L+C−L S1(L)+S2(L)−T2(L)`,

where

`T2(L)=4 sum_(r≥1) exp(−(2r+1/2)L)/(4r+1)²`.

Indeed the r=0 term of `exp(−L/2)Lerch(exp(−2L),2,1/4)/4` is exactly4exp(−L/2), and its negative sign cancels the positive4exp(−L/2) in the pole term. It is important not to retain either copy after removing the other. All remaining exponential-tail terms are positive and are subtracted from Psi. The large4sqrt(m), LS1 and S2 terms still cancel substantially; extended-precision compensated arithmetic and independent checkpoints remain appropriate.

If terms r=1,…,K are retained and L>0, the omitted nonnegative tail obeys

`0≤T2_remaining(L)≤4 exp(−(2K+5/2)L)/[(4K+5)²(1−exp(−2L))]`.

This follows by fixing the first omitted denominator and bounding the remaining exponential factors by a geometric progression. It is a uniform bound on[log2,log M] after substituting L=log2 on the right. Omitting this tail makes the computed Psi an upper approximation; the sign cannot be reversed when discussing positivity. A point calculation with a tiny remainder bound is still distinct from a full rounding-error certificate.

## Uniform-t antiderivative and endpoint bookkeeping

An exact primitive for L>0 is

`F(L)=8exp(L/2)+alpha L²/2+CL−[L²S1−2LS2+S3]/2+T3(L)`,

`T3(L)=8 sum_(r≥1) exp(−(2r+1/2)L)/(4r+1)³`.

Differentiating T3 gives−T2, with the factor(2r+1/2)=(4r+1)/2. Between prime powers the arithmetic derivative is−LS1+S2. At a prime-power endpoint n=exp L, the added quadratic term is−Lambda(n)(L−log n)²/(2sqrt n)=0, so F remains a valid continuous primitive. Using≤rather than<at the endpoint changes neither Psi nor F.

Therefore the primary registered mean is exactly

`[F(log M)−F(log2)]/log(M/2)`.

It is not an ordinary average over integer m, and is not exactly the trapezoid approximation on the log-integer grid. Those two quantities may be reported as distinct controls, with their own labels.

The omitted primitive tail after r=K satisfies

`0≤T3_remaining(L)≤8 exp(−(2K+5/2)L)/[(4K+5)³(1−exp(−2L))]`.

For the separately requested mean on[0,log M], a geometric remainder bound with1−exp(−2L) in the denominator must not be evaluated at L=0. Instead the exact lower-end constant is

`F(0)=8+8 sum_(r≥1)(4r+1)^−3=(7/2)zeta(3)+pi³/8`.

Thus the labelled mean on[0,log M] is `[F(log M)−((7/2)zeta(3)+pi³/8)]/log M`. This identity also avoids a slowly convergent numerical series at0.

## G3 and the zero representation

The proposed expression

`2 sum_(gamma>0) [1−cos(gamma L)]/(gamma²+1/4)`

is **not** Suzuki's Psi zero identity. If the full relevant zero multiset is on the critical line, Suzuki's paired positive-height expression uses **gamma²** in the denominator. Replacing that denominator by gamma²+1/4 produces a different function, not a more stable evaluation of the same one. The reference2+EulerGamma−log(4pi) is associated with the reciprocal rho(1−rho) sum; it should not silently be promoted into an exact finite-interval mean for the gamma² kernel.

A list containing only known critical-line zeros is not an unconditional complete source for Psi. Any comparison through such a list must state its completion/zero-location and omitted-tail premises. Without them G3 is a conditional or truncated diagnostic, not an independent unconditional accuracy gate. In particular no finite table establishes the absence of off-line zeros. Skipping an optional invalid or unpaid G3 is preferable to relabeling it as the exact Suzuki identity.

## Bounded implementation and existing-receipt review

Inspected `scripts/thermometer.cpp`, `constants.h`, `checkpoints.py`, `sieve.cpp` and the available native/checkpoint receipts. **No substantive sign, tail, counter, atom-ordering or mean-normalization flaw found.** This is source inspection and receipt review, not an independent exhaustive run.

The odd-only sieve is an ordinary Eratosthenes construction: marking starts at p², skips even multiples, and emits2 followed by unmarked odd integers. Wide integer multiplication is used where needed. The runner's higher-power generation starts at p², includes every exponent through the range limit, and uses an overflow-avoiding multiplication guard. Distinct primes cannot generate the same integer prime power. The observed5,761,455 primes plus1,404 higher powers match the checkpoint total5,762,859 arithmetic atoms at M. The shared prime file makes the checkpoint formula/summation independent of the native streaming sums, rather than providing an independent prime-file census.

Each integer m is evaluated **before** its own prime-power atom is inserted, so all running sums have n<m support. This is mathematically correct because the n=m atom contributes0 to both the linear Psi expression and the quadratic primitive. F(log2) computed with zero sums is therefore also correct. At non-prime-power checkpoints10^k strict/inclusive support agrees even for the raw S1,S2,S3 values. The independent checkpoint implementation includes endpoints and evaluates the original pole/Catalan/Lerch formula, without reading native sums; it uses40 decimal digits and compensated bucket sums. Prime powers are weighted as log(p)p^(−k/2), with log n=k log p.

`constants.h` matches alpha,C and F(0) derived above. Native S1,S2,S3, uniform-m summation and trapezoid accumulation use long-double Kahan compensation. The receipt reports64 mantissa bits for long double. The parent reports compilation without fast-math; compensated-summation semantics rely on retaining that choice. The final floating subtraction of the large analytic terms is not itself an interval enclosure, and checkpoint agreement must not be described as a proof of a uniform rounding bound.

The implemented tail is exactly T2 or T3: power begins at m^−2, the outer factor is4/sqrt(m) or8/sqrt(m), and the primitive adds its positive T3 tail. For m<64 it retains32 terms; the uniform omitted T2 bound is at most the bound above at m2,K32 (below3e−24). For m≥64 it retains3 terms; the worst omitted T2 bound is below6.2e−18 at m64. T3 has a still smaller analogous bound. The change in term count introduces only this explicitly bounded omitted-tail difference; it does not reverse its sign.

The exact-primitive primary mean uses `(F(log M)−F(log2))/log(M/2)`, as required. The zero-to-log-M control subtracts the closed-form F(0), while the log-grid trapezoid accumulates `(Psi_m+Psi_(m−1))/2 * log(m/(m−1))`. The ordinary integer mean divides by M−1. These quantities are correctly kept separate. In the available receipt the primary continuous mean is.04618405477529…, the log-grid trapezoid is.04722413217460…, and the ordinary integer mean is.04596677190964…; the difference between them is not a normalization error.

The runner evaluates99,999,999 integers2 through100,000,000. Extrema, strict record minima and the20-entry heap use long-double values. The double conversion is only for local raw-value storage and does not feed back into those native selections. The existing G1 receipt passes all three prescribed1e−10 checks. At M the native value.05738043229361877… agrees with the independent40-dps value.05738043229363766… to about1.9e−14. These are point diagnostics, not interval positivity certificates.

**Ranking limitation:** a native top20 or strict-record list is an arithmetic-dependent numerical ordering. When candidate values are closer than rounding uncertainty, retaining only the native20 and refining them cannot by itself certify the exact global20. A sufficiently broad guard band/neighborhood or an explicitly labelled native numerical ranking is needed; the parent has noted this and is arranging local high-precision refinement. This caveat does not invalidate the exhaustive native observations or the checkpoint gates. No mathematically certified exact ordering is claimed by this review.

G3 remains optional and unpaid unless its proper kernel, completion and tail assumptions are supplied. No zero table, RH assumption, new source matrix or route-state/export modification was used in this independent review.
