# Independent addendum source review

DIAGNOSTIC_NOT_RH. Bounded analytic/source review only. No full numerical run or source matrix regeneration is performed for this review. Original TaskA artifacts and its published commit are retained. Input scope: `INPUT_DH.md` §3 and `INPUT_TWO.md` §§2,5,6.

## Own DH corner: gamma, conductor, signs and absence of a pole

The source is the conductor5 odd-gamma DH completion specified in `INPUT_DH.md`, with

`j_D(u)=exp(−3u/2)/(1−exp(−2u))`,

`c_D=EulerGamma+log(8pi/5)−pi/2`.

Its arch multiplier at zero is−c_D, consistent with log(5/pi)+digamma(3/4). There is no zeta pole functional. Retaining the zeta pole or the zeta even-gamma constant would be a different source, even if its arithmetic coefficients were replaced correctly.

For the constant physical cosine, the overlap is R00(u)=2(1−u/t) on0≤u<t and zero beyond. Multiplying its arch contribution by t/2 gives

`−c_D t/2 + ∫_0^t u j_D(u)du + t∫_t^∞ j_D(u)du`.

Expanding the positive geometric series, each a_r=2r+3/2 contributes

`∫_0^t u exp(−a_r u)du+t∫_t^∞exp(−a_r u)du=(1−exp(−a_r t))/a_r²`.

Consequently the exact source-corner scalar is

`Psi_D(t)=−c_D t/2 + [zeta(2,3/4)−exp(−3t/2)Lerch(exp(−2t),2,3/4)]/4`

`             −sum_(2≤n≤exp t) b_D(n)/sqrt(n)*(t−log n)`.

Here zeta(2,3/4) is Hurwitz zeta, not Riemann zeta at a rescaled argument. The own-source constant mode is `(A_m^D)00=2Psi_D(log m)/log m`. There is no extra factor2 in the displayed arithmetic sum and no pole term. Endpoint n=m contributes zero, so strict/inclusive support is immaterial to this corner value.

For a truncated exponential Lerch sum retaining r=0,…,K at t>0, the omitted nonnegative exponential contribution is bounded by

`4exp(−(2K+7/2)t)/[(4K+7)²(1−exp(−2t))]`.

It is subtracted in Psi_D. Omitting it therefore gives an upper approximation, not a lower positivity bound. This geometric envelope does not include floating-point summation error. Its index convention must match the implementation's actual number of retained terms.

## Signed coefficients and the ascending convolution update

Let tau=(sqrt(10−2sqrt5)−2)/(sqrt5−1), and let a(n) be periodic mod5 with values a1=1,a2=tau,a3=−tau,a4=−1,a0=0. The exact Dirichlet convolution identity is

`a(n)log n=sum_(d|n,d≥2) b_D(d)a(n/d)`.

Because a1=1 this yields the pinned recurrence. Initialize b[n]=a(n)log n for every integer n≥2. Then iterate d in ascending order and subtract b[d]a(k) from b[dk] for every k≥2 with dk within range. At the moment b[d] is used, all its proper-divisor updates have already arrived. Each ordered proper-divisor contribution occurs exactly once. This is algebraically identical to the recurrence, evaluated in point arithmetic; it is not an Euler-product construction.

The exact small controls are

`b2=tau log2`, `b3=−tau log3`,

`b4=−(2+tau²)log2`, `b6=(1+tau²)log6`.

The n6 value is nonzero despite not being a prime power. Both signs and all integer coefficients must remain. A prime-power sieve alone is invalid for DH. Convolution roundoff can propagate to later entries; compensated final corner sums do not independently certify coefficient accuracy. Any coefficient/point checkpoints must therefore state their precision and scope.

## Two-by-two minors and ratios

For a Hermitian block `[[a,b],[conj(b),d]]`, positive semidefiniteness requires a≥0,d≥0 and ad≥|b|². The ratio |b|²/(ad) is a usable test only when **both** diagonals are strictly positive. A positive product ad by itself is insufficient: both diagonals could be negative. A ratio below1 in that case does not rescue positivity.

If d<0, the single-coordinate test already violates PSD. If d=0 and b≠0, the block is indefinite; if d=0 and b=0, positivity reduces to a≥0. The analogous rules apply if a=0. An undefined0/0 ratio must not be reported as an ordinary passing finite ratio. Tiny point values meeting a numerical tolerance should be classified as unresolved rather than silently assigned a sign.

For a shifted graph-floor premise, the actual diagonals are a=(A_m)00+kappa and d=(A_m)jj+kappa(1+omega_j²)^r, as in `INPUT_TWO.md` §6. Under that premise and d>0, the Schur correction |b|²/d is valid. If d<0 the premise already fails. A successful minor does not prove the full graph-floor premise, and the Schur identity does not supply its own sign hypothesis.

A failed own-source DH corner or minor is a finite negative test; a successful corner/minor does not establish the full matrix sign. From §5, the existence of a finite graph-floor constant is stable under a fixed bounded atom perturbation. It therefore cannot universally distinguish the doubled-n2 atom from the original source. This source/quantifier distinction must not be replaced by a blanket arithmetic detector claim.

## Meaning of the first DH failure

Any reported first DH m must specify the searched set, cutoff, observable and numerical sign criterion. Exhausting integers2,…,M_DH can identify the first **observed negative corner on that integer grid** (subject to point accuracy), not the first negative full-matrix eigenvalue, the first real window length, or the first cofinal complement-floor violation. A scan over selected modes or selected m is narrower still. Failure to find a sign change within the declared budget is a bounded negative result, not positivity for all m. The inherited DH cofinal floor theorem does not identify that first integer and cannot fill in unsearched cells.

## Bounded row/diagonal implementation inspection

Read `output/scripts/add_second_rung.py` without running it. Its DH coefficient weights use every integer n<m from the pinned coefficient routine. The own DH constant is−c_D, its digamma argument is3/4+iomega/2 and its exponential arch rates are2r+3/2; no pole is added for DH. The zeta branch separately retains its own gamma and pole.

The row formula is correct: the gamma sine moment is Im digamma/2 minus its exponential tail, and multiplication by sqrt(2)/(pi j) yields K0j; the arithmetic term has the positive sign in A=H+P−B. For the diagonal, the printed expression contains a redundant pair of terms: the two exponential fractions proportional to2omega²/[a(a²+omega²)] and2a/(a²+omega²) add to2/a. Their negative exponential sum cancels the separately added2tail, leaving exactly q(omega) plus the positive gamma boundary correction. The j0 limit and the zeta-only pole entries also agree with the pinned physical formulas. Midpoints from Arb special functions are deliberately converted to MPFR point values; these are not interval matrix-entry certificates.

The code records both diagonal signs, determinant and a separate raw ratio. Its `PSD_minor_pass` checks all three necessary-and-sufficient two-by-two conditions correctly. The initial summary implementation selected a maximum ratio by positive **product** of diagonals; that selection must not be interpreted as a valid PSD ratio if both diagonals are negative. The reviewer has flagged this to the parent: valid-ratio summaries should require both recorded diagonal-positive flags, leaving raw ratios separately labelled.

Its search observable is precisely a failed principal block on modes(0,j),1≤j≤m, for consecutive integers m starting at2 and stopping at the first observed failure or the declared2000 limit. The first such failure is not necessarily the first indefinite full source matrix or the first negative DH corner. Higher-precision selected-row confirmation checks numerical stability, not a certified sign for uncomputed modes or windows.

## Bounded DH streaming implementation inspection

Read `output/scripts/dh_thermometer.cpp` and `dh_constants.h` without compiling or running them. **No substantive own-source, recurrence, tail-sign, atom-ordering or counter flaw found.** The runner declares N=10,000,000,192-bit MPFR coefficient construction and extended-precision streaming point arithmetic. This is not a through-infinity statement and not an interval certificate.

The C++ tau evaluation implements the radical formula directly at192 bits. All b[n] begin at the correct periodic a(n)log n, including exact zero for multiples of5. Composite logs are assembled from earlier smallest-prime-factor logs, an exact real identity evaluated in MPFR. The ascending d update uses the already finalized b[d]; k mod5 selects1,tau,−tau,−1,0 with the correct subtraction signs. Stopping d at N/2 retains every proper divisor that can affect an n≤N. The code does not discard non-prime-power coefficients or impose positivity.

The scalar constants match−c_D/2 and Hurwitz zeta(2,3/4)/4. Its tail retains rates2r+3/2 and is subtracted. The loop variable K is a **term count**, so r=0,…,K−1 is retained; the analytic bound earlier in this report must be used with last retained indexK−1. The implementation keeps32 terms for m<64 and4 for m≥64, giving a small positive omitted exponential contribution of the stated sign. There is no zeta pole cancellation or zeta gamma constant in this source.

Each m is evaluated using strict n<m sums, and only then inserts its own atom. The192-bit S1/S2 snapshots written at checkpoints and the first negative point have the same support as the native value. Native streaming uses b[n]/sqrt n computed in MPFR before conversion to long double, then compensated S1 and S2 sums. The double-precision coefficient export is local output only and does not feed the corner evaluation. Saved minimum sums correspond to the particular native record candidate; that does not certify a global exact ordering.

The first-negative counter concerns Psi_D(log m)<0 on the evaluated integer grid2,…,10,000,000. Its zero sentinel means no observed negative point within that range, not a negative result about all m. The two-by-two-row search in the separate script has a different observable and limit; these two first-failure quantities must not be conflated. Independent or higher-precision checks of selected signed values remain point stability checks unless all error terms are enclosed.

The source, row/diagonal and streaming reviews do not supply a graph-floor theorem, a complete zero list, or an RH-related export. No numerical full run, source build, coefficient scan or matrix reconstruction was repeated by this reviewer.
