# Independent FIRST_STEP_LOG3_SOS audit

**Verdict: CONFIRMED — fixed-support computer-assisted PAPER certificate.**

`FIRST_STEP_LOG3_SOS_PAPER_AUDIT_PASS`

This is an audit of the claimed local theorem, not a new RH proof. Route B remains CHALLENGER / NOT_RH. No Lean or Arb run, global extension theorem, or route-state change is asserted. Numerical normalization controls are DIAGNOSTIC_NEVER_A_PROOF; acceptance rests on the separately reviewed analytic bounds, interval assertions and exact rational signs below.

Source: `PROSHKA_VERDICT_FIRST_STEP_LOG3_SOS_2026-11-03.md @e4390b8`, exact snapshot `SOURCE.md`, SHA256 `4daedf962be48ffa858f00afba6977654843cfcc099569b2b0bcd4a454d8aa01`. Source size29186 bytes. Embedded generator extracted without modification, SHA256 `453acb052cb87a6fc547b8c7e6028a0a9ca3fad9db2942f213e0f126596b4e8b`.

## Executed independent replay

Each run used `python3 -I`, an explicit separate cwd, mpmath1.3.0 and SymPy1.14.0. The default generator was unchanged. The refinement wrapper changes only `iv.dps=90` and `Q=48`, retaining identical generator bytes. Foreign code was read before execution; no network calls, installers, external executables or pickle loading occur. Runs terminated normally without approaching their360-second limit.

| Run | Interval precision | Gauss order | Runtime | Exact finite sign | Full source return |
|---|---:|---:|---:|---|---|
|default|70 digits|40|57.56s|Both parity blocks PASS|PASS|
|refinement|90 digits|48|67.09s|Both parity blocks PASS|PASS|

Both rational payloads are byte-identical, SHA256:

`8b7fb1900093eb47e663ae352e0b52a2ad18043bd5d654e0f1a71aacec5ddcc0`

The source Bareiss algorithm checked every exact division and all positive leading minors. A separately written checker read only the dyadic payload, formed `R=G−2^-29 I` over the rationals, and called SymPy rational LDL independently of the generator. Every diagonal was positive and `L D L^T−R` was exactly the zero matrix in both blocks. Independent integer determinants reproduced both announced hashes.

|Block|Dimension|Minimum rational LDL pivot (summary, **not** eigenvalue bound)|Integer determinant SHA256|
|---|---:|---:|---|
|even|31|0.00309751051730317091009157|d1fd3e6a268b545d0c672d6bc64ac84c9be08ec6b6368c4a74d848319f998967|
|odd|30|0.01940871944159910099675748|5895d0a4661b117dadfbd979a6bfd4e474d8c21d1b29b368486e47d53c84362d|

Thus the finite conclusion is `G≥2^-29 I`; the pivot sizes are not substituted for that spectral lower bound.

## Analytic audit, with exact source line references

Line numbers refer to the pinned `SOURCE.md` snapshot.

|Item|Verdict|Reason checked|
|Source, both poles and prime endpoint, lines93–109, (1)|CONFIRMED|Fourier convention has Plancherel1/(2π). The prime2 multiplier gives−c2 Q_f(log2); prime3 and higher overlaps vanish by support, including the length-equality endpoint in L2. The pole pair is the difference of squared cosh/sinh loads for complex f. The negative odd pole is present. Reflection eliminates mixed parity terms.|
|Exterior positivity, lines117–139, (2)–(4)|CONFIRMED|The absolutely convergent digamma difference series is nondecreasing termwise in |t|. The enclosure of a(40)−2c2 exceeds4/5. Plancherel then gives the exact full-form/comparison-operator split and nonnegative entire exterior remainder on the finite-energy domain.|
|Legendre normalization, lines145–164, (5)|CONFIRMED|Physical basis is orthonormal in Lebesgue L2. Fourier columns and pole loads carry precisely √(L(2n+1)) and √(2L(2n+1)); even/odd dimensions31/30 and odd pole sign agree. Independent direct-integral controls are included, not used as a proof of the estimates.|
|Infinite projection tail, lines168–193, (6)–(7)|CONFIRMED|Weighted consecutive majorant ratio is X²/[(2n+1)(2n+3)], decreasing for n≥61. It bounds all omitted modes, not merely one omitted eigenvalue. Rank-one difference is bounded by2||Pe||·||Qe||+||Qe||². Both pole tails are retained; each full pole vector has norm<2, making the stated8√τ_p+2τ_p conservative.|
|Operator Gauss remainder, lines197–207, (8)|CONFIRMED|ρ=2 gives |Im t|≤3/16 and Re(1/4±it/2)>1/8. The convergent digamma expansion yields the explicit bound1+8+22π²/6<45.189<53. Bessel's inequality bounds the complex evaluation vector without a dimension factor. Independent primitive intervals give an integrand bound<64.961, hence M512 is safe. Banach/operator-valued Chebyshev truncation at degree2Q−1, followed by positive Gauss exactness, gives8TM/(π·2^(2Q)). No entrywise-to-operator factor is missing.|
|Source-to-dyadic return, lines211–219|CONFIRMED|Exact rational sign changes in disjoint brackets isolate all Gauss roots; interval recurrence encloses weights. Each scalar/column quantization is checked against the source interval. Vector rounding≤8·2^-90, scalar magnitude<4 and vector norm<2 give per-node operator error<1000·2^-90. The pole term and final dyadic matrix rounding are separately charged.|
|Exact finite signs, lines221–236, (9)|CONFIRMED|Bareiss and the independent SymPy rational LDL/reconstruction both pass with the announced canonical payload and determinant hashes.|
|Binet remainder, lines289–299, (13)|CONFIRMED|After shifting by64, Re(w)>64 and |Im w|≤Re(w)/2. Hence Re(w²)≥(3/5)|w|²; the finite geometric expansion in Binet gives remainder at most(5/3)|B_(2P)|/(2P·|w|^(2P)), below the source's factor2 bound with64. Real and imaginary components are both enclosed.|
|Bessel seeds, lines301–306|CONFIRMED|The code retains a0 through a120, majorizes the next absolute term and uses the decreasing ratio for subsequent terms. Its denominators2·121·(2n+243) and2·122·(2n+245) have the correct indices. Modified Bessel uses the positive series; backward recurrence is enclosing interval arithmetic.|
|Total operator E, lines240–259, (10)|CONFIRMED|An independently written primitive-IV calculator reconstructs all five budgets and verifies the exact threshold E<2^-40 for both Gauss orders. Agreement of two quadratures alone is not the justification.|
|Exact SOS, lines263–283, (11)–(12)|CONFIRMED|E is a bounded self-adjoint difference already controlled independently. ||E/κ||<2^-10 justifies the binomial functional series and B*B=κI+E. Expanding all displayed squares yields PGP+βQ+E exactly: the two κI terms cancel the two−2κ projection terms. Thus there is no circular square-root positivity assumption.|
|All-node and anchor scope, lines310–329, (14)|CONFIRMED|Step functions have finite logarithmic form energy, and polarization of the exact indicator pullback yields K≥κ·min(s,t) on all finite node sets inside[0,log3]. Translation uses both poles. Reanchoring gives arbitrary short intervals; fixed anchor0 requires the interval containing0. Remote old histories and fixed-anchor kernels on arbitrary distant short intervals are outside the result.|

No first invalid step was found in the audited certificate.

## Independently recomputed error budget

Primitive interval arithmetic at90 digits, importing no generator:

|Contribution|Q40 upper summary|Q48 upper summary|
|---|---:|---:|
|Infinite band-projection tail|1.7377470e−18|same|
|Both pole tails|9.727552e−136|same|
|Analytic Gauss remainder|4.313904e−20|6.582495e−25|
|Scalar rounding|2.585748e−21|3.102736e−21|
|Matrix rounding|5.045802e−23|same|
|Total|**<1.783523e−18**|**<1.740902e−18**|

Both are below `2^-40≈9.094947e−13`, itself below `κ=2^-30`. The omitted Fourier-column squared norm is<6.623209e−41 and the pole squared tail<1.478520e−272. Decimal summaries are not substituted for the interval comparisons executed in code.

The doubled-prime control reproduces the enclosure
`[-0.2399107181322211385648193, −0.2394552573782343686037948]`, entirely below−23/100. Independent direct physical-form evaluation gives approximately−0.23945548474850738301515. The same normalization gives `W[1_(0,L)]=−2g(L)` with discrepancy5.3e−82 in an80-digit diagnostic. These checks expose the source dependence; they do not turn the local result into a global fake-world discriminator.

## What this closes and what it does not

The audited conclusion is `W[f]≥2^-30||f||²` for every complex finite-form-energy input supported on an interval of length≤log3. Its all-node kernel consequence is not a finite-grid extrapolation: it follows from this full supported-space estimate and the exact pullback.

The lower comparison matrix depends on the nodes and may be arbitrarily ill-conditioned as nodes coalesce; no node-independent Euclidean eigenvalue floor is asserted. Positive guarded Schur complements follow only when the **entire** old-plus-new configuration remains within the certified anchored/reanchored interval. The audit does not extend an arbitrary remote past, prove global(P), or prove RH.

Literature priority is separate from validity: the earlier LIT quickcheck reproduced stronger support±4/5 positivity for both parities from the external one-stroke implementation. This local log3 certificate is a source-matched implementation/audit and explicit SOS presentation; no novelty in the existence of short-window positivity is claimed.

Artifacts: `source_provenance.json`, the two run directories, `independent_exact_ldl.py/.json`, `independent_budget.py/.json`, `normalization_controls.py/.json`, and `SHA256SUMS`. No repository commit was made by this auditor.
