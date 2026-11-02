# Whole-history uniform-grid innovation scan

DIAGNOSTIC_NEVER_A_PROOF. CHALLENGER / NOT_RH. No route-state modification.

The source is g=-Psi from the pinned prediction verdict. All arithmetic integers up to exp(6) are retained (proper powers for zeta; every nonzero logarithmic-derivative coefficient for DH). The planted world adds 4 Re[(cos(wt)-1)/w^2], w=2pi/log2+i/4. No zero census or RH premise enters source evaluation.

Set r_0=-2g(h), r_j=2g(jh)-g((j-1)h)-g((j+1)h). A unit-triangular change from points to increments preserves every prefix Schur defect. Signed Levinson recursion costs O(n^2) and retains negative pivots. The structural t=0 row is omitted. Every tested nonstructural pivot clears the explicit precision guard; no pseudoinverse cutoff is used. After the first negative pivot, later values are algebraic signed Schur defects, not prediction variances or minima of an indefinite quadratic form.

| h | zeta first negative through6 | DH first negative | planted first negative | DH negative index at6 | planted negative index at6 |
|---|---|---:|---:|---:|---:|
|1/32|none|5.9375|1.4375|1|2|
|1/64|none|4.296875|1.203125|2|2|
|1/128|none|3.78125|1.046875|8|2|
|1/256|none|3.6875|1.03125|16|2|

The historical mesh64/128 DH onsets are reproduced exactly. All zeta prefixes are positive and nonincreasing:192,384,768,1536 respective prefixes to6. This monotonicity follows generically for positive stationary histories and is not an additional source-specific sign law. At t=6 every tested world's final signed pivot is positive despite the accumulated DH/planted negative index.

| h | zeta sigma^2(6) | zeta sigma^2(6)/(2Psi(h)) |
|---|---:|---:|
|1/32|0.01264925250538888|0.1922617224807437|
|1/64|0.008229081504653196|0.1900524625300976|
|1/128|0.005152316268250920|0.1911246157275300|
|1/256|0.003484294300768413|0.2156143162675369|

The registered Mythos exponential parametrization fails the stated finite tests. On [1,6], slopes of log(sigma^2) are -0.1624698,-0.2170533,-0.2706282,-0.2856816; R^2=.96497,.96677,.96381,.98544. The across-four-mesh slope spread is50.53% of the median magnitude. The last two whole-interval slopes are closer, about5.4% apart, so this does not refute an eventual limiting slope. The within-grid curvature gates still fail. On the finest grid the [1,3] slope is-.3044275 and [3,6] slope-.2288230. Detailed fixed-window fits and gates are in fits.csv and analysis.json; no fitting-window optimization was performed.

Validation: all three mesh256 sequences were rerun at160dps against100dps. Every cumulative negative index agrees. Maximum relative pivot changes are2.11e-97(zeta),5.84e-94(DH),4.93e-95(planted). Source values were independently compared against the physical archimedean integral (including its infinite tail), prime sum and both-pole expression, with maximum absolute discrepancy2.43e-100. At each of the12primary cells, direct dense point-kernel Schur solves for prefixes8,16,32 match the independent increment recursion to absolute error below8.80e-101. Every first negative pivot has a stored chronological residual vector and an independently evaluated direct Toeplitz quadratic form; maximum relative discrepancy6.23e-96 at100dps. These are floating diagnostics, not interval certificates.

Reproduce: python3 scan.py --mesh 32 64 128 256 --world zeta dh plant --dps 100; python3 scan.py --mesh 256 --world zeta dh plant --dps 160; python3 analyze.py. Only mpmath is needed. CSV retains every pivot/reflection/negative index. JSON retains g, r, direct checks and residual coefficients at t=1,3,6 plus the first negative prefix; other residuals are exactly reproducible by applying the saved reflections. All source and output precision is explicit.

HYPOTHESIS: one mesh-independent exponential describes zeta innovations over1<=t<=6. Evidence: all registered finite fit gates fail; kill this finite parametrization. What could revive it: a separately preregistered larger-precision/finer-mesh limiting regime with controlled curvature and unchanged windows. Handoff to Proshka: the exact stationary recursion v_n=v_(n-1)(1-a_n^2) explains monotonicity conditional on prefix positivity, but does not supply the source sign. Any proposed scale law must track every prefix and survive the planted-world comparison; final normalized magnitudes alone do not distinguish the worlds.
