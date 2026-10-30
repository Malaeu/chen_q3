# OpenAI math catalogue scan: possible suppliers for Q3 ropes

Sources (local copies, commit 7ef5c0cc, 2026-10-26, nothing fetched):
- C = /tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/9c6b42f5-8b18-42b2-a8ce-e07d053d1517/scratchpad/oai_CONTENTS.md (line numbers below refer to it)
- Y = /tmp/claude-1000/-mnt-hdd01-Soft-GitHub-chen-q3-rh-clean/9c6b42f5-8b18-42b2-a8ce-e07d053d1517/scratchpad/oai_formalization.yaml

Quotes are verbatim from C (HTML/LaTeX markup left as in the file). Only abstracts and family summaries were read. No PDF was read, so every "what is missing" line is judged from the abstract alone and is unverified against the paper.

Global Lean status (Y lines 987-989 and 1827-1829), applies to every family below:
- `status: scope: "Partial progress."`
- `review: status: unchecked`
The per-family Lean status is whatever Y lists under `main_results` (a comparator_config, declaration and file). Families with a "([Lean](lean/docs/NNN.md))" link in C but no `main_results` entry in Y are marked "no Y entry". The lean/docs files are not in the local copy.

Summary of the catalogue: 721 manuscripts in 373 families. It is almost entirely algebraic geometry, topology, combinatorics, operator algebras, PDE and complexity. Exactly one family (#003) touches zeta zeros. There is nothing on prolate or spheroidal functions, Sturm-Liouville asymptotics, Toeplitz/Hankel matrices, total positivity, Perron-Frobenius for kernels, Laguerre-Polya, de Bruijn-Newman, Jensen polynomials, Hermite-Biehler or de Branges, large values, moments of zeta, or zero-density estimates.

---------------------------------------------------------------------

## T1 (G1: simplicity/parity of ground state, uniform gap, odd-sector coercivity)

No DIRECT or PARTIAL candidate. Four ANALOGY candidates, none of which supplies a lemma for a finite real-symmetric Toeplitz-plus-Hankel matrix.

Search terms used (rg -i over C, counts in parentheses): Toeplitz (0), Hankel (0), total positiv / totally positive / totally nonneg (0 for the mechanism; the only hits are "totally real", "totally ordered"), Perron (0), Krein (0), Gantmacher (0), sign-regular (0), oscillat (2, both on oscillation of infinity-harmonic functions, irrelevant), Courant (0), rearrangement (1, GR mass rearrangement, irrelevant), simple eigenvalue / simplicity of (0), ground state (12, all many-body physics), spectral gap (10), nodal (3), eigenvalue/eigenfunction/eigenvector (about 25 hits, all read), Hermitian/symmetric matrix, Gram, Hilbert matrix, Cauchy matrix, Vandermonde, integral operator, Fredholm, Szego, circulant, reproducing kernel, Poincare inequality, Cheeger, Krahn.

### T1-a. Family #269, "Uniform Laughlin gap and stability under bounded scalar disorder" (C 6781; paper C 6799)
- Quote (C 6781): "The unique ground state remains uniformly gapped under sufficiently weak bounded real scalar one-body potentials projected to the lowest Landau level."
- Quote (C 6799): "the gap above the Laughlin state at filling 1/3 on the round sphere is at least 1/25 for all sufficiently large systems."
- Lean (Y): `declaration: OAI.Laughlin.mainTarget_proved`, file `OAI/Analysis/Laughlin/Main.lean`. Global status: partial, review unchecked.
- Rating: ANALOGY.
- Mapping: it gives a method template, namely a gap obtained from an operator inequality H^2 >= gamma H on a Fock space (C 6799 also says "H_Q^2 \ge \gamma H_Q"), together with a uniform lower bound for the gap in the size parameter, and gap-plus-simple-ground-state stability under bounded perturbations. Missing: the operator is a many-body projector Hamiltonian, not a Toeplitz-plus-Hankel Weil matrix. There is no parity or odd-sector statement, and no explicit rate delta_m for a matrix family.

### T1-b. Family #268, "The spin-one Haldane gap" (C 6756; paper C 6774)
- Quote (C 6774): "We prove a uniform spectral gap for odd open spin-one antiferromagnetic Heisenberg chains with the same fixed magnetic field at both endpoints."
- Quote (C 6756): "the spectral gap stays uniformly positive as the chain grows."
- Lean (Y): no entry (no `main_results` declaration found by rg for Haldane). The catalogue shows no Lean link for #268.
- Rating: ANALOGY.
- Mapping: it shows a uniform gap in a growing family with an explicit constant (C 6774: gap greater than log(10)/392). Missing: it is a quantum spin chain, a completely different matrix class, with no sign-regularity or Sturm structure. It is not transferable.

### T1-c. Family #369, "The hot spots conjecture for simply connected planar domains" (C 8938; paper C 8947)
- Quote (C 8938): "each nonzero eigenfunction for the first positive Neumann eigenvalue has no interior critical point, so all global extrema lie on the boundary. Eigenvalue multiplicity is allowed."
- Lean (Y): no `main_results` entry found. The catalogue shows a link to lean/docs/369.md, not available locally.
- Rating: ANALOGY.
- Mapping: it is the same flavour as "the first non-trivial (odd or Neumann) eigenfunction has controlled critical-point/extremum structure". Missing: it concerns a 2D smooth simply connected domain with the Laplacian. It is not a 1D matrix or integral operator, and it says nothing about the ground state or parity.

### T1-d. Family #350, "Yau's nodal bounds: surfaces and higher dimensions" (C 8508; paper C 8517)
- Quote (C 8517): "a nonzero real Laplace eigenfunction with eigenvalue λ > 0 on a fixed smooth closed connected Riemannian surface has nodal length at most C\sqrt\lambda."
- Lean (Y): only counterexamples listed, `OAI.YauCounterexamples.sphere_three`, `OAI.YauCounterexamples.sphere_two_torus_two` and `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`. No Lean statement of the surface upper bound itself in Y.
- Rating: ANALOGY (weak).
- Mapping: nodal-set size of Laplace eigenfunctions, the Courant-type theme. Missing: it is an upper bound on nodal measure on Riemannian surfaces, and gives no sign-change count for finite matrices or Sturm-type zero counting.

Considered and rejected for T1: #265 area law (needs a uniform gap as hypothesis, does not prove one), #178 Ramanujan graphs (adjacency spectrum of regular graphs), #179 circulant Hadamard (circulant is the only Toeplitz-like word; the theorem is about orders of +-1 matrices), #144 simple Lebesgue spectrum for diffeomorphisms, #261 Anderson model, #219 GOE universality, #091 log-Brunn-Minkowski (log-concavity, not kernel positivity).

---------------------------------------------------------------------

## T2 (prolate / Sturm-Liouville asymptotics)

One ANALOGY candidate, weak. Otherwise "no candidate".

Search terms used: prolate (0), spheroidal (0), Sturm (0), Liouville (15, all Liouville quantum gravity / Liouville function / Liouville measure), Slepian (0), time-band / band-limit / bandlimit (0), Meixner (0), Paley (0), exponential type (0), Bessel, Legendre, Hermite, Chebyshev, orthogonal poly, special function, uniform asymptotic, WKB, turning point (all 0 outside #262's sech^2 solitons), uncertainty (0), commuting differential operator (0), Cohn-Elkies / Delsarte (read #090, planar sphere-packing Fourier certificate; not about prolate functions).

### T2-a. Family #262, "Sharp finite-matrix Lieb-Thirring inequalities and all equality cases" (C 6552)
- Quote (C 6552): "the optimal constant is the scalar one-bound-state value, independent of matrix size. All equality cases are direct sums, in one constant unitary basis, of scalar sech2 solitons"
- Lean (Y): `declaration: OAI.SharpLiebThirring.sharp_lieb_thirring`, file `OAI/Analysis/LiebThirring/Main.lean`.
- Rating: ANALOGY (weak).
- Mapping: it is one-dimensional Schrödinger (Sturm-Liouville) operators with Hermitian matrix potentials, bounds on sums of negative eigenvalue moments, with sharp constants and extremisers. Missing: no eigenfunction asymptotics, no sup-norm bounds, no prolate/band-limited structure, and the quantity bounded is a moment sum of negative eigenvalues, which is not our objects (a Weil matrix has a positive-definite-form ground energy). Almost certainly not useful.

---------------------------------------------------------------------

## T3 (Theta-moving inputs)

The only relevant family is #003. The catalogue contains no zero-density estimate N(sigma,T), no large-values estimate, no moment of zeta/L-functions, and no Weil-positivity, de Branges or Hermite-Biehler statement. The zero-free half-plane is the only Theta-type statement. Three DIRECT (all within #003), two ANALOGY (consumers).

Search terms used: zeta (4 hits, all read), zero-density / zero density / zero-free / zero free (6), Dirichlet polynomial, large values, mean value, Montgomery, Vaughan, Hilbert inequality, large sieve (0), Bombieri, Vinogradov, Hoheisel, Linnik, Huxley, exponent pair, van der Corput, subconvex, Weyl sum (0), Siegel zero (hits only in #003), Selberg (0), Lindelof (0), pair correlation (0), Weil positivity / explicit formula (the 13 "Weil" hits are Weil group / Weil divisor / Weil classes, none about the explicit formula), Connes / Consani / Moscovici (7 hits, all Baum-Connes or the bicentralizer conjecture, nothing about the Weil form or CCM), Hecke L (only #003, #029, #142).

### T3-a. Family #003, main paper "The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re s > 7/8" (C 66, 75)
- Quote (C 66): "Proves that every Dirichlet <i>L</i>-function, including $`\zeta(s)`$, is zero-free in $`\Re s\gt 7/8`$, resolving the quasi-Riemann hypothesis."
- Quote (C 75): "all finite-order Hecke <i>L</i>-functions over $`\mathbb Q(\sqrt{-3})`$ and all Dirichlet <i>L</i>-functions are zero-free in the half-plane $`\Re s\gt 7/8`$"
- Lean (Y 1568-1570, 1200-1201, 1308-1309): `OAI.riemannZeta_ne_zero_of_seven_eighths_lt_re` (file `OAI/NumberTheory/DirichletL/Nonvanishing.lean`), `OAI.DirichletCharacter.LFunction_ne_zero_of_seven_eighths_lt_re` (same file), `OAI.SevenEighths.HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re` (file `OAI/NumberTheory/DirichletL/Hecke/Nonvanishing.lean`). Three comparator configs: QuasiRiemannHypothesis, DirichletSevenEighths, HeckeSevenEighths. Review status: unchecked.
- Rating: DIRECT.
- Stated Theta: Theta <= 7/8 (sup Re rho <= 7/8, hence Theta - 1/2 <= 3/8). For every Dirichlet L-function, with no dependence on the conductor in the statement.
- If your two ropes are exactly "floor exponent = Theta - 1/2" and "tracking rate = (Theta - 1/2)/2" (your statement, not checked by me), this gives floor exponent <= 3/8 and tracking rate <= 3/16. That is a real but modest loosening: the ropes remain graded by Theta, now from above by 3/8 and 3/16.
- Missing: it is a zero-free half-plane only. The explicit constant in the zero-free statement and the error-term form psi(x) = x + O(x^{7/8+eps}) are not in the abstract, and a version for the finite Weil form on [1/sqrt(lambda), sqrt(lambda)] would have to be derived from it. Your probe qrh78 already covers the 7/8 threshold; this family is its source theorem.

### T3-b. Family #003, alternate paper "The Quasi-Riemann Hypothesis (alternate 11/12 proof)" (C 84)
- Quote (C 84): "every Dirichlet <i>L</i>-function, including Riemann's zeta function, has no zeros in the half-plane $`\mathop{\mathrm{Re}}\nolimits s\gt 11/12`$."
- Lean (Y): none separate (the Lean declarations above are for 7/8).
- Rating: DIRECT, but weaker than T3-a.
- Stated Theta: Theta <= 11/12 (Theta - 1/2 <= 5/12). Note 11/12 > 7/8, so this region is smaller than T3-a's and is implied by it. Its only value is as a second, independent proof route (family summary C 66: "A companion gives a different proof of the zero-free half-plane $`\Re s\gt 11/12`$").
- Missing: nothing beyond T3-a; it adds no strength.

### T3-c. Family #003, "Uniform exclusion of Landau-Siegel zeros" (C 91-93)
- Quote (C 93): "There is an absolute constant <i>c</i> &gt; 0 such that every real zero $`\beta\in(0,1)`$ of every primitive nonprincipal real Dirichlet <i>L</i>-function of conductor <i>q</i> ≥ 3 satisfies $`(1-\beta)\log q\ge c`$."
- Lean (Y): `OAI.SiegelZeros.WeightedTorusJets.exists_absolute_real_zero_gap`, file `OAI/NumberTheory/SiegelZeros/Conclusions/Theorem.lean`.
- Rating: DIRECT for real zeros only; it does not move Theta (it is subsumed in the region where Theta <= 7/8 for all zeros).
- Missing: it controls only real zeros of real characters. Irrelevant to Theta = sup Re rho for zeta unless a Siegel-zero-type issue enters via the L-function side of your construction.

### T3-d. Family #182, "Power savings for intersective polynomial differences and prime arguments" (C 4220; paper C 4238)
- Quote (C 4238): "The proof uses the companion zero-free half-plane theorem for Dirichlet L-functions to obtain the required prime-distribution estimates."
- Lean (Y): the catalogue links lean/docs/182.md; Y shows only `OAI.PowerSaving.transform_main` and `OAI.PowerSaving.convolution_main` (Fourier-transform power-saving, file `OAI/Computability/FourierTransform/Main.lean`), which look unrelated to #182. Treat as no Y entry for #182.
- Rating: ANALOGY.
- Mapping: a consumer showing how the 7/8 region is turned into prime-distribution (psi/theta) estimates inside a larger argument. This is the same mechanism that grades your ropes (prime sums with error exponent Theta). Missing: a stated explicit prime-sum bound and its constants (not in the abstract; PDF would need reading). It supplies no new Theta information.

### T3-e. Family #029, "Primitive roots for every admissible integer base" (C 698; companion paper C 716)
- Quote (C 716): "The result assumes four explicitly stated analytic and sieve inputs from the companion paper on primitive roots for admissible integer bases."
- Quote (C 3445, from family #142): "The proof uses the uniform Hecke zero-free theorem from the companion paper *Primitive roots for every admissible integer base*."
- Lean (Y): no entry found.
- Rating: ANALOGY.
- Mapping: #029 carries a "uniform Hecke zero-free theorem", which is evidently the 7/8 input in the form needed for prime-distribution in arithmetic progressions/Hecke characters. Same consumer role as T3-d; "uniform" may mean uniform in the conductor. That is the part that would matter if your objects ever need uniformity in a modulus. Missing: it is not in the abstracts (only referenced); the PDF would need reading to see what exactly is "uniform".

---------------------------------------------------------------------

## T4 (Hurwitz / assembly side: locally uniform limits of real-rooted functions, Laguerre-Polya, de Bruijn-Newman, PF sequences, Jensen polynomials)

No candidate.

Search terms used: Laguerre, Polya, Laguerre-Polya, real-rooted, real rooted, only real zeros, real zeros, hyperbolic polynomial, stable polynomial, Lee-Yang, partition function zeros, Newman (7 hits: Kerr-Newman and Gupta-Newman-Rabinovich-Sinclair only), de Bruijn (0), Jensen (0), Pólya frequency (0), interlacing (0), Gauss-Lucas, Sendov, Smale, Schur, Mahler (hits: only geometric Mahler conjecture #087, convex bodies), Heilmann-Lieb, matching polynomial, Lorentzian, Hodge-Riemann, multiaffine, Kadison-Singer / Marcus-Spielman-Srivastava, "zeros of", "roots of" (only algebraic-geometric or polynomial-root-finding hits, e.g. #142, nothing about location of roots of real entire functions), Hurwitz (only Hurwitz-type statements in algebraic geometry/combinatorics, none on locally uniform limits), Hermite-Biehler, de Branges (0).

---------------------------------------------------------------------

## T5 (new 2026-10-26 families)

### #079, "Local smoothing for the Euclidean wave equation" (C 1963; paper C 1972)
- Quote (C 1963): "The wave estimate yields the Bochner–Riesz conjecture and, for $`2\le p\lt\infty`$, maximal bounds for these means and sharp bounds for Stein’s square function."
- Quote (C 1963): "The Kakeya and Nikodym maximal conjectures follow. In particular, every Euclidean Kakeya set has full Hausdorff dimension."
- Lean (Y): declarations `OAI.Analysis.Fourier.LocalSmoothing.Comparator.euclidean_local_smoothing`, `...bochner_riesz`, `...spherical_restriction`, `...kakeya_maximal`, `...kakeya`, `...stein_square`, all in `OAI/Analysis/Fourier/LocalSmoothing/Comparator.lean`.
- Verdict: touches none of T1-T4. All statements are on R^n (wave equation, Bochner-Riesz multipliers, restriction to sphere/paraboloid/cone, Kakeya). There is no prolate/Sturm-Liouville asymptotics (T2), no zeta or L-function content (T3), no eigenvector or Toeplitz structure (T1), no real-rooted limits (T4).
- Side note, from my own background knowledge and NOT stated in the catalogue (unverified): Kakeya/restriction-type bounds are known to feed into large-value estimates for exponential sums and Dirichlet polynomials, which is a T3 mechanism. The catalogue does not state any such application, so nothing here can be used without a separate derivation.

### #378, "Disproof of the Exponential Time Hypothesis" (C 9154; paper C 9163)
- Quote (C 9154): "a deterministic algorithm counts the satisfying assignments of a $`k`$-CNF with $`n`$ variables and $`m`$ clauses in time $`(n+m)^{O_k(1)}2^{n/(\log n)^{1/2+o(1)}}`$."
- Lean (Y): `OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.exact_count_and_sat`, file `OAI/Algorithms/SubexponentialSAT/SqrtLogSpace/Final.lean`.
- Verdict: touches none of T1-T4. It is about SAT-counting complexity. Its only conceivable use for you is computational (if some finite check of yours reduces to k-CNF counting), which is not a supplier of any rope.

---------------------------------------------------------------------

## Counts of candidates per target and fit level

| Target | DIRECT | PARTIAL | ANALOGY | Total |
|---|---|---|---|---|
| T1 | 0 | 0 | 4 (#269, #268, #369, #350) | 4 |
| T2 | 0 | 0 | 1 (#262) | 1 |
| T3 | 3 (#003 x3: 7/8, 11/12, Landau-Siegel) | 0 | 2 (#182, #029) | 5 |
| T4 | 0 | 0 | 0 | 0 |
| T5 | n/a: #079 and #378 touch none of T1-T4 | | | 0 |
| All | 3 | 0 | 7 | 10 |

## Top 5, ranked by likely usefulness

1. #003 main paper (7/8): the only family that moves Theta, and the only one with Lean declarations for zeta, Dirichlet and Hecke L-functions (still "Partial progress", review unchecked). Theta <= 7/8 means floor exponent <= 3/8 and tracking rate <= 3/16 under your stated grading. The ropes stay Theta-graded; this only improves the bound.
2. #003 alternate 11/12 paper: weaker than #1 (11/12 > 7/8), so useful only as an independent second proof to cross-check the mechanism of #1. It is not an improvement.
3. #182 (prime arguments): a worked consumer of the 7/8 theorem for prime-distribution estimates. Reading the PDF would show the exact explicit-formula-to-psi step, the same step that grades your ropes.
4. #029 / #142 ("uniform Hecke zero-free theorem"): shows what uniformity in the conductor the 7/8 theorem comes with. It matters only if uniformity in a modulus is ever needed.
5. #269 (Laughlin gap): the only transferable method found for T1 (gap from an operator inequality H^2 >= gamma H with an explicit constant 1/25, plus stability of a unique ground state under bounded perturbations). It is still an analogy with no direct transfer to a Toeplitz-plus-Hankel matrix.

Honest summary: nothing in the catalogue supplies G1 (T1), prolate/Sturm-Liouville asymptotics (T2) or the assembly side (T4). The non-Theta-graded ropes still have to come from classical mathematics. The catalogue's only contribution to the project is the 7/8 zero-free half-plane, and even that only changes the Theta-bound, not the grading. Items 3-5 are low-yield.
