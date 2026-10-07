# OpenAI math: RH-first alias hunt, 2026-10-07

## Obstruction and scope

Q3 needs a one-sided estimate on the actual full arithmetic source, not merely cancellation in a related family. On the original CCM cells m=N, SP asks: for every eta>0, eventually lambda_min(K_m)>=-C_eta*m^eta. An off-critical zero with real part 1/2+delta forces an upper bound -c*m^delta/(log m)^(2delta); SP would contradict it. Source: docs/Codex/PAPER_CHAIN.md and NEXT.md, full CCM negative-bottom route. Both SP and RH remain OPEN.

Scalar equivalent working obstruction: with the full prime-power prehistory retained, the current exact joint pairing returns W(x)=integral_1^x v^(-3/2)(1+log(x/v)/2)(psi(v)-v)dv, with coefficient exactly 1. No sign was gained. Negative controls: synthetic positive arrivals with strong count and summable convexity loss still allow both signs; carrier-wide lower-frame claims fail on cutoff/Fourier witnesses. Thus positivity, upper moments, or cancellation after changing the kernel cannot be imported silently.

Search rewrites, UNVERIFIED: (i) preserve one arithmetic probe while cancelling its local Euler obstruction; (ii) realize the actual signed remainder as a centered divisibility-graph bilinear form with uniform endpoint control.

Owner specifically requested this new external corpus, so it was fetched directly. Official release: https://openai.com/index/sharing-ai-progress-in-mathematics/ . Snapshot openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a, shallow source clone /tmp/openai-math. The catalogue has 722 manuscripts in 372 families. Whole-corpus text screening covered 722 manuscript directories and 7729 TeX files; this is discovery coverage, NOT 722 independently audited proofs. Dictionaries: arithmetic cancellation/Type II; Gram/Schur/sampling/spectral gap; positivity/reflection/Turan/de Branges. All 10 reasoning summaries were read by a delegated researcher. Source URLs and exact fetched-file hashes are in sources.json.

## RH first

The September 30 manuscript states zero-freeness for Re(s)>7/8, for zeta, all Dirichlet L-functions, and finite-order Hecke characters over Q(sqrt(-3)). It explicitly does not prove RH. Quote (paper.tex lines 106–119): “The theorem does not establish the Riemann hypothesis or its generalized versions”. The October 5 alternative proves the weaker claimed endpoint 11/12. These leave the strip 1/2<Re(s)<=7/8 unresolved (and do not exclude the 7/8 boundary).

Static Lean checks found actual solution wrappers, not just a catalogue entry: lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean delegates to ProbeFinalAssemblyUnconditional; Hecke/Nonvanishing.lean supplies the Hecke wrapper. lean/docs/003.md confirms scope. ComparatorChallenges/QuasiRiemannHypothesis.lean contains the expected challenge sorry; it is not the mapped solution. No local Lean build or axiom audit was run, so this report does not claim independent kernel verification. The release itself distinguishes verification stages.

## Candidate mechanisms and exact missing maps

### A. Same-probe prime compensation — highest priority partial analogue

Source qrh78, Proposition “Continuation from a common signal”, lines 400–501; compensated finite probe lines 6857–6916; local Euler calculation 8679–8729; low bound 8564–8648; endpoint arithmetic 15994–16071. Independently reread the continuation assumptions and compensation definition.

The probe uses complete cubic-theta indices c*n^3, target characters on the whole product, disjoint prime slots and inclusion–exclusion of marked versus rescaled terms. The undesired scalar Euler contribution cancels before estimating; a sextic-character factor survives. Low side is Z^(3/16+epsilon); high side uses two polynomial witnesses, moment inductions and sextic large sieve. Both describe the SAME probe. Target-independent positive exponent margins allow continuation of 1/L across a hypothetical rightmost zero. The reported endpoint margin is at least 49/440640, before loss allocation.

Map: Z is the paper's scale, NOT automatically Q3's m; the finite probe is NOT K_m or scalar W. A putative transfer must preserve the Q3 full source, exhibit both exact transformed expressions and bound every correction. PROVED here: source identity and assumptions located; OPEN: Q3 map, family-wide moment bounds and a route from 7/8 to 1/2. Full paper not independently reproved. The synthetic-arrival control lacks Euler characters and cannot satisfy these inputs; thus the mechanism is genuinely arithmetic rather than generic convexity.

### B. Repeated signal through p^6 rows — worked source extraction

Source qrh1112, Proposition thm:ms lines 679–689 and extraction 694–724. Short quote: “no zeros in the half-plane”. For primary prime ideals, the sixth-power row character becomes the indicator p does not divide n. With H=D^(1+vartheta), Y=H^(1/6), about Y/log Y rows carry the same Mobius sum A_1(D), each with error O(D/Y). Averaging the stated mean-square estimate yields

|A_1(D)|^2 << D^(2+vartheta+epsilon)/Y + D^2/Y^2
= D^(11/6+5vartheta/6+epsilon)+D^(5/3-vartheta/3).

The exponent arithmetic and row extraction were checked; the full mean-square theorem was not reproved. As vartheta tends to zero this gives exponent 11/12+epsilon. Useful operation: amplify ONE desired source by many almost identical rows, paying exact nonunit errors. Missing Q3 input: construct such rows without erasing the actual exceptional subspace or source weights. This is a partial analogue, not a lower sampling theorem for our K_m.

### C. Center before taking absolute values — arithmetic operator candidate

Source graph, Proposition prop:graph-estimate lines 86–105. Quote: “All graph parameters are fixed when X tends to infinity.” Fixed h,tau,C0,T; uniform bounded coefficients a_d and vertex sequences F,G, but the kernel g_d MUST be the prescribed core-divisibility/centered-prime kernel. High singular-value moments, forbidden-path deletion and finite-cylinder sieve average unexposed prime residues before absolute values. Arbitrary vertex sequences do not mean arbitrary kernels.

Companion correlations theorem gives Liouville fixed-shift cancellation with log-power saving at every scale, but constants may depend on the fixed affine forms; no uniformity for growing coefficients. General nonpretentious multiplicative correlation is qualitative. Map to Q3: an upper bound on an actual signed bilinear remainder could help pay the Schur coupling; it does not create a lower frame bound. OPEN: representation of our growing-scale kernel and quantitative eventwise uniformity. Negative-control Fourier witnesses remain untouched by a graph upper-norm estimate. Do not interchange fixed graph parameters and X->infinity.

### D. Unequal factor allocation pays the Cauchy diagonal

Source dilation, theorem thm:typeii and its proof. Quote: “There is no discrepancy hypothesis on $\\beta$.” For UV~x, both factors between x^b and x^(1-b), bounded alpha,beta, rough-supported alpha, a special marked smooth weight A(u), and mn=2u+1, obtain x*(log x)^(-D) provided ALL actual restricted alpha sums against chi(m)m^(it)/m are <=(log x)^(-B), for intervals I, moduli and frequencies <=(log x)^B.

Needle: split u=e*h with e near U*(log x)^(-K0), slightly smaller than m. Cauchy in (e,n) then pays the diagonal with E*V~x*(log x)^(-K0); all marked group factors and the mandatory long rough factor stay in h. Splitting costs must be independent of K0. Map to Q3 Type II: only a candidate for a structured bilinear component. OPEN: actual alpha discrepancy, special A(u), factorization and normalization. Even arbitrary log savings on a power-sized error do NOT imply SP: m^a/(log m)^D exceeds m^eta for every fixed D when eta<a. This simple asymptotic test rules out a direct SP import.

## Ten reasoning summaries: useful pivots, not proof certificates

- Correlations: separate core primes and centered marks; narrative leaves conditional-integration and singleton estimates to be checked against final manuscript.
- Pi irrationality: fix separated denominators before raising auxiliary degree; determinant nonvanishing and uniform geometry remain essential.
- Mahler: off-diagonal precision and oblique orthant examples defeat naive scalar induction; trace bound does not pay determinant slack.
- BasicSDP: choose beta=k^(-2/3) so k*beta^2 tends to zero while k*beta diverges; conditioning and dimension uniformity must survive.
- Arithmetic progressions: summability over dyadic scales; avoid circular truncation/grid parameters and unsupported lower-tail claims.
- Kaplansky: one-sided inverse UT=I before rank contradiction; algebra embedding and spectral transfer must be justified.
- Mezard–Parisi: shift branching to fresh levels and average errors over levels using square-summable martingale increments; freeze the same background.
- Heisenberg: Schur formula gives a conditional first mean, not a full path law or a universal positive Gram input.
- Free factors: recovering generation from edge increments can destroy freeness through new dependence.
- Vlasov–Maxwell: source-label integration by parts still leaves boundary, moving-cutoff and acceleration terms.

These are abridged narratives, often including failed intermediate attempts; an unresolved line in a narrative is not by itself a flaw in the final paper. Literal Singer/needle search in these summaries found only bibliographic Amit Singer. “Needles” here means concrete decisive proof moves.

## Decision and next bounded test

No candidate closes RH, SP, G1/G3, actual Schur positivity or the scalar reserve. Strongest next test: take the exact finite compensation identity of candidate A, compute its local factor on our full prime-power scalar source, and determine whether one surviving term has a new signed estimate from the source's moment theorem. Stop if it merely returns W with coefficient 1, changes the source, or requires the same unproved bound. Alternative B/C/D are retained with explicit missing hypotheses, not promoted to active proofs. This is a new source-driven attempt after Q10's recorded STALLED result, not a repetition of its exact algebraic repackaging.

## Cross-domain shortlist (delegated source checks)

Three further partial analogues, all with source paths, pinned URLs and hashes in sources.json:

1. Disk-transfer, analytic.tex 1011–1148 and 1291–1321: cross-label term “is positive only after integration”; fixed signed-charge decomposition, explicit 2x2 Schur coercivity, then a complex-contour perturbation absorbed in a spare real coercivity margin. Q3 map would send charge labels to complex zero rows and its remainder to E0. OPEN: finite fixed sign alphabet, integrated Fourier positivity, and uniform spare margin; none established for Q3. The synthetic signed-source control fails these specific Fourier/sign assumptions.
2. Isotropic entropy, matrix.tex 96–124, 275–286, 348–379: positive inverse-operator covariance Gram plus a commutator square, “without assuming that the Jacobian and the first-chaos matrix commute.” Hypotheses include a smooth uniformly log-concave density and Brenier/Gaussian normalization. Q3 map would identify its noncommuting matrices with our M,Y and the square with the double-commutator defect. OPEN: actual derivative/covariance identity producing that square; mere matrix similarity supplies nothing. Negative controls need not have convex Hessians or covariance identities.
3. Triangular lattice, 06-gaussian-energy-transfer.tex 25–53 and 139–192: real even Schwartz auxiliary with nonnegative Fourier transform gives positive pair energy, then interpolation enforces contact at lattice shells. Q3 map would require an auxiliary representing the actual complex zero rows and signed source correction. OPEN: that representation and all-domain sign; planar density-one points do not represent our exceptional Gram. Generic cutoff witnesses are not excluded by a hypothetical auxiliary.

Rejected direction controls: Parseval upper-frame bounds in BEC and upper moments of projection density cannot supply lower source observability. These cross-domain items are discovery evidence only; no Q3 status changes.
