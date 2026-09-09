# Five Loewner / pole-splitting sources — usage cards

Read date: 2026-09-09. Scope: local literature intake, not theorem admission.

All 33 pages of the five existing extracted texts were read in full, including proofs, appendices and references. The registered PDFs and their survey-directory copies were compared byte for byte: all five pairs match. PDF page counts were checked with `pdfinfo`. This reading used the extracted text, not a fresh visual audit of every formula; symbols vulnerable to text extraction require PDF recheck before verbatim mathematical import. No external search, cited-reference acquisition, numerical rerun, interval certificate, Lean proof, or independent full proof audit was performed.

Status vocabulary: READ_PAPER means the statement and printed argument were read; it does not mean the statement is accepted as a project theorem. OBSERVER_CHECK names a bounded elementary check explicitly described below. RELAY means a result cited by a paper whose original was not read here. These cards close missing-reading-card bookkeeping only. They supply no all-support Weil sign, no RH theorem, no cofinal T-squared bound, and no current radical-trial supplier.

## Source locks

Paths below are relative to `docs/routeB_bus/litreview/`. Registered PDFs are immutable for this reading by their full SHA-256.

| ID | Registered PDF | SHA-256 | Pages / source date |
|---|---|---|---|
| H | `pdfs/de_andrade_silva_10_5281_zenodo_20694588.pdf` | `b6ae873e851b0a4c381c36160f258d2bfdd40bd031f0a66cdf536d6de6692ffe` | 6 / 14 June 2026 |
| P | `pdfs/de_andrade_silva_10_5281_zenodo_20682834.pdf` | `4e0de4780905f407f318f2e9bf6b1aebc7770505f13ef25ab955d761f734676a` | 7 / 13 June 2026 |
| O | `pdfs/de_andrade_silva_10_5281_zenodo_20737111.pdf` | `390e3346a8964bf11e5b9919dfd4494e026673d4889907c747e18d59940ac312` | 5 / 17 June 2026 |
| D | `pdfs/de_andrade_silva_10_5281_zenodo_20710075.pdf` | `008890b6a3a6bb290a0d7ac18994a9974f2ed56ae3c7414f23202a9e68f1527a` | 4 / 15 June 2026 |
| I | `pdfs/1501.01505.pdf` | `338428051ab773c3e316181fc6c9e3787994ae0b35c2a98f37cade64957307b7` | 11 / arXiv:1501.01505v1, 7 January 2015 |

Read texts in `pdfs/survey_2026-09-03_sources/`, respectively: `herglotz_criterion.txt`, `pole_note.txt`, `silva_op_mono.txt`, `silva_loewner.txt`, `inertia_loewner.txt`. Matching PDF basenames there: `herglotz_criterion.pdf`, `pole_note.pdf`, `silva_operator_monotone.pdf`, `silva_loewner.pdf`, `inertia_loewner_1501.01505.pdf`.

## Card H — scalar Herglotz criterion

Bibliography: Breno Andrade, “A scalar Herglotz criterion for the even-simplicity hypothesis in the localized Weil quadratic form”, DOI 10.5281/zenodo.20694588. The author name and date are transcribed from the local publication, not a claim of present affiliation. Local paper, READ_PAPER; publication/review status not independently verified.

### What the paper supplies

- Section 2, page 2, (1)-(2): with C(x)=cosh(x/2), S(x)=sinh(x/2), the pole operator has kernel 2cosh((x-y)/2) and equals 2|C><C|-2|S><S|. Thus A_even=B_e+2|C><C|, A_odd=B_o-2|S><S|. OBSERVER_CHECK: this algebra is the cosh subtraction identity and parity orthogonality.
- Section 3, page 3, (4), Proposition 2: m_e(lambda)=<C,(B_e-lambda)^(-1)C>, m_o(lambda)=<S,(B_o-lambda)^(-1)S>; secular equations outside the respective base spectra are 1+2m_e=0 and 1-2m_o=0. The underlying rank-one eigenvalue identity is elementary. Identifying their smallest roots with sector bottoms needs the overlap/spectral qualifications below.
- Section 4, pages 3-4, Theorem 4, (5)-(6): the paper states even-simplicity is equivalent to mu=lambda_0(A_even)<lambda_0(B_o) and m_o(mu)<1/2, under its standing structural input (3) and claimed sector simplicity.
- The safe conditional core is: if the even bottom is simple and mu<inf spec B_o, then A_odd-mu=(B_o-mu)-2|S><S| has positive lower bound iff 2<S,(B_o-mu)^(-1)S><1. This follows by conjugating with (B_o-mu)^(1/2). It compares parity bottoms; it does not prove the required inequality.

### Hypotheses / first unpaid step

Equation (3), page 2, asserts that B_e has exactly one negative eigenvalue and B_o>0, citing the pole-free Perron result in source P. Perron simplicity/positivity of the ground alone does not imply either inertia claim. Treat (3) as an additional unproved source input for any use here, not an automatic consequence of source P.

Proposition 2's first-gap and below-first-pole root arguments require nonzero spectral overlaps at the relevant endpoints (and avoidance of surviving unperturbed eigenvalues). A resolvent pairing has a pole only at spectral values carrying nonzero vector weight; it need not have poles at every base eigenvalue. Exact control: B=diag(0,1), v=(1,0), perturbation B+2vv*=diag(2,1); the ground 1 is an unchanged base eigenvalue, not the root 2 in the open first gap. This checks the generic missing hypothesis, not a counterexample to the actual arithmetic operator.

### Evidence / use / non-use

Section 5, page 4 reports high-precision finite calculations at c=5,13,53 (150-300 digits, N=80-120); not rerun and not interval-certified by this intake. Sections 6 and Appendix A, pages 4-5 explicitly leave the scalar inequality open. Use the parity rank-one decomposition and qualified scalar interface as a candidate representation. Do not import all-a index one, odd positivity, sector simplicity, the numerical margins, or a lower-sign supplier. Cited references [1]-[7] remain RELAY unless separately read elsewhere.

## Card P — pole-free Perron structure and its limits

Bibliography: Breno Andrade, “The pole term is the only obstruction to Perron structure in the localized Weil quadratic form: a rank-two splitting and a scalar criterion for the bottom eigenvalue”, DOI 10.5281/zenodo.20682834, 13 June 2026. READ_PAPER.

### What the paper supplies

- Section 2, page 2, Proposition 1, (2): away from zero and prime jumps, the smooth kernel is 2cosh(t/2)-exp(-|t|/2)/(1-exp(-2|t|)). The source reports the change of sign t*=0.28119957..., and a classical sign regime 2a<=t*. This numerical root was not recomputed.
- Section 2, page 2, Proposition 2: subtracting the pole term removes exactly 2cosh((x-y)/2), a rank-two kernel with opposite parity signs. Its addition-formula algebra is independently elementary; mapping to the project's normalization still requires its source dictionary.
- Section 3, pages 3-4, Proposition 3, (3): a claimed form identity for the pole-free operator is a positive jump form with kernel J(t)=exp(-|t|/2)/(1-exp(-2|t|)), plus positive finite prime-jump difference squares, plus a lower-bounded potential kappa_a(x). Theorem 1, page 4, claims a simple strictly positive even ground state for every fixed a, by closed-form, irreducibility and semigroup arguments.
- Section 4, page 5, Corollary 1(i): outside the pole-free even spectrum the perturbed even eigenvalues satisfy 1+2<C,(B_e-lambda)^(-1)C>=0. This is the usable algebraic rank-one reduction, not a sign estimate.

### Cautions / first unpaid steps

Theorem 1 is READ_PAPER, not independently proved here. Its form-domain/closedness/Feynman-Kac steps and constants must be audited before theorem import. In particular lower-bounded potential does not alone establish the text's claimed relative form bound zero. The extracted page 3 writes A=1/2(log(2pi)+C0) and also 2A+1=log(2pi)+C0; these cannot both hold as written. Resolve against the PDF and source convention, not by silently choosing a constant.

Corollary 1(ii), page 5 writes strict positive bottom iff 1+2G(0)<=0. Even in the one-negative-base-eigenvalue regime, equality gives a zero eigenvalue, not strict positivity: B=-1 and perturbation +1 has ground 0. Thus the strict/non-strict endpoint must be repaired before use. Corollary 1(iii) and subsequent discussion add constant sign of the resolvent vector to even-simplicity; this is stronger than the definition “simple even ground” and no general necessity follows. Source H's later parity comparison avoids this nodelessness demand.

Section 5, pages 5-6 explicitly leaves its nodal identity unproved and discusses why local oscillation theory does not immediately apply to the nonlocal rank-one perturbation. Theorem 1, even if accepted, concerns the pole-free operator, not positivity of the full Weil form and not the count of its negative eigenvalues.

### Numerical scope / project use

Source reports finite c=53 spectra, grid sign counts, and approximately 1% matching of a crude bad-part norm and good-part gap (Remark 1, page 6). No calculation was rerun. Use the decomposition to preserve the pole term and to explain why positivity-improving reasoning for a different operator does not close our form. No lower-sign or radical-trial rate supplier is furnished. Referenced external semigroup/oscillation theorems were not acquired here.

## Card O — operator-monotone framework

Bibliography: Breno Andrade, “A Loewner/operator-monotone framework for the even-simplicity problem in the Connes–Consani–Moscovici spectral triple”, DOI 10.5281/zenodo.20737111, 17 June 2026. READ_PAPER.

### Exact candidate dictionary

Section 1, page 1, (1): the paper identifies the finite matrix with the Loewner divided differences of an odd symbol psi, including the diagonal derivative. Put h(xi)=psi(sqrt(xi))/sqrt(xi), Phi(xi)=xi h(xi), nodes xi=k^2.

Section 2, pages 1-2, Proposition 1: odd block D-X=2 diag(k)L_h diag(k); positive-index even block D+X=2 L_Phi. The full orthonormal even block is D_s L_Phi(full) D_s on nodes 0,1^2,...,N^2 with D_s=diag(1,sqrt(2),...,sqrt(2)). The constant-mode coupling is sqrt(2)h(k^2) under the defined xi-variable convention (the printed text abbreviates it as h(k)). OBSERVER_CHECK: substituting psi(k)=k h(k^2) into Q[k,l] +/- Q[k,-l] gives these formulas. Congruence preserves inertia, not eigenvalue values or the unweighted Rayleigh quotient.

### Theorem versus arithmetic case

Section 3, page 2, Theorem 1 assumes GLOBAL operator monotonicity of h on (0,infinity) and a finite boundary value h(0). It states lambda_even<=0<=lambda_odd, hence even ordering, not simplicity. The argument imports operator convexity of xi h(xi) and conditional negativity of its Loewner matrices. Those cited results are RELAY in this reading. The finite positive-size sectors are implicit; do not extrapolate to a zero-size odd block.

Remark 1, pages 2-3 explicitly says arithmetic h is outside this global monotone regime. Conjecture 1 on page 3 is the unproved arithmetic parity ordering. Positive semidefiniteness on one prescribed node family is not positivity on all node sets, and neither can be substituted for global operator monotonicity.

Proposition 2, page 3: for M_even=[[h(0),b*],[b,A]], lambda_o<lambda_min(A), define phi(lambda)=h(0)-lambda-b*(A-lambda I)^(-1)b. The reliable inertia identity is lambda_min(M_even)<lambda_o iff phi(lambda_o)<0 on that domain. The printed stronger assertion that phi always has a unique zero below lambda_min(A) needs nonzero coupling to a suitable low eigenspace or an endpoint condition; b=0,h(0)>lambda_min(A) is an elementary counterexample to that generic assertion. The conditional sign equivalence at a specified lambda_o remains the usable part.

### Limits

Section 4, pages 3-4 reports failed specific competitors and finite margins, not a proof that every variational method must fail. Appendix A, page 4 treats a finite Fourier/Neumann boundary dictionary with a rank-one correction, removes the constant mode in the cited continuum construction, and expressly says it does not transport ordering. No bridge to our Legendre projections or cut-radical family is proved. Use the finite algebra only after matching bases and Gram normalization; do not import the generic monotone hypothesis, eigenvalue equality under congruence, arithmetic positivity, or T-squared rate.

## Card D — prime divided differences and parity claim

Bibliography: Breno Andrade, “A Loewner divided-difference formula for the prime contribution in the localized Weil quadratic form, and a parity sign law”, DOI 10.5281/zenodo.20710075, 15 June 2026. READ_PAPER.

### Main representation and its source boundary

Section 1, page 1, (1)-(3): c>=2, L=log c, omega_q=1-log(q)/L; prime powers q<=c weighted by Lambda(q)/sqrt(q); psi_pr(x)=-(1/pi)sum_q Lambda(q)/sqrt(q) sin(2pi x omega_q). P is its Loewner matrix and W_v(beta)=sum_{|n|<=N}v_n exp(i beta n).

Section 2, page 2, Proposition 1, (4) gives a Fourier-symbol integral representation. Before copying (4) for complex vectors, verify its conjugation from the PDF: extracted overbars can be lost. A safe finite identity, rederived from the fundamental theorem of calculus, is

v*Pv = -2 sum_q Lambda(q)/sqrt(q) omega_q integral_0^1 sum_{m,n} conjugate(v_m) v_n cos(2pi omega_q (t m+(1-t)n)) dt.

The integrated matrix is real symmetric, so its quadratic value is real. This finite identity is the retained OBSERVER_CHECK; it is not a lower bound and does not identify a full-source Schur response. It retains every prime power, including the zero endpoint contribution at q=c.

### Printed parity results and cautions

Section 3, page 2, (5)-(6), Lemma 3 states a positive even symbol for the coefficient family C_n=sinh(L/4)/sqrt(L)/(1/4+(2pi n/L)^2), with a uniform omitted-tail bound and N>sinh(L/4)L/(2pi^2). Corollary 4, page 3 claims termwise negative prime contributions for c>2 under this threshold. This is a claim for the specified coefficient convention, not arbitrary even vectors.

There is an unresolved basis-convention issue before identifying those coefficients with the physical C(x)=cosh(x/2) on (-L/2,L/2) in the displayed centered Fourier basis: direct integration gives an extra (-1)^n factor. Explicitly integral_{-L/2}^{L/2} exp(mu x)exp(-2pi i n x/L) dx = 2(-1)^n sinh(mu L/2)/(mu-2pi i n/L). The paper's displayed elementary integral beneath (5) omits it. A translated/rephased basis can move this factor, but then the matrix and symbol conventions must also be transformed. Do not apply the sign law to our physical trial without this repair.

Section 4, page 3, (7)-(9) discusses an odd symbol and signed competition. Under the printed purely imaginary odd coefficients S_n, W_S(beta)=sum S_n exp(i n beta) is REAL and odd for real beta (pair n with -n); the text instead calls it purely imaginary. This is a direct convention warning, not a rounding issue. Recheck the source's conjugations/basis and rederive the odd formula before importing its signs. Equation (9) merely partitions a signed sum into positive and negative terms; it does not prove the required inequality. Its reported per-prime signs at c=53 and Simpson agreement to roughly 0.1%-1% are diagnostics, not certificates, and were not rerun.

### Project use / rejection boundary

Use the finite divided-difference identity as an arithmetic representation candidate. Do not credit a proven physical C/S sign law in the project's convention from this reading, and never substitute prime-only energy for full Q: the archimedean/pole pieces and their mixed Schur terms remain. No bound for the current D_psi-weighted remainder or cofinal degree law is supplied.

## Card I — inertia of power Loewner matrices

Bibliography: Rajendra Bhatia, Shmuel Friedland, Tanvi Jain, “Inertia of Loewner Matrices”, arXiv:1501.01505v1 [math.CA], 7 January 2015. READ_PAPER in full. Bibliographic names are transcribed from the publication; no present affiliation claim is made.

### Exact theorem and quantifiers

Section 1, page 3, Theorem 1.1: distinct positive nodes p_1<...<p_n, r>0; L_r[i,j]=(p_i^r-p_j^r)/(p_i-p_j), diagonal r p_i^(r-1). Inertia is ordered (positive,zero,negative).

- Singular iff r in {1,...,n-1}.
- At integer r<=n: r=2k gives (k,n-r,k); r=2k-1 gives (k,n-r,k-1).
- For noninteger 0<r<n: floor(r)=2k gives (n-k,0,k); floor(r)=2k-1 gives (k,0,n-k).
- For r>n-1, inertia equals inertia of L_n. This saturation clause is essential; the preceding floor formulas must not be extrapolated to arbitrary r>n.
- Every nonzero eigenvalue is simple.

Section 2, pages 5-9 supplies the printed proofs: negative powers by congruence (9)-(10), integer powers by rectangular Vandermonde factorization and generalized Sylvester law (13), zero counting Theorem 2.2 (pages 6-7) and nonsingularity Corollary 2.3, sign-regularity/exterior powers (pages 7-8), and recurrence (17) with moment-annihilator subspaces to prove the noninteger inertia cases (pages 8-9).

Proposition 2.1, pages 5-6: every such L_r with r>1 and n>=2 has a negative eigenvalue, already forced by a two-by-two principal minor. The end-of-paper determinant/complex-zero questions (pages 9-10) are open questions in that text, not available formulas.

### What is checked / applicable

These are precise published-source statements read with their proofs, not Lean-verified results. OBSERVER_CHECK: the integer identity L_r=W*VW with anti-diagonal V, and recurrence L_r=D^(r-1)E + D L_(r-2) D + E D^(r-1), follow by scalar polynomial algebra. The full zero-counting/sign-regularity proof was read, not independently reconstructed into a project theorem.

Use as an exact reference for power-symbol Loewner matrices, inertia under congruence, and possible proof mechanisms. Our arithmetic symbol is not t^r. Merely calling a matrix Loewner does not transfer this inertia, simplicity, total positivity, or a Schur pairing estimate. Exact missing bridge: a justified same-source identification/comparison preserving the required inertia or signed pairing, not a visual similarity of divided differences. There is no cofinal Weil lower bound or radical-trial upper-rate supplier here.

## Intake closeout

The five sources now have source-specific reading cards, precise hypothesis warnings, and PDF locks. The older `SURVEY_WALLS_A_B_DELTA_2026-09-03_APPENDIX_LOEWNER.md` remains a historical scout report; its broad VERIFIED labels do not override these narrower distinctions. No existing report was rewritten by this preparation. Reopen an individual import only after its named convention/domain/spectral gap is paid. No route promotion or mathematical admission follows from clearing NEEDS_CARDS.
