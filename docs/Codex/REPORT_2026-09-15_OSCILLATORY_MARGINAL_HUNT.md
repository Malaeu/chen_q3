# Oscillatory marginal hunt: exact theorem matching and two direct-transfer filters

STATUS: ANALYTIC_PAPER_CANDIDATE / SOURCE_VERIFIED_DISCOVERY; INCOMPLETE_NO_CONSUMABLE_TARGET. No full C6, V sign, RH, or canonical admission.
Brief: docs/Codex/BRIEF_2026-09-15_OSCILLATORY_MARGINAL_HUNT.md, SHA256 6648d9fc85388490e1ef1dada802d7c8617cbed431972c698b33426fba6a13d8; source base 4353bf4d7304457e3731cf6112149619f0116282.

## 1. Scope and source reconciliation

The consumer remains C6 for the fixed geometric gamma family, with source/normalization and the full negative control locked in the brief. We are looking for a mechanism of non-cancellation, not another statement that a real density or a Hilbert norm is positive. The current proven zero-free slab |Re z|<=5 for all N and real Im z remains unchanged.

The local shelf already contained the N=1 Bessel/Sturm-Liouville mechanism and the Lee-Yang closure route. REPORT_2026-09-12_PHYSICS_BROTHER_LEE_YANG.md explains the single-site premise in Lieb-Sokal; the LYGSPHI intake rejects one exact entropy-binomial lift, not all possible Lee-Yang realizations. These are retained prior findings, not new candidates. Three registered ask.sh queries used new dictionaries: complex Prekopa/Bergman, sectorial complex marginals, and stable-polynomial/Lee-Yang integration. All returned exit2 ASK_STATUS INCOMPLETE (semantic-index freshness); the retained tool results are truncated and explicitly not complete stdout. No query was retried and no absence claim or index refresh is made.

External search was bounded to primary statements distinguishing complex marginal norms from genuinely complex integrals. Two candidate mechanisms were read. The missing exact canonical consumer edge forbids CLOSES/OPENS or supplier admission.

## 2. Berndtsson: a real complex-geometry theorem, but a different output

Primary: Bo Berndtsson, Subharmonicity properties of the Bergman kernel and some other functions associated to pseudoconvex domains, arXiv:math/0505469v1 (2005), https://arxiv.org/pdf/math/0505469.
Local berndtsson2005.pdf SHA256 d882ff3951d4a1a506ed0a8c1e0a89dc2e9a35657831eec7605f43a8e354055b.
Quote, PDF p1 immediately after Theorem1.1: “Theorem 1.1 may be seen as a complex version of Prekopa’s theorem”.

For a pseudoconvex total domain D in complex parameter/fiber variables and a real plurisubharmonic weight phi, Theorem1.1 asserts plurisubharmonicity (or identically minus infinity) of log K_t(w,w), the weighted Bergman diagonal. The rotationally invariant Theorem1.2, PDF p2, concerns -log integral exp(-phi). The source was read at pp1-2; these are positive weighted L2 objects.

Mapping attempted: t would be our spectral parameter z, the fibers would need to encode the exact gamma variables, and the target would be M_N(z). The paper's measure is exp(-phi) with phi real, while our weight is G_N(x) exp(-izx). Taking its modulus produces G_N(x) exp(Im(z)x), erasing Re(z), precisely the variable beyond the proven central slab. There is no proved identity identifying M_N with a nonvanishing Bergman diagonal. Even a holomorphic function's log modulus is subharmonic in the extended sense at its zeros; that property by itself is not a zero exclusion theorem.

Verdict: VERIFIED_PARTIAL_ANALOGUE; reject the direct conclusion “complex Prekopa proves C6.” It may guide construction of an exact positive-space model, but does not provide such a construction. The brief's negative control has a positive real tilt integral and a complex Fourier zero, so the distinction is necessary on an explicit example. This is a transfer mismatch, not a refutation of Berndtsson's theorem.

## 3. Barvinok: an actual non-cancellation theorem

Primary: Alexander Barvinok, Computing Gaussian and exponential integrals in R^n, arXiv:2606.23556v3 (16 August 2026), https://arxiv.org/pdf/2606.23556.
Local barvinok2026.pdf SHA256 75a3325bf68a259647094f40cf9ff8d1d7c3ffb21ce632d8e612b7b7e0e07f52.
Quote, PDF p1 abstract: “for the integral to be non-zero”.

Theorem1.2, PDF p4, concerns E_gamma exp(sum phi_j) with complex-valued globally L_j-Lipschitz functions. If each coordinate occurs in at most c functions and, for every k,

sum_(j sharing a coordinate with k) L_j^2 <= 1/(64c),          (B1)

then the expectation is nonzero. Theorem1.3, PDF p6, gives a product symmetric-exponential counterpart with a sum of Lipschitz constants at most 1/(24 sqrt(r)), r>=9, for every coordinate. The Gaussian proof uses phase concentration plus an explicit tail bound (Lemma5.2, PDF pp22-23). We read the statements and this base mechanism, not the whole paper.

Mapping requirement: construct an exact representation of our integral under one of these product measures, with the prescribed nonvanishing scalar normalization, then prove these global Lipschitz and dependency budgets uniformly for the required N and spectral compact. The theorem does not assume that the desired integral is nonzero, so it is a genuine conditional mechanism. Below are direct mathematical tests on the actual source, before creating such a task.

## 4. Direct Gaussian reweighting fails before its numerical budget

Let f be either G_N or H_N at any fixed N. Permit any affine scalar change x=a+sigma y, sigma>0. Relative to standard Gaussian density, an exact continuous logarithm of the integrand is, up to a constant,

Psi_(N,z)(y)=log f(a+sigma y)+y^2/2-iz(a+sigma y).            (B2)

For the geometric source the already proved endpoint expansion gives
(log G_N)'(x)=-pi exp(2x)-2(N-1)+O_N(exp(-2x)) as x->+infinity.
For the arithmetic source the reviewed expansion gives
(log H_N)'(x)=-(4N+1/2)+O_N(exp(-2x)).

Differentiating (B2) therefore yields an unbounded derivative for either family. In the geometric case its leading real term is -sigma pi exp(2a+2sigma y); in the arithmetic case it is y-sigma(4N+1/2). Thus Psi is not globally Lipschitz. The normalization constant and the fixed spectral linear term cannot fix this.

Nor can a finite splitting into globally Lipschitz parts: any sum of such parts is globally Lipschitz. Any continuous logarithm giving the same exponential differs from (B2) by a constant multiple of 2pi i, so a branch choice cannot fix the failure either.

For completeness, on a single real variable a finite decomposition into m nonconstant terms all shares that coordinate. The best possible c in (B1) is m, and Cauchy-Schwarz forces

Lip(Psi) <= sum L_j <= sqrt(m sum L_j^2) <= 1/8.             (B3)

Dividing the same interaction into many pieces cannot buy an arbitrarily large budget. This is a necessary consequence of the source theorem's hypotheses, not a necessary condition for the integral itself to be nonzero.

## 5. Direct symmetric-exponential reweighting also fails

With the same affine x=a+sigma y and reference density exp(-|y|)/2, the exact logarithm is, up to a constant,

Psi^E_(N,z)(y)=log f(a+sigma y)+|y|-iz(a+sigma y).            (B4)

Because f is smooth and strictly positive at a, the one-sided derivatives at y=0 have the form b+1 and b-1 for one common complex b. Their difference is 2, so at least one has modulus >=1. Therefore every global Lipschitz constant for (B4), if finite, is at least 1.

Every nonconstant summand of a scalar decomposition depends on that single coordinate. Theorem1.3 would require sum L_j<=1/(24 sqrt(r))<=1/72, whereas Lip(Psi^E)<=sum L_j and Lip(Psi^E)>=1. This is impossible. The cusp argument survives all affine rescaling and applies to both source families, including the negative control, without relying on tail estimates.

Verdict for Barvinok: VERIFIED_CONDITIONAL_MECHANISM, with DIRECT_AFFINE_SCALAR_GAUSSIAN_AND_EXPONENTIAL_TRANSFER_REJECTED. This excludes these exact reweightings and their finite same-variable decompositions. It does not exclude nonlinear transports, genuinely coupled higher-dimensional representations, different reference measures, or other zero-free theorems. None of those is constructed here. Smooth positive negative-control sources are correctly rejected by the same exponential-reference filter; no false zero theorem is applied to them.

## 6. Outcome and next boundary

Two actual published mechanisms have been matched to their precise outputs. The names “complex Prekopa” and “nonzero complex integrals” do not justify a direct transfer to our source. There is no enlargement of the accepted |Re z|<=5 slab in this pass.

A future use of Barvinok needs an independently exact representation satisfying the small-interaction budgets; repeating the direct weight change, splitting it into more terms, or demanding only better scalar curvature will not supply it. Such a representation is an unresolved option, not a new goal or a conclusion that a fourth necessary property exists. Return to the coupled source structure before dispatching another task. Preserve the arithmetic alternative and the geometric-family theorem; neither has been disproved by this hunt.
