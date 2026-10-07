# Joint remainder alias return: theta coefficient pairs versus fixed cusp forms

2026-10-07. Target: exact N_eta after Q1, not a positivity surrogate. The squarefree n=1 block requires cancellation between the c and s coefficients after its incomplete m-average. Termwise square-root cancellation followed by absolute summation has the checked budget Z^(7/12-d), worse than the source low exponent 3/16. This is the return point, not a lower-bound obstruction.

Dictionaries: (i) bilinear power-residue character matrix and Gauss-weighted large sieve; (ii) cubic theta coefficients and level-aspect Voronoi; (iii) averaged homogeneous convolution and circle-method delta symbol. Local shelf query `bilinear sextic residue character sums` returned ASK_STATUS: INCOMPLETE because semantic freshness failed; it did not establish absence.

## Exact own rewrite, restricted to squarefree s and n=1

Source paper.tex 1041–1051 proves the CRT phases and signal identity gamma1(s)gamma2(s)=mu(s)alpha(s)G(s). Since |gamma2(s)|=1, substitute

gamma1(s)=mu(s)alpha(s)G(s) conjugate(gamma2(s)).

The full squarefree mixed kernel therefore contains gamma2(c) conjugate(gamma2(s)), with all other factors retained. Its c factor is baralpha(c)eta(c)Xi(c)^(-1)barG(c); its s factor is mu(s)alpha(s)G(s)bar chi_s(-1)chi_s(bstar)/xi(s). The remaining calR(c,s) is a fixed-ray bicharacter; source 1071–1092 allows its finite Fourier separation on T x T even at shared primes. The inner kernel remains

sum_m Omega(q_m/Q)(q_m/Q)^(-iv) xi(m) chi_c(m) conjugate(chi_s(m)),

with every zero extension. Multiplication by the normalized s and c weights, D|c, and original subset coefficients is unchanged. This is an exact dictionary to a pair of cubic Gauss coefficients, not yet an estimate or a single coefficient at the product cs. In particular the m-weight xi(m) is signed/complex; this character matrix is not supplied as a positive Gram matrix.

The negative control for a naive cuspidal shortcut is the actual theta expansion itself: a derivative may erase the constant term in one Mellin calculation while the nonzero coefficients remain those of theta. Erasing a zero Fourier mode is not by itself a proof of the full automorphic cusp-form hypotheses.

## Primary literature crosswalk — checked partial analogue

Alexander Dunn, *Metaplectic cusp forms and the large sieve*, arXiv:2403.13151v2, 15 June 2025. Primary HTML fetched from https://arxiv.org/html/2403.13151v2 into /tmp/q3-dunn-2403.13151v2.html; SHA256 132bf96e90698e79e04d25954a9097136b7e703e92d747f2c89cce5f7f756695. This is a source-text hash, not proof certification.

Theorem 1.5 applies to a fixed cubic metaplectic cusp form f and its bilinear sum at X~AB. Its bound is

B_f <= const_(epsilon,f) (X K N(v))^epsilon K^8 N(v)^4 [(AB)^(1/2)+A^(3/2)B^(1/4)] ||mu² alpha||_infinity ||beta||_2.

The theorem's kernel is rho_f(ab); after Cauchy the proof uses rho_f(a1*b) conjugate(rho_f(a2*b)), equation (1.16). The proof keeps the a1,a2 averages instead of bounding every convolution individually. Quote, §1.2.2: “the additional averaging over a1 and a2 is crucial”. Independent squarefree_conductor_check source crosswalk completed: PARTIAL ANALOGUE, not an applicable bound for N_eta. The full kernel is rho_f(lambda^-3*a*b); a is primary squarefree, A,B>=10, v is a congruence modulus divisible by 3, and the test W_K is smooth on [1,2]. Here this literature parameter v is NOT our Mellin height. Fixed norm scaling by N(lambda^-3) must be retained. The sum is restricted by a*b congruent to u modulo v, where (u,v)=1 and u is congruent to 1 modulo 3; u is an invertible residue class, not necessarily a global unit. Theorem constants depend on f.

## Derivative check: a local cancellation is weaker than scalar automorphy

Source paper.tex 1936–1984 identifies d_H as theta cusp-expansion coefficients; 2300–2365 differentiates at z=0 after a rational-cusp inversion and thereby removes C_H(v). To test the tempting inference to a cusp form, write the basic inversion coordinates with t=v²+z*barz:

z'=-barz/t, barz'=-z/t, v'=v/t.

Then d_(barz)z'=-v²/t², d_(barz)barz'=z²/t², d_(barz)v'=-v*z/t². At z=0 only the first survives, exactly as in the source reflection calculation. Away from that slice the chain rule mixes horizontal and vertical derivatives. Thus the displayed reflection identity alone does not establish that the plain derivative is a scalar cusp eigenfunction of the type required in Dunn's theorem. This does not rule out an appropriate representation-theoretic differential operator or a new estimate for its K-types; such a transfer would need its own identity and bounds.

Decisive source mechanism: Dunn Proposition 8.3 (downloaded TeX 1772–1791; corresponding HTML Proposition 8.10) uses cuspidal exponential decay at both endpoints and a zero constant term to make completed twists entire; the level-aspect Voronoi contour then crosses no residues. The source assumes automorphy, a Laplace eigenfunction and vanishing at every cusp (downloaded TeX 271–293). Our derivative calculation supplies no such fixed cusp-form realization. Independent audit also checked the exact Gauss-pair rewrite and the local-versus-global derivative distinction.

Arbitrary outer weights are allowed in Dunn: moving m,s can potentially be placed there if the exact factorization and norm bounds are proved. Their mere presence is not an exclusion; the absent fixed cusp coefficient identity is the issue.

Next bounded check: identify whether the exact Gauss-pair expression can enter the literature's averaged convolution while retaining moving m, Gauss masks and all compensation subsets. A fixed-form estimate with implicit constants depending on a moving twist is not sufficient. No Q3/SP/RH status changes, no new full low exponent, and no second message during Q2.
