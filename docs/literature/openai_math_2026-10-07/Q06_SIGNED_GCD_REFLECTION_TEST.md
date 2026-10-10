# Q6 entrance test: signed gcd and reflection length

2026-10-10. Independent read-only q06_reciprocal_k_map bounded PASS for S1/S2, R1 and conditional R2. Original consumer Q5 QL48–49, all masks/windows/outer sums; RH/SP/MB34 OPEN, K/P/M/R/high conditional.

## Brief and dictionaries
The paid low-frequency region ends at B=L U^-1/1000/(q_g q_R q_e^5). The remaining high-poor signed sum is the same original CF20 with B<q_h<=K, h=v t². At g=a0=d=e=1 the natural scale is J=L²/U>L. Source: PROSHKA_VERDICT_QUADRATIC_LABELS_Q05.md QL25–49, pinned paper SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3.
Known: actual Mobius/Gauss transport and exact gcd inclusion give QL32; K pays low sector PU, no full gain. Negative control outside the actual coefficient family: free columns on distinct prime ideals; trace cancellation cannot force an upper sign.
Search dictionaries: signed divisor Gram / coprimality operator; completed cubic reflection / angular Gauss coefficient; metaplectic polar bias / regularized moment. UNVERIFIED hints: exploit signed s before positive K domination; reflect the x-series, which already has the correct a(x), rather than the old frequency-series lacking it.
Three ask.sh queries (Mobius weighted canonical Gauss moment; coprimality matrix signed divisor Gram; cubic Gauss large sieve reciprocity duality) returned INCOMPLETE, semantic-index freshness failed. No absence claim.

## S1. Exact diagonal cancellation is already present
Fix original outer tuple g,a0,d,e and h, with its actual high-poor selector. Let F_nm(h) be the full continued pair coefficient in QL31–32 before gcd inclusion, including both windows, phases, zero masks,1/sqrt(q_n q_m), and Phi(Y q_h/(q_n q_m)). Then the finite identity is

    sum_(n,m) F_nm(h) 1_((n,m)=1)
      = sum_s mu(s) sum_(s|n,s|m) F_nm(h).

For a diagonal sharing a prime with h,e or R, every admissible s-term is already zero from the retained masks. Otherwise every s|z survives, and each original diagonal n=m=z>1 has coefficient sum_(s|z)mu(s)=0. After n=sx,m=sy the inverse phase/norm identities of QL32 give the SAME F_zz in each divisor contribution. The high-poor selector depends on h and the fixed outer tuple, not s; it therefore does not spoil this cancellation. The n=m=1 window is absent eventually by g<G0<alpha_W L. This is cancellation of the artificially continued column diagonal, not a new subtraction of original D_diag or comparison lambda R_H.
Separate dyadic s energies need not have zero diagonal. Restoring cancellation requires all matching divisor contributions before absolute values. General profile Fourier separation produces mixed profiles; one cannot silently replace their bilinear terms by one positive square.

## S2. Zero diagonal gives no source-independent saving
For arbitrary coefficients on k distinct good prime ideals, the coprimality matrix is J_k−I_k. Its spectrum is k−1 once and −1 with multiplicity k−1. The all-ones vector has Rayleigh quotient k−1 although every diagonal entry is zero. This is an exact algebraic negative control, not the actual coefficient a(n)nu_*(n)chi_n(h), not an asymptotic MB34 counterexample and not a lower bound on high-poor mass.
Thus 'retain mu(s), cancel the diagonal, infer a small/nonpositive operator' is invalid without an additional actual-coefficient estimate. Merely renaming QL32 a signed frame does not pay QL49.

## R1. Correct reflection entrance differs from old failed entrance
QL34 contains a(x)=baralpha(x)gamma2(x), with alpha(x)=x/|x| (paper575). This matches the uncompleted column series in prop:completed-reflection, paper1676–1740, after the exact reciprocity/fixed-ray decomposition and puncture masks. It differs from the old Q08 attempt to reflect the h-series, where the necessary a(h) was missing.
All good moving primes from h,e,s occur with j_p=v_p(h)+5v_p(e)+4v_p(s) modulo6 after reciprocity; R and any canceled exponent still require their zero-extended puncture. The established completion inverse Q08_JOINT_ENTRANCE_TEST.md D1–D2 still requires an all-scale bound in the SAME row measure, with all moving-data costs; no such bound is admitted here.
In the simplest diagnostic g=a0=d=e=s=1, h good squarefree, the local exponent is j=1 after reciprocity. The reflected local factor in paper1778ff is chi_h(mu)^3 (quadratic), but the transformed window is Vsharp(q_mu X/q_c²) with q_c comparable to q_h=J. Hence the natural dual scale is J²/X (not a sharp support cutoff). At J=X²/U it is X³/U²; its ratio to X is (X/U)²>1 throughout ell>=1.11. The change in character order is real, but it does not itself shorten the sum. This is a diagnostic of this sector, not an upper bound for the whole original signed sum.
For h=a² with a squarefree, j=2 instead; conductor scale is sqrt(J), transformed length J/X and reflected character is cubic. These cases must not be conflated. Shared primes with s, e or R introduce other exponents, j=4 Ramanujan branches and j=0 active/inactive masks. Any complete transform must retain all of them.

## R2. Conditional all-scale inverse test
This calculation assumes a hypothetical completed-series bound; it is not a proof of that bound. Suppose, in one fixed nonnegative row Hilbert space, ||T_x||_2 <= C(sqrt(J)+J/sqrt(x)) for all x above the fixed support cutoff. The exact inverse D_X=sum_b mu(b) A_h(b)/q_b T_(X/q_b³) has |A_h(b)|<=1, including zeros. Compact support permits only q_b<=C X^(1/3). Minkowski therefore yields

    ||D_X||_2 <= C[sqrt(J) sum_b q_b^-1
                        + J/sqrt(X) sum_b q_b^(1/2)]
              <= C[sqrt(J)log(2X)+J].

Thus this route supplies at best the envelope J log²(2X)+J², not the putative single-scale J+J²/X. Ideal counting O(B) justifies both sums. The positive-theta inverse lemma Q08 D2 cannot be used on x^-1/2: its convergence condition has the wrong sign. At natural J>X the J² envelope is even weaker than an elementary JX bound. This does not disprove a better signed b-sum or a uniform positive-theta completed bound; it rules out this particular free inverse return. No full CF20 estimate is asserted.

## Primary-source return, not a supplier admission
Zagier, Appendix C Theorem1(a), in The Coprime Quantum Chain (2017), DOI10.1088/1742-5468/aa5bb4, PDFp53: “The Perron–Frobenius eigenvalue” of N^-1 C^(N) converges to approximately0.678462. Domain: all ordinary integers1..N with unweighted coprimality, arbitrary vectors. This is a structural analogue for S2 only: not squarefree Eisenstein annuli, actual Gauss coefficients, radial pair profiles or a signed outer average. No spectral constant is imported.
Source https://people.mpim-bonn.mpg.de/zagier/files/doi/10.1088/1742-5468/aa5bb4/CoprimeQuantumChain.pdf ; fetched /tmp/q06-alias/coprime.pdf SHA256e2d4d762aa0e5abbfc6446ff6ac1c1d8f1e1deec2fa67bc124fe56377d1e39f6.
De Faveri–Dunn–Hoffstein2607.07911v1 (08Jul2026), Theorem1.1: Xi3(A,B) >=_eps (AB)^(-eps)[A+B+(AB)^(2/3)]. This is the arbitrary-coefficient cubic operator norm, not our sextic signed form. Proof§2.1 chooses conjugate normalized cubic Gauss coefficients and obtains a polar term plus a mean-square remainder. Potential bridge: subtract an actual mapped polar contribution before a joint estimate; missing: angular factor baralpha, fixed ray data, zero masks, all s and original centering/returns. In particular h=a² does NOT license this source's polar term by name: QL34 has the additional genuine angular factor. No lower bound for our actual sector follows.
Source https://arxiv.org/html/2607.07911v1 ; fetched /tmp/q06-alias/nonorthogonality.html SHA2569bea09caf792c531940c313c6a0bcc1d1512e52020e0865f959fe37725659a14. Verbatim locator, Theorem1.1: “Cubic large sieve lower bound”. Both papers are verified discovery evidence only; no new full moment supplier.

## Decision after bounded review
No new full bound is admitted. The independent report also offered a crude generic E1 envelope; it is not used or admitted in this note because the bounded diagnostic already resolves the proposed shortcut. Next bounded question should keep signed s and the correct completed x-series together, and require the full moving-conductor/reflected-length/zero-mask return. Stop a proposed direct reflection shortcut if it merely produces a longer quadratic sum without a paid bound. Do not repeat an arbitrary-coefficient perfect-orthogonality claim or discard the angular factor.

Finite root consistency check:256 gcd-incidence identities on divisors of7·13·19·31,15 diagonal cancellations, and the4-prime eigenvalue3 matched exact integer arithmetic. These are diagnostics, not proof of the actual Gauss estimate.
