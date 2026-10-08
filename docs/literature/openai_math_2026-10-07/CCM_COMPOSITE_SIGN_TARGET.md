# Exact composite operator remaining after the Ramanujan model

2026-10-08. Root derivation; independent read-only sparse_band_receiver audit PASS for C1-C4 and the conditional sufficiency of OPEN C5; its beta-domain correction is incorporated. Same original K_m, N=m,L=log m and sparse-band constraint projection P. Write A(n)=P Q_M(log n)P/sqrt(n), so ||A(n)||<=2/sqrt(n). Definitions C_R,lambda_R,b_R,D_R are unchanged from CCM_FULL_RAMANUJAN_RETURN.md; assume integer 2<=R<m and m>=4.

Define three Hermitian matrices, retaining their actual weights:

    S_small=sum_(2<=n<=R)(Lambda(n)-b_R(n))A(n),
    T_power=sum_(R<p^k<=m, p prime, k>=2)log(p) A(p^k),
    C_comp=sum_(R<n<=m, n composite)b_R(n) A(n).

Primewise equality b_R(p)=Lambda(p) for p>R yields EXACTLY

    D_R = S_small + T_power - C_comp.                     (C1)

Proper prime powers belong to BOTH T_power and C_comp, as required for their coefficient Lambda-b_R. Composites here include integers with small prime factors, not only R-rough integers.

## Small arguments and proper powers are paid

Since |c_q(n)|<=phi(q), one has |lambda_R(n)|<=sum_(q<=R)|mu(q)|<=R. Also 0<=Lambda(n)<=log n. Thus

    ||S_small||<=4(1+R^2/C_R^2)sqrt(R)log(R).              (C2)

This follows from sum_(n=2)^R n^-1/2<=2sqrt(R). It does not assert b_R majorizes Lambda.

All proper powers can be summed absolutely without any prime-distribution theorem. Extending their k-sums geometrically and then primes to integers gives

    ||T_power||
     <=2 sum_(p<=sqrt(m)) log(p)/(p(1-p^-1/2))
     <=[2/(1-1/sqrt(2))] L(1+L).                         (C3)

For the last loose bound use log n<=L and sum_(n<=sqrt(m))1/n<=1+L. Removing the condition p^k>R and extending k to infinity only increases this scalar majorant. There is no multiplicity issue: a proper prime power has a unique prime base.

Consequently, with C2+C3 denoted B_(m,R),

    lambda_max(D_R)<=B_(m,R)-lambda_min(C_comp),
    |lambda_max(D_R)+lambda_min(C_comp)|<=B_(m,R).        (C4)

The second assertion is Weyl's norm perturbation inequality applied to D_R=-C_comp+(S_small+T_power). No sign is assigned to either paid matrix.

For R=floor(m^beta), fixed 0<beta<1, B_(m,R)=O_beta(m^(5beta/2)log m+(log m)^2). In particular this cost can be made subordinate to any fixed hypothetical off-critical signal by choosing beta sufficiently small once, never as a function of m.

## Single remaining one-sided target

Combining C1 with the full quadrature and smooth-kernel identities gives

    P Aprime P = PJP/C_R + E_R + S_small + T_power - C_comp.

Here ||J||<=8, E_R has the FULL bound O(m^(alpha+4beta)), and C2-C3 pay every small integer and every proper prime power on the Lambda side. What is not proved is a lower spectral bound for the deterministic composite matrix C_comp. A sufficient interface is an absolute finite c such that, for every sufficiently small fixed alpha,beta>0,

    lambda_min(C_comp)>=-C_(alpha,beta)m^(c(alpha+beta)) eventually. (C5)

C5 is OPEN. Its sufficiency follows by fixing a hypothetical delta>0 and choosing alpha,beta so that alpha+4beta,c(alpha+beta),5beta/2 are all strictly below delta. All logarithms and the O(log m) archimedean term are then subordinate to m^delta/(log m)^(2delta). The original sparse-band receiver is unchanged.

The weights b_R(n) are nonnegative, but Q(log n) is a sum of translations and is not positive semidefinite in general. Therefore positivity of the weights proves neither C_comp>=0 nor C5. No sieve positivity or independent-edge analogy is imported. This reduction identifies the exact signed operator; it does not solve its spectral bound or establish RH.

## Bounded alias-hunt entry, not a supplied estimate

Plain obstruction: positive weights on composite shifts do not control the negative spectrum of their sum. C5 needs an arithmetic correlation property beyond the sign of each scalar weight. The exact object and normalization are C_comp above; C1-C4 identify its paid surroundings.

Negative control outside the intended arithmetic family: a single positive symmetric translation T_s+T_-s on the whole line has Fourier multiplier 2cos(s xi), which takes negative values. Thus positivity of a shift measure alone is insufficient; this is not a counterexample to the actual compressed composite sum.

Search dictionaries used: (i) Selberg sieve weights and composite adjacency spectrum, (ii) Ramanujan density and positive-definite Mellin transforms, (iii) logarithmic shifts and reflection positivity. Three ask.sh queries returned INCOMPLETE due to semantic-index freshness failure; this is not an absence result.

UNVERIFIED rewrite hints: a multiplicative integer-graph energy lift would require a norm-preserving return to the actual finite Fourier carrier; a whole-line Fourier multiplier lower bound would have to retain the exact composite cutoff and weights before compression. Neither map is asserted.

One local lead was inspected, not admitted: q3.lean.aristotle/Q3/Proofs/RouteB/MangoldtDivisibilityEnergy.lean, lines16-25 and theorem primeForm_le_log at442. Its finite form uses pairs (n,d) with nd<=M and weights Lambda(d)/sqrt(d), on counting-norm coefficient sequences c_n. The current form instead acts by physical log shifts on a Fourier carrier and uses b_R on composite n. The integer-graph theorem gives neither that coefficient map nor a bound on its norm return, and its upper prime-form direction is not C5's lower composite direction. No new Lean build was run and no supplier was admitted. Next bounded test: determine whether an exact lift retains both weights and a controlled norm, stopping if it merely returns the already open source inequality.
