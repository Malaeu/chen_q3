# Q2 common-lattice frequency Cauchy: own attempt

Obstruction: the exact kernel is now known, but a signed estimate at the original scales is missing. Test the direct frequency Cauchy/large-sieve mechanism on an actual surviving subblock before asking it to handle the whole probe. This is a restriction for testing a bound, not a replacement for the physical sum.

Use Q2(9)–(10), and restrict a,b,H to squarefree good ideals, pairwise coprime, P|a and (bH,P)=1. The squarefree sextic sieve applies directly to the two signs; any unit/ray-class split costs only a fixed factor. Then every selected prime is at valuation pair(1,0); the exact kernel is mu(a)barchi_a(H)chi_b(H). Coefficients retain eta(a)/q_a, original tuple weights, and the profiles V(q_a/(Zq_P)), W1(q_b/Y), W0tilde(Xq_H/q_a). At the Fourier transition,
A~Z^(7/6), B~Z^(23/48), C~Z^(13/16), q_P~Z^(1/6).
These scales are common-coordinate scales, not the subset-dependent primal c,s scales.

Mellin separation of the smooth ratio profile on this fixed dyadic box costs a fixed integrable transform norm and places only unit-modulus powers into coefficients. The nonunit zero values impose (a,H)=(b,H)=1; detect the remaining (a,b)=1 by sum_d|(a,b) mu(d). For each d, the two coefficient vectors are fixed before summing H. Apply Cauchy in H and the audited source squarefree sextic sieve with
D(C,N)=(CN)^epsilon [C+N+(CN)^(2/3)].
The divisor-mass sum is at most a divisor loss by Cauchy over d. In particular sum_d sum_a:P|a,d|a |alpha_a|^2 <= Z^epsilon/(Aq_P), whereas sum_d sum_b:d|b |beta_b|^2 <=Z^epsilon B. Thus the proposed per-tuple bound is

Z^epsilon sqrt(B/(Aq_P)) sqrt(D(C,A)D(C,B)).

There are at most Z^(1/6+epsilon) original tuples, and the exterior factor is sqrtX/Y=Z^-29/96. Exact exponent arithmetic gives D(C,A) exponent95/72 and D(C,B) exponent31/36. The resulting bound for this subblock is only Z^(19/36+epsilon), worse than the desired3/16 by49/144. Even replacing both norms by the HYPOTHETICAL optimal C+N shape gives exponent41/96, still worse by23/96. This calculation diagnoses this particular separation of the two polynomials, not the true size of the subblock. Other sectors can cancel it; no lower bound or universal no-go is asserted.

Negative control: replacing actual Mobius phases by arbitrary coefficient vectors erases exactly the additional arithmetic structure that a better estimate would need. The norm bound is designed to allow those arbitrary vectors, so it cannot supply cancellation specific to mu(a)eta(a) or the subtraction among subsets. Nor does this test cover repeated-prime H, shared-prime Ramanujan factors, selected valuation-two terms, or the exact physical complement in Q2(32).

Alias return: dictionaries are (i) signed bilinear sextic character forms with Mobius coefficients, (ii) metaplectic Eisenstein/cube residue and multiple Dirichlet series, (iii) parity-sensitive bilinear sieve rather than arbitrary-coefficient operator norm. UNVERIFIED bridge hints: a Type-II decomposition exploiting mu(a), or a complete spectral identity that matches residual and nonprincipal frequency terms. Both must map to the actual Q2 kernel and retain the complement.

Shelf query via ask.sh returned INCOMPLETE (semantic freshness), not absence. External search returned the already-checked Dunn fixed cusp theorem (mapping still missing), Baier–Young arXiv0804.2233v4 (Theorem1.4 is a rational-integer coefficient family, not this all-ideal triple correlation), and a simpler OpenAI October5 paper claiming11/12 and explicitly referring to September30 for7/8. No new estimate is imported. The negative control for Baier–Young is the changed ground-variable support: integers are a thin subset of Eisenstein ideals; merely renaming ideal norm as an integer length is invalid. Their introductory discussion expressly distinguishes these domains. These are excluded leads pending exact mapping, not verified candidates.

Next quantitative task: retain signed correlation between both character polynomials, or restore full sectors before a cancellation estimate. Repeating separate Cauchy bounds, even with a better arbitrary-coefficient large sieve, does not meet the budget demonstrated here. No Q3 question has yet been sent.

Independent squarefree_conductor_check: PASS for this restricted subblock and its budget, including Mellin separation, fixed-row coefficient condition, retained q_P divisor-mass saving, and exact exponent arithmetic. This is no estimate for omitted sectors.
