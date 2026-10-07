# Both long Mobius divisors before the frequency norm

Own continuation while Q5 is pending. Root derivation and squarefree_conductor_check bounded PASS for the coefficient regrouping, weighted sieve, profile/tail transfer and outer budget. Input remains the pinned source sextic large sieve and its previously checked all-row weighted version; this is not certification of the complete source manuscript.

## Exact same-product signs

Let mu_gt(d)=mu(d)1_(q_d>T), T>=1, and a_T=mu_gt*mu_gt. Its support consists of cube-free n. Uniquely write n=r s² with r,s squarefree and coprime. Ordered factorizations d1*d2=n with both factors squarefree are d1=s*x, d2=s*(r/x), x|r. Therefore

a_T(r s²)=mu(r)c_T(r,s),
c_T(r,s)=#{x|r:q_s q_x>T and q_s q_(r/x)>T}.                 (1)

Every summand has the same sign mu(r), and 0<=c_T<=tau(r). No sign cancellation occurs between these factorizations of one fixed n. This does not rule out cancellation as r varies or across frequency pairs. In particular replacing a_T(n) by mu(n) is wrong: with T=10 and a good prime of norm13, a_T(p²)=1 while mu(p²)=0.

The exact Q3 Type-II coefficient is A_T=mu_gt*beta_T=mu_gt*mu_gt*1. Thus

A_T(u)=sum_(r s² k=u),(r,s)=1 mu(r)c_T(r,s),                 (2)

with r,s squarefree and k arbitrary. There is no (k,rs)=1 condition. Whenever c_T is nonzero, q_r q_s²>T². On q_u~U this gives q_k<=C_F U/T², retaining the sharp long-divisor cutoff.

## Weighted polynomial bound

For fixed m and annular F define

P_H,m(U)=sum_(u,m)=1 A_T(u)eta(u)bar chi_u(H)/q_u F(q_u/U).

Fix g and selected states, and put R=q_(g P22 P11), W_H=Delta_P(H)L_g(H), as in LONG_DIVISOR_COFACTOR_BOUND.md. For all good primary rows Q<q_H<=2Q, the following estimate holds:

sum_H |W_H P_H,m(U)|² <<epsilon,F (QUR)^epsilon
 [Q/T²+sqrt(Q)R+(QR)^(2/3)T^(-2/3)].                        (3)

Empty support is omitted. All parameters contributing to (2) have U>=c_F T²; no hypothesis N/T->infinity is used. Constants also depend on the original fixed arithmetic data.

Proof: fix s,k in (2). Original multiplicativity splits the row character into bar chi_r(H) times bar chi_s(H)^2 bar chi_k(H), the latter of magnitude at most1. The r-coefficients are independent of H, supported at D~U/(q_s² q_k), and include the exact cutoff count c_T. Their squared mass is at most U^epsilon/(U q_s² q_k), using tau(r)<<epsilon q_r^epsilon and annular ideal counting. With support F in[a,b], rows of r are empty only when bU/(q_s²q_k)<1; otherwise take D=bU/(q_s²q_k)>=1. Bounded scales below1 in the comparable parameter change constants only.

The weighted all-row sieve gives the fixed-s,k l2 bound, up to epsilon powers,

sqrt(Q/U)/(q_s sqrt(q_k))
 +Q^1/4 R^1/2/(q_s² q_k)
 +Q^1/3 R^1/3 U^-1/6/(q_s^(5/3)q_k^(5/6)).

Minkowski over s and then k retains all cross terms. The s sums at exponents1,2,5/3 are O(logU),O(1),O(1); the k sums up to C_F U/T² at exponents1/2,1,5/6 are O(sqrt(U)/T),O(logU),O((U/T²)^1/6). This yields

||W P||_2 <<epsilon (QUR)^epsilon
 [sqrt(Q)/T+Q^1/4 R^1/2+Q^1/3 R^1/3 T^-1/3],

and proves(3). Punctures remove columns, and overlap between r,s,k is not silently discarded. Every frequency valuation, including principal/sixth-power rows, remains in the underlying all-row sieve.

## Full outer Type-II budget

Combining the original outer d and nu into u in (2) is exact: their target character, reciprocal symbol, masks and radial profile depend on the product. There is no remaining outer d harmonic sum. The U-annuli cost O(logZ). The same v/g/selected-state/tuple sums as OUTER_TRIANGLE_BUDGET.md give, after frequency Cauchy, the physical shell bound

Z^epsilon sqrt(X)[Q/T+Q^(3/4)+Q^(5/6)T^(-1/3)]
 *min(1,(Q/Q*)^-A), Q*=Zq_P/X~Z^(13/16).                   (4)

In detail v counting and the harmonic a_Pg denominator leave Y/(q_aP q_bP q_g²); each R^theta, theta=0,1/2,1/3, is absorbed by convergent sum_g q_g^(-2+theta) and local selected-state sum q_p^-1+q_p^(-2+theta)+2q_p^-3+q_p^(-4+theta)<<q_p^-1. Fixed slot ideal counting finishes the tuples.

The profile has c=q_aPg U/(Zq_P) in a fixed positive compact interval and b=XQ/(q_aPg U). Log-H Fourier separation is uniform at b=0 by smoothness and decays arbitrarily at large b by Schwartz bounds, exactly as in the earlier outer note. Low and high H shells sum to Q~Q*. Norm-one unit rows are separately at most Z^(17/96+epsilon), using A_T(u)<=tau_3(u), g=1 and no P22; H=0 is removed by the fixed primitive character.

At X=Z^(17/48),Q*=Z^(13/16),T=Z^(1/4), the three exponents are71/96,151/192,37/48. Hence

(sqrt(X)/Y)|TII| <<epsilon Z^(151/192+epsilon).              (5)

This improves the previously checked83/96 absolute-summation budget, but remains far above3/16. At R=1, (3)'s energy powers are5/16,13/32,3/8, so the ambient-normalized polynomial RMS saves13/64. The sqrt(Q)R term is now the largest term in the displayed balanced bound; this is an upper-bound limitation, not a lower bound for the actual sum.

Root checked exact rational arithmetic and64 finite free-monoid exponent vectors at norm labels7,13,19. These are algebra controls, not proofs of asymptotic cancellation. Type I, the physical complement, high continuation and RH remain OPEN. Q5 is still running in the same chat; no additional message has been sent. Compare (1)–(5) with its terminal answer before choosing another question.

## Source-native arbitrary-row refinement (bounded audit PASS)

The pinned source defines E_j(M,N) with arbitrary good evaluation rows and squarefree columns at paper.tex4735ff. Its equation `sextic-sieve-norm-power` (5094ff), combined with the final `sextic-sieve-norm-shell` (5154ff), gives the stronger input

E_j(Q,D) <<epsilon (QD)^epsilon [Q+Q^(1/3)D+(QD)^(2/3)].     (6)

Indeed write f=min(Q^(1/3),(Q/L)^(2/3)) for the source's selected squarefree factor length L<=C Q. Then f L<=C Q, f D<=Q^(1/3)D, and f(LD)^(2/3)<=(QD)^(2/3). The finitely many bounded subunit shells change constants only. The kernel in E is chi_H(n), whereas our kernel is bar chi_n(H): the zero-preserving fixed-ray reciprocity identity at1059–1092, finite ray splitting, and whole-sum conjugation supply the transfer without imposing squarefreeness on H. Sixth-power zeros must remain zeros.

Applying the same positive divisor expansion of |W_H|² with H=G a b² h changes the middle factor into

Q^(1/3)D/q_G^(1/3) *sum_a|G q_a^(5/3)*sum_b|J q_b^(4/3)
 <<epsilon Q^(1/3)D R^(4/3+epsilon).

Consequently the replacement for(3) is

sum_H |W_H P_H,m(U)|² <<epsilon (QUR)^epsilon
 [Q/T²+Q^(1/3)R^(4/3)+(QR)^(2/3)T^(-2/3)].                 (7)

The fixed-s,k middle norm is Q^(1/6)R^(2/3)/(q_s² q_k); its harmonic sums cost only logarithms. The outer middle power theta=2/3 still gives a convergent g sum and selected-state local factor O(q_p^-1). Thus the physical replacement for(4) is

Z^epsilon sqrt(X)[Q/T+Q^(2/3)+Q^(5/6)T^(-1/3)]
 *min(1,(Q/Q*)^-A).                                       (8)

Root exact-fraction check: physical exponents71/96,23/32,37/48, with maximum37/48. At R=1 the energy exponents are5/16,13/48,3/8, giving ambient-normalized RMS gain7/32. Independent squarefree_conductor_check bounded PASS for equations(6)–(8), kernel orientation, zero extension, weight density and outer sums. For row scale Q/q_E in[1/2,1), only the unit ideal can occur and its trivial O(D) estimate is covered by the middle term; q_E>2Q is empty. This remains a corollary of the pinned source lemma, not a fresh end-to-end certification of that lemma or manuscript. The exponent37/48 remains above the required3/16, and no full-probe or RH conclusion follows.
