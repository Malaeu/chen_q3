# Spending the weighted cofactor estimate in the outer sums

Root derivation; independent squarefree_conductor_check bounded PASS for the transition shell and full-H extension. This is an upper bound for the actual upper-annulus Type-II object, not for the physical complement or Type I.

Use LONG_DIVISOR_COFACTOR_BOUND.md(4), keeping tuple,selected states,g,v and outer d fixed before the H norm. For a dyadic H shell of norm Q, Cauchy over H costs sqrt(Q). With R=q_g q_P11 q_P22, the resulting three l2 terms are

sqrt(Q/T), Q^1/4 R^1/2 log(2N/T), Q^1/3 R^1/3 T^-1/6.

Outer d has harmonic mass O(1) on each dyad, even after retaining d>T. There are O(log Z) d and nu dyads. The v-window contains at most O(Y/(q_bP q_g)) ideals whenever nonempty. Multiplying its count by the original 1/(q_aP q_g) leaves Y/(q_aP q_bP q_g²). Masks only reduce these absolute bounds.

For each theta=0,1/2,1/3, the g factor sums as sum_g sf q_g^(-2+theta)<infinity. The five selected states at each p contribute

q_p^-1+q_p^(-2+theta)+2q_p^-3+q_p^(-4+theta) << q_p^-1.

The tuple sum is therefore bounded by a fixed multiple of sum_tuple |w|/q_P, which factors over the fixed disjoint slots and is O(1) by ideal counting and the original compact slot supports. This accounts for the large-R rows through their original denominators; they are not discarded.

Consequently the transition-shell Type-II bound is

|TII_Q| <<epsilon Z^epsilon Y sqrt(Q)
 [sqrt(Q/T)+Q^1/4+Q^1/3 T^-1/6].                            (1)

Profiles are uniform: writing c=q_aPg d N/(Zq_P), the V support places c in a fixed positive compact interval, while b=XQ/(q_aPg d N)=(XQ/(Zq_P))/c. At Q0=Z^(13/16), XQ0/(Zq_P) is bounded above and below. The log-H Fourier separation therefore has uniform seminorm bounds over all surviving outer boxes.

## Full H range

The direct-sieve proof only needs uniform smooth annular-profile seminorms. For Q<=Q0, b may tend to zero: smoothness of W0tilde at zero keeps every such seminorm bounded. For Q>Q0, its Schwartz decay gives O_A((Q/Q0)^-A) for every required seminorm, including log-H derivatives. Fourier separation in log H retains this factor and rapid decay in the separation parameter. These facts are stated for the radial transform in source paper.tex3762–3777. No Mellin contour is shifted here.

Thus (1) holds with an additional min(1,(Q/Q0)^-A) factor. More precisely the tuple-dependent transition is Q*=Zq_P/X, uniformly comparable to Q0. The three powers of Q are1,3/4,5/6. Summing all dyadic Q>=1, with A sufficiently large, is bounded by Q0. H=0 already vanishes by the fixed primitive character. Norm-one unit rows, omitted by Q<q_H<=2Q with Q>=1, are handled separately: L_g(1)=0 unless g=1 and D22(1)=0, while other factors have magnitude<=1. The trivial divisor bound for B on each nu-annulus and the same outer counting give physical O_epsilon(sqrt(X)Z^epsilon)=Z^(17/96+epsilon), below(2). Split all six unit classes when summing elements. Thus no nonzero good frequency valuation is discarded.

Multiplying by the original physical prefactor sqrt(X)/Y gives three exponents83/96,151/192,13/16, respectively. The resulting full-H upper-annulus Type-II bound is

(sqrt(X)/Y)|TII| <<epsilon Z^(83/96+epsilon).                 (2)

Exact rational arithmetic checked. This is much weaker than the desired3/16−delta. It does not improve the source-reported bound for the full original probe and does not imply a lower bound for any actual sum. It quantifies the loss of this particular absolute outer summation. A new joint signed estimate, or a correctly controlled recombination with Type I and the physical complement, is still required.
