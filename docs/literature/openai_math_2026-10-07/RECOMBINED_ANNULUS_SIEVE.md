# Recombine Type I and Type II before the frequency norm

Root derivation, independent mobius_source_audit bounded PASS for recombination, weighted norm, outer sums and scope. This addresses the original annular common-lattice sum C_eta,V, not the complementary physical sectors. Inputs: audited Q3(2)–(6) and the source-dependent arbitrary-row sieve in TWO_LONG_DIVISOR_COLLAPSE.md(6)–(8).

## Exact restoration of squarefree coefficients

Every retained support has q_u>=c Z^(25/48)>T=Z^(1/4), eventually. Therefore the exact convolution identity gives

C_eta,V = -T_I+T_II = C[mu].

This is cancellation at the coefficient level, before any triangle inequality. It removes nonsquarefree u exactly; it does not replace mu(u) by mu(a), and selected prime squares in a remain. The restored polynomial, at fixed tuple, states, g,v and u-annulus U, is

P_H(U)=sum_(u,gPv)=1 mu(u)eta(u)/q_u *bar chi_u(H)*F(q_u/U).

Its coefficients have squared mass O(1/U), are squarefree-supported, and are fixed before the H norm. With R=q_(gP11P22), W_H=Delta_P(H)L_g(H), the arbitrary-row weighted sieve gives

sum_H |W_H P_H(U)|² <<epsilon (QUR)^epsilon
 [Q/U+Q^(1/3)R^(4/3)+(QR)^(2/3)U^(-1/3)].                 (1)

All original coprimality zeros and frequency valuations remain. Profile separation and high-H Schwartz decay are exactly those of OUTER_TRIANGLE_BUDGET.md; no contour is moved.

## Spend U at its actual scale

The V support fixes U comparable to Zq_P/q_aPg. Retain that dependence rather than using the global minimum U>=c Z^(25/48). Frequency Cauchy contributes sqrt(Q), while counting v and the original denominator contribute Y/(q_aP q_bP q_g²).

The first norm term contributes Q U^(-1/2). Substitution of U gives a g sum with exponent -3/2. For one selected prime with state(a,b), the local exponent after taking out Z^(-1/2) is -1/2-a/2-b. In states10,11,12,21,22 these are -1,-2,-3,-5/2,-7/2. Thus the tuple sum is O(Z^epsilon), including all selected states.

The middle norm term contributes Q^(2/3)R^(2/3). Its outer g exponent is -4/3, and the previous selected-state sum remains O(q_p^-1).

The third norm term contributes Q^(5/6)R^(1/3)U^(-1/6). Its g exponent is -3/2. The selected exponent is -1/6-5a/6-b+1_(a=b)/3, respectively -1,-5/3,-3,-17/6,-7/2. Again the tuple sum is bounded by the original slot counting.

After multiplying by sqrt(X)/Y, the resulting shell bound is

Z^epsilon sqrt(X)[Q Z^(-1/2)+Q^(2/3)+Q^(5/6)Z^(-1/6)]
 *min(1,(Q/Q*)^-A), Q*=Zq_P/X comparable to Z^(13/16).     (2)

Summing dyadic H shells is dominated by Q*. Norm-one rows are separately bounded by Z^(17/96+epsilon) using the exact unit-row selected factors and g=1, as in the previous outer note. Root exact rational arithmetic yields exponents47/96,23/32,11/16. Thus the result is

(sqrt(X)/Y)|-T_I+T_II| <<epsilon Z^(23/32+epsilon).         (3)

This is a benchmark for this absolute outer-summation method. It improves its separate Type-II bound37/48 and additionally retains the exact Type-I cancellation, but remains much weaker than the needed3/16. It is not a new exponent for the full physical probe: R_eta,theta and compatible high continuation remain unpaid. A bound on this annular component cannot be promoted to a bound on the whole probe, nor does the upper estimate imply a lower bound or impossibility of signed cancellation.

Audit scope clarification: V=V_G theta selects the annular n=1, squarefree-s sector. The 1-theta, n>1 and prime-power-s physical contributions remain in R_eta,theta. Multipliers chi_v(H) and bar xi(H) have magnitude at most1, including their original zeros; no assertion of unit magnitude on noncoprime rows is needed. The inputs from Pro are the normalized Q2/Q3 extracts, not original response bytes.
