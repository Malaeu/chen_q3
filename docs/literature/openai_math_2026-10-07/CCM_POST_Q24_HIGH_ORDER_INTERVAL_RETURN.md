# Post-Q24: high-order local reconstruction, complete moment price

2026-10-25. One bounded attempt to remove the first-order interval reconstruction fee. No new source bound. Original actual complex two-time weight F_a and dE=dpsi-dx retained; no change to P or prime powers.

On I=[y,y+H], define D_j(I)=integral_I (x-y)^j dE(x), j>=0. For fixed k>=1 the exact Taylor decomposition is

    integral_I F_a dE = sum_(j=0)^(k-1) F_a^(j)(y) D_j(I)/j! + integral_I R_k dE.

On a full dyadic block [X,2X], actual fixed-profile derivatives satisfy |F_a^(j)|<=C_(w,j) X^(-1/2-j) uniformly in a. Constants may depend on fixed j,w; j does not grow with m. Taylor's remainder obeys |R_k|<=C_(w,k) X^(-1/2)(H/X)^k. Summing over the block and using total variation dpsi+dx gives the complete remainder price

    O_(w,k)(sqrt(X)(H/X)^k).

This improves the old reconstruction fee. It is not the full budget: every D_j is still present. The short-interval PNT supplies only D_0=o(H) for intervals longer than its threshold. If the higher D_j are paid by total variation, their full block contributions are at most

    O_(w,j)(sqrt(X)(H/X)^j), j>=1.

If only total variation is used, the j=1 term retains H/sqrt(X). However the existing UNIFORM short-interval supplier provides more than D_0 at the single length H. The independent audit correctly identified this missing use of its quantifiers.

Choose H_0=X^beta, 7/12<beta<theta<1, and A(t)=E(y+t)-E(y). Partial summation gives D_j=H^j A(H)-j integral_0^H t^(j-1)A(t)dt. For t>=H_0 the same supplier gives |A(t)|<=epsilon_beta(X)t uniformly. For t<H_0, positivity of dpsi and its bound at H_0 imply |A(t)|=O(H_0). Therefore, for every fixed j>=1,

    |D_j|<=C_j[epsilon_beta(X)H^(j+1)+H_0^(j+1)].

Thus qualitative moment cancellation IS supplied without a new theorem. Aggregating over complete cells, the full high-order budget is

    O_(w,k)(epsilon_beta(X)sqrt(X)
             +H_0^2/(H sqrt(X))
             +sqrt(X)(H/X)^k).

The j>=2 threshold fees are smaller by powers H_0/X; the D_0 fee is covered directly at length H. For a shortened terminal cell, use partial summation of its entire weight with the same threshold split; its fee is O_w(epsilon_beta(X)H/sqrt(X)+H_0/sqrt(X)). Alternatively the original production endpoint's actual rapidly decaying source tail remains available. This edge must not be replaced by the improved complete-cell budget without justification.

Example for COMPLETE dyadic blocks: beta=3/5,theta=4/5,k=3 gives threshold fee X^(-1/10) and Taylor remainder X^(-1/10). Hence the complete-block first-order reconstruction floor is removable. The leading term epsilon_beta(X)sqrt(X) nevertheless remains: epsilon_beta=o(1) does not imply any fixed power saving. This is the surviving arithmetic gap. No claim of a new prime theorem or favorable CCM bound follows.

Exact negative control for inference from D_0 alone: on [0,H], nu=H delta_(H/4)-H delta_(3H/4) has D_0=0, D_1=-H²/2. For a linear weight F(x)=a+b x, integral F dnu=-b H²/2, although every Taylor remainder of order>=2 is zero. Both signs and the first moment must be retained. This is a synthetic signed-measure control, NOT actual prime data, NOT a lower bound for actual CCM, and NOT a counterexample to uniform short-interval PNT on all its admitted intervals. It only disproves inference of weighted cancellation from one interval's total mass.

All dyadic and production endpoints are kept as in CCM_POST_Q24_SHORT_INTERVAL_PREFLIGHT.md. The original-P mixed returns, continuous credit, self terms and proper powers are unchanged and charged once. The best inherited pair bound is not replaced by these weaker budgets.

Conclusion after one bounded audit and root correction: high-order reconstruction and the existing uniform supplier reduce the complete-block reconstruction fees, but the unspecified leading relative-error rate remains. The initial claim that higher moments require wholly new arithmetic input was incorrect and has been withdrawn. This is a concrete supplier-interface obstruction, not a no-go for high-order methods with additional information. Q10 explicitly left high-order reconstruction open; this calculation checks its missing terms rather than repeating its first-order remainder. No Q25 sent.

Audit: post_q24_high_order_audit found the missing H_0 threshold split; incorporated above. Root checked aggregate exponents exactly:2beta-theta-1/2=-1/10 and1/2-k(1-theta)=-1/10 at the displayed choice. Synthetic D0/D1 control verified in SymPy1.14.0; it cannot refute uniform PNT, as explicitly limited. No second independent pass or global sign certification claimed.


## Full actual-pair summation (root continuation, not yet independent review)

Retain derivative envelopes A_j(v) formed from the finitely many actual C derivatives through order k; their unit-interval suprema have double-exponential tails. The derivative bound on each dyadic block is the preceding bound multiplied by an envelope at v=2a-log X and at v=2a+log X. The last incomplete dyadic block lies in [m/2,m]; for a<=h its full weight has |v|>=2log L-log2, so Chebyshev pays that entire endpoint by O_w(sqrt(m)exp(-c_w L²)). This avoids treating a short terminal interval as a complete one.

For complete blocks choose beta=3/5, theta=4/5,k=3. Weighted summation of the X^-1/10 reconstruction terms near X=exp(2a) is O_w(exp(-a/5)); the other scales are absorbed by the actual envelopes. Fixed initial blocks have vanishing actual profile tails as a increases. The reverse-time contribution is retained and has the same or smaller bound. Thus reconstruction is o(1) uniformly for h-T<=a<=h, T=alpha L,0<alpha<1/4.

For the leading discrepancy term, take epsilon_*(a)=sup_{X>=exp(a)}epsilon_beta(X)->0, with fixed small-X exceptions absorbed in the below-exp(a) source tail. The sum is bounded by C_w epsilon_*(a)exp(a)+o(1), since the exponential dyadic envelope is summable. Uniformly over the averaging window, replace it by epsilon_*(h-T). Integration gives the arithmetic price at most

    C_w epsilon_*(h-T) exp(h)(1-exp(-T))/T + o(1).

Adding unchanged self and arch O_w(L+1), full original-P o(1), and the joint continuous return gives a qualitative o_w(sqrt(m)/(LT))+O_w(L+1). This is not a fixed-power gain and is not claimed as a new PNT theorem or new research mechanism. The ratio of the displayed arithmetic budget to E_T is proportional to an unspecified epsilon_*(h-T) exp((1-2delta)h). Its convergence to zero is NOT established; it cannot be assumed from epsilon_*->0. All source signs were retained in the identity, but separate absolute interval-discrepancy payment is the remaining information loss.

Concrete impasse: high-order reconstruction does not provide a rate for the actual signed interval-moment coupling. A next task must use that coupling before independent absolute payments, or supply a genuinely different earlier source mechanism; it must not ask again for a Taylor remainder, uniform short-interval PNT, or the same missing global estimate under a new name.
