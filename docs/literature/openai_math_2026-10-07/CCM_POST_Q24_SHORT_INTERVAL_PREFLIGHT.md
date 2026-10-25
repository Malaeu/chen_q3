# Post-Q24: direct short-interval supplier strength on the full pair

2026-10-25. Root derivation plus post_q24_short_interval_check bounded applicability check: PASS with 7/12<theta<1 made explicit. No new favorable estimate and not a renamed independent Q10 experiment. Original full source and P unchanged.

Use the actual complex weight F_a(x)=exp(2i gamma a)x^(-1/2)[C(2a-log x)+C(2a+log x)]. The full centered sum is integral F_a d(psi-x); all prime powers remain. On X<=x<=2X, |F_a|<=A_w X^-1/2 and |F_a'|<=B_w X^-3/2 uniformly in a; constants use full C,C'. No components are deleted.

Suppose a uniform interval supplier gives |psi(y+h)-psi(y)-h|<=epsilon(X)h on intervals in [X,2X] with h comparable to H=X^theta, 7/12<theta<1 fixed, epsilon(X)->0. Partition the block into K=floor(X/H) equal intervals of length X/K, between H and2H eventually. Thus there is no unpaid last short interval. If a production endpoint cuts the dyadic block, keep that terminal interval explicitly; its contribution can be bounded by its actual source tail or by O(H log X/sqrt X), not silently discarded.

Freeze the FULL complex weight at each left endpoint. The discrepancy of the frozen terms costs at most A_w epsilon(X)sqrt X. Replacing the full weight by these constants in both the prime sum and continuous integral costs at most B_w H X^-3/2 times [psi(2X)-psi(X)+X], hence O_w(H/sqrt X) by Chebyshev. This includes all within-block interactions encoded by C; it is a linear discrepancy calculation, not a quadratic decoupling. The continuous main is retained exactly, with its inherited joint return.

The resulting block budget is O_w(epsilon(X)sqrt X+X^(theta-1/2)), plus the explicit terminal edge. A fixed power saving in the second term does not supply a fixed power saving in the first. A statement epsilon(X)=o(1) permits rates slower than every X^-c. On the source's dominant scale X approximately exp(2a), a target exp(2delta a) would require a quantitative relative discrepancy roughly X^(-(1/2-delta)) or additional signed coupling; it does not follow from relative o(1). Even the reconstruction alone requires theta-1/2<delta for this first-order formula; theta>7/12 therefore cannot cover arbitrary delta>0.

All original-P mixed return, proper-power bookkeeping, self and arch terms remain inherited and must be paid once. This calculation cannot replace the stronger existing pair budget sqrt(m)/(LT)+L+1. It identifies a missing input, not a lower bound for actual CCM or a prohibition on improved reconstruction or direct signed interval coupling.

Comparison: Q21 used short-interval PNT to price a shrinking-shell certificate; Q10 studied mean-square smoothing. This direct sup-discrepancy bridge clarifies supplier strength on the actual pair but does not count as a fresh arithmetic mechanism or justify Q25 by itself.

Supplier check: Matomaki–Teravainen, Oberwolfach Report50/2019 printed p3177, https://ems.press/content/serial-article-files/46829, states uniform relative o(1) for H>=x^(7/12+sigma), fixed sigma>0; attributes Huxley https://doi.org/10.1007/BF01418933. Displayed statement verified independently; original proof not re-proved. This note compares with CCM_Q10_MEAN_SQUARE_RETURN.md, not the unrelated CF22 Q10_SHORT_BOX_MOMENT_INTERFACE.md. No route closure or new arithmetic estimate.
