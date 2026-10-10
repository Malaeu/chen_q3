# Q2 smooth-sector mask test

2026-10-10. Bounded root attempt, independently checked by smooth_projection_test. No new full bound. P/M remain conditional; RH/SP/MB34 OPEN. Source: PROSHKA_VERDICT_ACTUAL_PRIME_LAYER_Q02.md, PLQ7, PLQ23–28 and pinned P-plain contract.

## Exact operation and cost

On q_n<=beta L, let B_Y be the product of all good primes with Y<q_p<=beta L. The smooth indicator is exactly 1_(n,B_Y)=1. This is not automatically an admissible P mask: the source requires q_B<=U^B for a fixed exponent, while this construction supplies no such bound. Merely fixing the mask within each row sum is insufficient.

Use instead the exact divisor expansion 1_smooth(n)=sum_(d|n, all p|d have q_p>Y)mu(d), with squarefree d and d=1 retained. Each surviving label has q_d<=beta L, hence its individual ad mask has polynomial norm. On the late band beta L<Y^6 every label has at most five prime factors. This finite tier count does not bound the total number of labels.

With V_1=R_sf, PLQ23 gives exactly R0=sum_d mu(d)V_d and ||R0||²=sum_(d,e)mu(d)mu(e)<V_d,V_e>. Every cross term remains. For d>1, ||V_d||²<<PU/q_d times losses; for d=1, ||V_1||²<<P(U+U^(1/6)L^(5/6)) times losses. Minkowski and ideal counting sum_(q_d<=beta L)q_d^(-1/2)<<sqrt(L) give only ||R0||²<<PUL times losses. Relative to H U^(-1/200), this envelope costs U^(ell-5p+1/200), with minimum exponent38059/37500 on the full band. This compares upper envelopes, not actual lower bounds.

Small-prime support does not force rY to vanish. Algebraic control using distinct good prime ideals of norms7 and13, Y=13: S_Y=1−2−2=−3, mu(n)=1, hence rY(n)=−2. This is a coefficient diagnostic, not a source-band counterexample. Root checked the smooth inclusion-exclusion identity for all15 nonempty subsets of norms7,13,19,31; finite identities do not establish cofinal cancellation.

## Decision

Direct one-mask invocation of P is unlicensed without its polynomial norm hypothesis. Expanding into licensed masks returns the same unpaid signed Gram correlation. The termwise smooth-sieve attempt is STALLED, not a refutation of the smooth-sector estimate or MB34. CF22 remains the best full bound. No new Pro request sent.

Return point: actual PLQ24 combines the smooth vector and the entire signed incidence Gram matrix. Next search must supply cancellation for this joint arithmetic family, not a bound for each vector or a density heuristic. Alternative search dictionaries: restricted character large sieve on friable coefficients; signed divisor-incidence Gram forms; Buchstab decomposition with bilinear cross control. These are UNVERIFIED leads, not imported estimates.
