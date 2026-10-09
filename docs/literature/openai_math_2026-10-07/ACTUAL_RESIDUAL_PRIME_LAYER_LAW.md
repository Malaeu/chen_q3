# Actual rY: prime layers with all character phases retained

2026-10-09. Own continuation after accepted short-box Q1 (79fbe292). Independent prime_layer_note_audit PL1–3 PASS, including cutoffs below1, all original masks and every cross-layer term. Algebraic interface only, no MB34/SP/RH gain. This applies the user's prime-layer idea to the actual remaining coefficient, rather than to its complete-residue mean.

## Exact coefficient transition

For every real t>0 define r_t(n)=mu(n)+sum_(d|n,qd<=t)c2(d), c2=mu*mu on original good ideals. For t<1 the sum is empty, so r_t(n)=mu(n), NOT zero. Let p be a good prime ideal, q=qp, and p not divide m. Write S_t(m)=sum_(d|m,qd<=t)c2(d). The exact local table c2(p^k)=1,−2,1,0,... gives

 r_Y(pm)=r_Y(m)−2r_(Y/q)(m),                         PL1
 r_Y(p^j m)=r_Y(m)−2r_(Y/q)(m)+r_(Y/q²)(m), j>=2.   PL2

Proof: divisors split as p^k d with d|m; their cutoff is qd<=Y/q^k. For j=1, mu(pm)=−mu(m); for j>=2, mu(p^j m)=0. Expanding the right sides yields exactly these values plus S_Y−2S_(Y/q) and S_Y−2S_(Y/q)+S_(Y/q²), respectively. Equal cutoffs retain <=, no limiting or asymptotic assertion.

Thus r_Y(p²m)−r_Y(pm)=r_(Y/q²)(m), and coefficients are constant across j>=2 at fixed p,m,Y. This constancy does not make the full source summands constant: their norm windows, phases, and support change. There is no assumption that r_t has a fixed sign. For example at m=1, r_t(1)=2 when t>=1 and1 otherwise; at a prime m of norm>t>=1, r_t(m)=0. For a prime m with qm<=t, r_t(m)=−2. For distinct primes q1<q2, r_Y(p1p2) takes values2,0,−2,2 across thresholds1,q1,q2,q1q2; no monotonicity in Y follows. These simple values are not mean-square estimates.

## Full source, without losing phases or powers

Keep original common W, all amplifier ideals a<=P, all sixthfree element rows u with rho>=0, and psi_u=nu chi_u in the accepted orientation. For a fixed good prime ideal p define

 F_j(a,u)=L^(-1/2) sum_(m good,p not dividing m) r_Y(p^j m) psi_u(m) 1_((m,a)=1) W(q^j qm/L).

Then exactly

 R(a,u)=F_0(a,u)+1_((p,a)=1) sum_(j>=1) psi_u(p)^j F_j(a,u).  PL3

All sums are finite by the original annular support. For p dividing the moving conductor, psi_u(p)=0, so positive layers vanish rather than acquiring a new artificial unit value. For p dividing a they vanish through the original amplifier mask. There is no added global (u,a)=1. Exponents j are unrestricted; the original six-power-free restriction is on u, not on the residual column n. psi_u(p)^0 in the j=0 term means1, including zero-character branches.

Set z_0=1 and z_j=1_((p,a)=1)psi_u(p)^j for j>=1. The exact positive energy is sum_(a,u)rho sum_(j,k>=0) z_j conjugate(z_k) F_j conjugate(F_k). No cross-layer term is dropped, and no positivity is assigned to it. Although PL2 stabilizes the scalar coefficient, it does not stabilize F_j, whose window is rescaled. The finite upper endpoint depends on L and q, and cannot be replaced by an infinite geometric sum with constant F_j.

## Consumer and stopping conclusion

Q1 SB25 needs the joint covariance of distinct sixth-power-free column cores with actual rY. PL1–3 give an exact computable local transition for that coefficient and full R, preserving both phase and cutoff data. They do not estimate the cross-layer quadratic form. To use them one must bound that form after all actual a,u,m sums, while retaining the already paid equal-core contribution and exact Q1 return to MB34. No independence of prime layers or monotonic decrease is proved. This is a sharper source-faithful input for the next question, not a replacement of the missing estimate by a recurrence assumption.

No extra Pro request sent. Same living chat Математическая попытка MB34, Q1 processed; Q2 remains unsent.
