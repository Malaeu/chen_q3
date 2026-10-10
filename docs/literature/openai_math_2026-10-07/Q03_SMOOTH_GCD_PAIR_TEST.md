# Q3 no-common-large-prime pair test

2026-10-10. Bounded algebraic discriminator; no new analytic estimate.
Independent read-only q03_pair_supplier_map: PASS for formulas, finite
nondeletion and hypothetical budget; no analytic supplier admitted.
Source: PROSHKA_VERDICT_SIGNED_INCIDENCE_Q03.md, SI.10–SI.12.
Consumer remains the complete signed C_Y and original MB34 return.

For squarefree good ideals n,m write n=gx,m=gy with g,x,y pairwise
coprime and squarefree. The condition k_Y(n,m)=0 is exactly that g
is Y-smooth. It does not restrict the large prime factors of x or y.
The character product is

    psi_u(gx) conjugate(psi_u(gy))
      =1_((u,g)=1) psi_u(x) conjugate(psi_u(y)).

The canceled g character leaves its zero mask. The amplifier weight is
w_P(gxy). The two windows remain W(qg qx/L) conjugate(W(qg qy/L));
neither may be replaced by their product support alone. Every original
sixth-free element row, unit, S-valuation and amplifier power remains.
The pair coefficient is r_Y(gx) r_Y(gy)/L, not mu(xy)/L.
Writing S_z(x)=sum_(d|x,qd<=z)(mu*mu)(d), it obeys exactly

    r_Y(gx)=mu(g)mu(x)+sum_(d|g)(mu*mu)(d) S_(Y/qd)(x).

This follows by uniquely splitting a divisor of gx into divisors of the
coprime factors g,x. On squarefree divisors (mu*mu)(d)=(-2)^omega(d).
An ephemeral exact-integer check covered all 16 splits of {7,13,19,31}
and Y in {1,10,20,100,1000}: 80 equalities passed. This checks the
algebra, not the analytic estimate.

The active primitive character on the good coprime factors x,y has
conductor xy (local exponents +1,-1, up to fixed orientation). Its norm
is qn qm/qg^2, with the separate g zero mask retained. In particular
g=1 is allowed. Smoothness of g gives no lower bound on qg, hence no
uniform shortening of this conductor.

The existing Q3 finite cell makes nondeletion concrete: U=23^6,
L=1415177965; take four distinct split-prime ideals of norms
37657,38377,38449,38557. Pair the first two into n, the last two into m.
Their norms are 1445162689 and 1482478093, respectively 1.02119L and
1.04756L, both in the original finite witness profile. Every prime norm
exceeds Y=U^(1/5). Thus g=1, S_Y(n)=S_Y(m)=1 and r_Y(n)=r_Y(m)=2.
The conductor norm is 2142422027263472077. These are actual nonzero
coefficients, not arbitrary replacements. This single cell asserts no
cofinal lower bound and no obstruction to cancellation after row summation.

Decision: do not use smooth gcd as a short-conductor hypothesis, and do
not reuse MB34_PRODUCT_PAIR_TEST.md's pure Mobius product coefficient for
this residual. Q09_CROSS_PRODUCT_CONDUCTOR_TEST.md already records why
absolute generic disjoint-product estimates are insufficient; its dual
frequency scale must not be identified with the present physical U.
Even granting the Q09 CF11 bound on physical rows of scale U, its
ratio to the trivial U envelope is min(1,sqrt(L/(U qg))). A power
saving would require qg>L/U by a power margin, which g=1 violates.
This is only a hypothetical budget comparison: CF11 has squarefree
rows, whereas our rows are sixth-power-free; that bridge is not supplied.
The remaining discriminator is a joint estimate retaining the above
cutoff convolution and both orientations before absolute values.
RH/SP/MB34 remain OPEN; CF22 unchanged. No new Pro request sent.

## Paid replacement by the pure Mobius pair (conditional)

Let M_d and R_d be the divisor-label vectors of M and R_sf, respectively,
on the identical row Hilbert space and with the same common W. Define
A(F)=sum_(d in D_Y) mu(d)||F_d||² and Q(F)=sum_d||F_d||².
Inclusion-exclusion gives B_empty(F)=E_F+A(F), including the smooth
sector. For the pure Mobius columns, exactly

    M_d(a,u)=mu(d) 1_((a,d)=1) psi_u(d)/sqrt(qd)
                 * M_u^[ad](L/qd;W).

This retains every zero, the cofactor mask, and the original window.
The identical M-old argument used in Q2 PLQ.23 bounds Q(M)<<PU*losses:
qd>Y, L/qd<U^(93/100), all five tiers are subsets of ideals and their
1/qd sum is logarithmic. Small scales have the inherited endpoint bound;
ad has fixed polynomial norm. Q(R)<<PU*losses was already paid in Q2.
Consequently, using E_M-E_R=J_sf from PLQ.17, exactly

    B_empty(M)-B_empty(R)=J_sf+A(M)-A(R),
    |B_empty(M)-B_empty(R)| <= |J_sf|+Q(M)+Q(R).

Thus the full pair functional can use mu(n)mu(m) in place of rY(n)rY(m)
only AFTER paying this explicit error, not by a pointwise substitution.
The bound is P[U+U^(7/12)L^(5/12)]*losses. Relative to H U^(-1/200),
the minimum power margins are 1783/18750 for PU and 1691/37500 for
J_sf over the full source band. The latter retains the old 257/75000
return reserve and a further 1/24. These are conditional on the SAME
P/M-old inputs and profile uniformity, not new certified source theorems.

Moreover C_Y=E_R-Q(R) gives the exact identity

    C_Y = B_empty(M)-J_sf-A(M)-Q(R).

Hence a target-sized upper bound for B_empty(M) would suffice with the
paid errors. But B_empty(M)=E_M+A(M)=E_M+O(PU*losses), so this is an
equivalent representation at the target scale, not a new moment gain.
The pure-Mobius product coordinates in MB34_PRODUCT_PAIR_TEST.md P1
can now be used for the off-diagonal with the additional smooth-g
restriction and this full error budget. B_empty(M) also includes the
smooth diagonal n=m=g (x=y=1); it is retained separately. Its absolute
cost is O(PU): each squared column is bounded by ||W||_infty²/L,
there are O(L) ideals in the fixed annulus, O(P) amplifiers, and total
nonnegative row weight O(U). Restricting to smooth ideals only decreases
this positive diagonal. Thus this is a separate paid term, not a deletion
by P1. Its reciprocal-L contour argument is still not paid.
Decision: do not ask for another cutoff-coefficient rearrangement alone;
a useful next supplier must improve the actual pure-Mobius joint moment
or its centered original return. RH/SP/MB34 and CF22 remain unchanged.

Independent q03_pair_supplier_map checked the replacement algebra, masks,
conditional trace bounds and margins. Its smooth-diagonal scope finding
is resolved by the explicit O(PU) ideal-counting bound above.
