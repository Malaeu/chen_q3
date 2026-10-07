# Own waiting-time refinement: exact cross-sector cancellation

PAPER own derivation, independently checked once. No full-sector norm or RH claim.
This refines the pre-question1 tuple in PARITY_PRIME_AUDIT_2026-10-06.md.
Do not send an extra question while rollover question1 is being processed.

Let X=m/U, z=ceil(X^(1/3)), and choose an odd prime z/4<p<=z/2.
For all sufficiently late cells, p>3 and b=3p³ satisfies U<b<=X.
In the exact k3 Heath-Brown identity, define H_short(b) as the signed sum
of ALL representations for j=1,2,3 whose j free factors n_i,u are <=3,
including coefficients c1=3,c2=-3,c3=1. Then
 H_short(3p³)=-log3,
 H_long(3p³)=+log3,
where H_long is the exact complementary sum (some free factor>3).

Proof. A nonzero logarithmic weight has u=2 or3. Since b is odd, u=3.
Every free factor is odd and <=3, thus is1 or3. The product b has exactly
one factor3, already used by u. Therefore all other free factors are1.
The Möbius-weighted product d1...dj must equal p³. For a nonzero term,
each di is squarefree, so each di is1 orp. Thus j=1 or2 is impossible,
and j=3 forces d1=d2=d3=p. This tuple satisfies the truncations di<=z,
and contributes mu(p)^3 log3=-log3. It is the only nonzero short tuple.
The full identity is Lambda(3p³)=0 because p!=3, hence the complementary
signed sum is +log3 exactly. No asymptotic prime-pair input is used.
The required p exists eventually by Bertrand, as in the audited tuple lemma.

This is stronger than the existence of an individual nonzero representation:
a complete coefficient sector is explicitly nonzero, and its cancellation
by the complementary sector is exact on these integers. However, it does
NOT imply a lower bound for the source-weighted sum or its operator norm.
F_(v,J_rv)(3p³) may vanish, and other integers may cancel in the source.
It also does not refute joint estimates for the actual Möbius coefficients.

For the parity residual coefficient e_o(b)=Lambda(b)-2 on odd b, the complete
pointwise coefficient is -2 here: -log3+log3-2=-2. The baseline remains.
The continuous compensator and actual Schur transfer are unchanged.
Use this as a source-specific discrimination test for any future sector
estimate: do not silently discard H_short or turn independent absolute
budgets for H_short/H_long into a claim about the coherent signed source.

Independent bounded pass: causal_algebra_audit checked uniqueness of the
short tuple, coefficients, exact complementary cancellation, Bertrand and
the eventual ceiling/product range. Pass; same narrow scope as above.

## Growing cutoff refinement (root derivation)

For every sufficiently large X and every real T with
 6<=T<=X^(1/4)/4,
there are odd distinct primes q,p with T/2<q<=T<p<=z such that
 X/64<b=q p³<=X/8,
 H_short,T(b)=-log q and H_long,T(b)=+log q.
Here H_short,T uses ALL j terms with every free factor<=T.

Proof: Bertrand supplies q in(T/2,T]. Set R=(X/q)^(1/3) and choose
p in(R/4,R/2]. Since X>=256T^4 and q<=T, R/4>=256^(1/3)T/4>T.
Thus p>T>=q, and p<=R/2<=X^(1/3)/2<=z. The product bounds follow.
Each free factor divides qp³ and is<=T<p, so is1 orq. Nonzero log weight
forces u=q; the other free factors are1. All p³ must lie in squarefree
Möbius factors, forcing exactly j=3 and d1=d2=d3=p. The same uniqueness
argument gives -log q, and Lambda(qp³)=0 gives the complementary +log q.
For the CCM relation X=m/U this b>U eventually. The claim is uniform over
this T-range, but makes no claim for larger T or an operator lower bound.

Hence all-free-short coefficients do not vanish merely by recombining the
three HB orders, even for these growing cutoffs. Their cancellation with
long-free coefficients must be respected. This does not show that the
complete weighted short sector lacks its own cancellation across b.

Independent bounded check of this refinement: causal_algebra_audit verified
uniform T-range, both Bertrand choices, constant256, product support and
unique surviving short tuple. Pass with the stated coefficient-only scope.
