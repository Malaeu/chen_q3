# Growth answer10: parity return paid, weighted even-shift estimate stalled

Exact answer: PROSHKA_PARITY_PRIME_INLINE_2026-10-06.md.
Exact question10: ADDITIVE_CRT_AUDIT_2026-10-06.md.
Same full complex CCM carrier and original eventual family. No RH assumption.
Proof of CCM Growth has exhausted 10/10 questions. Forced same-phase rollover.

## Accepted result and narrow stall

Lambda=e_o+w2+p2, e_o=1_odd(Lambda-2), w2=2*1_odd,
p2=log(2)*1_(powers of two), is exact with all prime powers.
The discrete-wheel mean returns to the ORIGINAL continuous source via
 Dtilde_U(x)=D_U(x)+x^(-1/2)M_U(x),
 M_U(x)=int_(U<a<A0,a<x/U) d rho_U(a)/a, |M_U|<=1.
Indeed the upper trace costs U/A, and the integral costs
U int_U^A a^-2 da=1-U/A; rho_U(U)=0. Excluded upper uses left trace.
The wheel error is controlled on the entire original carrier by 4M_wheel,
 M_wheel=8192L h_U sqrt(A0)(Omega^(1/6)+1)
          +57344 h_U m^(1/4) A0^(1/4),
and powers of two cost Pi_m=24h_U sqrt(A0/U).
All joint d,h entries and cross-frequency terms are paid.

The residual R_*(v,f)=sum_(n>U) e_o(n)F_(v,f)(n)+Dcal(v,f), f=J_r v,
retains both short-factor product cutoffs and the corrected vector.
Odd-shift correlations vanish exactly. Even shifts contain
 Lambda(n)Lambda(n+2k)-2Lambda(n)-2Lambda(n+2k)+4
with the COMPLETE double-a weight. Both continuous mixed terms and all
cross-box terms remain in the exact squared aggregate. They are unestimated.
Using only |C_(ell,2k)|<=E_ell gives (N_ell+H-1)E_ell, minimized at H=1.
The resulting absolute fallback 42h_U L² sqrt(m)||v|| ||J_r v|| is weaker
than the accepted full-source bound. This is a limitation of this envelope,
not a lower bound for the actual sum and not a kill of all parity methods.

H_m(r)=rI-C_*+F10, ||F10||<=Delta10=Delta9+4M_wheel+Pi_m.
The actual Schur form differs from r||v||²-Re R_*(v,J_r v) by at most
Delta10||v|| ||J_r v||. The regular equation and all couplings are retained.
Delta10=O(m^(5/12)L^(3/2)log(2L)) is only a COMPONENT-ERROR budget.
No improved full bottom exponent, common good subsequence or SP follows.

## One independent pass and numerical clarification

growth_symbol_attempt checked §§1–2: parity/density signs, shifted-lattice
quadrature including low and high frequencies, curvature, variation masses,
dyadic constants, full-carrier map and powers-of-two budget. Pass with one
minor intermediate proof clarification: for K_*>=2, floor(K_*)>=2K_*/3.
Using this stronger floor inequality establishes the displayed 214 constant;
the stated weaker K>=K_*/2 alone would give about217.02, hence218 suffices.
The final quadrature constant1024 and all downstream budgets are unaffected.
The exact answer capture is preserved unchanged.
causal_algebra_audit checked §§3–6 and identity(28), conditional on §§1–2:
weights, separate product domains, parity coefficients, full square expansion,
optimized available envelope, actual Schur signs and cutoff z³. Pass.
For clarity, the two integration domains in (18) are respectively
 U<a<A0, Y0<=a(n+2k)<=m and U<a'<A0, Y0<=a'n<=m.
No endpoint smoothness or ||J_r|| bound was assumed. No Lean run.

## Own next attempt: exact finite convolution sectors

Let z=ceil((m/U)^(1/3)), mu_z=mu*1_(n<=z) (pointwise cutoff).
With Dirichlet convolution D_z=epsilon-mu_z*1, D_z(n)=0 for n<=z.
Therefore D_z^{*3} vanishes for n<=(z+1)^3-1, in particular n<=z³.
Convolving epsilon-D_z^{*3}=3(mu_z*1)-3(mu_z*1)^{*2}+(mu_z*1)^{*3}
with Lambda proves the exact Heath-Brown k=3 identity for every b<=m/U:
 Lambda(b)=3(mu_z*log)(b)-3(mu_z^{*2}*1*log)(b)
            +(mu_z^{*3}*1^{*2}*log)(b).
Consequently, writing c1=3,c2=-3,c3=1 and Q=d1...dj n1...n_(j-1)u,
 R_*(v,f)=sum_(j=1..3)cj sum_(all factors odd,di<=z,U<Q<=m/U)
 [mu(d1)...mu(dj)log(u)F_(v,f)(Q)]
 -2 sum_(U<b<=m/U,b odd)F_(v,f)(b)+Dcal(v,f).
The definition of F supplies every original a/product cutoff; no new domain
or continuous replacement has been inserted. This is linear, before squaring.

For any T>=1, the sector with ALL j free factors n_i,u<=T satisfies
 Q<=z^j T^j. Thus Q>z^j T^j forces a free factor>T, but the j=3 term
has no automatic such conclusion on Q<=m/U<=z³. Long total product does
not imply a long FREE factor; the long variables can carry Möbius weights.
Concrete individual tuple: choose an odd prime z/4<p<=z/2, set
 d1=d2=d3=p, n1=n2=1,u=3. Its coefficient is -log3, Q=3p³,
 3z³/64<Q<=3z³/8<m/U eventually, while every free factor<=3.
Bertrand supplies p eventually; the ceiling in z does not change the last
strict inequality because (m/U)/z³ tends to1.
This is an obstruction ONLY to the automatic-free-factor argument.
It is not a nonzero lower bound for a full sector or the CCM source: different
representations and j-terms can cancel. The actual F may also vanish.

Next test: preserve those Möbius-weighted sectors and the exact compensator;
execute a joint finite multilinear estimate, with explicit free-factor
quadrature errors and the remaining coefficient-weighted sectors. A source
bound must return through the same actual Schur identity. No shifted-prime
conjecture or independent positive envelope is available.

causal_algebra_audit independently checked this own sector lemma once:
expansion, odd support, threshold, Bertrand tuple, ceiling asymptotic and
Q>U eventually all pass. It checks only the stated structural obstruction;
no full-sector lower bound or noncancellation is inferred.
