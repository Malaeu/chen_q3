# Q18 own attempt — transfer the pole filter before taking absolute values

2026-10-25. Original finite m=N,L=log m,M=floor(m^epsilon), same three-contact
P, fixed0<epsilon<1/32. This is a source-specific test after Q17, not a new
arithmetic exponent. Conditional source pair uses fixed w=delta+i gamma,
0<delta<1/2, multiplicity r, partner v=-conjugate(w), separate c_w,c_v.
Sources: full Q17 verdict §§1,6,8–10; its inherited source G=-4Phi and receiver.

## Exact signed transfer at finite prime cutoff

Put B=D²-1/4, F0=B G, R_G(y)=integral conjugate(G(t))G(t+y)dt.
All fixed derivatives have the inherited double-exponential tails. Integration
by parts in t (with vanishing endpoint traces) gives R0=B_y² R_G.
Define the full finite source
 H_G,m(y)=sum_(2<=n<=m) Lambda(n)/sqrt(n)
                       [R_G(y-log n)+R_G(y+log n)].
Then H_m=B_y² H_G,m EXACTLY. No n, proper prime power, time direction or
mixed translate has been omitted. This is not a diagonal approximation.
The actual source is checked in
../routeB_bus/proshka/PROSHKA_FULL_THETA_THREE_POINT_CLOSURE_2026-09-17.md §1:
 Phi(t)=sum_(j>=1)(4pi²j^4 exp(9t/2)-6pi j² exp(5t/2))exp(-pi j² exp(2t)).
Each term is positive for t>=0 and Jacobi reflection gives Phi(-t)=Phi(t).
Thus G=-4Phi<0 and R_G(y)>0 for every real y. This is actual pointwise
positivity, not an inference from positive Fourier definiteness.
Also M_G(z)=-4xi(1/2+z) is strictly negative for real z by this integral,
so a hypothetical zero w in this construction necessarily has gamma!=0.
Evenness/reality imply c_v=(-1)^r conjugate(c_w), but therefore
kappa=1/conjugate(c_w)^2, NOT1/|c_w|². The constant phase must stay.
We retain both constants below to prevent that erroneous phase deletion.

Write b=conjugate(w), p_r(u)=u^(2r-1)/(2r-1)!, k(u)=exp(-b u)p_r(u),
H(u)=H_G,m(y+u), kappa=(-1)^r/(conjugate(c_w)c_v).
The exact finite-horizon identity is

 integral_0^U k B²H = integral_0^U (B²k)H + F(U)-F(0),         (1)
 F(u)=k H'''-k' H''+k'' H'-k'''H -(k H'-k'H)/2.

Since m is finite, H and every fixed derivative decay double-exponentially
as u tends to infinity. Thus F(infinity)=0 with no infinite-prime exchange.
The Q17 finite-prime resolvent therefore becomes

 J(y/2;m)=kappa [ E_r(y;m)+integral_0^infinity exp(-b u)q_r(u)H_G,m(y+u)du ], (2)
 q_r=(b²-1/4)²p_r -4b(b²-1/4)p_r'
                         +(6b²-1/2)p_r''-4bp_r'''+p_r'''',
 E_1=H_G,m''+2b H_G,m'+(3b²-1/2)H_G,m,
 E_2=H_G,m,
 E_r=0 for r>=3.                                           (3)

All E_r are evaluated at y; they are not optional contact corrections.
For finite U the upper F(U) also remains; it is not zero by a pole condition.
In (2) y=2a and the target is Re(exp(2i gamma a)J). The full pair still has
 S_m[f_a]=S_m[g]+S_m[k]-2Re(exp(2i gamma a)J), self terms O_w(1).
Thus a LOWER bound on this real combination is required. Neither its endpoint
nor its integral can be assigned a favorable sign independently.

## Concrete sign test before an absolute completion

The leading coefficient of q_r is (b²-1/4)²/(2r-1)!, nonzero for the stated w.
For gamma!=0, the REAL kernel multiplying nonnegative H_G,m in the integral is
 Re(exp(2i gamma a)kappa exp(-b u)q_r(u)).                    (4)
Its leading term is a nonzero constant times
 exp(-delta u)u^(2r-1)cos(gamma u+theta), with relative error O_w(1/u).
Consequently it takes both signs on arbitrarily late intervals. This follows
by evaluating at successive maxima/minima of the cosine, not a numerical
assignment of a hypothetical zero. A fixed-sign theta source cannot by itself
make (4) nonnegative. The exclusion of gamma=0 here uses the checked positive-theta integral
above, not an unstated numerical-zero assumption.

This rejects the attempted automatic positivity argument, not an inequality
for the particular H_G,m: its arithmetic structure may correlate with (4).
For r=1,2 the explicit E_r must also be paid jointly. For r>=3 their absence
does not cure the signed bulk. No all-source or actual-spectrum no-go follows.

## Completed budget, including all endpoints

Set W(m)=sum_(n<=m)Lambda(n)/sqrt(n)<=6sqrt(m),
 G_j=||G||_2||G^(j)||_2 (j=0,1,2),
 I_r(b)=integral_0^infinity exp(-delta u)|q_r(u)|du < infinity,
 C_1=G_2+2|b|G_1+|3b²-1/2|G_0; C_2=G_0; C_r=0 (r>=3).
Cauchy-Schwarz is applied only at this final, explicitly recorded failure:
 |H_G,m^(j)(y)|<=2W(m)G_j.
Hence the FULL return of (2), endpoints included, is
 |J(a;m)|<=2|kappa| W(m)[C_r+G_0 I_r(b)]
         <=12|kappa|[C_r+G_0 I_r(b)]sqrt(m).                 (5)
Every constant depends only on the fixed actual source and fixed w,r.
This is no better in power than Q17 and worse than its profile-local price.
It is not a lower bound on actual |J|. No independent sector Cauchy square
or dropped mixed term was used before the final completion.

A finite implementation may use U=L-2a+2log L. For a in [h-T,h],
h=L/2-log L,1<=T<=h/2, the upper F(U) and integral tail in (2) are bounded
by C_w sqrt(m)(1+L)^C_r exp(-c_w L²)=o(1), using derivative tails of R_G.
Thus numerical cutoff does not hide an unpaid endpoint. There is NO exchange
with an infinite prime sum; the absolute interchange excluded by Q17 remains
forbidden. No improper radical transfer is used.

## Same original P and final consumer

All manipulations above are on the actual pre-projection pair. Return it as
a WHOLE by the accepted cutoff/Fourier/three-contact receiver, with one fixed
q>1/epsilon+2. The unchanged rho_K,rho_S in Q17§8 are o(1), uniformly in a.
No commutation of P with B or its inverse is assumed. All projection mixed
terms are in these full-form errors, not individually reset to zero.
Bounded source norms give archimedean price D_w(50L+8) ONCE.
Thus (5) gives only average K >= -C_w sqrt(m)-D_w(50L+8)-o(1).
Inherited sharper completion remains
 average K >= -C'_w[sqrt(m)/(L T)+L+1]-o(1).
At T comparable to L, this costs sqrt(m)/L², versus conditional adverse signal
E_T comparable to m^delta/L^(2delta+1). Power deficit1/2-delta persists.
No short-sector fee belongs to direct K; no ZF78 assumption introduced.

## Precise impasse for Q18

The theta differential filter can be transferred exactly with every endpoint.
The resulting nonnegative-source route (when G sign is verified) does NOT
supply a sign: coefficient (4) oscillates, and the r=1,2 endpoints are real
obligations. Taking its modulus returns (5). The missing line is a JOINT lower
bound on Re(exp(2i gamma a)kappa[E_r+integral exp(-bu)q_r H_G,m]),
independently of the adverse zero formula, sufficient to be -o(E_T) after
averaging. Merely writing this target is not a new mechanism.
A candidate for Pro to TEST, not to assume: exploit the explicit theta-series
inside R_G and group its two theta indices with the actual finite prime
translation before summation, retaining (1)'s endpoint polynomial. Determine
whether the actual dilation/divisibility structure yields a sign comparison
between the negative and positive lobes of (4), or identify its full paid
obstruction. Generic Fourier positivity/heat smoothing and absolute PNT were
already tested in CCM_Q09_AUTOCORRELATION_PREFLIGHT.md and
CCM_COMPOSITE_HEAT_RETURN.md; do not relabel them as new work.
No new favorable exponent, RH, actual off-line zero, Lean or Arb claim.

## Concrete arithmetic entrance for Q18, not a promised estimate

Let phi_j(t) be the exact theta summand displayed above. Direct rescaling gives
 n^(-1/2) phi_j(t+log n)=phi_(nj)(t).
Consequently, with a finite n-cutoff and locally normally convergent theta sums,
 G_m^+(t):=sum_(2<=n<=m)Lambda(n)/sqrt(n) G(t+log n)
          =-4 sum_(k>=1) d_m(k)phi_k(t),
 d_m(k)=sum_(n|k,2<=n<=m)Lambda(n).
In particular d_m(k)=log k for k<=m, while for k>m
 d_m(k)=log k-sum_(n|k,n>m)Lambda(n).
Both original time signs are retained by the exact identity
 H_G,m(y)=integral [G(t)G_m^+(t+y)+G_m^+(t)G(t+y)]dt.          (6)
The second term follows by a translation of the integration variable in
R_G(y-log n); it is not discarded by parity. Formula (6) uses a finite n-sum;
the displayed theta-series equality is pointwise/local. No exchange of an
infinite arithmetic sum with the resolvent, or unpaid global absolute theta
integral, is authorized. At negative t the individual phi_k can have either
sign even though their full sum is positive.

This is a specific finite divisor-weighted theta source to investigate:
apply Jacobi/scale pairing to the ACTUAL d_m(k), keeping its k>m tail and the
whole (6), then insert into (1)-(3) with the complex kappa and both endpoints.
Replacing d_m by log k everywhere would change the source. A proof must pay
the resulting moving theta-index edge; the infinite unweighted Jacobi identity
alone is already known and not an arithmetic gain. No bound for that new
weighted transformation is asserted here; Q18 asks to test this precise map.

## Checks and limits

q18_theta_source bounded read-only PAPER check: PASS on (1)-(5), theta
positivity, retained normalization phase and the exact scope of the sign test.
A mistaken candidate simplification of kappa to a modulus square was caught
before use; the archived derivation keeps 1/conjugate(c_w)^2 or separate c's.
q18_theta_checks/check.py verifies the finite Green identity, all lower
endpoints and q_r for r=1,...,6, and a negative control for phase loss.
These are finite algebra controls, not a universal arithmetic proof.
Root derives (6) directly from the literal theta series; its weighted-Jacobi
inequality remains the concrete next question, not a completed mechanism.
Incremental independent check of new (6): scaling, finite divisor weights and
both time directions PASS. For local normal convergence use
0<=d_m(k)<=psi(m)=sum_(n<=m)Lambda(n), a constant at fixed m; it is NOT bounded
by the differently weighted W(m) without an extra sqrt(m) factor.
The compact-t Gaussian majorant then suffices; no global interchange claimed.
Exact local controls:21 PASS (SymPy1.14.0); no source numerical evaluations.
