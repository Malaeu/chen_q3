# Local continuation during Q55 delivery failure: center inside the first Gram square

2026-10-27. Root derivation, bounded check pending. Q55 retry has NOT been
performed or authorized. This note is not an external response or new exponent.
Original P, all complex source coefficients, full Lambda and both cutoffs retained.

Q54 has Phi_tau=sum_(d<=m) j_tau(d)||sum_(k<=m/d)(dk)^(-tau/2)r_(dk)||²,
where r_d=sum_(k<=m/d)mu(k)f(t+log(dk))/sqrt(dk). In particular j_tau(1)=1.
Call its first channel y_tau=sum_(d<=m)d^(-tau/2)r_d.
Finite divisor inversion gives y_0=f and y'_0=-D_m f/2, with actual
D_m f=sum_(n<=m)Lambda(n) f(t+log n)/sqrt n.
Let C_m f=int_1^m x^(-1/2)f(t+log x)dx, on the same whole real t line.

Replace ONLY the first square by ||y_tau+tau C_m f/2||². All other Jordan
squares remain unchanged and nonnegative for tau>=0. Thus exactly

 Psi_tau=Phi_tau+tau Re<y_tau,C_m f>+tau²||C_m f||²/4 >=0.
 Psi_0=||f||²,
 Psi'_0=h_m||f||²-(A[f]-A_cont[f])/2,
 A_cont[f]=2Re<f,C_m f>.

The three continuous terms have not been separately discarded. In particular

 Psi''_0 = Phi''_0-Re<D_m f,C_m f>+||C_m f||²/2
         = ||(D_m-C_m)f||²/2 + E_endpoint[f],

where E_endpoint is EXACTLY the three nonsquare terms in the reviewed
CCM_POST_Q54_ENDPOINT_SEAM_CANDIDATE.md. Its full absolute allowance is
O(sqrt(m)(1+L)^2+(1+L)^3)||f||², not a new arithmetic gain.

## Continuous first-form return

Both original exponential contacts imply
int exp(±u/2)f(u)du=0. The symmetric kernel of A_cont is exp(|u-t|/2)
on [0,L]². Its sum with exp(-|u-t|/2) equals 2cosh((u-t)/2), whose
quadratic form vanishes by those two contacts. Hence A_cont equals minus
the quadratic form of exp(-|u-t|/2). The latter has nonnegative Fourier
multiplier 1/(xi²+1/4) under the angular-frequency convention. Therefore

 -4||f||² <= A_cont[f] <=0.

This is a continuous contact identity, not cancellation of actual primes.
It includes both time orientations and needs no approximate projector.
Bounding A-A_cont above suffices for A, with no additional positive fee.

## Full finite-parameter obligation remains

With R^Psi_tau=int_0^tau(tau-s)Psi''_s ds, exactly

 A-A_cont=2h_m||f||²+(2/tau)(||f||²-Psi_tau+R^Psi_tau).

Positivity alone still does not bound the derivative. Dropping -Psi_tau
requires an independent upper bound on the FULL R^Psi_tau, not just the
centered endpoint square. Mixed terms at positive s and every higher-prime
support remain. Treating R^Psi_tau-Psi_tau as an assumed small supplier
would merely rewrite the original open source bound.

The old fixed compact seam family no longer proves a cm lower bound for
Psi''_0: PNT gives (D_m-C_m)f=o(sqrt m) for that fixed translated profile,
and E_endpoint=o(m). This only removes that particular obstruction;
it supplies neither a uniform rate on original P nor eta(epsilon)->0.
General ||D_m-C_m||<=C sqrt m still pays half power after Taylor completion.
No new source improvement, no new RH claim. This follows through the already
sent Q55 question locally, not a second independent failed attempt.

For an explicit full fallback, 0<=s<=1 and ||C_m||<=2sqrt m give

 Psi''_s<=Ctilde_m||f||²,
 Ctilde_m=m[4L²(1+L)²+4L(1+L)+L²(1+L)+2].

Indeed Psi''=Phi''+2Re<y',Cf>+s Re<y'',Cf>+||Cf||²/2,
with ||y'||<=sqrt m L(1+L)||f|| and
||y''||<=sqrt m L²(1+L)||f||/2. Every mixed term is included.
For tau=sqrt(2/Ctilde_m)<=1 the resulting A cap is
s_trial=2h_m+2sqrt(2 Ctilde_m)=O(sqrt m (1+L)^2).
Thus T_>R<=(s_trial+bdiv)P and PK_mP>=-(s_trial+50L+8)P.
Retain the better independent fallback; do not add this price to it.
