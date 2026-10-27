# Q54: positive GCD deformation, full source tangent and curvature return

2026-10-27. Full original81134bytes1313LF read including code; SHA256
f2f6684f985e6691ca277b29718520a9db815cf2fde624af107eb9cde9ab0da0.
Independent q54_bounded_audit qualified PAPER PASS §§3–8, no material
findings, bound to that hash and request29975f46faee9550eea39e6de9048f0c73f9e483d1522ebfed9a32003651ce6a.
Upstream source and receiver inherited, not whole-chain recertification.
Independent q54_replay completed: all four asset hashes match; checker executed;
q54_checks.json is byte-identical to the embedded original. Assets in q54_replay/.
Finite exact rational controls only. No production spectrum, Lean or Arb.

## Exact arithmetic input and source return

Keep original P,N=m,L=log m,M=R=floor(m^epsilon), fixed0<epsilon<1/32.
E_nd=1_(d|n), U_nd=1_(d|n)mu(n/d), UE=EU=I.
For tau>=0, j_tau(n)=sum_(d|n)mu(n/d)d^tau
=n^tau product_(p|n)(1-p^(-tau))>=0, with j_tau(1)=1.
Q_tau(n,k)=(gcd(n,k)/sqrt(nk))^tau has its exact positive divisor Gram.
V_tau=U Q_tau U^T>=0. All indices through m are included.
V_0=e1e1^T; Vprime_0=diag(Lambda)-(lambda e1^T+e1 lambda^T)/2.
Normalization derivatives are essential for the offdiagonal source.

For one original complex f=I c, c=Pc, zero extended on R,
x_n(t)=f(t+log n)/sqrt(n), r=U^T x.
Phi_tau=int x*V_tau x=int r*Q_tau r>=0.
The source identities are exactly
 Phi_0=||f||², Phi_prime_0=h_m||f||²-A_m[f]/2,
 h_m=sum_(n<=m)Lambda(n)/n<=L+3.
Arithmetic rank-one baseline pulls back to the whole original identity;
it is NOT a contact direction killed by P. No free tangent sign follows.
The free arithmetic-index negative tangent control is not a P-counterexample.

## Signed second derivative and paid completion

d_de=log(sqrt(de)/gcd(d,e)), 0<=d_de<=L.
Phi_second_s=int sum_(d,e)conj(r_d)r_e d_de² exp(-s d_de).
Expanding r retains real mu(k)mu(l), both dk,el<=m boundaries and ALL
rational-ratio correlations I_(el/(dk)), including noninteger ratios.
These cannot be removed as if only prime-power ratios remained.
Finite Taylor remainder R_tau=int_0^tau(tau-s)Phi_second_s ds yields
 A=2h_m||f||²+(2/tau)(||f||²-Phi_tau+R_tau).
The available absolute completion gives
 Phi_second_s<=C_m||f||², C_m=4mL²(1+L)² for all s>=0.
At common tau=1/[sqrt(2m)L(1+L)], the full trial is
 s_trial=2L+6+4sqrt(2m)L(1+L).
It retains half power, worse than the inherited fallback. This is an upper
allowance, not a lower bound for actual curvature or CCM. Optimizing tau
inside this same allowance cannot supply a vanishing exponent.

An independent one-sided curvature upper Oepsilon(m^(2kappa)) uniformly
for0<=s<=m^(-kappa), kappa(epsilon)->0, would suffice; it remains OPEN.
A joint R_tau-Phi_tau estimate is weaker but by the exact formula merely
rewrites the source target; it is not a new independent supplier.
GCD distance can be large for nearby coprime integers whose physical log
ratio is small, so physical smoothness alone does not pay all d_de².

## Consumer and decision

Trial T_>R<=(s_trial+bdiv)P, PK_mP>=-(s_trial+50L+8)P.
No new contour/high/entire fees because this is a direct A return.
Retain s_keep<=6sqrt(m)+6m^(1/4), with short fee only in T and arch once
in K. Do not add trial prices to this independent fallback.
No new full exponent, no actual-source no-go, all-P goal and RH OPEN.
Rollback before absolute curvature. A next bounded test must use the exact
joint mu/GCD correlations on the source image, not positivity of Phi alone
or the same derivative under a new name. No Q55 dispatched.
AUTOPSY: dropped=NO_DERIVATION; note=Positive arithmetic family has nonzero original-P baseline; full signed curvature remains unpaid at vanishing exponent.

## Primary-source check

Root verified Guillot–Wu §1.1 Theorem1.2 and its divisor-factorization
argument at https://arxiv.org/html/1901.01947 ; it motivates the finite Gram
only, not total positivity or a source bound. DLMF27.5.2,27.5.3,27.5.5 at
https://dlmf.nist.gov/27.5 confirm the inversion/divisor identities.
The real-parameter normalized construction and its source transfer are
proved in Q54 and covered by the bounded review, not imported from a
claimed external CCM theorem.
