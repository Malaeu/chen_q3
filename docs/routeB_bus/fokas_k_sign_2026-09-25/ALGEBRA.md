# Two-energy normalization audit (candidate, awaiting independent review)
Source HEAD ee99aacc; R3 of FULL_SCALAR_SIGN_CHAIN. No source object changed.

Let P[-1]=0, P[0]=1 and u_k P[k+1](e)=(e-d_k)P[k](e)-ell_k P[k-1](e), u_k nonzero.
The symmetric divided-difference polynomial S_k(e0,e4) satisfies
P_k(e0)-P_k(e4)=(e0-e4) S_k(e0,e4), including the polynomial extension on the diagonal.
It is constructed without division by a small gap:
S[-1]=S[0]=0,
u_k S[k+1]=P_k(e4)+(e0-d_k)S[k]-ell_k S[k-1].
Subtract the two P recurrences and induct. Equivalently subtract in the opposite order to show symmetry.

Put w=F(((-1)^k S_k)_{k=1}^N), Delta=e0-e4. Then z=Delta w.
For the literal complete quartic R3,
Pfull(e0,e4)=Delta^4 [(w*Pi w) w*(K-theta I)w +(w*w) w*Pi K Pi w].
The source remains x=kappa Delta w. No sign comes from Delta or kappa: their fourth powers are positive off the separated energy intervals.
A fixed change of this homogeneous scale leaves the source energy-sign test invariant; it cannot by itself improve its relative conditioning.

Assume K is Hermitian and theta=tr(Pi K Pi). For any z with X=||z||>0, Y=||Pi z||>0, Pi the rank-two orthogonal projector,
let v in range Pi be a unit vector perpendicular to Pi z. Rank-two trace gives
v*Kv=theta-(z*Pi K Pi z)/Y^2.
Consequently Pfull=X^2 Y^2 ( (z*Kz)/X^2 - v*Kv ).
This equality is a diagnostic cross-check for computing R3; it does not determine its sign.

Negative control: Pi=I_2, K=diag(0,1). At z=(1,0), Pfull=-1; at z=(0,1), Pfull=+1.
Thus neither K>=0, nor exact representation, nor residual zero gives a fixed sign without selecting the branch.

162 exact rational recurrence controls are in divided_difference_check.py. These are algebra controls, not spectral/source certificates.
