# Own attempt: exact joint Mellin product, before any norm

Consumer: rollover Q1 Eq17, complete tau_V pairing on(v,J_rv), not TV.
This is finite algebra, not an analytic estimate or a new supplier.
Let T_X retain coefficients of odd n<=X in finite Dirichlet polynomials.
Then T_X(M_X N_X)=1 and differentiation preserves coefficient support.
Consequently the proposed beta polynomial satisfies
 T_X[-M_X N_V'+M_X'(N_X-N_V)]
 =T_X[-M_X N_X'-(M_X N_V)'].
The first summand has coefficient Lambda(n), the second has coefficient
 log(n) sum_(du=n,u<=V)mu(d). This gives the accepted beta identity.
It is not a pointwise identity after deleting T_X: products have support
up to X², whose tail is generally nonzero. No M_X=1/zeta substitution.

There is an exact operator realization that keeps this cutoff automatically.
On L²[0,logX], take zero-filled right shifts S_s. Set
 M=sum_(odd d<=X)mu(d)/sqrt(d) S_logd,
 N=sum_(odd u<=X)1/sqrt(u) S_logu,
 N_V=sum_(odd u<=V)1/sqrt(u) S_logu,
 and Df(t)=t f(t). Since S_s S_t=S_(s+t) and S_logX=0,
 MN=I exactly. Let Q=M N_V-I=-M(N-N_V). Its shift support is >logV;
 V²>=X implies Q²=0. Thus I+Q has exact inverse I-Q.
Writing P=M[D,N], the beta operator is
 B_beta=M[D,N_V]-[D,M](N-N_V)
       =P+[D,Q].
Indeed [D,M]N+M[D,N]=[D,I]=0. The coefficient of [D,Q] is
 log(n)/sqrt(n) sum_(du=n,u<=V)mu(d), with its n=1 contribution zero.
This causal identity represents b-coefficients only; the original a-flux,
continuous density and carrier embedding still have to be applied.

Nilpotence alone supplies no small self-adjoint commutator. For a projection
Pi, (Pi Q Pi)^2=-Pi Q(I-Pi)Q Pi: intermediate projection leakage remains.
In a two-dimensional negative control, D=diag(0,H), Q=c e_21, H>0,
Q²=0 and [D,Q]+[D,Q]* has eigenvalues +/-H|c|. Thus exact inverse and
triangular support alone cannot imply a uniform small lower bound.
This is an abstract control, not an arithmetic counterexample to SP.

Outcome: the joint product can be preserved exactly; bare finite inversion
and nilpotence do not yet estimate it. Next test must use the actual signed
Möbius coefficients AND compensator, with all cross modes and cutoff tails.
Do not rerun the already killed uniform inverse-norm causal dressing.

Independent bounded pass: causal_algebra_audit verified all displayed algebra,
shift endpoints, projected leakage and the two-dimensional control. The
auxiliary interval is explicitly not a carrier-transfer theorem.
