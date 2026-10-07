# Q1 audit extract — good-principal sector

Captured from the rendered complete attachment PROSHKA_VERDICT_JOINT_LOW_PROBE_Q01.md in https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd on 2026-10-07. This is a manually normalized mathematical extract, NOT the original file bytes. Browser download events timed out; complete rendered text was available. The full rendered answer was read; this extract is the local mathematical answer record. Root calculation and independent mobius_source_audit check PASS under the stated assumptions. Original byte-exact attachment archival remains unavailable. Source paper SHA256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3; request SHA256 d47d198f21d1ad97b0cffedf6fe87c501218f2c6c76f0d46bfb7e17398f18ce4.

Proshka claims the good-principal primal sector is exactly n=a^2, s=c*r^6, (r,c*a)=1, c squarefree. Shared primes of c,a are allowed. Its entire contribution is O_A(Z^-A) for every A>0. This is NOT the Poisson u=1 row and does not improve the full low exponent. Original equations (9)–(17) follow in normalized notation.

For fixed selected tuple and subset J: R=p_J, D=p_(J complement), d=sum_(i in J) ell_i; X_J=X/q_R, Y_J=Y/q_R, T_D=Z*q_D, Q_J=q_bstar*X_J*Y_J. All original slot weights retained. Here d is slot length, not the moving divisor in root parity notes. Gaussian V_G(x)=exp(-(log x)^2/4)/(2 sqrt(pi)); w_Q,v(m)=Omega(q_m/Q)(q_m/Q)^(-iv).

Mixed contraction:
M_J,D(v)=Y_J^-1 sum_s sum_(c sf,n) W1(r_s) r_s^(-1/2+iv) chi_s(bstar)/(tau xi(s))
 * gamma2(c) baralpha(A) eta(A) Xi(A)^-1 R(A,s) barG(A)/(sqrt(q_c) q_n)
 * 1_(D|A) V_G(q_A/T_D) K_QJ,v(s,A), A=c*n^3, r_s=q_s/Y_J.
K_Q,v(s,A)=sum_(m!=0) w_Q,v(m) xi(m) chi_A(m) q_s^-1/2 g_chis(s,-m).

Full probe: I_modified=(2pi)^-1 sum_tuples product Wi(q_pi/Z^ell_i)
 * sum_J (-1)^|J| q_R^-3/2 bareta(D) Q_J^-1/2 integral What0(iv) M_J,D(v) dv.

## Exact selection and coefficients

Unit projector is (1/6)sum_(epsilon in O*) xi(epsilon) chi_A(epsilon) barchi_s(epsilon), exactly zero or one. At a good p, write k=v_p(s), t=v_p(A), H=chi_p, P=q_p. Local factors (apart from m-independent CRT phase) are:
- k=t=0: 1.
- k=0,t>0: H(m)^t, zero mask retained.
- k=1,t>=0: gamma1(p) H(-1)^-1 H(m)^(t-1), zero mask retained even at exponent zero.
- k>=2,t>0: identically zero.
- k>=2,t=0,6 does not divide k: P^((k-1)/2) gamma_k(p) H(-m/p^(k-1))^-k 1_(v_p(m)=k-1).
- k>=2,t=0,6 divides k: P^(k/2)1_(p^k|m)-P^(k/2-1)1_(p^(k-1)|m).

Equation (9):
chi_(c*a^6)(m) q_(c*r^6)^(-1/2) g_chi_(c*r^6)(c*r^6,-m)
 = gamma1(c) chi_c(-1)^-1 1_((m,c*a)=1) q_r^3
   * sum_(e|rad(r)) mu(e)/q_e * 1_(r^6/e|m).

Equation (10): gamma1(c)gamma2(c)=mu(c)alpha(c)G(c);
R(c*a^6,c*r^6)=chi_c(-1); G(c*a^6)=G(c); Xi(a^6)=1; xi(r^6)=1.

Equation (11): E_v(T;L)=sum_(m!=0) Omega(q_m/T)(q_m/T)^(-iv) xi(m) 1_((m,L)=1).

Equation (12):
M^P_J,D(v)=(tau sqrt(Y_J))^-1 sum_(c sf,r,a; (r,c*a)=1)
 mu(c)eta(c)[baralpha(a)eta(a)]^6/[xi(c)^2 q_c q_a^2]
 * W1(q_c q_r^6/Y_J)(q_c q_r^6/Y_J)^(iv)
 * 1_(D|c*a) V_G(q_c q_a^6/T_D)
 * sum_(e|rad(r)) mu(e)xi(r^6/e)/q_e * E_v(Q_J q_e/q_r^6;c*a).

If xi is nontrivial on global units this sector is exactly zero. Otherwise the same fixed-character argument below applies.

## Claimed rapid-decay proof

(13) For every integer N>=1, if T/q_rad(L)>=1:
|E_v(T;L)| <= C_(N,xi,Omega) (1+|v|)^(2N+4) d_O(rad L) (T/q_rad(L))^-N.
Proof: expand coprimality by mu(f), f|rad L; substitute m=f*z. Inner sum is xi(z) Omega(q_z/U)(q_z/U)^-iv, U=T/q_f. Fixed primitive xi has zero mean mod bstar. Poisson gives U*tau/sqrt(B) sum_(h!=0) barxi(h) tildeOmega_v(U*q_h/B), B=q_bstar. The Fourier weight is bounded by C_N(1+|v|)^(2N+4)(1+x)^(-N-2). Sum over h and then f. No moving-character estimate is invoked.

(14) First restrict q_c q_a^6 <= T_D Z^(1/16).
(15) For T=Q_J q_e/q_r^6:
T/q_rad(c*a) >= Q_J/(q_c q_r^6 q_a)=Q_J/(q_s q_a)
 >> X_J/(T_D Z^(1/16))^(1/6).
(16) Its exponent is 17/48-d-(1+1/6-d+1/16)/6
 =23/144-5d/6-1/96 >=1/96 for 0<=d<=1/6.

Crude retained counts: q_c<<Z^(23/48), q_r<<Z^(23/288), q_a<<Z^(59/288); divisor bound d(rad(c*a))<=q_c q_a, e sum bounded by q_r, tuple count O(Z^(1/6)). Total exponent 2*(23/48)+2*(23/288)+2*(59/288)+1/6=61/36<2. Inverse normalizations bounded eventually.

Gaussian tail outside (14): |V_G| <=(2 sqrt(pi))^-1 exp(-(log Z)^2/1024). Use |E|<<Q_J+1 since T<=Q_J, and sum_a q_a^-2<infinity. Remaining crude count exponent 23/48+2*(23/288)+1/6+5/6=59/36<2.

(17) |I_good-principal(Z)| <= C_N Z^(2-N/96) integral |What0(iv)|(1+|v|)^(2N+4)dv + C Z^2 exp(-(log Z)^2/1024).
Choose N>=96(A+3). Constants fixed-data, uniform in original tuple/subset and large real Z. This is the candidate to audit.

## Other conclusions, not yet independently accepted

At u=1,(x,w,z)=(2,1,1/6), q=P^-1, d_p=eta(p)P^-2, r_p=baralpha(p)^6 eta(p)^6 P^-9, Delta=1-q*r_p-(1-q)d_p:
Pstar=(1+q)(r_p-d_p)/(1-r_p);
P=(1+q)Delta/((1-q)(1-r_p));
H=(1-q^2)Delta/((1-r_p)(1-d_p));
B=G/H=-(1-q)(1-r_p/d_p)/Delta-q.
B+1=(1-q)(r_p/d_p-q*r_p-(1-q)d_p)/Delta.
Thus |B+1|<=(q^2+q^7+q^10)/(1-q^2-q^10)<=2q^2, Re B<=-47/49 for P>=7. Nonnegative actual slot weights yield Re B_i<=-(47/49)S_i<0 when S_i>0. Disjoint-slot product gives nonzero full selected correction. This kills only an exact local/slot annihilator claim, not a power-saving estimate or the whole route.

Equation (24) defines N_eta by the exact same mixed sum with all signs and coefficients, restricted to the complement of the good-principal set, excluding identically annihilated overlaps and incompatible units. Equation (25): I_modified=N_eta+O_A(Z^-A). N_eta has NO improved bound.
Permitted n=1,c,s squarefree coprime block has primitive raw conductor bstar*c*s and Q_J/q_(bstar*c*s)~X_J/T_D~Z^(-13/16). Complete-period zero does not bound this incomplete average.

Full low exponent remains source-reported 3/16+epsilon, C(s)=s-11/16, threshold7/8. No high-domain extension to principal x>1/2. No transfer to Q3 K_m. RH/SP/G1/G3/Schur/scalar reserve OPEN.
