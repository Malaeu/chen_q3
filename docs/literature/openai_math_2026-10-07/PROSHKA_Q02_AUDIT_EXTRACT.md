# Q2 joint remainder — normalized mathematical extract

Full rendered PROSHKA_VERDICT_JOINT_REMAINDER_Q02.md read in the existing Execute Joint Probe Calculation chat at 2026-10-07 07:39–07:43 UTC. Original download did not complete; this is a manually normalized mathematical extract, NOT original attachment bytes. No byte-exact answer hash claimed. Browser extraction read all 254 blocks, about 50k characters including formulas.

Request: PROSHKA_JOINT_REMAINDER_Q02.txt, SHA256 851abf7be646b223fd70b355e188ea182ff4c7dc37a1f48c19d6eecc86d326d9. Source paper SHA256 42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, OpenAI math adc7f1241b42e322a6451854ab7e4b4c146bf78a. Chat https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184/c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd. Q1 is accepted as audited at cc02ef4e. Verdict: representation progress, NO improved full low exponent, no high extension, RH/SP/Schur/G1/G3/scalar reserve OPEN.

## (1)–(3) actual sector

B=q_bstar, X=Z^(17/48), Y=Z^(23/48), P=product selected primes, R=p_J, D=P/R, X_J=X/q_R,Y_J=Y/q_R,T_D=Zq_D. Original tuple weights w(p)=product W_i(q_pi/Z^li) and original windows stay fixed.
I_D^{1,sf}(X',Y',T;V) is the literal source physical n=1, squarefree s sector, mark D|c, c profile V(q_c/T).
U_eta,V = sum_tuples w(p) sum_R|P mu(R)q_R^(-3/2) bareta(D) I_D^{1,sf}(X_J,Y_J,T_D;V).
Choose V=V_G theta, theta nonzero smooth compact support, 0<=theta<=1. The complement 1-theta is retained. T_D/Y_J=Zq_P/Y, so q_c/q_s>=fixed_positive Z^(11/16) uniformly in subset/tuple. Thus c!=s eventually and this upper annulus lies in Q1's actual nonprincipal remainder.

## (4)–(8) actual finite Gauss contraction

c,s squarefree good; g=(c,s), c=gc0,s=gs0, pairwise coprime g,c0,s0; psi=xi chi_c0 barchi_s0 primitive modulus k0=b_*c0s0, additional zero mask at g.
E(c,s)=chi_s(b_*)/[tau xi(s) Xi(c)] * gamma2(c) baralpha(c) barG(c) R(c,s).
Exact claimed identity for every H in O:

E(c,s) sum_{m mod b_*cs} xi(m)chi_c(m)q_s^(-1/2)g_chis(s,-m)e(Hm/(b_*cs))
= sqrt(Bq_cq_s) barxi(H) product_p|cs T_p(vp(c),vp(s);H).             (4)

L_p(H)=1_{vp(H)=1}-(q_p-1)1_{vp(H)>=2}.
T(0,0)=1; T(1,0)=-barchi_p(H); T(0,1)=chi_p(H); T(1,1)=L_p(H); zero outside {0,1}^2. All character powers keep nonunit zero extension. H=0 vanishes at fixed primitive xi.

Poisson at original scale Bq_s X' gives exactly
I_D^{1,sf}=sqrt(X')/Y' sum_{c,s sf,D|c} eta(c)/q_c V(q_c/T)W1(q_s/Y')
 * sum_{H!=0} barxi(H) product T_p * W0tilde(X'q_H/q_c).             (6)
Original outside normalization 1/[Y' sqrt(Bq_sX')sqrt(q_c)], Poisson X'/q_c, Fourier sqrt(Bq_cq_s) multiply to sqrt(X')/(Y'q_c).

Phase proof: q_s^-1/2 g_chis(s,-m)=gamma1(s)barchi_s(-1)barchi_s(m).
Source signal gives gamma2(c)baralpha(c)barG(c)=mu(c)bargamma1(c).
For l=k0g and C_g(h)=product_p|g(q_p 1_{p|h}-1), CRT representatives m=gx+k0y give
sum_{m mod l} psi(m)1_(m,g)=1 e(hm/l)=psi(g)g_psi(k0,h)C_g(h).       (7)
Lifting to full modulus lg contributes q_g 1_{g|H}, H=gh.
With epsilon_psi=g_psi(k0,1)/sqrt(q_k0),
epsilon_psi=xi(c0s0)chi_c0(b_*s0)barchi_s0(b_*c0) tau gamma1(c0)gamma_-1(s0),
E gamma1(s)barchi_s(-1)psi(g)epsilon_psi=mu(c)barpsi(g).             (8)
Use gamma1(gu)=chi_g(u)chi_u(g)gamma1(g)gamma1(u), gamma_-1(s0)=chi_s0(-1)bargamma1(s0),
R(gc0,gs0)=chi_g(-1)R(g,c0)R(g,s0)R(c0,s0), Xi(c)=xi(c)chi_c(b_*).
Before table the result is sqrt(Bq_cq_s)mu(c)barxi(H)1_{g|H}C_g(H/g)barchi_c0(H)chi_s0(H).

## (9)–(14) common lattice and every subset

Set a=Rc,b=Rs. Squarefreeness is on a/R,b/R, NOT on common a,b.

U_eta,V=sqrt(X)/Y sum_tuples w(p)bareta(P) sum_{a,b} eta(a)/q_a
 * V(q_a/(Zq_P)) W1(q_b/Y)
 * sum_{H!=0}barxi(H) K_P(a,b;H) W0tilde(Xq_H/q_a).                (9)

K_P=product_p not|P T_p(vp(a),vp(b);H) product_p|P D_p(vp(a),vp(b);H).
Selected table:
D(1,0)=-barchi_p(H)
D(1,1)=L_p(H)-1
D(1,2)=-chi_p(H)
D(2,1)=+barchi_p(H)
D(2,2)=-L_p(H)
all other pairs zero.                                            (10)

Scalars:
q_R^-3/2 sqrt(X/q_R)/(Y/q_R)/q_(a/R)=sqrt(X)/(Yq_a),
eta(a/R)bareta(P/R)=eta(a)bareta(P).                               (11)
Arguments q_c/T_D=q_a/(Zq_P), q_s/Y_J=q_b/Y, X_Jq_H/q_c=Xq_H/q_a.
Local derivation: D(A,B1)=1_{A=1,B1 in{0,1}}T(1,B1)-1_{A,B1 in{1,2}}T(A-1,B1-1).
Product expansion is exactly all 2^K subsets with their signs.

Unit projector Pi(a,b)=1/6 sum_units eps xi(eps)chi_a(eps)barchi_b(eps) in{0,1}. Every H unit orbit vanishes if Pi=0; selected table has unit degree vp(b)-vp(a). For g0=(a,b), primitive modulus b_*a/g0*b/g0 has norm Bq_aq_b/q_g0^2, mask g0/R, original averaging scale BXY/q_R^2. No fixed conductor replacement.
Upper scale q_a~Zq_P,q_b~Y, transition q_H~Z^(13/16), independent of subset; full Fourier tail kept.
D(1,1;H)=-1,0,-q_p for frequency valuations 0,1,>=2 respectively. At D(2,2), valuation-one coefficient is -1; it must not be deleted. Sixth-power H never reaches the cancellation branch at D(1,1). This is local support information, NOT a global lower bound.

## (15)–(22) principal double residue of the whole upper block

Principal frequency H=h^6; Q=q_p,v=Q^-6z,w0=Q^-w,d=eta(p)Q^-x.
Psf=1/(1-v)+w0-d-d(Q-1)w0*v/(1-v).
Psfstar=-d[1+(Q-1)w0*v/(1-v)].                                  (15)
Asf=-(1+w0+w0^2)+d*w0+[-Q*w0+(Q-1)d*w0^2]*v/(1-v)
    =bareta(p)Q^x Psfstar-w0 Psf.                               (16)
Hsf=(1-v)(1-w0)/(1-d)*Psf; Gsf=samefactor*Asf.                    (17)
These are sector factors, NOT the full source P,H. Unselected scalar zeta_F^S(6z)zeta_F^S(w)/L_F^S(x,eta). Selected Gsf has extra Q^(z-1). Corrections normally converge near x=2,w=1,z=1/6.

c_S=What1(1) M(1/6) [Res_1 zeta_F^S]^2/6>0, using source radial Mellin M.
Rsf_eta,V(x,Z)=c_S X^(1/3)Z^(x-5/6)Vhat(x-5/6)/L_F^S(x,eta)
 * sum_tuples w(p) product_p|P q_p^-5/6 Gsf_p(x,1,1/6)
                  product_p not|P,p notin S Hsf_p(x,1,1/6).      (18)
This is the remaining x-integrand of the double residue, NOT U's value.

At x=2,w=1,z=1/6, q=1/Q,d=eta q^2,
Delta=1+q-q^2-(1-q^2)d, N=1+q-q^3-q(1-q^2)d,
Hsf=(1-q)Delta/(1-d), Gsf=-(1-q)N/(1-d), Bsf=-N/Delta.             (19)
|Delta|>=1+q-2q^2+q^4>=1. Good primes Q>=7.
Bsf+1=-(1-q)[q^2+(1-q^2)d]/Delta.                               (20)
Hence |Bsf+1|<=2q^2, Re Bsf<=-47/49, |Hsf-1|<=2q^2.
Exact Hsf=1-2q^2+q^3+q(1-q)d/(1-d).
Product Hsf converges nonzero. Actual slot Bi=sum_p Wi(qp/Pi)qp^-5/6 Bsf_p has Re Bi<=-47/49 Si, Si=sum_p Wi(qp/Pi)qp^-5/6>0 eventually by fixed-ray prime theorem. Disjoint slots factor the complete tuple sum as product Hsf * product_i Bi. Vhat(7/6)>0,c_S>0,L(2,eta)!=0 imply Rsf(2,Z)!=0 for all sufficiently large real Z. This does not lower-bound the physical probe; x integration, other rows and other sectors may cancel. Norm exponent X^(1/3) Z^(x-5/6) Z^(ell/6)=Z^(x-11/16). (22)

## (23)–(31) exact completion, inverse cubes and reflection cost

Here b is a NEW inverse-cube variable. Expand barG(A)=sum_theta a_theta theta(A) and actual s ray class sigma. Psi(A)=nu_sigma(A)theta(A)chi_A(m), nu_sigma=eta Xi^-1 R(A,s_sigma).
Psi_e(A)=Psi(A)1_(A,e)=1, beta_e(b)=baralpha(b)^3 Psi_e(b)^3. All powers keep zero masks.
Squarefree marked row D_D,V(C;Psi)=sum_c sf gamma2(c)baralpha(c)Psi(c)/sqrt(q_c) 1_D|c V(q_c/C).
Completed C_V(U;Psi_e)=sum_c sf,n gamma2(c)baralpha(c)Psi_e(c)beta_e(n)/[sqrt(q_c)q_n] V(q_c q_n^3/U).

D_D,V(C;Psi)=sum_e|D mu(e) sum_b mu(b)beta_e(b)/q_b * C_V(C/q_b^3;Psi_e). (24)
Proof: mark 1_D|c=sum_e|D mu(e)1_(c,e)=1; regroup k=bn and sum_b|k mu(b)=1_k=1. Shared c,n primes allowed. If V supported in [v-,v+], b sum is finite q_b<=(v+C)^(1/3). Gaussian tail version converges absolutely; C_VG(U)<<_N U^N at small U yields arbitrary power tail after q_b<=C^(1/3) Z^kappa, with crude outside loss Z^(7/12).

Equations25–28 substitute the pinned prop:completed-reflection, conditional on that proposition, retaining all three cusp coefficient functions d_branch(nu), full active denominator c_branch=c_F(h0) product_active p, fixed L, branch root phases and zero masks. Reflected completed row has
sum_branch zeta_branch sum_nu!=0 d_branch(nu)alpha(nu)theta_branch(lambda^4 nu)/sqrt(q_nu)
 * product_active B_p,j(lambda^4 nu) Vsharp(q_nu C/[q_b^3 q_cbranch^2]).
No extra primal S-mask is placed on dual coefficients. Active j=0, j=4 and nonzero generic branches retain the original source definitions; phases not independently recertified here. The full mixed pairing retains the s Gauss coefficient, m averaging, theta,e,b sums, all subset signs and all tuples. In squarefree m branches the dual character is quadratic, but its correlation with inverse b and s remains. Dual scale is q_m^2 q_eactive^2 q_b^3/T_D, base Q_J^2/T_D~Z^(1/2-3d_J). The moving factors are unpaid.

Source completed T(z0,Psi_e)=L0(z0,Psi_e)D(z0,Psi_e) with L0=Le(3z0-1/2), Le(w)=sum_b beta_e(b)q_b^-w. The isolated-squarefree Mellin integrand is
Vhat(z0-1/2) C^(z0-1/2) T(z0,Psi_e)/Le(3z0-1/2).                 (29)
T entire does NOT imply quotient entire. Given necessary meromorphic continuation, simple zero rho of Le yields potential residue at zrho=(rho+1/2)/3:
Vhat(zrho-1/2) C^(zrho-1/2) T(zrho,Psi_e)/[3 Le'(rho)].           (30)
No uncancelled pole asserted. Multiple zeros/deleted-factor zeros and numerator cancellation must be treated inside full joint sum. Angular baralpha^3 remains; no finite-order strip bound automatically applies.

On favorable squarefree m branches, source cusp-size/support bounds give sum_nu |d(nu)|/sqrt(qnu)|Vsharp(qnu/U)|<<sqrt(U). Then inverse b term <=q_cbranch/sqrt(C)*q_b^(1/2), summing q_b<=O(C^(1/3)) only gives O(q_cbranch). (31) Absolute summation loses the apparent C^-1/2 gain; not a lower bound or no-go for signed sums. j=4 branches not declared harmless by this calculation.

## (32)–(34) exact remaining obligation

R_eta,theta is original signed mixed sum on Q1 support N multiplied by [1-1_n=1 1_s sf theta(q_c/T_D)], retaining V_G(q_c q_n^3/T_D), mark D|cn^3, all phases and subsets.
N_eta=U_eta,VGtheta+R_eta,theta.                                  (32)
This keeps n>1, prime-power s, complementary Gaussian region and all shared primes.
Let C_eta,V be the full signed sum in(9) without sqrtX/Y=Z^-29/96. A sufficient upper-block improvement delta>0 is
|C_eta,V(Z)|<=C_eta,eps,data,theta Z^(47/96-delta+eps) for all large real Z. (33)
No such bound proved; the source full low bound does not automatically bound this cut block. Need same gain for complement OR directly for their signed sum. Lnew=3/16-delta gives only formal low threshold7/8-delta. (34) The high comparison/nonvanishing and target-uniform margins remain separate. FullRH at fixed geometry needs low approaching -3/16.

## Reported checks and required independent audit

Pro reports finite Fourier floating controls at norms7,13,19 and fixed b*=2lambda; these are diagnostic only. Reports exact symbolic identities,1152 cyclotomic local checks,2025 two-slot checks, planted missing rescaled subset detected (1 instead of0). Those computations have not been imported as executable certificates.
Independent audit requested: finite identity(4) with phases; common lattice(9)–(11) all valuations/units/subsets; Euler equality(16) from both representations; principal full tuple residue(18) and nonzero(19)–(21), explicitly not physical lower bound; finite inverse cube(24). First mismatch if any. The proposed next calculation is a signed contraction of K_P against sixth-power and non-sixth-power rows, preserving actual coefficients; any centering subtracts exact(18) with its contour remainder. No new question until this answer is processed.
