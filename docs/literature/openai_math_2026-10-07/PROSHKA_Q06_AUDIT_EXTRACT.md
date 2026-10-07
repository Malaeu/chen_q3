# Q6 full core-dual pairing — normalized extract

Full rendered PROSHKA_VERDICT_FULL_COMPLETED_PAIRING_Q06.md read2026-10-07 12:40–12:44UTC in SAME Execute Joint Probe Calculation chat. 240 blocks,44568 normalized characters. Manual mathematical normalization, NOT original attachment bytes. Terminal Antwort abgeschlossen and regenerate observed, no Stoppen. Request860044bytes SHA25660e140ea09e5c610b27a638fc2b487ba6d60b63f225a8aa03d1a70b61a5f1c1d; pinned source766316bytes SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, commitadc7f1241b42e322a6451854ab7e4b4c146bf78a. Q5 predecessor e2911bd2. No full gain claimed. All statuses RH/SP/Schur/G1/G3/scalar reserve OPEN.

## Exact expansion (1)–(8)

R=p_J,d=sum_J ell_i,X'=X/qR,Y'=Y/qR,Q=qb* X'Y',D=p_Jc,U_D=ZqD. wR,wD original slot weights. nu(A)=eta(A)Xi(A)^-1 R(A,s_sigma)theta(A). b_s(v)=W1(qs/Y')(qs/Y')^(-1/2+iv)chi_s(b*)/(tau xi(s)),s in sigma.
S_J=1/Y' sum_(tupleD,theta,s,c sf,n) wD baretaD a_theta b_s gamma2(c)baralpha(cn³)nu(cn³)/(sqrt(qc)qn) *1_D|cn³ VG(qc qn³/U_D)*L_Qv(c,n,s).
L_Qv=sum_m!=0 Omega(qm/Q)(qm/Q)^(-iv)xi(m)chi_cn³(m)qs^-1/2 g_chis(s,-m).
I_modified=(2pi)^-1 sum_(J,tupleR) (-1)^|J| wR/(qR^1.5 sqrtQ) sum_sigma int What0(iv) S_J dv. (2)

m=epsilon*kappa*h² uniquely, epsilon six units,kappa sf primary,h primary, NO(kappa,h)=1. Psi_kappa(A)=nu(A)chi_A(epsilon*kappa).
chi_cn³(epsilon*kappa*h²)=chi_cn³(epsilon*kappa)chi_c(h)²1_(n,h)=1;
gamma2(c)chi_c(h)²=qc^-1/2 g_chic²(c,h²). (3)
z_p(s)=baralpha(p)³ Psi_kappa(p)³ qp^(-3s+1/2),D0=D/(D,rad h),chi_h^[2](A)=chi_A(h)².
For Re s>1, spectral unpunctured K_D(s;h,Psi)=T_D0(s,Psi*chi_h^[2]) product_p|h z_p^(1_p|D)/(1-z_p). (4)
At p|kappa,z_p=0; scalar z^0=1 does not change character zeros.
Finite recombination sum_e|rad h mu(e)product_p|e z_p K_D/(D,e)
=T_D0 product_(p|h,p∤D)[1/(1-z)-z/(1-z)] product_(p|h,p|D)[z/(1-z)-z/(1-z)]
=1_(D,h)=1 T_D(s,Psi*chi_h^[2]). (5)
Thus all auxiliary denominators cancel BEFORE using continuation; remaining T continuation is an imported source premise. Physical scale U_D/qe³=Z' q_D/(D,e), Z'=Zq_(D,e)/qe³ (6); original Q,Y',slots not moved. Recombine first, no balanced norm at Z'.

H_kappa=sqrt(Q/qkappa) is a NORM scale; w_v(x)=Omega(x²)x^(-2iv).
f_(epsilon,kappa;c,n,s)(h)=1_h=1mod3 xi(h)² chi_c(h)²1_(h,n)=1 qs^-1/2 g_chis(s,-epsilon*kappa*h²). (7)
S_J=1/Y' sum_(tupleD,theta,epsilon,kappa sf<=C Q,s in sigma,c sf,n)
wD baretaD a_theta b_s gamma2(c)baralpha(A)nu(A)chi_A(epsilon*kappa)xi(epsilon*kappa)/(sqrtqc qn)
*1_D|A VG(qA/U_D) sum_h inO f(h)w_v(qh/H_kappa), A=cn³. (8)
No1/6; allsixunits,unit h retained. Outside coefficient zero if(A,kappa)>1.

## Every good local factor and Fourier transform (9)–(13)

The following table is ONLY on the remaining nonzero outside-coefficient locus (A,kappa)=1, as explicitly stated in the original Q6 before the table; it is not a standalone identity for f on discarded labels. At goodp put q=qp,a=vp(kappa)0/1,C=vp(c)0/1,N=vp(n),k=vp(s),s_p=s/p^k. For k>0 unit t_p=-epsilon*(kappa/p^a)*s_p^-1 modp. CRT additive argument uses s_p^-1; no phase-free product.
U_j^(b)(h)=1_vp(h)=b chi_p(h/p^b)^j,j0,2,4;R_b=1_p^b|h. U0 retainsunitmask.
Local table f_p; valid period:
- k0,C=N0:1;1.
- k0,C+N>0:U_2C^0;p.
- k1,a0:gamma1(p)chi_p(t_p)^-1 U_(2C-2)^0;p.
- k1,a1:0.
- k>=2,C+N>0:0.
- k>=2,6∤k,C=N0,b=(k-1-a)/2 nonnegative integer: q^((k-1)/2)gamma_k(p)chi_p(t_p)^(-k)U_(-2k)^b; p^(b+1). Otherwise0.
- 6|k,C=N0,a0:q^(k/2)(1-q^-1)R_(k/2);p^(k/2).
- 6|k,C=N0,a1:q^(k/2)R_(k/2)-q^(k/2-1)R_(k/2-1);p^(k/2).
Proof uses normalized nonprincipal Gauss q^((k-1)/2)gamma_k chi_p(z/p^(k-1))^-k1_vp(z)=k-1; principal Ramanujan difference after z has valuationa+2vp(h).
tau_pj(r)=sum_xmodp chi_p(x)^j e(rx/p),tau_p0=q1_p|r-1, tau_pj=sqrtq gamma_j barchip(r)^j forj2,4.
Plus normalized Fourier of U_j^b onp^(b+1) is q^(-b-1)tau_pj(r). (10)
Nonprincipal k>=2: fhat_p(r)=q^(a/2-1)gamma_k chi_p(t_p)^(-k)tau_p,-2k(r). (11)
k0,1: scalar*q^-1 tau_pj; absentfactor1.
6|k,C=N0: fhat_p(r)=1-q^-1 ifa0, and1_p∤r ifa1, with periodp^(k/2). (12)

ell=3b*,phi_ell(h)=1_h=1mod3 xi(h)²; phihat normalizedplus onell.
M=ell product_goodp p^B_p,using table periods; fixed primes maynonminimal.
G_(epsilon,kappa;c,n,s)(r)=phihat_ell(r(M/ell)^-1 modell)
*product_goodp fhat_p(r(M/p^B_p)^-1 modp^B_p). (13)
Globalgamma2(c) staysoutside in(8); all CRT inverses present.

## Full Poisson, zero mode and ramified control (14)–(19)

With source selfdual planar transform of radial w_v(qz),
sum_h f(h)w_v(qh/H)=H sum_r inO G(r)wtilde_v(H qr/qM). (14)
At fixed primep2 over2 residuefieldF4,xi hasorder3,soxi²nonprincipal. Primary conditionmod3 independent byCRT. Thus phihat(0)=0 and G(r)=0 wheneverp2|r. (15)
Do NOT impose(r,S)=1: atotherfixedprimesxi²mayprincipalunitmaskwithRamanujantransform. rnotprimary;allunitsremain. This linearhzero differsfromQ5positivecovariance,Q3/Q4zeros,Q2detector.
Actualramifiedbranchk6,a1,C=N0: f_p=q³1_p³|h-q²1_p²|h,periodp³;
q^-3 sum_hmodp³ f_p(h)e(rh/p³)=1_p∤r. (16)
Henceuniform unrenormalizedprimitive bound|fhat|<=q^-1/2 fails,notfullroute. Parsevalmean|f|²=q³-q²=sum_r|fhat|². (18)
Original linear-m normalized DFTmodp6: q^-6 sum_m [q^-3 g_chip6(p6,-m)]e(rm/p6)=q^-3 1_p∤r. (18a)
Compression periodq6->q3 increasescoefficientq^-3->1,notcontraction.
Exactdensity for everyk>=1:
sum_(a0,1;b>=0)q^(-a-2b)|q^(-k/2)g_chip^k(p^k,p^(a+2b))|²=1. (19)
Nonprincipalonlya+2b=k-1;principalboundarycontributesq^-1,tail1-q^-1. Actualvaluationprobabilities alsohavefactor1-q^-1. Notglobalcancellation.

## Quantitative discriminator and reflection (20)–(25)

Testonlyc,s sf,(c,s)=1,(kappa,csn)=1,(n,cs)=1,n arbitrary. Primitivecubicpsi=chi_c² barchi_s²,conductorc*s;extramaskradn. Openingmaskf|radn leavesprimallengthH/qf, dualK_f~qf qc qs/H. (20)
Termwiseenvelope <<(1+|v|)^C sum_f min(H/qf,sqrt(qc qs)). (21)
OnGaussiantransitionqc qn³~U_D,qs~Y': K1/H~qkappa Z^(13/16)/qn³. (22)
Writeqkappa=Z^a,qn=Z^b; favorableonlya+13/16-3b<0. (23)
Atboundedn,smallcore:H~Z^(5/12-d),K~Z^(59/48-d). Atqkappa~Q,Hbounded, K~Z^(79/48-2d)/qn³;evenlargestn givesK/H>>Y'. Theseareupperscaleconstraintsnotlowerbounds/noncancellation.
Separate SOURCE-DEPENDENT markedreflection: squarefreerowm,(m,D)=1,all-activebranchc_B=cF*mD, dualL_B=qcB²/(ZqD)~Q²qD/Z=Z^(5/6-5d); L_B/Q=Z^-3d. (24)
AtJemptyselfdual. Retainactiveqp^-1/2chi_p(lambda4mu)^-2 factors,rootphase,cuspcoefficients;notfixed-cuspmap.
SquarefreeinversionexactloopforfiniteF:
sum_kappa sf,h F(kappa h²)=sum_f,r,h mu(f)F(r(fh)²)=sum_r,t F(rt²)sum_f|t mu(f)=sum_r F(r). (25)
No(f,h)=1;separateunits;notadditionalgain.

## Actual remaining consumer and tails (26)–(33)

J_J is full outer sum in(8) WITHOUT1/Y', replacingh-sumby H sum_(r,p2∤r)G(r)wtilde(Hqr/qM); everyc,n,s,tuple,Gaussianretained. S_J=J_J/Y'. (26)
SOURCE benchmark:S_J<<Z^(29/48-3d/2+eps),J_J<<Z^(13/12-5d/2+eps). (27)
Unprovedsufficient:J_J<<Z^(13/12-5d/2-sigma_J+eps),d+sigma_J>=delta. (28)
Atdelta3/8:J_J<<Z^(17/24-3d/2+eps),S_J<<Z^(11/48-d/2+eps). (29)
Weakerfullsignedconsumer (2) withS_J=J_J/Y' <<Z^(3/16-delta+eps). (30)
OutsidebudgetL<=3/16-min_J(d+sigma_J). (31)
No(28),(29),(30)gainproved;highsamerowcontinuation/nonvanishingOPEN.

Convergence: |G|<=sup|f|<=sqrt(qs),qM<<S qs radnorm(cn)<=CS qs qc qn.
H sum_r|wtilde(Hqr/qM)| <<(1+|v|)^C(H+qM). CombinedGaussianbeatsallpolynomialc,nmass. AllothersfiniteforfixedZ.
Truncate|log(qc qn³/U_D)|<=tau logZ onlywithretainederror CZ^B0 exp[-tau²(logZ)²/8],smallerthananyinversepower. Dualtailqr>B qM/H <=CN(1+|v|)^CN sqrt(qs)qM B^(1-N); aftercutB=Ztau,Nlarge. UnitandboundedHkept.

Q2detectorunchanged(32): P_sf=(2pii)^-1 int_Rex2 [cS X^(1/3)Z^(x-5/6)Vhat(x-5/6)/L_F^S(x,eta)] sum_tuplew product_p|P qp^-5/6 Gp_sf(x,1,1/6) product_poutsideS,P Hp_sf(x,1,1/6) dx.
WithVp=qp^-6z,Wp=qp^-w,dp=eta(p)qp^-x:
Pp_sf=(1-Vp)^-1+Wp-dp-dp(qp-1)WpVp/(1-Vp);
Ap_sf=-(1+Wp+Wp²)+dpWp+[-qpWp+(qp-1)dpWp²]Vp/(1-Vp);
Hp_sf=(1-Vp)(1-Wp)/(1-dp) Pp_sf; Gp_sf=sameprefactor*Ap_sf. cS includes1/6residueJacobian.
Restoration(33):I_modified=I_goodprincipal+P_sf+(U_eta,V-P_sf)+R_eta,theta. Oldremainderliteral1-1_n1 1_s sf theta(qc/(ZqD)) onQ1nonprincipalphysicalsupport. No centeringorcontourshift. Fullhighsourceintegralon(3,3,2)unchangedwithactualselectedcorrection,notglobalquotient. C(s)=s-11/16.

## Verification boundary and next target

Pro reports8markpatterns,70Gaussorientations,F4characters,9399DFTfrequencies,720valuations,24densities,6exponentidentities; no local source of its diagnostic program was imported. Reported SHA0ccf5c2cc6b6f36c16bf181682bf0eb4b2d6ab421b02fb62240303f38f763add is provenance only, NOT a reproduced certificate.
Independent target: full restoration(4)–(16),scale(20)–(24),tailrestoration,detector(32)–(33),sourcepremisesexplicit. Proposednextmechanisms: jointcore/dualincidencekeepingdensity, or fullsource-reflectedmixedperiodonselfdualbranch. Neitherisproved,neitherfixed-cusptheoremimported. No next question sent.
