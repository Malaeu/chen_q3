# Q4 signed dual — normalized mathematical extract

Terminal response observed2026-10-07 around10:11UTC in the SAME Execute Joint Probe Calculation chat /c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd. Full rendered attachment read:227 blocks,47773 normalized characters. This is a manually normalized extract, NOT original attachment bytes. Request PROSHKA_SIGNED_DUAL_Q04.txt SHA25637cb10ded56e7fc731b63fe9d77f6ba4a2c7171a75baa3f70d4d6c1ace3ffd32,945248bytes. Embedded OpenAI SHA42a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3; DFDH SHAe46244c8ad0d8a214b7cb5e04490e5dded5e03be79524c0c7e5ca48f7b5773e8. Baselinef092b424. Verdict TRY_Q04_SIGNED_PARITY_SWITCH; no full exponent gain, no high extension, RH/SP/Schur/G1/G3/scalar reserve OPEN. Independent audit pending at creation.

## (1)–(5) actual cofactor completion

Audit closeout: mobius_source_audit bounded PASS(1)–(20); squarefree_conductor_check bounded PASS(21)–(29); root rational budgets checked. Unit exclusion also holds for N~T growing, despite the original response's overly strong prose N>>T. No original answer bytes or Pro-reported diagnostic runs are certified here.

Lambda=(tuple,aP,bP,g,v,H),m=gPv, all five selected states from Q2 retained; g,v sf,(g,v)=(gv,P)=1. H allnonzero good elements includingunits andprimepowers. DeltaP=productDp,Lg=productLp; Lp=1_vpH=1−(qp−1)1_vpH>=2. D10=−barchipH,D11=Lp−1,D12=−chipH,D21=barchipH,D22=−Lp. Full H-unit orbit implements original projector with a=aPg dnu,b=bPgv, not frozen beforeconvolution.

c0Lambda=wtuple baretaP eta(aPg)/q_aPg W1(q_bPgv/Y)barxiH DeltaP Lg chivH; PsiH(n)=eta(n)barchinH. (1)
F_Lambda,N,t(y)=omega(y)V(q_aPg M t N y/(ZqP))W0tilde(XqH/(q_aPg M t N y)); B=sum_(nu,m)=1 betaT(nu)PsiH(nu)/qnu F(qnu/N). (2)
TII=sum_qd>T mud etad/qd sum_Lambda,N c0Lambda barchidH mask(d,m) B(qd/M). (3)
All N cross terms stay inside energy. betaT=delta−mu_le*1 vanishesnu<=T; unitprofile F(1/N) retained until excluded bysupport. No(d,nu),(e,k)coprimality or sfek added.

H=epsilon h primary,ap=vp(h)mod6,rH=prod_ap!=0 p,psiH=prodchip^(-ap),EH=rad(hm)/rH. (4)
FixedSperiodell; phiH(z)=1_primarygood eta(z)barchiz(epsilon)R(z,h), zero branchwithoutsymbols; PsiH=phiH psiH withextracanceledprimezero mask. tauH=sum_y modrH psiH(y)e(y/rH), A_H,f(j)=sum_x modell phiH(frH x)e(jx/ell), W=F/y.
ForrH1 tau=psi=1 evenj0; otherwiseprimitive |tau|sqrtqrH.

B=−psiH(ell)tauH/(qell qrH) sum_e<=T,(e,hm)=1 mue PsiH(e)/qe
 *sum_f|EH muf psiH(f)/qf sum_j barpsiH(j) A_H,f(j) Wtilde(Nqj/(qe qf qell qrH)). (5)
AddF(1/N) for generalprofile includingunit. CRTz=rH x+ell y; factorpsiH(ell)tauH barpsiHj A. Harmonicscale(qf qell qrH)^−1.

## (6)–(11) full second completion

i=(Lambda,N,e,f,j), bi absorbs−c0Lambda andeverycoefficientof(5); Fi(t)=Wtilde_Lambda,N,t(Nqj/(qe qf qell qrH)).
EM=sum_d good rho(qd/M)|sum_i bi barchidHi mask(d,mi)Fi(qd/M)|². (6)
r12=prod_vpH'−vpH!=0mod6 p,E12=rad(HH'mimi')/r12,psi12=prodchip^(vpH'−vpH).
phi12(z)=1_primarygood barchiz(epsilon)chiz(epsilon')R(z,h)R(z,h'); A12,b(k)=sum_x modell phi12(br12 x)e(kx/ell); Wii'=rho Fi barFi'. tau12 finiteGauss. (7)

EM=M sum_ii' bi barbi' psi12(ell)tau12/(qell qr12)
 *sum_b|E12 mub psi12(b)/qb sum_k barpsi12(k) A12,b(k) Wtilde_ii'(Mqk/(qb qell qr12)). (8)
All signs/cofactor/tuplepairs retained. Ji=qe qf qell qrH/N,Ji'=qe' qf' qell qrH'/N',K12,b=qb qell qr12/M. (9)
rH1,j0 term=−mH Wtilde(0)prod_p|EH(1−1/qp)sum_e<=T,(e,hm)=1 muePsiH(e)/qe; mH=meanphiH. (10)
r121,k0 term=M m12 Wtildeii'(0)prod_p|E12(1−1/qp),m12=meanphi12. (11)
Means mayzero; j0/nonzeroj crossretained. Primitiveconductor!=1 killszeroonly. Wtilde0=2pi/sqrt3 integralF(y)dy/y. ExactrestrictedenergyEM−BcutM; Bcut=sum_qd<=T rho|inner|²>=0. ecutoffretained. First finiteHcutoffs; fullj,k,H tails restored via Schwartz derivatives plus polynomialdivisor/conductorgrowth. No taildiscard.

## (12)–(14) all-valuation Gauss rule

Gcal=tauH/sqrtqrH *bartauH'/sqrtqrH' *tau12/sqrtqr12.
Atp,a=vpHmod6,b=vpH'mod6, gj=gammaj(p) j1..5,g0=1 meansabsentconductor,notprincipalGaussvalue.
Gcal=prod_p U_p Theta_p(a,b),Theta=g_(b−a)g_(-a)bar g_(-b).
Up=[chip(rH/p)^(-a)]_p|rH [chip(rH'/p)^b]_p|rH' [chip(r12/p)^(b−a)]_p|r12. (12)
Setz=gamma2(p),G=G(p): (g0,g1,g2,g3,g4,g5)=(1,Gz²,z,G^9,z^-1,G^5z^-2),G12=1. (13)
SourceG(p³)=gamma3(p), NOT G(p)³; G6=chip(-1),G3=chip(-1)gamma3(p). Theta10=gamma_-1²,Theta01=chip(-1)gamma1²,Thetaaa1,Theta12=chip(-1)gamma2.

ForH=epsilon gr,H'=epsilon'gs withg,r,s sfpairwisecoprime:
Gcal=R(r,s)R(g,rs)chis(-1)barchir(g)²chis(g)²
 *mur mus baralpha(r)alpha(s)barG(r)²G(s)²bargamma2(r)gamma2(s). (14)
Positive denominator sqrt(qgr qgs qrs)=qg qr qs; dualK=qb qell qr qs/M. gcommonGaussfactorscancel; residualcrosssymbols=chir(s)^−1 chis(r)chig(r)^−1 chir(g)^−1 chig(s)chis(g). Unitsremainfixedperiod; repeatedfrequenciesuse(12),masksneverdeleted.

## (15)–(20) quadratic component and signed switch

Restrictedbalancedcomponent:aP=P,bP1,g1,M=N=Z1/2,B=Z23/48,C=Z13/16,v~B,H,H'~C squarefreecoprimeprimaryparts; f=f'=b1. Originalunit/ray,tupleprofilesretained. Lefthcoefficientapartfromspecifiedfixedfactors:
mu(h)baralpha(h)barG(h)²bargamma2(h) chi_h(jkv/(eP)). (15)
Rightcorrespondingconjugate. Fractiononlyonoriginalunitlocus; cancellationnevererasespunctures.
n_p=vp(jkv/(eP))mod6,delta=nmod2,bp=(n−3delta)/2mod3.
qfrak=prod_pgood p^delta=sf_S(jkveP),a3=prod p^bp.
chi_h(fraction)=vartheta_fixed(h)chi_h(qfrak)^3 chi_h(a3)^2. (16)
Quadraticgoodconductorqfrakexact. Forodd a1,3,5, normalizeddistance tospan(1,chip²,chip4)equals1 bycharacterorthogonality. (17)
ThisrefutesonlytermwisefixedS+cubic-onlymap,notaggregatesum,cancellation,movinglevelspectralmethod,orpopulationofannuli.
AtE=T, J=CE/N=Z9/16,K=C²/M=Z9/8,q_qfrak<=qj qk qv qe qP<<Z31/12. (18)
DFDHg3tilde(h)=chi_h(lambda)^−2 gamma2(h); relativetoitsconjugatewitness(15)hasmu(h)baralpha(h)barG(h)²chi_h(lambda)^−2 plus(16). G/lambdafixedray,mu/angularnotfixedray; cubicargumentneednotsf.

Evenparitysf_S(jkveP)=1 fixes e0=sf_S(jkvP),sinceesf.
sum_e<=T,sf,(e,hPv)=1 muePsiH(e)/qe 1_parityeven W(e,j,k,v,P)
=1_qe0<=T 1_(e0,hPv)=1 mue0PsiH(e0)/qe0 W(e0,j,k,v,P). (19)
Generalprescribedqfrak sets e_qfrak=sf_S(jkvP qfrak). (20)
Sumallqfrakrecoversoriginale exactly; retainscutoff,sign,e-dependentprofileandduallength. Applybothsidesinside(8).

## (21)–(26) restricted even covariance bound

Evenbothsidescomponentof(8)asabove, alltuples,allshortdyads,allnonzeroj,j',k plusfullSchwartztails. EMNev neednotpositive.
ForR1,R2 good squarefree:
count{j,j',k!=0;qj<=J,qj'<=J',qk<=K;sf_S(jk)=R1,sf_S(j'k)=R2}
 <<eps (JJ'KqR1qR2)^eps sqrt(KJJ' q_(R1,R2)/(qR1qR2)). (21)
Proofgoodsfpartk=s,k=sa²,j=sf(R1s)b²,j'=sf(R2s)c², finiteunit/Sparitychoices. Fixeds count<=C sqrt(KJJ')/[sqrt(qs qsf(R1s)qsf(R2s))]. Eulerproduct:1/sqrt(qR1qR2)*prod_poutside(1+qp^-3/2)*prod_symdiff(1+qp^-1/2)*prod_intersect(1+qp^1/2).
ActualR1=evP,R2=e'v'P' sfbyoriginalmasks. e~E,e'~E',v,v'~B:
sum_e,v,e',v' sqrt(q_(evP,e'v'P')) <<eps Z^eps EE'B² sqrt(q_(P,P')). (22)
Proof t=ev,t'=e'v' divisorboundedmultiplicities; commondivisor r costs1/q_(r/(r,P)) and1/q_(r/(r,P')); sameEulerfactors.
Eraw=N²EMN changes1/qnu toboundedN/qnu. Prefactor MN²/(C² EE' qPqP'), O(C²)frequencypairs,J=CE/N,J'=CE'/N,K=C²/M.
|Eraw,ev| <<eps Z^eps M^.5 N B C² sum_tuple,tuple' w w' sqrt(q_(P,P'))/(qPqP')^1.5. (23)
Disjointslots factor exactly; ithfactor=(sum_p Wi(qp/Pi)qp^-1.5)²+sum_p Wi²(qp^.5−1)qp^-3 <<Pi^-1; diagonalcorrectionO(Pi^-1.5),idealcountingonly. Total<=Z^-1/6. (24)
Thus|Eraw,ev|<=Z43/16+eps,|EMNev|<=Z27/16+eps. (25)
At M=Z^(1/2), the target weighted energy is Z^(71/48−2delta); gap5/24+2delta. sqrtwithphysicalfactorZ^-29/96 M^-1/2 givesZ7/24, gap5/48above3/16. (26)
ThisisNOTphysicalsectorbound; componentnotnonnegative,nodominance. EM=EMNev+EMrest exact; complementsunpaid. Dyadicj,j',ktailsclaimedcontrolledbyprofilesderivatives.

## (27)–(29) polar terms and remaining consumer

DFDHreferenceonly:sum_bprimary bar(a/b)_3 g3tilde(b)H(qb/C)=P_C(a)+R_C(a);
P=C1 Hhat(5/6)barg3tilde(a)qa^-1/6 C5/6 prod_p|a(1+qp^-1)^−1;
sum_qa<=A mua²|R|²<<(AC)1+eps. (27)
SpecificsfawitnessandKubotamoment; operatortheoremLOWERboundforsup,notupperactualvector. Pole5/6normalized,4/3unnormalized. NoactualQ3cubicpolartermadmitted.
EvenparitydenominatorePsf dividesjkv; jkv/eP=a² atgoodprimes. Attransitionqa~(C³B/(MNP*))^.5=Z7/8,referencepolarC5/6qa^-1/6=Z17/32,onlyifsfahypothesisandreferencevector,notactualamplitude.
DFDHlaterRSsectionsGaussian/quartic,dependonGamma; movingqfraknotfixedconstant.

Q2detectorPsf(Z)=1/(2pii)int_Rex2 cS X1/3 Z^(x−5/6)Vhat(x−5/6)/L_S(x,eta)
 *sum_tuple w prod_p|P qp^-5/6 Gpsf(x,1,1/6) prod_poutside Hpsf(x,1,1/6) dx. (28)
cS includeszresidueJacobian1/6. Nonzerointegrandnotlowerboundintegral. DistinctfromfinitePoissonzeromodes,artificialconvolutionpole,prospectivecubicthetapole. Ifcentered,mustrestorePsfexactly.

E_sw definedasbalancedgenericcomponentof(8),sf coprimeH,H',f=f'=b1,alloriginalsigns/tuple/profiles; replacee,e'by(20),sumallqfrak,qfrak' beforeabsolutevalue. Optionalcomponenttarget|E_sw|<=Z71/48−2delta+eps,M=NZ.5. (29)
Notnecessaryforfullconsumer; evenifprovedleavesmaskdivisors,shared/repeatedH,selectedstates,g,M,N,crossranges.
Physicalcomplementisoriginalmixedsum times1−1_n1 1_s sf theta(qc/(ZqD)), withoriginalVG(qc qn³/(ZqD)),D|cn³,allphases/compensation. Neta=√X/Y(−TI+TII)+R_eta,theta.
Fullrequired|−TI+TII+(Y/√X)R|<=Z47/96−delta+eps remainsOPEN. TypeIandhighnotimproved. Fullsource-reportedlow3/16 unchanged; sameprobehigh,Eulerholomorphy/nonvanishing,targetuniformmarginsrequired. C(s)=s−11/16; approachRHneedsfull low→−3/16.

Proreportedcontrols210finitefieldGauss,45orthogonality,20412parityswitch,512Eulercases+rationalarithmetic; theseareProreporteddiagnostics,notrootexecutedcertificates. Requestedindependentbounded audit(5),(8),(12)–(25),firstmismatchorPASS. NoLean/Arb/RHclaim.
