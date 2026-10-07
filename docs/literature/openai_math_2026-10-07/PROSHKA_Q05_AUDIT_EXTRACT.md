# Q5 joint contraction — normalized mathematical extract

Full rendered PROSHKA_VERDICT_JOINT_CONTRACTION_Q05.md read2026-10-07 11:40–11:44UTC in the same Execute Joint Probe Calculation chat. 308 blocks,61583 normalized characters. This is a manually normalized extract, NOT original attachment bytes. Request829808bytes SHA2566e520e516833752c40049e3717036f0be987832e8c4af03505aec4ee127489eb; predecessor4abeb330ecc73ed426545894947aaf5e7b3911a6. Pinned source766316bytes SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, commitadc7f1241b42e322a6451854ab7e4b4c146bf78a. Terminal Antwort abgeschlossen observed; no following question sent.

## Claims and exact object (1)–(7)

Q5 claims physical upper-annulus Type-II bound(sqrtX/Y)|TII|<<Z^(7/12+eps), improving supplied83/96 by9/32 but not full low3/16 (gap19/48). Separately complete zero mode of a NEW H-row covariance obeys0<=D_Q<<Zeps QY/(ZP*)h_A(Q/Q*)², P*=Z1/6,Q*=Z13/16,h_A(x)=min(1,x^-A). Transitionenergy1/8, own physical Cauchybudget1/6. Neither implies a full physical gain. Bounded imported input is LONG_DIVISOR_COFACTOR_BOUND.md(3), not certification of whole manuscript.

X=Z17/48,Y=Z23/48,T=Z1/4. Selectedstates10,11,12,21,22. a=aP g u,b=bP g v,u=d1d2k,d1,d2>T sf,k arbitrary; g,v sf,(g,v)=(gv,P)=1,(u,gPv)=1. No(d1,d2) or(di,k) condition. qa~ZP*,qb~Y,cZ25/48<=qu<=CZ. Both qu>T² andqu>T eventually.

Lp(H)=1_vpH=1−(qp−1)1_vpH>=2. DeltaP productof D10=−barchip,D11=Lp−1,D12=−chip,D21=barchip,D22=−Lp. For lambda=(P,aP,bP,g,v,d1,d2,k),
c_lambda=wP baretaP eta(aPgu)mu(d1)mu(d2)/q_aPgu *W1(q_bPgv/Y)V(q_aPgu/(ZqP)),
phi_lambda(H)=barxiH DeltaP(H)Lg(H)barchiu(H)chiv(H),
F_lambda,Q(x)=W0tilde(XQx/q_aPgu), V=VG theta compactupperannulus.
TII,Q=sum_H!=0 rho_Q(qH/Q) sum_lambda c_lambda phi_lambda(H)F_lambda,Q(qH/Q).
|TII,Q|² <<Q E_Q, E_Q=sum_H rho_Q |sum_lambda c_lambda phi_lambda F_lambda|². Dyadicrho nonnegative; initialprofilesvanishatnorm1, sixunitsseparate. This is NOT Q3 d-row E_M.

## Complete local calculation (8)–(14)

On O/p², q=qp, useUe=1_p∤x chip(x)^e,e0..5, V1=1_vp(x)=1,V2=1_p²|x. U0 notconstant1. Localf=sum ae Ue+bV1+cV2. One-side table:
absent: a0=1,b=c=1;
p^j||u: a_(-j mod6)=1,b=c=0;
p|v:a1=1,b=c=0;
p|g:alla0,b=1,c=−(q−1);
D10:a5=−1; D11:a0=−1,b0,c=−q; D12:a1=−1; D21:a5=1; D22:alla0,b−1,c=q−1.
Forpairedf barf', Ah=sum_(e−f=h mod6) ae bara'_f,B=b barb',C=c barc'. Product=sum Ah Uh+BV1+CV2.
tau_e(j)=sum_y modp chip(y)^e e(jy/p), tau0(j)=q1_p|j−1. For e!=0 tau_e(j)=barchip(j)^e tau_e(1), retainingzeros.

Normalizedplus Fourier:
q^-2 sum_x modp² f(x)barf'(x)e(jx/p²)
=1_p|j/q *sum_h Ah tau_h(j/p)+B/q²(q1_p|j−1)+C/q². (9)
Atj0 mean=(1−q^-1)A0+(q−1)B/q²+C/q². (10)
Controls:<L,1>=<L,Ue>=0,<L,L>=1−1/q;
<Ue,Uf>=(1−1/q)1_e=f;<D11,1>=−1;<D11,D11>=2−1/q;<D22,D22>=1−1/q.
Lhat(j)=−q^-1 1_p∤j. Unit-characterprime minimalperiodp, ramifiedV1/V2 needs p². CanceledexponentkeepsU0.

ChooseperiodM_lambda dividing b*ab; M=lcm(M_lambda,M_lambda').
A_pair(n)=qM^-1 sum_x modM phi_lambda(x)barphi_lambda'(x)e(nx/M).
Atlocalp^a use n_p=n(M/p^a)^(-1)modp^a inlocalFourier. FixedS pairedfactor|xi|² originalunitmask, exactFourierretained.
g_lambda(r)=qMlambda^-1 sum_x phi_lambda(x)e(rx/Mlambda).
A_pair(n)=sum_r,s g_lambda(r)barg_lambda'(s)1_[(M/Mlambda)r−(M/Mlambda')s=n modM]. (13)
W_pair,Q(x)=rho_Q(x)F_lambda,Q(x)barF_lambda',Q(x).
E_Q=Q sum_lambda,lambda' c_lambda barc_lambda' sum_n inO A_pair(n)Wtilde_pair,Q(Qqn/qM)=D_Q+O_Q. (14)
D is n0, Oalln!=0 includingprincipalproductnonzero modes. PrimalH0 distinctandabsent. FiniteouterlabelsatfixedZ, Schwartztailsabsolute; nocontourshift.

## Long-divisor allocation (15)–(18)

d1=t a,d2=t b,r=ab,(t,r)=1,t,r sf,a|r,b=r/a. Then d1d2=t²r,mu(d1)mu(d2)=mu(r).
N_T,D1,D2(t,r)=sum_a|r 1_qtqa>T 1_qtqr/qa>T omega1(qtqa/D1)omega2(qtqr/(qaD2))>=0, <=d(r). WithoutdyadsN_T.
InnerTypeII=sum_t,r sf,(t,r)=1 sum_k good mu(r)N_T(t,r)eta(t²rk)/(qt²qrqk) barchi_(t²rk)(H)1_(t²rk,gPv)=1 timesoriginalV andW0tilde evaluatedatproduct. Allouterfactorsunchanged. No(t r,k)condition.
Allallocationsfixedproducthaveidenticalsignmu(r), so absoluteallocation sum=N_T. t²witht>T gives+1, disprovingaddedcoprimality. No globalcancellationno-goorlowerbound.

## Complete periodic Gram (19)–(26)

ReferencefamilyPhi_c,s(H)=Lg(H)barchiu(H)chiv(H), c=gu,s=gv; g,v sf,(g,v)=1,(u,gv)=1,u arbitrary. qc~C,qs~B,coeff|b_c,s|<=K/C. Claimcompleteperiodnorm
||sum_c,s b_c,s Phi_c,s||per² <<eps(CB)^eps K² B/C. (19)
Proof: p|g notg' givesmean0 by<L,1>=<L,Ue>=0, henceg=g'. Decomposeu=n t6^6,n sixthpowerfree,n=w z^5, w exponents1..4,z sf,(w,z)=1. Nontrivialcharactersignatureis(w,h),h=zv: z andv bothgiveexponent+1. Sixthpowerpartretainsextraunitmasks. Differentsignaturesorthogonal; same signaturemaskmeansabs<=1. Fixg,w,h; choicesz|h costd(h)byCauchy. Thenv=h/z,n=wz^5 fixed. U=C/qg,V0=B/qg; #t6 with qn qt6^6~U <<(U/qn)^1/6 fornonemptyrange, includingunitboundary. Sum_n<=CU,v~V0 counts² <<V0 U1/3 sum_n<=CU qn^-1/3 <<V0 U. Sumg givesCB sumg^-2. CoeffK²/C² proves(19). Keepsaliases u multipliedbysixthpowers and u=p5,v=q vsu=q5,v=p.

Actualselectedfactors expandbyQ2subsetidentity: R|P,a=Rc,b=Rs,D=P/R. In eachsummand s sf,sharedprimes c,s exponent1inc; selectedvaluationsc,s0/1, nonselectedc arbitrary. FrequencyfamilyPhi_c,s. Exact1/qa=1/(qR qc), baretaP eta(a)=baretaD eta(c), qa/(ZqP)=qc/(ZqD).
g0=(c,s),gold=g0/(g0,P),cP=(c,P),sP=(s,P),u_P;c,s=c/(gold cP).
C10(P;c,s)=prod_p|P,vp(c)=1,vp(s)=0 p.
ForfixedR, periodicpolynomial(excludingbarxi):
(wR/qR) sum_c,s eta(c)/qc W1(qR qs/Y)W0tilde(XQx/(qR qc)) Phi_c,s(H)
 *sum_D inremaining slots,admissible wD baretaD mu(R)mu(C10(RD;c,s)) A_T(u_RD;c,s)V(qc/(ZqD)). (22a)
HereA_T=mu_gt*mu_gt*1, |A_T(u)|<=d3(u),u|c. AdmissibilitykeepsD|c andoriginalstates/masks. Selectedresidual10addsminusvia mu(C10); frequencyfamilyitselfhasnoinventedmu.
SumactualDtuplesBEFOREnorm: D|c impliesatmostd(c) assignments(disjointslots); originalD-dependentprofilekept. Groupedcoefficient(excludingwR/qR)<=Zeps/qc h_A(Q/Q*).
Forrescaledlengthd, C_R~Z^(1+1/6−d),B_R~Y/qR, B_R/C_R~Y/(ZP*). Mean-normfrom(19)<=Zeps sqrt(Y/(ZP*))h_A. MinkowskiRcostsum_R|wR|/qR<<1 byslotharmoniccounts; finitelymanysubsets. Thisretainscross-tuples.
LetF_x actualperiodicpolynomialexcludingbarxi. Then
D_Q=(2pi/sqrt3)Q rhoS integral rho_Q(x)||F_x||per² dx>=0, rhoS=prod_p inS(1−1/qp). (25)
ThereforeD_Q<<Zeps QY/(ZP*)h_A². AtQ*energy1/8 andphysical(sqrtX/Y)sqrt(Q*D_Q*) exponent1/6. D only, notE.

## Nonzero conductor and complement (27)–(31)

Allowedgenericbranch: allselected10,g1,k1, a,b,a',b' squarefreepairwisecoprime. Paircharacterpsi(H)=barchia(H)chib(H)chia'(H)barchib'(H), exactgoodconductorr=aba'b'. qa~A=Z7/6,qb~B=Y,qr~(AB)². Eachlocalexponent±1.
Transform=q_r^-1 tau_r(psi)barpsi(n), tau_r=prod_p|r chip(r/p)^ep tau_p,ep(1). Abs=qr^-1/2 at(n,r)=1, zerootherwise, fixedSfactorretainedseparately.
DualnormK=qr/Q*=Z119/48. Fourierabsolute budget sqrt(qr); directsumO(Q) smallerbutnogain. Notlowerbound.
Genericcongruence a'b' r_index−ab s_index=n modaba'b'. NonzeroGaussweightsforcer_indexunitatab ands_indexunitata'b', hencenunitatconductor, NOTconductordividesn. Validcomplement y=(a'b' r_index−n)/a retainsresidueterm. Withq_rindex<<AB, qy<<[(AB)²+qn]/A<<AB²(1+Q^-1)=Z17/8attransition, notqn/A. Ramifiedsharedprimesmayimposedivisibility, cannotglobalizeit.

## Two-long direct-sum interface (32)–(40)

FixP,states,g; R0=q_(gP22P11),W=DeltaP Lg. Importedweightedallsieve squarefreecolumnsq_r<=D:
sum_H~Q |W sum_r br barchirH|² <<eps(QDR0)^eps[Q+D sqrtQ R0+(QDR0)^2/3]sum_r|br|². (32)
Forfixedpuncturem,A_H,m(U)=sum_(u,m)=1 A_T(u)eta(u)barchiuH/qu F(qu/U), claim
sum_H |W A|² <<eps(QUR0)^eps[Q/T²+sqrtQ R0+(QR0)^2/3 T^-2/3]. (33)
Fix t,k after(17): r sf lengthD~U/(qt²qk),columnmass<<Zeps/(Uqt²qk). Outsidebarchi_(t²k)Habs<=1. ThreeL2terms:
sqrt(Q/U)/(qt sqrtqk), Q1/4R01/2/(qt²qk), Q1/3R01/3 U^-1/6/(qt5/3 qk5/6).
Cutoffs giveqk<<U/T²,qt<<sqrt(U/qk). Minkowskit,k withsumsqt^-1 log,qt^-2 const,qt^-5/3 const andksum exponents1/2,1,5/6 gives
||WA||2 <<Zeps[sqrtQ/T+Q1/4 R01/2+Q1/3R01/3T^-1/3]. (36)
Units/empty/boundedsubunitscaleshandled; sharpcutoffsinsidecoefficients.

Keepu-vcoprimalityby1_(u,v)=1=sum_f|u,f|v mu(f).
A_f(H)=sum_(u,gP)=1,f|u A_T(u)eta(u)barchiuH/qu F(qu/U);
V_f(H)=sum_v sf,(v,gP)=1,f|v chivH W1(qv/B), U=ZqP/q_aPg,B=Y/q_bPg.
Thenactualsum=sum_H,f barxiH W_H mu(f) A_f(H)V_f(H).
JointCauchy(H,f)<= [sum_H,f|W A_f|²]^1/2 [sum_H,f|V_f|²]^1/2. (38)
Directsumcolumninterface: fixedt,k sum_f sum_r|b_tkr|²1_f|t²rk <=sum_r|b_tkr|²d(t²rk)<<Zeps/(Uqt²qk). (39)
Apply(32)atfixedf,t,k thenMinkowskiinl2(H,f); firstfactorstill(36). Coefficientneednotindependentf, onlyH.
Secondfactor: sum_f sum_v:f|v |W1|²<=sum_v~B d(v)|W1|²<<Zeps B, v sf. Unweightedallsievegives
||V_f||_(H,f)<<Zeps[sqrt(QB)+Q1/4 B+Q1/3 B5/6]. (40)
No multiplicationofunrelatedgains.

## Outer budget and tails (41)–(48)

Restore1/q_aPg. Forproductsnormtermsouterfactor
sum_P,states |wP|sum_g (q_aP qg)^-1 [Y/(q_bP qg)]^beta [qg qP11 qP22]^theta,
beta in{1/2,1,5/6},theta in{0,1/2,1/3}. gpower−1−beta+theta<=−1; endpointbeta=theta=1/2 giveslogZfiniteactualrange, notconvergentinfiniteg-sum. Othersconverge. Selectedfivepowers−1,−1−beta+theta,−1−2beta,−2−beta,−2−2beta+theta all<=−1, soharmonictuplescostO1.
Thus |TII,Q|<<Zeps h_A [sqrtQ/T+Q1/4+Q1/3T^-1/3][sqrt(QY)+Q1/4Y+Q1/3Y5/6]. (43)
AtQ* firstpowers5/32,13/64,3/16; second31/48,131/192,193/288. Physicalnineentries:
row1:1/2,103/192,151/288;
row2:35/64,7/12,329/576;
row3:17/32,109/192,5/9. Max7/12 fromsqrtX Q*1/2, noT gain. RetuningTdoesnotremoveitwithinthisbound.
ProfileV(y)W0tilde(bh/y),b=XQ/(ZqP),h=qH/Q,ycompact. LoghFourierseparationuniformatb0, Schwartzhighb; commonmeasureindependentf. FullnonunitQsumdominatedQ* asallQpowerspositive<=1. FulldualPoissontailsretained. UnitH: g1,noD22,otherselectedabs<=1, harmonicu divisorbound; physicalunitO(Z17/96+eps), all6phasesretainedbeforebound.
OldQ4freecofactorj0=−mH Wtilde0 prod_p|EH(1−1/qp) sum_e<=T,(e,hm)=1 mu(e)PsiH(e)/qe, plusunit-profileifpresent. Olddcompletionzero=1_R12=1 M m12 Wtildeii'0 prod_p|E12(1−1/qp). Bothremaininprimalexpression; neitheridentifiedwithnewD_Q norseparatelyboundedhere.

## Detector, consumer and next inequality (49)–(56)

Q2detector integralunchanged:
Psf_eta,V=(1/2pii)integral_Rex2 cS X1/3 Z^(x−5/6)Vhat(x−5/6)/L_F^S(x,eta)
 *sum_tuple wP prod_p|P qp^-5/6 Gsf_p(x,1,1/6) prod_p notinS,p∤P Hsf_p(x,1,1/6) dx.
LocalfactorsactualQ2sector, cS1/6Jacobian; nonzerointegrandnotphysicallowerbound.
DI=Lpsi MT²,DII=Lpsi(Lpsi^-1−MT)²,2MT−DI+DII=Lpsi^-1 onabsolutehalfplane. Artificialprincipalresiduecancellationnotdetectorcancellation; noMellinshiftorcenteringused.
N_eta=(sqrtX/Y)(−TI+TII)+R_eta,theta. R originalQ1nonprincipalphysicalsumwithmultiplier1−1_n1 1_s sf theta(qc/(ZqD)), originalVG(qc qn³/(ZqD)),D|cn³, phases/subsets/windows/sharedprimes. FourierHtail isNOTphysicalGaussiancomplement.
Fullconsumer|−TI+TII+(Y/sqrtX)R|<<Z^(47/96−delta+eps). C(s)=s−11/16, full low3/16−deltaformal7/8−deltaonly; RHneedsfull lowapproaching−3/16andcompatiblehigh/nonvanishing/margins.

ExactO_Q=Q sum_lambda,lambda' c barc' sum_n!=0 A_pair(n)Wtilde_pair(Qqn/qM). (53)
SufficientnewTypeIIonlytarget: some0<delta<1/96, everyeps, alllargerealZ,
sum_Q sqrtQ |O_Q|1/2 <<Z^(47/96−delta+eps). (54)
Attransitionlocalenough |O_Q*|<<Z^(1/6−2delta+eps). (55)
D_Q*1/8fitsdelta<1/48; unit17/96needsdelta<1/96. E>=0,D>=0,E=D+O, so|O|boundimpliesTypeIIgain, NOTfullconsumerwithoutTI/Rinterface. O signed, notdominatedbyD.
SameHenergytriangleonlygives E_Q<<Zeps Y²[Q/T²+sqrtQ+Q2/3T^-2/3]h_A², transition131/96. (56)
Thedifferent(H,f)contraction7/12doesnotimprove(56)byimplication.
Admissiblenextrepresentations: signedcubefreeproductreciprocitywithfullcongruence, ORrecombinefullphysicalcn³sourceandexactTIbeforethenextnorm. Eq54sufficientnotnecessaryforfullconsumer. No route-deathclaim.

## Reported checks and independent audit request

Pro reports1944allocationcontrols,507pairedlocalmeanrules,4632basisFouriercontrols,3276CRTphasecontrols attestnorms7,13,19(plus31allocation); plantedshareddivisorandD11valuationtwodeletionsdetected. ScriptstatedSHA256878bfb507343c699fa1055de954834cc7d2b356f691ef9ada6269cafd433846d. Root readcodeinfullbuthasnotyetreproducedit; no local execution certificate claimed. Finite checks do notproveanalyticGram/directsum/outerbounds.
Audit compositeclaim: exact(8)–(18),meanGram(19)–(25),directsum(33),(39),outer(41)–(46), especiallysixthpower/fifthpoweraliases, selectedR,Dregroup,D|c, fcolumnmass,g^-1logendpoint, units/tailsandallninefractions. Firstmismatchorboundedacceptancewithdependencies. RH/SP/Schur/G1/G3/scalarreserveandhighremainOPEN.

Independent bounded analytic audits completed: mobius_source_audit PASS for(19)–(25) and local/selected interface; squarefree_conductor_check PASS for(32)–(46) andgeneric(27)–(31). Root independently reproduced507exact paired means andallninefractions/zero/duallengthnormalizations. No full low/high/RH status changes.
