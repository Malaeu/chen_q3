# Q3 signed Mobius dispersion — normalized mathematical extract

Full rendered PROSHKA_VERDICT_SIGNED_CORRELATION_Q03.md read at09:04UTC2026-10-07,200 blocks/about37672 characters. This is a manually normalized extract, NOT original answer bytes. Request SHA2561f9423ac7c532176bfe8d945c933222adbc68a65c921388c80855c97d1d49958,790389 bytes; source SHA25642a5ee0febca59fd1def55cfd6c6808c322ef4237d7726303ea52f711deac6a3, pinned adc7f1241b42e322a6451854ab7e4b4c146bf78a. Same Execute Joint Probe Calculation chat /c/6ac5dfb3-b068-83ed-810a-dc77fa77ebbd. Predecessor ee31a5d5.
Verdict: exact representation progress, no full exponent gain, RH/SP/Schur/G1/G3/scalar reserve OPEN. Conditional source inputs not a certification of full7/8 theorem.

## (1)–(4) correct Mobius variable

C_eta,V is Q2 common-lattice sum without sqrtX/Y, X=Z17/48,Y=Z23/48,qP~Z1/6, V=VG theta annular. At selected primes retain states(1,0),(1,1),(1,2),(2,1),(2,2); set aP=productp^ap,bP=productp^bp. Write a=aP*g*u,b=bP*g*v, initially g,u,v squarefree pairwise coprime and prime toP. Q2 Lp=1_vpH=1−(qp−1)1_vpH>=2, Lg=productp|g Lp; DeltaP=product selected Dp. Then
K_P(a,b;H)=DeltaP Lg mu(u) barchi_u(H)chi_v(H).                   (2)
Use mu(u), NOT mu(a), which would kill selected squares. Extend u to all good ideals with (u,gPv)=1 before convolution. Define C[f] by replacing mu(u) with f(u) in that extension. Its summand is
w_p bareta(P) eta(aPg)/(q_aPg) W1(q_bPgv/Y) f(u)eta(u)/qu
 * V(q_aPgu/(ZqP)) barxi(H)DeltaP Lg barchi_u(H)chi_v(H)
 * W0tilde(XqH/q_aPgu).                                         (3)
g,v remain sf,(g,v)=(gv,P)=1; H allnonzero good elements including units. Unit projector from Q2 retained. Since qa/qb~Z11/16 and q_aP/q_bP<=qP, every support has
c Z^(25/48)<=qu<=C Z.                                           (4)

## (5)–(7) exact truncated convolution

T=Z1/4, mu_le=mu*1_qd<=T pointwise, mu_gt=mu−mu_le, betaT=mu_gt * 1 (Dirichlet convolution on good ideals).
mu=2mu_le−mu_le*mu_le*1+mu_gt*betaT.                             (5)
C[mu_le]=0 eventually by(4), so C_eta,V=−TI+TII, with TI=C[mu_le*mu_le*1],TII=C[mu_gt*betaT]. (6)
TI coefficient at u is sum_rsk=u,qr,qs<=T mu(r)mu(s); TII is sum_dnu=u,qd>T mu(d)betaT(nu). No added pairwise coprimality/squarefree-product constraint: nonsquarefree products cancel in(5). Every mask/profile/character uses the entire product u.
For nu>1, betaT(nu)=−sum_e|nu,qe<=T mu(e).                       (7)
If all primes of nu have norm>T, betaT(nu)=−1, even nonsquarefree. If nu=s*t,(s,t)=1,1<qs<=T and allprimes t>T, betaT(nu)=0 by divisor summation. Not a density bound. Controls:T10,normprimes7,13 gives beta(p7p13)=0 !=mu=1; atp13² TI=TII=1 cancels to mu=0.

## (8)–(12) full joint TypeII and one Cauchy

Label lambda=(tuple,aP,bP,g,nu,v,H), qnu>T, nu good,(nu,gPv)=1; g,v sf with previous masks, H allnongzero good elements/units. m_lambda=gPv.
c_lambda=w_p bareta(P) eta(aPg nu) betaT(nu)/q_aPg nu * W1(q_bPgv/Y)
 *barxi(H)DeltaP Lg barchi_nu(H)chi_v(H).
F_lambda,M(t)=V(Mt q_aPg nu/(ZqP)) W0tilde(XqH/(Mt q_aPg nu)).     (8)
TII=sum_d good,qd>T mu(d)eta(d)/qd * sum_lambda c_lambda barchi_d(H)1_(d,m_lambda)=1 F_lambda,M(qd/M). (9)
M auxiliary cancels. Insert fixed nonnegative smooth dyadic rho(qd/M), O(logZ) scales T<qd<=CZ/T. Then
|TII,M|² <= [sum_qd>T rho |mu eta|²/qd²] E_M << M^-1 E_M,        (10)
E_M=sum_d good rho(qd/M) |sum_lambda c_lambda barchi_d(H)1_(d,m_lambda)=1 F_lambda,M(qd/M)|². (11)
All good d, not only squarefree. Enlargement includes exact positive cutoff term
Bcut_M=sum_qd<=T rho |inner|²>=0, supported M~T.                 (12)
The sharp boundary is kept in(9), not setzero.

## (13)–(23) exact completed covariance

For H=epsilon*h,H'=epsilon'*h' primary good h,h', e_p=vp(H')−vp(H) mod6 in0..5.
R12=product_e_p!=0 p; E12=rad(HH' m_lambda m_lambda')/R12;
psi12(z)=product_p|R12 chi_p(z)^e_p.                            (13)
R12,E12 disjoint squarefree, primitive moving conductor exactlyR12, canceled exponents keep masks. Reciprocity on primaryd:
barchi_d(H)chi_d(H')=barchi_d(epsilon)chi_d(epsilon') R(d,h)R(d,h') psi12(d)1_(d,rad(HH')/R12)=1. (14)
Fix ell supported onS sufficiently divisible for primary normalization/fixedunit/reciprocity factors. Define ell-periodic
phi12(z)=1_{z=1mod3,(z,S)=1} barchi_z(epsilon)chi_z(epsilon')R(z,h)R(z,h'), zero branch evaluated withoutsymbols. (15)
Fixed primitive conductor after resolution is oneof fixedfamily fS|ell timesR12.
W12(t)=rho(t)F_lambda,M(t)barF_lambda',M(t); Wtilde12 itsradial Fourier transform withsource e(-zy).
S12(M)=sum_d good W12(qd/M)barchi_d(H)chi_d(H')1_(d,m_lambda*m_lambda')=1
=sum_f|E12 mu(f)psi12(f) M psi12(ell)tau_R12(psi12)/(qf qell qR12)
 *sum_k inO barpsi12(k) A12,f(k) Wtilde12(Mqk/(qf qell qR12)),     (16)
A12,f(k)=sum_x modell phi12(fR12 x)e(kx/ell),
tau_R(psi)=sum_y modR psi(y)e(y/R)
=product_p|R [chi_p(R/p)^e_p sum_y modp chi_p(y)^e_p e(y/p)].      (17)
CRT uses z=R x+ell y, fixedphi(fRx), movingpsi(ell)psi(y). Allidealnormprefactors asdisplayed. ForR!=1 |tau|=sqrt(qR); nonunit frequencytransformzero. ForR1 setpsi1(k)=tau1=1 evenk0.
E_M=sum_lambda,lambda' c_lambda barc_lambda' S12(M).             (18)
Allnu,nu',v,v' andcrosstuple signs retained.

Let m12=(1/qell)sum_x modell phi12(x). Zero dualfrequency:
S12^0(M)=1_R12=1 M m12 Wtilde12(0) product_p|E12(1−1/qp).        (19)
Fixed mean independentoff via x->fx. If H,H' have same sixth-power-free part including unit, fixedcharactertrivial and meanpositive. Otherfixed/unitcoincidences mustuseformula, notassumemeanpositivefromR1alone.
Identicalcharacter normalization:mS=1/9 product_p inS,p!=lambda(1−1/qp), Wtilde(0)=2pi/sqrt3 integralW; product=κS=pi/(3sqrt3)product_p inS(1−1/qp).
D_M=sum c barc' S^0 contains ALLcofactors anddenominator pairs in eachmatchingfrequencyclass, not justidenticaltriples. Itiscompleteperiodprojection/coprimalityGram.
E_M=D_M+O_M, O_M allk!=0 evenwhenR1.                            (20)
IndividualR!=1 estimate:
|S12|<=C_A,W sum_f|E min{M/qf, sqrt(qR)(1+M/(qf qR))^-A}.        (21)
ForR1 nonzerofrequency part <=C_A,W sum_f|E(1+M/qf)^-A inadditionto(19). SmallM/qf handledbyannularsupport. Fixedellconstantonly.
Dualnormlength K12,f=qell qR qf/M.                              (22)
Tail qk>K12,f B,B>=1 boundedby
C_N B^(1−N)sum_lambda,lambda' |c c'|sqrt(qR)d(E)p_(2N+4)(W12).    (23)
FullHrange retained viaSchwartzdecay ofseminorms; noassumedfinitefrequencyidentity.

## (24)–(27) actual cofactor mean and artificial residue

For good squarefree punctureR, MR(T)=sum_qe<=T,(e,RS)=1 mu(e)/qe, rhoR=product_p|R(1−1/qp). N>=T>=1, smoothannularF:
sum_(nu,RS)=1 betaT(nu)F(qnu/N)
=F(1/N)−κS N rhoR(integralF)MR(T)+O_S,F(d(R)sqrt(NT)).           (24)
Harmonicversion:
sum betaT(nu)/qnu F(qnu/N)
=F(1/N)−κS rhoR(integral F(t)dt/t)MR(T)+O(d(R)sqrt(T/N)).         (25)
Frombeta=delta1−mu_le*1 andidealcounterrorO(d(R)(sqrtL+1)),L=N/qe>=1. AtN=Z1/2,T=Z1/4 errorZ^-1/8+eps; principalmeanMR has trivial O(logT) growth, but no power decay or useful cancellation estimate is proved; nonvanishing is not asserted. Onlyprincipal-targetspecialization, notfullweightedcovarianceestimate.
For fixedH,g,v,P, psi(u)=eta(u)barchi_u(H)1_(u,gPv)=1, Lpsi=sum psi(u)qu^-s, MT=sum_qe<=T mu(e)psi(e)qe^-s. Onabsolutehalfplane
DI=Lpsi MT²; DII=Lpsi(Lpsi^-1−MT)²;
2MT−DI+DII=Lpsi^-1.                                            (26)–(27)
Forprincipalinducingcharacter the artificialpoleat1 has equal residue ResLpsi*MT(1)² inDI,DII andcancels. ThisisNOTtheQ2detectorresidue. Nocontourthroughzerosmoved.

## (28)–(31) balanced fibre budgets

Allowed fibre:aP=P,bP=1,g1,M=qd~Z1/2,N=qnu~Z1/2,B=qv~Z23/48,C=qH~Z13/16. Selectedfactor mu(P)barchiP(H). Allactualbeta,eta,masks remain. CoprimesquarefreeH,H' give qR~C²=Z13/8, dualK=C²/M=Z9/8. Noindividualcompletiongain since sqrt(qR)=C>M.
Forbudgetonly, triangleovertuples, factorout1/(qP MN), Erawmaxper-tupleunweightedenergy. CounttuplesZ1/6 cancels1/qP, giving
|C_II,fibre|<<Z^-1+eps sqrt(M Eraw).                             (29)
Energy exponents/physicalbound aftersqrtX/Y:
- Entry-only diagonal M*N*B*C:55/24 ->3/32, INVALID: deletedcrosscofactors.
- Absoluteactualzero-mode envelope M*C*(N*B)^2:157/48 ->7/12, partialupperbudgetonly.
- Fulltrivialenergy M*(N*B*C)^2:49/12 ->95/96, validbutinsufficientfibrebound.
Sixthpowerratiofrequency pairs countO(C^(1+eps)) via H=u*a6 andsum_qu<=C(C/qu)^1/3<<C. Doesnoterase nu,v crossindices.
NeededfibreEraw<=Z^(119/48−2delta+eps).                          (30)
FullTypeII sufficient condition sum_M M^-1/2 sqrt(E_M)<=Z^(47/96−delta+eps), orindividual E_M<=M Z^(47/48−2delta+eps). (31)
Notproved/notsaidnecessary; TypeI andphysicalcomplement couldcancel.

## (32) second-transform partialphasebridge

Forcoprimesquarefree primaryh1,h2,psi=barchi_h1 chi_h2:
tau_h1h2(psi)/sqrt(qh1h2) * gamma_-1(h1) bargamma_-1(h2)
=R(h1,h2)chi_h2(-1) gamma_-1(h1)^2 gamma1(h2)^2
=R(h1,h2)chi_h2(-1)mu(h1)mu(h2)baralpha(h1)alpha(h2)barG(h1)^2G(h2)^2 bargamma2(h1)gamma2(h2). (32)
Uses gamma1(h)^2=mu(h)alpha(h)G(h)^2 gamma2(h). Completingbeta'sfreecofactor thusregeneratescubiccoefficients withMobius/angular/rayfactors. Relativebaralpha(h)gamma2(h), extraalpha(h)^2 ispresent. DoesNOTconstructfixedcuspeigenform. Noncoprimepairs,fixedtargettransform,masks,shortdivisors,profiles stillneedmatching.

## (33)–(36) unchangedfullconsumer

Q2physicalprincipalresidue retained as(1/2pii)integral_Re x=2 ofQ2(18); noleadingcontributionsubtracted. Artificialconvolutionpolecancellationnotdetectorcancellation.
ForupperHtail qH>(ZqP/X)Z^kappa, crude |K_P|<=qP qb andSchwartzdecay give physicaltail<=Z^(2+eps−kappa(N−1)), alsoTypepieceswithdivisorloss. Pre-round exponent173/96. Dualtailseparately(23); sharpcutoffboundary(12).
N_eta=sqrtX/Y(−TI+TII)+R_eta,theta,                             (35)
withoriginalQ2complement, all n>1,primepowerss,remainingGaussian,masks,phases. Weakestfullboundhere:
|−TI+TII+(Y/sqrtX)R_eta,theta|<<Z^(47/96−delta+eps) all largeZ.    (36)
NoTypeI/complementimprovementproved. Source-reportedfulllow3/16 unchanged,C(s)=s−11/16; RHrequireslowapproaching−3/16 pluscompatiblehighdomains/targetuniformmargins.

Reportedexactcontrols:576truncatedconvolutioncases,159rough/36mixedcofactorcases,288kernelfactorcases,195finiteFourierchecks at7,13,19, rationalbudgets; notindependentlyimportedcertificates. Independentdirective(2)–(23), support/cutoff,CRT16–17,coherentzero-mode19,budgets28–31. Proposednextrepresentation: expandbeta=delta−mu_le*1 insidecompletedenergy, completefreecofactor BEFORE anotherinequality; match(32) withallremainingphasesandnorms. Anothergenericnormorentrydiagonalcountisnotanestimate.
