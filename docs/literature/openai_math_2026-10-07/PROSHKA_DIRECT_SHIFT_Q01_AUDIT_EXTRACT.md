# Direct Shift Q1: normalized full-answer extract

Full238 rendered blocks (35698 normalized characters) read2026-10-07 at14:04UTC in Paper derivation estimate, chat6ac647d1-c258-83ed-bf5b-fe98fe331ecf. Terminal Antwort abgeschlossen, regenerate and no Stoppen observed. Source response attachment PROSHKA_DIRECT_SHIFT_Q01_PAPER_VERDICT.md. This file is a manually normalized mathematical extract, NOT original response bytes. Exact request177830bytes SHA256e59ce3e0d09d157995c73f4b60454c29527cdb0816227e4150bb225f89bd2de2 remains unchanged.

Verdict: INCONCLUSIVE / NO_DERIVATION for terminal sign. Conditional component mathematics only. No smaller zero-free boundary, no RH, no route-family impossibility. External ZF78 remains unverified. No conductor-uniform Dirichlet/Hecke estimate used.

## (1)–(19): concrete shift and full compensation

eta=5/16,a=3/16,b=13/16. Constants and source are exactly SHIFTED_ARITHMETIC_RESERVE. Write A(x)=sum_(n<=x)Lambda(n)n^-b, Y=A-c, Delta=Y-x^a/a; v(x)=a Delta(x)/x^a post-event and u_r=a Delta(r-)/r^a pre-event. E(x) is the same frozen-prefix elementary reserve, constant between events. All prior powers remain in A.
Assume |psi_Ch(x)-x|<=C x^(57/64) on both traces, C>=1, from conditional ZF78 with epsilon1/64. Let lambda=c+b/a,K=|lambda|+57C/5 and Q0>=max(4,C^(64/7),(2aK)^(64/7)). Exact partial summation:
Delta(x)=-lambda+x^-b(psi_Ch(x)-x)+b int_1^x t^-b-1(psi_Ch(t)-t)dt.
Thus |Delta|<=Kx5/64 and |u|,|v|<=aKx^-7/64, hence <=1/2 pastQ0; psi_Ch(x)<=2x.
Entropy H(x)=x^a/a²[(1+v)log(1+v)-v]>=0 has derivative -Delta/x between events and jump w_r log(1+u_r)/a+ell_r. With S=sum_(Q<r<=X)w_rlog(1+u_r), L=sumell, I=int_Q^X Delta(x)/x dx:
S/a+L=I+H(X)-H(Q),
E(q)=E(Q)+H(Q)-I(q)-H(q).
These hold for every real X>=Q, with post-event anchor and pre-event jumps. This matches the independently derived root entropy return.

## (20)–(39): signed prefix, energy and quantitative tails

Cprefix=sum_(Q<r<=X)Lambda(r)Delta(r-)/r,
J=(1/a)sum w_r[u_r-log(1+u_r)]>=0; S/a=Cprefix-J.
Exact BV square identity:
Cprefix=I+[Delta(x)²/(2x^a)]_Q^X+(a/2)int_Q^X Delta(x)²x^-a-1 dx
 -(1/2)sum_(Q<r<=X)Lambda(r)²/r^(1+b).
The negative jump diagonal is essential. Consequently J-L equals the displayed square boundary minus[H]_Q^X plus the quadratic integral minus diagonal. None is an independent favorable reserve after full recombination.
For |v|<=1/2, v²/3<=g(v)<=v²; 0<=u-log(1+u)<=u². Therefore
0<=H(X)<=K²X^-1/32,
0<=J(Q,infinity)<=66aK²Q^-1/32=(99/8)K²Q^-1/32,
0<=L(Q,infinity)<=BL(Q)=Q^-b[(logQ)²/b+2logQ/b²+2/b³],
(a/2)int_Q^infinity Delta²x^-a-1<=3K²Q^-1/32.
Here sum_(r>Q)Lambda(r)r^-s<=2s/(s-1)Q^(1-s); diagonal<=BL/2. All constants depend on the conditional C, not certified numbers.
Available |I(X)|<=64K/5(X5/64-Q5/64) is only magnitude, not the terminal constant ceiling.
Proper-power EVENT drift (not their prefix contribution) has full absolute tail
P(Q)=6K sigma/log2 *Q^-tau[logQ/tau+1/tau²], sigma59/64,tau27/64.
Proof uses weighted count sum_(p^j<=x,j>=2)logp<=3sqrtx logx/log2 and strict lower cutoff. If Cp,Jp retain only prime events but all earlier powers inside Delta(p-), then
M(q)-P(Q)<=E(q)-d_q<=M(q)+P(Q),
M(q)=E(Q)-Cp(q)+Jp(q)-L(Q,q)-d_q.
The net signed Cp-Jp bound remains OPEN.

## (40)–(51): original source return, tilt and pole discriminator

W_eta(x)=int_1^x v^-b-1[1+b log(x/v)](psi_Ch(v)-v)dv.
The full prime-power ramp equals the same integral with psi_Ch. Its continuous main term is(x^a-1)/a²-(b/a)logx. With kappa=k+a^-2=R_eta(0),
Psi_eta(logx)=lambda logx+kappa-R_eta(logx)-W_eta(x),
E(q)=lambda logq+kappa-W_eta(q)-H(q),
I_Q(X)=W_eta(X)-W_eta(Q)-lambda log(X/Q).
The complete shifted Selberg identity LF_eta+F_eta'*F_eta'=R_mu,eta survives because m^-b n^-b=(mn)^-b. Lf=tf-2int_0^t f; R_mu has (mu*log²)(n)n^-b ramp coefficients. Substituting F=B-Psi retains both convolution cross terms and the negative Psi'*Psi'; it is not a norm square. Initial values vanish and B' is locally integrable despite its logarithmic singularity. No source gain follows.
For omega3/8,h=omega-eta=1/16,alpha1/8, Abel summation gives
Delta_eta(x)=x^h Delta_omega(x)-h int_1^x v^(h-1)Delta_omega(v)dv+cstar,
cstar=c_omega-c_eta+h/(alpha*a).
Hence I_eta,1(X)=int_1^X v^(h-1)[1-h log(X/v)]Delta_omega(v)dv+cstar logX.
The kernel changes sign at v=X exp(-1/h); positivity of Psi_omega alone does not pay it.
For Laplace variable z, initially Re z>a,
Ehat_eta(z)=z^-2 xi'/xi(b+z)+Rhat_eta(z)-Hhat_eta(z).
Hhat is holomorphic Re z>-1/32, Rhat=sum_(j>=1)[(2j+b)²(z+2j+b)]^-1 holomorphic Re z>-(2+b). Therefore any actual zero rho with Re rho>b, IF one exists, gives uncancelled residue m_rho/(rho-b)². This is meromorphic continuation, not a claim of integral convergence there or existence of such a zero. Finite initial intervals add entire functions; subtracting a constant adds only a pole at0. The original source coefficient remains1.

## (52)–(62): exact and clipping-aware terminal budgets

Elementary sufficient target: I_Q(q)+H(q)+d_q<=E(Q)+H(Q), every sufficiently late prime power; d_q=256/2025*q^-45/16/(1-q^-2). It is not proved.
For cell Iq=[logq,logqnext], t*=log(aY(q))/a, tau=clip_Iq(t*), hq=tau-t*,
Cq=Y(q)/a[exp(a hq)-1-a hq]>=0,
Vq=E(q)+Cq-R(tau)=Psi(tau).
Within cell Psi''=exp(at)-exp(-(2+b)t)/(1-exp(-2t))>=5q^a/6.
0<-R'(tau)<=q^-(2+b)/[(2+b)(1-q^-2)]. Strong convexity and projection sign give
Vq-epsq<=min_Iq Psi<=Vq,
epsq=3/[5(2+b)²]*q^-(5+b)/(1-q^-2)²
 =256/3375*q^-93/16/(1-q^-2)².
At tau=logq, full derivative is positive and minimum exactlyVq. New upper-endpoint ramp is zero, so junction value remains correct.
Weaker sufficient target(61):
I_Q(q)+H(q)-Cq+R(tau)+epsq<=E(Q)+H(Q), every sufficiently late prime-powerq.
It dominates the elementary lower envelope at this shift: d_q-R(logq)>=q^-(4+b)/(2+b)²[1-(45/77)²]>epsq. Ratio lower bound atq2 is7320/5929>1 and increasing. Thus V-eps>=E-d. NegativeV disproves that cell's nonnegativity; negative lower bound alone does not. Finite cells do not prove eventual sign.

## Reported checks, audit and next decision

Pro reports symbolic identities and75-digit floating controls through64, including planted wrong-loss signs; these were NOT reproduced and are not certificates. Universal claims rely on the paper formulas.
Requested audit target: ETA_5_16_FULL_HISTORY_COMPENSATED_RETURN, identities(2),(4), entropy bound with every real endpoint; reject omitted diagonal/reversed loss/deleted history. Root additionally selected the new clipped-cell lower envelope for independent checking.
Pro suggests a source-specific dual certificate for the signed Abel kernel, or a strict-order two-variable Mellin pairing with all subtractions and residues. These are unproved suggestions, not suppliers. Do not send Q2 before this response is audited and an own bounded attempt/alias return identifies a genuinely new input. No terminal sign progress; original arithmetic source remains OPEN.
