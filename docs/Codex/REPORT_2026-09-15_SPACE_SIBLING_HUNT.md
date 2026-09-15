# Mathematical-space siblings and a source-faithful rebuild

STATUS: BOUNDED_SOURCE_VERIFIED_DISCOVERY_AND_ANALYTIC_PREFLIGHT; final independent review belongs to the certificate.
SOURCE_BASE: c394a7d5c08b41231938820878fb9e5b6360dc63.
BRIEF: BRIEF_2026-09-15_SPACE_SIBLING_HUNT.md, SHA256 6197d49081d89c45e1afdbca6437a1290dabfcbce422c1196a9dfb191a47bb78.
CONSUMPTION: INCOMPLETE_NO_CONSUMABLE_TARGET. Full theta V and RH remain open. No canonical admission or new Proshka send.

## 1. Exact question and existing facts

The requested positive construction is one source-built family psi_x in one Hilbert space with V(x,y)=<psi_x,psi_y>, for every x,y in I=(-log(2)/2,0). Here f=Phi/||Phi||_2 is the full source and
V(x,y)=integral_0^infinity (2t+x+y)f(t+x)f(t+y)dt.
The common family would cover arbitrary finite complex coefficients. The basis, weight, domains and every boundary term are part of the identity.

The previous layer Gram, anchored Hardy, weighted null identity, and exact xi support maps were read first. Their successes and exclusions are retained. Three new registered queries (Fock; Krein graph; Schur defect) each returned ASK_STATUS INCOMPLETE because semantic-index freshness failed. This is not shelf absence. Local primary Ball 2007 was read before external discovery. Hall and Shkalikov fill specific missing mechanism references. No broad index repair or theorem admission was performed.

## 2. Sibling F: coherent vectors in Segal-Bargmann/Fock space

Primary: Brian C. Hall, Holomorphic methods in analysis and mathematical physics, arXiv:quant-ph/9912054v2, Definition3.3 pp9-10 and Theorem3.4 p10, https://arxiv.org/pdf/quant-ph/9912054v2 . PDF SHA256 648218cdd94c7005fe16e669e6f7701c18c89baca60da1b7b27fd29e9a648d4e. Short quote: "is an orthonormal basis" (p10, above Theorem3.4). Only these sections were read.
With Gaussian measure pi^(-1)exp(-|z|^2)dA(z), the entire monomials z^n/sqrt(n!) are orthonormal and the kernel is exp(z conjugate(w)). This provides an explicit common feature construction, not an abstract square root of the desired kernel.

Our already proved quartic formula L3-L5 is precisely this mechanism:
f(u)=C exp(-a u^4-bu^2), a>0,b real;
K_s(x,y)=w_s(x)w_s(y)exp(4asxy),
w_s(x)=C exp(-as^2-bs-(4as+b)x^2-a x^4).
For real x use z=sqrt(4as)x. Its feature vector is
psi_x(s,n)=w_s(x)(sqrt(4as)x)^n/sqrt(n!).
The common space is L2(ds;ell2). The inner product integrates K_s and equals V for every finite family, with no omitted mixed term. The Gaussian limit has a=0,b>0. This is a newly source-verified NAME/MAP for an existing project proof, not a new theta theorem.

Strength: EXACT on this separate quartic source family; NOT an exact theta fit. For actual theta L13 already supplies negative small layers, so applying this map independently to each layer is false. The f0=e^(-u^2)-e^(-2u^2)/4 control lacks the required quartic exponential factorization; its negative four-node V remains consistent. An integrated construction mixing layers is not excluded.

## 3. Sibling K: positive graph in an indefinite space

Primary: A.A. Shkalikov, arXiv:math/0701410v1, Theorem2.1 pp4-5, Lemma2.2 p5, https://arxiv.org/pdf/math/0701410v1 . PDF SHA256 64746704b3b811a36810bf22763586ae66e78e76979559f7eb1fdca8c8459194. Quote (printed p4): "Тогда существует максимальное неотрицательное подпространство". Parent checked the rendered theorem pages.
The theorem assumes Krein dissipativity Re<JA u,u><=0, dense split domain D(A)=D_+ direct_sum D_-, maximal dissipativity of -A22, a bounded closure of (A22-mu)^(-1)A21, and compact A12(A22-mu)^(-1) for mu in the left half-plane. It yields a maximal nonnegative subspace invariant under the closure of A. Lemma2.2 represents such a subspace as graph(K), ||K||<=1.

Our exact map uses H=L2(mu_a), J=diag(I,-I) on H direct_sum H, xi_x=(U_x,B_x) from ANCHORED_CONTRACTION_HUNT H1. Then [sum c_i xi_xi,sum c_i xi_xi]=S_a[c]/D(a). This covers every finite complex row and preserves normalization. Strength: CONDITIONAL CONSTRUCTIVE ANALOGUE. No qualifying theta-built A or proof that its positive graph contains all prescribed xi_x has been supplied. The theorem gives SOME graph. The negative f0 control has a vector of negative Krein norm; no nonnegative graph contains it. Thus membership cannot follow for an arbitrary source from the existence theorem alone.

## 4. Sibling S: Schur defect / de Branges-Rovnyak / hidden isometry

Primary: Ball, Biswas, Fang, ter Horst, arXiv:0705.2042v3, Theorem1.1 pp1-2, Proposition1.2 p2, proof pp2-3, https://arxiv.org/pdf/0705.2042v3 . PDF SHA256 34b63b910628595af152f354d448c3da4837a18d2043174735b674f172e3eebc. Quote (p3): "the now standard lurking isometry argument".
For a scalar Schur function q on the unit disk, (1-q(z)conjugate(q(w)))/(1-z conjugate(w)) is a positive kernel. A source-built coisometric block U=[[A,B],[C,D]] with q(z)=D+zC(1-zA)^(-1)B supplies the factor C(1-zA)^(-1). Conversely, positive-kernel data constructs a realization via a hidden isometry. Proposition1.2 makes abstract Gram existence equivalent to all-family positivity.

Mapping: q(z)=S(i(1+z)/(1-z)), S=(F-iF')/(F+iF'), F=xi(1/2-iz)/||Phi||_2. This is the previously source-locked exact transfer. Strength: CONDITIONAL EXACT SUFFICIENT MECHANISM. An independent positive realization matching this q would supply the missing support property; constructing it from assumed positivity is circular. The existing weighted realization only controls a shifted domain, not this disk. A matching realization for the negative f0 control cannot exist. No new realization is supplied here.

## 5. Original assembly tests prompted by the user's follow-up

### A. Positive source sums do not preserve positive V

Let f_a(u)=exp(-a u^2), a>0. Direct integration gives
V_(f_a)(x,y)=f_a(x)f_a(y)/(2a), a positive rank-one Gram kernel for all real nodes and complex rows.
For f(u)=sum_(j=1)^m p_j exp(-a_j u^2), p_j>0, a_j>0, compute

J11=partial_x partial_y V_f(0,0)
=integral_0^infinity [2 f(t)f'(t)+2t f'(t)^2]dt
=-f(0)^2+2 integral_0^infinity t f'(t)^2dt
=-sum_(j,k) p_j p_k ((a_j-a_k)/(a_j+a_k))^2.          (A1)

The last equality uses integral_0^infinity t^3 exp(-c t^2)dt=1/(2c^2).
Thus J11<0 whenever at least two rates differ. In particular, f=e^(-u^2)+e^(-2u^2) gives J11=-2/9.
Take actual allowed shifts x1=-h,x2=-2h and coefficients c=(1/h,-1/h), with 0<h<log(2)/4. Two finite differences give

V_f[c] -> J11=-2/9 as h decreases to zero.             (A2)

Therefore sufficiently small h gives a strictly negative two-node V_f even though each summand source separately gives a positive V. This is not a theta counterexample; this f does not have theta's squared-coordinate log concavity. Positive rescaling to L2 normalization leaves the sign unchanged.

What was omitted by the tempting inference? If f=f1+f2, then V_f=V_f1+V_f2+C12+C21, where
Cij(x,y)=integral_0^infinity (2t+x+y)f_i(t+x)f_j(t+y)dt.
Positive direct sums of the two independent Gram spaces represent V_f1+V_f2, not V_f. The cross terms remain part of the required exact reconstruction.

### B. Positive quartic mixtures cannot equal the actual theta source in this coordinate

Existing LAYER_GRAM_TEST L2-L5 supplies all-rank positive V for each
C exp(-a u^4-bu^2), a>0,b real,C>0, also a=0,b>0.
Suppose the full normalized theta source admitted a positive mixture

f(u)=integral exp(-a u^4-bu^2) dnu(a,b),               (B1)

with finite a>=0 and real b and nu a nonzero positive measure. Coefficients C are absorbed into nu. Evaluation at u=0 gives nu(total)=f(0), so the measure is finite. Some box {0<=a<=A, |b|<=B} has mass m>0 by countable exhaustion. For every u>=0,

f(u)>=m exp(-A u^4-Bu^2).                            (B2)

But the complete-source tail, already proved in FIRST_ORDER_COMPENSATION_PREFLIGHT F8-F10 and used in ANCHORED_CONTRACTION_HUNT H7, is
log f(u)=-pi exp(2u)+(9/2)u+O(1).
It is eventually smaller than log m-Au^4-Bu^2, contradiction. Therefore (B1) is impossible in the fixed logarithmic coordinate. This excludes positive discrete sums and positive measure mixtures of these quartic/Gaussian sources, not signed expansions, products, nonlinear coordinate changes with exact transform correction, coupled higher-dimensional lifts, or arbitrary limiting constructions. Even a feasible positive source mixture would still need the cross-kernel condition exposed in A.



## 6. A concrete reconstruction that DOES recover xi

The separate REPORT_2026-09-15_ARITHMETIC_RECIPROCITY.md proves one bounded candidate, using the existing exact r_N density rather than a different convenient source:

H_N(x)=[e^(5x/2)r_N(e^(2x))+e^(-5x/2)r_N(e^(-2x))]/2.

Its normalized Fourier transforms converge to xi(1/2-iz)/xi(1/2), uniformly on each fixed horizontal strip eventually in N. The source H_N is entire; no square root generates a source branch. Each Fourier integral has the finite strip |Im z|<4N+1/2, and these strips expand with N. The proof retains this price explicitly. The exact Mellin formula is in that report; zero location is NOT proved.

This is an independent reconstruction option made concrete, not a claim that changing the approximation alone solves RH. In particular, neither a positive source nor an entire source forces the Fourier transform to have only real zeros. The earlier source-preserving unitary coefficient counterexample already demonstrates that distinction.

## 7. Decision and continuity

We found three named mathematical-space mechanisms with different roles: an explicit exact model factorization, a constructive invariant-space theorem with unpaid target-membership hypotheses, and an exact sufficient analytic-realization interface whose source construction is unpaid. Their combination is not a new theorem; cross-identifications still must be proved.

The user's reconstruction idea has been tested in two ways: naive positive source mixing is invalid as a positivity-preserving rule, while arithmetic reciprocal assembly genuinely recovers the full source and removes a specified finite-source branch mechanism. There is no new actual-theta negative V, sign theorem, canonical CLOSES/OPENS or RH claim.

Publication-time update: Proshka answered CRITICALSTRIP at commit 08b6b69c5ff269297b04a87df128d8459ee3471b without interruption or replacement. Its independently reviewed Prékopa argument proves a uniform central zero-free slab for the actual geometric gamma family; arbitrary-R C6 remains open. REPORT_2026-09-15_CRITICALSTRIP_INTAKE.md records that fourth mechanism and compares it with the arithmetic family. Do not send another generic energy or Gram request, demand full-plane real-rooted approximants, or treat an absent obstruction as a sign proof.
