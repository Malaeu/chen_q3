# STATUS: TRY_GREEN_REDUCED_RESPONSE_WITH_ESCAPING_BULK_ANCHOR
```yaml
OPERATIVE_CLASS: TRY_GREEN_REDUCED_RESPONSE_WITH_ESCAPING_BULK_ANCHOR
REQUEST_ID: REQ-2026-10-30-GREEN
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
SOURCE_BASE_COMMIT: 1a4966a43be3ebcfc39b5622cdcb11f0203c0ae1
SOURCE_OBJECT_FAMILY_ID: PROPOSITION59_CCM_FINITE_SELECTED_FERRERS_FAMILY
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_SHA256: f0a32cbee5a7643ef2bbb0e2730dee96ef33437109a1c672c0713c22e7bb8c72
REQUEST_GIT_BLOB_COMPUTED: 7d8897d0f5e16fb903b9b77f98e0f4803d332f71
REQUEST_BYTES: 7194
REQUEST_LINES: 121
REQUEST_FINAL_LF: true
REQUEST_HASH_CHECK: MATCH
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
NEW_LITERAL_SOURCE_THEOREM: LOWEST_J_EIGENSPACE_ESCAPES_EVERY_FIXED_THETA_JET
NEW_SOURCE_RATE: O_r_LOG_M_TIMES_M_TO_MINUS_ONE_QUARTER
BULK_GROUND_UPPER_ENVELOPE: MINUS_2_LOG_2_OVER_E_TIMES_SQRT_M_OVER_LOG_M_EVENTUALLY
CLAIM_ABOUT_FULL_A_BOTTOM_ESCAPE: NOT_MADE
POSITIVE_COMPLEMENT_FORMULA: CONFIRMED_WITH_ENDPOINT_CLASSIFICATION
THETA_SUBSTITUTION: EXACTLY_RETURNS_FULL_LEAKAGE_IDENTITY_WITHOUT_NEW_RESPONSE_BOUND
POSITIVE_COMPLEMENT_GREEN_KERNEL: NOT_INHERITED_AND_INCOMPATIBLE_WITH_POSITIVE_REMOVED_MODE
STRICT_COMPETITOR_FOR_LITERAL_BOTTOM: NOT_PROVED
SOURCE_LOCALIZED_RESPONSE_BOUND: NOT_PROVED
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: LITERAL_BULK_ANCHOR_THEOREM_AND_SCOPED_GREEN_OBSTRUCTIONS_ONLY
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
VERIFIER: PAPER
EXACT_SYMBOLIC_CONTROLS: PASSED
LEAN_EXECUTED: false
ARB_INTERVAL_EXECUTED: false
LITERAL_CCM_NUMERICAL_SCAN: false
INDEPENDENT_REVIEW_OF_THIS_VERDICT: NOT_PERFORMED
AUTHORIZED_REMOTE_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GREEN_2026-10-30.md
REMOTE_DELIVERY: ACTUAL_COMMIT_REPORTED_SEPARATELY_AFTER_WRITE_AND_READBACK
RH_PROVED: false
T_PROVED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Decision

The positive-complement calculation in the request is correct on its stated open spectral branch. It does not yet supply a localized response bound. Substitution of the theta equation into that calculation returns the full leakage equation, with its inverse-weighted error intact. No source-dependent estimate defeating that error is established here.

There is, however, a new unconditional theorem on the **literal source**, not a synthetic matrix: every unit vector in the lowest eigenspace of the jump matrix J_m converges weakly to zero in physical even L2. More precisely, for each fixed theta jet,

\[
 \boxed{\sup_{e\in\ker(J_m-\mu_1),\ \|e\|=1}
       \|P_{\mathcal J_r}e\|=O_r((\log m)m^{-1/4}).}
\tag{0.1}
\]

This theorem concerns J_m, equivalently the pole-free bulk J_m-C_m I. **It is not a theorem that the bottoms of the full A_m escape.** No hypothesis about their behavior is used. It proves that the reference mode e1 in the new block decomposition is itself not a fixed compact anchor. A bound on |<e1,f_m>| alone cannot be promoted to theta retention. The signed complementary response must do the localization work.

The other decisive obstruction is one of order, not merely a missing numerical gap: removing a strictly positive ground mode makes a nonzero complement inverse incapable of preserving the pointwise positive cone. Thus even granting the desired Perron property does not make this reduced inverse the positive Green kernel in Gridnev-Garcia.

T and the RH goal are unchanged. The first missing source estimate is localization and local frequency control of the **normalized, coherently summed response**, not a new name for <leakage,f>=lambda<h,f>. A precise optional supplier is stated in §9. It is not asserted proved or necessary.

### Source and test lock

The attached request was read completely; its UTF-8 bytes, LF count, SHA-256 and computed Git blob are recorded above. All mathematical repository reads were at the given source commit. The three requested own-attempt notes were read completely [S2-S4]. The local CONFINE and BOUNDARY copies were checked against their pinned Git blob identifiers before using their detailed bounds [S5-S6].

Before exact replay and final analytic checking, four qualitative predictions were registered: the theta substitution would preserve the old leakage obstruction; the bulk anchor would escape with the rate (0.1); small S would not control the inverse-square response even for exact minima; and a positive removed mode would obstruct order-positivity of the complement Green operator. Their outcomes are recorded in §11. No new CCM numerical scan was run.

## 1. Literal source and the three different notions of positivity

### Lemma 1. The retained finite jump and pole decomposition

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

Let L=log m, I_m=[-L/2,L/2], N=m, and use the original orthonormal Fourier carrier and its real-even subspace V_m^E. All physical functions are zero-extended. Put

\[
 j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad c_n=\Lambda(n)n^{-1/2},\quad
 c_*=\gamma+\log(8\pi)+\pi/2,\quad C_m=c_*+2\sum_{2\le n\le m}c_n,
\]
\[
 J_m[f]=\int_0^\infty j(s)\|f-T_sf\|_2^2ds
       +\sum_{2\le n\le m}c_n\|f-T_{\log n}f\|_2^2,
 \qquad p(x)=\sqrt2\cosh(x/2),\quad u_m=P_m^E p.
\]

Here projection of p means projection of its restriction to I_m; p is not a global L2 vector. In coefficient coordinates, exactly,

\[
 \boxed{A_m=J_m+u_mu_m^T-C_m I.}
\tag{1.1}
\]

Moreover J_m is positive definite, since its infinite archimedean tail gives

\[
 J_m\succeq 2\left(\int_L^\infty j(s)ds\right)I>0.
\tag{1.2}
\]

**Proof.** Expand each translation square as 2||f||^2-Q_ff(s). This recovers the original constant, archimedean and prime terms, and adds the even pole |<p,f>|^2. The odd pole vanishes by actual evenness. For s>L the two supports are disjoint, giving (1.2). At n=m the jump square is 2||f||^2 and cancels its part of C_m exactly. The tail is retained, not removed. Finite trigonometric zero-extensions have translation-square increment O(s) near zero, so the j-integral is finite. Polarization gives the matrix statement. [S3-S5] ∎

In what follows, positivity as a quadratic form, positivity of a pointwise kernel, and positivity of the full Weil form are kept separate. Equation (1.2) proves only the first for J_m.

## 2. A new source comparison: the proposed reference ground mode escapes

### Lemma 2. An elementary prime-mass lower bound and a negative bulk envelope

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

For real x>=16,

\[
 \Psi(x):=\sum_{n\le x}\Lambda(n)\ge\tfrac12(\log2)x.
\tag{2.1}
\]

Consequently, with alpha_m=mu1(J_m)-C_m,

\[
 \boxed{\alpha_m\le-a_0\frac{\sqrt m}{L},\qquad
 a_0=\frac{2\log2}{e}>0,}
\tag{2.2}
\]

whenever m/e^2>=16 and c_*L>=10. These are explicit eventual conditions. No PNT, zero-free region or RH premise is used.

**Proof.** Let n=floor(x/2). In the prime factorization of binom(2n,n), each p^k contributes floor(2n/p^k)-2floor(n/p^k), which is zero or one. Hence

\[
 \Psi(x)\ge\log\binom{2n}{n}
 \ge2n\log2-\log(2n+1)
 \ge(x-2)\log2-\log(x+1).
\]

For x>=16 this is at least x log2/2: the difference is increasing, and at 16 equals log(64/17)>0. This proves (2.1), including all prime powers.

The normalized constant mode q=L^(-1/2)1_I is in the original even carrier. Its translation square is 2 min(s/L,1). Also

\[
 \int_0^\infty s j(s)ds
 =\sum_{k\ge0}(2k+1/2)^{-2}<5.
\]

Thus the **bulk**, not the full A, satisfies

\[
 \langle q,(J_m-C_m I)q\rangle
 \le-c_*+\frac{10}{L}
       -2\sum_{n\le m}c_n(1-\log n/L).
\tag{2.3}
\]

Keep only n<=x=m/e^2 in the last nonnegative sum. There 1-log n/L>=2/L and

\[
 \sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}
 \ge\frac{\Psi(x)}{\sqrt x}\ge\tfrac12(\log2)\sqrt x.
\]

Insertion into (2.3), followed by the variational upper bound for the bulk minimum, proves (2.2). The retained large primes can only make this particular bulk upper envelope more negative. No term of A is deleted in a claim about A. ∎

### Lemma 3. Every lowest J mode has vanishing fixed-theta overlap

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

Equation (0.1) holds uniformly over the whole lowest J eigenspace, with no simplicity assumption. In particular any choice of its unit vectors e_m satisfies e_m weakly convergent to zero in L2_even(R).

**Proof, including the inherited return budget.** Fix r=h^(2k). The pinned theta normalization is hat h(z)=4 xi(1/2-iz), with global radicality k(r,v)=0. Let chi be the fixed even smooth cutoff equal to one on [-1/2,1/2], supported in (-3/4,3/4). Write

\[
 z_m=\chi(2x/L)r,\quad s_m=P_mz_m,\quad e=s_m-z_m,\quad w=r-z_m.
\]

For p>=2, the fixed derivative bound M_{r,p}=sup_{L>=2}||z_m^(p)||_2 is finite. Set

\[
 \epsilon_0=M_{r,p}(L/(2\pi m))^p,\qquad
 \epsilon_1=M_{r,p}(L/(2\pi m))^{p-1},
\]
\[
 B_m=\frac{2M_{r,p}}{\sqrt L}(L/(2\pi))^p
                 \sqrt{\frac2{2p-1}}m^{1/2-p}.
\]

The complete established source bound, re-used with the same cutoff and carrier, is

\[
 \|A_ms_m\|\le\eta_{r,m}:=(2+4L)\sqrt m\epsilon_0
             +10\epsilon_1+10B_m\sqrt{3m/L}+\tau_{r,m},
\tag{2.4}
\]
\[
 \tau_{r,m}=c_*\|w\|+10\|w'\|
  +2m^{1/4}\int e^{|x|/2}|w(x)|dx
  +2\sqrt m\left(\sum_{n\ge2}\frac{\log n}{n^{3/2}}\right)
                                      \|e^{|x|}w\|_2.
\tag{2.5}
\]

For completeness, Parseval gives the two epsilon bounds. Cauchy-Schwarz on the entire omitted Fourier series gives the sum of endpoint traces at most B_m. Moving a derivative onto the zero extension of e gives the mixed arch bound 10(epsilon1+B_m sqrt(3m/L)); the endpoint delta masses are included. The pole and supported prime costs are respectively 2 sqrt(m) epsilon0 and 4 sqrt(m)L epsilon0. The exterior comparison has two shifted terms, each bounded using e^{|x|}w; summation yields the **infinite** series in (2.5). These are CONFINE (3.2)-(3.8), not a larger Fourier cutoff. All weighted norms of w decay faster than powers of m. Thus

\[
 \varepsilon_{r,m}:=\|s_m-r\|=O_{r,B}(m^{-B}),\qquad
 \eta_{r,m}=O_{r,B}(m^{-B})
\tag{2.6}
\]

for every fixed B and the same s_m. [S5]

Let e_m be any unit vector with (J_m-C_m I)e_m=alpha_m e_m. Since A_m=J_m-C_m I+u_mu_m^T,

\[
 |\alpha_m|\,|\langle e_m,s_m\rangle|
 \le\eta_{r,m}+\|u_m\|\,|\langle u_m,s_m\rangle|.
\tag{2.7}
\]

The physical pole norm is

\[
 P_m^{\rm pole}:=\|p\|_{L^2(I_m)}
   =\sqrt{L+2\sinh(L/2)}\le\sqrt2\,m^{1/4}.
\]

Integration by parts gives <p,r>=2 sqrt(2) 4^(-k). Therefore

\[
 |\langle u_m,s_m\rangle|
 \le 2\sqrt2\,4^{-k}+P_m^{\rm pole}\varepsilon_{r,m}
       +\int_{I_m^c}|p r|=:D_{r,m}.
\]

D_{r,m} is bounded independently of m. Equations (2.2) and (2.7) give the explicit comparison

\[
 \boxed{|\langle e_m,r\rangle|
 \le\varepsilon_{r,m}+\frac{L}{a_0\sqrt m}
                 (\eta_{r,m}+P_m^{\rm pole}D_{r,m}).}
\tag{2.8}
\]

This is O_r(L m^(-1/4)). For a fixed jet, its fixed nonsingular Gram matrix converts the finitely many bounds (2.8) into (0.1). Uniformity over e_m is evident from (2.7). Density of the fixed theta derivatives in the even L2 sector, proved in CONFINE §2, then gives weak convergence to zero. This density is used only in unweighted L2, not to extend radicality by continuity. ∎

**Exact scope.** The minimization used in Lemma 2 is the minimization of J, not the full source A. Lemma 3 proves neither weak escape nor retention of A-bottoms. Even a positive, simple J-ground cannot be identified with h. The source-specific estimate is (2.8), not the generic statement that reference modes may move.

### Lemma 4. The pole forcing itself is not a fixed compact source

**THIS STEP IS PROVED HERE. [COFINAL_FAMILY | PAPER]**

The unit physical vector u_m/||u_m|| has local L2 mass tending to zero on every fixed compact interval. This is stronger than weak escape for this particular vector.

**Proof.** The full signed Fourier coefficients of p on I_m are

\[
 p_n=\frac{4\sqrt2 L^{3/2}\sinh(L/4)}{L^2+16\pi^2n^2}.
\]

The original basis phase cancels the endpoint cosine; no alternating factor is omitted here. Parseval and sum_{n>m}n^(-4)<=1/(3m^3) yield

\[
 \|(I-P_m)p\|_{L^2(I_m)}^2
 \le\frac{L^3\sinh^2(L/4)}{12\pi^4m^3}
 \le\frac{L^3}{48\pi^4m^{5/2}}.
\tag{2.9}
\]

Since ||p||_I^2=L+2sinh(L/2) is asymptotic to sqrt(m), ||u_m|| is asymptotic to m^(1/4). On fixed [-R,R], ||1_{[-R,R]}u_m||<=||p||_{[-R,R]}+||(I-P_m)p||, whose ratio to ||u_m|| tends to zero. ∎

## 3. Positive-complement algebra and every endpoint

### Lemma 5. Open-branch response, shielding, and singular alternatives

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]**

Write B=J+uu^T, beta=lambda+C. Suppose first mu1 is simple and mu1<beta<mu2, with beta the bottom of B. Choose a real unit e1, put Q=I-e1e1^T, u=b e1+u+, and

\[
 D=J_+-\beta I>0,\quad R=D^{-1},\quad
 S=u_+^TRu_+,
 \quad T_{\rm resp}=\|Ru_+\|^2,
\]
\[
 W=(D+u_+u_+^T)^{-1}
   =R-\frac{Ru_+u_+^TR}{1+S},\quad w=Wu_+=\frac{Ru_+}{1+S}.
\tag{3.1}
\]

Then b and a=<e1,f> are nonzero, and a unit bottom is

\[
 f=a(e_1-bw),\quad
 \beta-\mu_1=\frac{b^2}{1+S},\quad
 a^2=\frac1{1+b^2T_{\rm resp}/(1+S)^2}.
\tag{3.2}
\]

The request's bound follows from T_resp<=S/(mu2-beta). The scalar S does not upper-bound T_resp without further information. Also W<=R in quadratic-form order does **not** imply W^2<=R^2 or a directional norm inequality ||Wx||<=||Rx||. For example, R=diag(2,1), u+=(1,1) gives W=[[1,-1/2],[-1/2,3/4]] and det(R^2-W^2)=-1/4, although R-W is positive semidefinite.

**Proof.** The Q block of (B-beta)f=0 is Dv+u+(ab+u+^Tv)=0. Solving for t=ab+u+^Tv gives t=ab/(1+S), then v=-abw. The e1 equation and normalization give (3.2). If b=0, e1 survives at mu1, contrary to beta>mu1. If a=0, the positive Q block forbids a nonzero f. Formula (3.1) follows by multiplication. The spectral expansion of R gives T_resp<=S/(mu2-beta). Squaring does not preserve the Loewner order for noncommuting positive matrices, so the unproved directional inequality is not used. ∎

Here is the complete eigenvector classification at a singular value theta in spec(J). Let E_theta be its spectral projector and u_theta=E_theta u. The equation is (J-theta)f=-u t, t=u^Tf.

* If u_theta!=0, then t=0 and the eigenspace of B at theta is E_theta H intersect u_theta-perp.
* If u_theta=0, put K_theta=(J-theta I)^dagger and sigma_theta=1+u^TK_theta u. If sigma_theta!=0, the eigenspace is E_theta H. If sigma_theta=0, it is E_theta H plus span{K_theta u}.

These statements follow by projecting the equation onto E_theta and its complement and substituting t; they also cover ties. At the lower endpoint beta=mu1, directly

\[
 \ker(B-\mu_1 I)=\ker(J-\mu_1 I)\cap u^\perp.
\tag{3.3}
\]

In particular a multiple lowest J level always leaves an untouched bottom direction. Such cases cannot be analyzed by an inverse with an artificially deleted zero denominator. At beta=mu2 the general classification applies. No claim that an open branch occurs cofinally for the literal family is made.

## 4. Why the Green positivity import fails even after the complement is positive

### Lemma 6. Removing a positive mode obstructs order-positivity

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]**

Let e>0 almost everywhere in an L2 space and let K be a bounded positivity-preserving operator with Ke=0. Then K=0. Hence a nonzero reduced inverse, extended by zero on a strictly positive removed ground mode, cannot be positivity-preserving, even if it is a positive self-adjoint operator.

**Proof.** For g>=0, set g_n=min(g,n e). Then 0<=Kg_n<=nKe=0, and g_n->g in L2. Boundedness gives Kg=0. Differences of nonnegative functions give K=0 on the whole space. ∎

Thus, even in the favorable continuum setting in which the jump ground state is strictly positive, Q(J-beta)^(-1)Q on the positive complement is not the Green kernel of a positive potential. This is a conditional obstruction with a stronger premise than is currently proved for the finite J ground; it does not presume that finite Fourier compression preserves positivity.

The elementary matrix Q=[[1/2,-1/2],[-1/2,1/2]] is already positive semidefinite, kills (1,1), and has a negative off-diagonal entry. The source comparison cannot replace operator positivity by a pointwise absolute-value domination without paying the lost cancellation.

Gridnev-Garcia uses a full positive Green kernel fed by attraction supported in a fixed ball, and local compactness in addition to its envelope. Its inverse-square threshold is for the three-dimensional Laplacian. The present complement has neither that order structure nor a fixed compact pole source; Lemmas 3-4 make the latter distinction quantitative. The source's Appendix A and support typo were checked in the parsed primary text. [P1] Bellazzini et al. instead pay localization with an exterior repulsive term; that term has not been supplied for A_m. [P2]

### Lemma 7. Small S fails even on an exact minimum

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER; NONLITERAL CONTROL]**

For t>0 let

\[
 J=\operatorname{diag}(1,2+t^4),\quad
 u=(\sqrt{1+t^2},t^3)^T,\quad \beta=2.
\]

Then B=J+uu^T has a simple bottom beta in the strict open branch, because

\[
 B-2I=\begin{pmatrix}
 t^2&t^3\sqrt{1+t^2}\\
 t^3\sqrt{1+t^2}&t^4(1+t^2)
 \end{pmatrix}\succeq0
\]

has zero determinant and positive trace. But

\[
 S=t^2\to0,\quad T_{\rm resp}=t^{-2}\to\infty,\quad
 a^2=\frac{t^2(1+t^2)}{1+t^2+t^4}\to0.
\tag{4.1}
\]

Everything follows by direct substitution. Taking A=B-3I makes its exact bottom negative, -1, while all the positive-complement algebra remains valid. No positivity detector in this verdict certifies A from those facts. This is not a prime deformation or a literal CCM counterexample. It disproves only the proposed generic inference from small S and exact bottomness to a controlled inverse-square response. ∎

## 5. Theta substitution: the full response still contains the full leakage

### Lemma 8. Exact cancellation audit, not a new overlap estimate

**THIS STEP IS PROVED HERE. [FINITE_CELL | PAPER]**

Use the actual s=P_m h, unnormalized, and define e=A_m s. On the open branch write s=s1 e1+s+, e=e1err e1+e+, and d=u^Ts. For sufficiently large m, d tends to <p,h>=2sqrt(2), so d is nonzero. Then

\[
 (\mu_1-C_m)s_1+b d=e_{1\rm err},\qquad
 (J_+-C_m)s_++u_+d=e_+,
\]
\[
 \boxed{dRu_+=-s_++R(e_+-\lambda s_+),}
\tag{5.1}
\]
\[
 \boxed{s_++b s_1Wu_+=W(e_+-\lambda s_+).}
\tag{5.2}
\]

For the exact bottom f=a(e1-bWu+), (5.2) is

\[
 s-(s_1/a)f=W(e_+-\lambda s_+)\quad\text{in }QH.
\tag{5.3}
\]

**Proof.** Expand A s=e in its two J blocks, and use J_+-C=D+lambda I. Equation (5.1) follows by applying R. Adding u+u+^T s+ and using d=b s1+u+^T s+ gives (5.2). Equation (5.3) follows from (3.2). The statement d->2sqrt(2) follows from the fixed-theta return in Lemma 3; replacing its cutoff by P_mh changes it superpolynomially, since the removed theta tail has every exponential decay bound. The norm of the pole grows only like m^(1/4). ∎

In particular the proposed inverse-square bound becomes exactly

\[
 d^2T_{\rm resp}=\|-s_++R(e_+-\lambda s_+)\|^2.
\tag{5.4}
\]

The signed cross term in this square is essential. Pairing A s=e with f gives precisely <e,f>=lambda<s,f>, the already known identity. Equations (5.1)-(5.4) have **not** made e small after R or W, nor identified the sign of the cross term. They are the requested explicit demonstration of collapse back to the leakage obstruction.

### Full leakage ledger for this substitution

Let H(t)=4xi(1/2-it), omega_n=2pi n/L, h_out=h 1_{I_m^c}. For any real even carrier vector v,

\[
 c_n^{h,I}=\frac{(-1)^n}{\sqrt L}
       [H(\omega_n)-\widehat h_{\rm out}(\omega_n)],
\]
\[
 F_m(v)=\sum_{|n|>m}\frac{(-1)^n}{\sqrt L}H(\omega_n)\,k(\psi_n,v),
\]
\[
 X_m(v)=k(h_{\rm out},v)
       -\sum_{|n|>m}\frac{(-1)^n}{\sqrt L}
                      \widehat h_{\rm out}(\omega_n)\,k(\psi_n,v).
\]

Thus, since s is unnormalized,

\[
 \boxed{\langle v,e\rangle=-F_m(v)-X_m(v).}
\tag{5.5}
\]

This is the full NOESCAPE leakage formula, applicable to J eigenvectors as to any carrier vector. The high-mode entries use the same L and all supported prime powers. The h_out pairing includes every exterior prime power as well. Window endpoint derivatives and the phase (-1)^n are retained. Neither X=0 nor a separately positive F or X is used. [S7]

For an absolute norm budget one may use the cutoff construction in (2.4)-(2.5), then add M_m||h-chi(2x/L)h||, where a sufficient literal matrix bound is

\[
 M_m=c_*+8+\tfrac34(2\pi m/L)^2+
               3(2m+1)/L+(2+4L)\sqrt m.
\tag{5.6}
\]

This follows from translation differences, both endpoint strips, supported primes and pole norms, as in the pinned BOUNDARY estimate. It makes e superpolynomially small in ordinary norm. The corresponding paid inverse estimate is only ||Re+||<=||e||/(mu2-beta), or the exact directional quantity in (5.4). No comparison of that cost with a cofinal signed margin follows. An absolute exterior bound is not an inverse-weighted bound.

## 6. Residual, localization and normalization costs

### Lemma 9. The exact response error for a trial is filtered, not its bare residual

**THIS STEP IS PROVED HERE. [ABSTRACT | PAPER]**

For a unit q=a e1+v, choose any rho with mu1<rho<mu2, and let r=(B-rho I)q. Recompute R,S,W at rho. Then

\[
 v=-abWu_++Wr_+,\qquad
 a\left(\mu_1-\rho+\frac{b^2}{1+S}\right)
   =r_1-bu_+^TWr_+.
\tag{6.1}
\]

In particular, if y=a(e1-bWu+) and delta=||Wr+||<1, then

\[
 \|y\|\ge1-\delta,\qquad
 \left\|q-\frac y{\|y\|}\right\|\le2\delta.
\tag{6.2}
\]

If rho=q^TBq, then with dvec=Wr+ embedded in QH,

\[
 \frac{y^TBy}{\|y\|^2}-\rho
 =\frac{-2\langle dvec,r\rangle+
                \langle dvec,(B-\rho I)dvec\rangle}{\|q-dvec\|^2},
\]
\[
 \left|\frac{y^TBy}{\|y\|^2}-\rho\right|
 \le\frac{2\delta\|r\|+\|B-\rho I\|\delta^2}{(1-\delta)^2}.
\tag{6.3}
\]

**Proof.** Solve the Q block including r+, using W, and substitute into the first block. Then q-y=Wr+. The triangle inequality proves (6.2). Expand the shifted quadratic form at q-dvec, using (B-rho)q=r and q^Tr=0. ∎

Here the exact filtered error is

\[
 Wr_+=Rr_+-Ru_+\frac{u_+^TRr_+}{1+S}.
\tag{6.4}
\]

Both terms must stay together. If only ||r|| is available, the safe bound is delta<=||r||/(mu2-rho); the rank-one formula alone does not improve it. If a claimed strict gain is eta_m, the full right side of (6.3), plus any input/source errors, must be smaller than eta_m. No such comparison is claimed for the observed cells or an escaping family.

For an even physical localization chi, z=chi f need not lie in V_m. Put e_loc=(I-P_m)z, d_loc=||e_loc||^2. If ||z||^2>d_loc, the admissible normalized return has exact excess

\[
 \frac{k[P_mz]}{\|P_mz\|^2}-\lambda
 =\frac{k[z]-\lambda\|z\|^2-2\Re k(z,e_{\rm loc})
                    +k[e_{\rm loc}]+\lambda d_{\rm loc}}
              {\|z\|^2-d_{\rm loc}}.
\tag{6.5}
\]

This is an error ledger, not a supplied gain. Every k here is the full source form. If instead an ambient Green equation is used, projected stationarity leaves (I-P_m)H_L f as an additional forcing (or its form-dual version); it is not zero. If an ambient lower energy E is used, the excess lambda_m-E also remains. Thus none of the carrier-return or centering costs in [S2-S4] is silently removed by this calculation.

## 7. What the joint positive-complement response must actually accomplish

Define on the open branch

\[
 D_m^{\rm norm}=\sqrt{(1+S)^2+b^2T_{\rm resp}},\qquad
 z_m=\frac{b}{D_m^{\rm norm}}Ru_+.
\tag{7.1}
\]

Choose the phase a>0. Then exactly

\[
 f_m=\frac{1+S}{D_m^{\rm norm}}e_{1,m}-z_m,
 \qquad \|z_m\|\le1.
\tag{7.2}
\]

By Lemma 3, for every fixed jet,

\[
 \|P_{\mathcal J_r}(f_m+z_m)\|
       =O_r(Lm^{-1/4}).
\tag{7.3}
\]

Equation (7.3) locates the potentially retained component but is **not a new supplier for T**. Bounding a away from zero is not enough: e1 itself escapes. Conversely, T does not require a->0. Only under the stronger hypothesis that f_m has a strong nonzero subsequential limit does e1 weakly zero force a=<e1,f_m>->0.

The scalar spectral measure supplies another precise version of the failed bound. With d sigma=sum_{j>=2}|<e_j,u>|^2 delta_{mu_j},

\[
 S=\int\frac{d\sigma(x)}{x-\beta},\qquad
 T_{\rm resp}=\int\frac{d\sigma(x)}{(x-\beta)^2}.
\tag{7.4}
\]

Equivalently these are the zeroth and first time moments of the nonnegative scalar function

\[
 e^{\beta t}\bigl(\langle u,e^{-tJ}u\rangle-b^2e^{-\mu_1t}\bigr).
\tag{7.5}
\]

Tonelli proves the formulas on the strict branch. Positivity in (7.5) is spectral, not positivity of its physical kernel. A bound on its time integral does not bound its first time moment; Lemma 7 is an exact failure. Localization of (7.1) further requires the cross terms between different spectral components, not only these scalar integrals.

The DIAGONAL moment disk is a positive source-measure estimate. The weights in (7.4) are spectral projections of the actual pole under the full jump operator. No identity or inequality identifying the two measures has been established. Replacing one by the other would remove the substantive arithmetic/spectral step.

## 8. The known escaping source trials and the exact-bottom distinction

### Lemma 10. The proposed universal envelope still fails on literal trials

**THIS STEP IS PROVED HERE USING THE PINNED SOURCE CONSTRUCTION. [COFINAL_FAMILY | PAPER]**

There is no single L2 majorant for all unit original even trials with superpolynomial residual. The same remains true when any prescribed fixed finite set of linear source observations is forced to vanish.

**Proof.** Use the accepted BOUNDARY packets centered at +/-L/8, with their original-N=m return. Their distance from the corresponding normalized translates of h tends to zero, their norm is one, and their A-residual and fixed-jet overlaps decay faster than powers of m. For every fixed R, their mass on [-R,R] tends to zero. A common majorant G in L2 would give uniformly small mass outside [-R,R] for large R, a contradiction. The fixed-functional version uses finitely many separated packets with uniformly conditioned Gram matrix, as in BOUNDARY Lemma 6; a unit combination still has local mass tending to zero. [S6] ∎

These are not exact bottoms. In the complement reconstruction their precise exception is the term Wr+ in (6.1), and at singular endpoints the compatibility terms of Lemma 5. Superpolynomial ||r|| alone does not bound that filtered error. Exact bottomness enters at rank-one min-max and at r=0; it is not being replaced by near stationarity. Nevertheless r=0 does not itself supply a physical order kernel, fixed compact forcing, or the localization estimate below.

The abstract control of Lemma 7 is stronger than a stationary-vector control: it already has exact minimality. Together these two controls separate the roles of literal arithmetic, exactness, and inverse weighting without declaring all other mechanisms impossible.

## 9. A concrete additional supplier, and the precise present failure

### Lemma 11. Local response mass plus logarithmic regularity would suffice

**THIS STEP IS PROVED HERE AS A CONDITIONAL IMPLICATION. [COFINAL_FAMILY | CONDITIONAL]**

Suppose an unbounded set of original cells is proved to be on the strict branch. If a fixed real even chi in C_c^infinity, 0<=chi<=1, and constants eta>0, M<infinity satisfy

\[
 \boxed{\|\chi z_m\|_2^2\ge\eta,\qquad
 \frac1{2\pi}\int\log(2+|t|)
              |\widehat{\chi z_m}(t)|^2dt\le M,}
\tag{9.1}
\]

for the **actual signed response (7.1)** on that set, then T holds and hence RH follows by the accepted NOESCAPE implication.

**Proof.** The functions chi z_m have common compact support and bounded L2 norms. Their Fourier mass outside [-R,R] is at most M/log(2+R). Splitting the Fourier integral shows uniform translation continuity: for a shift a, the squared increment is at most a^2 R^2+4M/log(2+R). Compact support and these two bounds give L2 precompactness (or prove it directly by finite-frequency approximation on a fixed bounded interval). A subsequence converges strongly to w with ||w||^2>=eta. Along a further weakly convergent subsequence z_m tends weakly to z, with chi z=w, so z is nonzero. Lemma 3 and (7.2) imply f_m tends weakly to -z on that subsequence. Fixed-jet density then gives one finite jet with a persistent nonzero projection. ∎

Localizing the observable chi z_m in this proof is not a change of the eigenproblem or an energy competitor, so it requires no Fourier return. An attempted proof via an energy variation would require (6.5). For approximate response data, ||chi Wr+|| must be paid for the mass estimate, and the logarithmic Fourier norm of chi Wr+ must be paid separately for the regularity estimate; an L2 residual bound alone does not pay the latter.

**THIS SUPPLIER IMPLIES RH; its converse is not asserted.** It is not an algebraic restatement of the old inverse-eigenvalue overlap condition. It demands physical local regularity as well as mass; no equivalence to T on the literal family is known. On general Hilbert-space sequences this is a strictly stronger mechanism. For example, a sequence (r+v_n)/sqrt(2), with fixed unit r and normalized increasingly oscillatory even v_n orthogonal to r on the same physical region, retains r but can have unbounded localized logarithmic Fourier energy. Thus retention alone does not furnish this regularity mechanism; this example does not establish a strict separation on actual CCM bottoms. No full global tightness or full limiting ladder is made mandatory.

### The worked estimate that stops

The paid source energy yields only

\[
 J_m[f_m]=C_m+\lambda_m-|\langle u_m,f_m\rangle|^2
 \le C_m+o(1),
\tag{9.2}
\]

using the fixed-theta Rayleigh upper bound lambda_m<=o(1). The bound grows with m. From the positive complement alone one similarly obtains

\[
 \langle Ru_+,J_+Ru_+\rangle=\beta T_{\rm resp}+S.
\tag{9.3}
\]

Neither is a parameter-independent local regularity bound; neither gives local mass. The first attempted additional estimates are precisely the two independently source-derived bounds in (9.1), with the coherent sum preserved. They are **not established** here. No positivity of jumps, source moment disk, or small ordinary theta leakage has been shown to imply them.

A weaker compactness mechanism or a strict competitor may avoid (9.1). It is an optional concrete next supplier, not a mandatory reformulation of T. At endpoints one must use Lemma 5 and prove a corresponding retained component; the open-branch hypothesis may not be inferred from finite tables.

The actual plan-changing result of this batch is the source theorem (2.8): the mode proposed as the positive-complement anchor is unconditionally escaping. The actual Green obstruction is Lemma 6. The requested cofinal signed response estimate remains missing, rather than being renamed as a theorem.

## 10. Route map and strongest attack

**Established obstructions: [ABSTRACT | PAPER]. Proposed cofinal suppliers: [COFINAL_FAMILY | CONDITIONAL].**

| Representation | What is established | Decisive next input | Kill-power / cost estimate |
|---|---|---|---|
| Full positive-Green domination | Direct transfer fails: noncontractive global forcing, noncompact pole, and no inherited pointwise kernel | A new source decomposition with a valid order comparison and its projection defects | 8/10, 9/10 |
| Reduced signed response (primary) | Exact branch algebra, endpoints, source anchor escape, and complete filtered residual | Actual source bounds such as (9.1), not scalar S or full inverse norm | 9/10, 8/10 |
| Spectral-shell response | S/T are different weighted moments; (7.4)-(7.5) are exact | Source bounds on the spectral masses and their physical cross-correlations | 7/10, 7/10 |

These are estimates of research cost and discriminatory value, not success probabilities. No escalated numerical campaign is authorized.

The strongest attack is that (7.3) and (9.1) could be mistaken for a solution by restating retention. They are explicitly not counted as new source bounds. The new unconditional statement is (0.1), proved using actual prime mass, pole normalization and the full theta return. It narrows the Green mechanism but does not supply the missing retained response.

Dependency contract: DOWNSTREAM_CONSUMER is the fixed-jet T-to-RH implication. ACTUAL_CONSUMER_REQUIREMENT is one nonzero fixed finite theta component on an unbounded original family. ORIGINAL_REQUESTED_OBJECT is a source-weighted positive-complement response/localization estimate. ORIGINAL_OBJECT_IS is UNKNOWN as a necessary interface; other competitors remain allowed. A weaker sufficient interface is any nonzero weak subsequential limit of exact bottoms. FAILURE_TYPE for the unfinished response proof is NO_DERIVATION, EPISTEMIC_STATUS is RESEARCH_DEBT, and NOVELTY_AXIS is the separation of an escaping bulk anchor from a potentially retained signed response. Reopen upon an independently bounded source response, a valid alternative localization/barrier, or a strict same-carrier competitor. No route-family death is claimed.

The generic S-controls-T inference is refuted by the exact family (4.1), scope THEOREM_SHAPE only. The order-positive complement import is refuted under its positive-mode hypothesis by Lemma 6. Neither refutation says that the literal CCM family violates T or RH.

## 11. Prediction closeout and one next directive

P1 confirmed: the theta substitution returns the existing full leakage equation without a new inverse estimate.
P2 confirmed on paper: the lowest J eigenspace has the explicit source escape bound (0.1).
P3 confirmed by exact symbolic control: S can tend to zero while T_resp diverges for a simple exact minimum.
P4 confirmed at its stated scope: a nonzero complement inverse killing a strictly positive mode cannot preserve the positive cone. Positivity of the finite physical J ground is not assumed.

What became smaller: a proposed anchor has been ruled out as a fixed anchor on the literal source; response localization cannot be replaced by its coefficient a. What was not obtained: a strict competitor, the source estimate (9.1), T, or RH. Do not retry positivity of the reduced inverse or small S as substitutes for those bounds. The discriminator is a source-controlled local mass and local frequency budget for (7.1), with endpoint and filtered-error guards.

**CODEX DIRECTIVE — one bounded source task, no Lean or route-state changes:** seek an actual source proof or source counterexample for the coupled localized reduced-response estimate (9.1), retaining the exact vectors and normalization (7.1). First verify an unbounded admissible branch, or report its unproved endpoint alternative using Lemma 5. Work with the full prime/cosine source and theta leakage (5.5); do not import an order-positive complement kernel or use <e,f>=lambda<s,f> as the bound. Any approximation must include (6.1)-(6.5) at the claimed margin. Success means independent physical mass and logarithmic-frequency bounds from the coefficients, not an observed finite overlap. Failure must identify which of these bounds is unpaid and exhibit the relevant escaping-trial or endpoint control. The new bulk-anchor proof should be checked before spending it as an accepted supplier.

Memory: GREEN proves that the J ground anchor escapes unconditionally; the full A bottom may still be retained by its signed complementary response. Small S, positive quadratic inverse and ordinary theta residual do not prove that response localized.

## 12. Proshka's own line

The useful distinction is between the ground of the jump bulk and the ground of the full source.
The request already separated them algebraically; the new estimate separates them asymptotically.
The first vector cannot serve as a fixed anchor because its theta pairings vanish.
That conclusion uses actual prime mass, not a deformed-source plant.
The full bottom is not covered by that escape theorem.
Its localization can still be created by the signed complementary response.
This is why a scalar mixing coefficient is the wrong observable here.
A positive operator on a complement is also not a positive physical Green kernel.
Removing the positive mode destroys precisely that order property.
The nearest alternative is a localized response estimate with its cancellations intact.
The other alternative is a same-carrier competitor whose signed gain is independently bounded.
Neither has been proved in this batch.
The first next move is to control the physical response near a fixed central region.
A response bound that silently divides by the closing gap would fail its own budget.
The second next move would be a source estimate for local frequency compactness.
A spatial envelope without that step still allows weak-zero oscillation.
The data most useful for a bounded diagnostic would separate these two defects.
It should record signed response localization, not only S, T and a.
Such a diagnostic would choose a lemma, not prove a cofinal statement.
I distrust every proposed positivity transfer that drops the removed ground projection.
I also distrust splitting the theta leakage before applying the inverse.
The exact endpoint modes remain part of the problem.
The RH implication is the purpose of the work, not a reason to stop it.
No part of this report turns a failed sufficient estimate into the negation of RH.

## 13. Research log and provenance

All repository sources below are at 1a4966a43be3ebcfc39b5622cdcb11f0203c0ae1 unless noted otherwise.

- [S1] READ: attached PROSHKA_REQUEST_GREEN_2026-10-30.txt, all bytes and lines; request hash verified as above. The inline post-pin complement calculation was checked mathematically, not assumed remotely committed.
- [S2] READ: docs/routeB_bus/proshka/NOESCAPE_GRIDNEV_GARCIA_BRIDGE_2026-10-30.md, blob afa224ab988bb21bd819aaa01a9beb1bac409f6b; complete transfer audit and fixed-source distinction.
- [S3] READ: docs/routeB_bus/proshka/NOESCAPE_JUMP_RANK_ONE_ATTEMPT_2026-10-30.md, blob 9cee1a342d3a16909dbedfb621de5e860272d9c8; source decomposition and rank-one min-max. Its numerical rows are diagnostics only.
- [S4] READ: docs/routeB_bus/proshka/NOESCAPE_THRESHOLD_ALIAS_HUNT_2026-10-30.md, blob de2ab9f115e9ef5c6c26f2c9de6df00cd2b470d9; centering, localization and local compactness guards. Other papers named there but not separately read this batch remain RELAY and are not premises.
- [S5] READ: docs/routeB_bus/proshka/PROSHKA_VERDICT_CONFINE_2026-10-30.md, §§1-3, blob 1879347b72d1aa55cf506f5387de37059f929122; theta normalization, fixed-jet density, full return estimate. Mounted copy Git blob matched the pinned response.
- [S6] READ: docs/routeB_bus/proshka/PROSHKA_VERDICT_BOUNDARY_2026-10-30.md, §§3-4, blob 60909fcc71d86778404290704cd641223e210467; literal escaping packets and M_m. Mounted copy Git blob matched the pinned response.
- [S7] READ: docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md, §4, equations (4.7)-(4.11), blob 453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc; mounted copy matches the pinned blob. Used only with its stated source hypotheses and no new finite F/X certificate.
- [S8] READ: docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py, matrix_K, lines 1-38, blob 5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3; entry signs, diagonal and prime endpoints. Not executed numerically.
- [P1] READ: Gridnev-Garcia, arXiv:math-ph/0610038v2, 6 November 2006, Theorems 2-3, equations (4)-(6), (45)-(47), Appendix A; primary parsed PDF at `https://arxiv.org/pdf/math-ph/0610038`. Used to audit the proposed mechanism, not to import a CCM theorem. Web screenshots were attempted but returned cache-miss errors; binary download failed DNS. No primary PDF byte-hash or visual check is claimed. The shelf PDF hash remains the observer's verified provenance, not a fresh hash check here.
- [P2] READ: Bellazzini-Frank-Lieb-Seiringer, arXiv:1301.5370v1, §2, Theorem 2.1 and Lemmas 2.1-2.2; parsed primary PDF at `https://arxiv.org/pdf/1301.5370`. Only the exterior-barrier/local-compactness distinction was used. Screenshot retrieval failed; no CCM transfer was inferred.
- Protocol READ from rh_clean this batch; blob e0127d491799f7764e4f50e1ae4ed4cfcaf73c13.

Branches rejected at their exact scope: full positive inverse at beta fails interlacing; shifted positive inverse has absorption coefficient at least one; complement positivity does not give kernel positivity; small S cannot control its next inverse moment; theta substitution without a new bound is the old leakage equation; trial envelopes fail on actual translated radical packets. None excludes another source-sensitive competitor.

Reusable new statements are the elementary envelope (2.2), the fixed-jet bulk-ground bound (2.8), the pole projection-tail bound (2.9), and the exact filtered residual/normalization formulas (6.1)-(6.5). They remain useful independently of whether the proposed localized-response route closes.

## Appendix A. Exact replay

The following code was executed successfully with SymPy. It checks algebra and planted controls only, not the analytic estimates or the literal source spectrum.

```python
import sympy as s
from math import comb, lcm

t = s.symbols('t', positive=True)
u = s.Matrix([s.sqrt(1+t**2), t**3])
J = s.diag(1, 2+t**4)
H = J+u*u.T
B = H-2*s.eye(2)
assert s.simplify(B.det()) == 0
assert s.simplify(s.trace(B)-(t**2+t**4+t**6)) == 0
S = s.simplify(u[1]**2/t**4)
T = s.simplify(u[1]**2/t**8)
assert S == t**2 and T == t**-2
alpha2 = s.factor(1/(1+(1+t**2)*T/(1+S)**2))
assert s.limit(alpha2, t, 0, dir='+') == 0

J = s.diag(2, 5, 11)
u = s.Matrix([1, 2, -1]); H = J+u*u.T
rho = s.Integer(3); q = s.Matrix([1, 2, 2])/3
r = (H-rho*s.eye(3))*q
up = u[1:3, 0:1]
R = s.diag(s.Rational(1, 2), s.Rational(1, 8))
S = (up.T*R*up)[0]
W = R-R*up*up.T*R/(1+S)
assert s.simplify(W-(J[1:3, 1:3]-rho*s.eye(2)+up*up.T).inv()) == s.zeros(2)
a = q[0]; b = u[0]
assert s.simplify(-a*b*W*up+W*r[1:3, 0:1]-q[1:3, 0:1]) == s.zeros(2, 1)
sigma = J[0, 0]-rho+b**2/(1+S)
assert s.simplify(a*sigma-r[0]+b*(up.T*W*r[1:3, 0:1])[0]) == 0
C = s.Integer(4); lam = rho-C
z = s.Matrix([2, 1, -1]); e = (H-C*s.eye(3))*z
assert s.simplify(z[1:3, 0:1]+b*z[0]*W*up-W*(e[1:3, 0:1]-lam*z[1:3, 0:1])) == s.zeros(2, 1)
d = (u.T*z)[0]
assert s.simplify(d*R*up+z[1:3, 0:1]-R*(e[1:3, 0:1]-lam*z[1:3, 0:1])) == s.zeros(2, 1)

J0 = s.diag(1, 1, 4); u0 = s.Matrix([1, 0, 1])
assert (J0+u0*u0.T-s.eye(3))*s.Matrix([0, 1, 0]) == s.zeros(3, 1)
assert s.diag(1, 2)+s.Matrix([1, 0])*s.Matrix([[1, 0]]) == 2*s.eye(2)
Q = s.Matrix([[s.Rational(1,2), -s.Rational(1,2)],
              [-s.Rational(1,2), s.Rational(1,2)]])
assert Q*s.ones(2,1) == s.zeros(2,1)
assert Q.det() == 0 and s.trace(Q) == 1 and Q[0,1] < 0
RR = s.diag(2, 1); uu = s.Matrix([1, 1])
WW = RR-RR*uu*uu.T*RR/4
assert (RR**2-WW**2).det() == -s.Rational(1, 4)
for n in range(1, 101):
    v = 1
    for k in range(1, 2*n+1):
        v = lcm(v, k)
    assert v % comb(2*n, n) == 0
print('ALL_EXACT_CHECKS_PASSED')
```

The finite binomial control checks the implementation orientation; the all-x proof is Lemma 2, not those one hundred cases. The new analytic theorem remains PAPER and has not received an independent review or a Lean/Arb check.

## Final boundary

Only the new verdict path is authorized for remote creation. The actual write result and subsequent readback are reported with the delivery, not anticipated in this file. No Lean source, route state, settings, other verdict, or numerical data file is changed. The supplied request's hashes are not substituted for an executed remote write.

**No strict competitor for a literal escaping A-bottom has been obtained. The new proof concerns the escaping J reference eigenspace. RH, T, cofinal G1a and G3 remain open.**
