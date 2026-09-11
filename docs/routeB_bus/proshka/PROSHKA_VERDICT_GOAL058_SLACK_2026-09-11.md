# Ы — SLACK: an exact arithmetic kernel and its theta-kernel transfer

```yaml
REQUEST_ID: REQ-2026-09-11-SLACK
BOUNDARY_ID: GOAL058_INTEGRATED_SIGNED_SOURCE_SLACK_CANCELLATION
OPERATIVE_CLASS: TRY_SLACK_THETA_KERNEL_SIGNED_COMPARISON
PRIMARY_COUNT: 1
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
Q1_COMPLETE_SCOPE: exact_source_identities_and_equality_preserving_transfer_only
VERIFIER: PAPER
DERIVATIVE_EQUALITY_PRESERVED: true
NEW_INTEGRATED_SOURCE_IDENTITY_PROVED: true
NEW_IDENTITY_LOCATORS: [SL8, SL10, SL11, SL12, SL14]
FULL_SIGNED_REMAINDER_PAID: false
LOWER_SIGN_PROVED: false
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
FIRST_FAILURE:
  Q1_INITIAL: a_nonzero_L2_continuous_square_supplier_is_impossible_by_SL3
  Q1_REPAIRED: none_at_the_declared_identity_scope
  Q2: positivity_of_the_full_theta_kernel_in_SL20_is_not_proved
  Q3: the_transfer_is_proved_but_its_SL20_sign_premise_is_unpaid
INDEPENDENT_REVIEW: NOT_PERFORMED_THIS_BATCH
LEAN_VERIFIED: false
REQUEST_LOCK:
  COMMIT: d92fd17e78b28fe93939e6b94becf1b90c68dddc
  BLOB: 1bb6a64ca93430b52142071150fa2e6e36ce4520
  SHA256: 7cbb8da692f7603b66995dfafbc2ec483e05927f9331903db9b540e6d49638da
  BYTES: 15912
  LINES: 81
  FINAL_LF: true
  LOCAL_BYTES_AND_BOTH_HASHES_RECOMPUTED: true
SOURCE_BASE: 3fcf7759342ea41ef9a46de2597f0a6187f1931d
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md
PUBLICATION_RECEIPT: EXTERNAL_TO_THIS_FILE
```

## 0. Decision, source lock and meaning of the result

**The new result is an exact, equality-preserving integrated representation, not an all-test sign proof.** The original form is transferred to an explicit arithmetic kernel. A finite, invertible diagonal congruence and a double Fourier transform then transfer its sign to a smooth kernel constructed solely from the full canonical theta source. No inverse of the Fourier transform of the source is assumed bounded. The first unpaid inequality is the positivity of that last kernel on all complex compact smooth tests, displayed in SL20.

Three attempted sign mechanisms receive exact obstructions: an L2-continuous positive-square supplier, every fixed truncation of the prime sum on the unrestricted test class, and every fixed Gaussian rank-one lower comparison for the actual theta kernel. A separate explicit noncanonical control disproves the inference from entrywise positivity to kernel positivity. These are scoped failures, not negative values of the original full Q.

**PAPER** means the proofs printed here, not an independent review or a Lean admission. No originality claim relative to the entire literature is made.

The controlling request was read completely. Its UTF-8 text was captured locally and both hashes and all counts in REQUEST_LOCK were recomputed and matched. The following shelf objects were fetched at SOURCE_BASE. Their returned Git blob identifiers match the pinned identifiers. The complete shelf SHA-256 values below remain the request's authenticated values; this execution did not independently recapture and rehash all four complete shelf files.

| Key | Path, relative to the repository | Pinned SHA-256 | Returned matching Git blob | Read scope |
|---|---|---|---|---|
| S | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md | 93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9 | 136aceb3cbbabcdfa425459562b803b67c548b48 | source register; X/CONT/CAN/FT/ENV/EF/RAD/GS and their proofs |
| F | docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FLOW_2026-09-10.md | 629431c76e40a1af5fcb5f2b6721ae7be8dba3bfe71a2e8f238e6fd32e07e28d | 15493a4cbdb41845c92b176d96f542aff97b07a7 | F1-F5, F15-F24, own line and research log |
| R | docs/routeB_bus/FLOW_INDEPENDENT_CHECK_2026-09-11.md | 17bd247cc4c995a239e22136cb3ba899c0c20d337e8ec1cff49cd65b440c533f | e12910d0fa356f53788786bc40d52e3d4e41d2a3 | complete, including scripts, corrections, S1-S7 and acceptance receipts |
| B | docs/BATCH_PATTERNS.md | cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b | cb63bab5fbff3d39bf63c0b0f081a2264e004f2b | complete |

S's historical explicit-formula dependency is Connes--Consani, *Spectral Triples and Zeta-Cycles*, arXiv:2106.01715v1, section 2.1.1, equations (2.1)-(2.8); its stated positivity consumer is on printed page 5. S also identifies Connes--Consani--Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1, (3.1)-(3.11) and (7.1)-(7.4). These are **RELAY** references read in S's source register, not PDFs freshly checked here. The exact gamma identities additionally used below were read in the primary NIST DLMF HTML sources listed in section 10. No new zero-location theorem is imported.

## 1. Domain, radical family and the first construction that fails

### 1.1 Fixed conventions and domain recheck

Put f=Phi/A, A=||Phi||2>0, with the precise full theta series in the request:

\[
\Phi(x)=e^{x/2}\sum_{n\ge1}(4\pi^2n^4e^{4x}-6\pi n^2e^{2x})e^{-\pi n^2e^{2x}}.
\]

The theta identity makes this function positive and even. Its transform is F(z)=int f(x)e^{-izx}dx=Xi(z)/A. Write F_g for the same transform of any other test. Fourier inversion has factor 1/(2pi); every physical integral below uses dx, not a rescaled coordinate. B is antilinear in its first argument.

Retain exactly alpha(t)=e^{-t/2}/(1-e^{-2t}), c_A=gamma+log(8pi)+pi/2, w_n=Lambda(n)/sqrt(n), and M_+/-(g)=int g(x)e^{+/-x/2}dx. Thus

\[
Q(g)=D(g)-c_A\|g\|_2^2+2\Re(M_+(g)\overline{M_-(g)})
 -2\sum_{n\ge2}w_n\Re\int\overline{g(x)}g(x+\log n)dx,
\quad D(g)=\int_0^\infty\alpha(t)\|g(\cdot+t)-g\|_2^2dt.
\tag{SL1}
\]

The **control space**, the topology in which the source pairing is continuous, is

\[
\|g\|_X^2=\|e^{|x|}g\|_2^2+D(g),\qquad
|B(g,k)|\le C_X\|g\|_X\|k\|_X,\quad C_X=|c_A|+14.
\]

Here is the needed recheck rather than an L2-domain substitution. With W_g=||e^{|x|}g||2, the correlation is bounded by e^{-|t|}W_gW_k. The prime pairing costs at most 2 W_gW_k sum(log n)/n^(3/2)<=10 W_gW_k. Each pole moment has norm at most sqrt(4/3) W_g. Cauchy--Schwarz bounds the D-pairing. These bounds give the displayed C_X. Smooth cutoffs converge in X: expand their translated differences and dominate the cutoff-commutator term by min(C^2t^2,4)|g(x)|^2. This is integrable against alpha(t)dt dx. Compactly supported mollification then gives C_c^infinity(R;C) dense in X. This is precisely the topology used below.

For tau_a g(x)=g(x-a), direct substitution gives

\[
\|\tau_a g\|_X\le e^{|a|}\|g\|_X,
\qquad B(\tau_a g,\tau_a k)=B(g,k).
\tag{SL2}
\]

The two pole factors are e^{a/2} and e^{-a/2}, so their product does not change. Translation is strongly continuous on X by compact-smooth density and the locally bounded operator estimate. Completeness follows from the closed graph description of the weighted L2 term and the translation-difference map, as in S.

### 1.2 The whole equality family, not just one zero quadratic value

For each fixed k, S's ENV bounds f^(k) and f^(k+1) by fixed constants times exp(-(pi/2)e^{2|x|}). Thus f^(k) belongs to X, and integration by parts gives F_{f^(k)}(z)=(iz)^k F(z) without boundary terms. In the stated explicit-formula class, each summand of B(f^(k),g) contains F(z)=0 at the corresponding zero. Consequently B(f^(k),g)=0 for compact smooth g. Density and SL1 extend this to every g in X. This uses the inherited explicit-formula dependency, not an inference from Q(f^(k))=0 and not a positivity hypothesis.

There is also an X-topological check that does not reapply that formula at each order. SL2 preserves the radical of B. The fundamental theorem of calculus, applied to f^(k) and its derivative with the ENV envelopes, gives strong X difference quotients. Their limits are fixed derivatives. A norm limit of radicals remains a radical by continuity. If mu is a compactly supported finite complex Borel measure, the X-valued integral

\[
f^{(k)}*\mu=\int\tau_a f^{(k)}\,d\mu(a),\qquad
\|f^{(k)}*\mu\|_X\le\|f^{(k)}\|_X\int e^{|a|}d|\mu|(a)
\]

is well defined and is again a radical. No estimate uniform in a growing derivative order is used. No claim that this radical family is dense in X is made.

R's S1-S7 survive this domain recheck. For the finite-constraint assertion, the m-by-(m+1) matrix has entries S_c(u_j,f^(2k)/f), with the second slot linear. A nonzero null vector gives a nonzero radical whose even analytic ratio cannot be affine on any interval: Fourier transformation would make a nonzero polynomial times F vanish near zero, where F(0)>0. Equality in the central three-edge inequality forces equal secant slopes on an open set and hence that forbidden affine behavior. Compact cutoffs preserve all central vertices and all m constraints exactly. Continuity gives Q(g_N)->0 and T[g_N/f]<-sigma/2 eventually. This establishes the stated scope, not negativity of Q.

The positive point interval in R's S2 was read with its tail proof and acceptance receipts, but not numerically rerun. It is not an integrated value of sigma. Its strict integrated conclusion also has an analytic check: if S_c[f'/f]=0, the same secant-slope argument makes the analytic odd function f'/f affine, hence equal to cx globally. Integration would make f a Gaussian (or a nonintegrable exponential quadratic), incompatible with positivity and ENV's super-exponential upper bound. Thus S_c[f'/f]>0 without another point computation. The even-derivative argument supplies the arbitrary finite-constraint version.

### 1.3 A new class obstruction to an L2-continuous square supplier

The first candidate was a nonlocal sum of continuous L2 squares. It is ruled out at a stronger scope than a fixed finite projection:

\[
\boxed{\begin{gathered}
S_*(g)=\int_\Omega|\langle k_\omega,g\rangle_{L^2}|^2d\mu(\omega)
 \le Q(g)\quad\hbox{for all }g\in C_c^\infty,\qquad k_\omega\in L^2
\\ \Longrightarrow\quad k_\omega=0\quad\mu\hbox{-almost everywhere}.
\end{gathered}}
\tag{SL3}
\]

The family is assumed measurable, and mu may be any sigma-finite positive measure; no uniform bound on ||k_omega|| is required. For each rational a, compact cutoffs of tau_a f converge both in X and L2. Their Q values tend to zero. Fatou's lemma gives <k_omega,tau_a f>=0 almost everywhere. Intersecting these full-measure sets over rational a and using L2 continuity of translations gives the same equality for every real a.

The translates of f span a dense subspace of L2: orthogonality to all translates says that the inverse Fourier transform of the L1 function conjugate(F_k) F is zero. Hence that product vanishes almost everywhere. The nonzero entire function F has only a measure-zero set of real zeros, so F_k=0 almost everywhere. This proves SL3.

The L2 density used in this proof is ONLY a proof that the individual L2 kernels vanish. It is not X density and does not imply Q=0. The result does not exclude X-continuous but L2-unbounded functionals, distributional constructions, or all finite-rank methods. The concrete repair below works with X-admissible half-line atoms and does not posit a positive-square supplier.

## 2. Q1: an explicit arithmetic kernel with a proved all-test identity

### 2.1 Definitions, measures and normalization

Fix h=2 throughout the final test. The formulas are also valid for every fixed h>1. Put sigma=h+1/2 and let psi=Gamma'/Gamma be the **digamma function**. Define, for real u,v,

\[
\begin{split}
R_h(u)={}&\frac1{\sigma-iu}+\frac1{\sigma-1-iu}-\frac12\log\pi
 +\frac12\psi\!\left(\frac{\sigma-iu}{2}\right)
 -\sum_{n\ge2}\Lambda(n)n^{-\sigma+iu},\\
K_h(u,v)={}&\frac{\overline{R_h(u)}+R_h(v)}{2h+i(u-v)},\qquad
q_{h,u}(x)=\mathbf1_{[0,\infty)}(x)e^{-hx}e^{iux}.
\end{split}
\tag{SL4}
\]

All frequency integrals use ordinary du or du dv. The arithmetic series converges absolutely and uniformly on the real u-axis. It contains every prime power with its original von Mangoldt weight. The two rational terms are the two pole contributions; neither has been removed. **Hermitian kernel** means K_h(v,u)=conjugate(K_h(u,v)); it does not mean positive kernel.

### 2.2 Exact evaluation on half-line atoms

These discontinuous atoms belong to X. Direct calculation gives

\[
\|q_{h,u}\|_X^2\le\frac1{2(h-1)}+5+\frac9h u^2,
\qquad \|q_{2,u}\|_X\le\sqrt6\sqrt{1+u^2}.
\tag{SL5}
\]

Indeed their weighted L2 norm squared is 1/(2(h-1)), and
D(q)=(1/h)int alpha(t)(1-e^{-ht}cos(ut))dt. Use
alpha(t)<=e^{-t/2}(1+1/(2t)), int t alpha<=5, int t^2 alpha<=18, and
1-e^{-ht}cos(ut)<=ht+u^2t^2/2. The jump causes no forbidden derivative-domain assumption.

Write d=2h+i(u-v). The mixed L2 integral is 1/d. The two mixed positive-length correlations are e^{-(h-iv)t}/d and e^{-(h+iu)t}/d. Therefore the D-pairing has numerator
int alpha(t)(2-e^{-(h-iv)t}-e^{-(h+iu)t})dt.
The pole pairing, after multiplying by d, is the sum of the four corresponding reciprocals h+/-1/2-iv and h+/-1/2+iu. This follows from (a+b)/(ab)=1/a+1/b in each product of moments.

For the archimedean part, DLMF 5.9.16, with a change of variable, gives

\[
\frac12\psi(s/2)-\frac12\log\pi
=-\frac{\gamma+\log\pi}{2}
 +\int_0^\infty\frac{e^{-2t}-e^{-st}}{1-e^{-2t}}dt,
\quad\Re s>0.
\]

The reflection, duplication and half-argument values of psi give
psi(1/4)=-gamma-pi/2-3log2, so psi(1/4)-log pi=-c_A. Subtracting this constant proves that the sum of the two archimedean terms is exactly the D numerator minus c_A. Differences near t=0 stay grouped; no divergent integrals are separated. Finally the prime terms are exactly the two correlations in SL1. We obtain the fully signed identity

\[
\boxed{B(q_{h,u},q_{h,v})=K_h(u,v).}
\tag{SL6}
\]

This is an evaluated Gram pairing for an indefinite form, not a positive Gram assumed to equal the source.

### 2.3 Transfer to every original test, with explicit approximation control

Let g be any complex compact smooth test. Choose a real a such that g_a=tau_a g has support strictly inside (0,infinity), and put
G(u)=F_{g_a}(u+ih). This G is a Schwartz function, meaning that it and all derivatives decrease faster than every reciprocal polynomial. Fourier inversion gives the X-valued integral

\[
g_a=\frac1{2\pi}\int_{\mathbb R}G(u)q_{h,u}\,du.
\tag{SL7}
\]

To justify it, SL5 makes the integral absolutely convergent in X. Pointwise Fourier inversion on x>0 identifies it with g_a there; both sides vanish on x<0. The resulting equality is an equality of the same X functions, not merely a formal inversion.

Continuity of B, SL5 and SL6 justify both interchanges of these X-valued integrals and give

\[
\boxed{Q(g)=\frac1{4\pi^2}\iint_{\mathbb R^2}
       \overline{G(u)}K_h(u,v)G(v)\,du\,dv.}
\tag{SL8}
\]

In particular absolute convergence follows from
|K_h(u,v)|<=C_X||q_{h,u}||_X||q_{h,v}||_X, not from a sign assumption.

At h=2, frequency truncation at M has X error at most
sqrt(6)/(2pi) int_{|u|>M}|G(u)|sqrt(1+u^2)du. For a partition of [-M,M] with maximum cell length delta and arbitrary nodes u_j, use coefficients c_j=G(u_j)|I_j|/(2pi). There is the additional X error

\[
\frac{2M\delta}{2\pi}\sup_{|u|\le M}
\left(|G'(u)|\sqrt{6(1+u^2)}+|G(u)|\sqrt{5/2+9u^2/16}\right).
\tag{SL9}
\]

For this bound, differentiate q with respect to u in X: the derivative is ixq. Its weighted norm squared is 1/4, and its physical derivative has L2 norm squared (4+u^2)/32. The bound int t^2 alpha<=18 then gives ||xq||_X^2<=5/2+9u^2/16. Difference quotients converge by the same weighted estimates. The fundamental theorem of calculus proves SL9.

If the total X error is e, the quadratic error is at most C_X e(2||g_a||_X+e). Thus the finite expression sum conjugate(c_i)K_h(u_i,u_j)c_j converges to Q(g), with a proved error for each fixed original g. No even-test restriction, common finite support radius or assumed inverse is hidden in this map.

## 3. The source coupling and a smooth theta-only kernel

### 3.1 Exact coupling between arithmetic and theta weights

On Re s>1, unique factorization gives the absolutely convergent Euler product. Differentiating its absolutely locally uniformly convergent logarithm gives zeta'/zeta=-sum Lambda(n)n^{-s}. The factors are nonzero there. Differentiating the displayed definition of xi(s) consequently gives R_h(u)=xi'(sigma-iu)/xi(sigma-iu).

S's canonical Mellin calculation gives F(z)=xi(1/2-iz)/A. Its fixed-order theta envelopes justify differentiation. Hence the independently evaluated source relation is

\[
\boxed{R_h(u)F(u+ih)=iF'(u+ih)
       =\int_{\mathbb R}x f(x)e^{hx}e^{-iux}dx.}
\tag{SL10}
\]

F(u+ih) is nonzero for real u: here Re(sigma-iu)>1, so the Euler product, gamma factor and the two polynomial factors have no zero. This is a zero-free statement in an absolute-convergence half-plane, not a critical-strip assertion. Relation SL10 couples the full arithmetic correlations to a theta moment; the radical identities alone do not contain this calculation.

Define F_h(u)=F(u+ih) and the **diagonal congruence**, an invertible change of coordinates on each finite coefficient space,

\[
\begin{split}
W_h(u,v)&=\overline{F_h(u)}K_h(u,v)F_h(v)\\
&=\frac{i\{\overline{F_h(u)}F'(v+ih)
              -\overline{F'(u+ih)}F_h(v)\}}{2h+i(u-v)}.
\end{split}
\tag{SL11}
\]

There is no assertion that division by F_h defines a bounded operator on a function space.

### 3.2 The actual integrated theta kernel

Define the full, smooth, real symmetric kernels

\[
V_f(x,y)=\int_0^\infty(x+y+2t)f(x+t)f(y+t)dt,
\qquad H_h(x,y)=e^{h(x+y)}V_f(x,y).
\tag{SL12a}
\]

Every t-tail and every theta summand is included. The normalization is exactly A^{-2} through the two factors f. Then

\[
\boxed{W_h(u,v)=\iint_{\mathbb R^2}H_h(x,y)e^{iux-ivy}\,dx\,dy.}
\tag{SL12}
\]

**Proof.** Expanding the numerator in SL11 with SL10 gives
int int (x+y)f(x)f(y)e^{h(x+y)}e^{iux-ivy}dxdy. Insert
(2h+i(u-v))^{-1}=int_0^infinity e^{-2ht}e^{-iut+ivt}dt.
Its absolute integrability is bounded by
(1/(2h)) int int |x+y|f(x)f(y)e^{h(x+y)}dxdy<infinity.
The substitution x=X+t, y=Y+t gives exactly SL12a. This proves SL12 by ordinary absolute Fubini; no residue sum or zero-location assertion occurs.

All polynomially weighted derivatives of H_h are integrable. To check this explicitly after differentiating a fixed number of times, make the same substitution X=x+t,Y=y+t. Every term is a polynomial in X,Y,t times e^{h(X+Y)-2ht} and a product of fixed derivatives of f at X and Y. The t moments are finite, and ENV pays all X,Y moments. Applying the same estimate to sufficiently many derivatives also gives bounded polynomially weighted derivatives by the elementary two-variable Sobolev estimate. Thus H_h is a Schwartz kernel, in particular continuous, absolutely integrable and Hilbert--Schmidt on L2. This is a statement about this new kernel, not a global L2 operator realization of Q.

A noteworthy but insufficient positivity is visible. With m=(x+y)/2 and d=(y-x)/2, evenness of f gives

\[
V_f(x,y)=\int_{|m|}^\infty 2v f(v-d)f(v+d)dv>0.
\tag{SL13}
\]

The interval from -|m| to |m| cancels because the product is even and 2v is odd. This proves entrywise positivity. Section 5 shows explicitly why it does not prove positive semidefiniteness.

### 3.3 Exact sign transfer, without a function-space inverse

For this one fixed h=2 the following assertions are equivalent:

(A) Q(g)>=0 for every original complex compact smooth g.

(B) Every finite matrix [K_h(u_i,u_j)] is positive semidefinite, for all real nodes and all complex coefficient vectors.

(C) Every finite matrix [W_h(u_i,u_j)] is positive semidefinite.

(D) int int conjugate(a(x))H_h(x,y)a(y)dxdy>=0 for every complex a in C_c^infinity(R).

Here **positive semidefinite** means that every quadratic value is nonnegative; the equivalence does not assert that these conditions hold.

For (A)=>(B), approximate the finite sum of q-atoms by compact smooth functions in X and use SL1 and SL6. For (B)=>(A), use SL7-SL9. For (B)<=>(C), the diagonal entries F_h(u_i) are nonzero; finite diagonal congruence preserves and reflects the sign.

For (D)=>(C), use the compact cutoffs of a(x)=sum c_j e^{-iu_j x} and let the cutoffs tend to one. Dominated convergence applies because H_h is in L1 and the finite exponential sum is bounded. SL12 identifies the resulting quadratic value with that of W_h. Conversely, (C) gives nonnegative integrals against every compactly supported smooth frequency coefficient by Riemann sums. Passing to Schwartz coefficients is justified by the boundedness of W_h and their L1 tails. Fourier inversion then gives (D), including every compact smooth spatial a. All 1/(2pi) factors occur in pairs and are positive. We have proved

\[
\boxed{\text{original all-test sign}\quad\Longleftrightarrow\quad H_2\succeq0.}
\tag{SL14}
\]

The proof deliberately does not set a=Fourier^{-1}(G/F_h). That quotient need not have the required integrability. Finite congruence followed by the separately proved X transfer repairs this domain failure.

### 3.4 Where the derivative cancellation lives in the new expression

For every fixed radical w obtained in section 1, let g_N=chi_N w. Formula SL8 applies to each g_N after its own support shift a_N. It gives exactly Q(g_N), and
|Q(g_N)|<=C_X||g_N-w||_X(||g_N||_X+||w||_X)->0.
Thus the entire derivative/translation/convolution equality family is preserved by an explicitly controlled original-source limit. A large support shift may make the individual frequency coefficients large. No convergence of those coefficients in an unproved inverse norm is claimed.

There is an additional direct integrated cancellation for the fixed derivatives. Put L(z)=F'(z)/F(z) on the two lines Im z=+/-h only, and F_g^#(z)=conjugate(F_g(conjugate z)). Evaluation of the same two pole integrals, the grouped digamma integral and the absolutely convergent prime series used in SL6 gives, for compact smooth g,v,

\[
B(g,v)=\frac1{2\pi i}\left(\int_{\mathbb R-ih}-\int_{\mathbb R+ih}\right)
 L(z)F_g^\#(z)F_v(z)\,dz.
\tag{SL15}
\]

Both horizontal lines are oriented to the right. One can verify the signs directly: L(u+ih)=-iR_h(u) and L(u-ih)=i conjugate(R_h(u)). The first resulting term is conjugate(F_g(u-ih)) R_h(u)F_v(u+ih)/(2pi); the other is its Hermitian partner. Fourier inversion of (sigma-iu)^{-1} and (sigma-1-iu)^{-1} gives the e^{-t/2} and e^{t/2} pole correlations. The prime multiplier gives -Lambda(n)/sqrt(n) times the positive-length correlation. The grouped archimedean multiplier gives D-c_A. These calculations prove SL15 directly from SL1.

For justification, compact transforms on fixed horizontal lines are Schwartz, R_h has at most linear growth (subtract its value at zero in the digamma integral and use |1-e^{iut}|<=|u|t), the prime series is uniformly absolutely convergent, and the difference in the digamma integrand cancels at t=0. One may first integrate over epsilon<t<T; after Fourier inversion compact correlations control infinity and smooth differences control zero. These bounds justify both limiting operations. For g=f^(k), its cutoff transforms converge in every polynomially weighted uniform norm on the strip |Im z|<=h by ENV and integration by parts. SL1 therefore extends SL15 to that g.

Now F_g^#(z)=(-iz)^k F(z), so the whole integrand in SL15 becomes (-iz)^k F'(z)F_v(z), an entire function. Its vertical rectangle sides tend to zero by the uniform strip decay just stated. Cauchy's theorem makes the two horizontal integrals equal. This explicitly cancels the whole derivative family without summing zero residues. It is another verification of the equality, not a proof of a lower sign for an arbitrary g.

## 4. The original central and far slacks remain present

For precision, the retained measures are not replaced by a uniform reserve. Write c_t(x)=f(x)f(x+t), b=alpha-e^{-t/2}-e^{t/2}, n(t)=b_-(t), and

\[
\mathcal C_+(dy,du)=b_+(u)c_u(y)dydu+
 \sum_{n\ge2}w_nc_{\log n}(y)dy\,\delta_{\log n}(du),
\quad \mathcal D_-(dx,dt)=\mathbf1_{t>\tau}n(t)c_t(x)dxdt.
\]

The central measure Gamma_c is precisely the following pushforward: on Omega_c={t in I, |x+t/2|<=1/8}, integrate the ordered law j(s1)j(s2)j(s3)/Z(t), s1+s2+s3=t, and charge t/s_i to its three successive edges. Here I=[log(7/5),log(8/5)], j(s)=s^3b_+(s), Z=j*j*j. There is no factorial. All endpoints are in [-H,H], H=1/8+max(I)/2<3/8. Its point slack is sum_{i<j}s_i s_j|d_i/s_i-d_j/s_j|^2.

For Gamma_e retain the exact two probability-one laws of F, including all reflected preimages. Put p=log2. On Omega_3^+={t in I,x+t/2>=11/4}, use x,x-q,x-2q,x+t, q=(p-t)/2, each coefficient 3. There are four vertices, as corrected in R. Reflect for Omega_3^-. On Omega_9^+={t>tau,t outside I,x>=t+4}, put k=floor(t/p)+2 and u=(kp-t)/8; use x-iu for i=0,...,8, then x+t, all nine coefficients 9. Reflect for Omega_9^-={t>tau,t outside I,x+t<=-t-4}. The last atom has weight log2/2^(k/2), not k log2/2^(k/2).

These definitions specify the exact Gamma_3 and Gamma_9 by pushforward, not an approximate replacement of their densities. They include the short-edge inverse Jacobian factors 6 and 72 and the prime inverse Jacobian 1. F23's retained bound is Gamma_e<=1_U C_+/16, where both endpoints of U are at least 2 or both at most -2. Its proof and R's check have their stated scope; no new central certificate or far-tail numerical calculation was run here. The algebra below needs finiteness and the exact path laws, not a newly verified numerical central ceiling.

Let Omega_e be the union of those four far regions. The exact unpaid set remains

\[
\Lambda=\{t\in I,\ 1/8<|x+t/2|<11/4\}
 \cup\{t>\tau,\ t\notin I,\ -2t-4<x<t+4\}.
\]

For original compact r, define S_c,S_e by the charged edge energy minus the demand energy on Omega_c,Omega_e, respectively. Their nonnegativity is the path inequality, not the sign of Q. Separate convergence holds by smooth differences near zero and theta decay at infinity; the central charge is finite since j(s)/s is integrable, and the far charge is bounded by F23. If G is obtained from the original g=fr by SL7, then the new exact integrated accounting is

\[
\boxed{\begin{split}
&S_c[r]+S_e[r]+\int|\Delta r|^2d(\mathcal C_+-\Gamma_c-\Gamma_e)
             -\int_\Lambda|\Delta r|^2d\mathcal D_-\\
&\hspace{18mm}=\frac1{4\pi^2}\iint\overline{G(u)}K_h(u,v)G(v)du\,dv.
\end{split}}
\tag{SL16}
\]

The left side uses the original ratio r and the original physical slacks. Only the representation of g on the right uses a support shift. No translated ratio is silently substituted into the fixed central construction. In particular SL16 is never applied directly to (g-alpha f')/f or to a noncompact derivative ratio. For cutoff radicals the central equalities of R remain exact, the whole right side tends to zero, and the far slack and signed remainder must compensate. Neither is discarded.

## 5. Q2: attempted sign proofs, exact failures and concrete repairs

### 5.1 Entrywise positive theta kernels need not have positive quadratic form

SL13 is not the unpaid inequality. An exact smooth control shows the difference. Let f_c(x)=e^{-x^2}(1+x^4/3), an everywhere positive even function with all fixed derivatives decreasing faster than every exponential. Construct V by SL12a with this f_c, solely for this control. Gaussian polynomial integration gives

\[
V(1,1)=V(-1,-1)=\frac{23}{12e^2},\qquad
V(1,-1)=\frac{73}{36e^2}.
\]

For example the two constants are the integrals of
(1+(z+1)^2/3)^2 e^{-2z} on z>=0 and
2v(1+(v-1)^4/3)(1+(v+1)^4/3)e^{-2v^2} on v>=0, respectively, with the common factor e^{-2}. Expansion uses int_0^infinity z^j e^{-2z}dz=j!/2^(j+1). Thus the vector (1,-1) has value

\[
2V(1,1)-2V(1,-1)=-\frac{2}{9e^2}<0.
\tag{SL17}
\]

For H_h use the congruent vector (e^{-h},-e^h). Smooth compact approximations to the two point masses retain a negative value by continuity. This refutes a kernel-sign argument using only positivity, evenness, rapid decay and SL13. It is not the canonical theta source and does not satisfy its full arithmetic coupling SL10. No negative canonical Q is inferred.

### 5.2 A Gaussian rank-one repair also fails for the actual theta source

A Gaussian source f(x)=exp(-lambda x^2/2) makes V_f(x,y)=f(x)f(y)/lambda. This suggests a positive rank-one lower comparison. For the actual f, integration of the product derivative gives the exact repaired identity, for every fixed lambda>0,

\[
\begin{split}
V_f(x,y)={}&\lambda^{-1}f(x)f(y)\\
&+\int_0^\infty\left[x+y+2t+\lambda^{-1}\left(\frac{f'(x+t)}{f(x+t)}+
                         \frac{f'(y+t)}{f(y+t)}\right)\right]
 f(x+t)f(y+t)dt.
\end{split}
\tag{SL18}
\]

The boundary at infinity vanishes by ENV. The signed integral cannot be omitted or assumed positive. In fact V_f>=lambda^{-1} f tensor f as quadratic forms is false for every fixed lambda>0 for the actual source.

Here is a quantitative source proof. For x>=0, the first theta term and the complete geometric tail give

\[
\frac{2\pi^2}{A}e^{9x/2}e^{-\pi e^{2x}}
 \le f(x)\le\frac{8\pi^2}{A}e^{9x/2}e^{-\pi e^{2x}}.
\]

For the lower bound use pi>3. For the upper bound use n^4<=16^(n-1), n^2-1>=3(n-1), and sum(16e^{-3pi})^(n-1)<2. Consequently, for s>=0,
f(x+s)/f(x)<=4exp(-a_x s), a_x=2pi e^{2x}-9/2>0. Therefore

\[
\frac{V_f(x,x)}{f(x)^2}
 =2\int_0^\infty(x+s)\left(\frac{f(x+s)}{f(x)}\right)^2ds
 \le16\left(\frac{x}{a_x}+\frac1{2a_x^2}\right)\longrightarrow0.
\tag{SL19}
\]

Choose any x for which the explicit upper bound is less than 1/lambda. The diagonal of V_f-lambda^{-1} f tensor f is negative there; compact smooth approximate point masses refute the quadratic comparison. This is a full-theta, all-tail obstruction to that proposed repair, not a numerical small-eigenvalue diagnostic. It does not refute V_f>=0. The valid repair is to retain the full signed integral of SL18, equivalently the complete kernel SL12a, with no fixed rank-one reserve.

### 5.3 The first unpaid sign after those repairs

The entire remaining assertion, with h fixed to 2 and every parameter explicit, is

\[
\boxed{\forall a\in C_c^\infty(\mathbb R;\mathbb C),\quad
\int_{\mathbb R}\!\int_{\mathbb R}\overline{a(x)}\,e^{2(x+y)}
\left[\int_0^\infty(x+y+2t)\frac{\Phi(x+t)\Phi(y+t)}{A^2}dt\right]
a(y)\,dx\,dy\ \ge0.}
\tag{SL20}
\]

This is an explicit continuous-kernel inequality on a specified domain, not the scalar T with a new name. SL10-SL14 prove its exact coupling and transfer to the unchanged source. SL17 and SL19 show why two concrete sign arguments for it fail. No proof of SL20, of its complete signed remainder in SL18, or of the equivalent all-vector K_2 inequality has been established in this batch. This is FIRST_FAILURE Q2.

### 5.4 Every fixed prime truncation has a negative original-class witness

Another attempted repair is to prove positivity after keeping finitely many prime powers and then take a limit. It fails at EVERY fixed cutoff, not just at a sampled matrix.

Let Q_N be SL1 with only n<=N in its prime sum, N>=2, and R_{h,N},K_{h,N} be the corresponding SL4 expressions. The proof of SL6-SL9 applies to them too. Put delta=1/8 and
phi(x)=c exp(-1/(1-(x/delta)^2)) for |x|<delta, zero otherwise, where c>0 is chosen so ||phi||2=1. Let m_phi=int phi(x)e^{x/2}dx=int phi(x)e^{-x/2}dx>0, and C_phi(t)=int phi(x)phi(x+t)dx. It is nonnegative, at most 1, and zero for |t|>=2delta. Define g_a=tau_a phi-tau_{-a}phi for a>delta.

Direct expansion of ALL source terms gives

\[
\begin{split}
Q_N(g_a)={}&2Q_N(\phi)+2\int_0^\infty\alpha(t)C_\phi(t-2a)dt
 -4m_\phi^2\cosh a\\
&+2\sum_{2\le n\le N}w_n C_\phi(\log n-2a).
\end{split}
\tag{SL21}
\]

The other shifted correlation C_phi(t+2a) vanishes. The negative cosh term comes from both pole moments and has not been invented as a separate potential. If 2a-2delta>log N, the last sum is zero. For a>=1 the positive cross integral is at most 8delta alpha(2a-2delta)<1. Let M_phi=C_X||phi||_X^2, a finite source-defined number independent of N. The same continuity estimate bounds |Q_N(phi)| by M_phi. The explicit choice

\[
a=2+\max\left(0,\tfrac12\log N,
                 \log\frac{2M_\phi+1}{2m_\phi^2}\right)
\]

therefore gives Q_N(g_a)<=2M_phi+1-2m_phi^2e^a<0. This is an exact smooth compact witness for the truncated form. By SL7-SL9 it also forces some finite negative coefficient vector for K_{h,N}; no computation of that vector is needed for the theorem.

This obstruction concerns Q_N, not Q. In the full form the primes near log n=2a supply the omitted cross terms. Their sign cannot be decided by a cutoff that excludes them. A fixed compact witness cannot be carried unchanged to all increasing N by this argument.

### 5.5 Concrete repair of truncation: restore the tail with an all-vector budget

Put sigma=h+1/2 and

\[
E_N=N^{1-\sigma}\left(\frac{\log N}{\sigma-1}
                            +\frac1{(\sigma-1)^2}\right).
\]

The integral test applied to log(x)x^{-sigma}, decreasing for x>=2 here, gives |R_h(u)-R_{h,N}(u)|<=E_N uniformly in u. Hence for EVERY finite node set and EVERY complex coefficient vector,

\[
\left|\sum_{i,j}\overline{c_i}(K_h-K_{h,N})(u_i,u_j)c_j\right|
 \le\frac{E_N}{h}\left(\sum_j|c_j|\right)^2.
\tag{SL22}
\]

For the fixed original g and its fixed G in SL7, the corresponding integrated error is at most E_N||G||_1^2/(4pi^2h), which tends to zero. In fact its exact integrated prime tail is zero once N>=exp(diam(supp g)), by the correlation support; the bound is useful before that point. Neither statement is uniform on the moving witnesses g_a of SL21.

Thus finite truncation is repaired as an approximation with a quantified signed error, NOT as a family of globally positive forms. To prove SL20 by such approximations one would still have to prove a lower bound for all coefficient vectors that pays this error and survives the physical test transfer. SL21 prohibits asserting global nonnegativity of a fixed K_{h,N}. SL22 does not itself supply the missing lower bound.

## 6. Q3: what reaches all original tests, and what does not

The actual proved output transfers to every original g in C_c^infinity(R;C): SL8 evaluates its whole source form, SL16 retains its exact fixed slacks, and SL14 gives an if-and-only-if sign transfer. The proof uses an X-convergent half-line expansion, explicit frequency and quadrature errors, finite invertible congruences, and the absolutely convergent double transform of a full theta kernel. No growing derivative order, even-only density argument, finite physical window, missing prime tail, boundary residue or inverse-norm assumption remains inside these identities.

The hypothesis still required for a nonnegative conclusion is exactly SL20. Conditional on SL20, SL14, then SL8 and SL16, prove Q(g)>=0 on the unchanged complex class. The published Weil consumer is then the inherited terminal dependency identified in section 0. This conditional proposition is not an unconditional proof, and Q3/OVERALL are consequently partial. Conversely, no negative value of the actual complete theta-source form has been proved here.

There is no new noncompact extension theorem for the separate S_e or T functionals. The radical limits in sections 1 and 3.4 use Q and B on X and the original compact cutoffs. That distinction prevents the invalid use of F24 after subtracting a derivative radical.

## 7. False-positive controls and one decisive next test

### 7.1 Required exact algebraic controls

On C^(m+2), let Q_+(z)=|z_(m+2)|^2 and S(z)=sum_(k=1)^(m+1)|z_k|^2. The first m+1 coordinates form a genuine radical. Any m linear constraints restricted to that radical have a nonzero common null vector w. On w, Q_+=0 and Q_+-S=-||w||^2<0. This models residual negativity despite a nonnegative whole form.

On the DIFFERENT space C^(m+3), let Q_-(z)=|z_(m+2)|^2-|z_(m+3)|^2 with the same S on the first m+1 coordinates. It has the same radical and the same residual obstruction there, but also a negative direction outside that radical. At m=0 the last unit vector in C^2 gives Q_+=1; the last unit vector in C^3 gives Q_-=-1. These dimensions and values are not interchanged.

Our construction does not certify Q_-: neither a radical nor S>=0 was used as a sign supplier. The additional actual-source identity is SL10, and its independently evaluated consequences are SL11-SL12. They identify the exact kernel to test but do not, by themselves, distinguish a positive form from every indefinite form. The extra SIGN fact needed to distinguish the signs is precisely SL20, which is still unproved. SL17 supplies a second warning: even the theta-kernel algebra applied to an arbitrary positive even source does not force positivity. Controls are controls, not substitutions for the canonical source.

### 7.2 One new next_decisive_test

**Test name: THETA_SQUARED_COORDINATE_LOG_CONCAVITY.** Use the exact full canonical f, with no prime or theta truncation left without a tail proof. The observable is

\[
J_f(x)=x\big((f'(x))^2-f(x)f''(x)\big)+f(x)f'(x),\qquad x>0.
\tag{SL23}
\]

The proposed test is to prove J_f(x)>=0 for every x>0 from the full theta series and its derivative tails, or exhibit one rigorously negative value. This is not an eigenvalue or mesh request. Stop at the first negative witness, or report the precise unresolved interval/tail inequality; do not automatically launch a precision, degree or window sweep.

The reason this test pays a new, exact subproblem is the identity

\[
\begin{split}
V_f(x,x)-V_f(x,-x)
=2\int_0^\infty t\left[f\!\left(\sqrt{x^2+t^2}\right)^2
                         -f(x+t)f(x-t)\right]dt.
\end{split}
\tag{SL24}
\]

For the first term substitute v=sqrt(x^2+t^2) in 2 int_x^infinity v f(v)^2dv; the second term is SL12a at (x,-x). All tails converge by ENV. Write ell(s)=log f(sqrt(s)). For s=x^2>0,
ell''(s)=-J_f(x)/(4x^3 f(x)^2). Thus J_f>=0 makes ell concave. Jensen's inequality applied to (x+t)^2 and (x-t)^2, whose average is x^2+t^2, makes the integrand in SL24 nonnegative. Evenness handles x-t<0 and continuity handles zero.

A successful test therefore proves the odd reflection-diagonal family V_f(x,x)>=V_f(x,-x) for every x>=0. It does NOT prove all off-diagonal quadratic inequalities, the even sector, or SL20. Failure kills this particular pointwise comparison mechanism, not the full kernel route. The noncanonical control in SL17 fails exactly such a necessary reflection comparison. This test is new relative to S1-S7, F25 and the central certificate; none of those computations is requested again.

## 8. Prediction scores and bounded disposition

| Frozen content prediction | Score | Exact evidence and limits |
|---|---|---|
| P1, p=.95 | CONFIRMED | Sections 1.1-1.2 recheck the source domain and the finite-constraint radical argument; section 4 preserves the same charges. Negative T does not imply negative Q. The old numerical point interval is read evidence, not a fresh computation. |
| P2, p=.85 | CONFIRMED | Sections 1.2 and 3.4 preserve every fixed derivative order, and SL16 keeps both slacks. The finite-central-constraint completion remains excluded. SL3 additionally excludes the explicitly stated L2-square class, not every finite-rank or signed method. |
| P3, p=.75 | CONFIRMED | SL8, SL10-SL12 and SL16 are exact integrated source relations; SL3, SL19 and SL21 give new scoped obstructions, with the repairs in sections 2, 3.3 and 5.5. SL20 remains unpaid. |

These are outcomes of preregistered content predictions, not probabilities that RH is true, that a proof is complete, or that this manuscript will pass independent review. The single operative directive is the header's theta-kernel signed-comparison directive, with the single bounded test in section 7.2. Do not resume the stopped central, shell, inward-prime or 160-price campaigns on the basis of this verdict. Publication changes no Lean, queue, runtime, registry, old verdict or RH-claim file.

## 9. PROSHKA'S OWN LINE

I chose the half-line kernel because its entries can be evaluated directly from the unchanged source.
The topology is part of that choice: a half-line jump is admissible in X without pretending that Q is an L2 operator.
The first nearby alternative was a positive integral of ordinary L2 squares.
The translates of the canonical radical rule out every nonzero supplier in that class.
The second nearby alternative was another fixed finite projection against the central slack.
The accepted analytic obstruction already settles that proposal, so enlarging its matrix would add no mechanism.
The arithmetic kernel keeps the two poles visible, which makes the fixed prime-cutoff failure easy to locate.
That failure is not a statement that the full arithmetic source is negative.
Its witnesses move their separation beyond every retained prime correlation.
The full theta transfer is more informative than a renamed residual because it produces an explicit smooth two-variable kernel.
It also avoids dividing a general transformed test by a function that may be extremely small.
Only finite diagonal changes of coordinates are inverted.
What surprised me is that every entry of the theta kernel is positive without any zero-location assumption.
What surprised me next is how little that fact says about its quadratic sign.
The elementary polynomial-Gaussian control makes that distinction impossible to ignore.
The first move beyond this batch is the squared-coordinate logarithmic concavity test for the exact theta source.
A rigorously negative value of its displayed derivative observable would kill that proposed sufficient mechanism.
A positive result would pay the reflection-diagonal family, not the whole form.
The second move is to exploit that family in an off-diagonal signed comparison for the full two-variable kernel.
A negative compact-test value of the proposed comparison remainder would kill that comparison, not automatically the kernel itself.
I would ask for an existing exact analytic bound on the displayed theta logarithmic slope, with its full derivative tails.
I would not ask for another small eigenvalue table or the already authenticated central cover.
The finite-cutoff theorem says that a globally positive truncated source is the wrong intermediate objective.
The rank-one theorem says that a fixed Gaussian reserve is also the wrong objective for the actual far theta tail.
I distrust an argument that turns either failed objective into a verdict on the unmodified source.
I also distrust a kernel argument that silently identifies entrywise positivity with positivity on all coefficient vectors.
The remaining problem here is specific: prove the full signed theta-kernel inequality, rather than spend its equalities twice.
The present identities preserve that problem and expose two concrete places where an apparent proof would lose it.

## 10. RESEARCH LOG

### 10.1 Sources consulted, with READ versus RELAY

READ, complete and rehashed: the SLACK controlling request at commit d92fd17e78b28fe93939e6b94becf1b90c68dddc, path and exact receipt in the header; definitions, fixed phase, response schema and write scope.

READ, selected mathematical sections: S at SOURCE_BASE, source register and X/CONT/CAN/FT/ENV/EF/RAD/GS, chiefly file lines 80-285 and 375-460; domain continuity, canonical normalization, decay, radical mechanism and original signed change of variables. Complete file hash was not recomputed here.

READ, selected mathematical sections: F at SOURCE_BASE, F1-F5, F15-F24, section 9 and section 10, chiefly lines 330-550 and 662-745 in addition to the opening construction; exact central and far laws and their unchanged accounting. Complete file hash was not recomputed here.

READ, complete: R at SOURCE_BASE, including F15's four-vertex correction, F25's replacement rather than multiplication of indicators, S1-S7, scripts and acceptance receipts; exact scopes of previous obstructions and reported interval evidence. No script or central certificate was rerun, and the complete file hash was not recomputed here.

READ, complete: docs/BATCH_PATTERNS.md at SOURCE_BASE; proof-construction, provenance, false-positive-control and publication rules, not an analytic premise. Complete file hash was not recomputed here.

RELAY only: Connes--Consani, arXiv:2106.01715v1, https://arxiv.org/abs/2106.01715v1, section 2.1.1 (2.1)-(2.8), printed page 5 criterion and section 3 radical discussion, as explicitly identified in S. No PDF was freshly read and no current-version theorem numbering is substituted.

RELAY only: Connes--Consani--Moscovici, arXiv:2511.22755v1, https://arxiv.org/abs/2511.22755v1, (3.1)-(3.11), (7.1)-(7.4), as identified in S; historical source conventions and canonical normalization, not a newly authenticated PDF dependency.

READ, primary HTML: NIST DLMF https://dlmf.nist.gov/5.9, equation 5.9.16; the digamma integral used in the exact archimedean evaluation. Only the elementary identity is imported; the transfer and kernel calculations are derived here.

READ, primary HTML: NIST DLMF https://dlmf.nist.gov/5.5, equations 5.5.4 and 5.5.8; reflection and duplication of psi for the exact c_A constant.

READ, primary HTML: NIST DLMF https://dlmf.nist.gov/5.4, equations 5.4.12-5.4.13; psi at 1 and 1/2 for the same constant.

READ, primary HTML: NIST DLMF https://dlmf.nist.gov/5.7, equation 5.7.6; the convergent digamma expansion as a check on the grouped archimedean multiplier and its growth. No positivity theorem was taken from it.

READ, primary HTML: NIST DLMF https://dlmf.nist.gov/25.2, Dirichlet-series definitions and differentiated series; absolute-convergence conventions. The Euler-product logarithmic derivative used in SL10 is justified directly by unique factorization and absolute convergence, not by an unverified zero-location reference.

READ, operational only: GitHub file, branch and contents-write action schemas and repository responses; exact request transport, blob metadata and authorized publication. They are not mathematical evidence. A direct container acquisition route did not supply the shelf bytes; the request hash uses the exact captured connector text instead.

### 10.2 Branches tried and abandoned or retained

L2-continuous integral of positive squares: abandoned at the precise supplier inequality in SL3, which forces all its kernels to vanish.

Finite central-slack projection: not expanded; R's S6 and section 1.2 already exclude repairing the slack-dropped comparison that way.

Half-line source pairing: retained; SL6 evaluates every signed component and SL7-SL9 supply the missing X transfer.

Direct division of a general frequency coefficient by F_h: abandoned as an unjustified domain operation; repaired by finite congruence and the separate transfer in SL14.

Entrywise positivity of the theta kernel: abandoned as a sign proof at the exact control SL17.

Gaussian rank-one domination of the actual theta kernel: abandoned for every fixed positive coefficient by the all-tail diagonal bound SL19; SL18 retains the compensating signed integral.

Global positivity at a fixed prime cutoff: abandoned for every finite N by the explicit compact witness SL21; SL22 repairs only its use as a signed approximation.

Full theta-kernel positivity: retained as the explicit unpaid inequality SL20, not relabeled as a proved theorem.

Squared-coordinate logarithmic concavity: retained as the one unexecuted next test; SL24 proves exactly the reflection-diagonal consequence it would supply.

### 10.3 Reusable intermediate calculations and limits

The two pole moments of each half-line atom are 1/(h-1/2-iu) and 1/(h+1/2-iu). Their four-reciprocal identity is what fixes both terms in SL4.

The X atom estimates SL5 and SL9 and the quadratic error C_X e(2||g_a||_X+e) apply to every coefficient vector produced by the fixed-test expansion, without positivity.

The exact source moment relation is R_h F_h=iF'_h, with the derivative taken in the complex argument. It is valid on an absolute-convergence line and does not assert a bounded inverse.

The full theta kernel has the entrywise identity SL13 and the signed Gaussian comparison SL18. The former is positive; the latter's remainder cannot be discarded.

The polynomial-Gaussian control was evaluated by exact symbolic polynomial integration, not by a numerical theta simulation: the rational coefficients are 23/12, 73/36 and -2/9, with the common factor e^{-2}.

For every fixed prime cutoff the two-separated-bump identity SL21 isolates the unpaid pole cross term. Its witnesses depend on N, so it is not a negative test for the full form.

The uniform prime-multiplier bound and all-vector error are SL22. A fixed-test limit is paid; a uniform moving-test sign is not.

The reflected theta-kernel difference is SL24. Concavity of log f(sqrt(s)) would pay its entire integral, but not the other quadratic directions of SL20.

No new spectral grid, eigenvalue table, adaptive interval campaign, Lean file, formal kernel gate, or independent reviewer was used in this adjudication. The actual final byte counts, hashes, commit, changed-path check and remote publication status belong to the external receipt, not inside this hashed file.
