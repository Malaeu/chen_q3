# STATUS: TRY_DENSITY_INFINITE_THINNING_COUPLED_KERNEL
```yaml
OPERATIVE_CLASS: TRY_DENSITY_INFINITE_THINNING_COUPLED_KERNEL
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-11-DENSITY
BOUNDARY_ID: GOAL058_THETA_PROBABILITY_DENSITY_FULL_FORM_SIGN
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
ACTUAL_FULL_PROBABILITY_LAW_USED: true
NEW_SOURCE_IDENTITY_PROVED: true
NEW_SOURCE_IDENTITIES:
  - "DN2: r(t)=4*pi^2*exp(-pi*t)*E_mu[(t-Z)_+], with Z=sum_{n>=2} Gamma(2,1)/(pi*(n^2-1))"
  - "DN12: mu is stationary for Z -> Z/2+Y; Y is the full Bernoulli-exponential innovation in DN11"
  - "DN13: V_f=integral integral B_half(s,t) mu(ds) mu(dt), with exact independent innovations and both reflections"
NEW_PAID_SOURCE_BOUND:
  statement: "DN14-DN15: uniformly in the conditioning state, the repaired components have a double-exponential tail"
BOTH_FULL_PARITY_FORMS_PROVED: false
LOWER_SIGN_PROVED: false
FULL_SIGNED_REMAINDER_PAID: false
DERIVATIVE_EQUALITY_PRESERVED: true
PX_RH_CLAIM: NOT_MADE
HONESTY_STATE: CHALLENGER_NOT_RH
BUS_010: VOID
REQUEST_LOCK:
  COMMIT: 122076a3430251d8f1f9b0cd0577938456eaaed2
  BLOB: ffeb152da44d1b1b89917f2921b287f80e3fb4a0
  SHA256: 09b95fe3c5f228df3bac4905259f60e2329e943fa9e78d1898129c5eff7311b2
  BYTES: 14952
  LINES_LF: 83
  FINAL_LF: true
  ATTACHMENT_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: 659f389caf5e6ce7a354e7e8e804fc0e26259949
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
SOURCE_VERIFICATION:
  REQUEST_FULL_BYTES: VERIFIED
  S_FULL_LOCAL_SHA256_AND_BLOB: VERIFIED
  S_PINNED_CONNECTOR_BLOB: MATCH
  R_PINNED_CONNECTOR_BLOB: MATCH
  R_FULL_LOCAL_SHA256_RECOMPUTATION: NOT_COMPLETED
  B_PINNED_CONNECTOR_BLOB: MATCH
  B_FULL_LOCAL_SHA256_RECOMPUTATION: NOT_COMPLETED
  P_LFS_POINTER: READ_MATCHING_METADATA
  P_PINNED_PDF_MEDIA_SHA256: NOT_VERIFIED
  P_EXTERNAL_ARXIV_COPY: SELECTED_EQUATIONS_READ_AND_PAGE_7_SCREENSHOT
  P_EXTERNAL_COPY_BYTE_IDENTITY_TO_PINNED_MEDIA: NOT_ESTABLISHED
FIRST_FAILURE:
  INITIAL_CONSTRUCTION: "Conditional positivity is false on a positive-mu-product-measure box; DN8."
  FINITE_GAMMA_REPAIR: "Every symmetrized finite-gamma approximant has a negative odd direction; DN10."
  INFINITE_THINNING_REPAIR: "No proof of positivity of the full averaged signed form DN20."
  OPTIONAL_STRONGER_INTERFACE: "Conditional B_half positivity is unproved and is not asserted necessary."
SCOPED_REFUTATIONS:
  - scope: THEOREM_SHAPE
    claim: "B(s,t) is positive semidefinite for mu-product-almost every conditioning pair."
    evidence: "DN8: fixed nodes (+12,-12), coefficients (1,-1), strict negative upper bound on a positive-measure box."
  - scope: THEOREM_SHAPE
    claim: "The symmetrized finite-gamma approximants are globally positive semidefinite at every sufficiently large truncation."
    evidence: "DN9-DN10: an explicit source-defined odd witness exists at every finite N."
ORIGINAL_V_NEGATIVITY_PROVED: false
ORIGINAL_Q_NEGATIVITY_PROVED: false
INDEPENDENT_REVIEW_OF_NEW_PROOFS: PENDING
LEAN_VERIFIED: false
NUMERICAL_CAMPAIGN: false
NEW_EXACT_RATIONAL_CHECK: true
PREDICTION_FATES:
  P1: CONFIRMED
  P2: CONFIRMED
  P3: CONFIRMED
  D1: CONFIRMED
  D2: CONFIRMED
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DENSITY_2026-09-11.md
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  BRANCH: rh_clean
  ACTUAL_COMMIT_HASHES_AND_PUBLICATION_STATUS: EXTERNAL_DELIVERY_RECEIPT
```

## 0. Decision and provenance

**The full sign is not proved.** The new construction uses the entire fixed gamma law, not merely its mean or scalar concavity. It produces an exact positive-part representation with shifted gamma rates. The tempting conditional-positive-kernel proof then fails on a positive-probability set of that very law. A finite-gamma positivity induction also fails at every finite truncation. An infinite thinning repair preserves the exact source and supplies a uniform double-exponential envelope, but does not yet pay the remaining signed quadratic form. [ABSTRACT][PAPER]

**Positive semidefinite**, abbreviated **PSD**, means that every finite node matrix has nonnegative quadratic value for every complex coefficient vector. Positive entries, positive densities and a positive expectation measure are different assertions. The two refutations below concern specified intermediate kernels, not the original theta kernel or the original Weil form. [ABSTRACT][PAPER]

### Source register and verification boundary

All repository shelf references in this document use SOURCE_BASE unless another commit is printed.

| Key | Repository path | Pinned Git object | What was checked here |
|---|---|---|---|
| S | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SLACK_2026-09-11.md` | `ac3504f3e44b0442fc50c95fe1a095aea57cd7dc` | Local complete 49446 bytes and SHA256 `1d658eb3d6d828d3bc651967087dabf8e2f9774d179b02c7607f25c7ffe54588` recomputed; pinned connector blob matches; transfer and obstruction arguments read where used. |
| R | `docs/routeB_bus/SLACK_INDEPENDENT_CHECK_2026-09-11.md` | `de9578084446baecfbb2a316d7bda3da817c8c01` | Read the report, controls, BP1-BP5 and acceptance receipts; pinned blob matches. The complete 37796-byte SHA256 `14e98d5544783927c54b41769714675ff2027a15e0a822bb5dabf4b069d379dc` was not independently recomputed locally. |
| P | `docs/routeB_bus/litreview/pdfs/math_9912170.pdf` | LFS pointer `188e40b0e1153f629d5fe64b71b8644e4db43c21` | Read the pointer. It specifies media SHA256 `04a444275e5522cef9a1ba9f7d1b9f20a752764d3548f9c48be6dbc055bb12ea`, 351648 bytes. Those media bytes were not acquired or rehashed here. |
| B | `docs/BATCH_PATTERNS.md` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | Read completely at the pin; matching blob metadata. No fresh complete local SHA256 computation. This is the explicitly requested non-Route-B documentation opened. |

The attachment was read completely. Both its hashes and all counts match the request lock and the connector's exact-commit object. The bootstrap was fetched from `rh_clean`, not substituted by an old attachment.

A separate publicly served arXiv `math/9912170v1` PDF was read at equations (14)-(25), Proposition 1, and the product formulas (27)-(31). Printed page 7 was also inspected as a PDF screenshot. This corroborates the probability identities; it does **not** verify byte identity with the pinned, locally recompiled PDF. Direct media acquisition failed. The missing PDF-media hash check remains an explicit provenance limitation. The inherited explicit-formula and Weil-criterion publications behind S were not freshly audited in this batch.

No old numerical diagnostic, scalar-concavity probe, eigenvalue table, finite radical projection or path-allocation campaign was rerun. The new proofs below are paper derivations awaiting independent review; a Markdown commit is not a Lean verification.

## 1. Source, controls and the exact target

This section's mathematical statements have scope [ABSTRACT][PAPER], with the published source identities retained as the named dependencies above.

Use exactly the request's positive even source

\[
 f(x)=\Phi(x)/A,\qquad A=\|\Phi\|_2>0,
\quad \Phi(x)=e^{5x/2}r(e^{2x}).
\]

The constant \(A\) is not \(I=\xi(1/2)=\int\Phi\). For the probability law of \(T\),

\[
T=\sum_{n\ge1}\frac{\Gamma_{2,n}}{\pi n^2},\quad
L_T(z)=\prod_{n\ge1}\left(1+\frac z{\pi n^2}\right)^{-2},
\quad E T=\pi/3.
\]

The variables \(\Gamma_{2,n}\) are independent shape-two, unit-rate gamma variables. Their summable means prove almost-sure convergence of this nonnegative series. The logarithmic change \(x=\tfrac12\log T\) requires the tilt \(T^{1/4}/E T^{1/4}\); its density is \(\Phi/I\), and \(E T^{1/4}=2I\). No independence statement is transported through the logarithm.

For completeness, differentiation of the fixed Laplace product gives

\[
-L_T'(z)=L_T(z)\,2\sum_{n\ge1}(z+\pi n^2)^{-1}.
\]

The sum is the Laplace transform of \(k(v)=2\sum_{n\ge1}e^{-\pi n^2v}\). Tonelli gives \(\int k=\pi/3\); uniqueness for finite measures gives \(tr(t)=(k*r)(t)\). Local integrability of \(k\), continuity of \(r\), and its limit zero at zero give pointwise equality. This rechecks BP2 without a quadrature test. Reciprocity is \(r(1/t)=t^{5/2}r(t)\).

The kernel target remains

\[
V_f(x,y)=\int_0^\infty(x+y+2v)f(x+v)f(y+v)\,dv. \tag{DN0}
\]

S's exact transfer uses \(H_2(x,y)=e^{2(x+y)}V_f(x,y)\). It retains the physical measure, both pole moments, \(c_A=\gamma+\log(8\pi)+\pi/2\), and every \(\Lambda(n)/\sqrt n\) term of the original \(Q\). The transfer is recalled in section 6, not replaced by an inverse on all of \(L^2\).

The inherited controls survive at their stated scopes. For the same \(f_c\), the polynomials in R's OC1/OC2 show both strict scalar concavities while the full odd four-node value is \(-3/1250\). The formula for \(M_c\) follows by Gaussian differentiation. The mean ratio \(M_c(3\sigma/2)/M_c(-\sigma/2)\) is continuous, equals 1 at zero and exceeds \(3/2\) at one. Since \(1<\pi/3<4/3\), the intermediate value theorem supplies a mean-matching \(0<\sigma_*<1\). Substitution in DN0 gives the exact negative value \(-3\sigma_*^2/1250\). These arguments do not depend on the reported decimal root. They refute the scalar-plus-mean implication, not a theorem using the full fixed probability law.

## 2. A new exact source relation: remove one gamma and tilt the remainder

All assertions in this section are [ABSTRACT][PAPER].

### 2.1 The shifted-rate probability measure

Separate the first gamma variable:

\[
T=G_1+U,\qquad
G_1\sim\mathrm{Gamma}(2,\text{rate }\pi),\qquad
U=\sum_{n\ge2}\frac{\Gamma_{2,n}}{\pi n^2}.
\]

The product telescopes:

\[
E e^{\pi U}=\prod_{n\ge2}(1-n^{-2})^{-2}=4.
\]

Define a probability measure \(\mu\) by exponential tilting of \(U\):

\[
\mu(ds)=\tfrac14 e^{\pi s}\Pr(U\in ds).
\]

Under this measure its coordinate \(Z\) has the law

\[
\boxed{
Z=\sum_{n\ge2}\frac{\Gamma_{2,n}}{\lambda_n},\qquad
\lambda_n=\pi(n^2-1),\qquad
m:=E_\mu Z=\frac{3}{2\pi}.}
\tag{DN1}
\]

Indeed, tilting each finite collection changes its rates from \(\pi n^2\) to \(\lambda_n\). Integrability of \(e^{\pi U}\) just proved permits passage to the infinite product. Alternatively, compute the tilted Laplace transform and use uniqueness. Finally,
\(\sum_{n\ge2}(n^2-1)^{-1}=3/4\), by partial fractions. These facts prove both the law and its finite first moment.

### 2.2 Positive-part representation, including its exact compensator

Write \(a_+=\max(a,0)\) and define

\[
h(t)=E_\mu(t-Z)_+,\qquad d(t)=E_\mu(Z-t)_+.
\]

Convolution with the first gamma density gives, for every \(t>0\),

\[
\boxed{
r(t)=4\pi^2e^{-\pi t}h(t)
=4\pi^2e^{-\pi t}\left(t-\frac{3}{2\pi}+d(t)\right).}
\tag{DN2}
\]

**Proof.** The density of \(G_1\) is \(\pi^2 t e^{-\pi t}\mathbf1_{t>0}\). Therefore its convolution with the law of \(U\) equals
\(\pi^2e^{-\pi t}E[e^{\pi U}(t-U)_+]\), which is the first formula. The identity \((t-z)_+=t-z+(z-t)_+\) gives the second. No theta term was discarded. In particular, \(d(t)\) is the complete remainder, not a fitted correction. The Laplace check is
\(L_T(z)=4\pi^2L_Z(z+\pi)/(z+\pi)^2\), with \(L_Z(\pi)=1/4\).

The function \(h\) is nonnegative, convex and 1-Lipschitz, with \(h(t)\le t\). Its second distributional derivative is \(\mu\). Reciprocity becomes the additional exact relation

\[
h(1/t)=t^{5/2}e^{\pi/t-\pi t}h(t). \tag{DN3}
\]

This construction uses the full shifted-rate product in DN1. Replacing \(h\) by an arbitrary convex function, or \(m\) by the only datum of its law, is not the construction.

### 2.3 A paid full-tail bound

Set

\[
q=5\pi/4,\qquad K=E_\mu e^{qZ}=225\pi^2/256.
\]

To check the constant, the product for this expectation is
\(\prod_{n\ge2}[(n^2-1)/(n^2-9/4)]^2\).
Euler's sine product gives \(\prod_{n\ge2}(1-9/(4n^2))=8/(15\pi)\), whereas \(\prod_{n\ge2}(1-1/n^2)=1/2\). Their squared ratio is \(K\). This is the sine version of the Euler product used in P, not a numerical evaluation.

Since \(y\le e^{qy}/(eq)\) for \(y\ge0\),

\[
0\le d(t)\le\frac{45\pi}{64e}e^{-5\pi t/4},
\]
\[
\boxed{
0\le r(t)-(4\pi^2t-6\pi)e^{-\pi t}
\le\frac{45\pi^3}{16e}e^{-9\pi t/4}.}
\tag{DN4}
\]

The lower endpoint concerns this density remainder, not the Weil form. At small \(t\), the displayed main term may be negative; the exact positive compensator in DN2 must still be kept.

## 3. Conditional kernels: the first construction fails exactly

All statements in this section are [ABSTRACT][PAPER]. The explicitly displayed node witnesses are also [FINITE_CELL][PAPER].

### 3.1 Restore evenness before testing positivity

Put

\[
C=4\pi^2/A,\quad \beta=5/2,\quad \ell=9/2,\quad
w(x)=e^{\beta x-\pi e^{2x}},
\]
\[
p_s(x)=Cw(x)(e^{2x}-s)_+,\qquad
\phi_s(x)=\tfrac12[p_s(x)+p_s(-x)],\quad s\ge0.
\]

DN2 and the actual source's evenness give

\[
\boxed{f(x)=E_\mu p_Z(x)=E_\mu\phi_Z(x).} \tag{DN5}
\]

Thus evenization is an exact decomposition of the unchanged source, not an assumption that the unsymmetrized components are even.

The following bounds hold on the whole line:

\[
0\le\phi_s(x)\le\phi_0(x)\le C e^{-\ell|x|},\qquad
|\phi_s(x)-\phi_t(x)|\le C|s-t|e^{-\beta|x|}.
\tag{DN6}
\]

For \(x\ge0\), the first bound follows from
\(e^{9x-\pi e^{2x}}\le1\); the reflected term is immediate. For the second, use the 1-Lipschitz positive-part function and \(e^{5x-\pi e^{2x}}\le1\). Both inequalities follow from \(ax e^{-2x}\le a/(2e)<\pi\), for \(a=9,5\). Also, for \(x\ge1\),
\(\phi_0(x)\ge C e^{-\ell x}/(2e)\), since \(\pi e^{-2x}<1\).

Define the symmetric cross kernel

\[
B_{s,t}(x,y)=\frac12\int_0^\infty(x+y+2v)
 [\phi_s(x+v)\phi_t(y+v)+\phi_t(x+v)\phi_s(y+v)]\,dv.
\]

Independence of two copies of \(Z\) gives the new integrated identity

\[
\boxed{V_f(x,y)=\iint B_{s,t}(x,y)\,\mu(ds)\mu(dt).} \tag{DN7}
\]

DN6 makes the integral absolutely convergent locally uniformly in the nodes and supplies Fubini even where \(x+y+2v\) is negative. The symmetrization makes each \(B_{s,t}\) real symmetric and centrosymmetric. It does not make it PSD.

Using one random variable in both factors would instead produce \(E V_{\phi_Z}\), a different kernel with a covariance term. No such replacement is used.

The unsymmetrized cross integral already displays the cutoffs that logarithmic transport creates. With \(a=e^{2x}\), \(b=e^{2y}\), it is exactly

\[
\frac{C^2e^{\beta(x+y)}}2
\int_{\max(1,s/a,t/b)}^\infty
u^{3/2}(a\nu-s)(b\nu-t)e^{-\pi(a+b)\nu}
(x+y+\log\nu)\,d\nu.
\]

For reflected components one retains the reflected positive-part factors in DN7; their cutoffs must not be replaced by this unreflected lower bound. Positivity of the factors still does not determine the sign of the logarithmic/node multiplier or of a coefficient sum.

### 3.2 A strict negative event inside the actual conditioning law

Take nodes \((a,-a)\), coefficients \((1,-1)\), first with \(s=t=0\). Evenness gives the value \(2[V_{\phi_0}(a,a)-V_{\phi_0}(a,-a)]\). DN6 gives

\[
V_{\phi_0}(a,a)\le C^2e^{-9a}\left(\frac{2a}{9}+\frac2{81}\right).
\]

For \(a>1\), restrict the cross integral to \(0\le v\le a-1\). Both absolute arguments are at least 1, so

\[
V_{\phi_0}(a,-a)\ge C^2e^{-9a}\frac{(a-1)^2}{4e^2}
> C^2e^{-9a}\frac{(a-1)^2}{36}.
\]

At \(a=12\), the cross-minus-diagonal rational margin is
\(121/36-218/81=217/324\). The odd value is at most
\(-217 C^2e^{-108}/162\).

This is not merely a measure-zero conditioning point. For \(|x|,|y|\le M\), telescoping the two products in DN7 and using DN6 gives

\[
|B_{s,t}(x,y)-B_{0,0}(x,y)|\le C^2(s+t)I_M,
\quad I_M=3M^2+4M/7+2/49.
\]

The integral defining \(I_M\) is
\(\int_0^\infty2(M+v)e^{-7(v-M)_+}dv\); thus all physical tails are included. A coefficient vector costs its squared \(\ell^1\) norm, which is 4 for this witness. Put
\(\delta=e^{-108}/10000\). Since \(I_{12}=21506/49\) and
\(217/162-8I_{12}/10000=4903639/4961250>1/2\),

\[
\boxed{
(1,-1)^*[B_{s,t}(x_i,x_j)]_{x_i=12,-12}(1,-1)
\le-\tfrac12 C^2e^{-108}<0
\quad(0\le s,t\le\delta).}
\tag{DN8}
\]

The box has positive \(\mu\otimes\mu\) measure. To prove \(\mu(0<Z<\delta)>0\), choose finitely many coordinates so that the remaining expected sum is below \(\delta/4\). Markov's inequality gives positive probability that this tail is below \(\delta/2\). Independently, all finitely many retained gamma variables can have sum below \(\delta/2\) with positive probability. Also \(Z>0\) almost surely.

**Exact refutation scope:** there is no PSD factorization of these particular \(B_{s,t}\) blocks for almost every conditioning pair. Restoring evenness does not fix that statement. Invertible diagonal congruences cannot remove its negative direction. The mean in DN7 can still be nonnegative: cancellation between conditioning pairs has not been evaluated. Continuity also permits compact smoothing of the auxiliary node witness; that is not a negative original \(Q\) test.

### 3.3 Finite-gamma positivity induction fails at every finite order

Let \(Z_N\) be DN1 truncated through \(n=N\), with \(Z_1=0\), and set
\(h_N(u)=E(u-Z_N)_+\), \(f_N=E\phi_{Z_N}\). The constant \(A\) in these definitions remains the canonical one. Write

\[
K_N=\frac{\prod_{n=2}^N\lambda_n^2}{(2N-1)!},\quad
\kappa_N=4N+\tfrac12,\quad D_N=CK_N/2.
\]

Integrating the joint exponential densities over the simplex where their sum is below \(u\) proves

\[
K_N e^{-\lambda_Nu}u^{2N-1}\le h_N(u)\le K_Nu^{2N-1},
\tag{DN9}
\]

where the lower exponential is 1 at \(N=1\). The simplex integral of \((u-\sum z_j)_+\) in \(2N-2\) variables is \(u^{2N-1}/(2N-1)!\). Thus
\(f_N(x)\sim D_Ne^{-\kappa_N|x|}\) as \(|x|\to\infty\). The other, unreflected term has a double-exponential tail.

Here is a fully specified witness without relying only on that asymptotic. Let \(L_N\) be the least positive integer satisfying

\[
\pi N^2e^{-2L_N}\le1,\quad
2\pi e^{2L_N}\ge\kappa_N+\ell,\quad
 e^{(\kappa_N+\ell)L_N-\pi e^{2L_N}}\le K_N.
\]

Such an integer exists. Monotonicity of the exponent after \(L_N\), DN9 and \(h_N(u)\le u\) give, for \(x\ge L_N\),

\[
(D_N/e)e^{-\kappa_Nx}\le f_N(x)\le2D_Ne^{-\kappa_Nx}.
\]

For \(a>L_N\), the same diagonal/cross calculation yields

\[
V_{f_N}(a,a)\le4D_N^2e^{-2\kappa_Na}
 (a/\kappa_N+1/(2\kappa_N^2)),
\]
\[
V_{f_N}(a,-a)>D_N^2e^{-2\kappa_Na}(a-L_N)^2/9.
\]

Choose \(a_N=2L_N+12\). Because \(\kappa_N\ge9/2\),

\[
\frac{(a_N-L_N)^2}{9}-\frac{4a_N}{\kappa_N}
-\frac{2}{\kappa_N^2}
\ge\frac{L_N^2+8L_N+48}{9}-\frac8{81}>0.
\]

Consequently

\[
\boxed{(1,-1)^*[V_{f_N}(x_i,x_j)]_{x_i=a_N,-a_N}(1,-1)<0
\quad\text{for every finite }N\ge1.} \tag{DN10}
\]

These are the symmetrized, source-consistent finite-gamma approximants, not arbitrary substituted densities. Indeed the finite original remainder has tilt normalization
\(E e^{\pi U_N}=4N^2/(N+1)^2\); \(f_N\) differs from the corresponding symmetrized logarithmic density divided by \(A\) by the positive scalar \((N+1)^2/N^2\). Any further positive scalar normalization preserves DN10.

This kills a global-PSD induction on those finite approximants. It does not kill a signed error bound on each fixed compact window. The witnesses depend on \(N\); section 6 proves convergence on each fixed compact without asserting uniform positivity of the approximants.

## 4. Concrete repair: keep an infinite law inside each conditioning block

All statements in this section are [ABSTRACT][PAPER].

### 4.1 Exact thinning of the shifted-rate law

For \(0<\rho<1\), take independent variables \(E_{n,j}\) exponential with rate \(\lambda_n\) and Bernoulli variables \(b_{n,j}\) with \(\Pr(b_{n,j}=1)=1-\rho\), for \(n\ge2\), \(j=1,2\). Define

\[
Y_\rho=\sum_{n\ge2}\sum_{j=1}^2 b_{n,j}E_{n,j}.
\]

The series converges almost surely and in \(L^1\), because
\(E Y_\rho=(1-\rho)m\). Its complete Laplace transform is

\[
\boxed{
L_{Y_\rho}(z)=\prod_{n\ge2}
 \left(\frac{1+\rho z/\lambda_n}{1+z/\lambda_n}\right)^2
=\frac{L_Z(z)}{L_Z(\rho z)},\quad z\ge0.}
\tag{DN11}
\]

This follows directly from
\(E e^{-z bE}=\rho+(1-\rho)\lambda/(\lambda+z)\); bounded convergence handles the infinite series. For an independent \(Z'\sim\mu\), multiplication of Laplace transforms proves

\[
\boxed{\rho Z'+Y_\rho\ \text{has law }\mu.} \tag{DN12}
\]

Thus \(P_\rho F(s)=E F(\rho s+Y_\rho)\) is a probability transition preserving \(\mu\). This is a statement about the positive additive variable, before logarithmic transport.

### 4.2 Repaired components and exact transfer

Define

\[
\phi^{\rho}_s(x)=E\phi_{\rho s+Y_\rho}(x)
=\frac C2\{w(x)H_{\rho,s}(e^{2x})+w(-x)H_{\rho,s}(e^{-2x})\},
\]
\[
H_{\rho,s}(u)=E(u-\rho s-Y_\rho)_+.
\]

The components are even, continuous and nonnegative, with
\(0\le\phi^{\rho}_s\le\phi_0\). By DN12,
\(\int\phi^{\rho}_s(x)\mu(ds)=f(x)\) exactly. Define \(B^{\rho}_{s,t}\) by the formula for \(B_{s,t}\), replacing both components by their repaired versions. Independent innovations are used in the two factors. Then

\[
\boxed{
B^{\rho}=(P_\rho\otimes P_\rho)B,\qquad
V_f=\iint B^{\rho}_{s,t}\,\mu(ds)\mu(dt).}
\tag{DN13}
\]

The first equality is an identity of kernels, not an order inequality. A positive probability transition need not turn this signed kernel family into PSD kernels. All signed cross terms and both reflected terms remain present.

### 4.3 A uniform double-exponential envelope at half thinning

Fix \(\rho=1/2\) from now on. For \(0<u\le1/(16\pi)\), put
\(N=\lfloor1/(8\pi u)\rfloor\ge2\) and \(z=\pi(N^2-1)\). For every \(2\le n\le N\), \(z/\lambda_n\ge1\), hence its factor in DN11 is at most \((3/4)^2\). The remaining factors are at most one. Markov's exponential inequality gives

\[
\Pr(Y_{1/2}\le u)\le e^{zu}(3/4)^{2(N-1)}.
\]

Since \(zu\le N/8\), \(\log(4/3)>1/4\) and \(N\ge1/(16\pi u)\),

\[
\boxed{
\Pr(Y_{1/2}\le u)\le2\exp\{-3/(128\pi u)\}.}
\tag{DN14}
\]

The factor 128 includes the loss from the floor function. No unsupplied uniform limit in the number of gamma variables is used.

Let \(c_*=3/(128\pi)\) and \(x_*=\tfrac12\log(16\pi)\). Since
\(H_{1/2,s}(u)\le u\Pr(Y_{1/2}\le u)\), the preceding estimate and the elementary bound \(H_{1/2,s}(u)\le u\) give

\[
\boxed{
\phi^{1/2}_s(x)\le\frac{3C}{2}
 e^{\ell|x|-c_*e^{2|x|}}
\quad(|x|\ge x_*,\ s\ge0).}
\tag{DN15}
\]

For \(x\ge x_*\), the unreflected term is bounded by
\((C/2)e^{\ell x-\pi e^{2x}}\), and the reflected term by
\(C e^{-\ell x-c_*e^{2x}}\). Their sum proves DN15; evenness gives the other tail.

This is a substantive repaired property: it is uniform over **all** conditioning states. In the original family, fixed positive states eventually have fast tails, but the onset is not uniform as the state tends to zero; \(\phi_0\) has an exponential tail. DN15 removes that particular obstruction uniformly. It does not prove the full conditional or averaged sign.

A finite version of the innovation has an atom at zero, of mass \(4^{-(N-1)}\). Therefore its uniform small-ball estimate cannot be DN14 down to zero. One must not obtain DN15 by discarding the infinite innovation tail and silently keeping the infinite-law conclusion.

## 5. The first unpaid inequality and a second possible representation

The exact identities and the auxiliary identity in this section are [ABSTRACT][PAPER]. All proposed positivity implications with an unpaid premise are [ABSTRACT][CONDITIONAL].

### 5.1 Entire remaining signed form after the repair

For arbitrary finite real nodes \(x_i\) and complex coefficients \(c_i\), put

\[
F_s(v)=\sum_i c_i\phi^{1/2}_s(x_i+v),\qquad
G_s(v)=\sum_i c_i x_i\phi^{1/2}_s(x_i+v).
\]

The exact conditional quadratic value is

\[
\mathcal B_{s,t}(x,c)=\int_0^\infty
\Re\{2v\overline{F_s(v)}F_t(v)
 +\overline{G_s(v)}F_t(v)+\overline{F_s(v)}G_t(v)\}\,dv.
\tag{DN16}
\]

The remaining assertion is precisely

\[
\boxed{
\forall n\ge1\ \forall x\in\mathbb R^n\ \forall c\in\mathbb C^n:
\quad\iint\mathcal B_{s,t}(x,c)\,\mu(ds)\mu(dt)\ge0.}
\tag{DN20}
\]

Equations DN1, DN11 and DN16 specify every measure, function and tail in DN20. The first term becomes \(2v|E_\mu F_s(v)|^2\) after averaging. The other two terms become the full mixed term; no sign estimate pays it here.

Requiring \(\mathcal B_{s,t}(x,c)\ge0\) for almost every pair and all node vectors is one **stronger sufficient interface**, not a necessary condition for DN20. The corresponding condition before thinning was refuted by DN8. After thinning it is unproved, not accepted. The new progress is DN2, DN8-DN10 and DN12-DN15, not the act of writing DN20 in new coordinates.

### 5.2 An integrated alternative that does not require each block to be positive

The same shifted-rate law has

\[
k_*(v)=2\sum_{n\ge2}e^{-\lambda_nv}=e^{\pi v}k(v)-2,
\qquad \nu_*(v)=2\sum_{n\ge2}\lambda_ne^{-\lambda_nv}.
\]

Both are nonnegative, and \(\int_0^\infty v\nu_*(v)dv=m\). For bounded continuously differentiable functions with bounded derivative define

\[
\mathscr A H(s)=-sH'(s)
 +\int_0^\infty[H(s+v)-H(s)]\nu_*(v)dv.
\]

This is an auxiliary jump operator on the conditioning variable, not an asserted realization of the original Weil operator. The shifted Laplace product proves the measure identity
\(s\mu(ds)=(k_*\,dv)*\mu\). Integrating it against \(H'\), and using
\(H(s+v)-H(s)=\int_0^vH'(s+a)da\), gives \(E_\mu\mathscr A H=0\). All absolute integrals are paid by \(E Z=m\) and \(\int v\nu_*=m\).

For complex \(H\) in this class, expansion gives

\[
\boxed{
-2\Re E_\mu[\overline H\,\mathscr A H]
=E_\mu\int_0^\infty|H(s+v)-H(s)|^2\nu_*(v)dv\ge0.}
\tag{DN21}
\]

The right side is integrable: near zero use the derivative bound, and at infinity use boundedness and \(\int v\nu_*<\infty\). This supplies a genuine positive auxiliary energy from the full law. **No transfer from DN16 to DN21 is proved.** Such a transfer would need an explicit coefficient-dependent function and exact compensating terms; merely naming this positive energy does not certify DN20.

## 6. All-vector budgets and the original-test transfer

The quantitative identities and limits here are [COFINAL_FAMILY][PAPER], for each fixed compact node window or fixed original test. They do not assert a sign.

### 6.1 State and physical-tail errors, for every coefficient vector

For \(|x_i|\le M\), DN6 and \(\phi^{1/2}_s\le\phi_0\) give

\[
|\mathcal B_{s,t}(x,c)|\le C^2J_M\|c\|_1^2,
\qquad J_M=3M^2+4M/9+2/81.
\]

The same bound holds for the unthinned kernels. Indeed, integrate
\(2(M+v)e^{-9(v-M)_+}\) over \(v\ge0\). No matrix size or special choice of coefficients is hidden in the bound.

If the two conditioning states are restricted to \([0,S]\), without renormalizing their measure, the omitted contribution has absolute value at most

\[
2C^2J_M K e^{-qS}\|c\|_1^2.
\]

This follows from DN4's exponential moment and the union bound for the two independent states. If the physical integral is restricted to \(0\le v\le T\), with \(T\ge M\), its omitted contribution is at most

\[
C^2e^{-9(T-M)}\left(\frac{2(M+T)}9+\frac2{81}\right)\|c\|_1^2.
\]

Thus the fully retained finite-state, finite-physical integral differs from DN20 by at most the sum

\[
\boxed{
\varepsilon_{M,S,T}\|c\|_1^2,
\quad
\varepsilon_{M,S,T}=C^2\left[
2J_MK e^{-qS}+e^{-9(T-M)}
\left(\frac{2(M+T)}9+\frac2{81}\right)\right].}
\tag{DN17}
\]

For fixed \(M\), this tends to zero as \(S,T\to\infty\). A nonnegative finite matrix at selected nodes is still not the universal finite-window inequality.

### 6.2 Gamma truncation has a bound, not a positivity theorem

Couple \(Z_N\) with \(Z\) using the same independent variables. Then

\[
d_N:=E(Z-Z_N)=\frac1\pi\left(\frac1N+\frac1{N+1}\right).
\]

The positive-part Lipschitz bound proves
\(|f_N(x)-f(x)|\le C d_N e^{-\beta|x|}\). Telescoping the products gives

\[
\boxed{
|c^*[V_{f_N}(x_i,x_j)-V_f(x_i,x_j)]c|
\le2C^2d_N I_M\|c\|_1^2.}
\tag{DN18}
\]

The complete dependence on the node window \(M\) is explicit. DN18 and DN10 coexist: fixed-window convergence does not make a finite approximant globally PSD.

For half thinning, the innovation truncated through \(n=N\) has omitted mean \(d_N/2\). Uniformly in the conditioning state, truncating that innovation changes \(\phi^{1/2}_s(x)\) by at most \(C d_Ne^{-\beta|x|}/2\), and changes the corresponding conditional quadratic form by at most \(C^2d_N I_M\|c\|_1^2\). Truncating the independent state law as well costs another \(C^2d_N I_M\|c\|_1^2\). These bounds follow from the same coupling and product telescope; they do not reuse a fixed-order derivative envelope at growing orders.

### 6.3 Compact spatial tests and the full original consumer

For a compactly supported integrable complex spatial test \(b\), supported in \([-M,M]\), the same estimates hold with \(\|c\|_1\) replaced by \(\|b\|_1\). This follows by absolute Fubini with \(|b(x)b(y)|\). For \(H_2\), use \(b(x)=e^{2x}a(x)\), so \(\|b\|_1\le e^{2M}\|a\|_1\). All tails in DN17-DN18 therefore tend to zero on each fixed compact smooth kernel test.

Continuity of the kernels and compact smoothing of point masses prove the usual equivalence between all finite-node PSD and all compact smooth kernel-test positivity. Both directions use one fixed compact neighborhood at a time. Evenness makes every kernel in DN13 centrosymmetric. Splitting a spatial test into even and odd parts gives the two kernels \(V_+\) and \(V_-\), with vanishing cross pairing. Nothing in the repair proves either complete parity form. The node zero in the even part is retained by continuity; it is not excluded by writing positive-halfline parity formulas.

For clarity, the final source transfer does not demand a bounded inverse Fourier multiplier. In S, \(q_{2,u}(x)=\mathbf1_{x\ge0}e^{-2x+iux}\) belongs to the original control space \(X\), and \(K_2(u,v)=B(q_{2,u},q_{2,v})\) is the full original source pairing. Its arithmetic formula uses both poles and every prime power. The identity with \(\xi'/\xi\) on \(\Re s=5/2\) gives the finite diagonal congruence between \(K_2\) and the Fourier kernel of \(H_2\); its diagonal factors are nonzero there by the absolutely convergent Euler product. This congruence is finite-dimensional, not a division theorem on a function space.

To reach any original \(g\in C_c^\infty(\mathbb R;\mathbb C)\), first translate its support strictly into the positive halfline. The full \(Q\) is translation invariant, including the cancelling exponential factors of its two pole moments. Put \(G(u)=\int e^{2x}g(x)e^{-iux}dx\), which is Schwartz for this shifted test. Fourier inversion gives
\(g=(2\pi)^{-1}\int G(u)q_{2,u}\,du\) in \(X\). S's bound \(\|q_{2,u}\|_X\le\sqrt6\sqrt{1+u^2}\) pays the tail by an integrable Schwartz majorant; continuity in \(u\) pays the finite Riemann sums. Finally \(|B(g,h)|\le(|c_A|+14)\|g\|_X\|h\|_X\) pays the quadratic limit. The spatial/Fourier kernel passage uses S's Schwartz bound for \(H_2\), derived from the actual theta envelope. These are exactly the limits used here.

Consequently a proof of DN20 would give the original unconditional all-test sign. Without that proof the transfer remains a correct implication, not a completed conclusion. The derivative/translate radical family and S's retained slack identity remain unchanged because DN5 and DN13 are exact identities for the same \(f\). No individual conditional component is declared an original-source radical, and no \(L^2\)-continuous positive-square representation of \(Q\) is asserted.

## 7. Discriminator, route comparison and prediction scores

### One new decisive test

**HALF_THINNED_CONDITIONAL_ODD_MINOR** tests the stronger conditional-PSD repair, not the already tested canonical scalar inequalities. Use the exact infinite law DN11 at \(\rho=1/2\), and let \(\varphi=\phi^{1/2}_0\). Form

\[
M_{ij}=V_\varphi(i,j)-V_\varphi(i,-j),\qquad i,j\in\{1,2\},
\quad D=M_{11}M_{22}-M_{12}^2.
\tag{DN22}
\]

The observable is this full odd two-by-two minor, including all cross terms. A rigorous upper bound \(U(D)<0\), or a strict negative upper bound for an explicit rational quadratic vector, refutes the conditional-PSD repair. Continuity in both conditioning states then extends that failure to a positive-measure neighborhood, as in DN8. It would not refute the averaged DN20.

A finite-cell pass requires nonnegative lower bounds for both diagonal entries and the determinant; it certifies only this matrix. A zero-containing enclosure is **INCONCLUSIVE**, with DN22 itself the named discriminating functional. Do not classify it as equality or positivity. Use an analytic expression or a single bounded, fully budgeted integral evaluation with DN17-DN18; stop at a strict witness, a finite-cell certificate, or an unresolved enclosure. Do not automatically enlarge the node set, window, precision campaign or gamma order. This test was not run in this adjudication.

### Two candidate representations and their costs

The estimates below rank mathematical work, not probabilities of proof correctness. [ABSTRACT][CONDITIONAL]

| Candidate | Exact remaining obligation | Kill-power / initial cost | Principal risk |
|---|---|---|---|
| Infinite half-thinned cross kernels, DN13 | Prove their full PSD as a sufficient interface, or retain their signed average DN20 | 8/10 / 3/10 for DN22; full proof cost 9/10 | Fast tails and positive transitions do not control the node-weighted mixed term. |
| Stationary jump-energy representation, DN21 | Construct an exact transfer of DN16 to this energy with every compensator paid | 9/10 / 6/10 for the transfer audit | A positive auxiliary energy may represent a different functional. |

The first is selected for the single bounded discriminator. The second is an unexecuted alternative; it is not a second directive.

### Frozen and newly registered predictions

| Prediction | Fate | Exact reason |
|---|---|---|
| P1, .95 | CONFIRMED | Section 1 rechecks the tilt, BP2 and the exact IVT/scaling argument for BP3b. This score does not certify the missing PDF-media hash. |
| P2, .90 | CONFIRMED | The same two-concavity, reciprocal, mean-matched control still has the strict negative odd value in section 1. DN1 uses the full law instead. |
| P3, .70 | CONFIRMED | DN2, DN8-DN10 and the concrete DN11-DN15 repair supply new relations and scoped obstructions; DN20 is still unpaid. |
| D1, .90, registered in this chat before the construction tests | CONFIRMED | DN1-DN2 give the positive-part expectation and the exact shifted rates. |
| D2, .80, registered in this chat before the construction tests | CONFIRMED | DN8 gives a strict negative upper bound on a positive-measure set even after evenization. |

The finite-gamma obstruction DN10 was an additional analytic consequence, not a retroactively registered prediction. No diagnostic decimal has been promoted to an interval claim.

## 8. Dependency epistemics, directive and closeout

**Downstream consumer:** original \(Q(g)\ge0\) for every complex compact smooth \(g\), followed by the inherited published Weil criterion. **Actual requirement:** DN20, equivalently the full PSD of \(V_f\), with the exact transfer of section 6. [ABSTRACT][CONDITIONAL for the unpaid sign]

**Original requested object:** a full-law factorization or inequality paying that sign. **Proposed conditional-block object:** NOT_NECESSARY; it is sufficient only. A weaker admissible interface is the signed average DN20, or universal truncated signed lower bounds whose errors in DN17-DN18 tend to zero on each fixed compact test. **Failure type after repair:** NO_DERIVATION. **Epistemic status:** RESEARCH_DEBT. **Reopen trigger:** an exact DN16-to-positive-energy identity, or a proved all-vector lower estimate for DN20 with its full tails. **Novelty axis:** first-gamma removal, actual-law conditional obstruction, and infinite thinning before the logarithmic transport. No novelty relative to all literature is claimed.

For the two refuted statements the epistemic status is MATHEMATICALLY_DEAD at THEOREM_SHAPE scope, with evidence DN8 and DN10. Neither statement was proved necessary for the consumer; ROUTE_FAMILY death is therefore not asserted.

**Single Codex directive:** adjudicate DN22 for the exact half-thinned conditional source, with all gamma and physical-tail errors recorded. First check DN1-DN18 and their normalizations on paper; do not build a new framework. Return the observable, exact or interval enclosure, any rational negative coefficient witness, the error budget, and the limited conclusion. No old probe or numerical campaign is reopened. A positive finite result leaves the universal sign open. The independent review of the present paper is a validation handoff, not an assertion that such review already occurred.

**Closeout.** The full-law input now supplies a concrete positive-part source formula and a repaired infinite conditioning law. The conditional positivity claim and global finite-gamma PSD induction are refuted. They must not be retried by increasing a finite truncation or hiding the log cutoffs. The smallest unpaid consumer inequality is DN20; the cheapest new mechanism discriminator is DN22. The source-media verification gap is separate and remains open. [ABSTRACT][PAPER for the proved scope; CONDITIONAL for the sign]

```yaml
iteration:
  target: GOAL058_THETA_PROBABILITY_DENSITY_FULL_FORM_SIGN
  status: PROGRESS
  progress_class: FALSIFICATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: conditional_PSD_and_global_finite_gamma_PSD_induction
  new_gap_name: DN20_INFINITE_THINNING_AVERAGED_NODE_WEIGHTED_SIGN
  invariant_learned: full_law_and_evenness_survive_only_with_independent_cross_terms_and_complete_infinite_innovations
  forbidden_future_move: promote_additive_density_positivity_or_finite_gamma_PSD_to_logarithmic_full_form_sign
  next_decisive_test: HALF_THINNED_CONDITIONAL_ODD_MINOR
  route_score: 4
  route_death_claimed: false
```

### Publication and verification handoff

Only EXPECTED_VERDICT_PATH is written. No Lean source, state, queue, registry, old verdict or RH-claim file is changed. The actual commit, parent, changed-path set, bytes, LF count, SHA256, Git blob and remote publication result belong to the external delivery receipt. No Lean build command or axiom profile is fabricated for a paper-only document. Independent checking should prioritize the factor 4 in DN2, the positive-measure extension in DN8, the finite-gamma scales in DN9-DN10, the infinite product and floor-function constant in DN14, and all-vector convergence in DN17-DN18.

## 9. PROSHKA'S OWN LINE

The useful new datum is the complete probability law, not the word probability.
Removing the first gamma makes that law directly interact with a positive-part function.
The exponential tilt is essential; leaving its normalization implicit loses a factor four.
The remaining rates are shifted by one square, not by a fitted parameter.
That representation exposes where a positive mixture can still contain negative quadratic blocks.
I tested those blocks after restoring evenness, not before.
The negative conditioning event belongs to the actual law used in the decomposition.
That makes it a sharper obstruction than importing another unrelated control density.
It does not make the expectation negative.
The finite-gamma obstruction is different and should be recorded separately.
Every finite truncation has the wrong ultimate tail for global kernel positivity.
Its negative witness can move out while the approximation improves on each fixed compact.
I did not choose additive total positivity as the main argument.
Its minors do not automatically survive the logarithm and the node-dependent cutoff.
I also did not choose a new scalar concavity condition.
The supplied controls have already demonstrated the weakness of that interface.
The first move beyond this batch is to test the half-thinned conditional odd minor.
A strict negative minor would end that conditional-positivity repair, not the averaged problem.
The second move is to seek a coupling to the stationary jump energy.
A mismatched cross term would end that proposed transfer before any formalization.
The infinite innovation is not decorative in the first move.
It supplies a uniform small-ball estimate that finite innovations cannot have.
I would ask for the exact pinned PDF media bytes as a readable attachment.
That would settle an authentication gap, not manufacture a missing sign estimate.
What surprised me is that first-gamma removal gives a positive full remainder so directly.
What I distrust is replacing independent cross terms by a shared random parameter.
That replacement adds a covariance without permission.
The remaining sign must be earned on the complete averaged form.

## 10. RESEARCH LOG

### Sources consulted

**READ, exact connector:** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`; judging and publication requirements, not an analytic premise.

**READ, complete attachment and exact connector:** DENSITY request at `122076a3430251d8f1f9b0cd0577938456eaaed2`, blob `ffeb152da44d1b1b89917f2921b287f80e3fb4a0`; both hashes and byte/LF counts recomputed. Its full law and unchanged consumer define this task.

**READ, local verified bytes and pinned metadata:** S at SOURCE_BASE, SL1-SL14, SL3, SL16-SL20 and relevant convergence arguments; exact original-source transfer, control topology and the restriction against an unproved global inverse. The current task does not rerun its historical diagnostics.

**READ, pinned connector text:** R at SOURCE_BASE, source audit, OD1, OC1/OC2 and BP1-BP5 with later acceptance receipts; the controls, mean-matched scaling and fixed-law transfer. Its complete local SHA256 recomputation was not completed.

**READ, pointer only:** P at SOURCE_BASE, LFS blob `188e40b0e1153f629d5fe64b71b8644e4db43c21`; the named media SHA256 and size were extracted, not independently verified as PDF bytes.

**READ, external corroboration, not authenticated pinned media:** Biane, Pitman and Yor, *Probability laws related to the Jacobi theta and Riemann zeta functions, and Brownian excursions*, `https://arxiv.org/pdf/math/9912170v1`, equations (14)-(25), Proposition 1, and (27)-(31); printed page 7 also checked as a screenshot. The gamma-series/product facts were used; later probabilistic characterizations were not imported. No whole-paper audit or publisher-edition substitution is claimed.

**READ, complete:** `docs/BATCH_PATTERNS.md` at SOURCE_BASE, blob `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b`; scope and mandatory sections 9/10. No fresh complete local SHA256 check.

**RELAY only:** the original explicit-formula/Weil-criterion sources behind S, and original sources behind R's cited scalar theorems. Their historical receipts were not presented as fresh source verification.

**FAILED acquisition:** direct raw/media retrieval of repository sources and the pinned PDF; container DNS/download failures and the media access failure produced no authenticated pinned PDF. The public arXiv reading remained a separate source.

### Branches tried and abandoned or left unpaid

Positive conditional blocks after first-gamma removal: abandoned as a universal sufficient theorem by DN8, including evenization and a positive-measure state box.

Global PSD induction on symmetrized finite gamma sums: abandoned by DN9-DN10; every finite order has an explicit far odd witness.

Additive total positivity transported without a new logarithmic theorem: not admitted; the displayed node-dependent cutoff and mixed multiplier are not an additive-translation minor. No general impossibility theorem for all total-positivity methods is claimed.

A shared latent variable in both source factors: rejected as an identity substitution; it gives an extra covariance instead of DN7.

Infinite half thinning: retained as an exact repaired representation with DN15, but conditional and averaged signs remain unpaid.

Stationary jump-square factorization: retained only as an alternative requiring an exact transfer; DN21 alone is not a proof of DN20.

### Reusable intermediate results

DN2 isolates a positive complete compensator to the first theta exponential, with DN4's explicit tail budget.

DN8 is a source-law conditioning counterexample, not merely a scalar-concavity counterexample.

DN9-DN10 show why finite-gamma approximation and global PSD cannot be interchanged; DN18 still supplies fixed-test convergence.

DN11-DN15 supply a full-law-preserving transition and a uniform double-exponential envelope before any assertion about coefficient signs.

DN17-DN18 quantify every-vector truncation errors. The fresh rational arithmetic check was `I_12=21506/49` and `217/162-8*I_12/10000=4903639/4961250>1/2`; no numerical source test was run.
