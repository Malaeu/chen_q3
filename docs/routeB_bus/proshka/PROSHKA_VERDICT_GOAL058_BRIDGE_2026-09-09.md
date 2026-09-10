# Ы — BRIDGE: exact cancellation losses and the remaining saturation estimate

```yaml
REQUEST_ID: REQ-2026-09-09-BRIDGE
RESULT: IRREDUCIBLE_ATOM
VERIFIER: PAPER
PX_RH_CLAIM: NOT_MADE
BOUNDARY_ID: GOAL058_RADICAL_TRIAL_SCHUR_T_SQUARED_SUPPLIER
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_COMMIT: b968f9443d5491778ab5e65c75c4ad7d64ba0b14
REQUEST_BLOB: 3fffbc70ca538cf86959b348890f4a4966b3515f
REQUEST_SHA256: cee5ce05956d744b2e3c3d4275c9c510990bb25d0745bb2ad349b5728219fce8
REQUEST_BYTES: 9774
REQUEST_LINES: 83
SOURCE_BASE: 952bb52113fe3ff6881c905e7c8557846cfe96df
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BRIDGE_2026-09-09.md
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
SOLE_RETAINED_ATOM: UNIFORM_FULL_SOURCE_RECOVERY_SATURATION
COFINAL_RATE_PROVED: false
RATE_WITNESSES_PRODUCED: false
THETA_REVERSE_IMPLICATION: UNRESOLVED
LOWER_SIGN_SUPPLIER: NOT_PRODUCED
SHELF_SHA256_AND_GIT_BLOB_CHECKS: ALL_FIVE_MATCH
NEW_NUMERICAL_PROBE: NOT_RUN
LEAN_GATE: NOT_RUN
AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
REPOSITORY_COMMIT_STATUS: COMMITTED_TO_RH_CLEAN_VIA_GITHUB_CONTENTS_API
PUSH_STATUS: REMOTE_BRANCH_UPDATED_DIRECTLY_NO_SEPARATE_CLI_PUSH
COMMIT_ID_AND_ARTIFACT_HASH: EXTERNAL_DELIVERY_RECEIPT
```

## 0. Decision, source integrity and scope

**S15 implies the strong budget for its own reference minimizer. On positive signed blocks this implies S26b and then S26. No reverse implication is established for the theta family.** The precise loss is the sum of a coefficient-choice error and a positive-majorant slack. Neither is paid by finite invertibility. Section 2 gives their exact identity, not a comparison of different numerical functionals.

There is also a new source-specific calculation in this verdict:
\[
Q[t_a]=(2a+O(1))\|t_a\|_2^2\qquad(a\longrightarrow\infty). \tag{B0}
\]
Section 4 proves this for the full signed form, including all prime powers and both poles. Thus the uncorrected source really has one factor of T, not two. The missing signed estimate is recovery of that energy to relative accuracy of order \(e^{\nu a}T(a)/a\). This calculation is a paper proof, not an interval experiment or a claim about the window's lowest eigenvalue.

The single retained atom is a uniform bound for the unrecovered energy after allowing all finite exact source shells. Because the request puts no growth or regularity restriction on m(a), this atom is equivalent to the existence of the requested signed supplier, with a harmless factor-two enlargement of M. Its proof remains missing. No claim of metamathematical irreducibility is made.

### 0.1 Byte checks

The authoritative request was fetched at its specified commit. The attached bytes were hashed independently; their SHA-256, Git object hash, size and line count match the request binding and the fetched blob. All five shelf files were fetched at SOURCE_BASE, reconstructed as UTF-8 bytes, and independently checked with both SHA-256 and the Git blob hash \(\operatorname{SHA1}(\texttt{blob <length>\0}\Vert\text{bytes})\). Every file has a final LF. All checks below match, not merely their prefixes.

| Key | Exact repository path | SHA-256 | Git blob | Bytes / lines |
|---|---|---|---|---:|
| S | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCHUR_2026-09-09.md` | `7717cb8106b543339909d734f0128f2e45d3d8df33bf384ff0c2476fa4e38cab` | `84c1ae8791f5124cf676426cfc927898e052d61e` | 58293 / 795 |
| I | `docs/routeB_bus/SCHUR_INDEPENDENT_CHECK_2026-09-09.md` | `b4f643aa4e253c0beefc2c7d992621bd9ecdfc852e362bad3039610546cccb7f` | `7f8e725913a097df48e24d48e781f760bfe9a8c9` | 35580 / 485 |
| R | `docs/routeB_bus/RADICAL_SHELL_STABILITY_2026-09-09.md` | `81b2cfdb8fa2fa15a0968e85d36b76f27f8e2990f975083280b4c2044ef19758` | `fa696f6159e5472a21cfa754a3570e279585af52` | 23029 / 192 |
| Q | `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SCHUR_2026-09-09.txt` | `4c082be285b9d38df78d8e9ef50771798db1469492ed0ab22602ab7520ab418f` | `2b3dab1d1eb6cda458bb0d12a96cf8209660f271` | 13296 / 89 |
| B | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | 11341 / 79 |

These sources were read in full. Their prior arguments were rechecked where used, not accepted as axioms. Hashing I does not reproduce its historical computations. Hashing R does not rerun its Arb certificates or validate the companion JSON, which was not fetched in this batch. Reported finite enclosures below retain that provenance.

**Version limitation remains visible.** The independent report I used checked Suzuki's local **2606.09096v1**, dated June 9, 2026, according to that report; I did not personally open that local PDF. My separate web reading was the HTML served at `https://arxiv.org/html/2606.09096v1`, introduction and (3.1). Its header says v1 / June 8, while its body says “Version of August 24, 2026.” I therefore do not identify that HTML byte-for-byte with I's June PDF or with S's cited v2. Only the displayed functional and explicit formula are cross-checked. No cofinal theorem is imported from it. Current DLMF HTML equations 25.4.4 and 20.7.32 were read; no historical release identity is inferred from the current pages.

## 1. Frozen source and foundation recheck

All statements in Sections 1–3 concern every real a>0 and every integer m>=0, unless a condition is stated. Pairings are **antilinear in the first argument**. The space remains
\[
E=\{f:\mathcal W[f]+\mathcal D[f]<\infty\},\quad
\mathcal W[f]=\int e^{2|x|}|f(x)|^2dx,
\]
\[
\mathcal D(f,g)=\int_0^\infty A_0(u)\langle U_uf-f,U_ug-g\rangle du,
\quad A_0(u)=\frac{e^{-u/2}}{1-e^{-2u}},\quad U_ug(x)=g(x-u).
\]
The full form is
\[
\begin{aligned}
Q(f,g)={}&\mathcal D(f,g)-c_A\langle f,g\rangle\\
&-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 \{\langle f,U_{\log n}g\rangle+\langle f,U_{-\log n}g\rangle\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),
\end{aligned}
\]
where \(c_A=\gamma_E+\log(8\pi)+\pi/2\) and \(M_\pm(f)=\int f(x)e^{\pm x/2}dx\). Every prime power remains present through the von Mangoldt function Λ. No pole-null restriction is imposed.

The source is exactly
\[
\Phi(x)=\sum_{n\ge1}
(2\pi^2n^4e^{9x/2}-3\pi n^2e^{5x/2})e^{-\pi n^2e^{2x}}.
\]
Write \(I=\|\Phi\|_2^2\), \(t=t_a=1_{|x|>a}\Phi\), \(L=\|t\|_2^2=IT\), \(N^2=N_a^2=I(1-T)\), and \(p=1_{(-a,a)}\Phi/N\). Thus T is a mass fraction, not a tail norm. In particular \(0<T<1\) and \(N>0\).

For \(g_k=(\partial_x^2-1/4)\partial_x^k\Phi\), retain exactly
\[
\alpha_j=N^{-2}\int_{-a}^a\Phi g_{2j},\quad
h_j=g_{2j}-\alpha_j\Phi,\quad d_j=1_{(-a,a)}h_j,\quad e_j=1_{|x|>a}h_j.
\]
Then \(S_{m,a}=\operatorname{span}(d_0,\ldots,d_m)\). No rounded or normalized Legendre direction replaces a d_j.

Here are the foundation proofs used, with their source locators [S, S1–S10; I, foundational extension]. Weighted Cauchy–Schwarz gives
\( |\langle f,U_ug\rangle|\le e^{-|u|}\sqrt{\mathcal W[f]\mathcal W[g]}\) and \(|M_\pm(f)|\le\sqrt{4/3}\sqrt{\mathcal W[f]}\). Using \(c_A<7\) and \(\sum_{n\ge2}\log(n)n^{-3/2}<6\) yields
\[
|Q(f,g)|\le22\|f\|_E\|g\|_E. \tag{B1}
\]
Direct Mellin integration gives \(F_\Phi(z)=\xi(1/2+z)/2\) with standard ξ normalization. Theta inversion gives evenness and double-exponential decay of each fixed derivative. Integration by parts gives
\(F_{g_k}(z)=(z^2-1/4)(-z)^kF_\Phi(z)\). The signed explicit formula against a compact smooth second argument consequently gives zero pairings for Φ and every g_k. To extend them, strip evaluation is bounded by \(\sqrt{4/3}\|f\|_E\), a compact smooth transform decays cubically on vertical lines, and the unconditional zero count is \(O(R\log(2+R))\). Smooth cutoffs and mollification are dense in E: the cutoff commutator is bounded by \(\|f\|_2^2\min(C^2u^2,4)\) in the Dirichlet integral. B1 then extends the radical identities to every second argument in E. This does not assert absolute convergence of the zero sum for every pair in E x E.

For a finite smooth radical combination v, the sharp-cut translation difference obeys
\[
\|U_u(1_{\rm out}v)-1_{\rm out}v\|_2^2
\le3u^2\|1_{\rm out}v'\|_2^2+3u(|v(a)|^2+|v(-a)|^2).
\]
The corresponding inside estimate and an inward taper with E-error squared \(O(\eta(1+|\log\eta|))\) put the cut in \(V_a\), the E-closure of \(C_c^\infty(-a,a)\). These are fixed-function estimates, not growing-degree estimates. Subtracting α_jΦ before cutting preserves global radical membership and gives \(\langle p,d_j\rangle=0\).

Finally, vanishing of a finite h-combination on either open tail or inside interval extends analytically to the line. Its Laplace transform gives
\[
(z^2-1/4)\sum_j c_jz^{2j}-\sum_jc_j\alpha_j=0.
\]
At z=1/2 the constant sum is zero, and then every c_j is zero. Hence the physical Gram matrix G is positive definite. The same argument proves positivity of the reference Gram H. It does not prove positivity of the signed Gram C.

## 2. Exact loss decomposition and all finite branches

**Type: LEAN-READY finite identities, proved below, with the stated analytic inputs.** “LEAN-READY” here does not claim a compiled Lean file.

For any \(c\in\mathbb C^{m+1}\), define
\[
v_c=\Phi-N\sum_jc_jh_j,\quad w_c=1_{\rm out}v_c=t-N\sum_jc_je_j,
\quad f_c=1_{\rm in}v_c/N=p-\sum_jc_jd_j.
\]
The vector v_c is globally radical. Since \(v_c=Nf_c+w_c\), expansion against each summand gives equality of the two cut energies. With
\[
C_{ij}=Q(e_i,e_j)=Q(d_i,d_j),\quad s_i=Q(e_i,t),\quad \tau=Q[t],
\]
this proves
\[
N^2Q[f_c]=Q[w_c]=\tau-2N\Re(c^*s)+N^2c^*Cc,
\quad \|f_c\|_2^2=1+c^*Gc. \tag{B2}
\]
The affine budget is \(Q[f_c]\le\epsilon\), not \(Q[f_c]\le\epsilon\|f_c\|_2^2\).

### 2.1 Positive reference and its slack

Keep precisely S9's positive tail form
\[
\mathfrak B_a[v]=\int_{|x|>a}\!
[(e^{2|x|}+16a+16)|v|^2+3e^{-4a}|v'|^2]dx
+6e^{-2a}(|v(a)|^2+|v(-a)|^2).
\]
Splitting the translation integral at \(e^{-2a}\) and 1 proves
\(\|1_{\rm out}v\|_E^2\le\mathfrak B_a[v]\); B1 then gives \(|Q[1_{\rm out}v]|\le22\mathfrak B_a[v]\). For \(u=(\Phi,g_0,\ldots,g_{2m})\), retain H, ell and Z of S11. Weighted Cauchy–Schwarz proves
\[
\min_{\ell^*\theta=1}\theta^*H\theta=1/Z,
\quad \theta_B=H^{-1}\ell/Z,
\quad c_{B,j}=-(\theta_B)_{j+1}/N. \tag{B3}
\]
Let \(K^B_{ij}=\mathfrak B_a(h_i,h_j)\). Expanding the positive quadratic form at its constrained minimizer gives the further exact identity
\[
\mathfrak B_a[v_c]=1/Z+N^2(c-c_B)^*K^B(c-c_B). \tag{B4}
\]
Indeed, c parametrizes every coefficient vector with \(\ell^*\theta=1\), and the first variation vanishes at c_B. Here \(K^B>0\) by the same exterior independence proof. The available matrix comparison is only
\(-22K^B\preceq C\preceq22K^B\). It is an upper domination, not a coercive lower comparison.

Define, in **unnormalized tail-energy units**,
\[
\beta_{m,a}=22/Z_{m,a},\qquad
\mathcal L_c=22\mathfrak B_a[v_c]-Q[w_c]\ge0.
\]
Its exact two-part decomposition is
\[
\mathcal L_c=
22(\mathfrak B_a[v_c]-\|w_c\|_E^2)
+(22\|w_c\|_E^2-Q[w_c]). \tag{B5}
\]
Both displayed summands are nonnegative. The first is slack in the tail/trace estimator. The second is slack in absolute domination of the signed form. It retains, rather than omits, all arithmetic and pole terms. Explicitly, writing \(P[w]\) for the full prime-power contribution with positive coefficient in \(Q=\mathcal D-c_A\|\cdot\|_2^2-P+R_{\rm pole}\), the second summand equals
\(22\mathcal W[w]+21\mathcal D[w]+c_A\|w\|_2^2+P[w]-R_{\rm pole}[w]\).
The total is nonnegative; its individual source pieces need not be.

### 2.2 Signed minimizer and the exact bridge

If \(C>0\), completing the C-square in B2 proves
\[
c_Q=C^{-1}s/N,\quad \delta=\tau-s^*C^{-1}s,
\quad Q[w_c]=\delta+N^2(c-c_Q)^*C(c-c_Q).
\]
Put \(\mathcal A_{m,a}=N^2(c_B-c_Q)^*C(c_B-c_Q)\ge0\). Then
\[
\boxed{\beta=\delta+\mathcal A+\mathcal L_B,\qquad
Q[w_B]=\delta+\mathcal A=\beta-\mathcal L_B.} \tag{B6}
\]
This is the requested bridge. The coefficient mismatch \(\mathcal A\) and the majorant slack \(\mathcal L_B\) are different nonnegative quantities. Computing either inverse does not bound either loss uniformly. Border elimination also gives \(\det\bigl(\begin{smallmatrix}\tau&s^*\\s&C\end{smallmatrix}\bigr)=\det(C)\delta\), with its usual positive-block hypothesis.

### 2.3 Negative and singular windows

Define the extended finite recovered energy
\[
\mathcal R_{m,a}=\sup_c\{2N\Re(c^*s)-N^2c^*Cc\}.
\]
There are exactly these cases:

| Condition on the actual finite source block | Recovered energy | Strong affine consequence |
|---|---|---|
| C has a negative direction | \(+\infty\) | Scaling a phase-adjusted negative direction gives any finite upper budget. |
| \(C\succeq0\), \(s\notin\operatorname{ran}C\) | \(+\infty\) | A kernel direction with nonzero coupling gives linear unbounded recovery. |
| \(C\succeq0\), \(s\in\operatorname{ran}C\) | \(s^*C^\dagger s\) | The minimum is \(\delta^\dagger=\tau-s^*C^\dagger s\); the budget still must be checked. |

Here **Moore–Penrose inverse** \(C^\dagger\) means inversion on the range and zero on the kernel. In the last case,
\[
Q[w_c]=\delta^\dagger+N^2(c-C^\dagger s/N)^*C(c-C^\dagger s/N). \tag{B7}
\]
Proof: diagonalize the finite Hermitian matrix. A negative eigenvalue gives a negative quadratic leading term in B2. A coupled zero eigenvalue gives a nonconstant linear term. In the remaining case each positive coordinate completes a square, and zero coordinates contribute nothing. Thus B6 extends to this bounded singular case using B7; the value of \(\mathcal A\) is independent of the minimizing kernel component.

The decoupled-null obstruction is retained exactly: \(Q[x]=|x_0-x_2|^2\), \(\Phi=e_0+e_2\), \(p=e_0\), \(d=e_1\) give \(C=s=0\), \(\tau=N=1\). At \(\epsilon=1/2\), every strong margin is -1/2. A null direction supplies no recovery. This is the abstract control in S3.4, not a theta counterexample.

## 3. Implication diagram, necessity and reverse comparisons

Fix a,m and a tail budget \(K=\epsilon N^2>0\). On \(C>0\), B6 gives the exact diagram
\[
\begin{array}{ccccc}
\mathrm{S15}:\ \beta\le K
&\Longrightarrow&
\mathrm{S26b}:\ \beta-\mathcal L_B=\delta+\mathcal A\le K
&\Longrightarrow&
\mathrm{S26}:\ \beta-\mathcal L_B-\mathcal A=\delta\le K\\
&&\Updownarrow&&\Updownarrow\\
&&Q[f_B]\le\epsilon&&\exists c\in\mathbb C^{m+1}:Q[f_c]\le\epsilon.
\end{array} \tag{B8}
\]
S15 implies the actual c_B budget on **all** windows, without C>0. B7 gives the bounded singular extension. The negative/coupled-null cases are handled by scaling, not by forcing an inverse. A statement of S26 only on positive windows is not, by itself, a complete supplier: it says nothing about a decoupled-null window unless that window's B7 budget is also supplied.

Applying the pointwise arrows with the same \(M,\nu,a_*,m(a)\) proves the corresponding cofinal forward implications. The reverse implications remain **unknown on the actual theta family**, both at prescribed schedules and when existential witnesses may change. Numerical inefficiency does not prove strict logical strength between those theta assertions.

For a possibly enlarged budget K', the exact missing reverse comparisons are:
\[
\begin{array}{ll}
\mathrm{S26}\to\mathrm{S26b}:&\mathcal A\le K'-\delta,\\
\mathrm{S26b}\to\mathrm{S15}:&\mathcal L_B\le K'-Q[w_B],\\
\mathrm{S26}\to\mathrm{S15}:&\mathcal A+\mathcal L_B\le K'-\delta.
\end{array} \tag{B9}
\]
These are necessary and sufficient for the corresponding conclusion at that particular window and K'. To make a cofinal reverse reduction they need a uniform estimate along a source schedule. They are not new assumptions admitted into this verdict. In particular, bounding \((\mathcal A+\mathcal L_B)/\delta\) is not a legitimate general formulation: δ may be zero or negative. A sufficient, but unproved, additive comparison would be
\(\beta\le A_0\max(\delta,0)+B_0e^{\mu a}T^2N^2\), with constants independent of a and m on the chosen schedule. The shelf supplies no such comparison.

### 3.1 Abstract countermodels: scope of the nonreverse result

The following examples disprove reversal from the finite algebra and domination alone. They do **not** disprove a theta theorem. For \(0<T\le1/2\), take orthonormal inside vectors p,d_j and outside vectors q,e_j. Set \(N=\sqrt{1-T}\), \(\sigma=\sqrt T\), \(\Phi=Np+\sigma q\), \(h_j=d_j+e_j\), \(t=\sigma q\), \(\alpha_j=0\). Set the abstract g_{2j}=h_j and use the exterior Euclidean norm squared as \(\mathfrak B\). Thus \(H=\operatorname{diag}(T,1,\ldots)\), \(\ell=(1,0,\ldots)\), \(\beta=22T\), and \(c_B=0\).

First take
\[
Q_1[x]=|x_q+x_{e_0}-(\sigma/N)x_p-x_{d_0}|^2
+\sum_{j\ge1}|x_{e_j}-x_{d_j}|^2.
\]
On each finite shell \(C=I\), \(s=(\sigma,0,\ldots)\), \(\tau=T\), \(\delta=0\), \(\mathcal A=T\), \(\mathcal L_B=21T\). Hence the signed optimum meets every positive budget, while the reference candidate need not. Second take
\[
Q_2[x]=T|x_q-(\sigma/N)x_p|^2+\sum_{j\ge0}|x_{e_j}-x_{d_j}|^2.
\]
Now \(C=I\), \(s=0\), \(\tau=\delta=T^2\), \(c_Q=c_B=0\), \(\mathcal A=0\), and \(\mathcal L_B=22T-T^2\). The reference candidate itself meets \(Q[f_B]\le2T^2\), although its reference bound is \(22T/(1-T)\).

Both examples have globally radical Φ and h_j, exact physical orthogonality, the specified mass-fraction identity, positive physical and reference Grams, all the finite tail identities, and domination by 22 times the Euclidean E norm squared. Indeed the full operator norm of Q_1 is at most 4 for T<=1/2, and that of Q_2 is at most 2; on outside vectors the same domination holds. Increasing m merely adds decoupled coordinates. Setting \(T(a)=\exp(-2\pi e^{2a})\) shows that finite-algebraic families can have cofinal nonreversal even after changing M and ν.

**Missing theta structure is explicit:** these are parameterized abstract forms, not one fixed arithmetic Q and one fixed theta Φ. They lack S1's weighted translation domain, the prime-power and pole functional, the Mellin identity, the derivative relation \(g_{2j}=(\partial^2-1/4)\partial^{2j}\Phi\), actual theta projection integrals, and the nested physical cut geometry. The chosen T(a) is only a parameter, not a theta integral. Thus they establish abstract nonnecessity, while theta necessity remains unresolved.

## 4. A source-compatible obstruction: the uncorrected tail has scale aT

**Type: THEOREM, new paper proof in this section; not a finite identity or a Lean verification.** There exists an absolute constant C_0>0 such that
\[
\forall a\ge1:\qquad
|Q[t_a]-2a\|t_a\|_2^2|\le C_0\|t_a\|_2^2. \tag{B10}
\]
Only the fixed theta source and the full Q of Section 1 are used. In this section every O-constant is independent of a. No estimate here is asserted uniformly for arbitrary growing-degree radical combinations.

### 4.1 A uniform pointwise tail envelope

Put \(Y=e^{2a}\), \(k_0=2\pi^2-3\pi>0\), and \(\kappa=2\pi-9/2>0\). For y=e^{2x}>=1, positivity of each theta summand and a geometric bound on \(\sum n^4e^{-\pi(n^2-1)y}\) give
\[
k_0y^{9/4}e^{-\pi y}\le\Phi(x)\le4\pi^2y^{9/4}e^{-\pi y}.
\]
For completeness, \(\sum n^k e^{-\pi(n^2-1)y}<2\) for k<=6 follows by separating n=1 and bounding ratios of the remaining terms by \((3/2)^6e^{-5\pi}<1\). Thus these are full-series bounds, not a fixed truncation. Both physical tails give
\[
L\ge \frac{k_0^2}{2\pi}Y^{7/2}e^{-2\pi Y}.
\]
Using \(e^{2u}-1\ge2u\) and \(2\pi Y-9/2\ge\kappa Y\), it follows that
\[
0\le\Phi(a+u)\le A\sqrt{YL}\,e^{-\kappa Yu}\quad(u\ge0),
\qquad A=\frac{4\pi^2\sqrt{2\pi}}{k_0}. \tag{B11}
\]
Evenness gives the corresponding negative tail. Direct differentiation of the series also gives
\(|\Phi'(x)|\le K_0y^{13/4}e^{-\pi y}\), with \(K_0=8\pi^3+30\pi^2+15\pi\). Incomplete-gamma integration consequently bounds
\[
\|1_{\rm out}\Phi'\|_2^2=O(Y^2L),\qquad
|\Phi(a)|^2+|\Phi(-a)|^2=O(YL). \tag{B12}
\]
For example the first assertion follows by integrating \(K_0^2y^{11/2}e^{-2\pi y}\) and using \(11/2<2\pi\). The elementary bound \(\int_Y^\infty y^p e^{-2\pi y}dy\le Y^pe^{-2\pi Y}/(2\pi-p)\), for the positive exponents used here and Y>=1, follows from \((Y+u)^p\le Y^pe^{pu/Y}\). These reproduce the uniform estimates in I without assuming its numerical computations.

### 4.2 Dirichlet energy, including the jumps

Let \(R_t(u)=\langle t,U_ut\rangle\). It is nonnegative and at most L. Splitting into two same-side overlaps and one opposite-side overlap, B11 gives, for u>=0,
\[
R_t(u)\le \frac{A^2}{\kappa}L e^{-\kappa Yu}
 +A^2 L\,v e^{-\kappa v}\,1_{u\ge2a},
\qquad v=Y(u-2a). \tag{B13}
\]
The same-side integral is an integral of two exponentials on a half-line. The opposite-side integral has interval length u-2a and constant exponential factor \(e^{-\kappa Y(u-2a)}\). At u=2a its length is zero.

Now \(\mathcal D[t]=2\int_0^\infty A_0(u)(L-R_t(u))du\). On \((0,Y^{-1})\), the sharp-cut translation estimate and B12 bound the integral by O(L); it is nonnegative. On \((Y^{-1},1)\), there is no opposite-side overlap because a>=1. The expansion \(2A_0(u)=u^{-1}+O(1)\) gives a mass contribution \(L\log Y+O(L)\), while the overlap contribution is at most
\[
O(L)\int_{Y^{-1}}^1e^{-\kappa Yu}\frac{du}{u}=O(L).
\]
The integral over u>=1 is O(L), since A_0 is integrable there and translation is L2-unitary. Therefore
\[
\mathcal D[t]=L\log Y+O(L)=2aL+O(L). \tag{B14}
\]
This proof retains both boundary jumps; omitting them is not used to improve the estimate.

### 4.3 Full prime-power and pole budgets

The same-side part of \(2\sum_{n\ge2}\Lambda(n)n^{-1/2}R_t(\log n)\) is bounded by
\[
O(L)\sum_{n\ge2}\log(n)n^{-1/2-\kappa Y}=O(L)
\]
uniformly for a>=1. For the opposite-side part only n>=Y contributes. Put \(v_n=Y\log(n/Y)\).

For \(Y\le n\le2Y\), write r=n-Y. Then \(r/2\le v_n\le r\), and
\[
\frac{\log n}{\sqrt n}v_ne^{-\kappa v_n}
\le\frac{\log(2Y)}{\sqrt Y}\,r e^{-\kappa r/2}.
\]
The sum of the last exponential expression over the integer lattice, with any fractional offset Y, is uniformly bounded: compare with \(\sum_{j\ge0}(j+1)e^{-\kappa j/2}\). For the remaining n, partition into \([2^kY,2^{k+1}Y)\), k>=1. Counting integers and using \(\Lambda(n)\le\log n\) gives an upper bound by a constant times
\[
Y^{3/2}\sum_{k\ge1}(k+1)(\log Y+k+1)
 2^{-(\kappa Y-1/2)k}.
\]
This is uniformly bounded for Y>=e^2, since it is at most a constant times
\(Y^{3/2}(\log Y+1)2^{-\kappa Y+1/2}\). Thus the **entire** prime-power contribution is O(L). No prime-number theorem, omitted-prime cutoff or restriction n<=Y has been substituted for the infinite tail sum.

From B11,
\[
|M_\pm(t)|\le A\sqrt{YL}
\left(\frac{e^{a/2}}{\kappa Y-1/2}
+\frac{e^{-a/2}}{\kappa Y+1/2}\right).
\]
Consequently both-pole contribution is O(e^{-a}L), in particular O(L). The mass term is exactly \(-c_AL\). Combining these facts with B14 proves B10.

### 4.4 What this proves, and what it does not

Endpoint integration of the same full theta series yields [S, S18; I, S18b]
\[
T(a)\sim\frac{2\pi^3}{I}e^{7a}e^{-2\pi e^{2a}},\qquad
\mathfrak B_a[\Phi]\sim YIT(a).
\]
The omitted n>=2 source terms are exponentially smaller at fixed derivative order; \(\int_Y^\infty y^{7/2}e^{-2\pi y}dy\sim Y^{7/2}e^{-2\pi Y}/(2\pi)\) supplies the first constant. The weighted mass dominates S9 for Φ, supplying the second equivalence. Hence B10 proves
\[
Q[p_a]=\frac{\tau}{N^2}=\frac{(2a+O(1))T}{1-T}. \tag{B15}
\]
For **every** fixed M>0 and ν>=0 this uncorrected trial eventually fails \(Q[p_a]\le Me^{\nu a}T^2\): the ratio is asymptotic to \(2a/[Me^{\nu a}(1-T)T]\), which tends to infinity. This is an actual-source obstruction to c=0, not to all coefficients or all degrees.

The raw-reference inflation is only
\[
\frac{22\mathfrak B_a[\Phi]}{Q[t_a]}\sim\frac{11e^{2a}}a. \tag{B16}
\]
Such an exponential factor can be absorbed by changing ν. Thus even a large or growing raw-reference loss cannot by itself establish strict strength between the existential theta targets. The genuinely unabsorbed issue is the additional double-exponential factor T. Nothing in B10–B16 supplies a comparison uniform in an unbounded derivative degree.

## 5. The one remaining quantified atom

Define \(\mathcal R_{m,a}\) as in Section 2.3 and
\[
\mathcal R_\infty(a)=\sup_{m\ge0}\mathcal R_{m,a}\in[0,+\infty],
\qquad D_\infty(a)=\tau(a)-\mathcal R_\infty(a).
\]
Set \([D_\infty]_+=\max(D_\infty,0)\), with \([-\infty]_+=0\). These are quantities of the **same exact derivative shells**, not of a larger function-space completion or a ground eigenvector.

**Sole retained assertion — UNIFORM_FULL_SOURCE_RECOVERY_SATURATION:**
\[
\boxed{\begin{gathered}
\exists K>0,\ \mu\ge0,\ a_0\ge1\quad
\forall a\ge a_0:\\
[\tau(a)-\mathcal R_\infty(a)]_+
\le K e^{\mu a}T(a)^2N_a^2.
\end{gathered}} \tag{ATOM}
\]
**Type: NEW-MATH, unproved.** The assertion concerns uniform saturation of full-source recovery, not finite rank or inverse existence. It is irreducible only relative to the reductions and proof attempts in this verdict. This is the minimum remaining assertion for the signed supplier used here; optional recovery of the sufficient S15 certificate is not added as a second requirement.

### 5.1 Why arbitrary degree growth reduces exactly to this atom

For fixed a, appending a zero coefficient embeds every trial in the next shell. Thus \(\mathcal R_{m,a}\) is nondecreasing and
\[
D_\infty(a)=\inf_m\inf_{c\in\mathbb C^{m+1}}Q[w_c]. \tag{B17}
\]
If a legal cofinal strong supplier with witnesses \((M,\nu,a_*,m(a))\) exists, B2 immediately gives ATOM with K=M, μ=ν and \(a_0=\max(1,a_*)\).

Conversely, assume **exactly ATOM**. For each a>=a_0 put \(\mathcal K_a=Ke^{\mu a}T^2N^2>0\). Since \(D_\infty\le\mathcal K_a<2\mathcal K_a\), there is a finite m with \(\tau-\mathcal R_{m,a}<2\mathcal K_a\). Choose the least such m. On a bounded block use \(c=C^\dagger s/N\); on a negative or coupled-null block use the scaling construction of Section 2.3 until \(Q[w_c]<2\mathcal K_a\). This produces
\[
Q[p_a-z_a]\le 2Ke^{\mu a}T(a)^2,
\quad M=2K,\quad\nu=\mu,\quad a_*=a_0. \tag{B18}
\]
Equivalently \(J_a(z_a)\ge r_a-2Ke^{\mu a}T^2\). These are **conditional witnesses**, not witnesses established in this batch. The strict slack avoids assuming that an infinite-shell infimum is attained.

This is a deterministic, source-defined existence prescription. The least integer uses only exact source quantities. Negative directions can be chosen by the first negative rational coefficient vector in a fixed enumeration; a coupled kernel vector can be chosen as \((I-CC^\dagger)s\). No unknown full ground vector is used. No algorithmic complexity, effective inverse bound or numerical stopping certificate is claimed. The request permits arbitrary m(a), so none is required for the existence implication. The coefficient prescriptions themselves are the frozen signed-response cases of S3.4; no new direction family is introduced.

### 5.2 The missing estimate in cancellation coordinates

On every bounded finite block, B6–B7 identify
\[
\tau-\mathcal R_{m,a}=\beta_{m,a}-\mathcal L_{B,m,a}-\mathcal A_{m,a}. \tag{B19}
\]
Thus the retained atom controls what remains **after** both exact loss corrections, not merely the positive-reference cost. On any chain of positive blocks there is an even more local identity. Write
\[
C_{m+1}=\begin{pmatrix}C_m&k\\k^*&c\end{pmatrix},\quad
s_{m+1}=\binom{s_m}{s_{\rm new}},\quad
\eta=c-k^*C_m^{-1}k>0.
\]
Finite elimination gives
\[
\mathcal R_{m+1,a}-\mathcal R_{m,a}
=\frac{|s_{\rm new}-k^*C_m^{-1}s_m|^2}{\eta}. \tag{B20}
\]
Proof: eliminate the first block in the quadratic minimization. Its residual linear coefficient is \(s_{\rm new}-k^*C_m^{-1}s_m\), and its remaining quadratic coefficient is η; completing that scalar square yields B20. Small positive pivots alone do not ensure recovery: the numerator may vanish. This identity is not used across an indefinite or singular pivot.

By B10, τ>0 eventually and \(\tau\sim2aIT\). On the windows where \(\mathcal R_\infty<\infty\), ATOM consequently requires
\[
\left[1-\frac{\mathcal R_\infty(a)}{\tau(a)}\right]_+
\le \frac{Ke^{\mu a}T^2N^2}{\tau}
\sim\frac{K}{2a}e^{\mu a}T(1-T). \tag{B21}
\]
This is the quantitative accuracy that the cumulative full-source recoveries must reach. A qualitative nonzero coupling, finite inverse, or nonincreasing residual proves none of B21. On negative or coupled-null windows the atom is automatic; on a decoupled-null window it is not.

### 5.3 Proof attempts and FIRST_FAILURE

The direct majorant attempt starts with the feasible coefficient of Φ and proves \(1/Z\le\mathfrak B_a[\Phi]\). Rechecking I's endpoint estimates gives the unconditional bound
\[
Q[f_B]\le1{,}800{,}000\,e^{2a}\frac{T}{1-T}
\quad(a>0,\ m\ge0).
\]
Dividing this bound by \(Me^{\nu a}T^2\) leaves a factor proportional to \(e^{(2-\nu)a}/[(1-T)T]\), which diverges for every fixed ν. This disproves the attempted deduction from that bound, not the target. The stronger actual-source calculation B15 also rules out solving the problem by taking no correction.

The signed attempt computes the exact Schur recovery and then adds directions using B20. The **first failure** is the absence of any lower estimate for the accumulated recovered energy at the precision B21. Finite rank proves neither that the residual coupling is large enough nor that cumulative recovery has the required limiting value. Singular decoupling remains a genuine branch, not an inverse-bookkeeping exception.

The coefficient-approximation attempt uses S16–S17 to express every fixed-degree entry by theta moments. Those exact expressions give no bound uniform in growing derivative order. For example, a proved geometric contraction in m would suffice with degree proportional to \(\log(1/T)\sim2\pi e^{2a}\), as S19 shows; that contraction was not derived. Alternatively, pointwise convergence of the signed envelope to a value satisfying ATOM would suffice without a degree rate, by B18. Linear independence and analytic continuation do not prove that convergence or that limiting value.

The arithmetic attempt retains S35's identity for each actual f_c:
\[
Q[f_c]=\mathcal M_c+2\int_1^{e^{2a}}D_\psi(x)k_c'(x)dx,
\quad k_c(x)=x^{-1/2}R_{f_c}(\log x).
\]
Here \(\mathcal M_c=\mathcal D[f_c]-c_A\|f_c\|_2^2+R_{\rm pole}[f_c]-2\int k_c\). The autocorrelation derivative includes the moving-endpoint term
\(-\Re(\overline{v(\log x-a)}v(-a))\), for the smooth inside profile v of f_c. Both Stieltjes boundary products vanish, because \(k_c(e^{2a})=0\) and \(D_\psi(1)=0\). There is no independent signed estimate for this full main-term-plus-integral sum at T^2 scale. Splitting \(b=b_A-b_P+b_R\) and discarding mixed products is invalid: \(C=1,b_A=b_P=1,b_R=0\) gives total recovery zero. Thus this representation locates the same unpaid cancellation, not another admitted premise.

```yaml
FIRST_FAILURE:
  statement: uniform accumulated full-source recovery at the accuracy in B21
  finite_inverse_failure: false
  finite_rank_failure: false
  proved_source_obstruction: uncorrected theta trial fails every fixed cofinal T_squared budget
  obstruction_scope: c_equals_zero_only
  source_family_changed: false
  cofinal_positive_C_assumed: false
  irreducibility_scope: demonstrated_shelf_reductions_only
```

A repair that adds arbitrary localized functions or uses full ground eigenvectors exceeds the frozen source family. It would need a separate, quantitative approximation back into the exact S_{m,a}, with the physical affine normalization and E-to-Q error budget preserved. No such repair is adopted. Merely estimating another representation's coefficients does not discharge that transfer.

## 6. What the frozen finite comparison actually measures

The following are **READ report results from R**, not new computations of the source form. At a=7/10,m=6, R reports the full-source interval \(Q[f_y]/T^2\in[1.069376842,1.069376844]\), \(T^2\approx6.589865655707739776\cdot10^{-13}\), strong margin about \(-4.57184076\cdot10^{-14}\), and transfer uncertainty below \(1.541\cdot10^{-22}\). Hence M=1 fails this frozen row; M=1.07 covers that row only.

The reference comparison keeps two different coefficients:

| Functional / coefficient | Reported value |
|---|---:|
| Minimum \(B_H=\mathfrak B[v_B]=1/Z\) | \(3.931797412246448274\cdot10^{-11}\) |
| \(B_y=\mathfrak B[v_y]\) for the frozen signed row | \(2.384968930795830427\cdot10^{-10}\) |
| \(22B_H/(N^2T^2)\) | 16420.4321288621 |
| \(22B_y/(N^2T^2)\) | 99603.8614186945 |
| \(Q[f_y]/T^2\) | approximately 1.069376843 |
| \(Q[f_B]/T^2\) | **NOT COMPUTED in the pinned report** |

Subtracting the last known signed energy from the **same-row** reference bound gives
\[
\frac{\mathcal L_y}{N^2T^2}
=\frac{22B_y}{N^2T^2}-\frac{Q[f_y]}{T^2}
\approx99602.7920418515. \tag{B22}
\]
The same-row bound is about 93141.97 times its actual energy. These are arithmetic evaluations of the report's rounded values, not newly tightened intervals. They identify genuine majorant loss without changing coefficients.

By contrast, 16420.4321288621 is a minimum of the reference functional, not a measurement of the signed energy at c_B. Nor is f_y asserted to equal c_Q. On a bounded signed block, the rigorous algebraic inequality
\[
\mathcal A+\mathcal L_B=\beta-\delta^\dagger
\ge\beta-N^2Q[f_y] \tag{B23}
\]
would give an aggregate loss of at least approximately 16419.3627520181 in units \(N^2T^2\), using the displayed values. It cannot split that loss between \(\mathcal A\) and \(\mathcal L_B\). Positivity of C is not inferred from the physical Gram or the reference solve.

This finite comparison does not rule out improvement at larger m, an allowed larger ν, or an a_* that excludes this window altogether. K36/K48 results above a=.70 and the 1.5 forecast at a=.75 remain UNRESOLVED. No repeated scalar refinement, new eigensolve, matrix-builder run or interval experiment was performed.

## 7. Frozen predictions

| Prediction | Score | Exact scope of evidence |
|---|---|---|
| P1, p=.90 | **CONFIRMED** | B8 proves S15 -> actual c_B strong budget -> S26 on positive blocks. B6 and B9 identify the missing uniform reverse comparison. This confirms the shelf-reduction statement, not a theorem that every possible theta proof must use that comparison. Theta necessity and strict strength remain unresolved. |
| P2, p=.85 | **CONFIRMED** | B3 and the rank argument close finite existence; B20–B21 expose the first unpaid uniform cancellation/approximation estimate. B15 proves that the uncorrected source cannot supply the extra T. |
| P3, p=.95 | **CONFIRMED** | R's finite ratio is a fixed a,m sufficient-bound cost. Neither its quantifiers nor B22–B23 exclude another degree schedule or cofinal starting point. |
| P4, p=.90 | **CONFIRMED** | No bound below for the window floor or all compact smooth tests is proved. B10 is a sign/size statement for one tail vector only, not a lower-sign supplier. |

The separately frozen discriminator “minimum reference-bound ratio at a=.7,m=6 >10” is already resolved by R's 16420.4321288621. It was not rerun or treated as a new prediction. Predictions were not used as premises.

## 8. One next_decisive_test and actual delivery boundary

**One test: evaluate the signed energy of the reference minimizer already defined by the same source H and ell.** This is a proposed finite discriminator, **NOT_RUN** in this batch. It is a new observable, not another rounding of Q[f_y].

Freeze a=7/10,m=6, exact \(\theta_B=H^{-1}\ell/Z\), true physical N, and \(f_B=1_{(-a,a)}\sum_i(\theta_B)_iu_i/N\). Freeze the rational finite budget \(M_{\rm diag}=107/100\), \(\nu_{\rm diag}=0\). Enclose
\[
\mathfrak m_B=(107/100)T(7/10)^2-Q[f_B]. \tag{TEST}
\]
**Threshold:** zero. Require the resolved sign to exceed ten times the total absolute uncertainty. Include H/ell solve uncertainty, theta-series tails, physical normalization, full-form evaluation and source-transfer error. S41/B1 permits transfer through \(22e(2\|\widetilde f_B\|_E+e)\). Neither a printed inverse residual nor a Legendre matrix alone supplies that certificate.

**If the lower enclosure is positive:** this reference coefficient already passes the finite strong budget even though its positive bound costs 16420.43. Then \(\mathcal L_B/(N^2T^2)\) exceeds approximately \(16420.43-1.07\); discarded signed cancellation explains this particular certificate failure.

**If the upper enclosure is negative:** this reference coefficient fails a budget that the frozen f_y meets. Thus coefficient choice matters too. On any certified bounded signed block, \(\mathcal A\ge N^2(Q[f_B]-Q[f_y])>0\), so the coefficient-choice loss receives a direct lower bound without solving for c_Q.

An enclosure crossing zero or lacking a total-error budget is UNRESOLVED. Neither outcome proves or refutes ATOM. The test discriminates which exact loss mechanism deserves a uniform proof; it does not pretend that one window decides a cofinal assertion. No C-positivity certificate or new basis is required to compute TEST itself.

**Delivery.** Only EXPECTED_VERDICT_PATH is written. Before publication it was absent on rh_clean. The checked pre-publication head was `fd72b51b9f0ea534e0e5ee9e094df13442a2b265`; GitHub comparison places it four commits after the request pin, with that pin as merge base. The mathematical shelf remains SOURCE_BASE, not the moving head. Publication uses GitHub's Contents API to create a remote commit and update rh_clean directly; no separate command-line push is claimed. The final commit ID, artifact SHA-256, Git blob, bytes and lines are recorded in the delivery receipt, avoiding a self-referential hash inside this file. Publication verifies bytes and the one-path write boundary, not the new paper proof or ATOM. No Lean, registry, queue, goal, route status or RH-claim file is changed.

## 9. Proshka's own line

I keep the full signed response because it measures the affine energy the request actually spends.
The positive reference remains useful as a deterministic constructor and an independent diagnostic.
I do not require its certificate to be necessary for the theta supplier.
That distinction matters more than the large finite ratio by itself.
The first nearby alternative was to prove an inverse-growth law directly from H's positivity.
Its missing ingredient is approximation, not matrix existence.
The second nearby alternative was to fit a degree law to the finite shell table.
The unresolved matrix errors and the unrestricted schedule make that inference unjustified.
The exact loss identity separates coefficient choice from discarded signed cancellation.
That separation prevents a numerical comparison from answering the wrong logical question.
The first move beyond this batch is the signed-energy test for the existing reference minimizer.
A certified failure at 1.07 would reject that coefficient choice at that window.
It would not reject the derivative family or a cofinal construction.
The second move is a uniform estimate for the cumulative full-source recoveries in B20.
A source-compatible lower residual envelope larger than every exponential times T squared would kill that route.
A small pivot or a large inverse is not that estimate in either direction.
The data I would request are the reference coefficient enclosure and its source-normalized signed energy.
I would also request the residual couplings and pivots with errors when degree is increased.
I would not request more digits of the already resolved frozen signed scalar.
What surprised me is that the raw theta tail admits the sharper signed scale 2a times its mass.
Its full prime-power contribution remains lower order without a prime-number theorem.
That makes the additional factor T a concrete recovery requirement rather than a loose-bound artefact.
The positive raw-reference inflation is only exponential in a and can be absorbed in an existential exponent.
I therefore distrust any declaration of strict theta strength based on numerical waste alone.
I also distrust fixed-order theta error bounds reused at an increasing derivative degree.
The least-degree selection is valid only after its limiting recovery premise is paid.
The remaining premise is explicit enough to attack without changing the source object.
Nothing here turns an upper trial estimate into the missing lower sign.

## 10. Research log

### 10.1 Sources consulted: READ versus RELAY

Repository locators below mean `https://github.com/Malaeu/chen_q3/blob/<pin>/<path>` with the exact pins and paths in Section 0; their full hashes are not moving-branch citations.

| Source and locator | Status | Material taken or rejected |
|---|---|---|
| BRIDGE request at b968f9443d5491778ab5e65c75c4ad7d64ba0b14, `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_BRIDGE_2026-09-09.txt`, all 83 lines | **READ**, bytes verified | Frozen source, two terminal codes, exact implication question, forecasts and one-path authorization. |
| S at SOURCE_BASE, S1–S20, S21–S29, S30–S41, Sections 9–10 | **READ**, full file and hashes verified | Rechecked source/domain/radical arguments, finite identities, positive construction and the precise unproved targets; no cofinal premise promoted. |
| I at SOURCE_BASE, complete table, foundational extension, S18b proof, source limitations | **READ**, full file and hashes verified | Rechecked finite algebra and explicit fixed-source bounds; retained its local Suzuki v1 limitation. Its historical numerical runs remain report evidence. |
| R at SOURCE_BASE, all follow-ups, especially full-source margin and positive tail-reference comparison | **READ**, full file and hashes verified | Frozen finite numbers, distinction between f_y and f_B, and the missing Q[f_B]; no new computation or companion-JSON audit. |
| Q at SOURCE_BASE, Sections 2, 4–6 and boundaries | **READ**, full file and hashes verified | Exact unscaled source directions, strong versus normalized target, and fixed-family restrictions. |
| B at SOURCE_BASE, closure-batch and versioned-shelf rules, own line and research log | **READ**, full file and hashes verified | Verdict organization and evidence classifications, not a mathematical premise. |
| Suzuki HTML, `https://arxiv.org/html/2606.09096v1`, introduction functional and (3.1) | **READ primary HTML**, version identity limited | Geometric functional, pairing conversion and signed zero formula. The served header/body dates disagree; no identification with the local June PDF or S's v2 and no cofinal result imported. |
| Suzuki local PDF, arXiv:2606.09096v1, p.1, p.3, p.13 (3.1), as described by I | **RELAY from I**, not personally opened | Preserved the independent check's actual source version; not silently upgraded. |
| Suzuki arXiv:2606.09096v2, as cited in S | **RELAY from S**, not fetched as v2 | Historical citation only; the version-specific content is not independently certified here. |
| NIST DLMF, `https://dlmf.nist.gov/25.4`, (25.4.4) | **READ primary HTML** | Standard ξ normalization for the Mellin calculation; no historical release metadata claim. |
| NIST DLMF, `https://dlmf.nist.gov/20.7`, (20.7.32) at z=0, τ=iu | **READ primary HTML** | Theta inversion, differentiated to recover source evenness. |
| DISTANCE/KERNEL reports, point-5 supplement and source scripts mentioned inside S/I/R | **RELAY only in this batch** | Their embedded statements were not treated as fresh reads or executions; the mathematical inputs used are restated and proved above. |
| arXiv search hit at `https://arxiv.org/` | **REJECTED search result** | Generic landing-page search excerpt was not a versioned paper source and supplied no theorem. |
| GitHub connector reads, branch metadata and request-to-head comparison | **READ transport metadata** | Exact object bindings, absent target path and publication ancestry; not mathematical verification. Direct raw-HTTP transport attempts supplied no source evidence. |

No PDF was analyzed in this batch. No OCR, source numerical probe, interval rerun, Lean compilation or axiom check was performed. New arithmetic was limited to byte hashes and subtraction/division of already published rounded diagnostic numbers. B10 and the abstract examples are paper derivations, not inferred numerical experiments.

### 10.2 Attempted and abandoned branches

| Candidate | First inequality or fact that stops the attempted closure |
|---|---|
| Upgrade S18b merely by changing M and ν | \(e^{(2-\nu)a}/[(1-T)T]\to\infty\); B15 also rules out the actual uncorrected trial. |
| Infer approximation from finite reference invertibility | H>0 gives Z>0, not a lower bound of size \(1/(e^{\nu a}T^2N^2)\). |
| Identify the reference and signed minimizers | B6 contains the nonnegative mismatch \(\mathcal A\), which need not vanish. |
| Reverse the positive majorant using the small signed value | B5 leaves a nonnegative slack not bounded by the signed value; the Q_2 abstract model separates them. |
| Infer strict theta strength from 16420.43 | This is one coefficient optimization at one window and degree, not a quantified obstruction; B16 illustrates an absorbable growing loss. |
| Use an analytic-independence argument as a shell-approximation theorem | Vanishing finite combinations are excluded, but no norm of the inverse restriction or limiting recovery is controlled. |
| Impose a geometric contraction or match many boundary jets | No uniform coefficient bound and whole-tail remainder for growing degree was obtained; exact endpoint equations alone do not bound the exterior energy. |
| Use a null direction to settle the strong target | The decoupled-null model retains margin -1/2 for every coefficient. |
| Use prime-only recovered energy or an absolute prime-counting envelope | The full recovery includes mixed products; the entire main term plus signed integral must fit the budget. |
| Add a larger function family or an unknown ground vector | This changes the permitted input and requires an unpaid source-shell approximation and normalization transfer. |

### 10.3 Intermediate identities that remain useful

B4 gives the exact reference cost of changing coefficients, independently of Q's sign.
B5 separates estimator slack from signed-form domination slack without dropping any source term.
B6–B9 give the pointwise implication diagram and exact additive reverse budgets, including zero or negative δ.
B10–B16 give the new full-source raw-tail asymptotic, the c=0 obstruction, and its merely exponential reference inflation.
B17–B18 show why an unrestricted degree schedule needs limiting-envelope control but not a separately proved growth rate.
B20 gives the exact residual-coupling gain at one positive Schur pivot; it does not lower-bound that gain.
B22 is a same-coefficient cancellation measurement; B23 is only an aggregate optimizer-loss bound on bounded blocks.
The failed geometric-contraction deduction remains a conditional degree rule, not a supplier hypothesis accepted here.

**Terminal scope:** IRREDUCIBLE_ATOM answers this upper-rate mechanism question only. No cofinal T-squared supplier, no lower-sign supplier and no RH conclusion is asserted.
