<!-- PROVENANCE: second version of the PHASEPROOF verdict, produced by the judge in a session without GitHub write access and uploaded by the owner on 2026-09-06; relayed to the bus by Linux-Claude unchanged below this line. The committed version (4a29f389, 888 lines) is a separate run of the same request; both are kept. sha256 of the uploaded bytes: b37d2151c643006e -->
# STATUS: TRY_PHASE_MIXED_KERNEL_WITH_FULL_RESIDUAL_AND_TENSOR_CROSSWALK
```yaml
OPERATIVE_CLASS: TRY_PHASE_MIXED_KERNEL_WITH_FULL_RESIDUAL_AND_TENSOR_CROSSWALK
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-06-PHASEPROOF
BOUNDARY_ID: GOAL058_PHASE_CLASS_INEQUALITY_8_AND_MOLLIFIER_CROSSWALK
RESULT:
  Q1: PARTIAL_WITH_PRECISE_REMAINDER
  Q1a: PARTIAL_WITH_PRECISE_REMAINDER
  Q1b: COMPUTATION_SPECIFIED
  Q1c: OBSTRUCTION_NAMED
  Q1d: PARTIAL_WITH_PRECISE_REMAINDER
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a: PARTIAL_WITH_PRECISE_REMAINDER
  Q2b: OBSTRUCTION_NAMED
  Q2c: COMPUTATION_SPECIFIED
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: e3dba5975b10ba7dbebbdea948612dd830aaf67a
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06.txt
  GIT_BLOB: 1d00e0e9a735c43ac14e6785f2415fce472cc13e
  SHA256: ec050368d9d4bef1185df68a549d58f81ae6d5462b3b968831273c6349ffba7c
  BYTES: 11445
  LINES: 96
  FINAL_LF: true
  GITHUB_FETCH_PERFORMED: true
  UTF8_SHA256_AND_GIT_BLOB_RECOMPUTED: true
  ALL_FOUR_REQUEST_CHECKS_MATCH: true
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  FETCHED_REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
CLOSES_ARE_REVIEW_OBLIGATIONS_NOT_LEAN_CATALOG_EXPORTS: true
CLOSES:
  - PHASEPROOF_MIXED_TERM_EXPLICIT_TESTED_KERNEL_REPRESENTATION
  - PHASEPROOF_FULL_GALERKIN_RESIDUAL_TRACE_SANDWICH
  - PHASEPROOF_LITERAL_QSERIES_JACOBI_EQUALS_G_CLAIM_REFUTATION
  - PHASEPROOF_TWO_PRIME_THREE_LOBE_HERMITIAN_CONTRACT
  - PHASEPROOF_HS_SQUARE_TENSOR_DICTIONARY
OPENS: []
REMAINS_OPEN:
  - SEMITABLE_INEQUALITY_8_ON_THE_FULL_COMPLEX_POLE_NULL_PHASE_CLASS
  - CERTIFIED_SOURCE_CARRIER_AND_TEST_SPACE_COMPLEMENT_BUDGETS
  - GROWING_PRIME_SET_SECOND_MOMENT_CONTROL
  - IDENTIFICATION_OR_EXCLUSION_OF_A_ZETA_SPECIFIC_NONLINEAR_SINGLE_TEST_MAP
DECISIONS:
  INEQUALITY_8_PROVED_ON_WHOLE_CLASS: false
  INEQUALITY_8_PROVED_ON_INFINITE_DIMENSIONAL_SUBCLASS: false
  MIXED_KERNEL: EXPLICIT_TESTED_DISTRIBUTIONAL_KERNEL
  POINTWISE_KERNEL_CONVERGENCE: not_claimed
  ANGLE_EIGENVALUES_ALONE_SUFFICE: false
  CCM_2403_01247_JACOBI_IS_G_OR_G_INVERSE: false
  FULL_RESIDUAL_MAY_BE_REPLACED_BY_COMPRESSED_RESIDUAL: false
  FALSE_FACTOR_CLASSWIDE_SURVIVAL_PROVED: false
  DAVENPORT_HEILBRONN_ARITHMETIC_SONIN_CROSSWALK: not_supplied
  HS_SQUARE_CANONICAL_REPRESENTATION: TENSOR_SQUARE_OF_WEIL_FORM
  UNIVERSAL_FORM_INDEPENDENT_SINGLE_TEST_REPRESENTATION: refuted
  NO_POSSIBLE_ZETA_SPECIFIC_NONLINEAR_MAP: not_proved
  PRIME_OFF_DIAGONAL_IS_SIMPLY_ANGLE_REMAINDER: false
  HARDY_LITTLEWOOD_LOGICALLY_NECESSARY: not_proved
  MONTGOMERY_TAYLOR_CONSTANT_IN_REQUEST: FACTOR_REPAIR_REQUIRED
CORRECTIONS:
  Q1a_LOWER_BOUND: nu_a >= n0 - A0 - J_a - w
  R_MT: 1/2 + cot(1/sqrt(2))/sqrt(2)
EVIDENCE:
  NEW_DERIVATIONS_VERIFIER: PAPER
  SOURCE_SCOPE: ABSTRACT
  NUMERICAL_DIAGNOSTICS: REQUEST_REPORTED_NOT_CERTIFIED
  INDEPENDENT_LEAN_KERNEL_VERIFICATION: false
  SHELF_SHA_PREFIXES_INDEPENDENTLY_RECOMPUTED: false
  HISTORICAL_NOVELTY: not_claimed
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_PHASE_CLASS_INEQUALITY_AND_MOLLIFIER_CROSSWALK_2026-09-06.md
  STATUS: LOCAL_VERDICT_COMPLETE_REMOTE_COMMIT_BLOCKED
  REASON: AVAILABLE_GITHUB_ACTIONS_ARE_READ_ONLY_NO_AUTHENTICATED_CLI
  COMMIT_SHA: null
  REMOTE_PATH_UPDATED: false
  COMMITTED_VERDICT_CLAIMED: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_EXPERIMENT_PERFORMED: false
ARISTOTLE_SUBMISSION: false
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

**The phase inequality is not proved in this batch.** There is a complete paper derivation of its mixed kernel and of a two-sided, full-residual certificate for finite test packets. There is also an exact obstruction to the proposed q-series shortcut: the cited Jacobi operator is not the Sonin-image Gram operator. The two-thirds second moment has a precise **tensor** crosswalk, not the asserted direct identification with a single Weil square.

The remaining inequality is displayed in (12). No diagnostic value is a premise. Failure to derive its sign does not refute it, its infinite-dimensional subclasses, or the route. All new proofs below are **PAPER**, not Lean-verified results. Publication is separately blocked: no available GitHub action writes files, and no authenticated GitHub CLI is available in this runtime. This document is not a committed repository verdict.

**Source abbreviations** are resolved in §9. [REQ], [ST], [IC], and [SW] are read at the immutable request commit. [C20], [C23], [C26], [J24], [AF26], [A26], and [L26] are primary papers. In particular, the 17-page Anthropic PDF and arXiv:2608.13637v1 are distinct documents; their page numbers are not interchangeable. [ABSTRACT][PAPER]

### Structure retained

Use the common log carrier \(\mathcal H=L^2(\mathbb R,dx)\),
\[
 (U_c f)(x)=f(x-c),\qquad T_h f=h*f,\qquad
 \langle f,g\rangle=\int\overline f g.
\]
The last convention is conjugate-linear in the first argument. A convolution test is not a vector to which the position cutoff can be applied to annihilate its trace.

Fix
\[
 a=\log2,\quad r=2^{-1/2},\quad w=ar,\quad
 \delta_0=\frac{\log3-\log2}{8},\quad
 B=I-rU_a,\quad P_0=\mathsf S_{\infty,1}.
\]
Put \(\mathcal H_0=\operatorname{ran}P_0\), \(J=B|_{\mathcal H_0}\), and
\[
 G=J^*J=P_0B^*BP_0|_{\mathcal H_0},\qquad
 g_-=(1-r)^2,\quad g_+=(1+r)^2.
\]
Then \(g_-I\le G\le g_+I\). These are squared norm bounds, not angle eigenvalues.

For \(v\in C_c^\infty(\mathbb R;\mathbb C)\), retain the exact [ST] definitions
\[
\begin{split}
 C_v(t)&=\operatorname{Re}\int\overline{v(x)}v(x+t)\,dx,\\
 \mathcal D(v)&=2\int_0^\infty
 \frac{e^{-t/2}}{1-e^{-2t}}\bigl(\|v\|_2^2-C_v(t)\bigr)\,dt,\\
 L_2(v)&=\mathcal D(v)-c_A\|v\|_2^2
       -2\sum_{j\ge1}a2^{-j/2}C_v(ja),\\
 c_A&=\gamma+\log(8\pi)+\pi/2,\qquad
 n(v)=\|T_v\mathsf S_{2,1}\|_{HS}^2.
\end{split}                                                    \tag{1}
\]
Here **HS** denotes the Hilbert–Schmidt norm, the square-sum of an operator on an orthonormal basis. At \(T=W=1\), the contact term vanishes. On support diameter below \(\log3\),
\[
 \mathcal Q(v)=L_2(v)+2\operatorname{Re}
       \bigl(A_+(v)\overline{A_-(v)}\bigr),\qquad
 A_\pm(v)=\int v(x)e^{\pm x/2}\,dx.                            \tag{2}
\]
Thus \(\mathcal Q=L_2\) on the stated pole-null class, not on all modulated windows. [ST; C26, (22)] [ABSTRACT][PAPER]

## Q1(a) — Exact mixed form, kernel, and the unsuccessful sign step

**RESULT: PARTIAL_WITH_PRECISE_REMAINDER.**

### A1. Correct the inequality before estimating it

For real even \(h\), let \(H=\|h\|_2^2>0\), \(Z=T_h\mathsf S_{2,1}\), and use the request's \(n_0,\nu_a,A_0,J_a\). Then
\[
 n_0-\nu_a\le A_0+J_a+w
 \quad\Longleftrightarrow\quad
 \boxed{\nu_a\ge n_0-A_0-J_a-w.}                              \tag{3}
\]
The extra minus sign in Q1(a) reverses the requested threshold. We repair that sentence, not SEMITABLE (8). An algebraic check with \(n_0=1\), \(\nu_a=0\), and \(A_0+J_a+w=0\) satisfies the erroneous threshold but violates SEMITABLE (8). This checks an algebraic equivalence; it is not a source-test counterexample. [REQ; ST, (8)] [ABSTRACT][PAPER]

### A2. Source-faithful projection and trace identities

**Lemma 1. [ABSTRACT][PAPER]** With the above definitions,
\[
 \mathsf S_{2,1}=JG^{-1}J^*,\qquad
 n(h)=\operatorname{Tr}(C_hG^{-1}C_h^*),\qquad C_h=T_hJ.
                                                                    \tag{4}
\]
Moreover,
\[
 H\nu_a=\operatorname{Re}\operatorname{Tr}
       (G^{-1}C_h^*U_{-a}C_h)
       =\operatorname{Tr}(G^{-1}C_h^*D_aC_h),
 \qquad D_a=(U_a+U_{-a})/2.                                      \tag{5}
\]

**Proof.** [C23, v2, (57)–(59), Theorem 4.6] identifies the semilocal Sonin range with \(B\mathcal H_0\). It does not identify its metric with the old metric. Since \(\|Bx\|\ge(1-r)\|x\|\), this range is closed. The operator \(JG^{-1}J^*\) is self-adjoint, is idempotent, and fixes every \(Jx\); it is therefore its orthogonal projection.

The map \(V=JG^{-1/2}\) is an isometry onto that range. Consequently
\(\|T_h\mathsf S_{2,1}\|_{HS}=\|T_hV\|_{HS}\), which proves (4).
Unitarity gives
\(\langle U_{a/2}Z,U_{-a/2}Z\rangle_{HS}
=\operatorname{Tr}(Z^*U_{-a}Z)\).
Insert \(VV^*\), use \(V^*V=I\), and cycle the trace-class products to obtain the first expression in (5). Taking the real part replaces \(U_{-a}\) by its self-adjoint part \(D_a\). The second expression is real. ∎

**Trace-domain boundary.** These are traces after smooth testing, not bare traces of a projection or a translation. One can justify the required domain as follows. In log coordinates, the archimedean Fourier involution has the form \(M R\), with \(M\) a unitary convolution multiplier and \(R\) reflection. For the cutoff \(P=1_{(-\infty,0]}\),
\(I-P-Q=MPM^*-P=[M,P]M^*\).
For smooth compact \(f\), both \(T_f\) and \(T_fM\) are convolutions with Schwartz kernels. Expand
\(T_f[M,P]=[T_fM,P]-[T_f,P]M\).
Each commutator is trace class by the half-line convolution lemma [C20, Appendix D]. The archimedean angle correction is trace class because the compressed cosine kernel on a bounded square has an absolutely summable rank-one expansion. Hence \(T_fP_0\) is trace class. In particular, \(T_hP_0\) is Hilbert–Schmidt; commuting \(T_h\) with \(B\) proves the corresponding assertion for \(C_h\) and \(T_h\mathsf S_{2,1}\). This also explains why the non-Hilbert–Schmidt *bare semilocal angle* is not being summed in (4)–(5). [ST, Theorems 3–4; C20] [ABSTRACT][PAPER]

### A3. An explicit tested kernel, including the angle data it actually needs

**Lemma 2. [ABSTRACT][PAPER]** The mixed form has an explicit distributional kernel determined by the archimedean cosine compression and \(B\). Angle eigenvalues alone are insufficient; translated eigenfunctions are needed.

Here is a construction not involving any unknown zeta zeros. On the physical carrier \(L^2(0,\infty;du)\), let \(E\) extend functions on \((0,1)\) by zero, and let
\[
 (\mathcal F_\infty f)(u)=2\int_0^\infty\cos(2\pi uv)f(v)\,dv,
 \qquad A_\infty=E^*\mathcal F_\infty E.
\]
Then
\[
 P_0=I-\mathcal W
 \begin{pmatrix}I&A_\infty\\A_\infty&I\end{pmatrix}^{-1}
 \mathcal W^*,\qquad \mathcal W=(E,\mathcal F_\infty E),             \tag{6}
\]
transported to the log carrier by \(f(u)\mapsto e^{x/2}f(e^x)\).
The cosine kernel on \((0,1)^2\) determines \(A_\infty\) explicitly. On a prolate eigenfunction with eigenvalue \(\alpha_j\), the block inverse in (6) is
\[
 \frac1{1-\alpha_j^2}
 \begin{pmatrix}1&-\alpha_j\\-\alpha_j&1\end{pmatrix}.
\]

For completeness, \(\|A_\infty\|<1\): it is a compact self-adjoint contraction. Equality would give a nonzero function compactly supported in both physical and Fourier coordinates. Its entire Fourier transform would vanish on an open interval, a contradiction. Thus the displayed block inverse exists. Since \(\mathcal W^*\mathcal W\) is that block matrix, its range projection is the term subtracted in (6). Its orthogonal complement is exactly the common cutoff kernel. This proves (6).

There is also an explicit convergent series for the second inverse. Set
\[
 A=P_0D_aP_0|_{\mathcal H_0},\qquad q=\frac{2r}{1+r^2}<1.
\]
Then
\[
 G=(1+r^2)(I-qA),\qquad
 G^{-1/2}=\frac1{\sqrt{1+r^2}}
 \sum_{k=0}^{\infty}\frac{\binom{2k}{k}}{4^k}q^kA^k.               \tag{7}
\]
Because \(\|A\|\le1\), this series converges absolutely in operator norm. It is an elementary binomial series, not the Jacobi operator of [J24].

Choose an orthonormal basis \((e_j)\) of \(\mathcal H_0\), and define
\(b_j=JG^{-1/2}e_j\). The \(b_j\) form an orthonormal basis of the semilocal Sonin range. Define the kernels
\[
 K_{a,M}(s,t)=\sum_{j<M}
       \langle U_s b_j,U_{t-a}b_j\rangle_{\mathcal H}.
\]
The exact answer to the kernel question is
\[
 \boxed{
 H\nu_a=\operatorname{Re}\lim_{M\to\infty}
 \iint\overline{h(s)}K_{a,M}(s,t)h(t)\,ds\,dt.}                  \tag{8}
\]
More generally this defines the polarized mixed form for two different smooth tests. Its Hermitian part is obtained from
\((K_{a,M}(s,t)+\overline{K_{a,M}(t,s)})/2\).

**Proof of the tested limit.** Expand \(T_hb_j=\int h(s)U_sb_j\,ds\). For a finite sum, Fubini is justified by compact support and the bound \(\|b_j\|=1\). The resulting integral equals
\(\sum_{j<M}\langle T_hb_j,U_{-a}T_hb_j\rangle\).
The series is absolutely convergent after testing, since
\[
 \sum_j\left|\langle T_hb_j,U_{-a}T_hb_j\rangle\right|
 \le\sum_j\|T_hb_j\|^2=n(h)<\infty.
\]
For two tests use Hilbert–Schmidt Cauchy–Schwarz. On each fixed compact support, the commutator bounds used above control the tested trace norm by finitely many smooth-test seminorms. Thus the polarized form is continuous and defines a distributional kernel. This proves (8), with (6)–(7) supplying its operator coefficients. ∎

The assertion is a **tested distributional kernel**, not pointwise convergence of the untested \(K_{a,M}\), nor an elementary closed scalar expression. In particular, (8) must not be implemented by assigning a finite value to \(\operatorname{Tr}(U_a\mathsf S_{2,1})\).

**Falsifier for angle-only reasoning.** Let \(S_1,S_2\) project onto the first and second coordinates of \(U=\operatorname{diag}(1,-1)\). They have identical projection eigenvalues but mixed trace \(+1\) or \(-1\). Taking \(P_j=Q_j=I-S_j\) also gives identical paired-projection angle data. Thus those data do not determine a mixed trace relative to the separately fixed unitary. This refutes a generic loss of eigenfunction information, not R1− on the source class. [ABSTRACT][PAPER]

### A4. Using \(U_a=(I-B)/r\) preserves, but does not settle, the sign

**Lemma 3. [ABSTRACT][PAPER]** The proposed substitution gives the exact identities
\[
\begin{split}
 \nu_a&=\frac1r\left(n_0-
     H^{-1}\operatorname{Re}\operatorname{Tr}(Z^*BZ)\right),\\
 \frac{\|BZ\|_{HS}^2}{H}&=(1+r^2)n_0-2r\nu_a,\\
 n_0-\nu_a&=\frac{\|BZ\|_{HS}^2/H-g_-n_0}{2r}.
\end{split}                                                       \tag{9}
\]

**Proof.** Expand \(B=I-rU_a\), and then expand \(B^*B=(1+r^2)I-r(U_a+U_{-a})\). Taking the tested traces gives the first two identities; rearrangement gives the third. Also \(BZ=T_{Bh}\mathsf S_{2,1}\), so \(\|BZ\|_{HS}^2=n(Bh)\). ∎

Consequently (8) of SEMITABLE is equivalent to
\[
 n(Bh)-g_-n(h)\le2rH\bigl(A_0+J_a+w\bigr).                       \tag{10}
\]
This does not identify \(B\)-images with equal-amplitude phase differences. It compares two tests using the **same** semilocal projection.

The attempted proof using only \(g_-I\le B^*B\le g_+I\) stops here. Those bounds imply merely \(-n_0\le\nu_a\le n_0\). The resulting sufficient condition
\(2n_0\le A_0+J_a+w\) is stronger than the requested inequality and has no proved supplier on this class. Failing that sufficient condition would not refute R1−. An estimate on the actual mixed kernel, not just the norm of \(B\), remains necessary for this representation.

## Q1(b) — Exact remainder; q-series obstruction; finite certificate specification

**RESULT: COMPUTATION_SPECIFIED**, with an explicit distinction between a finite-packet certificate and the still-unproved whole-class bound.

### B1. The first unproved inequality

Set
\[
 \mathcal H_{00}^{\rm test}
 =\{h\in C_c^\infty(-\delta_0,\delta_0;\mathbb C):A_+(h)=A_-(h)=0\},
 \quad v_h=\frac{U_{a/2}h-U_{-a/2}h}{\sqrt{2}\|h\|_2}.
                                                                    \tag{11}
\]
The supports are disjoint. Hence \(\|v_h\|_2=1\), \(C_{v_h}(a)=-1/2\), and the only active prime-power translation in (1) is \(a\). Each translate preserves the zero moments, so (2) has no pole term.

The remaining demand is exactly
\[
 \boxed{\forall\,0\ne h\in\mathcal H_{00}^{\rm test}:\quad
 \Delta(h):=L_2(v_h)-\operatorname{Tr}
 (C_{v_h}G^{-1}C_{v_h}^*)\ge0.}                                  \tag{12}
\]
**Budget: zero negative remainder.** For real even \(h\),
\(\Delta(h)=A_0+J_a+w-n_0+\nu_a\). For complex \(h\), use (12) or the polarized kernel; do not silently assume the real-even phase formula. [ST, (4)–(8); Lemmas 1–3] [ABSTRACT][CONDITIONAL]

The stop is not just an unevaluated finite number. No all-direction estimate of (12), no certified finite-packet margin, and no infinite-dimensional test-complement bound have been supplied here.

### B2. The proposed exact-arithmetic supplier is a different operator

**Lemma 4. [ABSTRACT][PAPER]** The Jacobi matrix in arXiv:2403.01247v1 is not \(G\), is not \(G^{-1}\), and cannot be made either by a unitary change of basis.

[J24, §2.2, (3); §3.2] represents multiplication by the real spectral variable,
\[
 (\mathcal J f)(s)=s f(s)\quad\text{on }L^2(\mathbb R,d\mu_S),
 \qquad d\mu_S(s)=\left|\prod_{v\in S}L_v(1/2-is)\right|^2ds.
\]
The measure is even, positive on all of \(\mathbb R\), and has finite moments. The Jacobi diagonal is zero. The moment and Jacobi q-series belong to this scaling-generator problem.

**Proof of incompatibility.** The normalized constant polynomial \(p_0\) satisfies
\(\langle p_0,\mathcal Jp_0\rangle=0\) by evenness. In contrast,
\(\langle x,Gx\rangle\ge g_-\|x\|^2>0\) and
\(\langle x,G^{-1}x\rangle\ge g_+^{-1}\|x\|^2>0\) for nonzero \(x\).
A unitary identification would contradict this on \(p_0\). Independently, \(\mathcal J\) is unbounded with spectral support \(\mathbb R\); both proposed targets are bounded and strictly positive. ∎

A spectral representation of translations might eventually use a scaling generator, but it would also have to represent the **noncommuting Sonin cutoff \(P_0\)** and the compressed inverse. The moment theorem does not supply that crosswalk. Nor does a ring of formal series coefficients imply that evaluating an infinite series at \(q=1/2\), or integrating an arbitrary smooth test, produces a finite element of that ring.

This refutes the literal identification in [SW, C3] and Q1(b). It does not refute [J24] or every possible future use of its spectral model. The claimed automatic removal of implementation A/B's carrier error is rejected. [ABSTRACT][PAPER]

### B3. A two-sided certificate that accounts for the *full* carrier residual

**Lemma 5 — full-residual trace sandwich. [ABSTRACT][PAPER]** Let \(F\) be a finite-rank orthogonal projection on the actual \(\mathcal H_0\), and set
\[
 G_F=FGF|_{F\mathcal H_0},\quad C=C_v,\quad
 Y=F G_F^{-1}F C^*,\quad R=C^*-GY.
\]
Here \(F G_F^{-1}F\) means extension by zero outside \(F\mathcal H_0\). Define
\[
 b_F(v)=\operatorname{Tr}(CF G_F^{-1}FC^*),\qquad
 \rho_F(v)=\|R\|_{HS}^2.
\]
Then
\[
 \boxed{n(v)=b_F(v)+\operatorname{Tr}(R^*G^{-1}R),}\qquad
 \boxed{b_F(v)+g_+^{-1}\rho_F(v)
 \le n(v)\le b_F(v)+g_-^{-1}\rho_F(v).}                           \tag{13}
\]

**Proof.** \(FR=0\) by the Galerkin equation. Also
\[
 \operatorname{Tr}(CY)=\operatorname{Tr}(Y^*C^*)
 =\operatorname{Tr}(Y^*GY)=b_F(v).
\]
Expanding \(R^*G^{-1}R\) therefore gives
\(\operatorname{Tr}(CG^{-1}C^*)-2b_F+b_F=n(v)-b_F\).
The operator inequalities \(g_+^{-1}I\le G^{-1}\le g_-^{-1}I\), applied to the Hilbert–Schmidt map \(R\), give the sandwich. ∎

This is stronger than treating \(G_F^{-1}\) as an approximation without a tail. It provides both a lower and an upper envelope in the correct direction.

For an orthonormal basis of \(F\mathcal H_0\), let
\[
 H_v=FC^*CF,\quad D_F=FG^2F|_{F\mathcal H_0},\quad
 m(v)=\|C\|_{HS}^2=n_\infty(Bv).
\]
The finite formula for the residual is
\[
 \rho_F(v)=m(v)-2\operatorname{Tr}(G_F^{-1}H_v)
       +\operatorname{Tr}(G_F^{-1}D_FG_F^{-1}H_v).                 \tag{14}
\]
It follows by expanding \(\|C^*-GY\|_{HS}^2\). Importantly,
\[
 \boxed{D_F=FG^2F\ne(FGF)^2\quad\text{in general}.}
\]
The former includes the excursion into the omitted carrier.

**Mandatory residual plant.** Take
\[
 G=\begin{pmatrix}1&1/2\\1/2&1\end{pmatrix},\quad
 F=\begin{pmatrix}1&0\\0&0\end{pmatrix},\quad C^*=\binom10.
\]
Exact arithmetic gives
\[
 G_F=1,\quad b_F=1,\quad R=\binom0{-1/2},\quad
 \rho_F=1/4,\quad D_F=5/4,\quad n=4/3.
\]
Using \(D_F=G_F^2\) instead would report zero residual and the false value \(n=1\). The false upper certificate \(1-n\ge0\) has the exact upper bound \(-1/3<0\). This kills that compressed-residual implementation, not the source phase inequality. [FINITE_CELL][PAPER]

### B4. Finite computation, specified without running it

The following transaction has a finite-packet output, not a whole-class output. Its genuinely unprovided analytic inputs are explicit.

**Test lock.** For a new packet, choose in advance \(\delta_1=\delta_0/2\) and
\[
 \eta(x)=
 \begin{cases}
 \exp\!\bigl(-1/(1-(x/\delta_1)^2)\bigr),&|x|<\delta_1,\\
 0,&|x|\ge\delta_1,
 \end{cases}\qquad
 h_j=(\partial_x^2-1/4)(x^j\eta),\quad v_j=A_-h_j.
\]
Start with \(j=0,1\). Their support is compactly contained in \((-\delta_0,\delta_0)\), as the literal test class requires. Both moments vanish by two integrations by parts; the packet admits arbitrary complex coefficients. This explicitly defined bump is **not claimed byte-identical to the observer's earlier bump normalization**. Reproducing that exact diagnostic instead requires its source definition, not a fit to the reported norm. A flat bump whose support reaches \(\pm\delta_0\) is not literally in \(C_c^\infty(-\delta_0,\delta_0)\); admitting such a diagnostic to this open-interval class requires a separate smooth-approximation/continuity argument. The narrower new packet avoids that ambiguity.

**Carrier lock.** Construct \(P_0\) from (6). For example, project a predeclared linearly independent finite set of compact carrier functions by \(P_0\), prove its Gram matrix positive, and orthonormalize with that exact Gram matrix. This defines \(F\) on \(\mathcal H_0\). A finite Fourier-grid vector satisfying an approximate cutoff equation is not automatically in \(\mathcal H_0\).

**Matrices to enclose.** In these coordinates compute \(G_F\), \(D_F\), and \(H_v\). Compute the archimedean tested trace \(m(v)=n_\infty(Bv)\), and the geometric form \(L_2(v)\) from (1). Formula (14) gives \(\rho_F(v)\). Polarize these quadratic forms to obtain packet matrices \(\mathbf B_F,\mathbf R_F,\mathbf L\) and the physical packet Gram matrix \(\mathbf H\). Off-diagonal entries are mandatory.

A script can organize the exact operations as follows; each `enclose` call must carry a proved remainder, not an estimated convergence error:

```text
freeze h[0], h[1], v[0], v[1], carrier functions, and precision budget
prove pole_null(h[j]) and exact carrier Gram positivity
build source P0, J, G, F
Gf = enclose(F*G*F)
Df = enclose(F*G*G*F)                 # NOT Gf*Gf
for v in the complex-polarization tests of (v[0], v[1]):
    Hv = enclose(F*C_v^*C_v*F)
    m  = enclose(HS_norm_squared(T_(Bv)*P0))
    b  = trace(inverse(Gf)*Hv)
    rho = m - 2*b + trace(inverse(Gf)*Df*inverse(Gf)*Hv)
    l  = enclose(L2(v))
assemble packet matrices L, B, R and physical Gram H
form lower and upper margin envelopes by (15)
return signed packet result, all residual budgets, and uncovered domains
```

The symbols are literal definitions: for example, `Gf` means \(G_F\) on the chosen carrier, and `v[0]` means \(A_-(\partial_x^2-1/4)\eta\). No user-supplied path or parameter is hidden in the pseudocode.

After incorporating outward-rounding, quadrature, prolate truncation, and carrier errors in **matrix** envelopes, the exact target bracket is
\[
 \underbrace{\mathbf L-\mathbf B_F-g_-^{-1}\mathbf R_F}_{\text{lower margin}}
 \ \preceq\ \mathbf L-\mathbf N\ \preceq\
 \underbrace{\mathbf L-\mathbf B_F-g_+^{-1}\mathbf R_F}_{\text{upper margin}}.
                                                                    \tag{15}
\]
An error \(\varepsilon\|v\|_2^2\) is represented by \(\varepsilon\mathbf H\), not by \(\varepsilon I\) unless the test coordinates are orthonormal. Entrywise interval bounds must be converted to a valid quadratic-form envelope.

**Acceptance.** A certified lower margin matrix \(\succeq0\) proves the inequality for that packet. A rational coefficient vector with certified upper margin \(<0\) supplies a source-valid counterexample to (12). An interval containing zero proves neither. The **DISCRIMINATOR** is the same vector's geometric value minus the full-residual Sonin bracket, with the error contribution that straddles zero isolated.

**Coverage.** Include both bump endpoints, both translated lobe endpoints, the \(t=0\) archimedean cancellation, both ends of each correlation interval, the exact prime translation \(a\), physical cutoff \(u=1\), and the omitted physical/Fourier carrier. On this packet no higher power of 2 is active. Formula (14) still requires a rigorous enclosure for the complete archimedean trace \(m\); the q-series ring does not provide one. These source and tail bounds have not been built in this batch. Without them the script must stop as `SOURCE_TRACE_ENCLOSURE_MISSING` rather than print a pass. [FINITE_CELL][CONDITIONAL]

**Universal boundary.** Even a passing packet and vanishing carrier residual for its two tests leave all other \(h\) untouched. A whole-class proof needs, for example, a positive test-space tail and a controlled head–tail Schur complement for the mixed kernel in (12). No such bound is claimed. The finite-stencil obstruction reported in [REQ], whose Lean proof was not rerun here, is not circumvented by calling a finite packet an exhaustion.

## Q1(c) — Both plants, with the conclusions they actually support

**RESULT: OBSTRUCTION_NAMED.**

### C1. False local factor

For the source-locked artificial factor from [ST, (13)–(14)], keep \(n\) unchanged. The added Weil form is
\[
 Q_M(v)=2a\|v\|^2+4a\sum_{j\ge1}\cosh(ja/4)C_v(ja).
\]
For every normalized minus-phase test in (11),
\[
 Q_M(v_h)=-\delta_M,\qquad
 \delta_M=2a(\cosh(a/4)-1)>0,
\]
so
\[
 \boxed{\Delta_{\rm sharp}(h)=\Delta(h)-\delta_M.}                 \tag{16}
\]
This follows directly from \(C_{v_h}(a)=-1/2\) and the support exclusion of all \(ja\), \(j\ge2\). It applies to complex \(h\), not only the real-even slice. [ABSTRACT][PAPER]

A proof of \(\Delta\ge0\) would **not** automatically survive the plant. Classwide survival requires the stronger estimate \(\inf_h\Delta(h)\ge\delta_M\). None is proved. The reported margin near 0.34 suggests survival for that one diagnostic vector after a decrease near 0.021; without an enclosure this is not even a certified finite sign. [REQ; IC] [FINITE_CELL][CONDITIONAL]

The parenthetical inference “survival means archimedean” is not valid. The formula still contains the genuine prime weight \(w\) and the Euler-dependent projector \(JG^{-1}J^*\). Survival means only that the tested direction does not detect this particular modification. It does not remove the prime dependence or establish that the entire phase class survives. No full proof has been produced here whose survival could be asserted.

### C2. Davenport–Heilbronn

There are three distinct questions.

**Projection algebra.** A pair of projections always has a common kernel and an angle decomposition. One may call the corresponding positive tested trace \(N\). This algebra does not identify any arithmetic function. [ABSTRACT][PAPER]

**Arithmetic crosswalk.** The equality of the particular zeta local terms with a tested cutoff trace uses the precise Fourier/Euler intertwiner of [C23] and the trace formula [C26, (22)]. A Davenport–Heilbronn-type function with no Euler product is not supplied with those local factors or with a corresponding \(B\). Keeping the zeta pair therefore keeps the zeta local trace, not a Davenport–Heilbronn Weil form. Defining \(E_{\rm DH}:=N_S-Q_{\rm DH}\) is always possible as bookkeeping, but proves no trace identity or sign. [ABSTRACT][PAPER]

**Sign test.** No exact Davenport–Heilbronn function, completed-function normalization, substitute local operator, or same-test arithmetic dictionary is given in [REQ]. Thus an arithmetic Sonin split of the requested type has not been constructed for that plant, and neither validity nor failure of R1− there has been proved. This is not a theorem that every conceivable such split is impossible. [ABSTRACT][CONDITIONAL]

[A26, §1.4] explicitly states the counting method's robustness to the cited off-line configurations. That supports the limitation of those counting inputs. It does **not** imply that a source-faithful semilocal sign theorem for zeta transfers to Davenport–Heilbronn. The registered compound plant prediction remains unresolved, rather than being scored by a tautologically defined \(E_{\rm DH}\).

## Q1(d) — Adding 3: exact two-lobe and three-lobe contracts

**RESULT: PARTIAL_WITH_PRECISE_REMAINDER.**

Let \(b=\log3\), \(r_3=3^{-1/2}\), and define
\[
 B_{23}=(I-rU_a)(I-r_3U_b),\quad
 G_{23}=P_0B_{23}^*B_{23}P_0|_{\mathcal H_0},\quad
 S_{23}=B_{23}P_0G_{23}^{-1}P_0B_{23}^*.
                                                                    \tag{17}
\]
The proof of Lemma 1 applies with
\[
 [(1-r)(1-r_3)]^2I\le G_{23}\le[(1+r)(1+r_3)]^2I.
\]
Thus \(n_{23}(v)=\|T_vS_{23}\|_{HS}^2\ge0\) still exists. Positivity of the Sonin energy does not break. [C23; same proof] [ABSTRACT][PAPER]

On arbitrary tests of support diameter **strictly below \(\log5\)**, the exact local arithmetic form is
\[
 L_{23}(v)=\mathcal D(v)-c_A\|v\|^2
 -2\left[
 \frac{\log2}{\sqrt2}C_v(\log2)
 +\frac{\log3}{\sqrt3}C_v(\log3)
 +\frac{\log2}{2}C_v(\log4)\right].                              \tag{18}
\]
The prime power **4 must be included**. There is no prime atom at \(\log(3/2)\), and none at \(\log6\). At an exact support-diameter endpoint \(\log5\), one must check the correlation at that endpoint; smooth compact support in the closed interval makes it zero. We use the strict inequality to avoid dropping an endpoint without justification.

For \(c=a\) or \(b\), a normalized two-lobe difference with the same narrow \(h\) requires
\[
 n_{0,23}(h)-\nu_{c,23}(h)
 \le A_0(h)+J_c(h)+w_c,
 \quad w_a=\frac{\log2}{\sqrt2},\quad w_b=\frac{\log3}{\sqrt3}.      \tag{19}
\]
Here \(J_c=H^{-1}\int_0^\infty a_\infty(t)C_h(t-c)dt\) on the real-even slice. The separation and narrow supports exclude the other prime atoms in each of these two classes.

**An earlier new obligation appears before three lobes.** A proof for \(S=\{\infty,2\}\) does not give (19), even at separation \(a\): the projector has changed. For that test, the arithmetic form is unchanged, and the exact transfer requirement is
\[
 n_{23}(v)-n_2(v)\le L_2(v)-n_2(v).                              \tag{20}
\]
An invertible Euler map is not an isometry and supplies no such inequality by itself. This is the first new quantitative comparison; it is not a loss of positivity of \(n_{23}\).

### The smallest three-lobe space containing the two difference classes

For real even pole-null \(h\), consider
\[
 v=c_0h+c_2U_ah+c_3U_bh.
\]
All three lobes are disjoint. Their total diameter is \(b+2\delta_0<\log4\), so the \(4\)-term of (18) vanishes **for this particular class**, not for all windows below \(\log5\).

Define
\[
 d_0=A_0-n_{0,23},\quad
 s_a=J_a+w_a+\nu_{a,23},\quad
 s_b=J_b+w_b+\nu_{b,23},\quad
 s_{b-a}=J_{b-a}+\nu_{b-a,23}.
\]
Then the full three-lobe margin is
\[
 \frac{L_{23}(v)-n_{23}(v)}H
 =\begin{pmatrix}\overline c_0&\overline c_2&\overline c_3\end{pmatrix}
 \begin{pmatrix}
 d_0&-s_a&-s_b\\
 -s_a&d_0&-s_{b-a}\\
 -s_b&-s_{b-a}&d_0
 \end{pmatrix}
 \begin{pmatrix}c_0\\c_2\\c_3\end{pmatrix}.                     \tag{21}
\]

**Proof.** Expand each quadratic form. The diagonal is \(A_0-n_{0,23}\). For lobes separated by \(c>2\delta_0\), the archimedean cross coefficient is \(-J_c\); an active prime translation contributes \(-w_c\); the Sonin form contributes \(+\nu_{c,23}\) before subtraction. Only \(a,b,b-a\) occur, and \(b-a\) is not a prime-power logarithm. This proves (21). ∎ [ABSTRACT][PAPER]

Requiring (21) nonnegative for **all** \((c_0,c_2,c_3)\) means positivity of the displayed \(3\times3\) matrix. This is a stronger, separate assertion.

The minimal linear three-lobe class generated by the two minus directions has \(c_0+c_2+c_3=0\). This is an explicit restriction, not an implicit definition of the full three-lobe class. Write \(c=(-x-y,x,y)\). Its exact condition is
\[
 \begin{pmatrix}
 2(d_0+s_a)&d_0+s_a+s_b-s_{b-a}\\
 d_0+s_a+s_b-s_{b-a}&2(d_0+s_b)
 \end{pmatrix}\succeq0.                                         \tag{22}
\]
Thus the two individual minus inequalities must be supplemented by
\[
 \boxed{4(d_0+s_a)(d_0+s_b)
 \ge\bigl(d_0+s_a+s_b-s_{b-a}\bigr)^2.}                           \tag{23}
\]
For complex \(h\), use the actual Hermitian mixed entries and the squared modulus of the off-diagonal entry in (22); a real-even \(J_c\ge0\) formula is not available automatically.

For example, a Hermitian \(2\times2\) matrix with diagonal \(1,1\) and off-diagonal \(2\) satisfies both diagonal tests but has value \(-2\) on \((1,-1)\). This is the exact falsifier for inferring the three-lobe statement from its two two-lobe statements. [FINITE_CELL][PAPER]

Neither (20) nor (23) is proved here. A mixed translation at \(\log3-\log2\) for **two fixed primes** is not itself a Hardy–Littlewood prime-pair asymptotic. That analogy does not establish equality of the two obstructions.

## Q2(a) — The window dictionary is real; the single-test identification is not established

**RESULT: PARTIAL_WITH_PRECISE_REMAINDER.**

### E1. Correct variables and the exact full compressed form

In [A26, §2], the window profile \(\psi\) is on \([-1/2,1/2]\), not on the height interval \([T,2T]\). Use its notation
\[
 L=\log(T/(2\pi)),\quad X=e^L,\quad
 \alpha_j=T+2\pi j/L,\quad d=\lfloor LT/(2\pi)\rfloor,
\]
\[
 \phi(u)=\chi(L/2+u)\chi(L/2-u)\sqrt{\psi(u/L)},\qquad
 a_\psi=\|\phi\|_2^2/L.
\]
The source's Fourier convention is \(\widehat f(\xi)=\int f(u)e^{-iu\xi}du\).
Define the following explicit log tests:
\[
 \boxed{f_j(u)=\frac{\phi(u)e^{i\alpha_ju}}{L\sqrt{a_\psi}}.}      \tag{24}
\]
For the two specified profiles, the smooth cutoff gives smooth compact tests. Each has support diameter \(L\). Its convolution square has support in \([-L,L]\), so the largest positive translation is \(L\), and primes/powers stop at \(X\). There is no extra factor of two in that cutoff.

Since \(\phi\) is real and even, \(f_j^\sharp=f_j\), and \(\widehat f_j(\tau)=\widehat\phi(\tau-\alpha_j)/(L\sqrt{a_\psi})\) is real on the real axis. Polarizing the same explicit formula therefore gives
\[
 M_{ij}:=\mathcal Q(f_i,f_j)
 =\frac1{a_\psi L^2}\int_{\mathbb R}
 \widehat\phi(\tau-\alpha_i)\widehat\phi(\tau-\alpha_j)
 \nu_X(\tau)\,d\tau
 =(\widetilde G+\widetilde E_{\rm out})_{ij}.                     \tag{25}
\]
The last equality is [A26, (2.11)]. The exterior-zero matrix is indispensable in an **exact** identity; \(\widetilde G\) only retains the enlarged height interval. This dictionary changes neither measure nor normalization and assumes no reality of zeta zeros. [ABSTRACT][PAPER]

The HS norm here is in the specified coefficient coordinates. Arbitrary Gram whitening would change its numerical value and the normalization of \(R(\psi)\), even though inertia is invariant. Also, these tests generally have nonzero \(A_\pm\). They are not members of (11).

### E2. Exact tensor identity and a counterexample to the universal single-test shortcut

**Lemma 6. [FINITE_CELL][PAPER]** For any Hermitian form \(W\) on a complex vector space \(V\), and any finite family \(f_1,\ldots,f_d\), let \(M_{ij}=W(f_i,f_j)\). In \(V\otimes\overline V\), set
\(\Psi=\sum_i f_i\otimes\overline{f_i}\). Then
\[
 \boxed{\|M\|_{HS}^2=(W\otimes\overline W)(\Psi,\Psi).}            \tag{26}
\]

**Proof.** Define
\(\overline W(\overline x,\overline y)=\overline{W(x,y)}\), and extend the tensor form sesquilinearly. Expanding its value on \(\Psi\) gives
\(\sum_{i,j}W(f_i,f_j)\overline{W(f_i,f_j)}=\sum_{i,j}|M_{ij}|^2\).
No positivity assumption on \(W\) is used. ∎

This is a two-copy form on a two-variable test. It is not \(W(v,v)\) on the original test space. Nor does its nonnegativity on this special \(\Psi\) establish positivity of \(W\) on arbitrary vectors.

**Exact falsifier.** Fix \(f_1=e_1,f_2=e_2\) and
\(W_t=\operatorname{diag}(1,t)\), for \(t=0,1,2\). The HS squares are \(1,2,5\). For any vector \(v=(v_1,v_2)\) determined by this fixed window/basis geometry independently of \(W_t\),
\[
 W_t(v,v)=|v_1|^2+t|v_2|^2
\]
is affine in \(t\). Its second difference is zero, whereas
\(5-2\cdot2+1=2\). No universal form-independent single-test map can realize (26) as an original one-copy form. This plant even uses positive semidefinite forms. [FINITE_CELL][PAPER]

**Scope of the refutation.** It does not exclude a specially constructed, nonlinear, zeta-dependent \(v\). A scalar rescaling using an already known positive direction and the already computed HS square can manufacture such an equality; it would merely re-encode the answer. No source-specific non-tautological construction of that sort is established here. Accordingly the literal existential version of the observer's prediction is not scored as mathematically false.

[L26, Proposition 2.1 and its proof] provides an independent type check: with its \(2\pi\)-Fourier convention it uses \(K=\widehat{\eta^2}\), and its double zero sum is represented by an \(L^2\)-square of a **two-variable** function. It does not identify that quantity with one original Weil square. The notation is \(\widehat{\eta^2}\), not \((\widehat\eta)^2\). [ABSTRACT][PAPER]

Finally, “\(R(\psi)N-\text{something}\)” does not specify a functional. The exact trace/rank terms and exterior error must be fixed before asking for its representation. The listed method is a pair-correlation/second-moment method; no Levinson–Conrey mollifier error is defined by (25).

## Q2(b) — Entrywise Sonin split; where the new prime-pair problem remains

**RESULT: OBSTRUCTION_NAMED.**

For a finite smooth family such as (24), let \(S\) contain every prime \(p\le X\), with cutoff product one. Polarization of the semilocal trace identity gives
\[
 \boxed{M=\mathbf N_S-\mathbf E_{\rm angle}+\mathbf P_{02},}
 \qquad
 (\mathbf N_S)_{ij}=\langle T_{f_i}\mathsf S_S,
                                    T_{f_j}\mathsf S_S\rangle_{HS},
                                                                    \tag{27}
\]
where \(\mathbf P_{02}\) is the pole pairing and has rank at most two. It need not be positive. Combining with (25),
\[
 \boxed{\widetilde G=
 \mathbf N_S-\mathbf E_{\rm angle}+\mathbf P_{02}
                    -\widetilde E_{\rm out}.}                    \tag{28}
\]
The angle remainder and the discarded-zero remainder are different objects. The source intertwiner and smoothing argument extend to a fixed finite set of primes by taking products of the bounded invertible Euler factors. This proves the finite entrywise decomposition, not a bound uniform in \(T\) or \(|S|\). [C23; C26; Lemma 1] [ABSTRACT][PAPER]

Set \(A=\mathbf N_S+\mathbf P_{02}\) and
\(D=\mathbf E_{\rm angle}+\widetilde E_{\rm out}\). The exact square is
\[
 \|\widetilde G\|_{HS}^2
 =\|A\|_{HS}^2+\|D\|_{HS}^2
       -2\operatorname{Re}\operatorname{Tr}(A^*D).               \tag{29}
\]
Thus the prime off-diagonal second moment is not simply a linear piece of \(\mathbf E_{\rm angle}\). It belongs to the tensor expansion of the complete expression, including cross terms.

To see the arithmetic issue directly, expand a prime Dirichlet polynomial. Its difference-frequency terms contain
\[
 \sum_{\substack{n,m\le X\\n\ne m}}
 \frac{\Lambda(n)\Lambda(m)}{\sqrt{nm}}
 \int_T^{2T}e^{it\log(n/m)}\,dt,\qquad
 \int_T^{2T}e^{it\omega}dt
 =\frac{e^{2iT\omega}-e^{iT\omega}}{i\omega}.                    \tag{30}
\]
The integral has modulus at most \(\min(T,2/|\omega|)\). When \(X\) exceeds the height scale, near pairs with \(|n-m|\lesssim n/T\) enter without strong oscillatory suppression. Window smoothing changes the weight but retains the joint arithmetic dependence. This is the type of term discussed at the support boundary in [A26, §5]. [ABSTRACT][PAPER]

The Sonin substitution has not bounded (30). Expanding its many-prime \(B_S\), or its compressed inverse inside (29), also introduces products of translation weights. An identity between these representations is not cancellation or a second-moment estimate.

There is an additional uniformity problem. The elementary inverse estimate is only
\[
 G_S\ge \left(\prod_{p\in S\setminus\{\infty\}}
                         (1-p^{-1/2})\right)^2 I.                \tag{31}
\]
It is not a uniform positive constant along growing prime sets. Using it in an absolute norm estimate can discard exactly the cancellation the second moment needs. For \(X>T\), retaining only primes \(\le T\) would additionally omit active arithmetic terms.

**Precise unresolved demand.** Supply a bound for the window-weighted off-diagonal bilinear sum at the enlarged \(X\), or an equally strong combined bound for the three terms in (29), with its error small enough for the intended rank–trace gain. No such supplier is produced here. Full Hardy–Littlewood would be a possible kind of additional information; these identities do not prove that it is logically necessary, or that no weaker averaged estimate can suffice. The frozen prediction asserting that the projector *needs the same input* therefore remains unresolved. [COFINAL_FAMILY][CONDITIONAL]

## Q2(c) — Correct constants and the cheapest decisive check

**RESULT: COMPUTATION_SPECIFIED.** No numerical run is needed for the first checks.

For the profiles in [A26, §5], the normalized functional is
\[
 R(\psi)=\frac{\displaystyle\int_{-1/2}^{1/2}\psi(u)^2du
 +\displaystyle\iint_{[-1/2,1/2]^2}|u-v|\psi(u)\psi(v)dudv}
 {\left(\displaystyle\int_{-1/2}^{1/2}\psi(u)du\right)^2}.
                                                                    \tag{32}
\]
For \(\psi_0=1\), the two numerator terms are \(1\) and \(1/3\), while the denominator is one. Thus \(R(\psi_0)=4/3\).

For \(\psi(u)=\cos(\sqrt2u)\), put
\(F(u)=\psi(u)+\int_{-1/2}^{1/2}|u-v|\psi(v)dv\).
On the interval, \(F''=\psi''+2\psi=0\). Evenness makes \(F\) constant. With \(t=1/\sqrt2\), evaluation at \(u=1/2\) gives
\[
 F=\cos t+\frac{\sin t}{\sqrt2},\qquad
 \int\psi=\sqrt2\sin t.
\]
The numerator of (32) equals \(F\int\psi\), hence
\[
 \boxed{R(\psi_{MT})=\frac12+\frac1{\sqrt2}\cot\frac1{\sqrt2}.}    \tag{33}
\]
The request includes an extra factor \(1/2\) on the cotangent term. That would imply a proportion greater than one after the displayed \(2-R\) step; it is not the source constant. Equation (33) also agrees with the complement of the constant in [L26, (1.1)]. [ABSTRACT][PAPER]

**What agreement can decide.** Reproducing (32)–(33) checks the window and normalization dictionary. It cannot establish a one-test representation of an HS square. Furthermore, \(R(\psi)\) is an asymptotic coefficient: exact equality to a finite matrix's HS square divided by \(N(T,2T)\) is not expected without finite-error terms.

**The cheapest actual discriminator** is the exact second difference in Lemma 6: \(2\) for the HS-square functional and \(0\) for every form-independent single-test pullback. That decides the universal structural assertion before a large matrix is computed.

For a finite source implementation, the correct paired check is instead
\[
 D_{\rm tensor}=\|M\|_{HS}^2
 -(\mathcal Q\otimes\overline{\mathcal Q})(\Psi,\Psi)=0,
 \quad M_{ij}=\mathcal Q(f_i,f_j),                                \tag{34}
\]
using exactly the same family and coefficient normalization on both sides. If comparing \(\widetilde G\) rather than \(M\), also include \(\widetilde E_{\rm out}\). Formula (34) is proved algebraically; its numerical use is an implementation falsifier, not new evidence for the sign in (12).

There is no valid single scalar whose agreement with \(4/3\), without a specified \(v\) and a proved finite-error dictionary, decides the literal existential question Q2(a). That requested decision criterion is rejected, not silently replaced by an asymptotic fit.

## 3. Route map and alternative representations

| Representation | What it changes | Decisive falsifier or acceptance test | Estimated kill power / cost | Status and tags |
|---|---|---|---|---|
| Full-residual Sonin Gram, (13)–(15) | Keeps the true carrier inverse and makes its error a positive residual trace | The exact 2×2 excursion plant; then a signed source packet envelope | 9/10 / 5/10 | Selected finite preflight; source enclosures absent. [FINITE_CELL][CONDITIONAL] |
| Direct mixed-kernel test-space form, (8), (12) | Keeps prime/archimedean/mixed cancellation before any operator-norm bound | Positive test-space tail plus a nonnegative head–tail Schur complement; a negative rational direction refutes the target | 10/10 / 8/10 | Candidate whole-class route; tail and complement estimate unproved. [ABSTRACT][CONDITIONAL] |
| Tensor second-moment dictionary, (26)–(29) | Moves the HS square to the correct two-copy space | Exact second-difference plant and preservation of pole/exterior terms | 10/10 / 1/10 for the type audit | Dictionary proved; no new prime-pair estimate. [ABSTRACT][PAPER] |

The estimates describe decision value and implementation difficulty, not probabilities of proving R1−. No escalated computation is authorized by these estimates.

## 4. Frozen prediction scoring and new registration

The observer's names and probabilities are unchanged. “Not achieved in this batch” is a score of a proof-attempt event, not evidence that the underlying theorem is false.

| Frozen prediction | p | Fate | Scope of the score |
|---|---:|---|---|
| P_8_PROVED_ON_CLASS | 0.20 | NOT_ACHIEVED_IN_THIS_BATCH | No proof of (12); no mathematical refutation. |
| P_8_PROVED_ON_SUBCLASS | 0.30 | NOT_ACHIEVED_IN_THIS_BATCH | No explicit infinite-dimensional subclass has received a sign proof. Defining a subclass by the desired inequality would not count. |
| P_NU_A_HAS_EXPLICIT_KERNEL | 0.55 | CONFIRMED_WITH_KERNEL_TYPE_EXPLICIT | Lemma 2 gives a tested distributional kernel from the cosine compression, translated modes, and the Euler multiplier; not a pointwise scalar series. |
| P_CCM_QSERIES_IS_OUR_GRAM | 0.60 | REFUTED | Lemma 4 gives an exact operator incompatibility with the literal claim. |
| P_DH_PLANT_KILLS_IDENTIFYING_CLAIM | 0.50 | UNRESOLVED | The required arithmetic DH split and its phase sign are not supplied. A tautological split does not test this compound event. |
| P_CROSSWALK_A_YES | 0.35 | UNRESOLVED_AS_LITERAL_ZETA_SPECIFIC_EXISTENTIAL | The universal form-independent version is refuted; the correct tensor identity is proved. No broader nonexistence claim is inferred. |
| P_CROSSWALK_B_NEEDS_HL | 0.70 | UNRESOLVED | A growing-set correlation bound is missing; necessity of Hardy–Littlewood is not proved. |

**Own predictions registered in the conversation before these tests:** “the mixed term admits a kernel formula” is confirmed by Lemma 2. “The claimed Hilbert–Schmidt-to-single-test identification fails” is **not fully confirmed as phrased**: only the universal form-independent reading has been refuted. The zeta-specific existential reading remains unresolved. No probability was assigned to either, and none is retroactively added. [ABSTRACT][PAPER]

**New prospective registration, not scored here:**

```yaml
P_PHASEPROOF_SOURCE_PACKET_MINUS_MARGIN_POSITIVE:
  probability: 0.70
  exact_event: >-
    A complete source-valid enclosure for the previously registered observer
    h=(partial^2-1/4)eta_delta0 reports a strictly positive minus-phase margin.
  prerequisite: Recover and freeze the exact earlier eta definition; no substitute bump.
  failure_or_nonresolution: >-
    An unclosed carrier/trace budget leaves this event unscored; a certified
    nonpositive result refutes it.
  evidence_known_at_registration: The approximate minus margin reported in REQ.
  blind_prediction: false
P_PHASEPROOF_FULL_RESIDUAL_PLANT_ACCEPTED_BY_INDEPENDENT_CHECKER:
  probability: 0.98
  exact_event: >-
    An independent checker reproduces n=4/3, b=1, rho=1/4 for the displayed
    2x2 plant and rejects replacing FG^2F by (FGF)^2.
  outcome_in_this_session: not_run_independently
```

These registrations do not permit modifying the old probabilities or replacing the whole-class event by a favorable finite test.

## 5. Strongest attack and exact kill boundaries

**The strongest mathematical objection is unchanged:** SEMITABLE (8) asks for a sign on every admissible test. An explicit kernel and a finite-packet sandwich do not supply that sign. Lemmas 1–5 remove the carrier ambiguity and give honest one-sided error accounting; they do not close (12). No proof-completeness label is assigned to Q1.

| Rejected assertion | KILL_SCOPE | KILL_EVIDENCE_KIND | Exact evidence | What is not killed |
|---|---|---|---|---|
| Literal q-series Jacobi operator equals \(G\) or \(G^{-1}\) | THEOREM_SHAPE | PROVED_INCOMPATIBILITY | [J24, v1, (3), §3.2]; Lemma 4, zero constant-vector quadratic value versus strict positive floor | The moment paper; a new explicit functional-calculus/cutoff crosswalk |
| Compressed residual is the full inverse error | THEOREM_SHAPE | EXACT_COUNTEREXAMPLE | Lemma 5 plant: omitted excursion changes \(n\) from alleged 1 to \(4/3\) | Full-residual method; SEMITABLE (8) |
| Universal form-independent one-test realization of an HS square | THEOREM_SHAPE | EXACT_COUNTEREXAMPLE | Lemma 6: second difference 2 versus 0 on \(W_t=\operatorname{diag}(1,t)\) | Zeta-specific nonlinear constructions; tensor representation |
| Two minus diagonal tests imply three-lobe positivity | THEOREM_SHAPE | EXACT_COUNTEREXAMPLE | §Q1(d): matrix with diagonal 1 and off-diagonal 2; upper value \(-2\) on \((1,-1)\) | Additional determinant condition (23) |

All these statements have scope [ABSTRACT][PAPER], except the displayed finite plants [FINITE_CELL][PAPER]. No `ROUTE_FAMILY` death is asserted. Absence of a source, missing tail estimates, and failure to obtain a proof remain research debt.

## 6. Dependency epistemics — consumer-first audit

```yaml
DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
ACTUAL_CONSUMER_REQUIREMENT: >-
  Q(v) >= 0 for every complex smooth compact log test, with the exact
  measure, convolution involution, pole terms, and arithmetic local factors.
ORIGINAL_REQUESTED_OBJECT: >-
  n(A_minus h) <= L2(A_minus h) on the one-prime pole-null phase class,
  together with a one-test identification of the two-thirds second moment.
ORIGINAL_OBJECT_IS: NOT_NECESSARY
WHY: >-
  The consumer does not require a Sonin minorant or a second-moment
  representation. The one-prime phase class alone also does not cover its
  full quantifier.
KNOWN_WEAKER_INTERFACES:
  - Z: Direct Q(v) >= 0 for every full-class test.
    Z_IMPLIES_Y: Identity of the consumer requirement.
  - Z: >-
      For every fixed full-class v, source-faithful lower bounds
      Q(v) >= -epsilon_j(v) with epsilon_j(v) >= 0 and epsilon_j(v) -> 0.
    Z_IMPLIES_Y: Take the limit separately for each fixed v.
  - Z: >-
      Nonnegative Q on a dense smooth-test family on each compact support,
      with continuity in the exact Weil-form topology and support exhaustion.
    Z_IMPLIES_Y: Pass to each fixed-test limit, then exhaust supports.
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
NOVELTY_AXIS: >-
  Retain the mixed translation kernel and the complete Galerkin excursion;
  identify the second moment on the tensor, rather than one-copy, space.
REOPEN_TRIGGERS:
  INEQUALITY_8: >-
    A source-valid lower margin for the full test-space operator in (12),
    or a precise coercive-tail/Schur argument covering every admissible h.
  FINITE_PACKET: >-
    Certified P0 carrier membership, tested archimedean trace enclosure,
    ambient FG^2F, and all outward error budgets in (15).
  QSERIES_AS_TOOL: >-
    An explicit representation of P0 and the compressed inverse in the
    moment spectral model, not identification of the Jacobi generator with G.
  DH_PLANT: >-
    Specify the completed DH function and an exact arithmetic trace
    crosswalk to a declared projection pair, then test the same phase class.
  SECOND_MOMENT_GAIN: >-
    A window-weighted growing-X correlation estimate or a combined bound
    for (29) retaining all pole and exterior terms.
  SINGLE_TEST_EXISTENTIAL: >-
    Exhibit a non-tautological source-specific v and prove the exact
    equality, including its dependence on the original Weil form.
MATHEMATICALLY_DEAD:
  - Only the four exact theorem shapes with evidence in section_5.
SCOPE: ABSTRACT
VERIFIER: PAPER
```

## 7. One bounded directive and validation gate

**CODEX DIRECTIVE — prepare one source-locked full-residual certificate for the frozen minus-phase test; do not run a larger sign table.**

The downstream local consumer is the inequality \(\Delta(h)\ge0\) for that exact test. Use Lemma 5, preserve the exact observer bump and pole-null construction, verify literal open-interval class membership or its explicit continuity extension, and return the lower and upper margins with all source-carrier and tested-trace errors exposed. First reproduce the exact 2×2 excursion plant. Use (14), never a residual projected back into \(F\mathcal H_0\). If the archimedean trace or carrier enclosure is unavailable, return its precise missing bound and `SOURCE_TRACE_ENCLOSURE_MISSING`; do not replace it with a q-series Jacobi matrix or a grid-convergence estimate.

This document specifies the follow-up; it performs no run, starts no observer process, authorizes no Lean edit, and changes no physical bus or shared state. The allowed success is **one finite-test theorem** from a certified nonnegative lower margin. A strictly negative certified upper margin is a source-test counterexample. A straddling bracket is inconclusive and must name the dominant remainder. Neither outcome is a whole-class verdict unless the negative witness itself refutes that universal claim. [FINITE_CELL][CONDITIONAL]

**Lean-ready mathematical interfaces, not source submissions:**

```text
sonin_image_projection:
  bounded J, J*J >= g_minus*I > 0
  => orthogonal_projection(range J) = J*(J*J)^(-1)*J*

full_residual_trace_sandwich:
  0 < g_minus*I <= G <= g_plus*I,
  F finite orthogonal projection, C Hilbert-Schmidt,
  Y = F*(FGF)^(-1)*F*C*, R = C* - G*Y
  => Tr(C G^(-1) C*) = Tr(CY) + Tr(R* G^(-1) R)
  and the two bounds (13)

finite_hermitian_hs_tensor_identity:
  Hermitian W, finite family f
  => HS_norm_squared(matrix(W,f)) =
     (W tensor conjugate(W))(sum f_i tensor conjugate(f_i), same)
```

These describe already proved paper statements. They are not asserted to be elaborated Lean signatures or existing declaration names. No `sorry`, new axiom, or theorem weakening is proposed.

## 8. Meta closeout and publication handoff

**What became smaller?** The mixed term has an explicit source-defined tested kernel. The inverse-carrier discrepancy is represented by a positive full-residual trace with an exact two-sided budget. The three-lobe extension is a specific Hermitian determinant condition. The second-moment crosswalk is placed in a tensor square with the pole and exterior corrections retained.

**What was killed?** The literal q-series/Gram identification, compressed-residual substitution, universal form-independent one-test shortcut, and diagonal-only three-lobe inference. Nothing here kills the original phase inequality or the full Weil route.

**What must not recur?** Inferring signs from norms of \(B\); summing a bare non-HS semilocal angle; changing the observer's bump while scoring its prediction; treating a coefficient ring as an operator identification; deleting \(4\) on all windows below \(\log5\); conflating \(E_{\rm angle}\) with \(E_{\rm out}\); using a single matching \(R\)-constant to certify a functional identity; calling lack of a bound a proof that Hardy–Littlewood is necessary.

**Smallest current sign gap:** (12), or equivalently its mixed threshold (3), with the stated full complex test domain and zero negative budget. The cheapest source-changing check is a complete finite-test residual enclosure, not an increased grid with the same unbounded carrier error.

```yaml
PROGRESS_CLASS: REPRESENTATION_PROGRESS
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
ROUTE_SCORE: 4
STRATEGY_MEMORY:
  target: SEMITABLE_INEQUALITY_8_AND_SECOND_MOMENT_CROSSWALK
  status: OPEN
  failed_strategy: IDENTIFY_JACOBI_GENERATOR_WITH_SONIN_IMAGE_GRAM
  cognitive_operator_used: REPRESENTATION_SHIFT
  new_gap_name: SAME_SOURCE_MIXED_KERNEL_MARGIN_WITH_COMPLETE_RESIDUAL
  invariant_learned: >-
    Preserve the carrier, the quadratic-versus-tensor degree, and every
    excursion outside a compressed inverse.
  forbidden_future_move: Substitute matching notation or coefficient rings for an intertwiner.
  next_decisive_test: Source-valid finite minus-phase margin using equations_13_to_15.
```

**Publication handoff.** The intended repository path is exactly the `EXPECTED_VERDICT_PATH` in the header. No remote file was written. Commit SHA, remote blob SHA, and branch-update receipt are therefore **absent**, not pending verification of a purported commit. The local artifact contains this entire verdict. An authenticated writer must publish this document without changing closed predecessor verdicts; the commit subject must carry `[Proshka]`. Local availability is not a substitute for the requested remote commit.

No Lean file was written, so no Lean build or axiom-profile result is claimed. A publication check would verify the Markdown bytes and the single changed path; it would not promote any PAPER statement to LEAN or any finite sign to a universal result.

## 9. Sources and exact provenance

**[REQ]** The authoritative 96-line request at commit `e3dba5975b10ba7dbebbdea948612dd830aaf67a`, path, Git blob, and SHA-256 in the header. The UTF-8 bytes were recovered from the GitHub response and independently hashed. The supplied size, newline count, Git blob hash, and SHA-256 all match.

**[PROTO]** `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, fetched from `rh_clean`, Git blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. The source-selected intake and operative-class rules were read; no queue was scanned to select this work.

**[ST]** `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SEMILOCAL_TABLE_PHASE_CLASS_2026-09-06.md`, at the request commit, Git blob `80eb2189b7a9de523fb0aec1bbdaa198bb02bba2`; request-supplied SHA-256 prefix `0054743f1847e2c7`. Relevant sections: phase class (1)–(8), inverse and carrier budgets (9)–(10b), artificial factor (13)–(14), tested-trace domain. Own earlier mathematics is treated as a derivation to recheck, not an axiom.

**[IC]** `docs/routeB_bus/SEMITABLE_INDEPENDENT_CHECK_2026-09-06.md`, same commit; supplied prefix `d13d68bf18bd970c`. Its quadrature and sign reports are not independent interval certificates in this session.

**[SW]** `docs/routeB_bus/litreview/SWEEP_C_FRESH_TOOLS_FOR_INEQUALITY_8_2026-09-06.md`, same commit; supplied prefix `b00d7014bb4f6035`. Card C3's literal operator identification is refuted above. Other speculative tool cards are not imported as positivity theorems.

**[WP]** The WEILPROOF request at `a23dc64d4b94515dc9b24151a65f4b95a8908879`, `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_DIRECT_WEIL_SOURCE_PROOF_2026-09-04.txt`, Git blob `6f60ccbee0d64461ca423e1ecb75c7242abfc7c6`; proof-construction rules and prohibitions read. The corresponding verdict commit `b8b0dc95584907078745bbb5576503268065b1e2` was fetched to resolve provenance, not used as a substitute for the sign proof.

**[C20]** Connes–Consani, arXiv:**2006.13771v1**, 57-page version, §4 and Appendix D, especially the prolate/cutoff decomposition and the half-line convolution commutator lemma. Used for the archimedean model and tested trace domain, not a semilocal phase sign theorem.

**[C23]** Connes–Consani–Moscovici, arXiv:**2310.18423v2**, (57)–(59), Theorem 4.6, printed pp.22–23. Supplies the finite Euler map between Sonin spaces. The map is bounded and invertible, not asserted isometric.

**[C26]** Connes, arXiv:**2602.04022v1**, (22), printed p.32. Supplies the finite-place cutoff trace formula with its contact term. The pole correction is not included in its local sum and is retained separately here.

**[J24]** Connes–Consani–Moscovici, arXiv:**2403.01247v1**, *On q-series and the moment problem related to local factors*, §2.2, (3), and §3.2–3.3. This is the moment/Jacobi/scaling-generator source, not the compressed Sonin-image Gram source.

**[A26]** Claude/Anthropic, *More than two thirds of the zeta zeros are simple and on the critical line*, 17-page primary PDF dated 11 August 2026, CDN document identifier `95c246936988e43127bc6b2ceb7077c1dad2d68e.pdf`. Relevant locations: §1.4; §2.2–2.3, (2.7)–(2.11); §5 and its support-range limitation. The identifier is a locator, not a hash verified in this session.

**[AF26]** Alpöge–Furman, arXiv:**2608.13637v1**. This is the separate arXiv paper named by the request; it is not byte-identical to [A26]. The explicit window and finite normalization formulas used in (24)–(25) are pinned to [A26], rather than transplanted between versions.

**[L26]** Lamzouri, arXiv:**2609.02882v1**, *A new proof that more than 2/3 of the zeros of the Riemann zeta function are simple and on the critical line*, (1.1), Proposition 2.1, and its two-variable Hilbert-space proof. Used as an independent check of the constant and tensor type, not as a Sonin mixed-term bound.

Primary PDFs were opened online, and relevant displayed formulas were visually checked where accessible. No repository PDF was claimed byte-matched to an online PDF. Shelf checksum prefixes, other than the authoritative request's complete hash, were not independently recomputed. No Lean source, external verification pipeline, or numerical experiment was executed.
