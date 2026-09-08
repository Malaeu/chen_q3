# STATUS: TRY_DISTINCT_ZERO_INERTIA_AND_TARGET_IDENTIFICATION
```yaml
OPERATIVE_CLASS: TRY_DISTINCT_ZERO_INERTIA_AND_TARGET_IDENTIFICATION
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-08-SCREW
ADDENDA: [SIGNATURE, CLOSURE]
BOUNDARY_ID: GOAL058_ZERO_SIDE_QUOTIENT_VERSUS_SUZUKI_CANONICAL_SYSTEMS
ARTIFACT_KIND: APPEND_ONLY_SUPPLEMENT
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  SIGNATURE_1: PROVED_ON_CLASS
  SIGNATURE_2: PROVED_ON_CLASS
  SIGNATURE_3: PROVED_ON_CLASS
  SIGNATURE_4: PARTIAL_WITH_PRECISE_REMAINDER
  CLOSURE_1: PARTIAL_WITH_PRECISE_REMAINDER
  CLOSURE_2: PARTIAL_WITH_PRECISE_REMAINDER
  CLOSURE_3: PROVED_ON_CLASS
SOURCE_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  SIGNATURE:
    PATH: docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_SCREW_SIGNATURE_2026-09-08.md
    COMMIT: 430905611d3c6a130c34314ffbafa0f73bae4ba3
    GIT_BLOB: f66090b80efb877c1191a81631cf7af69ad269f5
    SHA256: 4a81f33292f7b9a183859f2d7498a758ba844c2ac517b321b7350db131476b23
    BYTES: 2902
    LINES: 13
    FINAL_LF: true
  CLOSURE:
    PATH: docs/routeB_bus/proshka/PROSHKA_ADDENDUM_GOAL058_SCREW_CLOSURE_2026-09-08.md
    COMMIT: 00dc8e84f349605425c742d613e3dd4a44851f7f
    GIT_BLOB: d92bbfce5c9036e69e48a1c6545de344c6f43f14
    SHA256: 162afea7a0bb78442e6dda825733dab8d600d2e572ef10910ca15a5f15229704
    BYTES: 2433
    LINES: 17
    FINAL_LF: true
  FETCHED_VIA_GITHUB_CONNECTOR: true
  SHA256_AND_GIT_OBJECT_SHA1_INDEPENDENTLY_RECOMPUTED: true
  ALL_CHECKS_MATCH: true
PARENT_VERDICT:
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCREW_2026-09-08.md
  COMMIT: b1e76e520f37b97c35f74dcaea56839ab4d908f3
  GIT_BLOB: 41ec60c8f3f8a1c9b112eba9dca7e0c88c5efa2c
  SHA256: 80dbb8ac5f9b8569be9b5bf3b663916a82d44af8f69bf290d59410d9a25ecd4e
  LOCAL_BYTES_HASH_VERIFIED: true
  MODIFIED: false
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
DECISIONS:
  NEGATIVE_INDEX_COUNTS_DISTINCT_OFF_LINE_J_PAIRS: true
  ZERO_MULTIPLICITY_CREATES_EXTRA_SIGNATURE_DIRECTIONS: false
  POLE_SUMMAND_HAS_SIGNATURE_1_1: true
  POLE_PLANE_IS_A_HYPERBOLIC_SUMMAND_OF_FULL_Q: not_established_and_not_implied
  SUZUKI_SCREW_NORMALIZATION_REMOVES_POLES: false
  WINDOW_NEGATIVE_INDEX_FINITE: true
  WINDOW_NEGATIVE_INDEX_NONDECREASING: true
  SUP_WINDOW_NEGATIVE_INDEX_EQUALS_GLOBAL_NEGATIVE_INDEX: true
  ARGUMENT_PRINCIPLE_FOR_W_COUNTS_NEGATIVE_A_EIGENVALUES: false_without_new_crosswalk
  UNCONDITIONAL_POSITIVE_DDF_COORDINATES_FOR_Q: not_supplied
  ANCHORED_W_NORMALITY_FOLLOWS_FROM_SELF_ADJOINTNESS: false
  SOURCE_EVALUATION_KERNEL_RATIO_NORMALITY_TEST: derived_sufficient_not_necessary
  NORMALIZED_HERGLOTZ_NORMALITY: proved_for_that_distinct_object
  RH_IMPLIES_SPECIFIC_SCREW_FAMILY_IDENTIFICATION: not_proved
  NOT_RH_FORCES_ANY_UNSPECIFIED_SPECTRAL_CONVERGENCE_TO_FAIL: false_as_an_inference
  NOT_RH_FORCES_CORRECT_TARGET_IDENTIFICATION_TO_FAIL: true_under_stated_local_conditions
  ALL_SUPPORT_WEIL_SIGN_PROVED: false
CLOSES: [SCREW_ADDENDUM_SIGNATURE_DICTIONARY, SCREW_ADDENDUM_CLOSURE_LOGICAL_SPLIT]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
SCOPE: ABSTRACT
VERIFIER: PAPER
NEW_DERIVATIONS_INDEPENDENT_REVIEW: pending
LEAN_KERNEL_VERIFIED: false
EXECUTION:
  HASH_CHECKS_ONLY: true
  NUMERICAL_RUN: false
  LEAN_EDIT: false
  EMAIL_ACTION: false
  QUEUE_OR_STATE_EDIT: false
PUBLICATION:
  PATH: docs/routeB_bus/proshka/PROSHKA_SUPPLEMENT_GOAL058_SCREW_SIGNATURE_CLOSURE_2026-09-08.md
  ONLY_THIS_NEW_DOCUMENT: true
  COMMIT_AND_READBACK: delivery_receipt
  COMMIT_IS_NOT_A_PROOF_GATE: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision and evidence boundary

**SIGNATURE is correct after removing multiplicity from the dimension count and separating the pole summand from the full form. CLOSURE correctly withdraws finite-window positivity, but neither anchored normality nor identification of Suzuki's particular approximants is established.** No global sign is proved here.

This is a supplement, not a replacement of SCREW. Both addenda were read in full and their fetched UTF-8 bytes reproduce the supplied hashes. The old verdict and its predictions remain unchanged. The question labels below follow the addenda, not a new queue item.

**Source keys.** [S] is the pinned SCREW verdict above, read locally and blob-checked through GitHub. [K] is the KERNEL verdict at `a367e9e88249b356c33774dc6ce182224c5fc72c`, blob `d171a2fb7b6b917a1780656952b1db5458cc9a34`, especially (K14)--(K23) read through GitHub. [26] is Suzuki, arXiv:2606.09096v2; [23] is arXiv:2301.00421v3; [22] is arXiv:2206.03682v4. The primary-paper locators are listed in Section 10. Mathematical extensions proved below are labelled DERIVATION; they are not silently attributed to the papers.

The old v1 target is inherited from [S,(S25)]. The v2 target is rechecked directly. The Hodge/DDF comparison and the isolated Zhu-certificate reference are RELAY framing, not imported sign theorems or a verified inventory of all known window results. The supplementary HYPERBOLICITY file is not separately adjudicated here. No old conversation export or newly scanned queue is used as a premise.

All proofs below have **[ABSTRACT][PAPER]** scope unless marked COFINAL_FAMILY. PAPER means an analytic derivation awaiting independent review, not a Lean kernel result.

## 1. SIGNATURE-1: the exact inertia counts distinct sampling coordinates

### 1.1 Conventions and the two-dimensional block

Keep the project completion, without silently switching to global unweighted L2:

\[
 \mathscr E=\{f:\mathcal W[f]+\mathcal D[f]<\infty\},\qquad
 \mathcal W[f]=\int e^{2|x|}|f(x)|^2dx,\qquad
 \mathscr H=\ker M_+\cap\ker M_-\subset\mathscr E.
\]

Here \(F_f(z)=\int f(x)e^{zx}dx\), \(M_\pm(f)=F_f(\pm1/2)\), and \(Q\) is the complete geometric form. Let \(Z\) be the set of **distinct** centered zeros of \(\Lambda_\xi(z)=\xi(1/2+z)\), \(m_\lambda\) their multiplicities, and \(j\lambda=-\overline\lambda\). The signed explicit formula on the compact core is

\[
 Q(f,g)=\sum_{\lambda\in Z}m_\lambda
             \overline{F_f(j\lambda)}F_g(\lambda).       \tag{SC1}
\]

[K,(K16)--(K23)] extends the needed pairings and identifies \(\mathcal N=\operatorname{rad}(Q|_{\mathscr H})\) with the pointwise vanishing space. At a fixed point of j, the contribution is \(m_\lambda|F_f(\lambda)|^2\). For a two-element orbit \(\{\lambda,j\lambda\}\), write \(u=F_f(\lambda)\), \(v=F_f(j\lambda)\). Its contribution is

\[
 m_\lambda(\bar vu+\bar uv)
 =m_\lambda\left|\frac{u+v}{\sqrt2}\right|^2
 -m_\lambda\left|\frac{u-v}{\sqrt2}\right|^2.             \tag{SC2}
\]

Thus the matrix is \(m_\lambda\begin{pmatrix}0&1\\1&0\end{pmatrix}\), of inertia (1,1), **not** \((m_\lambda,m_\lambda)\). Repeated zeros repeat the same evaluation functional. There are no derivative/jet coordinates in (SC1). This is why multiplicity changes weights, not dimension.

For example, weight 3 gives eigenvalues 3 and -3, and the vector (1,-1) has energy -6. It does not give three negative directions. This exact control rejects the addendum's phrase “with multiplicity” when applied to the index count.

### 1.2 These blocks are actual directions, not formal independent variables

Normalize [K,(K21)] to obtain \(e_\lambda\in\mathscr H\) satisfying

\[
 F_{e_\lambda}(\mu)=\mathbf1_{\mu=\lambda}\quad(\mu\in Z).
\]

The construction uses the actual finite order of each zero, not simplicity. On every finite selected set its Gram matrix is exactly that of (SC1). In particular, for each two-element j-orbit,

\[
 e_\lambda^\pm=\frac{e_\lambda\pm e_{j\lambda}}{\sqrt{2m_\lambda}},
 \qquad Q[e_\lambda^+]=1,\quad Q[e_\lambda^-]=-1,
 \quad Q(e_\lambda^+,e_\lambda^-)=0.                     \tag{SC3}
\]

Different orbits are Q-orthogonal. The cutoff domination needed for these tests is supplied explicitly in [S, Appendix B, (S32)]. This is not a claim that their infinite span is an orthonormal basis in the independently chosen reference norm.

Let s be the number of distinct fixed points of j and r the number of distinct two-element orbits. Both are counted as extended nonnegative integers. **DERIVATION:**

\[
 \boxed{\operatorname{ind}_+\bar Q=s+r,\qquad
        \operatorname{ind}_-\bar Q=r,\qquad
        \operatorname{rad}\bar Q=0.}                    \tag{SC4}
\]

Here an index is the supremum of dimensions of finite positive- or negative-definite subspaces, not a count of isotropic vectors.

Proof of the upper bound when r is finite: on compact smooth pole-null tests, the map consisting of the r negative coordinates in (SC2) has values in \(\mathbb C^r\). On its kernel, every term remaining in the absolutely convergent zero sum is nonnegative. A negative-definite subspace can therefore have dimension at most r. A finite negative-definite subspace of \(\mathscr H\) can be approximated, basis vector by basis vector, in the E norm by compact pole-null tests. Boundedness of Q preserves strict negative definiteness, so the same upper bound holds after completion. Equation (SC3) proves the reverse bound. If r is infinite, (SC3) gives arbitrarily large finite negative subspaces. The same argument with the positive coordinates proves the positive-index assertion whenever its proposed count is finite; otherwise (SC3) and the fixed-point vectors give all finite dimensions.

For zeta the positive index is infinite. Independently of any count of on-line zeros, [K,(K14)] is positive on the infinite-dimensional space \((\partial_x^2-1/4)C_c^\infty(J)\) for a fixed sufficiently short interval J. The differential map is injective on compact tests. Hence

\[
 \boxed{\operatorname{sig}(\bar Q)=(\infty,r),\qquad
        RH\ \Longleftrightarrow\ r=0.}                 \tag{SC5}
\]

An off-line quartet normally contains two j-orbits. It contributes (2,2), not (1,1) in total. For real tests the conjugate coordinates are linked, and the corresponding real four-dimensional block also has inertia (2,2). These conventions must be fixed before counting. Neither r nor an actual off-line zero is computed here.

Finally, \(Q(e_\lambda,e_\lambda)=0\) off the line does not put \(e_\lambda\) in the radical: \(Q(e_\lambda,e_{j\lambda})=m_\lambda\ne0\). Quotienting removes radical vectors, not every vector of zero self-energy.

## 2. SIGNATURE-2: the pole summand is retained, not an intrinsic full-Q plane

### 2.1 What really has signature (1,1)

The pole contribution alone is

\[
 P[f]=\overline{M_+(f)}M_-(f)+\overline{M_-(f)}M_+(f)
     =2|M_c(f)|^2-2|M_s(f)|^2.                          \tag{SC6}
\]

The two moment functionals are independent. Therefore P has rank two and inertia (1,1) on its moment image. On \((-a,a)\), its actual L2 operator is

\[
 (P_af)(x)=e^{x/2}M_-(f)+e^{-x/2}M_+(f).
\]

Its even and odd eigenvectors are \(\cosh(x/2)\) and \(\sinh(x/2)\), with eigenvalues

\[
 2(\sinh a+a)>0,\qquad -2(\sinh a-a)<0.                  \tag{SC7}
\]

This proves the pole-plane statement for **P**, not the inertia of \(A_a\). On global \(\mathscr E\), \(e^{\pm x/2}\) are moment kernels, not elements of that Hilbert space. The reference-metric Riesz representatives are different objects.

\(\mathscr H\) is the radical of the summand P. It is not thereby the Q-orthogonal complement of a specified hyperbolic plane in Q. The remaining archimedean and prime form can have mixed terms with the chosen moment representatives. No Hodge intersection pairing or fibre-class isometry has been constructed over Q in these sources. The geometric analogy must not be used as that missing theorem; its sign convention would also need an explicit minus-intersection dictionary.

### 2.2 Differentiating the primitive recovers the poles exactly

**READ:** [26,(1.3)--(1.6)]; [22, Proposition 3.1, (3.8), and Section 3.5]. The relevant part of the screw function is

\[
 g_{\rm pole}(t)=-4(e^{t/2}+e^{-t/2}-2),\qquad
 -g_{\rm pole}''(t)=e^{t/2}+e^{-t/2}.                    \tag{SC8}
\]

Twice integrating by parts on compact tests gives

\[
 \int\!\!\int g_{\rm pole}(x-y)\overline{f'(x)}f'(y)\,dxdy=P[f].
                                                               \tag{SC9}
\]

The factors i in \(Df=if'\) cancel in the quadratic pairing. Centering the screw kernel by \(g(x-y)-g(x)-g(-y)+g(0)\) removes the one-variable terms on derivative tests because \(\int Df=0\); it does **not** remove (SC8). A single zero ordinary moment of Df is not the pair \(M_\pm(f)=0\).

Thus Suzuki's differentiation and primitive normalization **retain** the pole plane in the full form. [23] starts its positive completion from the full compact test space under RH; it does not remove the two poles by the project's restriction. Any later quotient is by null vectors of the full positive form, not by declaring the two moment directions null.

### 2.3 An unconditional signed quotient refinement

There is a sharper way to show why the pole summand is not intrinsic to the full quotient. Let \(\mathcal N_E=\operatorname{rad}(Q|_{\mathscr E})\). **DERIVATION from [K,(K16),(K18)]:** the theta test \(\Phi\), and all its translates, lie in \(\mathcal N_E\). Indeed their transforms vanish at all centered zeros, so they pair to zero with every compact test by (SC1), then with all of E by continuity. Put \(c=F_\Phi(1/2)=F_\Phi(-1/2)=\xi(1)\ne0\).

For fixed b>0, \(r_+=U_b\Phi\) and \(r_-=U_{-b}\Phi\) have moment matrix

\[
 c\begin{pmatrix}e^{b/2}&e^{-b/2}\\e^{-b/2}&e^{b/2}\end{pmatrix},
 \qquad \det=c^2(e^b-e^{-b})\ne0.                       \tag{SC10}
\]

For every f in E there is consequently a unique linear combination r of these two radical elements with \(M_\pm(r)=M_\pm(f)\). Then f-r belongs to H and has the same full Q pairings. Hence inclusion induces a **signed-form-preserving bijection**

\[
 \boxed{\mathscr H/\mathcal N\ \longrightarrow\
        \mathscr E/\mathcal N_E.}                       \tag{SC11}
\]

The finite correction is bounded in E, so it also gives bounded inverse maps for the reference quotient topologies; no equality of those reference norms is claimed. These corrections are noncompact and do not preserve a fixed window. They cannot be used to change the spectrum of \(A_a\) without cost.

In particular, \(Q[\Phi]=0\) but \(P[\Phi]=2|c|^2>0\). Thus P does not even descend separately to the full-Q quotient. This exact control prevents confusing its rank-two plane with an intrinsic negative sector of \(\bar Q\). The positive Hilbert-space identification with \(H_W\) still requires the conditional completion proved in [S,(S8)]; (SC11) does not assert positivity.

## 3. SIGNATURE-3: finite window inertia and its global meaning

**READ:** [26, paragraph following Theorem 1.1, (1.7), Corollary 1.2, Section 4.1]. The window operator is lower bounded with discrete eigenvalues \(\mu_j(a)\to+\infty\). Therefore

\[
 \operatorname{ind}_+Q_W^a=\infty,\quad
 n_-(a)=\#\{j:\mu_j(a)<0\}<\infty,\quad
 n_0(a)=\dim\ker A_a<\infty.                            \tag{SC12}
\]

Eigenvalue multiplicity **does** count here: distinct independent eigenvectors are being counted. This differs from repeating one zero-evaluation functional in (SC1). The zero index should not be omitted when a window is degenerate. The negative spectral part of \(A_a\) is finite rank; compactness alone for an arbitrary negative perturbation would not have been enough to prove a finite negative index.

**DERIVATION [COFINAL_FAMILY][PAPER]:** support inclusion and the form core give

\[
 n_-(a)\le n_-(b)\quad(a<b),\qquad
 \boxed{\sup_{a>0}n_-(a)=r.}                            \tag{SC13}
\]

For the first assertion approximate a finite negative eigenspace in the a-form norm by compact smooth tests in that window; strict negativity persists and the same tests belong to the b-window. For the upper bound in the second assertion use the compact signed formula and the r-coordinate argument of Section 1; that upper-bound argument also applies to unrestricted compact tests, since it does not use pole-nullity. For the lower bound choose any k distinct off-line j-orbits and their vectors (SC3). Compact, exactly pole-null approximants have a Gram matrix tending to \(-I_k\). Choose one sufficiently large common cutoff so that the operator-norm error is less than 1/2. Their whole span then has the strict upper form bound \(-\tfrac12 I_k\) on one **finite** window. This proves the lower bound for every k<=r, including the case r is infinite.

Consequently

\[
 RH\ \Longleftrightarrow\ n_-(a)=0\text{ for every }a>0.
                                                               \tag{SC14}
\]

If r is finite, the integer-valued indices eventually stabilize at r. If r is infinite, they tend to infinity. The conditional \(\lambda_a\to-\infty\) of [S,(S24)] does not by itself prove that r is infinite: an eigenvalue can become arbitrarily negative without increasing its multiplicity. A negative full-form direction does not first appear only at infinity.

### A source-side count, but not the argument principle for W

With a legal \(\sigma<\min(0,\lambda_a)\), put \(T=A_a-\sigma I>0\). Spectral calculus gives the exact source representation

\[
 \boxed{n_-(a)=\#\{\kappa\in\operatorname{Spec}((-\sigma)T^{-1}):\kappa>1\},}
                                                               \tag{SC15}
\]

counted with eigenvalue multiplicity. The inverse is compact and defined before any sign assumption. A certified high-mode positive complement and a full-residual Schur head give another exact representation: if the tail is \(B\ge bI>0\), then

\[
 n_-(a)=\operatorname{ind}_-(H-E^*B^{-1}E).               \tag{SC16}
\]

Completing the square proves (SC16). Its finite evaluation still needs all complement errors; a raw Galerkin matrix does not certify equality of indices.

The argument principle for \(W(a,\sigma,\theta;z)\) counts zeros of the characteristic function of \(\overline{\mathscr D}_{a,\theta}\). That is the derivative realization in the shifted metric, **not** the operator \(A_a\). No equality of these two counts follows from their self-adjointness. No all-a bound is supplied by (SC15) or (SC16).

## 4. SIGNATURE-4: exactly what DDF-type coordinates would need to do

In the L2 eigenbasis \(u_j\) of \(A_a\), define \(e_j=u_j/\sqrt{\mu_j(a)-\sigma}\). This is orthonormal for the positive shifted form. It gives the exact, generally **signed**, diagonal expression

\[
 Q\!\left[\sum_j c_je_j\right]
       =\sum_j\frac{\mu_j(a)}{\mu_j(a)-\sigma}|c_j|^2.   \tag{SC17}
\]

In a shifted-orthonormal eigenbasis of the different operator \(\overline{\mathscr D}_{a,\theta}\), the expression instead is

\[
 Q\!\left[\sum_jc_je_j\right]
       =c^*(I+\sigma G_{L^2})c.                         \tag{SC18}
\]

Both formulas initially apply to finite sums; form continuity gives their stated completion versions. The second physical Gram matrix need not be diagonal. Taking \(A=\operatorname{diag}(-1,1)\), \(\sigma=-2\), gives a positive shifted metric but coefficients \(-1,1/3\) in (SC17). Thus the sign problem can already be present at a finite window.

An invertible change of coordinates preserves inertia. A real-zero factorization of W cannot turn (SC17) into positive squares unless an additional identity identifies those squares with **unshifted Q**. The DDF requirement is precisely a dense-core identity \(Q(f,g)=\langle J[f],J[g]\rangle\), with the correct radical and completed range. The sources read do not supply it unconditionally. This is not a theorem forbidding its future construction.

Under RH the zero-evaluation coordinates are positive, and the de Branges construction supplies a corresponding Hilbert interpretation. Using that conditional fact as a construction before the sign would reverse the implication. The window's two deficiency indices (1,1), the pole summand's inertia (1,1), and an off-line zero block's inertia (1,1) are three different invariants.

## 5. CLOSURE-1: anchored normality is a separate, source-dependent estimate

### 5.1 Keep the corrected premise and repair the target domain

The withdrawn assertion that all finite unshifted windows are positive stays withdrawn. Theorem 1.5 supplies real-zero W-functions through the **shifted** metric; it does not prove \(A_a\ge0\). Nor does “no active prime” alone extend Theorem 1.4 from sufficiently small a to every a below the first prime.

[S,Section 5.1] distinguishes the v1 target \(z^2\xi/\xi_s'\) from v2's \(\xi/(\xi+\xi_s')\). Both are meromorphic with genuine poles, so neither is an ordinary locally uniform limit of entire holomorphic-gauge approximants on **all** of C. The latest addendum does not repair that obstruction. All subsequent closure assertions here require a specified connected holomorphic domain, a nonvanishing holomorphic gauge there, and a target with a nonzero holomorphic germ on the disks used for zero exclusion. Genuinely meromorphic approximants require a separate pole and convergence contract.

**READ:** [26,(1.2), (1.12), Sections 7.1 and 7.8] gives no proved cofinal normality theorem for the stated ground-family constants \(c_a\) or for a selected gauge of W. The c_a in (1.2) belongs to a different ground-transform family. This is a conclusion about the named sources, not a claim of an exhaustive literature search.

### 5.2 A natural exact anchor and a sufficient source estimate

Restore every parameter. On a cofinal a-family choose legal \(\sigma(a)<\lambda_a\), and real \(\theta(a)\). In the source convention of [S,(S20)], take

\[
 T_a=A_a-\sigma(a)I,\quad v_{\pm,a}=T_a^{-1}e^{\pm x},\quad
 b_a=\langle e^{-x},T_a^{-1}e^{-x}\rangle_2>0.
\]

Reflection gives equal b-values for + and -. Substitution in the boundary formula gives

\[
 W_a(i)=2ie^{i\theta(a)}b_a,\qquad F_a(z)=\frac{W_a(z)}{2ie^{i\theta(a)}b_a},
 \qquad F_a(i)=1.                                      \tag{SC19}
\]

This is a specified nondegenerate anchor, not a proof of normality. Put

\[
 e_z(x)=e^{-i\bar z x},\qquad
 K_a(z)=\langle e_z,T_a^{-1}e_z\rangle_2.
\]

Positive-inverse Cauchy--Schwarz, separately for the two source columns, yields

\[
 \boxed{|F_a(z)|\le\frac{|z-i|+|z+i|}{2}
                     \sqrt{\frac{K_a(z)}{K_a(i)}}.}      \tag{SC20}
\]

**DERIVATION:** both integrals in W are \(\langle e_z,T_a^{-1}e^{\pm x}\rangle\), whose moduli are at most \(\sqrt{K_a(z)b_a}\). Divide by \(2b_a\), noting \(K_a(i)=b_a\). The source inverse is positive because of its legal shift, not because Q is assumed positive. To use the anchor to exclude a zero cluster on a connected domain, that domain must contain i.

Thus a sufficient normality supplier on a domain \(\Omega\) is

\[
 \forall K\Subset\Omega:\quad
 \sup_{a\ge a_0}\sup_{z\in K}\frac{K_a(z)}{K_a(i)}<\infty.
                                                               \tag{SC21}
\]

An alternative sufficient estimate is a uniform bound for
\(b_a^{-1}\int e^{R|x|}(|v_{+,a}(x)|+|v_{-,a}(x)|)dx\)
for every required R. The sharper combined W expression may satisfy a bound even if these separate-column bounds fail. Hence (SC21) is **sufficient, not proved necessary and not a new mandatory route input**.

A per-window Fourier bound has type a and constants depending on \(a,\sigma(a)\). It is not uniform as a tends to infinity. The general Montel theorem is analytic; verification of its hypothesis for these source columns is not automatically prime-independent.

### 5.3 Exact detector against automatic anchored normality

Use a comparison model, not a surrogate Weil operator: on L2(-a,a) set \(A_a=I\), \(\sigma=0\), \(v_\pm=e^{\pm x}\), \(\theta=\pi\). The same boundary construction gives

\[
 W_a(z)=-4i\sinh a\cos(az),\qquad
 F_a(z)=\frac{\cos(az)}{\cosh a}.                        \tag{SC22}
\]

Every zero is real and \(F_a(i)=1\). Nevertheless \(F_a(2i)=\cosh(2a)/\cosh a\to\infty\). No subsequence can converge locally uniformly to a finite holomorphic function on C, and the fixed anchor excludes an identically infinite normal limit. On \(|\Im z|<1\), the same family converges to zero on compacts: an anchor outside a chosen domain does not exclude zero collapse inside it.

This exact model refutes the general inference from positive window metrics, real zeros and one anchor to all-plane normality. It does not prove nonnormality of the actual W-family. A free gauge making every family tend to zero would be equally uninformative.

### 5.4 One normalization where normality really is automatic, on another object

For a nonzero vector u and a self-adjoint positive-metric realization L, the scalar resolvent
\(m(z)=\langle u,(L-z)^{-1}u\rangle\) maps the upper half-plane into itself, because
\(\Im m(z)=(\Im z)\|(L-z)^{-1}u\|^2>0\).
Set

\[
 \widetilde m_a(z)=\frac{m_a(z)-\Re m_a(i)}{\Im m_a(i)}.
\]

Then \(\widetilde m_a(i)=i\). Applying Schwarz's lemma after the two Cayley transforms gives

\[
 \left|\frac{\widetilde m_a(z)-i}{\widetilde m_a(z)+i}\right|
 \le\left|\frac{z-i}{z+i}\right|.                       \tag{SC23}
\]

On a compact subset of the upper half-plane the right side is less than one uniformly, hence the family is locally bounded and normal. This is a proved abstract alternative for normalized Herglotz functions, not a theorem identifying a particular source Weyl function, its spectral weights, its Hamiltonian or W with zeta. The affine normalization changes the measure scale and real constant; those cannot be forgotten in an identification claim.

## 6. CLOSURE-2: what the RH-conditional heuristic does and does not identify

**READ:** [26,Section 7.1] assumes RH before constructing the positive global space. Sections 7.2--7.4 import a de Branges isometry and transport the multiplication operator. Section 7.8 uses its reproducing kernel with \(E(z)=\xi(1/2-iz)+\xi_s'(1/2-iz)\), substitutes the two deficiency kernels at \(\pm i\), and takes phase \(\theta=\pi\). It derives a formal target expression proportional to \(X/E\). This is the identification in the hypothetical global model, **not** a convergence theorem for the finite-window columns. [23,Theorem 1.1, Proposition 4.1, Theorem 5.6] supplies the conditional Hilbert identities; it does not remove their sign hypothesis.

Without RH, the source functions, their signed explicit formula, the shifted finite-window realizations and their real-zero property survive. The assertion that the global signed form supplies a positive de Branges norm does not. Even with RH, the passage from the finite source columns to those global deficiency kernels, with a fixed shift/phase/gauge and a valid domain, is not established in the cited heuristic.

The logical distinctions are:

\[
 \text{normality + a nonzero cluster + correct identification + real-zero bricks}
 \Longrightarrow RH;                                   \tag{SC24}
\]

\[
 RH\Longleftrightarrow\bigl(n_-(a)=0\ \forall a\bigr),
 \qquad RH\not\Longrightarrow_{\rm proved\ here}
       \text{the specified finite-source convergence law}.
                                                               \tag{SC25}
\]

A statement identifying **every nonzero cluster** can be vacuous if there is no such cluster. Anchor and compactness must therefore refer to the same normalized family on the same connected domain. An abstract existence assertion allowing arbitrary real-rooted approximants is equivalent to RH (under RH one can take the target itself); that does not settle the fixed Suzuki-source problem.

No logical equivalence between the repaired specific-source identification theorem and RH is proved here. Nor is it proved strictly stronger: the converse is an open implication, not a theorem of separation. The literal all-plane version already fails the meromorphic-target test independently of RH. Replacing a source estimate by the words “identification” or “rigidity” does not close it.

## 7. CLOSURE-3: the exact defect under not-RH

### 7.1 What must fail

Let a disk \(D\) around a hypothetical nonreal zero lie off the real axis, and let H be the correctly normalized target, holomorphic on a neighborhood of \(\bar D\), nonzero on \(\partial D\), with a zero inside. Let \(F_a\) be holomorphic and zero-free on D. This includes a real-zero W multiplied by a holomorphic nonvanishing gauge there. Put \(m_D=\min_{\partial D}|H|>0\). Rouche's theorem gives, for **every** a,

\[
 \boxed{\sup_{\partial D}|F_a-H|\ge m_D,\qquad
        \sup_{\partial D}|F_a/H-1|\ge1.}                \tag{SC26}
\]

Indeed a strict reverse inequality would force equal zero counts in D. This is the discriminator for a zero-consistent residual. It needs a boundary supremum, not agreement on a finite sample or the real axis.

For either ratio target, a zero of X of order q gives a removable quotient with a **simple** zero locally: \(\xi_s'=iX'\), so \(X/\xi_s'\sim(z-z_0)/(iq)\) and \(X/(X+\xi_s')\sim(z-z_0)/(iq)\). The additional \(z^2\) of v1 is nonzero at a nontrivial zero. Thus (SC26) applies on a sufficiently small disk even though the global meromorphic formulation needs repair.

### 7.2 The requested diagnostic, one line per object

| Object | What not-RH forces, and what it does not |
|---|---|
| Normality of normalized W | No failure is forced: a normal family can have a different real-zero limit, or zero without a valid anchor; simultaneous correct target identification fails by (SC26). |
| Weyl m-functions | Convergence can occur to a different Herglotz function; a limit identified with a target having a nonreal pole in the domain cannot be a holomorphic Herglotz limit. |
| Hamiltonians | No failure is forced by not-RH alone; an explicit source Hamiltonian, parameter, trace normalization and boundary dictionary are first required, and a convergent positive system can describe the wrong object. |
| Resolvents of the shifted derivative realization | Convergence to another self-adjoint realization is compatible with the premises; a claimed ordinary self-adjoint limit whose spectrum includes an off-real zero fails the target identification. Common Hilbert-space transports must be specified first. |
| Positive spectral measures on the real axis | They can converge while retaining real support, or lose mass in weak local limits; they cannot simultaneously represent all nonreal zeta zeros by a proved spectral dictionary. |

The table is a logical diagnosis, not a prediction that any particular actual source sequence converges. None of these source convergence laws is proved here.

There is also one mandatory source consequence available from the parent: under not-RH, [S,(S24)] gives \(\lambda_a\to-\infty\), so **every** legal shift law \(\sigma(a)<\lambda_a\) tends to \(-\infty\). A fixed shift, the choice zero, or a shift tending to zero cannot remain legal on all large windows. This does not prevent compactness after other normalizations; it prevents silently using the RH-only unshifted global metric. [COFINAL_FAMILY][PAPER, conditional alternative]

The phrase “only a wrong limit can be born” is correct for a **nonzero locally uniform limit of the real-zero functions on the stipulated domain**. It is not a description of the unshifted form's inertia: by (SC13), any finite set of negative quotient directions is already detected in one finite window.

## 8. Decision, forecasts and next bounded task

### 8.1 Claim ledger and preserved boundary

| Claim | Status | Scope / verifier |
|---|---|---|
| Distinct-zero signature and compact realization of finite negative blocks | (SC1)--(SC5), (SC13) proved here from the pinned kernel theorem | ABSTRACT, COFINAL_FAMILY / PAPER |
| Pole primitive retains the rank-two term; signed full/pole-null quotient bijection | (SC6)--(SC11) proved here | ABSTRACT / PAPER |
| Exact source negative-index representations | (SC15)--(SC18); no evaluated all-window certificate | ABSTRACT / PAPER |
| Nondegenerate W anchor and sufficient kernel-ratio bound | (SC19)--(SC21); the cofinal bound itself remains open | ABSTRACT / PAPER; cofinal supplier CONDITIONAL |
| Automatic anchored normality | Refuted only as a general theorem shape by (SC22), not for actual W | ABSTRACT / PAPER |
| Not-RH target-error obstruction | (SC26), with explicit holomorphy/domain conditions | COFINAL_FAMILY / PAPER |
| Positive Q quotient / specified source identification | Not proved | COFINAL_FAMILY / CONDITIONAL |

The addenda register no new probability events. The five observer events and their fates in [S,Section 8.1] remain as printed. The three prospective parent registrations `P_SCREW_FIRST_PRIME_SHIFT_AUDIT` (0.94), `P_SCREW_QUOTIENT_AND_LIMIT_DICHOTOMY_AUDIT` (0.88), and `P_SCREW_SOURCE_SHIFT_SEPARATED` (0.70) remain pending: this supplement is not an independent gate return or a numerical run.

New **future independent-review** registrations, not retrospective predictions of derivations already made: `P_SC_SIGNATURE_MULTIPLICITY_AND_POLE_QUOTIENT_SURVIVE`, p=0.90, for (SC4), (SC11), (SC13); `P_SC_SOURCE_ANCHOR_AND_NORMALITY_CONTROL_SURVIVE`, p=0.91, for (SC19)--(SC23); `P_SC_LOCAL_TARGET_DEFECT_SURVIVES`, p=0.96, for (SC26) and its meromorphic-germ qualifications. No new blind preregistration is claimed for this session's analytical derivations, and no prior forecast is repaired.

### 8.2 Two representations, ranked without authorizing computation

| Representation | Exact decision object | Kill power / cost, ordinal |
|---|---|---|
| Unshifted form inertia with a certified positive complement | (SC16), or an all-support source square preserving Q | 10/10 / 7/10 for sign research; no all-support proof supplied |
| Normalized source evaluation/Weyl data with a target dictionary | (SC21), or (SC23) plus a proved source identification and spectral normalization | 9/10 / 5/10 for the object audit; global identification cost unknown |

The first retains the original sign directly. The second can make compactness inexpensive, but it is not selected as a shortcut that makes identification automatic. An estimate of one of these costs is not a probability of RH.

**One next directive: SCREW_SIGNATURE_CLOSURE_DICTIONARY_AUDIT.** Independently check the finite zero blocks and their compact approximation, the pole primitive and theta-radical correction, and the anchored W estimate. Require the exact controls of Appendix A before accepting the corresponding positive claims. Freeze the source, sigma, theta, anchor, domain and spectral weight before any future normalization experiment. Do not rerun the pending two-shift experiment, enlarge a packet, edit Lean, send email, or promote state in this supplement. The existing parent experiment is neither cancelled nor scored here.

Success: (SC4), (SC11), (SC13), (SC20), (SC22) and (SC26) survive with their stated domains and no added sign premise. Failure: report `SCREW_SIGNATURE_OR_NORMALITY_DICTIONARY_GAP`, the first unsupported equation, and the weakest repair. This paper check is cheaper than an unnormalized W-to-xi sweep and can actually change the next mathematical target.

### 8.3 Consumer contract and closeout

**DOWNSTREAM_CONSUMER:** the unchanged all-test Weil criterion, or the same-family real-zero local-limit consumer. **ACTUAL_CONSUMER_REQUIREMENT:** full source nonnegativity on exhausting test domains, or correctly identified nonzero local limits of real-zero approximants. **ORIGINAL_REQUESTED_OBJECT:** quotient signature and the compactness/identification split for Suzuki's fixed source. **ORIGINAL_OBJECT_IS:** NOT_NECESSARY as a particular route; its dictionary must nevertheless be correct if used.

**KNOWN_WEAKER_INTERFACES:** cofinal full-support bounds \(Q\ge-\epsilon_a\|\cdot\|^2\) with \(\epsilon_a\to0\); a direct signed-head proof; local target convergence on disks sufficient for zero exclusion. (SC21) is only one sufficient normality input, not a newly imposed wall. **FAILURE_TYPE / EPISTEMIC_STATUS:** NO_DERIVATION / RESEARCH_DEBT for the same old universal sign and source identification. **REOPEN_TRIGGER:** an actual source inequality or target-normalized convergence identity, with complete domains; alternatively a certified strict negative source upper witness.

**SCOPED REFUTATIONS:** multiplicity-as-extra-dimensions, pole-summand-as-intrinsic-full-Q-plane, and automatic anchored normality fail their exact controls. Their scope is THEOREM_SHAPE, never ROUTE_FAMILY. No impossibility is claimed for a future arithmetic geometry, a positive DDF-type basis, or a repaired spectral limit.

**What became more precise:** the negative index, the role of poles, the exact normalized compactness supplier, and what not-RH actually obstructs. **What did not close:** the all-support sign. **DISCRIMINATOR:** a strict negative upper Schur value for an actual source test, or the strict boundary margin in (SC26); a straddling interval is not a verdict on the sign. **NOVELTY_AXIS:** exact dictionary and falsifier construction, not historical priority.

**Memory:** REPRESENTATION_PROGRESS with theorem-shape falsification; cognitive operator UNIT_AUDIT; route score 3. Preserve source form, weighted topology, point-value multiplicity, physical metric, the shift, both pole conditions, and local holomorphic domains. Do not rename a conditional norm, a diagonal signed form, or a normal family as the missing positive source identity.

**Publication handoff:** only the new supplement path in the header is written, with a `[Proshka]` commit. Its delivery receipt records commit, parent, blob, SHA-256 and one-file diff. There is no Lean source, axiom profile or kernel gate in this task. Hash agreement certifies delivery only; independent review may ratify the PAPER claims without changing the RH status.

## Appendix A. Exact controls and rational ledger

All items are [ABSTRACT][PAPER]. No quadrature, floating eigensolver or numerical experiment was run.

A1. The unitary change \((u,v)\mapsto((u+v)/\sqrt2,(u-v)/\sqrt2)\) sends \(m\begin{pmatrix}0&1\\1&0\end{pmatrix}\) to \(\operatorname{diag}(m,-m)\). At m=3 the (1,-1) value is -6. This tests multiplicity and sign simultaneously.

A2. To preserve a k-dimensional negative block \(-I_k\), it is sufficient that every entry error have modulus less than \(1/(2k)\). Its Hermitian operator-norm error is then less than 1/2 by the maximum absolute row sum, giving an upper envelope \(-I_k/2\). E-core convergence and \(|Q(f,g)|\le(65/3)\|f\|_E\|g\|_E\) supply such a common compact cutoff for each fixed k. No uniform cutoff in k is asserted.

A3. \(\int_{-a}^a\cosh^2(x/2)dx=\sinh a+a\) and \(\int_{-a}^a\sinh^2(x/2)dx=\sinh a-a\), with even-odd orthogonality. Since \(\sinh a>a\) for a>0, (SC7) has exactly one eigenvalue of each sign. The trace is 4a, matching the integral of the rank-two kernel's diagonal.

A4. Two derivatives of \(-4(e^{t/2}+e^{-t/2}-2)\) give \(-(e^{t/2}+e^{-t/2})\). In (SC9) the integration-by-parts sign is minus the second derivative. This fixes the pole sign and factor without fitting.

A5. The determinant in (SC10) is nonzero at every b>0. Since \(P[\Phi]=2|\xi(1)|^2>0\) while \(Q[\Phi]=0\), the pole summand cannot define a form on the full radical quotient.

A6. \(\mu/(\mu-\sigma)<0\) exactly when \(\mu<0\), since the denominator is positive. For \(\sigma<0\), this is equivalent to \((-\sigma)/(\mu-\sigma)>1\). Equality to one detects \(\mu=0\), not a negative mode.

A7. In (SC22), \(1+iz=i(z-i)\) and \(-1+iz=i(z+i)\). Inserting the exact exponential integrals gives \(-4i\sinh a\cos(az)\), including the removable points z=+/-i. This is the negative normality control; no sampled roots are needed.

A8. For \(z\) in the upper half-plane, \(r(z)=|(z-i)/(z+i)|<1\); (SC23) gives \(|\widetilde m_a(z)|\le(1+r(z))/(1-r(z))\). On each compact its right side is finite. This proves normality only in that half-plane and only for the normalized Herglotz object.

A9. The relative Rouche threshold is exactly 1, not an arbitrary numerical tolerance. Boundary equality remains inconclusive for zero transfer; strict error below 1 is the operative hypothesis.

## 9. PROSHKA'S OWN LINE

I retain the signed form because its inertia cannot be improved by changing names.
The signature question has an exact answer once distinct evaluations are separated.
Multiplicity is a weight in that answer, not a new family of oscillators.
The pole term has the requested hyperbolic shape, but the full quotient need not contain that plane.
The theta radical gives a direct check of this distinction.
Removing pole moments globally is different from removing them on one fixed window.
The first nearby alternative is another finite packet with more fitted eigenvalues.
I did not choose it because it cannot establish the continuum complement or a limit dictionary.
The second alternative is to force an entire normalizer onto the printed meromorphic target.
I did not choose it because the target's poles already invalidate the literal all-plane contract.
The next mathematical move is an independent audit of the index and pole dictionary.
A failure of the compact approximation of a negative block would invalidate its window interpretation.
The move after that is a fixed source, shift and normalization for a meaningful local limit.
A violated evaluation-kernel bound would reject that sufficient compactness estimate, not the sign theorem.
I would ask for the exact transported spectral measure before another convergence graph.
I would also ask for the domain on which the target is meant to be holomorphic.
The owner's request for positive coordinates is valuable when the coordinates preserve the original form.
What I distrust is the substitution of a positive shifted metric for that form.
A Herglotz normalization can provide genuine compactness very cheaply.
It does not identify the arithmetic spectral measure.
A nonzero normal limit can be perfectly regular and still be the wrong function.
An off-line zero would force a quantitative identification defect, not necessarily a failure of every convergence process.
The negative source direction associated with it is visible in a sufficiently large finite window.
The present supplement proves that distinction and does not pay the remaining sign.

## 10. Source and candidate-certificate log

**READ:** the two exact addenda at the header commits, the current protocol, [S] with its verified local bytes, and [K,(K14)--(K26)] through GitHub. These supply the requested questions, weighted space, separating tests, original shift dictionary and already reported limit obstruction. The old sources and forecasts were not rewritten.

**READ:** arXiv:2606.09096v2, (1.3)--(1.12), Corollary 1.2, the discrete-spectrum statement following Theorem 1.1, Sections 4.1, 6.3--6.5 and 7.1--7.8; PDF printed pp.4, 6, 7, 22, 27 visually checked. Taken: retained pole primitive, legal shift, evaluation columns, characteristic function and conditional global model. Rejected: interpreting those as a proved cofinal normality or identification theorem.

**READ:** arXiv:2301.00421v3, Introduction/Theorem 1.1, Section 2.2, Proposition 4.1, Theorems 4.2 and 5.6; PDF p.2 visually checked. Taken: conditional H_W/de Branges identification and the weighted zero coordinates. No new author response or independent correction of the signed-time erratum is claimed.

**READ:** arXiv:2206.03682v4, Lemma 2.1, Proposition 3.1 (3.8), Section 3.5. Taken: derivative/Weil dictionary and its distributional sign. No new arithmetic positivity theorem is imported.

**RELAY ONLY:** the Hodge/DDF analogy, Zhu's isolated certificate, and the v1 formula as documented and checked in [S]. No conclusion here depends on an exhaustive claim about the literature or on an unread physical no-ghost theorem.

**Candidate statements tested and rejected:** multiplicity increases inertia dimension (SC2); a pole plane is automatically a full-Q plane (SC10--SC11); shifted coordinates make Q positive (SC17); one nonzero anchor makes expanding real-zero bricks normal (SC22); arbitrary spectral convergence must fail under not-RH (Section 7's target/non-target distinction).

**Reusable intermediate identities:** the signed quotient map (SC11), the count (SC15), the normalized positive-resolvent ratio (SC20), and the local boundary defect (SC26). They are object and diagnostic results, not the missing source sign.

End of supplement. The closed SCREW verdict is preserved. All new analytical conclusions remain PAPER pending independent review. RH is not claimed.
