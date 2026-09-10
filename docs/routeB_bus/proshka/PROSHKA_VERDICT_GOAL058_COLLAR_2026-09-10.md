# STATUS: TRY_COLLAR_PRIME_CHANNEL_LOW_RESPONSE
```yaml
OPERATIVE_CLASS: TRY_COLLAR_PRIME_CHANNEL_LOW_RESPONSE
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-COLLAR
BOUNDARY_ID: GOAL058_FULL_SOURCE_COUPLED_COLLAR_EQUALITY
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
ODD_OBSTRUCTION_VERIFIED: true
COUPLED_SOURCE_EXCLUSION_PROVED: false
LOWER_SIGN_PROVED: false
PX_RH_CLAIM: NOT_MADE
INDEPENDENT_CHECK_OF_NEW_LEMMAS: PENDING
LEAN_VERIFIED: false
REQUEST_LOCK:
  REPOSITORY: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: d01e056eef27d0eff657f082a8fb58457a6e5866
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_COLLAR_2026-09-10.txt
  BLOB: d9171c32e23c11144ae29b01157d1744ec11bb55
  SHA256: 697302c9b40ac098ea5c59262f6df4f916cc3da3e445e49e5f240fd3ebec79c6
  BYTES: 13396
  LINES: 76
  FINAL_LF: true
  ATTACHMENT_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: f7ce930f6baa3a6cb7a44f1a02657d8d6067f78a
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SHELF_VERIFICATION:
  PINNED_BLOB_IDENTIFIERS_MATCH: 6
  FULL_SHA256_AND_GIT_BLOB_RECOMPUTED_MATCH: 4
  NOT_REHASHED_THIS_BATCH: [CONTACT_INDEPENDENT_CHECK, XIDEV_VERDICT]
  LFS_POINTER_BYTES_VERIFIED: true
  HYDRATED_PDF_BYTES_VERIFIED: false
  REMOTE_ARXIV_V1_READ: true
  REMOTE_PDF_IDENTIFIED_WITH_LFS_OBJECT: false
  LIMITATIONS: section_0_2
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
NEW_PAPER_RESULTS:
  THIN_COLLAR_INTERNAL_PRIME_TERMS_VANISH_BY_SUPPORT: true
  PRIME_CROSS_CHANNELS_ARE_EXACTLY_ORTHOGONAL: true
  PRIME_CROSS_GRAM: Omega_a_times_identity
  FULL_CROSS_NORM_SQUARED_LIMIT: pi_squared_over_4_plus_Omega_a
  UNIVERSAL_TWO_COLLAR_MODEL_WITH_BOUNDED_ERROR: true
  SCALAR_RELATIVE_COLLAR_INVERSE_APPROXIMATION: REFUTED_FOR_ACTUAL_SOURCE
  COMPLETE_LOW_CORE_PROJECTION: true
  REGULAR_CORE_AND_COLLAR_FEEDBACK_REMAINDER: PROVED
  LEGENDRE_MOMENT_OPERATOR_TAIL: PROVED
  STRICT_LOW_RESPONSE_MARGIN: NOT_PROVED
FIRST_INCORRECT_ASSERTION_Q1: NONE_FOUND
FIRST_FAILURE:
  Q1: NONE_REMAINING_AT_REQUESTED_SCOPE
  Q2_INITIAL: relative_operator_norm_scalarization_of_the_collar_inverse_is_false
  Q2_REPAIR: full_source_low_response_matrix_not_bounded_strictly_below_core_energy
  Q3: depends_on_the_unproved_strict_low_response_margin
PREDICTION_FATES:
  P1: {probability: 0.95, fate: CONFIRMED}
  P2: {probability: 0.95, fate: CONFIRMED}
  P3: {probability: 0.80, fate: CONFIRMED}
EXECUTION:
  NEW_SOURCE_NUMERICAL_RUN: false
  OLD_FINITE_TESTS_RERUN: false
  EXACT_RATIONAL_AND_SYMBOLIC_CONTROLS: true
  LEAN_GATE: NOT_RUN
  QUEUE_STATE_REGISTRY_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COLLAR_2026-09-10.md
  COMMIT_BLOB_HASH_COUNTS_AND_PUSH_STATUS: external_verified_receipt
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
```

## 0. Decision and source integrity

**The odd reflected-prime obstruction survives. The source equality case is not excluded.** The new work identifies the complete thin-collar arithmetic channels, derives the actual cross-operator norm asymptotic, constructs a universal two-collar operator with an explicit bounded error, and reduces the remaining equality to a finite low-core response with a controlled infinite operator remainder. No part of this is promoted to a lower-sign theorem. [ABSTRACT][PAPER; COFINAL_FAMILY][CONDITIONAL for exclusion]

The principal source results are
\[
\mathcal P_{a,d}^*\mathcal P_{a,d}=\Omega_a I,
\qquad
\lim_{d\downarrow0}\|J_{a,a-d}^{\rm src}\|^2
=\frac{\pi^2}{4}+\Omega_a,
\qquad
\Omega_a=\sum_{2\le n<e^{2a}}\frac{\Lambda(n)^2}{n}.                 \tag{L0}
\]
These hold for each fixed real a>0, with the explicit arithmetic separation conditions below. They are not assertions about a tending to infinity. The sum includes every prime power. The collar's *internal* prime form vanishes for these splits, but its prime coupling to the core does not vanish. [ABSTRACT][PAPER]

A concrete failed approximation is also resolved. With the actual positive thin-collar operator C and the scalar c_d defined in (L9),
\[
\|I-c_d C^{-1}\|=1
\]
for all sufficiently small d. Thus the inverse cannot be replaced by c_d^{-1}I with relative operator-norm error tending to zero. The repair keeps a nontrivial universal logarithmic operator; its absolute inverse error is explicitly bounded by O_a(d/c_d^2). [ABSTRACT][PAPER]

The remaining problem is not inverse existence or an unpaid infinite high-mode tail. It is the strict inequality for the finite matrix (L25), whose entries retain the full source boundary responses of every low core eigenspace. A usable one-feedback lower envelope is written in (L29). Its strict positive sign has not been proved. [COFINAL_FAMILY][CONDITIONAL]

### 0.1 Immutable source ledger

All repository paths in this table are at SOURCE_BASE, not moving rh_clean. READ records inspected content; it does not elevate an older proof or review receipt to an axiom.

| Key | Path | Declared SHA-256 | Pinned Git blob | Reading and independent hash status |
|---|---|---|---|---|
| C | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONTACT_2026-09-10.md` | `3475f7e1d9c11bf2ff259f1d10b967d0fdbbf7c1e68219fcd9c4ab3fcb5dd034` | `dc30c38e5832859e3b84cebaddcf5779545bdd58` | READ C1-C8, C10-C11, C14-C25 and closeout in the full local artifact; exact-pin connector cross-check; both hashes recomputed, 52815 bytes, 729 lines. |
| I | `docs/routeB_bus/CONTACT_INDEPENDENT_CHECK_2026-09-10.md` | `d3865192de724c857413385eb58b7baa8a0811b0457857c292260c046d451879` | `af682a509363ddcf1f21bcb584b7a4e6f21c6c22` | READ report, acceptance receipt and complete odd appendix; pinned blob matched; full SHA-256 not independently recomputed here. |
| E | `docs/routeB_bus/FIRST_CONTACT_EXTERIOR_2026-09-10.md` | `b5869eb1573d7d25ce0c11ce08184643e71e6323cdbed6e4195e95c3b0de8560` | `34a54f8154efc3c072ac030485cb3320d231f507` | READ full; both hashes recomputed from reconstructed connector text, 9448 bytes, 93 lines. |
| X | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_WEIL_POSITIVITY_AROUND_XI_PROOF_2026-09-05.md` | `93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9` | `136aceb3cbbabcdfa425459562b803b67c548b48` | READ pinned lines 350-455, especially RAD, VAR, GS and the negative-density calculation; full SHA-256 not independently recomputed here. Not used as a new positive representation. |
| P | `docs/routeB_bus/litreview/pdfs/2606.09096.pdf` | `880d5e8f4e1a121569580bcc9f8a38ad8c7ecd8b907f067b73667a104a1d72ed` | `6a52f0cbd9e5d43b0284fab64931037442079f9a` | READ Git LFS pointer; both pointer hashes recomputed, 131 bytes, 3 lines. Hydrated object not obtained. |
| B | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full; both hashes recomputed, 11341 bytes, 79 lines. This is the only repository file opened outside the bus for this task. |

The authoritative attachment was read in full and independently gave exactly the request hash, blob, 13396 bytes, 76 LF characters and final LF in the header. Its independently computed blob matches the exact-commit connector response. No request binding was changed.

### 0.2 Source/version limitations

Four of six shelf files have a fresh full SHA-256 and Git-blob recomputation. I and X do not. Their declared SHA values are binding metadata, not recomputed results. No mismatch was observed. Complete shelf rehashing is **not claimed**.

The pointer P identifies a 501231-byte object with SHA-256 `06e2abeb778d9414f98589d8654ecf06a7f6d9d0b9914961e88365a6b48b91b2`. The GitHub read returned the pointer only. Hydration/download attempts did not yield usable local PDF bytes. The object's size and hash therefore remain **RELAY from the pointer/request**, not an independently verified hydrated file.

Separately, the versioned remote `https://arxiv.org/pdf/2606.09096v1` was READ: first-page metadata and rendered pages 4-5. It has the June 8 arXiv header, June 9 internal date and 30 pages. Theorem 1.1/Corollary 1.2 and Theorem 1.3 provide the expected domain/attainment and continuity statements. This is a version-labeled primary cross-check, **not a byte identification with P's LFS object**. No later HTML or v2 was used. No new estimate below is imported from that paper; the necessary local operator facts are the rechecked literal-source arguments in C. The conditional terminal consumer is the Weil criterion stated on page 1 of this actually read v1.

Bootstrap was freshly fetched from `rh_clean`, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`, including the response and write rules. The older locally uploaded bootstrap was not substituted for it.

### 0.3 Literal source used throughout

The physical pairing is antilinear first, with \(U_tf(x)=f(x-t)\). Keep
\[
\alpha(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
w_n=\frac{\Lambda(n)}{\sqrt n},\quad
c_A=\gamma+\log(8\pi)+\pi/2,\quad
M_\pm(f)=\int_{\mathbb R}e^{\pm x/2}f(x)dx,
\]
\[
\begin{split}
B(f,g)={}&\int_0^\infty\alpha(t)
 \langle U_tf-f,U_tg-g\rangle_2dt-c_A\langle f,g\rangle_2\\
&-\sum_{n\ge2}w_n\{
 \langle f,U_{\ell_n}g\rangle_2+\langle f,U_{-\ell_n}g\rangle_2\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),
\qquad Q[f]=B(f,f).                                    \tag{SOURCE}
\end{split}
\]
Here \(\ell_n=\log n\), and \(\Lambda(n)\) is the von Mangoldt function, including its prime-power values. The control norm is \(\|f\|_E^2=\int e^{2|x|}|f(x)|^2dx+\mathcal D[f]\), where D is the first quadratic term in (SOURCE). The window domain is \(V_a=\overline{C_c^\infty(-a,a)}^{E}\), equivalently the supported logarithmic form domain of C5. Its Friedrichs operator is characterized by \(B(h,v)=\langle h,A_av\rangle_2\) for every h in V_a. C2 gives \(|B(f,g)|\le22\|f\|_E\|g\|_E\). These conventions remain fixed in every decomposition below. [ABSTRACT][PAPER]

## 1. RESULT Q1 — PROOF_CANDIDATE_COMPLETE

This section proves precisely the narrow requested obstruction, for every a>log(2)/2. It does not prove a negative quadratic value or any statement about the parity of a ground state. [ABSTRACT][PAPER]

Write \(\ell_n=\log n\). The odd lift is
\[
(Ou)(x)=\operatorname{sgn}(x)u(|x|)/\sqrt2.
\]
It is unitary from L2(0,a) to the odd physical subspace. For disjoint real nonnegative smooth u,v, expand the polarized source in its four physical quadrants. The equal-sign quadrants together contribute \(-\alpha(|x-y|)\); the opposite-sign quadrants contribute \(+\alpha(x+y)\). The diagonal mass term is zero. The two prime shifts, after folding, give
\[
\begin{split}
B_{\rm odd}(u,v)={}&-\int_0^a\!\int_0^a
 [\alpha(|x-y|)-\alpha(x+y)]u(x)v(y)\,dx\,dy\\
&-\sum_{n\ge2}w_n\int_0^a u(x)
 [v(x-\ell_n)+v(x+\ell_n)-v(\ell_n-x)]\,dx
-4S_uS_v,\quad S_u=\int_0^a\sinh(x/2)u(x)dx.             \tag{L1}
\end{split}
\]
Indeed \(M_+(Ou)=\sqrt2 S_u\) and \(M_-(Ou)=-\sqrt2 S_u\), giving the last coefficient -4. The reflected arithmetic coefficient is **+w_n**. All profiles here are supported strictly inside the half-interval; the equation needs no endpoint trace.

At a=1/2 choose the exact centers x0=log(2)/3, y0=2log(2)/3, d0=1/100, and an even nonnegative \(\varphi\in C_c^\infty(-1,1)\) with \(\int\varphi^2=1\). Set
\[
u(x)=d_0^{-1/2}\varphi((x-x_0)/d_0),\qquad
v(x)=d_0^{-1/2}\varphi((x-y_0)/d_0).
\]
The bounds 69/100<log(2)<7/10 place their supports inside (0,1/2), disjoint, at separation greater than 21/100. These logarithm bounds can be obtained without floating arithmetic from
\(\log2=2\sum_{k\ge0}[(2k+1)3^{2k+1}]^{-1}\): the first two terms give 56/81>69/100, and bounding every remaining denominator by 3 gives the upper bound 25/36<7/10.

Every direct prime shift is zero by support. Exactly the reflected n=2 term remains, since x+y lies within 1/50 of log(2), below log(3). Evenness of the bump gives
\(\int u(x)v(\log2-x)dx=1\).
For separation at least 21/100, \(\alpha(t)<3\), because
\(e^{42/100}>1+42/100+(42/100)^2/2=7541/5000>3/2\).
Also \(\sinh(x/2)<1/3\) for 0<x<1/2. Since each L1 norm is at most \(\sqrt{2d_0}\), the complete archimedean and pole loss is at most \(6d_0+8d_0/9\). Therefore
\[
B_{\rm odd}(u,v)\ge\frac{\log2}{\sqrt2}-\frac{62d_0}{9}
>\frac{23}{50}-\frac{31}{450}
=\frac{88}{225}>\frac{39}{100}.                         \tag{L2}
\]
Here \(\sqrt2<3/2\) and log(2)>69/100 justify the strict arithmetic comparison. No quadrature or source-eigenvalue computation was used.

For an arbitrary a>log(2)/2, choose two distinct positive interior centers whose sum is log(2). Shrink the same normalized even bumps around them. Their separation remains a fixed positive number. All continuous archimedean and pole terms are O(d0), while the reflected n=2 contribution stays exactly w2. The finitely many other relevant integer logarithms stay outside their sum/difference intervals for sufficiently small d0. This proves a strictly positive disjoint cross pairing on every such window.

If the odd semigroup \(T_t=e^{-tA_{\rm odd}}\) preserved nonnegative functions, then \(\langle u,T_tv\rangle\ge0\) and \(\langle u,v\rangle=0\). The spectral-calculus form limit gives
\[
B_{\rm odd}(u,v)=\lim_{t\downarrow0}
 t^{-1}\langle u,(I-T_t)v\rangle\le0,                   \tag{L3}
\]
a contradiction. For a semibounded operator this limit follows after a scalar shift; on the nonnegative spectrum \((1-e^{-t\lambda})/t\le\lambda\), and form-domain Cauchy-Schwarz supplies domination for polarized pairs. The scalar shift pairs to zero on these disjoint u,v.

**Q1 outcome:** no substantive correction. Positive off-diagonal pairing is compatible with a positive definite operator. It excludes this positivity-preserving semigroup, not source positivity, an individual resolvent value, or a node-free/with-nodes theorem. It says nothing affirmative about the even sector. **FIRST_FAILURE Q1: NONE.** Inputs: C1-C8 and I's checked appendix; all coefficients were rederived above.

## 2. Source geometry of an arithmetically separated collar

The lemmas in sections 2-4 are unconditional fixed-parameter source statements. They hold for every fixed a>0, and every d in the explicit range below. [ABSTRACT][PAPER]

### 2.1 An exact separation rule, including integer thresholds

Set
\[
N=\lceil e^{2a}\rceil-1,\quad
 g_a=2a-\log N>0,\quad \chi_a=\log(1+1/N),\quad
 d_{\rm geom}(a)=\min\{a/2,1,\log2/4,g_a/4,\chi_a/4\}.     \tag{L4}
\]
Here N>=1 is the largest integer **strictly** below e^(2a). If e^(2a) is an integer, its endpoint translation has zero overlap a.e. and is excluded for exactly that reason. No nonzero source atom is removed.

Take 0<d<d_geom(a), b=a-d, core I_b=(-b,b), and collars
\(J_+=(b,a)\), \(J_-=(-a,-b)\). Then b>a/2 and 2b>log(N). There is no integer logarithm strictly between 2b and 2a. Same-collar differences have length less than d<log(2). Thus
\[
\text{the prime part of }Q|_{L^2(J_-\cup J_+)}\text{ is identically zero}.       \tag{L5}
\]
This is a support theorem for C alone. It is not a prime truncation in the full-window form or in its cross operator.

Let w_+,w_- denote the two zero-extended collar components and define the positive-weight prime cross map
\[
(\mathcal P_{a,d}w)(x)=\sum_{n=2}^{N}w_n
 [w_+(x+\ell_n)+w_-(x-\ell_n)],\quad x\in I_b.
\]
The source cross operator contains **-P**, not +P. For each n, the two image intervals are
\[
I_{n,+}=(b-\ell_n,a-\ell_n),\qquad
I_{n,-}=(-a+\ell_n,-b+\ell_n).
\]
They are wholly inside I_b: d<log(2) and log(n)<=log(N)<2b. Two image intervals of the same sign are disjoint because distinct integer logarithms below N differ by more than chi_a>d. Opposite-sign images could overlap only if
\(2b<\ell_n+\ell_m<2a\). This would place the integer logarithm log(nm) in that empty interval. If nm=e^(2a), the images only touch at an endpoint, with zero L2 overlap. Therefore **all image intervals are pairwise disjoint**, including both signs and all prime powers.

Translations preserve each component's physical L2 norm. Expanding the resulting orthogonal sum gives the exact identity
\[
\boxed{\mathcal P_{a,d}^*\mathcal P_{a,d}=\Omega_a I,
\quad \Omega_a=\sum_{n=2}^{N}w_n^2,
\quad \|\mathcal P_{a,d}\|=\sqrt{\Omega_a}.}             \tag{L6}
\]
If Omega_a=0, P=0. Otherwise P/sqrt(Omega_a) is an isometry from the *whole* two-collar L2 space into the core. This is not a finite-rank claim and does not replace \(P^*A_b^{-1}P\) by a scalar. The core inverse can mix the orthogonal physical channels.

### 2.2 Full-source cross norm: the boundary singularity does not become small

Use the exact J in C19. Define S by its same-sign singular kernels:
\[
(Sw)(x)=
\begin{cases}
\frac12\displaystyle\int_b^a\frac{w_+(y)}{y-x}dy,&0<x<b,\\
\frac12\displaystyle\int_{-a}^{-b}\frac{w_-(y)}{x-y}dy,&-b<x<0.
\end{cases}
\]
It is a direct sum of two restricted half-Carleman operators, hence \(\|S\|=\pi/2\).
For the upper bound, put t=e^u in the Carleman operator with kernel 1/(s+t). The unitary logarithmic transform gives convolution with \(1/[2\cosh(u/2)]\), whose L1 norm is pi. For the matching lower bound, use normalized indicators of increasingly long intervals in logarithmic coordinates and translate both intervals sufficiently far to the left to lie within both truncated domains. Their pairing tends, by dominated convergence, to that L1 norm. Thus the finite physical interval lengths do not reduce the norm; the singular corner remains at arbitrarily small scales.

Put
\[
k_a=\sup_{0\le t\le2a}|\alpha(t)-1/(2t)|,
\quad \alpha(t)-1/(2t)\big|_{t=0}=1/4,
\]
\[
L_a^{\rm reg}=\sqrt{2a}\,[k_a+\alpha(a/2)]
+4\sqrt{\sinh a\cosh a}.
\]
The full decomposition is
\[
J=-S-\mathcal P_{a,d}+R,
\qquad \|R\|\le L_a^{\rm reg}\sqrt d.                  \tag{L7}
\]
For this bound, the same-sign regular kernels have combined Hilbert-Schmidt norm at most sqrt(2bd) k_a. The opposite-sign archimedean kernels have separation at least b and combined norm at most sqrt(2bd) alpha(b). The pole cross operator has norm at most
\(4\sqrt{\sinh b(\sinh a-\sinh b)}\), bounded by the remaining term in (L7). Both pole terms are present. The cross mass term is zero by disjoint support.

There is also a bound on the *mixed* singular/arithmetic product, sharper than multiplying their norms. Put
\(q_a=\min\{\log2/2,g_a/2\}>0\) and \(s_a=\sum_{n=2}^{N}w_n\).
Every image interval of P is at distance at least q_a from both endpoints of the core. Indeed its distance to the nearest core endpoint is bounded below by either log(n)-d or 2b-log(n), both at least q_a by (L4). In S*P each resulting collar-to-collar kernel is therefore bounded by s_a/(2q_a). Its whole domain is a union of four rectangles of area d^2, so
\(\|S^*P\|\le d s_a/q_a\).

Consequently, with
\[
E_J(a,d)=\frac{2d s_a}{q_a}
+2(\pi/2+\sqrt{\Omega_a})L_a^{\rm reg}\sqrt d
+(L_a^{\rm reg})^2d,
\quad j_a(d)=\pi^2/4+\Omega_a+E_J(a,d),
\]
we have the two-sided source estimate
\[
\boxed{
\left|\|J\|^2-(\pi^2/4+\Omega_a)\right|\le E_J(a,d),
\qquad \|J\|^2\le j_a(d).}                             \tag{L8}
\]
To prove it, expand J*J using (L7), subtract S*S+Omega_a I, bound S*P+P*S as above, and then bound all R cross terms. Since S*S is nonnegative with norm pi^2/4, its sum with Omega_a I has norm pi^2/4+Omega_a. This proves (L8) and the limit in (L0).

Thus shrinking the collar does not make J small in operator norm. The source-specific squared prime weights survive alongside the singular geometric norm. This does **not** compute the normalized coupling K, because the source inverse A_b^{-1} is still between its factors.

## 3. A universal two-collar operator, and the first failed approximation

### 3.1 Exact model and explicit error

Define the unitary physical rescaling
\[
(U_dw)_+(s)=\sqrt d\,w(b+ds),\qquad
(U_dw)_-(s)=\sqrt d\,w(-b-ds),\quad 0<s<1.
\]
The target space is \(\mathscr H=L^2(0,1)\oplus L^2(0,1)\). In particular no parity sector is discarded.
For a zero-extended profile f on (0,1), define the nonnegative closed form
\[
\mathfrak l[f]=\int_0^1\frac{\|f(\cdot+t)-f\|_2^2}{2t}dt,
\]
and its Friedrichs operator L. Its form domain is the logarithmic zero-extension domain, not H1_0. Closedness follows from the graph of the difference map. Its Fourier symbol is \(\int_0^1(1-\cos(\xi t))dt/t\), comparable with log(2+|xi|) after adding 1; fixed support then gives compact embedding as in C4-C5. Thus L has compact resolvent and unbounded spectrum. Write L_2=L direct-sum L.

Let
\[
c_d=2\int_d^\infty\alpha(t)dt-c_A,
\qquad
\varepsilon_C(a,d)=d[4k_a+\alpha(2b)+4\cosh a].          \tag{L9}
\]
Then the **actual** collar operator satisfies the bounded-perturbation identity
\[
\boxed{U_d C_{a,b}U_d^{-1}=c_d I+L_2+E_{a,d},
\qquad E_{a,d}=E_{a,d}^*,\quad \|E_{a,d}\|\le\varepsilon_C(a,d).}    \tag{L10}
\]
This is an equality of closed forms and hence of the associated operators, with their bounded-perturbation domains. It is not a surrogate definition of C.

For a single collar, translations of length t>=d are disjoint and supply exactly the scalar \(2\int_d^\infty\alpha\). Below d, rescale t=ds. The difference of the kernels d alpha(ds) and 1/(2s) has absolute value at most d k_a, so its form perturbation has norm at most 4d k_a. This comparison also proves equality of the respective form domains. The cross term between the two physical collars has operator norm at most d alpha(2b). Their prime form is exactly zero by (L5). The full pole operator on the collars has norm at most
\(4(\sinh a-\sinh b)\le4d\cosh a\).
These are all the terms in (L10).

Every endpoint -a,-b,b,a, or equivalently both copies of 0 and 1, is accounted for by zero extension in l. Inward smooth approximation follows from the logarithmic form core C5; no point value or normal derivative has been assumed. The retained operator E includes the two poles and the interaction between the two collars.

### 3.2 The universal potential and harmonic-number lower operator

A direct separation of inside and outside translations gives
\[
\mathfrak l[f]=\frac12\int_{0<x<y<1}\frac{|f(y)-f(x)|^2}{y-x}dxdy
+\int_0^1 V(x)|f(x)|^2dx,
\quad V(x)=-\tfrac12\log[x(1-x)]\ge\log2.              \tag{L11}
\]
Both sides are nonnegative integrals, so the identity extends by Tonelli to their full form domains. The outside term is obtained by integrating 1/(2t) from x to 1 and from 1-x to 1. In particular it keeps the two endpoint costs; for f=1, the regional term is zero and the whole value is 1, not zero.

There is an explicit diagonal lower operator for the regional part. Let
\(p_n(x)=\sqrt{2n+1}\,P_n(2x-1)\), an orthonormal Legendre basis of L2(0,1), and let \(H_0=0\), \(H_n=\sum_{k=1}^n1/k\). On polynomials the regional operator is
\[
(Tp)(x)=\tfrac12\int_0^1\frac{p(x)-p(y)}{|x-y|}dy,
\quad
T(x^n)=H_nx^n-\tfrac12\sum_{k=0}^{n-1}\frac{x^{n-1-k}}{k+1}.       \tag{L12}
\]
The monomial identity follows by splitting at y=x and integrating the divided polynomial. T is symmetric and preserves every polynomial degree space. Its leading coefficient in degree n is H_n, so orthogonality to the lower-degree spaces gives T p_n=H_n p_n.

For any finite-energy f, polarization against p_n is legitimate by form Cauchy-Schwarz and equals \(H_n\langle p_n,f\rangle\). Subtracting a finite Legendre projection in the nonnegative regional form proves its energy is at least \(\sum_{n\le m}H_n|\langle p_n,f\rangle|^2\). Let m increase. Therefore, in closed-form order,
\[
\boxed{L\ge D_H+(\log2)I,
\qquad D_Hp_n=H_np_n.}                                \tag{L13}
\]
Only a lower comparison is asserted; the variable potential V has not been declared constant. Polynomial density in physical L2 suffices for the later Parseval identity. The all-degree proof above, not the finite symbolic controls, proves (L13).

### 3.3 A real source failure and its repair

The natural first approximation was the relative operator-norm claim
\(c_d U_dC^{-1}U_d^{-1}\to I\) as d decreases to zero.
It is false. For sufficiently small d, c_d>0 and epsilon_C<log(2); (L10)-(L13) imply C>=c_d I. Its inverse is compact on an infinite-dimensional Hilbert space. Hence
\[
\boxed{\|I-c_d C^{-1}\|=1,
\qquad \|C^{-1}-c_d^{-1}I\|=c_d^{-1}.}                 \tag{L14}
\]
The upper bound follows from 0<=c_d C^{-1}<=I. For the lower bound take an orthonormal sequence of eigenvectors whose eigenvalues tend to infinity. The difference tends to 1 on that sequence. Unitary rescaling does not alter the norm. This is an exact obstruction for the actual source collar, not a random matrix model.

The absolute error 1/c_d does tend to zero. What is refuted is the **relative** error o(1/c_d), which would be required to replace a coupled inverse by its scalar leading term uniformly over all profiles. No finite list of low profiles establishes that operator-norm claim. For the attempted threshold 1/2, the exact success margin is 1/2-1=-1/2.

The concrete repair retains the entire universal L_2. Put R_d=c_d I+L_2 and r_d=c_d+log(2). Whenever r_d>epsilon_C,
\[
\boxed{\|(U_dCU_d^{-1})^{-1}-R_d^{-1}\|
\le\frac{\varepsilon_C}{r_d(r_d-\varepsilon_C)}.}        \tag{L15}
\]
This is the resolvent identity applied to (L10), using the independently proved lower bounds on its two positive operators. Since c_d=log(1/d)+O(1), it is O_a(d/log(1/d)^2). It is an operator-norm estimate for all collar profiles. It pays an actual remainder without assuming a sign-definite eigenfunction or a positive semigroup.

## 4. RESULT Q2 — PARTIAL_WITH_PRECISE_REMAINDER

### 4.1 The exact low-core split, without a bottom-gap substitution

Now impose the **hypothetical first-contact premises**, and only those premises:
\[
a>a_0=e^{-20}/2,\qquad \lambda_a=0,\qquad
\lambda_c>0\quad(a_0\le c<a).
\]
Choose d as in (L4), also d<a-a0. Thus A_b is strictly positive. The source-only results above let us further choose d so small that
\[
\eta(a,b)>0,\quad c_d>0,\quad
\kappa_{a,d}:=\varepsilon_C(a,d)+j_a(d),\qquad
q_{a,d}:=\frac{\kappa_{a,d}}{r_d}\le\tfrac12.             \tag{L16}
\]
Such d exist for each fixed a: eta and c_d tend to infinity, epsilon_C tends to zero, and j_a(d) tends to the finite constant in (L0). No uniform-in-a positive core floor has been assumed. [COFINAL_FAMILY][CONDITIONAL for the contact premises; PAPER for the construction of the admissible split]

Let
\[
P=\mathbf1_{(0,1]}(A_b),\quad \mu_1,\ldots,\mu_r\in(0,1],
\quad \phi_1,\ldots,\phi_r\text{ an orthonormal eigenbasis of }\operatorname{ran}P,
\quad \mathsf M=\operatorname{diag}(\mu_1,\ldots,\mu_r).
\]
All eigenspaces below or at 1, with all multiplicities and both parities, are retained. P does not mean a chosen ground direction. On P-perp the actual core operator A_H is greater than or equal to I. Put J_H=(I-P)J.

For clarity, the number r admits a source bound independent of b<a. Set
\(L_a^{\rm floor}=c_A+2s_a+4\sinh a\) and
\(R_a^{\rm freq}=\exp(4(L_a^{\rm floor}+2))\).
C4's increasing Fourier symbol m obeys
\(m(R)\ge\frac12\log(2R)\) for R>=1: retain beta_j=2j+1/2<=R in its positive sum, bound each retained summand below by 1/beta_j, and compare the sum with its decreasing-function integral. Each unit vector in ran(P) has D-energy at most 1+L_a^floor, so at least half of its Fourier mass lies in [-R_a^freq,R_a^freq]. For an orthonormal basis of this subspace, Bessel's inequality gives a total low-frequency mass at most 2b R_a^freq/pi. Consequently
\[
 r\le 4aR_a^{\rm freq}/\pi<\infty.                       \tag{L17}
\]
This crude cap is a proof of completeness of the low projection, not an invitation to build a matrix of that size. It uses no unproved eigenvalue gap or simplicity. [ABSTRACT][PAPER]

### 4.2 Every low coupling is an explicit full-source boundary response

Define columns in the fixed two-profile space
\[
h_j=U_dJ^*\phi_j\in\mathscr H,
\qquad F:\mathbb C^r\to\mathscr H,\quad Fz=\sum_jz_jh_j.
\]
For x_+(s)=b+ds and x_-(s)=-b-ds the exact columns are
\[
\begin{split}
h_j^+(s)=\sqrt d\bigg[&-\int_{-b}^b\alpha(x_+(s)-y)\phi_j(y)dy
-\sum_{n=2}^{N}w_n\phi_j(x_+(s)-\ell_n)\\
&+e^{x_+(s)/2}M_-(\phi_j)+e^{-x_+(s)/2}M_+(\phi_j)\bigg],\\
h_j^-(s)=\sqrt d\bigg[&-\int_{-b}^b\alpha(y-x_-(s))\phi_j(y)dy
-\sum_{n=2}^{N}w_n\phi_j(x_-(s)+\ell_n)\\
&+e^{x_-(s)/2}M_-(\phi_j)+e^{-x_-(s)/2}M_+(\phi_j)\bigg]. \tag{L18}
\end{split}
\]
These are L2 statements, with phi_j extended by zero. The first integral has the half-Carleman boundary singularity. C14-C15 or the proof of (L7) gives its L2 meaning up to s=0. No trace or analyticity of phi_j at b is required. The unused shifts vanish by support, not by neglecting an arithmetic term.

Every product of columns below is formed **after adding** the signed archimedean, prime and two-pole pieces in (L18). The isometry (L6) does not authorize replacing these products by prime-only squares. Nor does it diagonalize the core resolvent.

### 4.3 Eliminate the regular core completely

Transport the regular recovery to the collars:
\[
T_H=U_dJ_H^*A_H^{-1}J_HU_d^{-1},\qquad
0\le T_H\le j_a(d)I,
\]
\[
D=R_d+E_{a,d}-T_H,\qquad
D\ge (r_d-\kappa_{a,d})I>0.                            \tag{L19}
\]
The infinite high-core sector has not been discarded. It is represented by its full resolvent; the inequality uses only its proved spectral floor 1 and the new full-source cross bound (L8). In particular it contains no factor 1/lambda_b.

For physical v=x_L+x_H+w, with x_L=sum z_j phi_j and x_H in the high-core form domain, completing the two positive squares gives
\[
\begin{split}
Q[v]={}&Q_H[x_H+A_H^{-1}J_Hw]
+\|D^{1/2}(U_dw+D^{-1}Fz)\|^2
+z^*\mathsf S_{a,d}z,\\
\mathsf S_{a,d}={}&\mathsf M-F^*D^{-1}F.                \tag{L20}
\end{split}
\]
All additions preserve the form domains: bounded positive resolvents map L2 into the corresponding operator domains; (L10) and (L19) are bounded form perturbations of the same collar operator. The internal cuts are bounded in E by the truncated Carleman argument in C19, which includes all four endpoints. This proves an exact decomposition of the original form, not a finite replacement for it. [ABSTRACT][PAPER]

Thus \(\mathsf S\succ0\) implies lambda_a>0 by bounded invertible triangular changes of variables and the two positive diagonal floors. Explicitly, the change is (z,x_H,w) to (z,x_H+A_H^{-1}J_Hw,U_dw+D^{-1}Fz). Its inverse first recovers w from the third coordinate and z, and then x_H from the second coordinate and w. Both maps are bounded in physical L2. The three floors are respectively the positive smallest eigenvalue of S, 1, and r_d-kappa_(a,d); comparison with the bounded inverse map gives a positive physical Rayleigh floor. At a contact, S is positive semidefinite and singular. Conversely if S is positive semidefinite and has a nonzero null z, take
\[
w=-U_d^{-1}D^{-1}Fz,\qquad
x_H=-A_H^{-1}J_Hw,\qquad v=\sum_jz_j\phi_j+x_H+w.        \tag{L21}
\]
Then v is nonzero, both positive squares in (L20) vanish, and v is an actual local null vector. Its low projection z prevents it from vanishing. Setting u=-x_L-x_H gives exactly the requested equations A_bu=Jw and Cw=J*u, with v=w-u. If r=0, the two positive squares instead prove lambda_a>0 immediately; hence any contact must have r>=1. No multiplicity assumption occurs.

### 4.4 A complete geometric-series remainder for the coupled response

Scalarization (L14) is not used. Keep the full universal resolvent and put
\[
T=R_d^{-1/2}(E_{a,d}-T_H)R_d^{-1/2},\qquad
Y=R_d^{-1/2}F.
\]
Then T is bounded self-adjoint, \(\|T\|\le q_{a,d}\le1/2\), and
\[
F^*D^{-1}F=Y^*(I+T)^{-1}Y.
\]
For every integer m>=0, define the finite r-by-r matrix
\[
\mathsf G^{(m)}=Y^*\sum_{k=0}^{m}(-T)^kY,
\qquad e_m=\frac{q_{a,d}^{m+1}}{1-q_{a,d}}.
\]
The entire unretained operator response has the two-sided **matrix-order** enclosure
\[
\boxed{
-e_mY^*Y\preceq F^*D^{-1}F-\mathsf G^{(m)}
\preceq e_mY^*Y.}                                      \tag{L22}
\]
Proof: the omitted self-adjoint functional-calculus remainder is
\((-T)^{m+1}(I+T)^{-1}\), with norm at most e_m. Pair it with Yz for each complex z. This proves both matrix inequalities for every coefficient vector. It controls the full infinite high-core feedback and the collar perturbation together; no finite source spectrum has replaced a quantifier.

The m=1 response is especially explicit:
\[
\begin{split}
\mathsf G^{(1)}={}&F^*R_d^{-1}F
-F^*R_d^{-1}E_{a,d}R_d^{-1}F\\
&+F^*R_d^{-1}T_HR_d^{-1}F,
\qquad e_1=q_{a,d}^2/(1-q_{a,d}).                       \tag{L23}
\end{split}
\]
The last term is nonnegative recovery from the high core; its plus sign matters. Dropping it would overestimate the final lower margin. The middle term retains the signed two-pole and cross-collar corrections. None of these coefficients is assumed zero.

### 4.5 A second, fully explicit source-moment upper envelope

To expose the universal profile dependence rather than leave just an inverse notation, let
\[
g_{\sigma n,j}=\int_0^1p_n(s)h_j^\sigma(s)ds,
\quad \Theta=F^*F,\quad
\beta_n=c_d+\log2+H_n-\kappa_{a,d}>0.
\]
For each sigma and n, g_sigma,n is a row vector of length r. Equations (L18) specify its full arithmetic and pole content; Theta is the exact L2 Gram of those same columns.
By (L13) and (L19), closed-form order and the variational formula for a positive inverse give
\[
F^*D^{-1}F\preceq
\sum_{\sigma\in\{+,-\}}\sum_{n\ge0}
 \frac{g_{\sigma n}^*g_{\sigma n}}{\beta_n}.
\]
For every integer p>=0, Parseval pays the whole remaining Legendre tail:
\[
\boxed{
F^*D^{-1}F\preceq\mathsf U_p:=
\sum_{\sigma,n\le p}\frac{g_{\sigma n}^*g_{\sigma n}}{\beta_n}
+\frac{\Theta-\sum_{\sigma,n\le p}g_{\sigma n}^*g_{\sigma n}}
 {\beta_{p+1}},
\qquad \mathsf M-\mathsf U_p\preceq\mathsf S.}           \tag{L24}
\]
The numerator of the last term is a positive semidefinite matrix, not an informal truncation error. It is at most Theta<=j_a(d)I. This supplies an explicit tail even when the low source eigenvectors have no proven boundary trace or smoothness. Constants and the degree-zero Legendre term remain included.

There is a real loss here: (L24) replaces V(s) by log(2) and bounds E-T_H in form order. Increasing p removes only the displayed Legendre tail; it does not remove those other losses. Failure of this sufficient lower envelope is not failure of S or of the source sign. The exact signed response (L22)-(L23) remains the less wasteful primary representation.

### 4.6 The remaining source estimate, with its exact budget

The reduction now leaves the finite matrix
\[
\boxed{\mathsf S_{a,d}=
\operatorname{diag}(\mu_j)
-Y^*(I+T)^{-1}Y.}                                      \tag{L25}
\]
Its index set contains **every** core eigenvalue in (0,1], and its columns are exactly (L18). The complete perturbation and high-core remainder are (L19) and (L22). There is no unrecorded infinite operator tail.

A sufficient source statement, equivalent to strict positivity of S after allowing m, is
\[
\begin{gathered}
\forall a>a_0\text{ satisfying the first-contact premises},\\
\exists d,m,\epsilon>0:\quad
0<d<\min(d_{\rm geom}(a),a-a_0),\quad (L16),\\
\mathsf M-\mathsf G^{(m)}-e_mY^*Y\succeq\epsilon I_r.   \tag{L26}
\end{gathered}
\]
If S is positive, a finite m exists because the finite-dimensional remainder (L22) tends to zero. The converse follows directly from that lower envelope. This equivalence does not prove (L26).

**FIRST_FAILURE Q2 after repair:** the new arithmetic identities and inverse bounds do not prove (L26), or the stronger one-feedback version m=1. Specifically no bound has been derived that makes the signed boundary response (L23), plus its paid error \(e_1Y^*Y\), strictly smaller than the actual small core eigenvalues in M. The low eigenvalues are retained, not replaced by a speculative uniform gap. The physically orthogonal prime channels in (L6) cease to be orthogonal after applying the core inverse, and the mixed source pieces in (L18) cannot be independently maximized or removed.

This is more than writing a Schur complement again: (L4)-(L10) give a new actual-source collar model and norm law; (L14) refutes the first proposed inverse estimate on the actual source; (L15), (L19), (L22) and (L24) pay its repaired operator tails. What is still missing is the indicated **low response energy inequality**, not an assertion that these estimates are unavailable merely because their consumer concerns RH.

## 5. RESULT Q3 — PARTIAL_WITH_PRECISE_REMAINDER

### 5.1 Exact transfer and its limits

The dependency chain for the chosen construction is as follows. Each row's scope concerns the mathematical assertion, not repository publication.

| Supplier | Domain / quantifiers / normalization | Input and output | Proof / status |
|---|---|---|---|
| Literal local form | Every a>0; complex zero-extended V_a in physical L2 | C1-C8 give closed semibounded A_a, compact resolvent and attained bottom | C, rechecked as used; [ABSTRACT][PAPER] |
| Positive start and contact | a0=e^(-20)/2; all smaller/larger windows on the same source | Continuity and inclusion turn any nonpositive later window into an attained first zero | C10-C11 and argument below; [COFINAL_FAMILY][PAPER] |
| Separated arithmetic channels | Every fixed a>0, all 0<d<d_geom(a) | Exact P*P=Omega I and internal collar prime vanishing | (L4)-(L6); [ABSTRACT][PAPER] |
| Full cross and collar model | Same physical split, both components, all source terms | j_a(d), c_d, E, epsilon_C; no inverse-sign assumption | (L7)-(L15); [ABSTRACT][PAPER] |
| Complete low-core reduction | A_b>0, complete spectrum in (0,1], (L16) | Finite M and exact S; all high modes included in T_H | (L17)-(L21); [ABSTRACT][PAPER under stated hypotheses] |
| Infinite response enclosure | All m>=0, q<=1/2; every complex coefficient vector | Two-sided matrix remainder e_m Y*Y; optional complete moment tail | (L22)-(L24); [ABSTRACT][PAPER] |
| Strict source budget | Every hypothetical first-contact a, one admissible d | Strict positive lower envelope for S | (L26); [COFINAL_FAMILY][CONDITIONAL, unproved] |
| Original all-test lower sign | Every complex compact smooth f | Strict S contradicts contact; no nonpositive window can occur | Conditional implication below; [COFINAL_FAMILY][CONDITIONAL] |

To check the terminal implication, assume (L26) has been proved independently. A nonpositive later window would, by continuity and the positive anchor, give the first a with lambda_a=0. Its bottom is attained. Choose the admissible split provided by (L26). Equations (L20) and (L22) make the full form strictly positive, contradicting lambda_a=0. Hence every window is positive. Any complex compact smooth f lies in some V_a, so Q[f]>=0. The full Hermitian Weil criterion then reaches its consumer.

No simplicity, sign-definite ground vector, even-only reduction, new numerical anchor, or uniform positive gap in a enters that implication. But the premise (L26) is unpaid, so **neither the unconditional all-test lower sign nor source kernel exclusion is claimed here**. PX_RH_CLAIM remains NOT_MADE even at the conditional terminal step.

### 5.2 Required scalar equality control

For A=C=1 and J=t, the full form is
\[
|x|^2+|w|^2+2t\Re(\bar xw),\qquad
\det\begin{pmatrix}1&t\\t&1\end{pmatrix}=1-t^2.
\]
The low projection at cutoff 1 contains the entire core, the high sector is empty, and exact elimination gives
\[
\mathsf S=1-t^2.                                      \tag{L27}
\]
At t=1 the equality system has u=w and actual null vector (-u,w). Our exact reduction returns zero, not strict positivity. At |t|<1 it returns positive; at t>1 it returns negative. Positive diagonal blocks and compactness therefore do not make the detector falsely reject equality.

This is not an arithmetic counterexample or a fixed-source first-contact model; it tests the elimination algebra only.

The additional **proved source properties** absent from this scalar control are the integer-product separation giving (L6), the half-Carleman plus squared-prime norm law (L8), and the exact logarithmic collar model (L10). They distinguish the new analysis from a generic matrix argument. They have **not** yet been shown to force the strict low-response inequality. There is no already-proved source fact here that may be asserted to eliminate t=1 and then silently applied to the arithmetic equality case.

### 5.3 The reflected-prime falsifier remains active after the new split

At a=1/2 and sufficiently small admissible d, N=2. A right-collar profile is shifted into the negative part of the core, and a left-collar profile into the positive part. The full physical source has cross coefficient -w2 on those shifts. Under the odd lift the opposite-side sign changes, producing exactly **+w2** on the halfline reflection. Thus (L5) does not erase the obstruction (L1)-(L2).

Any implementation that reads “collar prime form is zero” as “remove the prime part of J” changes Omega from w2^2 to zero and changes the limit (L8) by w2^2. It also fails the exact reflected bump pairing (L2). Those are source-level falsifiers; no eigenvalue or positivity-preserving assertion is needed. All full response matrices in this verdict retain this term through (L18).

### 5.4 Strongest attack and preserved scope

The strongest objection is that the remaining finite matrix is still difficult and depends on actual source eigenspaces. That objection is correct. Defining the eigenspaces by the spectral theorem is not supplying their quantitative boundary responses. This verdict proves the new channel geometry and the complete regular remainder; it does not pretend to have proved the missing low-response inequality by choosing a basis.

In particular (L6) is an identity **before** the core inverse. It provides no equality such as \(P^*A_b^{-1}P=\Omega_a I\), and no inequality with an unproved sign. The source C includes both poles even when its prime overlaps vanish. Analyticity was never inferred for the translated L2 prime profiles. Neither local nullity nor the automatic radical-tail identity E4 was used as exterior vanishing. The upper-rate supplier from SATURATION is untouched.

## 6. Route map and dependency epistemics

| Representation | Preserved / lost | Decisive issue | Kill-power / cost estimate |
|---|---|---|---|
| **Chosen: full low-source response with universal collar resolvent and signed feedback** | Same Q, four boundaries, physical norm, both parities; all small eigenspaces and mixed terms | Strict margin (L26); all regular feedback has the enclosure (L22) | 9/10 / 7/10 |
| **Alternative: harmonic-number/Legendre boundary moments** | Same source columns, exact physical Gram tail; loses the excess potential V-log2 and some feedback cancellation | Positivity of M-U_p with the complete remainder (L24) | 8/10 / 5/10; failure kills only this sufficient bound |
| **Rejected: scalar collar inverse or unweighted small-J approximation** | Drops profile-scale dependence or the singular/arithmetic channel mass | Exact (L14), or the positive norm limit (L8) | 10/10 / 1/10 against those exact approximation claims |

These are planning estimates, not probabilities, authorizations to escalate computation, or mathematical certificates.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_every_complex_compact_smooth_test
  ORIGINAL_REQUESTED_OBJECT: strict_full_source_collar_contraction_at_first_contact
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - direct_all_test_source_nonnegativity
    - all_large_window_lower_envelope_tending_to_zero
    - first_contact_kernel_exclusion_without_a_uniform_gap
  CHOSEN_INTERFACE_IMPLICATION: strict_L26_implies_positive_S_implies_no_contact_implies_all_test_sign
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: arithmetic_channel_isometry_plus_universal_logarithmic_collar_response
  REOPEN_TRIGGER: full_source_strict_low_response_bound_with_the_L22_remainder_paid
SCOPED_REFUTATION:
  CLAIM: relative_operator_norm_scalarization_c_d_C_inverse_tends_to_identity
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: exact_actual_source_inverse_norm_identity
  EVIDENCE: this_verdict_L14
  SUCCESS_MARGIN_UPPER_ENVELOPE_AT_THRESHOLD_ONE_HALF: minus_one_half
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  ACTUAL_THETA_SIGN_REFUTED: false
CLOSES:
  - narrow_odd_reflected_prime_obstruction_review
  - exact_thin_collar_prime_channel_geometry
  - scalar_collar_inverse_approximation_attempt
  - universal_collar_model_operator_error
  - regular_response_infinite_tail_accounting
OPENS: []
CARRIES_OPEN:
  - full_source_strict_low_response_margin
  - first_contact_exclusion
  - all_test_lower_sign
```

The class of **first-contact** conditions is sufficient, not mandatory for every route to the consumer. No route-family death is inferred from the failed scalar approximation. The genuinely open margin is recorded as research debt, with its exact source objects and reopening condition above.

## 7. Frozen predictions and closeout

The three events were frozen in the authoritative request before this proof work. No new numerical forecast is invented and no historical ratio is rescored. [ABSTRACT][PAPER for these audit outcomes]

| Frozen event | Fate | Evidence |
|---|---|---|
| P1, 0.95: narrow odd obstruction survives | CONFIRMED | (L1)-(L3), including its semigroup-only conclusion and exact coefficient +w2. |
| P2, 0.95: shrinking/splitting alone does not exclude norm one | CONFIRMED | Actual source failures (L8), (L14), and exact scalar equality control (L27); new tail bounds do not prove (L26). |
| P3, 0.80: partial result with a new source lemma or exact attempted-estimate refutation | CONFIRMED | New (L4)-(L15), full response enclosures (L22)-(L24), and exact source refutation (L14); strict margin remains unpaid. |

What became smaller: an uncontrolled entire collar/core inverse is replaced by a fixed universal profile operator, a bounded source perturbation, every low core eigenspace, and an explicit matrix-order remainder. The source cross norm is computed to a vanishing error, rather than merely bounded by a large sum of prime weights.

What was killed: the relative scalar collar-inverse approximation and the inference that unweighted J vanishes with collar width. What was not killed: the source contraction, the low-response mechanism, the even or odd lower-sign problem, or any route family. Failure of a positive sufficient lower envelope remains a failure of that envelope only.

The exact rational checks reproduced 88/225>39/100. Symbolic checks reproduced the regional Legendre identity for degrees 0 through 8 and the scalar determinant/kernel in (L27). The proofs above establish all degrees and all stated parameters; the finite controls are not their quantifiers. No source matrix, approximate ground state, numerical spectrum, old finite row, or interval-energy campaign was run.

```yaml
iteration:
  target: GOAL058_FULL_SOURCE_COUPLED_COLLAR_EQUALITY
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: scalarize_the_collar_inverse_uniformly_over_all_profiles
  new_gap_name: full_source_low_response_margin_after_universal_collar_reduction
  invariant_learned: internal_prime_clearance_preserves_nonzero_orthogonal_cross_channels
  forbidden_future_move: remove_reflected_prime_channels_or_replace_the_low_core_inverse_by_a_uniform_floor
  next_decisive_test: LOW_SOURCE_ONE_FEEDBACK_MARGIN
  route_score: 4
```

## 8. Exactly one next_decisive_test and publication handoff

**LOW_SOURCE_ONE_FEEDBACK_MARGIN.** The next bounded analytical task is the following **specific** matrix budget, not another source eigensolve or an increase in dimension.

Use the complete spectral cutoff 1, the full columns (L18), R_d=c_d+L_2, and T_H from (L19). Keep precisely one feedback term as in (L23), with the already proved full error. The terminal observable is
\[
\mathsf L^{[1]}_{a,d}=\mathsf M-\mathsf G^{(1)}
-\frac{q_{a,d}^2}{1-q_{a,d}}Y^*Y.                      \tag{L28}
\]
The requested source lemma for this selected sufficient test is
\[
\boxed{
\forall a\text{ satisfying the first-contact premises},\quad
\exists d\text{ satisfying }(L4),(L16),\ d<a-a_0:
\quad \mathsf L^{[1]}_{a,d}\succ0.}                    \tag{L29}
\]
Its new data are the **two boundary-channel profiles for every low eigenspace**, not the already resolved BRIDGE/SATURATION scalar rows. Its complete feedback uncertainty is the matrix term in (L28), not a roundoff estimate. Equation (L24) is an optional rigorously tailed way to bound the universal profile response; it must not be identified with it.

**ЕСЛИ_A:** a proof gives a strictly positive lower envelope for (L28) at the full quantifiers (L29). Then (L22), (L20) and section 5 exclude first contact and reach the all-test consumer. A certificate on a bounded set of windows proves only that set.

**ЕСЛИ_B:** a strict upper envelope makes the selected sufficient matrix margin negative, or the proof obtains only a worst-bottom-eigenvalue bound with no source low-response comparison. Stop this one-feedback estimate. That outcome rejects this sufficient budget, not the source theorem or the exact response (L25). Do not automatically increase feedback order, Legendre degree, arithmetic precision or window size. A representation repair must identify which actual signed response was lost.

If an enclosure contains zero, the outcome is UNRESOLVED. The exact-zero discriminator is a nonzero vector z in the kernel of the exact matrix S, with reconstruction (L21), or a source proof that no such z exists. A kernel of a truncated or lower-envelope matrix is not that witness. No unproved first-contact vector is claimed to have been found.

**One Codex directive:** independently check the prime-image interval proof (including nm=e^(2a)), the sharp coefficient pi^2/4 in (L8), the collar identity and relative inverse obstruction (L10)-(L15), and the full signed response remainder (L22); then adjudicate precisely (L29) from its source profiles. Return a proof at the stated quantifiers or the first source coefficient inequality that fails, keeping the lower/upper envelope orientation. No old scalar reruns or new Lean/state/queue/registry writes are authorized by this document.

**Publication handoff:** add only EXPECTED_VERDICT_PATH. The external receipt must identify its actual commit, parent, Git blob, SHA-256, bytes, LF count and final-LF status, and check that this commit changes exactly one path while retaining concurrent branch changes. No self-hash is embedded here. No Lean source was written, no axiom profile is asserted, and a documentation commit is not an independent mathematical check.

## 9. Proshka's own line

I keep the two physical collars instead of imposing a sign cone on either halfline.
The reflected prime atom makes that distinction operational, not stylistic.
The first useful simplification is arithmetic separation, not a positivity assumption.
It removes prime overlap inside the collars while preserving every cross channel.
The integer product nm explains why opposite channels separate at the same time.
That is the source fact I would keep even if the present estimate later fails.
The singular geometric coupling does not disappear with the collar width.
Its exact norm is what makes a scalar-smallness argument misleading.
The collar inverse becomes small in absolute norm, but it never becomes relatively scalar in operator norm.
Keeping the universal profile operator repairs that particular mistake.
The second nearest alternative was an absolute norm bound on the whole core inverse.
That would again erase the small eigenspaces that actually carry the question.
The other alternative was a halfline positivity-preserving argument.
The existing reflected bump already rules out that shortcut for the odd sector.
The next move is a source bound for the low boundary-channel response, with its first feedback retained.
A verified negative sufficient margin would stop that estimate, not settle the original sign.
The move after that would retain the variable endpoint potential in the universal resolvent more accurately.
That move is useful only if the lost potential, rather than the core response, explains the failed budget.
I would ask for exact source formulas for those low boundary responses before another spectral ratio.
I would also ask that both components and their mixed products remain visible in any proposed certificate.
The same coefficient family must appear in the head matrix and in every remainder.
What surprised me is that the thin prime cross map has an exact isometry identity.
Its orthogonality is physical; it is not orthogonality after the source resolvent.
I distrust any proof that slides between those two meanings without an equation.
The new operator tails are paid, but the decisive low energy inequality is not.
That is the precise difference between a better representation and a lower-sign proof.

## 10. Research log

### 10.1 Every source consulted this batch

| Source / locator | READ or RELAY | Use and limitation |
|---|---|---|
| Authoritative COLLAR attachment; exact GitHub request commit and hashes in header | READ full; hashes recomputed | Scope, frozen forecasts, literal odd control, source equality system, one-path write boundary. |
| Fresh `PROSHKA_SYSTEM_PROMPT_v2.md`, `rh_clean`, blob in header | READ, including continuation through final response rules | Intake, evidence/scoping, one operative class and append-only publication. |
| C, exact source-base pin; C1-C8, C10-C11, C14-C25 | READ from full local bytes and pinned connector excerpt; full hashes recomputed | Source/domain, four-boundary splitting, cross operator, positive anchor and contact consumer. Used lemmas rechecked where needed; no new audit of the old upper-rate construction. |
| I, exact source-base pin; full report and odd appendix including acceptance receipt | READ; full SHA not recomputed | Provenance, requested narrow obstacle; (L1)-(L3) rederived rather than accepting the receipt as an axiom. |
| E, exact source-base pin; E1-E5 | READ full; both hashes recomputed | Distinction between local and global nullity and a.e. exterior source formula; no exterior completeness imported. |
| X, exact source-base pin; L2 and L3a-L3b, RAD/VAR/GS/negative-density interval | READ specified excerpt; full SHA not recomputed | Prevented reuse of a signed ground-state transform as a positive kernel. Its formulas are not premises of the new channel/resolvent lemmas. |
| P, exact source-base pin; 131-byte LFS pointer | READ; both pointer hashes recomputed | Exact object identifier only. The 501231-byte PDF object was not obtained or rehashed. |
| Remote Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v1, `https://arxiv.org/pdf/2606.09096v1`; page 1, rendered pages 4-5 | READ version-labeled primary PDF | Weil consumer, Theorem 1.1/Corollary 1.2 and Theorem 1.3 cross-check only. No identification with the LFS bytes, later HTML or v2; no new quantitative lemma imported. |
| B, exact source-base pin; proof-batch and sections 9-10 rules | READ full; both hashes recomputed | Required proof/remainder format. Sole opened repository path outside the bus. |
| Raw GitHub connectivity / media hydration / PDF download attempts | UNAVAILABLE transport, not source evidence | Raw hostname resolution failed; media access/download did not produce a hydrated artifact. No resulting byte-verification claim. |
| PDF reading skill and GitHub action schemas | READ tool instructions, not mathematical sources | PDF inspection and supported GitHub reads/writes; no theorem imported. |

The words **Carleman**, **Friedrichs**, **Legendre** and **spectral projection** refer to the explicitly defined operators and general mathematical constructions proved or instantiated above. No additional article was used for these new lemmas. The logarithmic convolution norm, regional harmonic-number calculation and matrix feedback bounds have their proofs in this document.

### 10.2 Candidate branches and first obstacles

| Candidate | First failed assertion or limiting fact |
|---|---|
| Relative scalar collar inverse | The actual compact source inverse obeys (L14); the purported norm convergence has constant error 1. |
| Vanishing unweighted core/collar cross norm | The source limit in (L8) is pi^2/4+Omega_a, strictly positive. |
| Remove primes after proving the collar has no internal prime overlap | False object substitution: (L6) retains Omega_a and section 5.3 retains the reflected +w2 term. |
| Infer inverse orthogonality from physical prime-channel orthogonality | P*P=Omega I does not compute P*A_b^(-1)P; the actual low columns and core feedback remain. |
| Replace all universal profiles by their degree-zero component | L has an unbounded logarithmic spectrum; (L11)-(L13) retain the endpoint potential and every harmonic-number mode. |
| Harmonic diagonal majorant as an automatic strict source proof | (L24) is only an upper bound for recovery; the low-core energy comparison is unpaid and potential/coupling losses remain even as p increases. |
| Complete low-core elimination with signed feedback | Survives as (L20)-(L23); stops exactly at (L26)/(L29), not at a missing infinite-tail estimate. |

### 10.3 Reusable intermediate results and restrictions

(L6) is a source prime-channel isometry, not a prime-only energy formula.
(L8) computes the thin-collar cross norm to an explicit vanishing error, not the normalized coupling norm.
(L10) is a universal two-profile collar model with O_a(d) bounded source error, keeping all endpoints and poles.
(L14) is an actual-source obstruction to relative scalarization, even though the absolute inverse norm tends to zero.
(L15) pays the repaired universal-model inverse error at O_a(d/log(1/d)^2).
(L12)-(L13) provide an all-degree harmonic-number lower operator with the constant mode retained.
(L17) bounds the complete low-core dimension without a bottom-gap or simplicity assumption.
(L18) is the exact a.e./L2 source formula for every retained boundary response, on both components.
(L22) pays all omitted signed regular feedback in matrix order for every complex low coefficient vector.
(L24) pays the whole Legendre tail through the physical source Gram; its other sufficient-bound losses remain explicit.
(L26) and (L29) remain unproved source inequalities. None of the preceding entries is called an all-test lower-sign theorem.
