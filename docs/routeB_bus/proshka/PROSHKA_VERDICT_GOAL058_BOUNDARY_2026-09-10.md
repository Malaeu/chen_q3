# STATUS: TRY_BOUNDARY_SIGNED_MEAN_RESPONSE
```yaml
OPERATIVE_CLASS: TRY_BOUNDARY_SIGNED_MEAN_RESPONSE
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-BOUNDARY
BOUNDARY_ID: GOAL058_SIGNED_BOUNDARY_LOW_ENERGY_COMPARISON
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
VERIFIER: PAPER
UNIFORM_BOUNDARY_INPUT_VERIFIED: true
SIGNED_SOURCE_COMPARISON_PROVED: false
LOWER_SIGN_PROVED: false
INDEPENDENT_CHECK_OF_NEW_LEMMAS: PENDING
LEAN_VERIFIED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_LOCK:
  COMMIT: b574857250e2c0e136bb04cfddd906ea1b3aee8f
  BLOB: a1c4f3c77013823562e13f86ad7a342e42f16669
  SHA256: 1988f386d36cc16925ddf14d1d67e83c94ab3af1b50a36cd70586a1a5c40a589
  BYTES: 13190
  LINES: 74
  FINAL_LF: true
  LOCAL_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_BLOB_MATCH: true
SOURCE_BASE: a443424e10a119ded80aca6ddc664b23eaf854fb
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
CANONICAL_COLLAR:
  COMMIT: d254ce1f1baae6329fc01f20cf2df52a482048ea
  BLOB: 77ba2a24022b5a8993316018db8919e0a15a24a7
  SHA256: 03b9e2ed966dec1d776cf768970992731913f830a087faf0d8f51c35e9cfc51b
  ALTERNATIVE_LOCAL_COLLAR_USED_AS_SOURCE: false
SHELF_CHECKS:
  CONNECTOR_BLOB_PINS_MATCH: 5
  FULL_SHA256_RECOMPUTED_MATCH: 2
  FULL_SHA256_NOT_RECOMPUTED: [canonical_COLLAR, COLLAR_INDEPENDENT_CHECK, CONTACT_INDEPENDENT_CHECK]
  COMPLETE_BYTE_VERIFICATION_CLAIMED: false
NEW_PAPER_RESULTS:
  ALL_LOW_ZERO_EXTENSION_EQUICONTINUITY: proved
  EXPLICIT_TWO_SIGNED_BOUNDARY_MEAN_ROWS: proved
  MEAN_ZERO_RESPONSE_NORM: o_a_sqrt_d
  EXACT_SIGNED_MEAN_VARIANCE_IDENTITY: proved
  CONSTANT_CHANNEL_CORRECTION_LIMIT: identity_matrix_2
  FULL_RESPONSE_EXPANSION: d_times_1_minus_1_over_c_times_beta_star_beta_plus_o_a_d_over_c
  NORMALIZED_ENDPOINT_TRACE_LIMIT: not_assumed_not_proved
  CORE_ENERGY_VS_BOUNDARY_MEAN_STRICTNESS: not_proved
FIRST_FAILURE:
  Q1: NONE_IN_THE_STATED_PAPER_DERIVATION
  Q2_INITIAL: no_signed_lower_comparison_of_M_with_d_beta_star_beta
  Q2_AFTER_REPAIR: no_strict_source_boundary_mean_energy_deficit_above_the_positive_variance_remainder
  Q3: unconditional_transfer_requires_the_unproved_Q2_inequality
PREDICTION_FATES:
  P1: CONFIRMED
  P2: CONFIRMED
  P3: CONFIRMED
  P_BOUNDARY_MEAN_REPRESENTATION_078: CONFIRMED
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
EXECUTION:
  NEW_SOURCE_NUMERICAL_CAMPAIGN: false
  EXACT_SYMBOLIC_ALGEBRA_CONTROL: true
  LEAN_GATE: NOT_RUN
  LEAN_QUEUE_REGISTRY_STATE_EDITS: false
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BOUNDARY_2026-09-10.md
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  BRANCH: rh_clean
  COMMIT_PUSH_BLOB_AND_FILE_HASH: external_delivery_receipt
HONESTY_STATE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
BUS_010: VOID
```

## 0. Decision and source integrity

**The boundary input survives. The signed comparison with the core energies is not proved.** This batch obtains more than another absolute scale: two explicit, full-source boundary averages determine the first two response terms. Their exact correction has a negative sign in the recovered energy, and the remaining variance is a positive square with a complete bound. None of this establishes the required lower bound for the actual core energies. [ABSTRACT][PAPER]

For every fixed admissible outer window, with the definitions below,
\[
F^*D^{-1}F
=d\beta^*\beta-\frac d{c_d}\beta^*\mathcal A_\partial\beta
+\mathcal Z^*D^{-1}\mathcal Z,
\qquad \mathcal A_\partial\longrightarrow I_2,
\qquad \mathcal Z^*D^{-1}\mathcal Z=o_a(d/c_d).
\tag{N0}
\]
This is an operator identity and a fixed-a estimate for the **entire** low spectral space. The matrix beta depends on d; neither beta nor M/d is asserted to converge. The full high-core inverse remains in D and in the displayed correction. [ABSTRACT][PAPER]

### 0.1 Immutable shelf and verification limitations

All five repository paths in this table are read at SOURCE_BASE. READ means the indicated text was inspected; independent-check conclusions are not additional axioms. The new arguments are rederived below.

| Key | Exact repository path | Pinned SHA-256 | Pinned Git blob | This continued batch |
|---|---|---|---|---|
| C | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONTACT_2026-09-10.md` | `3475f7e1d9c11bf2ff259f1d10b967d0fdbbf7c1e68219fcd9c4ab3fcb5dd034` | `dc30c38e5832859e3b84cebaddcf5779545bdd58` | READ C1-C8/C19-C25 as used; local full bytes rehashed and both hashes match; 52815 bytes,729 lines |
| L | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COLLAR_2026-09-10.md` | `03b9e2ed966dec1d776cf768970992731913f830a087faf0d8f51c35e9cfc51b` | `77ba2a24022b5a8993316018db8919e0a15a24a7` | READ canonical L4-L29 and applicable context through pinned connector reads; blob matches; full SHA not recomputed |
| I | `docs/routeB_bus/COLLAR_INDEPENDENT_CHECK_2026-09-10.md` | `08a0aedc5e2c32b26dcff0ba94e19432a9ce9770e9bf07cb5d051069359255e4` | `fbac9618c618e23af4b43a1dea7ceddd092a5129` | READ audit and both new boundary appendices; blob matches; full SHA not recomputed |
| J | `docs/routeB_bus/CONTACT_INDEPENDENT_CHECK_2026-09-10.md` | `d3865192de724c857413385eb58b7baa8a0811b0457857c292260c046d451879` | `af682a509363ddcf1f21bcb584b7a4e6f21c6c22` | READ applicable operator qualifications, odd obstruction and provenance; blob matches; full SHA not recomputed |
| P | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full; reconstructed content rehashed, both hashes match; 11341 bytes,79 lines |

**The requested independent full-byte verification is incomplete for three shelf files.** A matching connector blob is not a claim to have independently computed SHA-256. Raw HTTP acquisition failed; no unobserved byte check is credited. The authoritative request itself was read completely, independently hashed, counted, and matched to its exact-commit connector blob.

The local alternative COLLAR, SHA `41c760d4f4c3cae22b17415adf4734a55210d503f731f15d5497ae34dbc9062a`, was hashed only to identify and quarantine it. Its 54755-byte/763-line text is not the accepted 58946-byte/786-line source L. No historical file is overwritten.

### 0.2 External theorem actually read

[H] is Hernandez-Santamaria, Lopez Rios and Saldana, *Optimal boundary regularity and a Hopf-type lemma for Dirichlet problems involving the logarithmic Laplacian*, **arXiv:2401.18033v2**, HTML `https://arxiv.org/html/2401.18033v2`: Theorem 1.1, (1.2), (1.15)-(1.19), its proof in section 4, and Lemma A.3. Its bounded weak-solution theorem applies to the interval and is used separately on real and imaginary parts. Its proof compares a barrier with both signs of the solution. Hopf Theorem 1.4 is not imported.

This is an identified published theorem, not a claim to have re-proved every cited barrier and continuity dependency. The fetched HTML's raw bytes were not hashed against the parent's historical 1227643-byte SHA `2f75d6d6cbb231facf481271b3f673bc2340e3cdde962730f86947e2b37209f3`. No HTML/PDF identity or Suzuki-version upgrade is claimed. No PDF was used in this batch.

## 1. Q1: narrow audit of the boundary input

Every proved assertion in sections 1-5 is [ABSTRACT][PAPER], with **fixed-a** constants. An invocation under hypothetical contact is conditional only on the stated local premises, not on RH. A limit as d decreases is never a uniform-in-a assertion.

### 1.1 Objects and domains

Retain the antilinear-first form C1:
\[
\begin{split}
B(f,g)={}&\int_0^\infty\alpha(t)\langle U_tf-f,U_tg-g\rangle_2dt-c_A\langle f,g\rangle_2\\
&-\sum_{n\ge2}w_n\{\langle f,U_{\log n}g\rangle_2+\langle f,U_{-\log n}g\rangle_2\}\\
&+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),
\end{split}
\tag{N1}
\]
where alpha, c_A, w_n and the two moments have exactly the values in the request. Q[f]=B(f,f). V_b is the logarithmic finite-energy zero-extension space; it is not replaced by an H1 boundary space. The physical L2 form operator is A_b. The positive whole-line translation-energy operator will instead be denoted by script D. These two operators are not identified.

CONTACT supplies the compact-resolvent and first-contact prerequisites. For the present estimates only their precise consequences are used: fixed-support compact embedding of the form domain, the full bounded perturbation A_b=script D_b+B_b, and the complete finite-rank spectral projector P_b=1_(0,1](A_b). We retain every low eigenspace, its multiplicity, and both parities. No differentiable eigenbasis or transported spectral branch is selected.

### 1.2 Uniform boundedness without positive source dynamics

Put s_a=sum_(2<=n<exp(2a)) w_n. The absolute value of the bounded source perturbation is dominated by convolution with
\[
\nu_a=c_A\delta_0+\sum_nw_n(\delta_{\log n}+\delta_{-\log n})
+2\cosh(a)\mathbf1_{[-2a,2a]}(t)dt,
\quad N_a^{\rm bd}=c_A+2s_a+8a\cosh a.
\]
The diagonal coefficient is positive; the two-pole kernel is 2cosh((x-y)/2). This is an **absolute domination**, not positivity preservation of exp(-t A_b).

For completeness, the needed domination for the positive part-form follows by resolvents. Given nonnegative supported f, compare u=(script D_b+lambda)^(-1)f and v=(script D+lambda)^(-1)f. Test the difference with (u-v)_+. The logarithmic jump form has the lattice property, the test vanishes outside I_b, and its energy is bounded above by zero. Thus u<=v. Resolvent iteration gives the part-semigroup domination. Complex input is controlled by its absolute value.

Dominate each bounded-perturbation insertion in the Dyson series by nu_a and discard intermediate support restrictions. Convolution commutes with the whole-line positive semigroup. Its angular-frequency symbol m satisfies m>=0 and m(xi)>=.5 log(2|xi|) for |xi|>=1, by C4/L17. Plancherel therefore bounds the whole-line L2-to-Linfty norm at time 2 by sqrt(5/(4pi)). The Dyson sum costs exp(2N_a^bd). On the entire low space, exp(2A_b) has norm at most exp(2), so
\[
\|u\|_\infty,\ \|A_bu\|_\infty\le C_a\|u\|_2,
\qquad C_a=e^{2(N_a^{\rm bd}+1)}\sqrt{5/(4\pi)}.
\tag{N2}
\]
This proof has no factor dim(P_b), no inverse low eigenvalue, and no sign assumption on a source eigenfunction. It leaves the reflected-prime obstruction intact.

### 1.3 Domain matching and a uniform boundary constant

Set k(t)=alpha(t)-1/(2t), with its smooth extension k(0)=1/4. The exact source decomposition is
\[
A_b=\tfrac12 L_{\Delta,b}-\log(2\pi)I-K_b-\text{prime shifts}+\text{two poles},
\quad K_b(x,y)=k(|x-y|).
\tag{N3}
\]
To check the constant, the difference of the kernels gives
c_0=2 int_0^1 k+2 int_1^infinity alpha+gamma=-log2-psi(1/4), hence c_0-c_A=-log(2pi). In dimension one the convention in [H] has c_1=1 and rho_1=-2gamma. The two forms have the same logarithmic domain since their singular kernels agree and the remaining fixed-window kernels are L2-bounded. The identity on the smooth core extends in the common form norm; bounded perturbation then identifies the operator domains.

Consequently u in P_b has bounded u and bounded L_Delta,b u. Apply [H] as identified in section 0.2. To make its constant uniform, use the Banach graph space X={v in D(L_Delta,(-1,1)): v,L_Delta v in Linfty}, norm ||v||infty+||L_Delta v||infty. The map v to v/sqrt(ell(dist)) is defined everywhere by that theorem and has closed graph: convergence of v and of its weighted quotient in Linfty identifies the latter limit almost everywhere. The closed graph theorem supplies one finite C_J.

Here ell(t)=1/max(log(1/t),log10). Exact unitary scaling v(t)=sqrt(b)u(bt) gives
\[
L_{\Delta,(-1,1)}v(t)=\sqrt b(L_{\Delta,b}u)(bt)+2\log(b)v(t).
\]
This agrees with [H, Lemma A.3], and also follows from the angular symbol 2log|xi|. Define
\[
V_a^{\rm bd}=|\log(2\pi)|+2\int_0^{2a}|k(t)|dt+2s_a+4a\cosh a,
\quad m_a=\max(|\log(a/2)|,|\log a|).
\]
The Lipschitz bound for max(log(1/t),log10) compares the physical and scaled boundary weights. Combining it with (N2) gives, uniformly a/2<=b<=a,
\[
|u(x)|\le K_a\|u\|_2\sqrt{\operatorname{ell}(\operatorname{dist}(x,\partial I_b))},
\quad
K_a=\sqrt2 C_JC_a(3+2V_a^{\rm bd}+2m_a)\sqrt{1+m_a/\log10}.
\tag{N4}
\]
Real and imaginary parts, then linearity of the weighted map, cover every complex vector. These constants are finite, not numerical certificates.

### 1.4 Rechecked full-response budget

Let tau=min(a/2,.1), k_a=sup_[0,2a]|k| and
\[
B_a^{\rm bd}=K_a/2+C_a[\tfrac12\log(2a/\tau)+2ak_a+s_a+4a\cosh a].
\]
Integrating the same-side singularity in L18 uses
int_0^tau dt/((v+t)sqrt(log(1/t)))<=1+2sqrt(log(1/v)), for 0<v<tau. The far regular, prime, and pole terms retain their full bounds. Thus each of the two profiles is bounded by sqrt(d)||z||[K_a sqrt(log(1/(ds)))+B_a^bd]. Integrating both profiles proves
\[
F^*F\preceq\eta^\sharp_a(d)I,
\quad \eta^\sharp_a(d)=4d[K_a^2(\log(1/d)+1)+(B_a^{\rm bd})^2].
\tag{N5}
\]
With the canonical L16/L19 denominators this gives recovery O_a(d), Y*Y=O_a(d), and e_1Y*Y=O_a(d/log(1/d)^2). The first-contact reduction and these source budgets survive the narrow audit. The rest of Q1 requires an actual signed response relation; sections 2-5 supply it.

## 2. A new uniform modulus for all low zero extensions

The bounded boundary weight alone supplies no normalized endpoint trace. We instead prove enough uniform continuity to control how a prime-shifted low mode varies across a shrinking collar.

### 2.1 An integrable resolvent kernel for the positive archimedean operator

The exact nonnegative decomposition
\[
\alpha(t)=\frac{e^{-t/2}}{2t}+n(t),\qquad n(t)\ge0,\qquad
2\int_0^\infty n(t)dt<\infty
\tag{N6}
\]
follows from 1-e^(-2t)<=2t, n(t)->1/2 at zero, and exponential decay at infinity. The first term has symbol
m_0(xi)=.5log(1+4xi^2), obtained by differentiating the elementary cosine integral with respect to xi and fixing its value at zero.

For every time s>0, (1+4xi^2)^(-s/2) is the characteristic transform of the convolution of a Gamma(s/2,rate 1/2) density and its reflection. This follows directly by integrating t^(s/2-1)exp(-(1/2+i xi)t), dividing by its gamma normalization, and multiplying by the reflected transform. The remaining finite positive measure n(|t|)dt has the compound-Poisson convolution semigroup. The product therefore has a probability density p_s in L1 for every s>0. Its multiplier is exactly exp(-s m), not that of the full source A_b.

It follows by Tonelli that
\[
G=\int_0^\infty e^{-s}p_s\,ds\in L^1(\mathbb R),\quad \|G\|_1=1,
\quad (\mathscr D+1)^{-1}f=G*f,
\quad \|G(\cdot+h)-G\|_1\longrightarrow0.
\tag{N7}
\]
These statements can first be checked on L2 by the multiplier integral, then on bounded data by the L1 convolution. They make no claim about positivity of a full Weil resolvent.

### 2.2 Localization without differentiating a low eigenfunction

Fix 0<delta<min(a/4,.1). Choose smooth cutoffs chi_(b,delta), equal to one at distance at least delta from both endpoints, zero at distance at most delta/2, with Lipschitz constant at most C_chi/delta and values in [0,1]. For bounded u in P_b, the distributional commutator is
\[
\mathscr D(\chi u)-\chi\mathscr D u
=\int_{\mathbb R}\alpha(|x-y|)(\chi(x)-\chi(y))u(y)dy.
\tag{N8}
\]
Prove it first for truncated jump kernels and smooth approximants. Its absolute bound is
2 C_a||u||_2 int_0^infinity alpha(t) min(1,C_chi t/delta)dt, which is finite. Dominated convergence proves (N8) in distributions. No pointwise differentiability or Dini hypothesis on u was used.

On I_b, script D u=A_bu-B_bu is bounded by (N2) and the bounded perturbation estimate. Multiplying this weak equation by chi is legitimate because chi is supported strictly inside I_b. The commutator is bounded and decays exponentially outside a fixed larger interval. Thus f=(script D+1)(chi u) belongs to L2 and Linfty, with ||f||infty<=H_(a,delta)||u||_2 uniformly in b. The form characterization of the operator domain identifies chi u=(script D+1)^(-1)f. Equation (N7) gives
\[
\|(\chi u)(\cdot+h)-\chi u\|_\infty
\le H_{a,\delta}\|G(\cdot+h)-G\|_1\|u\|_2.
\]
The removed boundary strips have supremum at most K_a||u||_2/sqrt(log(1/delta)) by (N4). Consequently the continuous zero extensions satisfy
\[
\omega_a(h):=\sup_{\substack{a/2\le b\le a\,,\ u\in P_bL^2\,,\ \|u\|_2\le1}}
\ \sup_{|t|\le h}\|u(\cdot+t)-u\|_\infty\longrightarrow0.
\tag{N9}
\]
Indeed the upper bound is 2K_a/sqrt(log(1/delta)) plus H_(a,delta) sup_(|t|<=h)||G(.+t)-G||_1. First fix delta small, then take h small. This proves a common modulus for the **whole** family, not continuity separately for an arbitrarily changing list of eigenvectors. It is a qualitative modulus with an explicit defining bound, not a claimed power law.

## 3. The actual signed boundary averages

### 3.1 Canonical split and a fixed two-dimensional profile space

Take the canonical L4/L16 split: b=a-d, c=c_d>0, r_d=c+log2, kappa=epsilon_C+j_a(d), q=kappa/r_d<=1/2. Write
\[
\mathscr H=L^2(0,1)\oplus L^2(0,1),\quad
D=cI+L_2+E-T_H\ge(r_d-\kappa)I,
\quad \mathsf M=\operatorname{diag}(\mu_j).
\]
L_2, E, and T_H are precisely canonical L9-L19. In particular T_H contains the complete core sector above 1; its floor 1 is proved by the spectral cutoff, not guessed from a gap. No other low modes are eliminated.

Let iota:C^2->H be the isometry iota(q_+,q_-)=(q_+1,q_-1). Let Pi=iota iota*. Define
\[
\boxed{\beta=(dc)^{-1/2}\iota^*F,\qquad H=(I-\Pi)F,\qquad
F=\sqrt{dc}\,\iota\beta+H,\quad\iota^*H=0.}
\tag{N10}
\]
The symbol H here denotes the mean-zero column operator only; it is not a high-core spectral projection. Its domain is the same complete low coefficient space C^r as F. By (N5),
\[
\|\beta\|\le B_0(d):=\sqrt{\eta^\sharp_a(d)/(dc)}=O_a(1).
\tag{N11}
\]
This finite-dimensional profile split does not assert that the resolvent preserves physical orthogonality.

### 3.2 Formula for both rows, including every source sign

For u=u_z=sum_j z_j phi_j, zero extended, put N=ceil(exp(2a))-1. The row beta_+(u) is exactly
\[
\begin{split}
\frac1{d\sqrt c}\bigg[&-\int_{-b}^b u(y)\int_b^a\alpha(x-y)dx\,dy
-\sum_{n=2}^{N}w_n\int_{b-\log n}^{a-\log n}u(t)dt\\
&+2(e^{a/2}-e^{b/2})M_-(u)
+2(e^{-b/2}-e^{-a/2})M_+(u)\bigg].
\end{split}
\tag{N12+}
\]
The other row beta_-(u) is exactly
\[
\begin{split}
\frac1{d\sqrt c}\bigg[&-\int_{-b}^b u(y)\int_{-a}^{-b}\alpha(y-x)dx\,dy
-\sum_{n=2}^{N}w_n\int_{-a+\log n}^{-b+\log n}u(t)dt\\
&+2(e^{-b/2}-e^{-a/2})M_-(u)
+2(e^{a/2}-e^{b/2})M_+(u)\bigg].
\end{split}
\tag{N12-}
\]
These follow by integrating L18 in the rescaled variable and substituting x=b+ds or x=-b-ds. Fubini is licensed by the integrable logarithmic singularity against bounded u; alternatively its absolute integral is bounded directly by (N5)'s profile estimate. Every prime power is kept. The integer endpoint excluded by N has zero overlap, exactly as in L4. Both pole coefficients have been integrated, not declared zero.

These are signed **strip averages**, not limiting endpoint traces. The singular contribution contains the logarithm log((t+d)/t), while the prime terms sample actual interior strips. Products beta*beta include the mixed archimedean, arithmetic, and pole products. For an odd vector the reflection changes the appropriate row sign; working with two rows retains this automatically.

### 3.3 The mean-zero part is smaller than sqrt(d)

For 0<d<tau^2, let ell_d=log(1/d), k'_a=sup_[0,2a]|k'|. The latter is finite because the singularity was removed in k. Compare the plus singular profile with its value at s=1. Write g(t)=u(b-t). The difference involves
\[
\int_0^{2b}g(t)\left(\frac1{t+ds}-\frac1{t+d}\right)dt.
\]
For 0<t<d, (N4) and the nonnegative kernel difference bound its magnitude by K_a||z|| log(1/s)/sqrt(ell_d). For d<t<tau, split at sqrt(d); the bound is
K_a||z||[sqrt(2)/sqrt(ell_d)+sqrt(d)/sqrt(log(1/tau))]. For t>=tau it is at most C_a||z||d/tau. These estimates use t as the actual distance to the nearer endpoint only where t<tau<=b.

The regular archimedean part varies by at most 2a C_a d k'_a||z||. The two-pole part varies by at most 2a C_a d e^a||z||. Every shifted source value varies by at most omega_a(d)||z||, so the **full** prime contribution varies by at most s_a omega_a(d)||z||. The negative sign of that contribution was not changed; absolute values are used only to bound this variation, after retaining its mean in (N12).

Since ||log(1/s)||_(L2(0,1))=sqrt(2), both components yield
\[
\boxed{\|H\|\le\sqrt d\,h_a(d),\qquad h_a(d)\longrightarrow0,}
\tag{N13}
\]
where one sufficient explicit expression is
\[
\begin{split}
h_a(d)=\sqrt2\bigg[&\frac{\sqrt2K_a}{\sqrt{\ell_d}}
+\frac{K_a\sqrt d}{2\sqrt{\log(1/\tau)}}+\frac{C_ad}{2\tau}\\
&+2aC_ad(k'_a+e^a)+s_a\omega_a(d)\bigg].
\end{split}
\]
Projection onto the mean-zero subspace contracts the norm of the difference from any constant profile, including the endpoint comparison just used. Continuous representatives are available by (N4)/(N9), and that endpoint is a positive distance d outside the core. No value of a rough representative at the original core boundary was presumed. Equations (N10)-(N13) are dimension-free source relations.

## 4. Concrete signed repair: do not scalarize the whole inverse

### 4.1 The constant profile belongs to the operator domain

For the universal L from L11, direct polarization against compact smooth tests gives
\[
L1=V(s)=-\tfrac12\log(s(1-s)),\qquad
\int_0^1V(s)ds=1,\qquad \|V\|_2\le\sqrt2.
\tag{N14}
\]
The constant function has finite form energy, and V is in L2. Core density and the operator representation therefore prove 1 in D(L), not just a formal identity. This pays the operator-domain use of iota below. The endpoint potential is not replaced by log2 or by its average on arbitrary profiles.

Put W=L_2+E-T_H, so D=cI+W. Define the bounded two-column operator and its Hermitian two-by-two compression
\[
Z=W\iota,\qquad
\mathcal A_\partial=\iota^*W\iota
=I_2+\iota^*E\iota-\iota^*T_H\iota,
\quad \|Z\|\le\sqrt2+\kappa.
\tag{N15}
\]
The high-core sign here is negative. It remains the complete source inverse, including mixed recovery, not a prime-only or scalar inverse.

### 4.2 Exact identity with a positive full variance remainder

The identity D iota=c iota+Z gives
\[
D^{-1}\iota=c^{-1}\iota-c^{-1}D^{-1}Z,
\]
\[
\iota^*D^{-1}\iota=c^{-1}I_2-c^{-2}\mathcal A_\partial+c^{-2}Z^*D^{-1}Z,
\quad
\iota^*D^{-1}H=-c^{-1}Z^*D^{-1}H.
\]
The last equality uses only iota*H=0 **before** the inverse; its right side is precisely the resolvent mixing that cannot be omitted. All formulas are valid for the unbounded W because its only un-inverted action is on iota, whose operator domain was proved in (N14).

Expand F from (N10), retaining the two mixed products. Completing the remaining square proves
\[
\boxed{F^*D^{-1}F=d\beta^*\beta-\frac d c\beta^*\mathcal A_\partial\beta
+\mathcal Z^*D^{-1}\mathcal Z,
\qquad \mathcal Z=H-\sqrt{d/c}\,Z\beta.}
\tag{N16}
\]
This is the promised **signed boundary-response relation**, not an operator-norm upper bound. The last matrix is positive semidefinite and contains all mean/mean-zero mixing and all remaining feedback. Nothing in (N16) says cD^(-1) tends to identity in norm; the false scalarization of L14 stays rejected.

Moreover every complex coefficient vector is covered by
\[
0\preceq\mathcal Z^*D^{-1}\mathcal Z\preceq d\sigma_a(d)I,
\quad
\sigma_a(d)=\frac{[h_a(d)+(\sqrt2+\kappa)B_0(d)/\sqrt c]^2}{r_d-\kappa}
=o_a(1/c).
\tag{N17}
\]
The denominator is the proved full D floor. The little-o follows from h_a(d)->0, B_0 bounded, kappa bounded, and c~log(1/d). This bounds the entire variance, not the first few feedback terms. It is a paper bound with nonnumerical constants and modulus, not an interval computation of its entries.

### 4.3 The two-dimensional correction tends to identity

We next show
\[
t_a(d):=\|\iota^*T_H\iota\|\longrightarrow0,
\qquad \mathcal A_\partial\longrightarrow I_2.
\tag{N18}
\]
Fix q in C2 and put f_d=J U_d^(-1)iota q, as a core function extended by zero to (-a,a). The source cross bound makes f_d bounded in L2. For a fixed compact smooth h supported strictly inside (-a,a), eventually h is in the smaller core. Its exterior source response J*h on the two collars is uniformly bounded: its archimedean kernel is separated from the support, every shifted h is smooth, and both pole moments are finite. Hence <h,f_d>=O_(a,h)(sqrt(d))||q||. Density and the uniform L2 bound prove f_d converges weakly to zero.

Let x_d=A_H^(-1)(I-P_b)f_d. Its norm is bounded by ||f_d|| because A_H>=1. Its full energy equals <(I-P_b)f_d,x_d> and is bounded. The bounded source perturbation therefore bounds its positive Dirichlet energy uniformly. All x_d have support in [-a,a]. The fixed-support compact form embedding gives a strongly convergent subsequence of any such bounded sequence. Along it, <f_d,x_d> tends to zero by the weak convergence of f_d. Thus every sequence gives limit zero for this nonnegative quadratic pairing. It is exactly <q,iota*T_H iota q>. Finite-dimensional polarization gives (N18) in the two-by-two operator norm. Finally ||E||=O_a(d).

This proof requires neither convergence of P_b nor a smooth eigenbasis, and it does not claim that T_H itself tends to zero in operator norm. In particular all its coupling to nonconstant profiles remains inside (N16). Eventually A_partial>=I_2/2, but the conclusion is fixed-a and not a global source lower sign.

Combining (N16)-(N18) yields the genuinely signed subleading law
\[
\boxed{F^*D^{-1}F=d(1-c^{-1})\beta^*\beta+\mathcal E_{a,d},
\qquad \|\mathcal E_{a,d}\|=o_a(d/c).}
\tag{N19}
\]
An explicit bound is d rho_a(d), where
rho_a(d)=sigma_a(d)+B_0(d)^2(epsilon_C+t_a(d))/c=o_a(1/c).
There is **no** claim that beta or M/d has a limit. The negative coefficient in the recovery comes from the actual average of the universal endpoint potential, together with the proved vanishing of the constant-channel high response.

### 4.4 Compatibility with the frozen one-feedback formula

The canonical one-feedback remainder is exactly
\[
0\preceq F^*D^{-1}F-G_1
=Y^*T^2(I+T)^{-1}Y\preceq e_1Y^*Y,
\quad e_1=q^2/(1-q).
\tag{N20}
\]
It follows by the scalar identity (1+t)^(-1)-(1-t)=t^2/(1+t) and self-adjoint functional calculus. With (N5), its norm is at most e_1 eta_a^sharp(d)/r_d=O_a(d/c^2). Therefore G_1 has the same signed expansion (N19), with an additional completely bounded error of that size. No feedback order was increased, and no high-source term was removed.

**Q1 result:** the narrow imported input and the actual d-dependent signed response are proved at the stated paper scope. FIRST_FAILURE Q1: none identified in this derivation. Independent checking of the new lemmas remains pending; the three missing shelf rehashes remain an integrity limitation, not a silently completed check.

## 5. Q2: actual comparison attempt and its first failure

### 5.1 Why a leading positive gap has not been obtained

The first attempted mechanism was to use the now-computable leading response to prove a source trace-energy inequality of the form
\[
\mathsf M-d\beta^*\beta\succeq\epsilon_a d I
\tag{N21-attempt}
\]
for one sufficiently thin admissible collar at each hypothetical contact. Such an independently proved inequality would indeed dominate the o(d) error. It does **not** follow from (N2)-(N5), the source equation on the core, or the positive diagonal blocks.

The exact obstruction in the derivation occurs when the core equation is paired with the boundary-average functional. Positivity of A_b gives only
\[
|q^*\beta z|^2\le (z^*\mathsf Mz)\,(q^*\beta\mathsf M^{-1}\beta^*q).
\]
The second factor is the actual two-boundary inverse energy. The source means (N12) do not make it diagonal or supply the needed upper bound. Replacing it by ||beta||^2/mu_min returns the forbidden worst-eigenvalue estimate. The equation has not produced a lower bound for M at scale d.

**FIRST_FAILURE of this attempt:** the signed inequality (N21-attempt), not boundary boundedness or convergence of the paid feedback tail. It is left unproved, not labelled false for the theta source. No hypothetical contact has been exhibited.

### 5.2 The source identity that makes leading cancellation precise

At a hypothetical actual contact, canonical L20-L21 supply a nonzero z in ker(S), with its full reconstructed source null vector. Testing the local null equation against its core and collar components, then eliminating the high component, yields Mz=F*D^(-1)Fz. Substitution of the source identity (N16), not a chosen asymptotic trace, gives
\[
\boxed{z^*\mathsf Mz
=d\|\beta z\|^2-\frac d c\langle\beta z,\mathcal A_\partial\beta z\rangle
+\|D^{-1/2}\mathcal Zz\|^2.}
\tag{N22}
\]
Thus for unit null z the leading order cancels, and
z*(M-d beta*beta)z=-(d/c)||beta z||^2+o_a(d/c), uniformly. If the boundary mean stays bounded away from zero along such a sequence, the next term has the displayed negative sign. If beta z tends to zero, this assertion does not provide a relative estimate or force z=0. That branch is retained.

Equation (N22) is a consequence **under the proposed contact premises**. It is not an actual-source counterexample to a contradiction-proof target. Nor does it prohibit a future independent source theorem from proving a strict inequality and thereby excluding those premises. What it prohibits is treating the computed leading response or a vanishing error as such an independent theorem.

### 5.3 Concrete repair and the complete surviving remainder

The repair is to keep the signed two-by-two correction **and the positive variance**, instead of assuming an order-d gap or increasing feedback depth. Define
\[
\Xi_{a,d}=\mathsf M-d\beta^*\beta+(d/c)\beta^*\mathcal A_\partial\beta.
\]
Equations (N16)-(N17) give the exact identity and lower envelope
\[
\boxed{\mathsf S=\Xi_{a,d}-\mathcal Z^*D^{-1}\mathcal Z,
\qquad \mathcal L_\partial:=\Xi_{a,d}-d\sigma_a(d)I\preceq\mathsf S.}
\tag{N23}
\]
All entries in beta are the signed, integrated source expressions (N12). A_partial and Z retain the actual two-pole collar perturbation and the entire high-core inverse. The remaining square is positive, not an error whose sign is guessed.

The first unpaid assertion after this concrete repair is
\[
\boxed{\begin{gathered}
\forall a>a_0\text{ with the first-contact premises},\quad
\exists\ d\text{ satisfying L4/L16, }d<a-a_0,\ d<\tau_a^2:\\
\lambda_{\min}(\Xi_{a,d})>d\sigma_a(d).
\end{gathered}}
\tag{N24-target}
\]
This is a precise **relative source boundary-mean energy comparison**. Neither the existence of finite K_a, the sign A_partial>=I_2/2, nor sigma=o(1/c) establishes it. The positive correction of order d/c is useful only after controlling the signed deficit M-d beta*beta at that same scale for every coefficient vector.

The work above pays the response side, including a new signed coefficient and all residual variance. It does not pay that core-energy side. No claim of a reduced logical difficulty of RH is made. Q2 therefore remains PARTIAL_WITH_PRECISE_REMAINDER, with FIRST_FAILURE exactly (N24-target). The wider source exclusion is not refuted.

## 6. Q3: original-form transfer and adversarial controls

### 6.1 The full conditional chain

For any physical v=u_z+x_H+w in V_a, canonical L20 gives
\[
Q[v]=Q_H[x_H+A_H^{-1}J_Hw]
+\|D^{1/2}(U_dw+D^{-1}Fz)\|^2+z^*\mathsf Sz.
\tag{N25}
\]
The two first terms have positive floors 1 and r_d-kappa. The triangular change of variables and its inverse are bounded in physical L2 because J and the required positive inverses are bounded. All components remain in the appropriate form domains by bounded perturbation and the proved sharp restriction. Hence a positive lower matrix L_partial in (N23) yields a strictly positive full-window Rayleigh floor. If there are no low modes, the two positive squares already suffice.

Conversely at equality S has a nonzero null z and the actual vector is
w=-U_d^(-1)D^(-1)Fz, x_H=-A_H^(-1)J_Hw, v=u_z+x_H+w. Its nonzero low component prevents v from vanishing. This checks the direction and normalization of the transfer; a normalized quotient has not replaced an unnormalized form identity.

If (N24-target) were proved independently, a hypothetical first contact would be positive by (N23)-(N25), contradicting its attained zero bottom. The CONTACT positive anchor, continuity and nested domains then rule out every later nonpositive window. Every complex compact smooth test lies in one such window, so Q[f]>=0 for all these tests, the exact input of the published Weil criterion. [COFINAL_FAMILY][CONDITIONAL]

The only unproved mathematical link in this **chosen** sign chain is (N24-target). The hash-verification limitations are separate and remain disclosed. No uniform positive gap, simple eigenvalue, parity restriction, normalized trace limit, or RH-conditional prime estimate was introduced. FIRST_FAILURE Q3 is its dependence on that unproved strict source comparison. LOWER_SIGN_PROVED remains false.

### 6.2 Required scaled algebraic discriminator

For the request's scalar data A=d, C=ell_d, J=t sqrt(d ell_d), exact elimination gives recovery=d t^2 and S=d(1-t^2). With R=C, E=T_H=0 and the conservative q=1/ell_d, the actual unretained response is zero but its sufficient envelope is positive. At d=exp(-4), t=1,
\[
e_1=\frac{(1/4)^2}{1-1/4}=\frac1{12},\qquad
\mathcal L_1=-e^{-4}/12<0,\qquad \mathsf S=0.
\tag{N26}
\]
The detector must return exact equality for S and failure of this sufficient lower certificate, not a negative source direction. For |t|<1, =1, >1 the exact signs remain positive, zero, negative. No numerical rerun was needed.

The new signed correction also has a useful algebraic control. In a scalar constant-profile model take W=1, D=c+1, H=0, F=t sqrt(d(c+1)), M=d. Then beta=t sqrt((c+1)/c), A_partial=Z=1, and (N16) gives
\[
d\beta^2-\frac d c\beta^2+\frac d{c(c+1)}\beta^2=dt^2.
\tag{N27}
\]
Equality at t=1 survives **even with** the negative subleading term and the exact positive residual. This model lacks the actual arithmetic core and universal infinite-dimensional collar; it checks algebra only. The new proved source properties are (N9), the exact shifted-strip rows, and the true V(s) endpoint potential. They have not been proved to enforce (N24-target), so no false claim that they already separate the source equality case is made.

A separate exact complex matrix check of (N16) was executed with positive Hermitian D of size three, a two-column isometry iota, and complex F. Its symbolic residual was exactly zero. This is a conjugation control, not a proof of the operator/domain argument or the source sign.

### 6.3 A boundary-bound falsifier that is not an eigenfunction

Near zero the compactly tapered profile
u(t)=sin(log log(1/t))/sqrt(log(1/t)) is continuous with zero endpoint value and satisfies the same absolute boundary envelope. Its derivative is bounded by a constant times 1/(t log(1/t)^(3/2)), so it has bounded variation. Bounded amplitude and variation imply squared translation differences O(t), hence finite logarithmic form energy. Nevertheless its quotient by 1/sqrt(log(1/t)) has no limit.

This example is in the source form domain, not claimed to solve the source eigen-equation. It refutes only the inference from that domain and absolute boundary estimate to a normalized endpoint trace. Our averages (N12) and the common modulus proof avoid that inference entirely.

## 7. Dependency ledger and what was actually preserved

| Supplier | Domain and quantifiers | Input/output and proof locator | Status |
|---|---|---|---|
| Literal source/window realization | Every fixed a; all complex V_a | C1-C8 and canonical L4-L19, rechecked as used | [ABSTRACT][PAPER] |
| Bounded entire low space | All b<=a, all vectors in P_b | Absolute perturbation domination gives u and A_bu in Linfty, (N2) | [ABSTRACT][PAPER] |
| Uniform boundary bound | All a/2<=b<=a, all low vectors | N3, [H] with matching domain, fixed graph estimate and scaling, (N4) | [ABSTRACT][PAPER; published theorem import] |
| Common zero-extension modulus | Same low family, not chosen branches | Positive archimedean resolvent density and localized weak equation, (N6)-(N9) | [ABSTRACT][PAPER] |
| Actual leading source means | Every admissible d, all coefficient vectors | Both signed rows (N12), full-profile variance (N13) | [ABSTRACT][PAPER] |
| Full signed response and remainder | Positive core and admissible collar; whole low space | Exact identity (N16), bound (N17), constant-channel limit (N18) | [ABSTRACT][PAPER under stated local hypotheses] |
| Comparison with low energy | Every hypothetical contact, one admissible d | Xi must dominate the positive variance; (N24-target) | [COFINAL_FAMILY][CONDITIONAL; unproved] |
| All-test lower sign | All complex compact smooth tests | N23-N25 and CONTACT first-contact reduction, conditional on N24 | [COFINAL_FAMILY][CONDITIONAL] |

No raw theta normalization is changed: this batch does not construct a new theta trial at all. Physical L2 orthogonality is used only for the exact projections where it holds; it is never presumed to survive D^(-1) or the core inverse. Boundary points -a,-b,b,a are included through zero-extension forms; the cutoff proof covers both inner transition regions. No trace, endpoint atom, prime power, pole, parity or high-core response is discarded.

## 8. One next_decisive_test and closeout

### 8.1 The single directive

**next_decisive_test: SIGNED_STRIP_MEAN_TRACE_ENERGY_DEFICIT.** Use exactly the full-source rows (N12), the two-by-two matrix (N15), and the all-vector error (N17). The terminal observable is
\[
\Gamma(a,d)=\lambda_{\min}\left[\mathsf M-d\beta^*\beta+(d/c)\beta^*\mathcal A_\partial\beta\right]-d\sigma_a(d).
\tag{N28}
\]
The requested paper lemma is: for each a satisfying the first-contact premises, at least one d satisfying L4/L16, d<a-a0 and d<tau_a^2 has Gamma(a,d)>0. The task is to derive the **core-energy comparison for these actual integrated source rows**, not to re-prove their O(d) response scale. All coefficients and both rows must be treated together.

Success requires a strictly positive lower bound with its quantifiers proved; (N23)-(N25) then complete this route. A negative upper enclosure for one proposed finite-parameter sufficient margin rejects only that envelope at those parameters. An enclosure containing zero is UNRESOLVED. The exact-zero discriminator is a proved strict matrix inequality or the exact full equality system, not additional digits of Gamma.

**Stop condition:** if the proposed argument uses only ||beta||, mu_min^(-1), q->0, or the already proved A_partial->I without a signed estimate of M-d beta*beta, stop that subattempt and return the precise failed inequality. Do not increase feedback order, dimension, precision, or the window. This is a symbolic/source-estimate directive, not authorization for a new numerical campaign.

The gate for the receiving paper reviewer is to check N6-N18 at their actual domains, verify N16 with nonzero resolvent mixing, and reject any attempted transfer at N24 unless its full matrix inequality is proved. No Lean source was written, so there is no new Lean command or axiom profile to report; a later formalization is not admitted by this documentation commit.

### 8.2 Two candidate re-representations, not two execution directives

| Representation | What it preserves and exposes | Main risk | Kill-power / cost estimate |
|---|---|---|---|
| Selected: signed strip means plus exact positive variance | Actual prime/pole averages, all low modes, full high response; explicit leading and negative next coefficient | Missing relative trace-energy comparison with M | 9/10 / 5/10 |
| Alternative: weak finite-displacement Green identity for the same source | Avoids unproved endpoint limits and smooth eigenbranches; can couple smaller-window energies directly to deleted strips | A new signed inequality is still needed; locality cannot be imposed on prime shifts | 8/10 / 7/10 |

These are planning estimates, not theorem probabilities or permission to launch additional work. A Hadamard trace formula is not a third supplier secretly imported into the proof.

### 8.3 Frozen predictions

| Prediction, unchanged probability | Fate | Evidence at the stated scope |
|---|---|---|
| P1, .90: new uniform input survives | CONFIRMED | N2-N5, matching primary theorem/domain and fixed-window closed-graph scaling; no new inverse-eigenvalue or rank factor |
| P2, .95: rates and o(d) error do not exclude equality | CONFIRMED | Exact scaled control N26 and retained source balance N22; no sign inferred from a small error |
| P3, .80: partial with new proved relation or exact mechanism refutation | CONFIRMED | New full-source signed N16/N19; strict comparison N24 remains unproved |
| Continued own registration, .78: two-boundary leading representation with uniform o(d) remainder | CONFIRMED | N9-N19 prove it, in fact with an explicit negative d/c correction and o(d/c) remainder |

The own event was registered before the source decomposition in the continued attempt. These scores report this paper derivation, not independent validation of the new mathematics. No old numerical forecast or closed scalar test was rescored.

### 8.4 Meta closeout and consumer-first contract

What became smaller: the response's first two terms are explicit signed two-boundary means, rather than just an absolute O(d) norm. Its remaining variance has a known sign and a complete bound. What did not close: the comparison of the actual small core energies with those means. There is no source counterexample, no first-contact exclusion, and no all-test lower-sign result.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_every_such_test
  ORIGINAL_REQUESTED_OBJECT: signed_boundary_response_strictly_below_actual_low_core_energies
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - direct_all_test_nonnegativity
    - all_large_window_lower_envelope_with_error_tending_to_zero
    - any_independently_proved_first_contact_kernel_exclusion
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: signed_two_mean_response_and_positive_variance_with_actual_source_modulus
  REOPEN_TRIGGER: a_signed_core_energy_inequality_for_N12_above_the_N17_budget
CLOSES:
  - boundary_input_narrow_audit
  - all_low_zero_extension_common_modulus
  - full_signed_mean_response_identity_and_its_fixed_a_subleading_coefficient
CARRIES_OPEN:
  - canonical_COLLAR_L29_strict_source_comparison
  - first_contact_exclusion
  - all_test_lower_sign
OPENS: []
iteration:
  target: GOAL058_SIGNED_BOUNDARY_LOW_ENERGY_COMPARISON
  status: OPEN
  progress_class: REPRESENTATION_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: infer_a_strict_leading_gap_from_absolute_boundary_control
  new_gap_name: signed_strip_mean_trace_energy_deficit
  invariant_learned: source_mean_and_positive_variance_must_be_compared_to_the_same_full_low_energy_matrix
  forbidden_future_move: discard_mean_zero_resolvent_mixing_or_assume_a_normalized_endpoint_trace
  next_decisive_test: SIGNED_STRIP_MEAN_TRACE_ENERGY_DEFICIT
  route_score: 4
```

No KILL_ROUTE_FAMILY is issued. The scalar controls reject general inferences only; the oscillating profile rejects a boundary-limit inference only. They do not prove mathematical death of the unchanged source target. Publication certifies a durable paper record, not independent mathematical acceptance.

## 9. PROSHKA'S OWN LINE

I keep the signed source averages because they retain the arithmetic that the absolute bound discards.
The two collar means are simple enough to write as actual integrals.
They do not require an endpoint trace that nobody has proved.
I did not choose a smooth-eigenbranch argument.
The moving low projector can change rank at the cutoff, and our estimates do not need to prevent that.
I also did not choose the worst core eigenvalue as the first bound.
That substitution loses the coupling information before the source has a chance to contribute.
The first move beyond this batch is a signed energy inequality for the two rows in N12.
It must compare those rows with the same low modes and the same core energies.
An argument that replaces the rows by their norms has not performed that move.
The second possible move is a weak finite-displacement identity for the source equation.
It must retain shifted arithmetic strips rather than pretend that the operator is local.
An unproved boundary trace or differentiable eigenbasis would invalidate that move.
The new negative response correction is real, but it is not free positivity.
Its positive residual square has the opposite effect on the final lower margin.
The exact identity makes those two effects impossible to confuse.
The data I would ask for are paired source energy and signed strip-average records.
Another table of small eigenvalues without the corresponding source profiles would not answer this question.
The complete high-core response must stay attached to any such record.
I was surprised that an integrable archimedean resolvent kernel gives the needed common modulus so directly.
That argument uses positive jump geometry only where it is actually positive.
It does not restore a positivity-preserving semigroup for the odd source operator.
I distrust the phrase leading order when the proposed leading coefficient has not been identified.
Here that coefficient is explicit, but it is still allowed to depend on the collar width.
I also distrust treating a vanishing absolute error as a relative error near zero energy.
The remaining obstacle is now a signed trace-energy comparison, not boundary regularity.
The present file records exactly that distinction.

## 10. RESEARCH LOG

### 10.1 Sources actually consulted

The repository base and exact SHA/blob locators are in section 0.1. References to external literature are version-specific, not moving assertions about a latest version.

| Source | READ / RELAY and exact use |
|---|---|
| Authoritative BOUNDARY request at b574857250e2c0e136bb04cfddd906ea1b3aee8f | READ full attached text and pinned connector content; both hashes and all counts recomputed; controls, scope and response schema |
| PROSHKA_SYSTEM_PROMPT_v2.md at rh_clean, blob eba04b799176c9e6a1d5f7fc4061280cfbf96ad4 | READ in this continued task, refreshed response-format tail; no closed-file mutation or proof-by-publication |
| C, CONTACT C1-C8/C19-C25 | READ applicable exact source/domain and coupling arguments; existing first-contact prerequisites retained, not rerun as a new batch |
| L, canonical COLLAR L4-L29 | READ pinned arithmetic separation, universal L, full columns and high-core elimination; old alternate local labels rejected |
| I, COLLAR independent audit | READ applicable scope and source limitations; acceptance receipts are provenance, not premises |
| I, Additional source-boundary derivation and Parent verification supplement | READ full working derivation used here; absolute Dyson domination and exact log-Laplacian identification rechecked in section 1 |
| I, Uniform-boundary extension and explicit full-response estimate | READ full; closed-graph constant, scaling, complete low space and o(d) feedback error rechecked in section 1 |
| J, CONTACT independent audit and reflected-prime qualifications | READ applicable operator/source limitations and semigroup obstruction; no even-sector or sign theorem imported from it |
| P, BATCH_PATTERNS.md | READ full outside routeB_bus because this exact request pins it; proof-attempt and research-log requirements; content independently rehashed |
| H, arXiv:2401.18033v2, https://arxiv.org/html/2401.18033v2, Theorem 1.1, (1.2)/(1.15)-(1.19), section 4 proof, Lemma A.3 | READ exact primary HTML; matching bounded weak-solution boundary theorem and scaling only; no Hopf conclusion imported |
| H's cited barrier and continuity dependencies | RELAY within the published proof; not all independently re-proved or separately fetched; explicitly retained import boundary |
| Alternative local COLLAR, SHA41c760d4... | Bytes inspected only for identity/quarantine; NOT a mathematical source for canonical L4-L29 |
| Exact raw-GitHub download attempts | FAILED acquisition, including DNS failure; not source evidence and not completion of the three missing shelf SHA checks |
| Local SymPy algebra control | EXECUTED exact complex matrix identity and e1=1/12 arithmetic; no source numerical experiment |
| GitHub publication/readback | Actual commit, parent, changed paths and hashes belong to the external delivery receipt; no fabricated write status is encoded here |

No new paper theorem beyond the identified boundary import was used. The gamma-convolution, commutator, mean-response and compactness arguments are supplied in this verdict. No Lean proof, source eigensolve, interval certificate, old scalar rerun or PDF-byte verification was performed.

### 10.2 Branches attempted or rejected

| Candidate | First failed or restrictive step |
|---|---|
| Absolute O(d) recovery plus o(d) feedback implies sign | It does not compare M with recovery; the scaled scalar equality control passes all those scales |
| Boundary envelope supplies a normalized endpoint limit | The bounded-variation oscillating profile in section 6.3 satisfies the domain and envelope but has no such limit |
| Leading order-d positive trace-energy gap | N21 has no source proof; positive-core Cauchy-Schwarz leaves the full inverse boundary energy unpaid |
| Relative scalarization of the entire collar inverse | Canonical L14 gives exact relative norm error one; this false step is never used |
| Physical mean-zero columns stay orthogonal after D inverse | The exact cross term is -c^(-1)Z*D^(-1)H; keeping it produces N16 |
| Drop stable low modes and follow a convenient ground branch | No such projection is made; all low modes are retained so no projector-transport or simplicity hypothesis is needed |
| Vanishing high response on every collar profile | Only its two constant-channel compression tends to zero by N18; the full high inverse remains |
| A positive subleading boundary correction proves the comparison | The positive variance and the signed core deficit must both be controlled; N27 preserves equality |

### 10.3 Reusable identities and exact limits

N6-N9 prove an integrable positive archimedean resolvent and a common modulus for the actual full-source low eigenspaces.
N12 gives two explicit signed source strip-average rows, including every prime power and both pole moments.
N13 proves uniform o(sqrt(d)) response after subtracting those physical means.
N16 is the exact mean/correction/positive-variance identity, with no false resolvent orthogonality.
N17 bounds the entire variance for every coefficient vector.
N18 shows constant-channel high-core recovery tends to zero without eigenbasis transport.
N19 identifies the negative d/c correction but does not assert convergence of its d-dependent coefficient.
N22 records the actual conditional contact balance rather than inventing a leading positive gap.
N23 gives a complete sufficient lower envelope; its strict sign remains N24, not a proved supplier.

The final outcome is a partial paper proof with a new signed source response calculation. The all-test lower sign remains unproved, and PX_RH_CLAIM remains NOT_MADE.
