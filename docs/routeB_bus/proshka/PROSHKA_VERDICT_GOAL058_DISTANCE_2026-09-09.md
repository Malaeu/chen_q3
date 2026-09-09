# STATUS: TRY_NORMALIZED_WINDOW_RAYLEIGH_WITH_EXPLICIT_OFFLINE_WINDOW
```yaml
OPERATIVE_CLASS: TRY_NORMALIZED_WINDOW_RAYLEIGH_WITH_EXPLICIT_OFFLINE_WINDOW
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-09-DISTANCE
BOUNDARY_ID: GOAL058_WINDOW_FLOOR_AS_Q_DISTANCE_OF_THE_THETA_TAIL
RESULT:
  OVERALL: PARTIAL_WITH_PRECISE_REMAINDER
  Q1: PROVED_ON_CLASS
  Q1a: PROVED_ON_CLASS
  Q1b: PROVED_ON_CLASS
  Q1c: PROVED_ON_CLASS
  Q2: PARTIAL_WITH_PRECISE_REMAINDER
  Q2a_LITERAL_UNNORMALIZED_UPPER: PROVED_ON_CLASS
  Q2a_NORMALIZED_T_SQUARED_UPPER: OBSTRUCTION_NAMED
  Q2b_LITERAL_POSITIVE_DISTANCE_LOWER: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q2b_NORMALIZED_T_SQUARED_LOWER_UNDER_RH: OBSTRUCTION_NAMED
  Q2c_ORTHOGONAL_PROJECTION_MECHANISM: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
  Q2c_CONSTRAINED_STATIONARITY: PROVED_ON_CLASS
  Q3: PARTIAL_WITH_PRECISE_REMAINDER
  Q3a: PROVED_ON_CLASS
  Q3b: PARTIAL_WITH_PRECISE_REMAINDER
  Q3c: PROVED_ON_CLASS
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 19054597ea92cd6d696f087a4676345ef067813f
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_DISTANCE_2026-09-09.txt
  GIT_BLOB: 5ba3cb9ce440e3b3c4e1004f1aefc5b518de2e32
  SHA256: 9fbe548d4826ea7770897d512e2017c993002a36ef5484a4ac71dbde2c565ffd
  BYTES: 14066
  LINES: 90
  FINAL_LF: true
  CONNECTOR_FETCHED: true
  HASHES_AND_COUNTS_RECOMPUTED: true
  ALL_CHECKS_MATCH: true
BOOTSTRAP:
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  REF: rh_clean
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
PHASE_KEY:
  PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
  ROUTE_ID: RouteB_TwoLevelSpectralLadder
  FRONT_ID: GOAL058_SECOND_EXPRESSION
  SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
  TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
  CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
  CHANGED: false
DECISIONS:
  D1_WITH_NONZERO_DENOMINATOR: valid_on_full_local_logarithmic_form_domain
  FULL_E_NOT_POLE_NULL_H: required_for_the_displayed_theta_test
  SHARP_CUTS_IN_FORM_DOMAIN: true
  ORDINARY_Q_DISTANCE_UNDER_RH: exactly_zero
  POSITIVE_DISTANCE_EQUIVALENT_TO_POSITIVE_WINDOW_FLOOR: false
  FIXED_WINDOW_NORMALIZED_FLOOR_MINUS_INFINITY: false
  UNNORMALIZED_INFIMUM_WITH_A_NEGATIVE_DIRECTION: minus_infinity
  THETA_TRANSFORM_IN_REQUEST: one_half_of_standard_centered_xi
  T_SQUARED_DOUBLE_EXPONENTIAL_COEFFICIENT: 4_pi_not_2_pi
  NORMALIZED_T_SQUARED_LAW: not_proved_or_refuted_for_the_actual_source
  SOURCE_UPPER_BOUND_PROVED_HERE: O_exp_4a_times_T
  EXPLICIT_OFFLINE_WINDOW: proved_with_source_defined_conditioning_constants
  OFFLINE_NORMALIZED_FLOOR: negative_exponential_upper_envelope_section_4
  ZHU_0_8_TWO_SIDED_BOUND: read_paper_not_certificate_rerun
CLOSES: [REQ-2026-09-09-DISTANCE]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
SELECTED_RATE_REMAINDER: normalized_source_Schur_cancellation_at_T_squared_scale
DISCRIMINATOR: fixed_L2_constraint_and_cached_correction_spectral_centroid
DERIVATIONS:
  SCOPES: [ABSTRACT, COFINAL_FAMILY]
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: PENDING
  LEAN_KERNEL_VERIFIED: false
EXECUTION:
  HASH_COMPUTATION: true
  NEW_EIGENSOLVE: false
  NUMERICAL_CERTIFICATION: false
  LEAN_EDIT: false
  LEAN_TOOLCHAIN_USED: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_STATE_EDIT: false
PUBLICATION:
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md
  COMMIT_SHA_AND_READBACK_HASH: delivery_receipt
  OLD_ARTIFACTS_OVERWRITTEN: false
  COMMIT_IS_NOT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision

**The affine identity survives. The positive-distance interpretation does not.** The denominator in D1 depends on the variable being minimized. Removing it changes the problem completely. Under RH, the ordinary distance of the tail to the window is exactly zero: the inside part completes it to the radical vector. This remains true when the window has a strictly positive normalized floor. [ABSTRACT][PAPER]

The corrected object is a **constrained Rayleigh minimum**, meaning a quadratic-form minimum with a fixed physical L2 norm. Its stationarity is an eigenvalue equation, not orthogonal projection of the tail. The observed T-squared scale remains a legitimate hypothesis about that minimum, but neither of its meaningful asymptotic bounds is proved here. An unconditional, weaker polynomial-times-T upper bound is proved below. [COFINAL_FAMILY][PAPER]

There is also a constructive result for the alternative sign. Given a specified off-line zero, Section 4 constructs compact smooth witnesses and an explicit distinguishing half-width, with all conditioning constants defined by theta integrals and a derivative of xi. It gives a negative exponential upper envelope for the normalized floor. It does not rely on the conjectured T-squared law. [COFINAL_FAMILY][PAPER]

The request was read in full and independently rehashed. Repository evidence below is fixed at the request commit, not substituted from a moving branch. The references [K], [H], [P], [J], [S26], [S23], and [Z] are resolved in the research log. New proofs are **paper derivations awaiting independent review**, not Lean results.

## 1. Q1: exact class, sharp cuts, and the radical

All statements and proofs in this section have tags [ABSTRACT][PAPER].

### 1.1 Preserve the full source and correct the theta normalization

Use antilinear-first inner products, U_t f(x)=f(x-t), and
\[
 A_0(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\frac\pi2,\quad
 w_m=\frac{\Lambda(m)}{\sqrt m}.
\]
The source is exactly [K, (K6)]:
\[
\begin{split}
 Q(f,g)={}&\mathcal D(f,g)-c_A\langle f,g\rangle
 -\sum_{m\ge2}w_m\{\langle f,U_{\log m}g\rangle+
                         \langle f,U_{-\log m}g\rangle\}\\
 &+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),\\
 \mathcal D(f,g)={}&\int_0^\infty A_0(t)
               \langle U_tf-f,U_tg-g\rangle\,dt,\qquad
 M_\pm(f)=\int f(x)e^{\pm x/2}\,dx.                 \tag{D2}
\end{split}
\]
Set
\[
 \mathscr E=\{f:\mathcal W[f]+\mathcal D[f]<\infty\},\quad
 \mathcal W[f]=\int e^{2|x|}|f(x)|^2dx,
 \quad \|f\|_E^2=\mathcal W[f]+\mathcal D[f].          \tag{D3}
\]
This is the full space, not the smaller pole-null subspace
\(\mathscr H=\ker M_+\cap\ker M_-\) used for [K]'s Riesz operator.

Write phi for the series with coefficients 2 pi-squared and 3 pi printed in this request. With the standard convention
\(\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\), direct Mellin integration gives
\[
 F_\phi(z)=\frac12\xi(1/2+z),\qquad
 \Theta:=2\phi,\qquad F_\Theta(z)=\xi(1/2+z).         \tag{D4}
\]
Indeed, put s=1/2+z and u=e^{2x}. In the initially absolutely convergent region Re s>1 the two terms give
\[
 \pi^{-s/2}\zeta(s)
 \{\Gamma(s/2+2)-\tfrac32\Gamma(s/2+1)\}
 =\tfrac14s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s).
\]
Evenness and double-exponential decay, obtained from theta's Poisson identity as in [K, (K18)], extend the equality everywhere. The factor two is immaterial for T and Rayleigh quotients, but must not be hidden in an exact transform identity. Also M_+(phi)=M_-(phi)=1/4, so phi is not in the pole-null H. We retain both pole terms throughout.

### 1.2 Continuity and the signed identity, without RH

The following estimates recheck the relevant part of [K, (K8)-(K16)]:
\[
 |\langle f,U_tg\rangle|\le e^{-|t|}\mathcal W[f]^{1/2}\mathcal W[g]^{1/2},
 \qquad |M_\pm(f)|\le\sqrt{4/3}\,\mathcal W[f]^{1/2}.
\]
Use \(|x|+|x-t|\ge|t|\) for the first and weighted Cauchy-Schwarz for the second. The elementary bounds c_A<7 and
\(\sum_{m\ge2}\log(m)m^{-3/2}<6\), together with Cauchy-Schwarz in D, yield
\[
 |Q(f,g)|\le22\|f\|_E\|g\|_E.                       \tag{D5}
\]
This is absolute continuity, not positivity.

Compact smooth functions form a core in E. Smooth truncation converges in W by dominated convergence. For D, expand a translated product and use the translation-difference integrand of f together with
\(|\chi_R(x+t)-\chi_R(x)|\le C\min(t/R,1)\).
The error is integrable against A_0 and tends to zero. Subsequent mollification converges in W and in the Fourier multiplier defining D. No pole correction is needed for the full E core.

Let Z be the distinct centered zeros, with multiplicity m_lambda, and j lambda=-conj(lambda). For f in E and g compact smooth, the polarized signed explicit formula is
\[
 Q(f,g)=\sum_{\lambda\in Z}m_\lambda
                 \overline{F_f(j\lambda)}F_g(\lambda). \tag{D6}
\]
This is [K, (K16)] with its actual class. Its extension in f follows from D5, bounded evaluation on the centered strip, rapid vertical decay of F_g, and the unconditional zero-count bound. In particular it does not turn off-line pairs into positive squares.

Every value F_phi(lambda) vanishes. Thus Q(phi,g)=0 first on the compact smooth core and then, by D5, for every g in E:
\[
                    Q(\phi,g)=0\quad(g\in E).         \tag{D7}
\]
The same argument applies to any n in E whose transform vanishes at every distinct centered zero. This is a radical statement, stronger than Q[n]=0. An arbitrary isotropic vector cannot replace n.

### 1.3 Why the discontinuous windows belong to the domain

Put v_i=phi 1_{(-a,a)} and v_o=phi-v_i. Both have finite W. Each has two jumps and otherwise square-integrable derivative. Integrating that piecewise derivative and the two jump measures gives, for 0<t<1,
\[
 \|U_tv-v\|_2^2\le C_vt+C'_vt^2.
\]
Since A_0(t)=O(1/t) at zero and is integrable at infinity, D[v] is finite. In particular **v_o is in E**; its decay is not by itself the proof of its small-scale energy regularity.

Approximate v_i by inward smooth tapers at both endpoints. Their difference e_epsilon has squared L2 norm O(epsilon), uniformly bounded total variation and uniformly bounded amplitude. Hence
\[
 \|U_te_\epsilon-e_\epsilon\|_2^2
       \le C\min(t,\epsilon),\qquad
 \|e_\epsilon\|_E^2=O(\epsilon(1+|\log\epsilon|))\to0. \tag{D8}
\]
This accounts for both endpoints and their shrinking junction regions. Therefore
\(v_i\in V_a:=\overline{C_c^\infty(-a,a)}^{\,E}\).
Values at exactly plus/minus a, including a midpoint convention, do not affect this a.e. form statement.

### 1.4 The whole radical family, not only the smooth examples

Here is a multiplier proof that removes a possible hidden restriction in Q1(c). Multiplication by an interval indicator is bounded on the logarithmic Fourier space
\[
 \|f\|_{\log}^2=\int(1+\log(2+|t|))|\widehat f(t)|^2dt.
\]
First prove the familiar fractional estimate directly, rather than requiring an unverified interpolation citation. For s=1/4, average
\(|f(x)|^2\le2|f(-y)|^2+2|f(x)-f(-y)|^2\)
over 16x<y<32x, x>0, and integrate with weight x^{-2s}. The coefficient of the negative-half-line weighted norm is
\[
 2\,16^{2s-1}\frac{2^{2s}-1}{2s}=\sqrt2-1<1.
\]
The difference term is bounded by a constant times the fractional H^s seminorm, since x+y is comparable with x on this integration region. Repeat with the half-lines reversed and absorb the displayed coefficient. This proves
\(\int |f(x)|^2|x|^{-2s}dx\le C_s\|f\|_{H^s}^2\).
The crossing term in the fractional seminorm of 1_{x>0}f is a constant times the same weighted integral. Thus half-line multiplication, and hence interval multiplication, is bounded on H^{1/4}.

Let P_j be the orthogonal dyadic Fourier projections, j>=0. The H^{1/4} bound and the L2 self-adjointness of interval multiplication M give
\[
 \|P_jMP_k\|_{2\to2}\le C2^{-|j-k|/4}.
\]
The logarithmic norm is equivalent to the square sum with weights 1+j. Multiplying this inequality by sqrt(1+j)/sqrt(1+k) costs at most sqrt(1+|j-k|). The resulting convolution kernel is summable, proving the claimed logarithmic bound by the elementary l2 convolution inequality.

The Fourier symbol of D is
\(\operatorname{Re}\psi(1/4+it/2)-\psi(1/4)\); its sum with 1 is comparable with the logarithmic weight. W decreases under cutting. Consequently M is bounded on E. Cut compact smooth approximations to an arbitrary f in E, and then use D8 on each approximation. This proves
\[
 V_a=\{f\in E:f=0\text{ a.e. outside }(-a,a)\}.        \tag{D9}
\]
All interval endpoints are included in this argument. In particular every n in the E-radical, including every specified g_k and its translates, admits the required decomposition n=n_i+n_o with n_i in V_a and n_o in E.

## 2. Q1 continued: the valid identity and the fatal distance reading

All statements in this section are [ABSTRACT][PAPER].

For f in V_a set w=v_i-f. D7 gives
\[
 Q[f]=Q[\phi-(v_o+w)]=Q[v_o+w].
\]
The map f -> w is an affine bijection of V_a. Therefore the exact repaired D1 is
\[
 \boxed{\lambda_a
 =\inf_{\substack{w\in V_a\\w\ne v_i}}
       \frac{Q[v_o+w]}{\|v_i-w\|_2^2}.}              \tag{D10}
\]
The exclusion w=v_i is essential: its quotient is 0/0. The same proof works with every n from Section 1.4, including n=0, replacing phi. These are representations of the **same** variational value, not distinct values whose best one improves lambda_a.

Now examine the different object requested in Q2:
\[
 d_a:=\inf_{w\in V_a}Q[v_o+w]=\inf_{f\in V_a}Q[f].
\]
Homogeneity proves the complete dichotomy
\[
 \boxed{d_a=0\text{ if }Q|_{V_a}\ge0;
 \qquad d_a=-\infty\text{ if }Q|_{V_a}\text{ has a negative direction}.} \tag{D11}
\]
**Under RH**, Q is nonnegative on E by D6 on the compact smooth core, followed by D5 and core density. The specific choice w=v_i gives v_o+w=phi and Q[phi]=0. Thus
\[
           \operatorname{dist}_Q(-v_o,V_a)^2=0.       \tag{D12}
\]
Excluding w=v_i does not repair the distance: choose w=v_i-epsilon f_0 and let epsilon tend to zero. In the quotient by the radical, [v_o]=-[v_i] is already in the window image. There is no positive separation to estimate.

Consequently the literal upper bound in Q2(a) holds, without RH, with C=0, because the candidate w=v_i is available. This is vacuous information about lambda_a. The proposed positive lower bound in Q2(b), **under RH**, is false for the actual source: at that same w its upper residual against c(a)T(a)^2||phi||^2 is strictly negative for every c(a)>0. T(a)>0 because phi is positive on the positive half-line.

The weakest useful normalization repair is, for any fixed M>0,
\[
 \boxed{\inf_{\substack{w\in V_a\\\|v_i-w\|_2^2=M}}
                   Q[v_o+w]=M\lambda_a.}           \tag{D13}
\]
For comparison with the proposed cut mass, take M=||v_i||^2=(1-T)||phi||^2. A factor 1-T may be harmless asymptotically, but a variable denominator is not.

### Finite windows never have normalized floor minus infinity

On V_a only m<=exp(2a) can contribute. Cauchy-Schwarz bounds the two pole terms below by -4 sinh(a)||f||^2. Since D is nonnegative,
\[
 \boxed{\lambda_a\ge-C_a> -\infty,\quad
 C_a=c_A+2\sum_{m\le e^{2a}}\frac{\Lambda(m)}{\sqrt m}+4\sinh a.} \tag{D14}
\]
Including an atom exactly at the endpoint merely enlarges this safe bound; its overlap is zero a.e. The local form is D plus an L2-bounded Hermitian perturbation. It is closed after the displayed shift. Its domain embeds compactly in local L2: the logarithmic Fourier weight controls high-frequency mass, while fixed support controls translations and escape. Hence the normalized minimum is attained and the associated self-adjoint operator has compact resolvent. This also recovers the domain required by [S26, Theorem 1.1, Corollary 1.2], rather than assuming it.

## 3. Q2: what remains of the T-squared proposal

### 3.1 The asymptotic exponent must be corrected

The following calculation is unconditional [COFINAL_FAMILY][PAPER]. Let I=||phi||^2. The n=1 term dominates the positive tail, including derivatives:
\[
 \phi(x)\sim2\pi^2e^{9x/2}e^{-\pi e^{2x}}.
\]
The relative errors from the second polynomial term and n>=2 tend to zero and are dominated on every sufficiently large tail. With y=e^{2x}, endpoint integration, equivalently one integration by parts in the incomplete gamma integral, gives
\[
 \begin{split}
 T(a)&\sim\frac{2\pi^3}{I}e^{7a}e^{-2\pi e^{2a}},\\
 T(a)^2&\sim\frac{4\pi^6}{I^2}e^{14a}e^{-4\pi e^{2a}}. \tag{D15}
 \end{split}
\]
Thus exp(-2 pi exp(2a)) is the exponential part of T, not T-squared. The request's a=1.19 extrapolation cannot follow from its T-squared assertion with that exponent. Polynomial prefactors must also be retained before using an asymptotic formula at a finite a.

### 3.2 An unconditional upper bound that can actually be proved

By D7 and D10,
\[
 \lambda_a\le\frac{Q[v_i]}{\|v_i\|^2}
 =\frac{Q[v_o]}{\|v_i\|^2}
 \le\frac{22\|v_o\|_E^2}{(1-T)I}.                  \tag{D16}
\]
For completeness, the energy on the right is controlled by the tail mass at polynomial cost. The distributional derivative of v_o is its smooth outside derivative plus its two endpoint jumps. Integration over a translation interval and Cauchy-Schwarz give
\[
 \|U_tv_o-v_o\|^2\le3t^2\|\phi'1_{|x|>a}\|^2
                              +6t|\phi(a)|^2\quad(0<t<1).
\]
Use A_0(t)<=2/t there, and A_0(t)<=2 exp(-t/2) for t>=1. The same endpoint calculation as D15 yields
\[
 \frac{|\phi(a)|^2}{IT}=O(e^{2a}),\quad
 \frac{\|\phi'1_{|x|>a}\|^2}{IT}=O(e^{4a}),\quad
 \frac{\mathcal W[v_o]}{IT}=O(e^{2a}).
\]
It follows that fixed constants C and a_1 exist such that
\[
 \boxed{\lambda_a\le C e^{4a}\frac{T(a)}{1-T(a)}
                          \quad(a\ge a_1).}         \tag{D17}
\]
No lower bound for Q or RH premise enters this proof. D17 is weaker than the requested normalized T-squared rate. It is retained, not mislabelled as that rate. [COFINAL_FAMILY][PAPER]

### 3.3 Why generic interpolation does not provide the missing factor

The proposed matching of the tail values is already exact:
\[
 F_{v_i}(\lambda)=-F_{v_o}(\lambda)\quad(\lambda\in Z).
\]
It is achieved by the forbidden zero-denominator choice in D10. The missing condition is a lower bound on ||v_i-w||, not mere existence of an interpolant.

Moreover, F_{v_o} is entire of **infinite exponential type**, not a finite-type Paley-Wiener function with a slightly larger bandwidth. Along the positive real axis, Stirling's formula and D4 give log F_phi(z)=(z/2)log z+O(z), whereas the compact part has growth at most exp(az) times a constant. Subtracting the compact part does not remove this growth. Arbitrary interpolation data at all zeta zeros are therefore not a supplied finite-type interpolation theorem in this setting.

The meaningful statement **under RH** is a quantitative lower sampling bound for nonzero type-a transforms with their physical L2 norm fixed. The qualitative finite-window positivity is available; the rate c exp(-pa)T(a)^2 is not established by the sources read here. [S23, Theorem 1.1] explicitly assumes RH and concerns Hilbert-space equivalence classes, not a ready-made pointwise window interpolation bound. It does not supply the claimed rate. [ABSTRACT][PAPER] [COFINAL_FAMILY][CONDITIONAL for the rate]

A sharp abstract falsifier shows why the radical alone cannot force this rate. For 0<T<1 let
\[
 n_T=(\sqrt{1-T},\sqrt T),\quad V=\mathbb C e_1,\quad
 Q_T[x]=|\sqrt T x_1-\sqrt{1-T}x_2|^2.              \tag{D18}
\]
Then n_T is radical, the relative outside mass is T, and Q_T[(n_T)_o]=T(1-T), but the normalized window floor is T, not O(T^2). Multiplying Q_T by T^3 gives a floor T^4 and disproves any universal T^2 lower rate inferred from this geometry alone. These are exact **abstract** controls, not substitute zeta forms or counterexamples to the actual source asymptotic. [ABSTRACT][PAPER]

### 3.4 The minimizer equation and the actual cancellation object

Let f_a attain the normalized minimum and put w_a=v_i-f_a, choosing whatever nonzero scale for f_a has been specified. Variation of the quotient gives
\[
 Q(h,f_a)=\lambda_a\langle h,f_a\rangle\quad(h\in V_a),
\]
thus
\[
 \boxed{Q(h,v_o+w_a)=-\lambda_a\langle h,v_i-w_a\rangle.} \tag{D19}
\]
This is not Q(h,v_o+w_a)=0. The latter equation selects an unconstrained projection; under RH w=v_i already solves it and leaves zero denominator. At a zero lambda,
\(F_{v_o+w_a}(\lambda)=-F_{f_a}(\lambda)\),
which is exact but does not determine those values without the ground state.

The percentage size of w_a also requires a scale convention. The scale minimizing ||v_i-c f_a|| is its L2 projection scale. A unit ground vector and an unnormalized v_i must not be subtracted before this alignment. [ABSTRACT][PAPER]

Here is a source weak equation for f_a, with f_a extended by zero. On (-a,a), in the sense of forms/distributions,
\[
\begin{split}
 A_af={}&\int_0^\infty A_0(t)(2f-U_tf-U_{-t}f)\,dt-c_Af\\
 &-\sum_{m\le e^{2a}}w_m(U_{\log m}f+U_{-\log m}f)
       +e^{x/2}M_-(f)+e^{-x/2}M_+(f),\\
                         A_af_a={}&\lambda_af_a.      \tag{D20}
\end{split}
\]
Pair D20 with a compact smooth h; changing variables in the translated terms gives exactly D2. D5 and local form closure then define the self-adjoint realization. No pointwise derivatives of a discontinuous endpoint representative are presumed.

The screw-kernel version has **two derivative factors**. In centered coordinates its continuous even primitive can be written
\[
 g(t)=-\sum_{\lambda\in Z}m_\lambda
                    \frac{e^{\lambda t}-1}{\lambda^2}.
\]
The series converges locally uniformly, using |Re lambda|<1/2 and the zero count. Its distributional second derivative and the signed explicit formula give -g''=K_Q, the convolution distribution of D2. The source expression for this same primitive is [S26, (1.3)]; its normalization is fixed by evenness and g(0)=0. Integrating twice against compact smooth h,f therefore proves
\[
 Q(h,f)=\iint g(x-y)\overline{h'(x)}f'(y)\,dx\,dy
       =\langle Dh,G_aDf\rangle,\quad D=i\partial_x. \tag{D21}
\]
The zero-mean projection in G_a is harmless here because derivatives of compact tests have integral zero. Closure yields the Friedrichs realization of D*G_aD. It does **not** yield Q[f]=<f,G_af>. This derives the form-to-operator dictionary at the common core; [S26, (1.5)-(1.8), Lemma 3.1] is the independently read cross-check. [ABSTRACT][PAPER]

A usable second representation is a **Schur response**, or energy-minimizing complement correction. Normalize p=v_i/||v_i|| and split V_a into Cp and its L2 orthogonal complement. Write r=Q[p], b(h)=Q(h,p), and C for the complement form. **If** C has a positive lower bound, its inverse is legitimate and
\[
 y=C^{-1}b,\quad s_0=r-b^*C^{-1}b,\quad
 Q[p-y]=s_0,\quad\|p-y\|^2=1+\|y\|^2.              \tag{D22}
\]
For an eigenvalue below the complement spectrum, the exact scalar equation is
\[
        r-\lambda-b^*(C-\lambda)^{-1}b=0.            \tag{D23}
\]
These follow by completing the quadratic form and solving the complement equation. The first-order energy cancellation to test is r against b*C^{-1}b. It is a **stationary Schur cancellation**, not orthogonal projection of a fixed tail with free norm. No all-a complement floor is assumed here. [ABSTRACT][PAPER, conditional on the displayed complement hypothesis]

The first unpaid inequality for this candidate upper-bound mechanism is explicitly
\[
 \frac{r-b^*C^{-1}b}{1+\|C^{-1}b\|^2}
                  \le C_0e^{pa}T(a)^2              \tag{D24}
\]
on a cofinal range where this C-inverse is independently justified. An arbitrary normalized trial achieving the same upper bound is a weaker acceptable interface; C-invertibility is not made mandatory. For a lower bound **under RH**, D24 must be replaced by an all-vector lower estimate, not the success of one trial. Neither estimate has been proved. [COFINAL_FAMILY][CONDITIONAL]

The request's HODGE H17 locator is not verified in the pinned artifact; the verified equality-case statement is Section 10.4. A positive-floor ground/tail correction is not a first-contact null pair. At lambda_a=0 it is a local isotropic vector; global radical membership is precisely the further equality-case question, and the pole-null Hodge class must also be matched. [ABSTRACT][PAPER]

### 3.5 What the fresh Zhu source really supplies

**READ [Z, v2, Theorem 1.2, Corollary 6.3, Section 8, Table 3]:** at a=0.8 it reports the unconditional enclosure
\(8.9\cdot10^{-18}\le\lambda_{0.8}\le2.27\cdot10^{-17}\), including the odd-sector extension needed for arbitrary complex tests. Its symbol (3) matches D2 on the even real class. Thus the factor approximately 2.55 is already a reported two-sided certificate, not dependent on this request's extrapolation. I did not rerun those certificates. **Under RH**, its Theorem 1.3 proves the weaker eventual upper bound exp(-a exp(a)); the stronger Landau-Widom law is Conjecture 12.1. Neither supplies a proved T-squared asymptotic. [FINITE_CELL][PAPER] [COFINAL_FAMILY][PAPER for the explicitly conditional theorem]

## 4. Q3: an explicit distinguishing window for an off-line pair

The following is a new paper derivation from D2-D6 and the separator construction of [K, (K19)-(K22)]. It is [COFINAL_FAMILY][PAPER], **conditional only on the specified off-line zero**. No RH premise is used. The constants expose the dependence on zero multiplicity and conditioning rather than claiming a uniform elementary formula in delta and gamma alone.

### 4.1 Exact pair isolation with source-defined constants

Let Lambda(z)=xi(1/2+z). Suppose lambda=delta+i gamma is a zero with delta>0; reflection permits this choice from any off-line zero. Let r be its multiplicity. The partner j lambda=-delta+i gamma has the same multiplicity.

For a smooth double-exponentially decreasing v with F_v(lambda)=0 define
\[
 J_\lambda v(x)=e^{-\lambda x}\int_{-\infty}^xe^{\lambda t}v(t)dt
              =-e^{-\lambda x}\int_x^\infty e^{\lambda t}v(t)dt.
\]
The equality uses that zero. The two integrals control the two tails. Differentiation and integration by parts give
\[
 (\partial_x+\lambda)J_\lambda v=v,\qquad
 F_{J_\lambda v}(z)=F_v(z)/(\lambda-z).
\]
Iterate r times on Theta. Each intermediate zero required for the next iteration remains. Put
\[
 d_\lambda=\frac{(-1)^r}{r!}\Lambda^{(r)}(\lambda),
 \quad q_\lambda=J_\lambda^r\Theta/d_\lambda,          \tag{D25}
\]
and define q_{j lambda} identically. Then F_q_lambda equals 1 at lambda and vanishes at every other distinct zero. Both functions and all derivatives retain double-exponential decay. The signed identity extends to them by smooth truncation with uniformly bounded weighted derivatives, giving a summable zero-side majorant. It follows that
\[
 Q[q_\lambda]=Q[q_{j\lambda}]=0,\qquad
                  Q(q_\lambda,q_{j\lambda})=r.      \tag{D26}
\]
No list of the other zeros is needed to define these functions.

For b>=0 set
\[
 u_b=e^{-ib\gamma}U_bq_\lambda-e^{ib\gamma}U_{-b}q_{j\lambda}.
\]
Its two nonzero sampled values are exp(b delta) and -exp(b delta). Thus
\[
 Q[u_b]=-2r e^{2\delta b},\qquad
 \|u_b\|_2^2\le D:=2(\|q_\lambda\|_2^2+\|q_{j\lambda}\|_2^2). \tag{D27}
\]
Define the explicit finite source constant
\[
 B=\int e^{4|x|}\bigl(|q_\lambda|^2+|q'_\lambda|^2
                    +|q_{j\lambda}|^2+|q'_{j\lambda}|^2\bigr)dx. \tag{D28}
\]
B and D are positive. They are given by theta integrals and the first nonzero derivative in D25. They may be very large. Suppressing them would conceal the quantitative separation problem.

### 4.2 Compactification, including its complete error budget

The elementary bounds for A_0 used earlier imply, for h in H1,
\[
 \mathcal D[h]\le\|h'\|_2^2+16\|h\|_2^2.           \tag{D29}
\]
Choose a smooth chi_a supported in (-a,a), equal to 1 on [-a+1,a-1], with 0<=chi_a<=1 and |chi'_a|<=2. Let s=a-1>=0. For
\(B(v)=\int e^{4|x|}(|v|^2+|v'|^2)dx\),
D29, the support of 1-chi_a, and the product derivative give
\[
 \|(1-\chi_a)v\|_E^2
 \le(e^{-2s}+24e^{-4s})B(v)\le25e^{-2s}B(v).         \tag{D30}
\]
This includes both transition strips, all outside tails, and the derivative of the cutoff. Translation gives
\[
 B(u_b)\le2e^{4b}B,\qquad\|u_b\|_E\le\sqrt{34B}\,e^b.
\]
Let f_a=chi_a u_b and e=||f_a-u_b||_E. Then e<=5 sqrt(2B) exp(-s+2b), and D5 yields
\[
\begin{split}
 |Q[f_a]-Q[u_b]|
 &\le22e(2\|u_b\|_E+e)\\
 &\le220\sqrt{68}\,B e^{-s+3b}+1100B e^{-2s+4b}.
\end{split}
\]
Take b=s/4. Since 220 sqrt(68)+1100<3000,
\[
                  |Q[f_a]-Q[u_b]|\le3000B e^{-s/4}. \tag{D31}
\]
Consequently an explicit distinguishing half-width is
\[
 \boxed{a_0(\lambda)=1+4\log\max\{1,3000B/r\}.}     \tag{D32}
\]
For every a>=a_0, f_a is a nonzero compact smooth test and
\[
 \boxed{Q[f_a]\le-r e^{\delta(a-1)/2}<0,\qquad
 \lambda_a\le-\frac rD e^{\delta(a-1)/2}.}           \tag{D33}
\]
The denominator estimate is legitimate because ||f_a||^2<=D and the numerator is negative. This is a strict upper-envelope witness. The proof covers arbitrary multiplicity and makes no simplicity assumption.

D32 is an explicit function of the specified root through the fixed source Lambda and D25-D28. A bound with no dependence on its derivative/multiplicity conditioning has not been established. This distinction is part of the answer, not hidden inside an unspecified constant. In D10 take w=v_i-f_a: the identical negative value appears in the requested tail coordinates.

The decisive comparison here is **zero** unwanted sampled mass for u_b versus its exponentially growing negative pair, followed by the explicit compactification error D31. There is no need to presume that the positive part of a different minimizer has size T-squared. The request's proposed comparison to that unproved scale is bypassed, not used.

### 4.3 Signed squares and the information still missing at the minimizer

For tests where the zero series converges absolutely, define x_lambda=F_u(lambda). Then
\[
\begin{split}
 Q[u]&=P_+[u]-N_-[u],\\
 P_+[u]&=\sum_{j\lambda=\lambda}m_\lambda|x_\lambda|^2
       +\frac12\sum_{\{\lambda,j\lambda\}}m_\lambda
                                  |x_\lambda+x_{j\lambda}|^2,\\
 N_-[u]&=\frac12\sum_{\{\lambda,j\lambda\}}m_\lambda
                                  |x_\lambda-x_{j\lambda}|^2. \tag{D34}
\end{split}
\]
Both displayed functionals are sums of nonnegative terms. For the rapid separators the identity is literal. For a general form-domain minimizer it must be understood through the smooth form-core limit unless convergence of the two separate sums is proved; D6 alone does not assert that convergence for every pair in E.

**Under RH**, N_- is absent. Without RH, it is exactly the unpaid signed contribution. At u=phi-f_a its pair contribution is
\[
 2m_\lambda\operatorname{Re}\left(
       \overline{F_{f_a}(j\lambda)}F_{f_a}(\lambda)\right). \tag{D35}
\]
For the constructed witness before cutoff it is -2r exp(2 delta b). For the actual minimizing f_a, delta, gamma and a do not determine its two transform values without solving the variational problem. No formula depending only on those three numbers is supplied by the current identities. Calling -N_- the single B_0 term is exact bookkeeping, not a nonnegative representation or a source proof of its required sign. [ABSTRACT][PAPER]

### 4.4 What remains of unconditional coercivity

The literal statement that windows carry no unconditional coercivity is false. D14 gives a finite lower bound on every fixed window. There are also strictly positive sufficiently small windows: if 2a<log 2, there are no prime overlaps and disjoint translates for t>2a give
\[
 Q[f]\ge\left(2\int_{2a}^{\infty}A_0(t)dt-c_A-4\sinh a\right)\|f\|^2. \tag{D36}
\]
The bracket tends to positive infinity as a decreases to zero. This proof needs neither a numerical certificate nor RH.

What is not supplied is an all-large-window lower bound
\(\lambda_a\ge-\epsilon(a)\) with epsilon(a)->0. Such a bound would make every fixed compact test nonnegative by inclusion into growing windows. Conditional on an off-line pair, D33 explicitly contradicts it. A T-squared **upper** bound cannot be turned into that **lower** bound. [COFINAL_FAMILY][PAPER]

## 5. Route map, strongest attacks, and dependency epistemics

The following exact refutations have scope **THEOREM_SHAPE**, not ROUTE_FAMILY. Their evidence is pinned by this verdict's committed bytes, together with the request/source pins in the header and research log. All are [ABSTRACT][PAPER].

| Rejected assertion | Exact evidence | Failure type / epistemic status |
|---|---|---|
| Positive window floor means positive ordinary tail distance | D11-D13; w=v_i reconstructs the actual radical vector | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for this implication |
| A positive T-squared lower bound holds for the unnormalized distance under RH | D12: its value is 0, and T>0 | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for the literal inequality |
| The Rayleigh minimizer is the unconstrained Q-projection of the tail | D19 versus the zero-denominator projection w=v_i | INCOMPATIBILITY / MATHEMATICALLY_DEAD for this identification |
| A negative direction makes the normalized fixed-window infimum minus infinity | D14 proves a finite lower bound for the actual source | INCOMPATIBILITY / MATHEMATICALLY_DEAD for this conclusion |
| Radical plus first-order tail energy forces a T-squared normalized law | D18 has floor T; its rescaling has floor T^4 | COUNTEREXAMPLE / MATHEMATICALLY_DEAD for the structure-only inference |

**Strongest surviving objection:** D22-D24 isolate a cancellation but do not pay it. The full source T-squared upper bound needs a nonzero normalized trial with that small energy; the lower bound under RH needs an all-vector quantitative sampling estimate. No change of coordinates replaces those inequalities. [COFINAL_FAMILY][CONDITIONAL]

| Representation | Preserves / drops | Decisive test; estimated kill-power / cost | Status |
|---|---|---|---|
| Selected: normalized Rayleigh/Schur response | Preserves Q, physical norm, support, complex class and every prime/pole term; no free rescaling | D24 on a source-defined response; 9/10 / 6/10 | Exact finite algebra; asymptotic supplier open |
| Alternative: normalized zero-sampling extremal problem | Same physical norm and type; Hilbert reading explicitly under RH | Quantitative smallest sampling singular value, not arbitrary interpolation; 9/10 / 8/10 | Lower-rate research debt |
| Alternative: source-space trial from a different radical element | Same Q and same window; changes only the candidate before minimization | A directly bounded normalized trial; 8/10 / 5/10 | Legal, but taking all w yields exactly the same lambda_a |

Scores are planning estimates, not probabilities or proof evidence. None authorizes an escalated eigensolve.

**K8A contract.** [ABSTRACT][PAPER for implications; COFINAL_FAMILY][CONDITIONAL for missing suppliers]

- **DOWNSTREAM_CONSUMER:** the unchanged published Weil criterion on all complex compact smooth tests.
- **ACTUAL_CONSUMER_REQUIREMENT:** Q[f]>=0 on that class; equivalently, nonnegative window floors. A cofinal lower envelope with error tending to zero also suffices by the fixed-test argument after D36.
- **ORIGINAL_REQUESTED_OBJECT:** a positive tail distance and a T-squared law.
- **ORIGINAL_OBJECT_IS:** NOT_NECESSARY. The positive ordinary distance is incompatible with the existing radical. A quantitative T-squared law is not required by the sign consumer.
- **KNOWN_WEAKER_INTERFACES:** any same-source all-window nonnegative lower envelope; or the existing source null-rigidity implication with its positive anchor. A normalized upper bound only limits a possible floor; it does not feed the positivity consumer.
- **FAILURE_TYPE:** COUNTEREXAMPLE for the exact distance/projection readings; NO_DERIVATION for the normalized source rate and the all-support sign.
- **EPISTEMIC_STATUS:** RESEARCH_DEBT for both surviving source problems. Only the precisely listed false theorem shapes are mathematically dead.
- **NOVELTY_AXIS:** sharp-cut closure, correct norm constraint, a source-faithful Schur remainder, and the quantitative off-line compactification D25-D33. No priority claim for Rayleigh minimization, fractional multipliers, Schur complements or Weil separation.
- **REOPEN_TRIGGER:** an independently bounded normalized trial at T-squared scale, an all-vector sampling lower bound under RH, or an unconditional source lower envelope. Merely matching the tail at the zeros or improving a scalar fit does not reopen the refuted distance reading.

## 6. Frozen predictions: score the event that was registered

All fates below concern this paper adjudication, not independent validation. [ABSTRACT][PAPER]

| Frozen prediction | Fate | Exact reason |
|---|---|---|
| P_IDENTITY_ON_CLOSURE, 0.85 | CONFIRMED WITH DOMAIN/QUOTIENT REPAIR | D7-D10 prove it on full E and its exact window closure, excluding 0/0. The distance interpretation is not included in this success. |
| P_FAMILY, 0.60 | CONFIRMED ON THE SPECIFIED E-RADICAL | D9-D10 apply to every cut radical element; in particular to the g_k. No density of their span is assumed. |
| P_UPPER_T2, 0.55 | NOT ESTABLISHED FOR THE MEANINGFUL EVENT | The literal numerator bound is vacuous. D17 is only polynomial-times-T. D24 is not a named classical lemma already proved elsewhere. |
| P_LOWER_T2_UNDER_RH, 0.30; alternative 0.55 | LITERAL EVENT REFUTED; NORMALIZED RATE UNRESOLVED | D12 kills the distance lower bound. Under RH there is qualitative positive finite-window coercivity, but no claimed T-squared lower rate. Do not score the two different questions as one successful alternative. |
| P_MECHANISM_NAMED, 0.60 | REFUTED AS THE REGISTERED PROJECTION CLAIM | D19-D23 supply a constrained eigenproblem/Schur response, not the alleged unconstrained projection. |
| P_OFFLINE_WINDOW, 0.50 | CONFIRMED WITH EXPLICIT CONDITIONING DISCLOSED | D25-D33 give a_0 and a rate from the specified root, multiplicity, xi derivative and theta integrals. No uniform derivative-free threshold is claimed. |
| P_COERCIVE_EMPTY, 0.70 | REFUTED AS STATED | D14 and D36 give unconditional local coercivity information. The narrower assertion that no vanishing all-window lower error has been supplied is preserved. |

No aggregate probability score is computed for these partly composite events. No definition of a prediction was changed after the proof checks. The final cache threshold is a prospective execution discriminator, not a blinded prediction: the request already supplied the component diagnostics.

## 7. Meta closeout

**Progress class:** REPRESENTATION_PROGRESS. **Cognitive operator:** REPRESENTATION_SHIFT. **Route score:** 4/5 as a proof/contract result, not proximity to RH. [ABSTRACT][PAPER]

What became smaller is the rate question: the denominator, domain and stationarity are now fixed, and the candidate missing cancellation is D24. What was killed is the positive ordinary-distance interpretation and its projection mechanism. What must not recur is removing the Rayleigh norm constraint, interpreting a fixed-window floor as minus infinity, or using exp(-2 pi exp(2a)) as the exponential part of T-squared.

The all-support signed lower bound remains the same open atom. The off-line alternative now has the explicit source-conditioned witness D33 instead of an unspecified eventual window. This is conditional separation, not an actual off-line zero or a positivity result.

Strategy memory: target=window-floor/T-squared mechanism; status=PROGRESS; failed_strategy=unconstrained radical distance; operator=REPRESENTATION_SHIFT; invariant=Q plus fixed physical norm on the same support; forbidden_future_move=drop denominator then infer a floor; next_test=cached correction spectral centroid. No new supplier is manufactured merely to justify another wrapper.

## 8. Verification and delivery boundary

The only repository write is the requested verdict path. The commit subject begins `[Proshka]`. Its commit SHA, blob and SHA-256 are returned with delivery and checked by immutable readback; they are not inserted into their own hashed contents.

**WORKDIR: repository root**
```bash
git log -1 --format='%H %s' -- docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md
git hash-object docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md
shasum -a 256 docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_DISTANCE_2026-09-09.md
```
The commands use literal paths; no variable substitution is needed. No Lean file or axiom profile was generated, and no lake/Mathlib gate was run. Text readback validates delivery only. An independent paper check must particularly verify the sharp-cut multiplier proof and constants in D29-D33. A successful check does not prove D24 or promote Route B.

## 9. Proshka's own line

I keep the window Rayleigh problem because it is the quantity the certificate must actually bound.
The ordinary-distance alternative loses that quantity before any difficult analysis begins.
The zero-interpolation alternative is useful only after the nonzero norm constraint is restored.
Exact interpolation without that constraint already has the trivial radical completion as a solution.
The denominator is therefore not a technical nuisance; it is the entire distinction between the two questions.
The domain issue is real but repairable because logarithmic energy permits jumps.
It would have been wrong to impose a Sobolev boundary condition stronger than this form needs.
The two-sided endpoint proof lets the whole radical family remain available.
It does not make one family representation a different spectral minimum.
One move beyond this batch is to study the energy-weighted correction rather than its small L2 size.
A correction can be small in mass and still occupy directions far above the lowest cluster.
The cached centroid test can distinguish those situations without a new matrix build.
That move dies as an explanation if its proposed response does not retain the source mixed terms.
The other move is a normalized trial built from another member of the radical family.
That move dies if its normalization collapses at the same scale as its form value.
I would ask for saved coefficient vectors and matrix error budgets, not another rounded overlap percentage.
The current JSON is sufficient for a centroid but not for reconstructing a Schur solve.
I would especially want the signed cancellation evaluated independently of the low eigenvalue routine.
The useful surprise is that a specified off-line pair can be separated before compactification.
That avoids an unproved comparison with the observed positive T-squared scale.
The explicit threshold still pays for the derivative conditioning of the chosen zero.
I distrust any formula that hides that conditioning in a universal constant.
The small-window data remain interesting after the distance reading is removed.
They suggest a normalized variational cancellation, not a positive distance from the radical to itself.

## 10. Research log

### 10.1 Sources actually consulted

Repository reads use `Malaeu/chen_q3@19054597ea92cd6d696f087a4676345ef067813f` unless stated otherwise. Old paper derivations were rechecked only to the extent explicitly used above, not imported as axioms.

| Reading | Locator | Taken or rejected |
|---|---|---|
| READ, REHASHED [REQ] | Request path and hashes in the header | Entire controlling payload, frozen predictions and exact write boundary. |
| READ protocol | `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, live rh_clean, blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4` | Adjudication, scope, evidence and publication protocol. |
| READ batch rules | `docs/BATCH_PATTERNS.md`, blob `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | Specifically required non-mirror file; proof-attempt and research-log requirements. |
| READ [K] | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_KERNEL_2026-09-08.md`, blob `d171a2fb7b6b917a1780656952b1db5458cc9a34`; K6-K26 | Full source/E versus H, continuity, signed identity and separator formulas. |
| READ [H] | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_HODGE_2026-09-08.md`, blob `4e68922d186cf95f41a2b4db25fe068f9c2b02ed`; Sections 2-4, 10.4 | Primitive class and isotropic/radical distinction; no verified H17 equation in this artifact. |
| READ [P] | `docs/routeB_bus/WINDOW_TAIL_DERIVATIVE_PROBE_2026-09-09.md`, blob `11cf942aa06edc451eb10d7003774d6c8773133f` | Diagnostic hypotheses, denominator error, finite-precision limits and exponent claim. |
| READ [J], relevant rows | `docs/routeB_bus/phase5_codex/six_centre/out/window_derivative_K36.json`, blob `021d8e401d81dec35070bccf0b526d6750a325ed` | Exact cache column names and a<=0.70 rows; not a new eigensolve or certificate. |
| READ script | `docs/routeB_bus/phase5_codex/six_centre/window_derivative.py`, blob `d5969fefcf94bd58ad57447b1465f7a357eaf4ac` | The cache stores scalar eigenvalues, Rayleigh value and overlap, not matrices/eigenvectors. |
| READ assembly, lines 1-100 | `docs/routeB_bus/phase5_codex/six_centre/sc_build.py`, blob `bd9ac8062f111b6dda2820d29e1621434d50b05b` | Full source convention; costly Fourier build and single-centre tail correction. Not rerun. |
| READ [S26] | `https://arxiv.org/pdf/2606.09096v1`; (1.3)-(1.8), Theorem 1.1, Corollary 1.2, Theorems 1.3-1.4, Lemma 3.1, Proposition 4.1 | Derivative/screw dictionary and local domain; no all-window unshifted positivity imported. Formula page visually checked. |
| READ [S23] | `https://arxiv.org/pdf/2301.00421v3`; (1.1)-(1.4), Theorem 1.1, pp. 1-2 | RH premise and equivalence-class nature of the Hilbert/de Branges identification; no T-squared sampling theorem. Theorem page visually checked. |
| READ [Z] | `https://arxiv.org/html/2608.24827v2` and versioned PDF; Theorems 1.2-1.3, Proposition 2.3, Corollary 6.3, Section 8, Table 3, Conjecture 12.1 | Finite reported enclosure versus conditional theorem versus fitted law. Table/theorem pages visually checked; certificates not rerun. |
| ACQUIRED, no imported theorem | Suzuki `2206.03682`, PDF | Broader screw background; no additional theorem from it is used. |
| DISCOVERY ONLY | Primary-source search results for Beurling-Malliavin/Landau density and Hunt-Muckenhoupt-Wheeden weighted Hilbert transforms | No exact rate supplier extracted; no theorem credited on the strength of a snippet. Full HMW acquisition failed; the needed multiplier estimate is proved in Section 1.4 instead. |
| RELAY ONLY | SCREW/SIGNATURE/CLOSURE, ALIGN, COMPENSATE, ground-state probe, identity JSON, obstruction-space file and Suzuki usage cards as summarized in REQ/K/H/P | No independent certificate or additional source theorem imported. Their forbidden-return boundaries are preserved. |

Search was used for acquisition, not as a theorem verifier. The queue, state files, unrelated uploaded conversations and personal archive contents were not used to select or replace this task.

### 10.2 Rejected branches and reusable residues

| Candidate | First failed fact or inequality | Reusable result |
|---|---|---|
| Positive ordinary distance of a radical tail | w=v_i makes Q[v_o+w]=0 | D10 and the fixed-norm repair D13. |
| Ignore discontinuous endpoints | Decay says nothing about the t->0 Dirichlet integral | D8-D9 prove the legal closure without imposing H1 traces. |
| Exact matching at the zeros supplies a small nonzero window vector | Matching is already solved by the zero-denominator candidate | The residual must be optimized on a fixed physical sphere. |
| Bare Paley-Wiener interpolation of the tail | F_v_o has infinite exponential type; arbitrary matching lacks normalization control | A quantitative sampling singular-value problem remains well typed under RH. |
| Unconstrained orthogonal projection identifies the ground | It omits the lambda-dependent right-hand side in D19 | The correct Schur response is D22-D23. |
| Radical geometry proves the exponent two | D18 gives floor T with the same null/tail geometry | The source arithmetic must pay D24. |
| One finite window has normalized floor minus infinity | D14 is an explicit finite lower bound | Distinguish finite lambda_a from the homogeneous numerator infimum and its limit. |
| Off-line negativity must beat an assumed on-line T-squared term | That assumed term is not established for the relevant witness | D25-D33 isolate the pair first and pay only the compactification error. |
| Upper tail law supplies an almost-nonnegative lower floor | Inequality direction is reversed | D36 and the fixed-test inclusion argument state the required lower interface. |

The useful intermediate identities are D8, D13, D15, D19, D21-D23 and D30-D33. The numerator-distance calculation did not fail numerically; it failed exactly by homogeneity. No new eigenvalue computation was performed in this batch.

## next_decisive_test

**One cache-only computation: the spectral centroid of the removed correction.** [FINITE_CELL][CONDITIONAL as a prospective diagnostic, never a proof]

Read only [J]'s K=36 rows with a<=0.70. Write c for `overlap_ground_cutPhi`, R for `rayleigh_cutPhi`, and l1,l2 for `lam1`,`lam2`. Compute
\[
 E=1-c^2,\qquad
 \mu_\perp=\frac{R-l_1c^2}{E},\qquad
 H=\frac{\mu_\perp}{l_2}.                           \tag{D37}
\]
For an exact generalized Hermitian eigensystem, mu_perp is the Rayleigh value of the normalized component of the cut-theta trial orthogonal to the ground. This follows by writing the unit trial as c times the ground plus its orthogonal component. Thus the test distinguishes correction energy in the near-bottom cluster from correction energy much higher in the spectrum. It uses the physical Gram overlap already stored by the script.

**Registered execution threshold:** E>1e-8, l2>0, and H>=100 in each of the a=0.60,0.65,0.70 rows. Also report every a<=0.70 row and the exact input blob. This threshold is not presented as a blinded forecast: its constituent diagnostics were available in the request. Reject malformed rows; do not repair signs or take absolute values. No new matrix build, no precision escalation, no extrapolation and no RH inference.

**ЕСЛИ_A:** if the threshold passes, classify the correction as high-energy relative to the first excited mode and make the source-directional Schur response D22-D24 the next proof target; do not replace it by the lowest-gap operator norm.

**ЕСЛИ_B:** if a row is invalid or the threshold fails, stop that proposed high-energy explanation, preserve the raw row, and require the saved coefficient spectral decomposition before choosing a low-cluster response. Do not rebuild the three-block identity experiment or declare the T-squared law refuted from this diagnostic.
