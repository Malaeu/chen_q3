# STATUS: KILL_COUPLED_FINITE_STENCIL_CSS
```yaml
OPERATIVE_CLASS: KILL_COUPLED_FINITE_STENCIL_CSS
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-05-COUPLED
BOUNDARY_ID: GOAL058_COUPLED_SIGNED_SQUARE_CERTIFICATE_FOR_THE_CANONICAL_KERNEL
RESULT: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
REQUEST_LOCK:
  COMMIT: 7f141f59db0a94b4b6208ae108f6b0b53eba38e5
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_COUPLED_SIGNED_SQUARES_FOR_CANONICAL_KERNEL_2026-09-05.txt
  GIT_BLOB: 9b7cdf9e09482bb35c2f3c67fad106d533572510
  SHA256: 2882115e67f5abcb24f4ee18bd5a00d3fd9f78af1d7de3b688e452deb33aa617
  BYTES: 9827
  LINES: 91
  FINAL_LF: true
  SHA256_AND_GIT_BLOB_RECOMPUTED: true
SOURCE_BASE_REF: e4a3bad2
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_COUPLED_SIGNED_SQUARE_CERTIFICATE_FOR_THE_CANONICAL_KERNEL_2026-09-05.md
ADMISSION:
  DELIVERY: OWNER_EXACT_GITHUB_REQUEST_LOCATOR
  AUTOMATED_REVIEW_PLAN_EXECUTION_VERIFIED: false
  REQUEST_OR_QUEUE_REBOUND: false
CLOSES: []
OPENS: []
CANONICAL_RH_SUPPLIER_COUNT_DELTA: 0
CLOSED_REVIEW_OBLIGATIONS:
  - C1_EXACT_SPLITTING_COST_AND_FAILED_SOURCE_CAPACITY
  - C2_RECTANGLE_IDENTITY_AND_DIV_TRANSPORT_MISMATCH
  - C3_NO_NONTRIVIAL_POSITIVE_FINITE_STENCIL_MINORANT
  - C4_COMPACT_COUNTEREXAMPLE_WITH_STRICT_NEGATIVE_CERTIFICATE_MARGIN
KILL_SCOPE: THEOREM_SHAPE
FAILURE_TYPE: INCOMPATIBILITY
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_BOUND_ON_CERTIFICATE_IDENTITY_MARGIN
KILL_EVIDENCE: THIS_DOCUMENT_C3_EQUATION_CERTIFICATE_KILL
KILLED_CLASS:
  exact_CSS_on_all_compact_smooth_tests: true
  fixed_finite_or_countable_family_of_finite_point_stencils: true
  arbitrary_nonnegative_measurable_weights: true
  uniform_stencil_diameter_bound_required: false
  positive_measure_integrals_of_finite_stencils: also_excluded_under_C3_measurability_conditions
NOT_KILLED:
  - actual_Weil_positivity_DOM_FM_ZG
  - nonlocal_infinite_spatial_support_factorizations
  - cutoff_dependent_finite_certificates_with_proved_recovery_and_vanishing_error
  - arbitrary_positive_semidefinite_finite_matrices
SOURCE_REPAIRS:
  zero_side_modulation_sum_is_unconditionally_a_sum_of_real_squares: false
  finite_graph_SOS_equivalence_implies_continuum_finite_stencil_CSS: false
  DIV_transports_to_zero_mean_canonical_stencils_without_new_terms: false
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INDEPENDENT_REVIEW: PENDING
NOVELTY_IN_LITERATURE: NOT_CLAIMED
LEAN_EDIT_PERFORMED: false
LEAN_KERNEL_RUN: false
NUMERICAL_EXPERIMENT_RUN: false
ARISTOTLE_SUBMISSION: false
OLD_VERDICT_OR_SHARED_STATE_CHANGED: false
PHASE_KEY_CHANGED: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## Decision and pinned basis

**The literal CSS class in the request is empty for this nonzero form.** The obstruction is not the negative edge measure by itself. Every translate of the canonical test is a radical vector. Compact truncations approximate those translates in the form-control norm. A nonnegative square decomposition would force every individual finite stencil to annihilate every translated canonical ratio. Finite translates of a nonzero integrable function are linearly independent, so every such stencil must be zero wherever its weight is positive.

Section C3 proves this statement and gives a compact test with a strictly negative upper bound for the proposed certificate's **identity margin**. It does not give a negative Weil test. It also shows why the finite-graph analogy does not extend to this global finite-stencil representation.

**Sources.** [R] is the byte-exact request above. [D] is the DOMFM verdict at `e4a3bad2`, blob `d1a8c9091bfabd14730b72065058355e803afa7b`; its local bytes match SHA-256 `8a5d326180c9663353ffb619ca5e4fecf87502a7c0662887b4e407a470462d8c`. [X] is the XIDEV verdict at the same ref, blob `136aceb3cbbabcdfa425459562b803b67c548b48`; its local bytes match SHA-256 `93db2de6357821918211a8033b2c8f34e7f684320a25e5623e1f24d33ed58fe9`. The analytic inputs used below are [X, domain lemma, L1-L3] and [D, D1.3, D2.1-D2.3], reread as PAPER proofs, not promoted to Lean.

[L] is `q3.lean.aristotle/Q3/Proofs/RouteB/DomfmFiniteObstructions.lean` at `e4a3bad2`, blob `8e2b22601ad9931da1d671be6d904d001933f54c`. Its inspected source explicitly covers finite algebra only. The request reports a green kernel gate; this adjudicator did not rerun it. No analytic conclusion is imported from its compilation.

[CCM] is Connes-Consani-Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755v1: Lemma 2.2, (3.1)-(3.11), (7.1)-(7.4). [CC] is Connes-Consani, *Spectral Triples and Zeta-Cycles*, arXiv:2106.01715v1: (1.1)-(1.4), Section 2.1.1 and Section 3. Their primary HTML texts were checked. These provide the explicit formula, its test class and the radical mechanism, not global positivity. The new obstruction and splitting calculations below are derivations in this document. No observer decimal, zero list, or `Progress_Log.md` entry is a premise; that log was not needed or opened.

The fetched request was materialized as UTF-8 and both hashes, bytes, lines and final LF were recomputed. File hashing is not a mathematical numerical experiment.

## Objects and inherited analytic facts

All tests are complex. Use angular Fourier transform
\[
 \widehat g(z)=\int_{\mathbb R}g(x)e^{-izx}dx,
 \qquad (U_qg)(x)=g(x-q).
\]
Write \(f=f_0>0\), \(\|f\|_2=1\), with the exact source normalization
\[
 h(u)=(\pi^2u^4-3\pi u^2/2)e^{-\pi u^2},\quad
 \Phi(x)=4e^{x/2}\sum_{n\ge1}h(ne^x),\quad
 A=\|\Phi\|_2,\quad f=\Phi/A.
\]
Thus \(\widehat f=\Xi/A\). Put
\[
 a(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 k(t)=\frac{e^{-5t/2}}{1-e^{-2t}},\quad b(t)=k(t)-e^{t/2},\quad
 w_n=\Lambda(n)/\sqrt n,\quad c_A=\gamma+\log(8\pi)+\pi/2.
\]
Here \(\Lambda\) is the von Mangoldt function. Set \(b_+=\max(b,0)\), \(B_-=\max(-b,0)\), and \(t_0=\log\rho\), where \(\rho>1\) is the unique root of \(\rho^3-\rho=1\). No rounded value of this root is used.

For \(H(g)=\|g\|_2^2\), \(C_g(t)=\Re\int\overline{g(x)}g(x+t)dx\), and \(A_\pm(g)=\int g(x)e^{\pm x/2}dx\), the full source form is
\[
 Q(g)=\mathcal D(g)-c_AH(g)+2\Re(A_+(g)\overline{A_-(g)})
                -2\sum_{n\ge2}w_nC_g(\log n),
 \quad \mathcal D(g)=\int_0^\infty a(t)\|g(\cdot+t)-g\|_2^2dt.       \tag{Q}
\]
The control space and pairing are
\[
 \|g\|_X^2=\|e^{|x|}g\|_2^2+\mathcal D(g),\qquad
 |\mathcal B(g,v)|\le C_X\|g\|_X\|v\|_X,\quad C_X=|c_A|+14.        \tag{X}
\]
Here \(\mathcal B\) is the Hermitian polarization of Q, antilinear first. The relevant inherited PAPER facts are
\[
 \mathcal B(f,v)=0\ (v\in X),\qquad
 |f^{(j)}(x)|\le A_j e^{-a_*e^{2|x|}},\quad a_*=\pi/2,\quad j=0,1. \tag{RAD-ENV}
\]
The constants \(A_j\) are explicit in [X, ENV]: if \(p_0(z)=4z^2-6z\), \(p_{j+1}=p_j/2+2z(p_j'-p_j)=\sum_r p_{jr}z^r\), then
\[
 A_j=\frac{\pi^{-1/4}}{A(1-e^{-3\pi/2})}
       \sum_r|p_{jr}|\bigl(2(r+1/4)/e\bigr)^{r+1/4}.
\]
These facts follow from Gaussian/Poisson identities and the explicit formula: each canonical zero-side summand contains \(\Xi(z)=0\). They do not assume that a zero is real. The control bound follows from Cauchy-Schwarz on translation energy, \(|C_{g,v}(t)|\le e^{-|t|}\|e^{|x|}g\|_2\|e^{|x|}v\|_2\), and the convergent majorant \(\sum\log n/n^{3/2}\). The source scale 4 is retained.

For compact smooth s define
\[
 E_s(t)=\int f(x)f(x+t)|s(x+t)-s(x)|^2dx,\quad
 D(s)=Q(fs)=\int_0^\infty b(t)E_s(t)dt+\sum_{n\ge2}w_nE_s(\log n). \tag{GS}
\]
This is [X, GS], obtained by subtracting \(\Re\mathcal B(f,f|s|^2)=0\) from Q(fs). All terms converge: differences are O(t) at zero, and the canonical factors control the large-distance tails. Measures at prime distances are Dirac measures, not values of a density. Every compact smooth g is fs for the compact smooth ratio s=g/f.

**Scope/verifier for this paragraph:** [ABSTRACT][PAPER]. The global sign of D is not among the inherited facts.

## C1. Exact splitting: the cost is not a free logarithm

### Lemma C1.1 — path identity [ABSTRACT][PAPER]

For N complex increments \(z_0,\ldots,z_{N-1}\),
\[
 N\sum_i|z_i|^2-\left|\sum_i z_i\right|^2
                 =\sum_{i<j}|z_i-z_j|^2.                      \tag{PATH}
\]
**Proof.** Expand both sides. Each diagonal coefficient on the right is N-1 and each mixed coefficient is minus twice its real pairing. The same coefficients occur on the left. This proves the identity, including N=1.

Take \(z_i=s(x+(i+1)h)-s(x+ih)\), \(t=Nh\). Then
\[
 |s(x+t)-s(x)|^2=N\sum_{i=0}^{N-1}|\Delta_hs(x+ih)|^2
                      -\sum_{i<j}|\Delta_hs(x+ih)-\Delta_hs(x+jh)|^2. \tag{PATH-S}
\]
For N=2 the subtracted term is the square of the second difference. After q equal binary subdivisions, N=\(2^q\): the coefficient of each of the N edge squares is N, not q. On affine data the cost is exactly \(N^2h^2=t^2\); there is no gain.

**Lean-ready head:** `coupled_path_energy_identity (N : ℕ) (z : Fin N → ℂ)` with conclusion (PATH), followed by `coupled_path_difference_identity` substituting these increments. These are finite algebraic specifications, not newly compiled declarations.

### Lemma C1.2 — exact source capacity and a strict failure [ABSTRACT][PAPER]

Let \(I=[u,v]=[\log(7/5),\log(8/5)]\). It lies in \((t_0,2t_0)\): \(13/10<\rho<7/5\) and \((13/10)^2>8/5\). On I, \(B_-(t)\ge b_*:=43/168\), by the exact calculation in [X, NEG-MEASURE]. Fix an integer N≥2 and set h=t/N.

Multiply (PATH-S) by \(B_-(t)f(x)f(x+t)\) and integrate in x and t over I. The positive edge cost, after \(z=x+ih\) and \(dt=Ndh\), is
\[
 \int_{I/N}\int A_N(z,h)|\Delta_hs(z)|^2dzdh,\quad
 A_N(z,h)=N^2B_-(Nh)\sum_{i=0}^{N-1}f(z-ih)f(z+(N-i)h).          \tag{CAP}
\]
The subtracted coupled-square term retains the weight \(B_-(t)f(x)f(x+t)\) in the original (x,t) variables. Thus this is an exact identity, not a loss of its negative sign.

To absorb this cost using the original short edges would require
\[
                  A_N(z,h)\le b_+(h)f(z)f(z+h).                 \tag{CAP-REQ}
\]
This fails for sufficiently fine equal subdivisions, quantitatively. Define the positive finite source constants
\[
 m_f=\min_{[-1-v,1+v]}f>0,\qquad M_f=\max_{[-1-v,1+v]}f.
\]
For \(|z|\le1\), \(h\in I/N\), all arguments in (CAP) are in that compact interval. Also \(b_+(h)\le a(h)\le4/(3h)\) for h≤1. Therefore
\[
 A_N(z,h)\ge N^3b_*m_f^2,\qquad
 b_+(h)f(z)f(z+h)\le\frac{4N}{3u}M_f^2.
\]
In particular
\[
 \boxed{b_+(h)f(z)f(z+h)-A_N(z,h)
       \le-\tfrac12N^3b_*m_f^2<0}
 \quad\text{if}\quad N^2\ge\frac{8M_f^2}{3u b_*m_f^2}.         \tag{CAP-KILL}
\]
The N³ includes the path coefficient, the N edges, and the change-of-variable Jacobian. The available density grows only as N. Refinement worsens this capacity ratio quadratically.

For the full dyadic splitting of all negative lengths, choose N=\(2^q\), q≥1, on \([Nt_0/2,Nt_0)\). The required density on \(t_0/2\le h<t_0\) is the sum of (CAP) over these N. Already its N=2 term defeats (CAP-REQ) near \(h=t_0\), z=0: the available density tends to zero, while that term tends to
\[
 4B_-(2t_0)\{f(0)f(2t_0)+f(t_0)^2\}>0.
\]
Continuity gives an open rectangle of strict negative capacity margin. The identities and the series converge for compact smooth s: N is O(t), while \(\int f(x)f(x+t)dx\) decays super-exponentially. These failures exclude these capacity allocations; the stronger class-wide exclusion is proved in C3.

**Lean-ready heads:** `coupled_equal_path_cost_density`, with the exact substitutions in (CAP), and `coupled_equal_path_capacity_negative`, with positive extrema witnesses and (CAP-KILL). The minima can be replaced in Lean by explicit lower/upper witnesses on the stated compact interval.

### Lemma C1.3 — the ultraviolet budget vanishes [ABSTRACT][PAPER]

For every compact smooth s,
\[
 \lim_{t\downarrow0}\frac{E_s(t)}{t^2}=\int f(x)^2|s'(x)|^2dx=:I_s,
 \qquad
 \int_0^\delta b_+(t)E_s(t)dt=\frac{I_s}{4}\delta^2+o(\delta^2). \tag{UV}
\]
**Proof.** The difference quotient tends pointwise to s'. For t≤1 its support is in a common compact set and its modulus is at most \(\|s'\|_\infty\). Dominated convergence proves the first limit. Since \(tb(t)\to1/2\), the integrand is \((I_s/2)t+o(t)\); integration proves the second. Thus the logarithmically divergent degree is not a logarithmically divergent usable difference energy.

**Lean-ready head:** `coupled_short_jump_energy_asymptotic`, with compact smooth s and both limits in (UV). No numerical value of the negative mass is used.

## C2. Multiplicative rectangles: exact algebra, nonexact source transport

### Lemma C2.1 — all six rectangle edges [ABSTRACT][PAPER]

For complex A,B,C,D,
\[
 |A-B-C+D|^2=|A-B|^2+|A-C|^2+|B-D|^2+|C-D|^2
                                      -|A-D|^2-|B-C|^2.       \tag{RECT}
\]
**Proof.** Expansion gives diagonal coefficient 1 at every vertex, negative mixed coefficients on the four sides and positive mixed coefficients on the two diagonals, on both sides of the identity.

For a=log m, c=log n, take the values of s at x, x+a, x+c, x+a+c. The positive sides have lengths a,c, each twice. The negative diagonals have lengths a+c and |c-a|. Multiplication by any nonnegative W(x) preserves (RECT). However **one and the same W(x)** occurs on all six pairs. For example the canonical pair weights on the four sides would be
\[
 f(x)f(x+a),\quad f(x)f(x+c),\quad
 f(x+a)f(x+a+c),\quad f(x+c)f(x+a+c),
\]
which are not interchangeable. A construction must allocate W against each of them separately.

Furthermore a fixed pair (m,n) produces **Dirac edge masses** at both diagonal lengths. The edge at log(n/m) is not a piece of the continuous density b. If m,n are powers of different primes, log(mn) has no von Mangoldt atom at all. Introducing and then canceling artificial atoms requires an exact additional identity; their locations in the negative continuous region do not license treating them as continuous mass. For m=n the coincident middle vertices reduce (RECT) to the three-vertex identity.

**Lean-ready head:** `coupled_rectangle_energy_identity (A B C D : ℂ)`, conclusion (RECT); `coupled_weighted_rectangle_identity` multiplies by a nonnegative real weight before integrating. No arithmetic or positivity assumption is required for the algebraic identity.

### Lemma C2.2 — what DIV actually transports to [ABSTRACT][PAPER]

Let \(g=fs\), with s compact smooth, and fix M≥2. Apply the finite divisibility identity pointwise to
\(c_n(x)=g(x+\log n)\), 1≤n≤M, and integrate. Translation of x gives exactly
\[
 \begin{split}
 &A_M\|g\|_2^2
   -2\sum_{d=2}^M\lfloor M/d\rfloor\frac{\Lambda(d)}{\sqrt d}C_g(\log d)\\
 &=\sum_{d=2}^M\lfloor M/d\rfloor\Lambda(d)
            \int\left|g(x+\log d)-\frac{g(x)}{\sqrt d}\right|^2dx,\qquad
 A_M=\sum_{d=2}^M\lfloor M/d\rfloor\Lambda(d)(1+1/d).            \tag{DIV-CONT}
 \end{split}
\]
**Proof.** Expand the square on the right. Both translated and unshifted norm integrals equal \(\|g\|_2^2\), and the mixed integral is \(C_g(\log d)\). There are exactly \(\lfloor M/d\rfloor\) indices n with nd≤M. Equivalently, the divisor identity \(\sum_{d\mid n}\Lambda(d)=\log n\) collects the finite diagonal before integration. This proves every coefficient in (DIV-CONT).

This is not the atom part of (CSS). Its weights have the extra floor, its diagonal is A_M, and in ratio variables its stencil is
\(f(x+\log d)s(x+\log d)-f(x)s(x)/\sqrt d\), not a zero-mean stencil in s. Its exact comparison with a zero-mean edge, writing p=f(x), q=f(x+log d), is
\[
 |qz-pu/\sqrt d|^2
 =\frac{pq}{\sqrt d}|z-u|^2
  +q(q-p/\sqrt d)|z|^2
  +\frac p{\sqrt d}(p/\sqrt d-q)|u|^2.                         \tag{DIV-POT}
\]
Expansion proves this identity. The last two diagonal terms have not disappeared and have no asserted sign.

There is a decisive constant-ratio control. For M=2 and s=1 the right-hand side of (DIV-CONT) satisfies
\[
 \Lambda(2)\|f(\cdot+\log2)-f/\sqrt2\|_2^2
       \ge\log2\,(1-1/\sqrt2)^2>0,                            \tag{DIV-PLANT}
\]
by the reverse triangle inequality and \(\|f\|_2=1\). But D(1)=Q(f)=0. Smooth cutoffs s=χ_R make this a compact-test contradiction to any uncorrected identification: Q(fχ_R) tends to zero while the displayed finite DIV energy tends to the strictly positive value. The correction cannot be a discarded nonnegative remainder.

Thus the rectangle identity survives; the requested automatic DIV-to-canonical-CSS transport does not. Reweighting all coordinates to make \(c_{nd}=c_n/\sqrt d\) on constants requires the multiplicative profile \(c_n\propto n^{-1/2}\), not the canonical translates \(f(x+\log n)\). Such a replacement changes the object unless (DIV-POT) and the other source terms are retained.

**Lean-ready heads:** `coupled_integrated_divisibility_identity` for (DIV-CONT), `coupled_divisibility_ground_weight_potential` for (DIV-POT), and `coupled_divisibility_constant_ratio_positive` for (DIV-PLANT). The first is a finite sum/integral and translation calculation, not a claim of continuum Weil positivity.

## C3. The certificate-class obstruction

### Lemma C3.1 — the full translated null family [ABSTRACT][PAPER]

For every real q, \(f_q=U_qf\) lies in X and
\[
 \mathcal B(f_q,v)=0\quad(v\in X).                            \tag{TRANS-RAD}
\]
**Proof.** Translation preserves \(\mathcal D\) and
\(\|e^{|x|}U_qg\|_2\le e^{|q|}\|e^{|x|}g\|_2\), so U_q acts boundedly on X. In (Q), H and all correlations are translation invariant. Also
\(A_\pm(U_qg)=e^{\pm q/2}A_\pm(g)\); their product is unchanged. Polarization gives
\(\mathcal B(U_qg,U_qv)=\mathcal B(g,v)\). Apply the inherited radical identity to \(f,U_{-q}v\). This also follows directly from [CCM, Lemma 2.2] and (3.10). No statement that the radical is one-dimensional is made.

**Lean-ready head:** `coupled_translate_canonical_radical (q : ℝ) (v : X)`, conclusion (TRANS-RAD), after `coupled_translate_weil_pairing` and the explicit bounded translation action on X.

### Lemma C3.2 — compact witnesses with an explicit vanishing budget [COFINAL_FAMILY][PAPER]

Fix smooth cutoffs \(0\le\chi_R\le1\), equal to 1 on [-R,R], zero off [-R-1,R+1], with \(|\chi_R'|\le c_\chi\), and R≥1. Define
\[
 r_q(x)=\frac{f(x-q)}{f(x)},\qquad
 s_{q,R}(x)=\chi_R(x)r_q(x)\in C_c^\infty,\qquad
 a_q=a_*e^{-2|q|}>0.
\]
Then
\[
 \boxed{|D(s_{q,R})|\le C_XC_q^2e^{-2a_qe^{2R}}\longrightarrow0},\qquad
 C_q^2=\frac{(35/3)A_0^2+(4/3)(A_1^2+c_\chi^2A_0^2)}{2a_q}.     \tag{NULL-BUDGET}
\]
Also s_{q,R} agrees **exactly** with r_q on every prescribed compact set when R contains it.

**Proof.** From \(|x-q|\ge|x|-|q|\), (RAD-ENV) bounds \(|f_q^{(j)}(x)|\) by \(A_j e^{-a_qe^{2|x|}}\). Let \(e_R=(1-\chi_R)f_q\). Direct integration gives
\[
 \|e^{|x|}e_R\|_2^2\le\frac{A_0^2}{2a_q}e^{-2a_qe^{2R}},\quad
 \|e_R'\|_2^2\le\frac{A_1^2+c_\chi^2A_0^2}{a_q}e^{-2a_qe^{2R}}.
\]
For H¹ functions u, the translation estimates \(\|\Delta_tu\|_2\le t\|u'\|_2\) and \(\|\Delta_tu\|_2\le2\|u\|_2\), together with \(a(t)\le4/(3t)\) below 1 and \(a(t)\le(4/3)e^{-t/2}\) above 1, give
\(\mathcal D(u)\le(2/3)\|u'\|_2^2+(32/3)\|u\|_2^2\).
These bounds prove \(\|e_R\|_X^2\le C_q^2e^{-2a_qe^{2R}}\). By (TRANS-RAD),
\(D(s_{q,R})=Q(f_q-e_R)=Q(e_R)\). Apply (X). No noncompact ratio is substituted directly in CSS and no positivity premise is used.

**Lean-ready head:** `coupled_compact_translated_radical_budget (q R : ℝ)`, with the stated cutoff conditions and both the X-error and (NULL-BUDGET) inequalities. The ratio is formed only with the proved strictly positive f.

### Lemma C3.3 — finite translates are independent [ABSTRACT][PAPER]

Let f be the canonical function above. For distinct real \(p_1,\ldots,p_k\) and complex \(d_1,\ldots,d_k\),
\[
 \left[\forall q\in\mathbb Q:\ \sum_{\ell=1}^k d_\ell f(p_\ell-q)=0\right]
                         \quad\Longrightarrow\quad d_\ell=0\ (1\le\ell\le k). \tag{INDEP}
\]
**Proof.** Continuity and density of the rationals extend the identity to every real q. Fourier transform in q is legitimate because f is integrable. It gives
\[
 \widehat f(-\xi)\sum_\ell d_\ell e^{-i\xi p_\ell}=0\quad(\xi\in\mathbb R).
\]
Since f>0, \(\widehat f(0)=\int f>0\). Continuity of this transform gives an open interval around zero where it is nonzero. The finite exponential polynomial therefore vanishes on that interval. Its derivatives of orders 0 through k-1 at zero give
\(\sum_\ell d_\ell p_\ell^j=0\), j=0,...,k-1. The Vandermonde determinant is \(\prod_{i<j}(p_j-p_i)\ne0\), hence every coefficient vanishes. This is an elementary Fourier/finite-algebra argument; it imports no zero-free region for zeta and uses no locations of its zeros.

**Lean-ready head:** `coupled_finite_translates_linearly_independent`, for a continuous integrable real f with positive integral, distinct points and the displayed rational-translate vanishing condition. It can be generalized to any nonzero L¹ function after locating a nonzero Fourier interval. The needed primitives are `Integrable`, Fourier translation, continuity, finite differentiation and the Vandermonde determinant; exact convenience-API spellings are not claimed checked here.

### Theorem C3.4 — no nontrivial positive finite-stencil minorant [ABSTRACT][PAPER]

Let
\[
 (Ss)(x)=\sum_{\ell=1}^k c_\ell s(x+\tau_\ell),\qquad
 A_S(s)=\int W(x)|(Ss)(x)|^2dx,                            \tag{STENCIL}
\]
where the shifts are distinct, the real coefficient vector is not zero, and W is a nonnegative finite measurable function. No uniform diameter bound is required. Even the condition \(\sum c_\ell=0\) is unnecessary for the following stronger conclusion:
\[
 \left[\forall s\in C_c^\infty:\ A_S(s)\le D(s)\right]
                           \quad\Longrightarrow\quad W=0\text{ a.e.}       \tag{NO-MINORANT}
\]

**Proof.** For each rational q, apply the asserted inequality to s_{q,R}. Nonnegativity and (NULL-BUDGET) force \(A_S(s_{q,R})\to0\). For each fixed x, all k sampled points eventually lie in [-R,R], so \(Ss_{q,R}(x)=Sr_q(x)\) eventually. Fatou's lemma for the nonnegative integrand gives
\(\int W|Sr_q|^2=0\).
There are only countably many rational q. Outside one null set, every x with W(x)>0 therefore satisfies
\[
 \sum_\ell\frac{c_\ell}{f(x+\tau_\ell)}f(x+\tau_\ell-q)=0
                                                  \quad(q\in\mathbb Q).
\]
Lemma C3.3, at the distinct points p_ell=x+tau_ell, forces all \(c_\ell/f(p_\ell)\) to vanish. This contradicts the chosen nonzero coefficient vector. Thus W vanishes almost everywhere. Repeated shifts can first be combined; a stencil that cancels identically is, correctly, not excluded as a zero term. □

**Lean-ready heads:** `coupled_nonnegative_stencil_annihilates_translated_ratios` for the Fatou step and `coupled_no_positive_finite_stencil_minorant` for (NO-MINORANT). Define the finite stencil as `Fin k → ℝ` coefficients and shifts, with injective shifts; use nonnegative Lebesgue integrals for Fatou before converting finite values to real integrals. Neither head assumes global Q≥0.

### Corollary C3.5 — exact CSS is impossible [COFINAL_FAMILY][PAPER]

Suppose the finite or countable fixed family in [R, CSS] represented D exactly on every compact smooth s. Each nonnegative summand would separately be bounded by D(s). C3.4 makes every nontrivial summand zero. Hence CSS would imply D identically zero.

But D is not identically zero. Choose
\[
 0<\ell\le\min\{\tfrac12,\tfrac12\log2,
                 \exp[-e^{1/2}(|c_A|+1)]\},
\]
and a real nonnegative compact smooth g supported in an interval of length ell, normalized by \(\|g\|_2=1\). Prime correlations all vanish. Both pole functionals are positive. For \(\ell\le t\le1\), translated supports are disjoint, so \(\|\Delta_tg\|_2^2=2\), and \(a(t)\ge e^{-1/2}/(2t)\). Consequently
\[
 Q(g)\ge e^{-1/2}\log(1/\ell)-c_A\ge1.
\]
The test s=g/f is compact smooth and satisfies D(s)≥1, a contradiction. This proves nonexistence of CSS for precisely the requested full complex test class.

There is also an explicit **strict negative certificate margin**, not merely a zero-limit argument. If one proposed nontrivial summand has W>0 on a set of positive measure, (INDEP) and countability provide a rational q and a bounded measurable set E with
\[
                  0<\eta:=\int_E W(x)|Sr_q(x)|^2dx<\infty.
\]
To obtain E, intersect with bounded x-intervals and sets on which W is bounded above and below; continuity makes Sr_q bounded there. Choose R containing every x+tau_ell with x in E, and satisfying
\(C_XC_q^2e^{-2a_qe^{2R}}<\eta/2\).
For example it suffices, in addition to the support condition, that
\(e^{2R}>(2a_q)^{-1}\log(1+2C_XC_q^2/\eta)\). Then
\[
 \boxed{D(s_{q,R})-A_S(s_{q,R})\le-\eta/2<0.}                 \tag{CERTIFICATE-KILL}
\]
Subtracting the entire proposed nonnegative CSS makes the margin no larger. If all terms are trivial instead, the preceding g/f test gives the reverse identity margin `CSS(g/f) - D(g/f) ≤ -1 < 0`. These are exhaustive strict-upper-bound obstructions. Neither claims \(D(s_{q,R})<0\).

**Lean-ready head:** `coupled_no_countable_finite_stencil_css`, with the exact countable identity and conclusion false; its quantitative companion `coupled_stencil_certificate_margin_negative` has the witnesses q,E,eta,R and conclusion (CERTIFICATE-KILL). Finite cardinality may depend on the summand; no common bound on cardinality or diameter enters the proof.

### C3.6 — continuum splittings and finite-graph scope [ABSTRACT][PAPER]

C1 integrates stencils over t, whereas literal CSS only lists countably many stencils. The obstruction extends to that explicitly enlarged class: let (J,mu) be a sigma-finite positive measure space and integrate \(W(j,x)|S_js(x)|^2\) over (j,x), with jointly measurable data and finitely many sample points per j (partition J by their finite cardinality if necessary). Fatou and the countable set of rational q give the simultaneous equations almost everywhere in (j,x). Pointwise application of (INDEP) again makes every active stencil trivial. For a quantitative witness, also restrict the selected positive-measure set to bounded x and bounded shifts; these restrictions exhaust the parameter space. The same compact cutoff and (CERTIFICATE-KILL) then apply. Thus introducing a continuous splitting parameter does not evade this result.

For comparison, a **real symmetric finite matrix** M with M1=0 is positive semidefinite exactly when it is a sum \(\sum_i\lambda_i u_i u_i^T\), with \(\lambda_i\ge0\) and each nonzero u_i orthogonal to 1. The forward implication is the spectral theorem: Mu_i=lambda_i u_i and lambda_i>0 imply \(u_i^T1=0\). The converse follows by expanding the nonnegative squares. Zero eigenvalues contribute nothing. This is a characterization, not an independent source construction.

Two-point edge squares are a narrower cone: their off-diagonal entries are nonpositive. The three-vertex matrix \((1,-2,1)(1,-2,1)^T\) is PSD with zero row sums but a positive (1,3) entry, so it is not a positive sum of two-point edge squares. The request's broader zero-mean-stencil finite statement is valid; its continuum extrapolation is not. The canonical ratio form has far more null functions than constants, and their restrictions to **every finite set of points span all sample values**, by (INDEP).

No contradiction with finite matrix factorization arises: compact truncations of translated null functions do not live in one fixed finite section. Nor does the theorem exclude a limit of certificates whose stencils change with the cutoff. Such a limit is not the fixed positive-series identity CSS.

**Lean-ready heads:** `coupled_no_measurable_finitary_stencil_factorization` under the stated product-measure hypotheses; `coupled_finite_psd_row_sum_zero_sos_iff` over real finite matrices. The latter finite characterization must not be used as an assumed factorization of the continuum form.

## C4. Exact remainder, Fourier check, and what remains live

### Lemma C4.1 — a genuine local extraction has a negative remainder direction [COFINAL_FAMILY][PAPER]

For the same fixed interval I in C1, define the explicitly nonnegative extraction
\[
 A_I(s)=\int_I B_-(t)\int f(x)f(x+t)
             |s(x)-2s(x+t/2)+s(x+t)|^2dxdt.                    \tag{EXTRACT}
\]
It is finite for compact smooth s. Let \(\Omega(x,t)=B_-(t)f(x)f(x+t)\) and
\(P(s)=\int b_+E_s+\sum w_nE_s(\log n)\). Applying the N=2 identity gives exactly
\[
 \begin{split}
 D(s)&=A_I(s)+R_I(s),\\
 R_I(s)&=P(s)-\int_{(t_0,\infty)\setminus I}B_-(t)E_s(t)dt\\
 &\quad-2\int_I\int\Omega(x,t)
       \{|s(x+t/2)-s(x)|^2+|s(x+t)-s(x+t/2)|^2\}dxdt.          \tag{REMAINDER}
 \end{split}
\]
This identity pays the displayed long-edge term by a square, but charges both shorter edges. It does not create free positive capacity. Moreover its remainder is **not positive semidefinite**.

**Proof of the last assertion.** The three coefficients (1,-2,1) at the distinct points x,x+t/2,x+t are nonzero, and \(\Omega>0\) on \(\mathbb R\times I\). The product-measure version of C3.6 supplies a rational q, a bounded positive-measure region E in this product space, and \(\eta=\iint_E\Omega|S_t r_q|^2>0\). Choose R to contain its sampled points and satisfy (NULL-BUDGET) <eta/2. The extraction on s_{q,R} is at least eta, so
\[
                         R_I(s_{q,R})\le-\eta/2<0.             \tag{REMAINDER-KILL}
\]
This is a counterexample to closing this extraction with an everywhere nonnegative remainder, not a counterexample to Q≥0. In fact C3 excludes **every** nonzero globally dominated extraction of this positive local type.

**Lean-ready heads:** `coupled_second_difference_extraction_identity` for (REMAINDER) and `coupled_second_difference_remainder_negative` for (REMAINDER-KILL), using the product-measure witness theorem rather than an unproved sign estimate.

### Lemma C4.2 — exact Fourier kernels; a source correction [ABSTRACT][PAPER]

Let \(w_t(x)=f(x)f(x+t)\), \(C_0(t)=\int w_t(x)dx\), and
\[
 \mathcal M(\eta,\xi)=\int_{t>0}
       (e^{-i\eta t}-1)(e^{i\xi t}-1)
                 \widehat{w_t}(\eta-\xi)\,d\nu(t),\quad
 d\nu=b(t)dt+\sum_{n\ge2}w_n\delta_{\log n}.
\]
The notation means the separately convergent weighted integral and sum, not multiplication by a pointwise delta function. Define \(p_t(\xi)=(1-e^{i\xi t/2})^2\). The remainder's two-frequency kernel and plane-wave value are
\[
 \begin{split}
 \mathcal M_{R_I}(\eta,\xi)
 &=\mathcal M(\eta,\xi)-\int_I B_-(t)
               \overline{p_t(\eta)}p_t(\xi)\widehat{w_t}(\eta-\xi)dt,\\
 R_I(s)&=(2\pi)^{-2}\iint\overline{\widehat s(\eta)}
                      \mathcal M_{R_I}(\eta,\xi)\widehat s(\xi)d\eta d\xi,\\
 \sigma_{R_I}(\xi)&=\int2(1-\cos\xi t)C_0(t)d\nu(t)
                   -\int_I B_-(t)|1-e^{i\xi t/2}|^4C_0(t)dt.   \tag{FOURIER-R}
 \end{split}
\]
**Proof.** Insert Fourier inversion into every difference, and integrate in x. The x-integral of \(w_t(x)e^{i(\xi-\eta)x}\) is its transform at eta-xi. Near zero the original difference product contributes \(O(|\eta\xi|t^2)\), which is integrable against b. At infinity the canonical autocorrelation controls the total variation; Schwartz decay in both frequencies justifies Fubini. The extraction integrates over the compact interval I away from zero, so its interchange is immediate from the same bounds. Setting eta=xi yields the displayed plane-wave value. Both values at xi=0 are zero exactly. The kernel is Hermitian, not a scalar multiplier.

**Correction of [R, Section 2 and C4].** The asserted unconditional formula with only real gamma and nonnegative squares is not licensed by the explicit formula. For \(g_\xi(x)=f(x)e^{i\xi x}\), with real xi, its actual zero-side expression is
\[
 Q(g_\xi)=\frac1{A^2}\sum_{z\in Z(\Xi)}
       \overline{\Xi(\bar z-\xi)}\Xi(z-\xi)
          =\frac1{A^2}\sum_{z\in Z(\Xi)}\Xi(z-\xi)^2.          \tag{SIGNED-ZERO}
\]
The squares in the last expression can be **complex**. A conjugate pair contributes \(2\Re\Xi(z-\xi)^2\), whose sign is not fixed. Real-zero sums would be nonnegative under the additional reality assertion; that assertion is not used here. Likewise, subtracting a nonnegative extraction does not preserve a plane-wave sign automatically. No global sign or monotonicity of either symbol is established by the observer's finite numbers.

The genuine consistency check is equality of the exact geometric and zero-side formulas with their actual conjugations and normalization. Nonnegativity of the two-frequency diagonal would still not establish positive semidefiniteness of its full kernel. Formula (FOURIER-R) and (REMAINDER-KILL) retain that distinction.

**Lean-ready heads:** `coupled_extraction_two_frequency_remainder` with all three formulas in (FOURIER-R); `coupled_modulation_signed_zero_pairing` with the published explicit-formula import and (SIGNED-ZERO). No root-location hypothesis is inserted or inferred.

### Positive control separating certificate death from form negativity [ABSTRACT][PAPER]

Let \(F(x)=e^{-(x-1)^2}+e^{-(x+1)^2}>0\), \(\omega=\pi/2\), and
\(Q_*(g)=|\int g(x)e^{-i\omega x}dx|^2\). This form is nonnegative. Fourier translation gives
\(\widehat F(\omega)=2\cos\omega\,\widehat{e^{-x^2}}(\omega)=0\), so every translate of F is in its radical. Gaussian tails give the same compact-approximation argument; (INDEP) applies because F is continuous, positive and integrable. Therefore the associated ratio form \(Q_*(Fs)\) also has **no nontrivial positive finite-stencil CSS**, although it is manifestly nonnegative and not zero. Nonzeroness follows by taking \(g=e^{i\omega x}\varphi\) for a nonzero nonnegative compact bump varphi. Its positive factor is a global integral, not a finite-sample stencil.

This exact control rejects the false inference “C3 proves the original form is negative.” It also explains the boundary of the result without assuming RH.

**Lean-ready head:** `coupled_nonlocal_psd_without_finite_stencil_css_plant`, with F and Q_* as above and the explicit Fourier cancellation.

### Unchanged consumer and remaining inequality [COFINAL_FAMILY][CONDITIONAL]

The remaining source statement is still
\[
 \sum_{n\ge2}w_nE_s(\log n)+\int_0^{t_0}b_+(t)E_s(t)dt
                  \ge\int_{t_0}^{\infty}B_-(t)E_s(t)dt
                    \quad(s\in C_c^\infty(\mathbb R;\mathbb C)).       \tag{DOM-OPEN}
\]
It is not proved or refuted here. Through g=fs it would give W and then the published Weil criterion. The conditional assembly is immediate; it supplies no new sign premise.

The alternative same-family finite target remains [D, ZG], on the literal full matrices \(K_m=\operatorname{ccmWeilMatFinite}(m,m)\): independently construct \(e_m\ge0\), \(e_m\to0\), and prove \(K_m+e_m I\succeq0\) for all sufficiently large m, with [D, REC-FORM]. This is outside the killed fixed-series CSS class. Neither a finite list of cells nor an eigenvalue fit supplies its universal quantifier.

For a fixed test g=fs in [X]'s super-exponential class, the existing finite-prime enclosure is an admissible sign discriminator:
\[
 \mathcal A_P(g)-E_S(g,P)\le Q(g)
                    \le\mathcal A_P(g)+E_S(g,P)+E_J(g,P),
\]
with the **positive cutoff boundary** \(2\Delta(\log P)P^{-1/2}C_g(\log P)\) retained in \(\mathcal A_P\). PASS requires its rigorous lower endpoint to be nonnegative; KILL of a Weil test would require a strictly negative upper endpoint. Neither result is manufactured from a zero-consistent interval. For the certificate-class obstruction, (CERTIFICATE-KILL) is the separate, exact discriminator and already has the correct upper-bound direction.

## Prediction ledger and independent checks

Observer wording and probabilities are unchanged. Fates concern the specified events, not a retroactive replacement by easier claims.

| Prediction | p | Fate |
|---|---:|---|
| P_C1_SPLITTING_BALANCE_COMPUTED | 0.75 | CONFIRMED, PAPER: (PATH), (CAP), (CAP-KILL), and (UV). |
| P_C1_SPLITTING_SUFFICES | 0.15 | REFUTED for the requested local-square mechanism; C3 excludes its exact closure even after repairing the allocation. |
| P_C2_MULTIPLICATIVE_RECTANGLE_IDENTITY_PROVED | 0.55 | NOT REALIZED AS THE FULL STATED EVENT: (RECT) is proved; the literal transport (DIV-CONT) has extra weights and (DIV-POT) terms. No corrected DIV-to-CSS atom construction is supplied. This does not exclude every possible arithmetic rewrite. |
| P_C3_LOCAL_STENCIL_OBSTRUCTION_THEOREM | 0.40 | CONFIRMED, PAPER; no common bound on stencil diameter or cardinality is needed. |
| P_RESULT_COMPLETE | 0.03 | REFUTED as this batch's outcome. |
| P_RESULT_PARTIAL | 0.80 | REFUTED as the selected overall result code; the requested certificate class is excluded, not just left unconstructed. |
| P_RESULT_REFUTED | 0.17 | CONFIRMED. |

An informed prediction was registered in this conversation before completion of the obstruction/domain check: “the translated canonical null family excludes nontrivial positive finite-stencil certificates,” p=0.85. Its fate is **CONFIRMED AT PAPER LEVEL**, independently unverified. It was not described as a blind prediction of an already unfamiliar mechanism. Earlier requests' predictions and artifacts are not changed.

Register the following only for subsequent independent checks, not as retrospective predictions of the present derivations:

```yaml
P_COUPLED_TRANSLATED_RADICAL_AND_CUTOFF_SURVIVE:
  probability: 0.92
  event: TRANS_RAD_and_NULL_BUDGET_survive_independent_domain_and_constant_audit
  fate: PENDING
P_COUPLED_FINITE_STENCIL_NO_GO_SURVIVES:
  probability: 0.90
  event: NO_MINORANT_and_CERTIFICATE_KILL_survive_without_extra_global_positivity_premise
  fate: PENDING
P_COUPLED_SPLITTING_JACOBIAN_SURVIVES:
  probability: 0.90
  event: CAP_has_N_squared_before_the_edge_sum_and_CAP_KILL_preserves_its_direction
  fate: PENDING
P_COUPLED_RECTANGLE_DIV_REPAIR_SURVIVES:
  probability: 0.94
  event: RECT_DIV_CONT_DIV_POT_and_DIV_PLANT_survive_exact_algebra_audit
  fate: PENDING
```

## Dependency epistemics, alternatives, and closeout

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: nonnegative_full_Weil_form_W
  ORIGINAL_REQUESTED_OBJECT: exact_CSS_with_positive_finite_point_stencils
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - DOM_OPEN_without_any_local_SOS_factorization_implies_W_via_GS
    - same_family_finite_lower_errors_tending_to_zero_plus_REC_FORM_imply_W
    - nonlocal_source_defined_positive_factorization_would_imply_W_if_constructed
  FAILURE_TYPE: INCOMPATIBILITY
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: STRICT_NEGATIVE_UPPER_BOUND_ON_CERTIFICATE_IDENTITY_MARGIN
  PINNED_EVIDENCE: THIS_DOCUMENT_C3_CERTIFICATE_KILL_AND_NONZERO_CONTROL
  NOVELTY_AXIS: translated_radical_local_sample_rank_obstruction
  ROUTE_FAMILY_MATHEMATICALLY_DEAD: false
REMAINING_ROUTE:
  EPISTEMIC_STATUS: RESEARCH_DEBT
  MINIMAL_MISSING_IDENTITY: DOM_OPEN_or_same_family_vanishing_lower_error_for_literal_K_m
  REOPEN_TRIGGER: nonlocal_signed_control_or_a_quantified_recovering_finite_certificate_family
```

**Two representations outside this kill.** R1: a genuinely nonlocal factor acting on fs, with its annihilation of every translated canonical vector proved before estimating its sign. Audit object: the full two-frequency kernel, not its diagonal. Estimated kill-power/cost for checking a concrete proposed factor: 9/10 and 6/10. No such source-defined positive factor is asserted here. R2: cutoff-dependent full CCM Gram certificates with a vanishing negative allowance and independently proved fixed-test recovery. Estimated kill-power/cost for a proposed cofinal rule: 9/10 and 7/10. These are qualitative estimates, not runtimes. Neither representation is authorized for a numerical escalation by this verdict.

**Strongest attack and answer.** CSS was required only for compact s, while r_q is noncompact. C3 never substitutes r_q in CSS. It uses the compact s_{q,R}, the explicit bound (NULL-BUDGET), and either Fatou or exact agreement on a bounded witness set. This is the crucial scope guard. Positivity of the individual proposed weights, not positivity of Q, forces their disappearance. The argument also does not assume point evaluation is continuous on X.

**Single next local directive: independent paper audit of C3.1-C3.5.** Rebuild translation covariance from [CCM, Lemma 2.2 and (3.10)], verify the compact-cutoff budget, check the rational-translate/Vandermonde step, and reproduce (CERTIFICATE-KILL) for an arbitrary proposed active stencil. Success requires the exact universal finite-stencil scope and no positivity input. Failure must identify an explicit admissibility, measure, or limit counterexample. Do not replace this check by another generic Gram constructor. No execution, Lean edit or Aristotle submission is issued in this transaction.

The Lean realization needs a finite-stencil structure, `ContDiff`, `HasCompactSupport`, Lebesgue/Bochner integration, nonnegative integrals and Fatou, continuous Fourier transform of L¹ functions, finite differentiation, and finite Vandermonde linear algebra. The heads above are mathematical specifications with named definitions to implement, not source claimed to compile. The source explicit formula remains a PAPER theorem; it is not introduced as a project axiom. [L]'s already written finite theorems remain separate from this new analytic proof.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: FALSIFICATION_PROGRESS
  COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
  ROUTE_SCORE: 4
  what_became_smaller: local_finite_stencil_CSS_is_removed_as_a_global_sign_strategy
  what_was_killed: exact_positive_finite_sample_square_factorizations_and_nonzero_local_minorants
  what_must_not_recur: treating_one_canonical_null_direction_as_the_entire_radical
  smallest_open_gap: DOM_OPEN_with_joint_signed_interactions
  next_decisive_test: independent_translated_radical_and_Fatou_obstruction_audit
  iteration:
    target: source_defined_coupled_signed_square_certificate
    status: FATAL
    failed_strategy: fixed_positive_local_stencil_decomposition
    invariant_learned: every_positive_factor_must_annihilate_the_entire_translated_radical_family
    forbidden_future_move: retry_local_stencils_by_increasing_their_finite_size_or_diameter
```

## Verification handoff

Only EXPECTED_VERDICT_PATH is written, on `rh_clean`, with a `[Proshka]` commit subject. The actual commit SHA and Git blob are returned after readback; they cannot be embedded recursively into the same content. The request lock was independently recomputed from the connector-fetched text. The two local parent-verdict byte hashes were also recomputed and matched the pinned GitHub blobs. No uncomputed full hash is claimed for [L].

This is a documentation-only **PAPER** verdict. No Lean source, Lean blob, kernel output, or new numerical result exists for this adjudication. Expected axioms for a future completed formalization are `[propext, Classical.choice, Quot.sound]`; the necessary analytic imports must be proved, not hidden in an extra axiom. Independent confirmation preserves this certificate-class KILL; it does not prove or refute RH. The route, phase key, old verdicts and shared state remain unchanged.
