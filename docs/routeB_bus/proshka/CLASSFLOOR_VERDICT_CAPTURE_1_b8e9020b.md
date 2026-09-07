# STATUS: TRY_CLASS_FLOOR_SOURCE_TRACE_CLOSURE_AND_SIGNED_COMPLEMENT
```yaml
OPERATIVE_CLASS: TRY_CLASS_FLOOR_SOURCE_TRACE_CLOSURE_AND_SIGNED_COMPLEMENT
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-07-CLASSFLOOR
BOUNDARY_ID: GOAL058_CERTIFICATE_RATIFICATION_AND_CLASS_FLOOR_REPRESENTATION
RESULT:
  Q1: CERTIFICATE_RATIFIED
  Q1_SCALAR: CERTIFICATE_RATIFIED
  Q1_PACKET: CERTIFICATE_RATIFIED
  Q2: PROVED_ON_CLASS
  Q3: PROVED_ON_CLASS
  Q4: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 89bd22f6f88e472cf42f4e03f73852c6594e21a6
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_CLASS_FLOOR_REPRESENTATION_2026-09-07.txt
  GIT_BLOB: 682c0c543f77dd3e9994e4a951601a3eb6a0c78e
  SHA256: d2a61d4dcd9f3235e167db3c355ca3f8bd53226dc6d6c7d032ed0b3e2345aa57
  BYTES: 14489
  LINES: 108
  FINAL_LF: true
  GITHUB_FETCH_AND_LOCAL_UTF8_HASH: MATCHED
  GIT_OBJECT_SHA1_INDEPENDENTLY_RECOMPUTED: true
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
RATIFIED_CERTIFICATE_SCOPE:
  H4_SCALAR_FLOOR: at_least_1_over_500
  REQUESTED_PACKET_RANK: 3
  REQUESTED_PACKET_PHYSICAL_SPAN_FLOOR: at_least_1_over_1000
  FOUR_COORDINATE_PENCIL: quotient_by_exact_kernel_required
  REPORTED_0_00116_LOWER_BOUND: upward_rounding_not_authorized
  LAST_PRINTED_DECIMAL_DIGITS: not_promoted_to_directed_endpoints
  GENUINE_FOUR_DIMENSIONAL_ENLARGEMENT: not_certified_not_refuted
  INTERVAL_RUNS_RERUN_BY_JUDGE: false
  BASIS: pinned_outputs_plus_static_checker_and_analytic_budget_audit
SOURCE_IDENTITY:
  TESTED_TRACE_AND_MELLIN_IDENTIFICATION: PAPER_PROOF_SUPPLIED
  GENERALIZED_WAVE_ASSUMED_L2: false
  UNTESTED_SEMILOCAL_TRACE_ASSUMED_FINITE: false
  CONSTANT_256: survives
  ADDITIONAL_VALID_CONSTANT: 120
  CONSTANT_AT_MOST_8: not_established
CLASS_RESULT:
  WHOLE_SCALAR_CLASS_NONNEGATIVE: not_proved
  WHOLE_MARGIN_CLASS_NONNEGATIVE: not_proved
  WHOLE_CLASS_SUM_OF_SQUARES: not_constructed
  EXPLICIT_INFINITE_DIMENSIONAL_POSITIVE_NEIGHBORHOOD: proved_from_ratified_seed
  NEGATIVE_MULTIPLIER_IMPLIES_NEGATIVE_COMPRESSION: rejected
  UNSIGNED_COMPLEMENT_NORM_PROVES_PSD: rejected
CLOSES:
  - REQ-2026-09-07-CLASSFLOOR
CLOSES_REVIEW_OBLIGATIONS:
  - h4_scalar_and_rank_three_packet_certificate_audit
  - uniform_Mellin_J_constant_256_paper_recheck
  - RESONANCE_6_tested_trace_domain_at_fixed_cutoff
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
EVIDENCE_BOUNDARY:
  PIN: 89bd22f6f88e472cf42f4e03f73852c6594e21a6
  POST_REQUEST_RESEARCH_RESULTS_USED: false
  ALL_SHELF_SHA_PREFIXES_REHASHED: false
  ANOTHER_CLASSFLOOR_VERDICT_USED: false
NEW_DERIVATIONS:
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  HISTORICAL_PRIORITY: not_claimed
EXECUTION:
  NUMERICAL_RUN: false
  LEAN_EDIT: false
  LEAN_KERNEL_VERIFICATION: false
  ARISTOTLE_SUBMISSION: false
  QUEUE_OR_STATE_EDIT: false
  WRITE_SCOPE: VERDICT_DOC_ONLY
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CLASS_FLOOR_REPRESENTATION_2026-09-07.md
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Decision, sources, and certification boundary

The scalar certificate supplies a genuine positive lower bound for the declared polynomial profile, and the requested packet supplies a lower bound on a **three-dimensional physical span**, not an invertible four-dimensional coefficient pencil. The analytic source identification can be closed on paper without assuming that a generalized Mellin wave belongs to the cutoff Hilbert space. The whole-class sign is still not proved. [FINITE_CELL][ARB_INTERVAL, pinned execution; PAPER audit]

The ratified robust thresholds are **1/500** for the scalar seed and **1/1000** on the requested span. The latter must not be rounded upward to 0.00116. The reported extra fourth independent direction remains uncertified. No new numerical execution occurred in this adjudication.

The original error formulas are sound. Two implementation descriptions require correction: there are padded floating-point transport conversions, and a radius-free decimal is not automatically a directed endpoint. Section 2.5 gives an explicit serialization allowance; the improved constant in Section 3 leaves enough unused Euler-tail budget to absorb this allowance without enlarging the packet's stored entry hulls. This does not certify the last digit of a radius-free printed spectral endpoint.

**Sources at the request pin.** [REQ] is the complete hashed request. [H4] is `docs/routeB_bus/H4_SCALAR_FLOOR_CERTIFICATE_REPORT_2026-09-07.md`, SHA-256 prefix `83e7c763e373404b`. [PK] is `docs/routeB_bus/H4_PACKET_FLOOR_CERTIFICATE_REPORT_2026-09-07.md`, blob `2f6a0fb766e5d8c3623cdf04ba7365b19bd8b9f0`. [SF1] is the SCALARFLOOR verdict including its append-only Section 11, blob `e7f3bb3300b251c589bf6cc6ebd4ed4f69eadf40`. [SF2] is the separately preserved `...SCALAR_FLOOR_AND_SEMILOCAL_CONDITIONING_2026-09-07_INDEPENDENT_66cc75a1.md`. [R] is the RESONANCE verdict named in the request, blob `ce20e425edcdaad189902e90c6b3dbe414b5bb34`.

The load-bearing implementation files read were:

| File below `docs/routeB_bus/phase5_codex/h4_cert/` | Git blob |
|---|---|
| `h4arb.py` | `216a34f24c51b6f31694c2af55ce3576fc632c3d` |
| `evalf.py` | `58505ed264ff638e602e4fc73098f234758e12d5` |
| `cert.py` | `479515055ad0bed84fc38e5f9c52fec338345d97` |
| `budget.py` | `db375d4e80230a6369cae9ce3959a002947acd67` |
| `assemble.py` | `72c48e86398753e4f37156fabcc7c1dc2356a91e` |
| `packet/packassemble.py` | `09cfec9c92bfc4b44341eb6eb9fdb112884e2f58` |
| `packet/packequad.py` | `c6931aef797b980533225052c4bb6c9d97ae8003` |
| `packet/packverify.py` | `15215269b687ef6316b3392fd46304fee9ff67c6` |
| `out/main.txt` | `0046b9ecb1615efef9af5505eba9d9d66fa529dc` |
| `packet/out/verify.txt` | `caaea234f1bf56d496578513d01b034b4b53713d` |

The recorded outputs, not a newly rerun process, are the numerical evidence. The request hash was independently recomputed; this sentence does not claim that every shelf hash was recomputed.

**External primary sources.** [CC20] Connes--Consani, arXiv:2006.13771v1, Theorem 4.7 and Appendix D, supply the trace conventions and the smooth half-line commutator mechanism. [CCM23] Connes--Consani--Moscovici, arXiv:2310.18423v2, (57)--(59) and Theorem 4.6, supply the finite-Euler multiplier and the Sonin-space correspondence. The relevant CCM23 pages 22--23 and CC20 page 51 were visually checked; two other requested CC20 screenshots failed, and the parsed text was used there. [ATAP] Trefethen, *Approximation Theory and Approximation Practice*, Chapter 8, Theorems 8.1--8.2, was checked in the author's `chebfun/ATAP/chap8.m` source. [ARB] FLINT's official `arb_get_str` documentation supplies the decimal-rounding contract. No historical attached roadmap is an input to this adjudication.

## 1. Convention and target lock

Put
\[
 a=\log2,\qquad r=2^{-1/2},\qquad
 \delta=(\log3-\log2)/8,\qquad I=(-\delta,\delta).
\]
The source test class is
\[
 \mathcal H_{00}^{\rm sm}(I)=
 \{h\in C_c^\infty(I;\mathbb C):\int h(x)e^{x/2}dx=
                                     \int h(x)e^{-x/2}dx=0\}.
\]
Let \(H=\|h\|_2^2\), use \(\widehat h(\xi)=\int h(x)e^{-i\xi x}dx\), and distinguish the unitary Fourier transform \(\mathscr F=(2\pi)^{-1/2}\widehat{\phantom h}\). With \(U_ch(x)=h(x-c)\),
\[
 v_h=\frac{U_{a/2}h-U_{-a/2}h}{\sqrt{2H}},\quad
 W_h=\frac{(1-\cos(a\xi))|\widehat h|^2}{H},\quad
 \int W_h=2\pi.                                                    \tag{1}
\]
The last identity uses disjoint supports and Plancherel. Define
\[
 \ell_2(\xi)=2\Re(\gamma_2(\xi)t_2(\xi)),\qquad
 \mathcal F(h)=-\int W_h\ell_2,\qquad
 \mathfrak m(h)=L_2(v_h)-n_2(v_h)=-\int W_hd_2.                     \tag{2}
\]
The source identity and the last equality are proved in Section 4, not assumed in the final application. The compact test-space operator in Section 5 represents the **unnormalized numerator** \(H\mathcal F(h)\). The normalized floor is not itself a quadratic form. [ABSTRACT][PAPER]

## 2. Q1: certificate ledger audit

### 2.1 The two tail ingredients are valid

For every real \(\xi\),
\[
 |J(\beta,\xi)|\le\int_0^1(-\log v)v^{-1/2}dv=4.
\]
Combining this with the uniform estimate of Section 3 term by term gives
\[
 |t_2(\xi)|\le T_0:=\frac1{2\pi}
 \left[4+\sum_{j\ge0}\min\{4,256\beta_j^{-1/2}(1+\log\beta_j)\}\right],
 \quad\beta_j=2\pi2^j.                                            \tag{3}
\]
`budget.Tstar` sums a finite prefix and an explicit geometric/logarithmic upper tail. Thus its output is an upper enclosure for (3); the convenient safe statement is \(T_0<14\), not \(T_0\le13.937\). The more precise recorded ball is \([13.9371046604\mathbin{+/-}1.24\cdot10^{-11}]\). [ABSTRACT][PAPER; FINITE_CELL/ARB_INTERVAL for that value]

For the zero-extended \(h_4\), both \(h_4\) and \(h_4'\) vanish at the endpoints. Integrating twice by parts produces no boundary term. A third integration isolates \(h_4''(\pm\delta)\); integrating its remainder once more gives
\[
 |\widehat h_4(\xi)|\le B_3|\xi|^{-3}+B_4|\xi|^{-4},
 \quad B_3=2|h_4''(\delta)|,
 \quad B_4=2|h_4'''(\delta)|+\int_{-\delta}^{\delta}|h_4''''|.        \tag{4}
\]
The code bounds the last integral by integrating each absolute polynomial monomial. It is conservative, not an identity claiming that all polynomial terms have one sign. Squaring (4), using \(1-\cos\le2\), and integrating both tails gives exactly
\[
 \mu_X\le\frac4H\left[
 \frac{B_3^2}{5X^5}+\frac{2B_3B_4}{6X^6}+\frac{B_4^2}{7X^7}\right].\tag{5}
\]
The omitted floor is bounded by \(2T_0\mu_X\). The Euler-series tail and this frequency tail are different omissions and are not counted twice. [ABSTRACT][PAPER]

For packet entries, Cauchy--Schwarz gives the second, sharper estimate
\[
 |R^{ij}_{\rm freq}|\le2T_0\sqrt{D_iD_j},\qquad
 D_i=2\pi H_{ii}-\int_{|\xi|\le X}(1-\cos(a\xi))|\widehat h_i|^2.
                                                                    \tag{6}
\]
The subtracted mass needs its **own** quadrature and arithmetic enclosure. A sampled mass deficit is not an exact number. Taking the smaller of two proved upper bounds is valid. A nonnegative upper bound on \(D_i\) larger than another analytic upper bound is merely weaker; the printed `D<=nu: False` for the extra h7 row is not evidence that the true mass violates either bound.

### 2.2 Holomorphic continuation and the quadrature bound

One must not analytically continue `Re` or `abs_squared` literally. For the real-even packet, the relevant holomorphic continuation is
\[
 f_{ij}(z)=-(1-\cos(az))\widehat h_i(z)\widehat h_j(z)
       [\gamma_2(z)t_2^{[J_0]}(z)+\gamma_2(-z)t_2^{[J_0]}(-z)].    \tag{7}
\]
On the real axis it is the required integrand. For general complex tests replace the first transform factor by \(\overline{\widehat h_i(\bar z)}\), which is entire, before polarizing.

The defining integral makes \(J(\beta,-z)\) holomorphic for \(\Im z>-1/2\), and its reflection is holomorphic for \(\Im z<1/2\). The gamma quotient and finite Euler quotient are holomorphic in their corresponding half-strips; their first possible singularities border \(|\Im z|<1/2\). Thus (7) is holomorphic throughout that strip. Zeros of reciprocal gamma are not poles.

For a panel of width \(w\), the Bernstein ellipse has
\[
 R_{\rm maj}=\tfrac w4(\rho+\rho^{-1}),\qquad
 R_{\rm min}=\tfrac w4(\rho-\rho^{-1}).
\]
The condition is \(R_{\rm min}<1/2\). Using the major axis also as the imaginary bound is more conservative when it is below 1/2; it is not mandatory. The packet's rectangular enclosure with the two distinct axes is valid.

On that rectangle,
\[
 |\widehat h_i(z)|\le\|h_i\|_1e^{\delta R_{\rm min}},\quad
 |J(\beta,\pm z)|\le(1/2-R_{\rm min})^{-2},\quad
 |1-\cos(az)|\le1+\cosh(aR_{\rm min}).
\]
Together with the interval gamma/Euler bound this gives the stated \(M_{ij}\). The denominator bound \(1-re^{aR_{\rm min}}>0\) is essential and holds on the chosen ellipses. The gamma-shift fallback bounds moduli through the recurrence; it does not change gamma itself.

For completeness, analyticity in the ellipse gives Chebyshev coefficients bounded by \(2M\rho^{-k}\), by the Laurent expansion under \(z=(w+w^{-1})/2\). Summing the omitted coefficients and their interpolation aliases gives \(\|f-p_n\|_\infty\le4M\rho^{-n}/(\rho-1)\). Integration on \([-1,1]\) therefore costs at most \(8M\rho^{-n}/(\rho-1)\); scaling each panel and doubling the positive-frequency integral gives the code's error formula. [ATAP; ABSTRACT/PAPER]

Optimizing \(\rho\) after the quadrature has run is legal: the quadrature rule is unchanged, and each admissible \(\rho\) proves an error bound for that same rule. This is not post-hoc adjustment of a mathematical prediction. The selected bound must still be exported outward, as addressed in Section 2.5.

### 2.3 Large-beta Mellin evaluation and the series stopping rule

Write \(s=1/2-i\xi\). The classical cosine Mellin integral, first on \(0<\Re s<1\), is
\[
 \int_0^\infty v^{s-1}\cos(\beta v)dv
       =\beta^{-s}\Gamma(s)\cos(\pi s/2).
\]
The integral and its parameter derivative on compact substrips are justified by integration by parts at infinity. Subtracting the part beyond 1 and differentiating yields
\[
 J(\beta,-\xi)=\beta^{-s}\Gamma(s)
 [ (\log\beta-\psi(s))\cos(\pi s/2)+(\pi/2)\sin(\pi s/2)]
       +\int_1^\infty (\log v)v^{s-1}\cos(\beta v)dv.              \tag{8}
\]
For \(g(v)=(\log v)v^{s-1}\),
\[
 g^{(k)}(v)=v^{s-1-k}(P_k\log v+Q_k),\quad
 P_{k+1}=(s-1-k)P_k,\quad Q_{k+1}=(s-1-k)Q_k+P_k.
\]
Here \(P_0=1,Q_0=0\). The boundary term for \(g(1)\) vanishes. Repeated integration by parts gives the recorded sine/cosine boundary terms and, on \(\Re s=1/2\),
\[
 |E_k|\le\beta^{-k}
       \left[\frac{|P_k|}{(k-1/2)^2}+\frac{|Q_k|}{k-1/2}\right].  \tag{9}
\]
This is the error added by `J_asym`; the actual bound, not overlap with another evaluator, is the proof input. Float-based choices between two valid representations do not invalidate either enclosure.

The small-beta series uses twice the first omitted term. The comment `2n>beta+4` alone would not justify a geometric ratio below 1/2. However the implementation also requires the absolute factorial term to be below a threshold smaller than one. Since
\[
 (2n)!\le n^n(2n)^n=(2n^2)^n,
\]
that second condition implies \(2n>\sqrt2\,\beta\). The ratio of subsequent factorial terms is then below 1/2. The factors \(|s+2n|^{-2}\) decrease for the real nodes used. The same argument handles the entire cosine-moment series. Thus the implemented combined stopping conditions justify the remainder; the abbreviated comment is repaired, not used as a false lemma. [ABSTRACT][PAPER]

### 2.4 Packet rank, complex directions, and the pencil

Linearity of \(\partial^2-1/4\) gives
\[
 h_{4z}=h_4-h_5.
\]
The three remaining polynomials are independent: their degrees are distinct, and \(\partial^2-1/4\) is injective on polynomials. For
\[
 L=\begin{pmatrix}1&0&0&1\\0&1&0&-1\\0&0&1&0\end{pmatrix},
\]
therefore
\[
 F_{\rm requested}=L^*F_3L,\qquad H_{\rm requested}=L^*H_3L.
                                                                    \tag{10}
\]
Both four-coordinate matrices have kernel \((1,-1,0,-1)\). The physical quotient, or the independent basis \(h_4,h_5,h_6\), is the proper pencil domain.

If \(|F-F_0|\le R\) entrywise with a symmetric nonnegative radius matrix, then
\(\|F-F_0\|_2\le\|R\|_2\le\min(\|R\|_F,\|R\|_\infty)\).
Interval Cholesky of \(F_0-sI\), with a proved \(s\ge\|R\|_2\), certifies the entire hull. Applying this to \(F-\lambda H\) certifies the generalized lower bound. An arbitrary nonzero exact coefficient vector supplies an upper bound via its interval Rayleigh quotient; a float-generated vector is permissible here because it is subsequently treated as that exact binary vector, not assumed to be an eigenvector.

The raw output records positive shifted pivots on the independent span and a pencil lower bound above 1/1000. This certifies all **complex** linear combinations as well: the matrices are real symmetric and the quadratic form separates real and imaginary coefficient parts. Only the requested span, not every moment-null test, is covered. [FINITE_CELL][ARB_INTERVAL, recorded; PAPER audit]

### 2.5 Numerical transport, printed endpoints, and conservative guards

The claim “no float on the certificate path” is not literally correct. `cert.pack` and `assemble.read_ball` use floats with explicit radius padding. At the finite normal magnitudes present here, the factors \(2^{-50}|m|\), \(2^{-48}|m|\), and the radius inflations exceed the binary rounding error and the 20/25-digit decimal conversion error. Selection/precision floats are also present. These are not unprotected substitutions of a float value for a proof value.

A different issue is the two optimized packet error constants copied as radius-free decimals. `arb_get_str` guarantees a last-decimal-unit accuracy, not outward rounding when its radius is suppressed. To make the ledger independent of the direction of that final rounding, allow an extra **10^-18** in the printed `Ebase` and **10^-26** in `Ebasem`. These allowances greatly exceed a unit in their printed last places. They are documentary serialization guards, not fresh numerical estimates of the integrals.

These guards do not require rerunning the packet or enlarging its stored entry hulls. Section 3 proves 120 in place of 256. Keeping the originally computed uniform \(T_0\) and frequency estimates, this releases \(17/32\) of each Euler-tail row. In normalized entry units, the extra quadrature cost is at most \(2\delta\,10^{-18}\). The extra mass error is at most \(2\delta H_{ii}10^{-26}\). Using \(D_i\le2\pi H_{ii}\) in (6), the additional frequency cost is at most
\[
 2T_0\sqrt{H_{ii}H_{jj}}
 [2\sqrt{(2\pi)(2\delta)10^{-26}}+2\delta10^{-26}]
 <5\cdot10^{-12}\sqrt{H_{ii}H_{jj}}.
\]
The released Euler row exceeds \(4\cdot10^{-10}\sqrt{H_{ii}H_{jj}}\), using the recorded outward Euler enclosure. It pays both guards with strict slack. Thus the original entry hulls are conservative under this reallocated **proved** budget. Nothing about a sign was used in the reallocation. [FINITE_CELL][PAPER budget repair]

For future serialization retain the complete ball or explicitly round upward; do not rely on this special spare-budget argument. Likewise `abs_lower` must not be used as a general signed lower-endpoint function. Its use on already proved positive values in this run does not change their sign, but it would mislabel a negative interval in a general-purpose checker.

The safe exported statements are
\[
 \boxed{\mathcal F(h_4)>1/500,\qquad
   c^*F_3c\ge(1/1000)c^*H_3c\quad\forall c\in\mathbb C^3.}        \tag{11}
\]
A conservative human-readable scalar enclosure is
\([0.00343936,0.00357821]\).
For the pencil, use the rational lower threshold or round the reported lower endpoint down, never up to 0.00116. The high-precision decimals in the request remain reporting values, not newly re-executed directed outputs.

### 2.6 Exactly which inputs turn these numbers into source theorems

The certificate consumes: the exact profile/norm and Fourier convention; (3)--(9); outward scalar arithmetic and quadrature; the source identity proved in Section 4; its positive-square corollary; and the regularity extension in Section 4.6. No semilocal inverse, dropped mode, source spectral gap, RH assumption, or plant outcome enters (11).

The h4 result says nothing about the separately frozen exponential bump. The packet's scalar lower bound says nothing by itself about survival under a plant requiring a lower bound above \(\delta_M\), or about plant failure requiring an upper bound on the **full** margin. The failed four-independent-test certificate is not a negative direction.

## 3. Q2: independent proof of the uniform Mellin bound

**Theorem 1.** For all \(\beta\ge1\) and \(\xi\in\mathbb R\),
\[
 \boxed{|J(\beta,\xi)|\le120\,\beta^{-1/2}(1+\log\beta)
                  \le256\,\beta^{-1/2}(1+\log\beta).}             \tag{12}
\]
[ABSTRACT][PAPER]

**Proof.** Substitute \(y=\beta v\) and expand the cosine. Discard the unit-modulus factor \(\beta^{-i\xi}\). The amplitude is
\(b(y)=y^{-1/2}\log(\beta/y)\ge0\), decreasing on \((0,\beta]\), and the phases are \(\pm y+\xi\log y\). On \((0,1)\), absolute integration costs \(2\log\beta+4\).

Partition \([1,\beta]\) into dyadic intervals \([B,2B]\), truncating the last. If \(|\xi|<B/2\) or \(|\xi|>4B\), the phase derivative is monotone and has modulus at least 1/2. Integration by parts bounds every unweighted subinterval primitive by 8. Abel integration with the decreasing amplitude bounds the weighted integral by \(8B^{-1/2}\log\beta\). Their total is at most \(8(1-2^{-1/2})^{-1}\log\beta\).

There are at most four remaining dyadic intervals, since \(|\xi|/4\le B\le2|\xi|\). On each, \(|\phi''|\ge1/(8B)\). For a phase with second derivative of one sign and magnitude at least \(\lambda\), split where \(|\phi'|\le\sqrt\lambda\): its length is at most \(2/\sqrt\lambda\), and integration by parts on the two complements costs at most \(6/\sqrt\lambda\). Thus every primitive is at most \(8/\sqrt\lambda\). Here it is at most \(16\sqrt{2B}\); Abel integration costs at most \(16\sqrt2\log\beta\) per interval. Summing all pieces gives
\[
 |J|\le\beta^{-1/2}
 [4+(2+8/(1-2^{-1/2})+64\sqrt2)\log\beta]
 =\beta^{-1/2}[4+(18+72\sqrt2)\log\beta].
\]
Since \(18+72\sqrt2<120\), (12) follows. Averaging the two exponential integrals introduces no further factor. This also proves the old 256 bound **as written**. QED.

No uniform constant at most 8 is established by this proof. The observed maximum is not its substitute. Conversely, the formerly used constant 1 is genuinely false: (8) at \(\xi=0\) gives
\[
 \frac{|J(\beta,0)|\sqrt\beta}{1+\log\beta}
       \longrightarrow\Gamma(1/2)\cos(\pi/4)=\sqrt{\pi/2}>1.
\]
This is an asymptotic counterexample, not just a numerical objection. It does not damage certificates that used 256.

The same dyadic argument with amplitude \(y^{-1/2}\), and with extra fixed powers of \(\log(\beta/y)\), gives uniform bounds
\[
 |I(\beta,\xi)|\le120\beta^{-1/2},\qquad
 |\partial_\xi^kJ(\beta,\xi)|\le C_k\beta^{-1/2}(1+\log\beta)^{k+1}.
                                                                    \tag{13}
\]
For \(I\), also use the elementary bound 2. These bounds will justify the source series, not numerical asymptotic fitting.

## 4. Q3: complete tested source identification at cutoff one

This section is a new **PAPER** derivation of the analytic domain needed for RESONANCE (6). It uses the finite-Euler Fourier model, not positivity of the desired Weil form. All constants here may depend on the fixed finite set of places. No growing-prime uniformity is asserted.

### 4.1 The exact operators and their compression

Work on \(L^2(\mathbb R,dx)\) and transport to the physical half-line by
\((Vg)(u)=u^{-1/2}g(\log u)\). Let \(P=1_{(-\infty,0]}\), equivalently the physical cutoff \((0,1)\), and let \(E\) be zero extension from that physical interval. The archimedean Fourier involution has kernel \(2\cos(2\pi uv)\). For a fixed finite set of primes,
\[
 B_S=\prod_p(I-p^{-1/2}U_{\log p}),\qquad
 F_S=B_S(B_S^*)^{-1}F_\infty=(B_S^*)^{-1}F_\infty B_S^*.
                                                                    \tag{14}
\]
This is the multiplier/intertwining convention of [CCM23, (57)--(59)], transported to the stated log Hilbert space. It is not a unitary identification of \(B_S\) itself.

The generalized Mellin wave and its Fourier action are
\[
 f_\xi(u)=(2\pi)^{-1/2}u^{-1/2+i\xi},\qquad
 F_Sf_\xi=\gamma_S(\xi)f_{-\xi},
\]
\[
 \gamma_S(\xi)=\pi^{-i\xi}
 \frac{\Gamma(1/4+i\xi/2)}{\Gamma(1/4-i\xi/2)}
 \frac{b_S(-\xi)}{b_S(\xi)},\quad
 b_S(\xi)=\prod_p(1-p^{-1/2}e^{-i\xi\log p}).                      \tag{15}
\]
The cosine Mellin integral proves the archimedean factor, and each shift supplies its exponential. In log Fourier coordinates \(F_S=C_m\mathcal R\), with \(m(\xi)=\gamma_S(-\xi)\) and reflection \(\mathcal R\). On the real line \(|m|=1\) and \(m(-\xi)=\overline{m(\xi)}\), so \(F_S\) is a real self-adjoint involution. Its derivatives are polynomially bounded: this follows from the gamma quotient and its logarithmic derivatives, and the denominators of the fixed Euler factors are bounded away from zero.

For one prime,
\[
 F_p=\left[(1-r_p^2)\sum_{j\ge0}r_p^jU_{-j\log p}
                                      -r_pU_{\log p}\right]F_\infty.\tag{16}
\]
The series converges in operator norm. Each cutoff-compressed shifted cosine kernel is compact, hence \(A_S=E^*F_SE\) is compact. It is real and self-adjoint.

In fact \(\alpha_S=\|A_S\|<1\). Otherwise compactness gives a nonzero cutoff-supported \(f\) with \(F_Sf=\pm f\): equality of the compression norm leaves no component outside the cutoff. Both \(B_S^*\) and its inverse preserve the lower log half-line. Thus \(g=B_S^*f\ne0\) and \(F_\infty g=B_S^*F_Sf\) are compactly supported in physical space. The Fourier transform of a compactly supported \(L^2\), hence \(L^1\), function is entire. Its vanishing on the exterior interval forces it to vanish identically, a contradiction. Put \(Z_S=(I-A_S^2)^{-1}\).

### 4.2 Smoothing really supplies trace class

We record the needed elementary nuclearity argument rather than asserting that a bare semilocal trace exists. If \(k\) is Schwartz, the half-line Hankel operator with kernel \(1_{x\ge0}k(x+y)1_{y\ge0}\) is trace class. Choose a smooth function \(\chi\) equal to 1 on \([0,\infty)\) and 0 on \(( -\infty,-1]\). The kernel \(\chi(x)k(x+y)\chi(y)\) is Schwartz on \(\mathbb R^2\): on its support, bounded \(x+y\) forces bounded \(x,y\). A Schwartz-kernel operator is trace class, for example by factoring it through the inverse square of the harmonic oscillator; that inverse is trace class and applying the oscillator twice to the kernel remains bounded. Compressing back proves the assertion. This is also the mechanism of [CC20, Appendix D].

Let \(T_v\) be convolution by \(v\in\mathcal S(\mathbb R)\). Its off-diagonal blocks against \(P\), after reflection, are such Hankel operators. Therefore \([T_v,P]\) is trace class. Moreover \(PT_vF_SP\) is a half-line Hankel operator: \(\widehat v\,m\) is Schwartz. Consequently
\[
 T_vPF_SP=[T_v,P]F_SP+PT_vF_SP
\]
is trace class. These trace-norm bounds are continuous in finitely many Schwartz seminorms of \(v\), with fixed source-dependent constants.

Write \(Q_S=F_SPF_S\), let \(\mathsf S_S\) project onto \(\ker P\cap\ker Q_S\), and put
\[
 D_S=P+Q_S-I+\mathsf S_S.
\]
For \(W=(E,F_SE)\),
\[
 W^*W=\begin{pmatrix}I&A_S\\A_S&I\end{pmatrix},\qquad
 D_S=W\begin{pmatrix}-A_S^2Z_S&A_SZ_S\\A_SZ_S&-A_S^2Z_S\end{pmatrix}W^*.
                                                                    \tag{17}
\]
Indeed the orthogonal projection onto the closed range of \(W\) is \(W(W^*W)^{-1}W^*\); subtract it from \(P+Q_S=WW^*\). The block matrix in (17) factors through \(\operatorname{diag}(A_S,A_S)\). The preceding nuclearity result proves \(T_vEA_S\) trace class. Also \(T_vF_SEA_S=F_ST_{\check v}EA_S\), where \(\check v(x)=v(-x)\), is trace class. Hence **\(T_vD_S\) is trace class**, and in particular Hilbert--Schmidt. No assertion is made that untested \(D_S\) is Hilbert--Schmidt.

### 4.3 The arithmetic trace, with no subtraction of infinite traces

Set \(R_S=I-P-Q_S=C_mPC_m^*-P\). In unitary Fourier coordinates,
\[
 P(\xi,\eta)=\tfrac12\delta(\xi-\eta)
                         +\frac{i}{2\pi}\operatorname{pv}\frac1{\xi-\eta}.
\]
The delta term cancels in \(R_S\). Thus the kernel of \(T_vR_ST_v^*\) is
\[
 \widehat v(\xi)\overline{\widehat v(\eta)}\frac{i}{2\pi}
          \frac{m(\xi)\overline{m(\eta)}-1}{\xi-\eta}.             \tag{18}
\]
The divided difference extends smoothly across the diagonal. Its derivatives have polynomial bounds, so (18) is a Schwartz kernel. Its diagonal is
\(|\widehat v(\xi)|^2 i m'(\xi)\overline{m(\xi)}/(2\pi)\).
Differentiating (15), with the reflection sign retained, gives
\[
 i m'\overline m=q_S,
\quad q_S=\Re\psi(1/4+i\xi/2)-\log\pi
            -2\sum_p\log p\sum_{j\ge1}p^{-j/2}\cos(j\xi\log p).
\]
Therefore
\[
 \boxed{\operatorname{Tr}(T_vR_ST_v^*)
       =\frac1{2\pi}\int |\widehat v|^2q_S=:L_S(v).}             \tag{19}
\]
This computes the trace of the **difference operator after testing**, never the difference of two infinite projection traces.

Since \(\mathsf S_S=R_S+D_S\), its tested sandwich is positive and trace class, and
\[
 \boxed{n_S(v)-L_S(v)=\operatorname{Tr}(T_vD_ST_v^*),\qquad
 n_S(v)=\|T_v\mathsf S_S\|_{HS}^2.}                              \tag{20}
\]
Fourier inversion of \(q_S\) is precisely the archived geometric local form: its Euler term is \(-2\sum_{p,j}(\log p)p^{-j/2}C_v(j\log p)\). On the present pole-null two-lobe class the pole terms vanish, and all prime-power correlations except the one at \(\log2\) vanish by support. Thus this \(L_2(v_h)\) is the actual Weil form on that class, not an auxiliary positive form. The strict inequality \(a+2\delta<\log3\) supplies the outer support guard.

### 4.4 The Mellin integrals and the cross-term trace

For one prime define
\[
 \beta_{-1}=2\pi/p,\quad c_{-1}=-1/p,\qquad
 \beta_j=2\pi p^j,\quad c_j=1-1/p\quad(j\ge0).
\]
Transporting (16) to physical coordinates gives the distributional kernel \(2\sum c_j\cos(\beta_juv)\). Define
\[
 I(\beta,\xi)=\int_0^1v^{-1/2+i\xi}\cos(\beta v)dv,
\quad J(\beta,\xi)=\int_0^1(-\log v)v^{-1/2+i\xi}\cos(\beta v)dv.
\]
Each integral is absolutely convergent. The legitimate source vector and scalar are
\[
 u_S(\xi)(u)=\sqrt{2/\pi}\sum_{j\ge-1}c_jI(\beta_ju,\xi),
\qquad
 t_S(\xi)=\frac1\pi\sum_{j\ge-1}c_jJ(\beta_j,-\xi).              \tag{21}
\]
The bounds (12)--(13), together with \(|I|\le2\), imply
\[
 \|I(\beta\,\cdot,\xi)\|_{L^2(0,1)}
       \le\beta^{-1/2}\sqrt{4+120^2\log\beta}\quad(\beta\ge1).
\]
Thus the vector series in (21) converges in \(L^2(0,1)\), uniformly on compact frequency sets; the scalar series converges absolutely and locally uniformly. Extra logarithmic powers justify any fixed number of local frequency derivatives by the same dyadic argument. Small fixed beta terms cause no problem. The geometric Euler weights in physical kernel coefficients are recovered by these oscillatory estimates, not by summing an absolute lacunary cosine kernel.

This vector represents the actual operator, not merely a definition with the same notation. For every cutoff vector \(z\), the finite-kernel identity is \(\mathscr F E A^{[J]}z(\xi)=\langle u^{[J]}(\xi),z\rangle\). Operator-norm convergence gives convergence of its left side in \(L^2(d\xi)\); the locally uniform vector convergence gives convergence of its right side against compact frequency tests. The two limits agree. This identifies \(u_S\) as the source Fourier-evaluation vector almost everywhere, with the specified continuous representative. It does not require an exchange of two uncontrolled cutoffs on the singular wave.

For a finite kernel sum, ordinary double integration gives
\[
 \langle f_\xi,A^{[J]}f_{-\xi}\rangle
       =\frac1\pi\sum_{j=-1}^Jc_jJ(\beta_j,-\xi),
\]
because \(\int_0^1\int_0^1F(uv)dudv=\int_0^1(-\log v)F(v)dv\).
This is a Mellin integral, **not** a Hilbert inner product between two assumed \(L^2\) cutoff waves. The notation is only shorthand for the displayed convergent integral.

Here is a precise limit procedure for the trace. First replace \(\widehat v\) by a smooth compact-frequency cutoff of it and take a finite Euler kernel. The Fourier kernels are then smooth on a compact square. Their diagonal traces follow by an absolutely convergent smooth-kernel expansion. The two cross terms of
\[
 PQ_S+Q_SP=W\begin{pmatrix}0&A_S\\ A_S&0\end{pmatrix}W^*
\]
use the coefficients \(f_\xi|_{(0,1)}\) and \(\gamma_S(\xi)f_{-\xi}|_{(0,1)}\), and yield \(2\Re(\gamma_St_S)\).

Pass to the infinite Euler sum next. In log coordinates, each fixed derivative of its multiplier tail is bounded by a geometric tail times a polynomial in the shift index, times the fixed archimedean multiplier seminorm. The nuclearity bounds of Section 4.2 therefore give trace-norm convergence of the tested linear term. The scalar side converges by (12) and (21). Finally remove the frequency cutoff: the tests converge in Schwartz seminorms, the trace-norm bounds are continuous in those seminorms, and the scalar integrals have an integrable Schwartz majorant. Consequently
\[
 \boxed{\operatorname{Tr}(T_v(PQ_S+Q_SP)T_v^*)
          =\int|\widehat v(\xi)|^2\ell_S(\xi)d\xi,
      \qquad\ell_S=2\Re(\gamma_St_S).}                          \tag{22}
\]
This passage neither subtracts bare traces nor uses an unproved eigen-expansion of the Mellin wave.

### 4.5 The full density formula and the positive square

In (17), split \(AZ=A+A^3Z\). The linear term is (22). The remaining terms factor through the actual \(L^2\) vector \(u_S(\xi)\). Hilbert-space-valued Plancherel gives their traces: their integrals are absolutely convergent since \(Z,AZ\) are bounded, \(u_S\) has the locally uniform bounds above, and \(\widehat v\) is Schwartz. The reality of \(A_S\) identifies the opposite-frequency vector with \(\overline{u_S}\). Thus
\[
 \boxed{
 d_S(\xi)=2\Re\{\gamma_S(\xi)
 [t_S(\xi)+\langle u_S(\xi),A_SZ_S\overline{u_S(\xi)}\rangle]\}
                 -2\langle u_S(\xi),Z_Su_S(\xi)\rangle,}         \tag{23}
\]
\[
 n_S(v)-L_S(v)=\int|\widehat v|^2d_S.
\]
All scalar functions in (23) are continuous. Equality as tested distributions therefore fixes their continuous representatives, not arbitrary values on a null set. This proves RESONANCE (6) on the requested source and domain. The analogous fixed finite-S argument has finitely many multi-indices and convergent products of the same geometric tails; no uniformity in S is inferred.

For two orthogonal projections, \(D=P+Q-I+S_0\), with \(S_0\) their common-kernel projection, satisfies
\[
 D+D^2=PQ+QP.
\]
Indeed, with \(K=P+Q\), \(KS_0=S_0K=0\) and
\(D^2=K^2-2K+I-S_0\). Combining this identity with (20)--(22) gives
\[
 \boxed{\mathfrak m(h)=\mathcal F(h)+\|T_{v_h}D_2\|_{HS}^2.}     \tag{24}
\]
The squared norm is finite by Section 4.2. This is an independent operator proof of the floor and packet ordering, not a numerical mode-sign argument.

As a domain falsifier, replacing the true contraction by an arbitrary matrix outside the unit ball destroys the resolvent floor. For example \(A=2,\gamma=1,u=2i,t=-2\) in the algebraic right side of (23) gives \(d=4\), whereas \(\ell=-4\). Such a substitution is not a pair-of-projections source. It explains why noncontractive Euler truncations and mode deletion cannot replace the preceding trace proof. [ABSTRACT][PAPER; THEOREM_SHAPE only]

### 4.6 Polynomial profiles and the literal smooth class

The zero extension of \(\eta_4=(1-(x/\delta)^2)^4\) has its first four boundary traces through order three equal to zero. It belongs to \(H^4\); \(h_4\in H^2\), not \(C_c^\infty(I)\). Smooth inward approximations to \(\eta_4\) converge in \(H^4\). Applying \(\partial^2-1/4\) gives approximants to \(h_4\) in \(H^2\), with both moments zero exactly. The same construction applies to every polynomial in the certified packet.

The scalar multiplier \(\ell_2\) and the density correction \(d_2\) are bounded. The arithmetic symbol grows only logarithmically, and \(k_2=q_2/(2\pi)+d_2\). Consequently the separate \(L_2\) and \(n_2\) integrals are continuous under these \(H^2\) approximations. Equations (20), (23), and (24) extend to the polynomial profiles. This pays the regularity and open-support debt rather than silently declaring a piecewise polynomial smooth.

The numerical floors in (11), combined with (24), now give actual source positivity for those extended profiles. A sufficiently close smooth moment-null approximation retains a strictly positive lower bound; Section 5.2 makes this quantitative. [ABSTRACT][PAPER; FINITE_CELL/ARB_INTERVAL for the seed bounds]

## 5. Q4: the class, the sufficient object, and the next discriminator

### 5.1 What is proved and what is not

On the closed moment-null subspace \(\mathcal H_{00}\subset L^2(I)\), set
\[
 b(\xi)=(1-\cos(a\xi))\ell_2(\xi),\quad
 \mathcal T=-2\pi P_{00}E_I^*\mathscr F^{-1}M_b\mathscr F E_IP_{00}.
                                                                    \tag{25}
\]
Then \(\langle h,\mathcal Th\rangle=H\mathcal F(h)\). The operator is self-adjoint and compact: compact-frequency truncations have square-integrable kernels on \(I^2\), and the multiplier tail tends to zero. The latter follows directly from the low/high Mellin splitting, or from (32) below.

The full class statement \(\mathcal T\succeq0\) is not established by the three-dimensional certificate. Nor does the sign change of \(\ell_2\) establish its negation. The request's phrase “as inf = 0 on the class demands” is also too strong before that sign is proved. Compactness on the infinite-dimensional moment-null space gives \(\inf\operatorname{Spec}\mathcal T\le0\); if positivity is proved, the infimum is exactly zero. It may otherwise be negative. Declining positive packet floors do not determine which case holds. A useful exact counterexample to that inference is the multiplier \(1/2+\cos(a\xi)\): it changes sign, but for every test supported in an interval shorter than \(a\) its quadratic integral is \(\pi\|h\|^2>0\), because the cosine autocorrelation vanishes. Compression matters. [ABSTRACT][PAPER]

A whole-line scalar factorization of \(-b\) as a modulus square cannot work: \(q_2(0)<0\), while \(k_2\ge0\) implies \(d_2(0)>0\); (24)'s pointwise version gives \(\ell_2(0)\ge d_2(0)>0\). By continuity, \(-b<0\) on a punctured neighborhood of zero. This refutes only the **uncompressed pointwise modulus-square** representation, not a factorization after moment-null compression.

Likewise, writing \(\mathcal T^{1/2}\) before proving positivity would put the desired sign into the definition. A generic Fejer--Riesz or Herglotz slogan supplies neither a source factor nor a positivity proof on this compressed class.

### 5.2 A genuine infinite-dimensional positive subclass is now available

This result was only conditional in SCALARFLOOR; the certified seed now supplies its missing input. Exact periodization gives the operator bound
\[
 \|\mathcal T\|\le2\pi\|\ell_2\|_\infty\le4\pi T_0<176.
\]
Let \(h_*=h_4/\sqrt{H_4}\). Equation (11) gives
\(\langle h_*,\mathcal Th_*\rangle\ge1/500\).
For every moment-null \(h\) with \(\|h-h_*\|\le\varepsilon\),
\[
 \mathcal F(h)\ge
 \frac{1/500-176(2\varepsilon+\varepsilon^2)}{(1+\varepsilon)^2}.
                                                                    \tag{26}
\]
This follows by expanding the quadratic form and bounding both cross terms. At \(\varepsilon=10^{-6}\), the right side exceeds **1/1000**. Hence
\[
 \boxed{\mathfrak m(h)\ge\mathcal F(h)>1/1000
 \quad\text{for every }h\in\mathcal H_{00}^{\rm sm}(I)
                  \text{ with }\|h-h_*\|\le10^{-6}.}             \tag{27}
\]
The class is nonempty and infinite-dimensional. Smooth functions are dense in the closed moment-null subspace: approximate smoothly and correct the two small moments using two fixed smooth functions with independent moment vectors. Section 4.6 also constructs direct smooth approximants of this particular seed. A small open ball about one such approximant contains infinitely many independent perturbations. This is an explicit neighborhood, not the unknown positive spectral subspace and not a linear infinite-dimensional space with a uniform coercivity claim.

Equation (27) is a restricted prime-carrying positivity result obtained from an audited finite seed and continuity. It is **not** the whole R1-minus class, and no historical “first” claim is made. [ABSTRACT][PAPER using the ratified finite certificate]

### 5.3 The sufficient factorization object, with the unknown kept visible

The exact source-weighted maps are
\[
 V_+h=\sqrt{(1-\cos(a\xi))(-\ell_2(\xi))_+}\,\widehat h(\xi),
 \quad
 V_-h=\sqrt{(1-\cos(a\xi))(\ell_2(\xi))_+}\,\widehat h(\xi).
\]
They retain the support and moment-null domain, and
\[
 H\mathcal F(h)=\|V_+h\|^2-\|V_-h\|^2.
\]
An explicit source-defined contraction \(C\), satisfying
\[
 \boxed{V_-=CV_+\quad\text{on }\mathcal H_{00},\qquad C^*C\le I,} \tag{28}
\]
would give the requested representation
\[
 H\mathcal F(h)=\|(I-C^*C)^{1/2}V_+h\|^2,
\]
and (24) supplies the second square for the full margin.

This is a precise sufficient object, but its source formula and contraction estimate have **not** been constructed here. Merely defining \(C(V_+h)=V_-h\) and assuming it is contractive would be circular. The statement is retained as a factorization target, not reported as a whole-class sum of squares. A negative scalar direction would kill (28) on that class while leaving the positive correction in (24) available for the full margin.

There is already an exact sum-of-squares representation on the certified finite span: the positive matrix \(F_3\) has a Cholesky factor, and the packet's complete margin equals that finite quadratic square plus the source Hilbert--Schmidt square. Its existence is justified by the proved interval lower bound, not used to obtain that bound. It cannot be extrapolated to the infinite complement.

### 5.4 An explicit finite-compression error theorem

Here is an executable complement bound, including its limitation. Let \(\Pi_N\) project onto
\(\operatorname{span}\{P_{00}p:\deg p\le N\}\subset\mathcal H_{00}\).
For \(g\perp\operatorname{ran}\Pi_N\), the first \(N+1\) polynomial moments vanish. Taylor's remainder gives, on \(|\xi|\le X\),
\[
 |\widehat g(\xi)|\le A_N(X)\|g\|,
 \qquad A_N(X)=\sqrt{2\delta}\,e^{\delta X}
                         \frac{(\delta X)^{N+1}}{(N+1)!}.
\]
Put \(M_X=\sup_{|\xi|\le X}|b(\xi)|\), \(B_X=\sup_{|\xi|>X}|b(\xi)|\). Plancherel and the preceding evaluation bound imply
\[
 \boxed{\|\mathcal T-\Pi_N\mathcal T\Pi_N\|
       \le\epsilon_{N,X}:=
          4\sqrt{\pi X}\,M_X A_N(X)+4\pi B_X.}                  \tag{29}
\]
Indeed \(\|\mathscr FE_Ig\|_{L^2(-X,X)}\le\sqrt{X/\pi}A_N\|g\|\). Apply the multiplier and the outside bound to \(\mathcal T(I-\Pi_N)\); self-adjointness bounds the other off-compression term by the same norm. This proves (29), including the factor two.

An explicit tail supplier, not a fitted exponent, is available. Two integrations by parts after \(v=e^{-x}\), with amplitude \(xe^{-x/2}\), give
\[
 |J(\beta,\xi)|\le128/|\xi|^2
       \quad(|\xi|\ge2,\ \beta\le|\xi|/2).                     \tag{30}
\]
For detail, the reciprocal phase derivative has bounds \(2/T,2/T,6/T\) through its second derivative, \(T=|\xi|\). The boundary costs \(4/T^2\), and the integrals cost
\([4\|f''\|_1+12\|f'\|_1+16\|f\|_1]/T^2\), with
\(\|f\|_1=4,\|f'\|_1\le4,\|f''\|_1\le3\), giving 128.

For \(X\ge4\pi\), let \(J_X\) be the largest integer with \(\beta_{J_X}\le X/2\). Combining (12) and (30), uniformly for \(|\xi|\ge X\), gives
\[
 |\ell_2(\xi)|\le L_X:=\frac1\pi\left[
 \frac{128(J_X+2)}{X^2}+
 \frac{120r^{J_X+1}}{\sqrt{2\pi}}
 \left(\frac{1+\log\beta_{J_X+1}}{1-r}+\frac{ar}{(1-r)^2}\right)
 \right]\longrightarrow0.                                      \tag{31}
\]
Thus \(B_X\le2L_X\), and one may use \(M_X\le4T_0\) or a sharper certified compact-frequency bound. These constants are deliberately conservative. They prove convergence of a finite approximation; they do not promise a cheap exact-zero decision. [ABSTRACT][PAPER]

A finite interval spectral enclosure plus (29) yields
\[
 \inf\operatorname{Spec}\mathcal T
       \ge\min\{0,\lambda_{\min}(\Pi_N\mathcal T\Pi_N)
                                      \text{ lower endpoint}\}-\epsilon_{N,X}.
                                                                    \tag{32}
\]
The zero in (32) is mandatory because the finite compression is extended by zero on an infinite-dimensional complement.

### 5.5 Why unsigned smallness is not the missing positivity theorem

For every positive finite compression and every \(\epsilon>0\), one may add \(-\epsilon\langle e,\cdot\rangle e\) on an untested orthogonal direction. This compact self-adjoint operator has the same tested compression, satisfies the same norm-error allowance, and has a negative direction. Therefore finite positivity plus a nonzero unsigned complement bound cannot certify whole-class positivity. This is an exact theorem-shape obstruction, not a negative direction for our source. [ABSTRACT][PAPER]

A **signed** complement certificate is different. With the actual block decomposition
\[
 \mathcal T=\begin{pmatrix}A&B\\B^*&C_0\end{pmatrix},\quad A\succ0,
\]
the exact sufficient-and-necessary remainder is
\[
 \boxed{C_0-B^*A^{-1}B\succeq0.}                                \tag{33}
\]
Completing the square gives
\[
 \langle(x,y),\mathcal T(x,y)\rangle
 =\|A^{1/2}x+A^{-1/2}By\|^2+
        \langle y,(C_0-B^*A^{-1}B)y\rangle.
\]
For a merely semidefinite head the corresponding range/pseudoinverse condition must also be proved; it cannot be omitted. No source supplier for the nonnegative infinite operator in (33) has been obtained here. A whole-class sum of positive terms still requires a source construction, not an unsigned error estimate. An analytic proof that every member of a fixed dense nested compression family is PSD would also suffice by continuity. It must quantify all dimensions; finitely many computed packets do not supply that proof. Neither (28) nor (33) is declared the only admissible interface.

### 5.6 The cheapest decisive computation

Use the already validated **scalar** evaluator, not the ill-conditioned semilocal eigensolver. First include odd tests: the certified packet is entirely even, while the requested class is complex and has both parities. Since \(b\) is real and even, parity blocks decouple exactly.

A bounded first packet is
\[
 h_j=(\partial^2-1/4)[\eta_4(x)P_j(x/\delta)],\qquad 0\le j\le7,
\]
with zero extension, exact Gram/rank reduction, and the regularity extension of Section 4.6. Its even and odd blocks should be certified separately. Preselect this packet before looking at its spectrum. A rational coefficient vector with a strictly negative **upper** enclosure of its scalar quadratic value refutes scalar positivity on the class. It does not yet refute the full margin; then evaluate a positive-correction level from [SF1, Theorem 5] or an upper bound for the complete value.

Positive packet results give only packet results. To quantify proximity to the whole operator, use the projected-polynomial compression and (29)--(32), recording \(N,X,M_X,B_X\). To announce whole-class positivity, supply the signed complement (33), or an explicit contraction in (28). A norm tail alone is not that supplier. The rule may find a negative witness in finite time whenever one exists and dense packets are refined with certified errors; there is no symmetric guarantee of a finite-time PSD decision at the compact operator's zero boundary.

The **DISCRIMINATOR** is the signed upper value on the declared test vector; for a zero-straddling whole-operator enclosure, it is the signed Schur complement, not the smallest displayed positive finite eigenvalue. This is a computation specification for a subsequent authorized transaction, not a numerical run initiated here.

## 6. Strongest attack, dependency record, and representations

**Strongest attack.** “A few positive scalar tests and a positive square do not prove the class sign.” Correct. This verdict closes the analytic identity and ratifies the finite thresholds; it does not assert either a global factorization or a nonnegative full complement. The new infinite-dimensional neighborhood (27) is explicitly local in test space.

**DOWNSTREAM_CONSUMER:** `published_Weil_criterion_on_all_complex_compact_smooth_tests`.

**ACTUAL_CONSUMER_REQUIREMENT:** nonnegativity of the actual Weil form on that full class. The fixed short two-lobe class is an intermediate restricted class, not an exhaustion theorem.

**ORIGINAL_REQUESTED_OBJECT:** a certified finite scalar/packet floor, source-domain closure, and a construction making the class sign manifest.

**ORIGINAL_OBJECT_IS:** `NOT_NECESSARY` for the terminal consumer. Separate scalar positivity is sufficient, not necessary, even for the restricted margin because (24) contains a nonnegative square.

**KNOWN_WEAKER_INTERFACES:** the complete margin certified without separate scalar positivity; an inverse-free positive-correction hierarchy on a declared packet; a signed full-complement inequality; or direct positivity of the unchanged full Weil form. Every implication retains its test class. Restricted success does not discharge the terminal all-test quantifier.

**FAILURE_TYPE:** `NO_DERIVATION` for full-class contraction/signed-complement positivity; `COUNTEREXAMPLE` for inferring PSD from a finite positive compression and unsigned tail; `INCOMPATIBILITY` for a four-dimensional invertible pencil on the dependent packet and for a pointwise square of the negative whole-line multiplier.

**EPISTEMIC_STATUS:** the remaining class sign is `RESEARCH_DEBT`. Only the explicitly refuted generic theorem shapes are mathematically dead at their stated scope. No route-family death is claimed.

**NOVELTY_AXIS:** source trace regularization plus exact finite positivity, followed by a signed rather than unsigned complement problem. Historical originality is not asserted.

**REOPEN_TRIGGER:** a certified negative smooth scalar direction, a proved source contraction (28), or a signed full complement (33). For the frozen bump's separate event, a certificate for that exact bump. For a high-digit machine endpoint, the complete directed serialization receipt, not a radius-free decimal.

| Representation | Preserves | Decisive output | Ordinal kill-power / cost |
|---|---|---|---|
| Scalar compressed kernel with exact moments, both parity blocks, and (29) | full frequency multiplier, support, normalization, complex coefficients | finite negative witness or quantified lower enclosure; PSD still needs signed complement | 9/10 / 4/10 for the first packet |
| Source positive-correction hierarchy plus Euler-Gram full residual | actual complete margin rather than only its sufficient scalar floor | a lower certificate after a negative scalar floor, or a genuine upper counterexample | 9/10 / 6/10 |
| Explicit weighted-frame contraction (28) | joint positive/negative frequency geometry and exact compression | whole-class sum of squares if its norm is proved | 10/10 / 9/10; presently research debt |

The cost figures are ordinal, not measured runtimes. No larger computation is authorized by them.

## 7. Prediction ledger

Probabilities and events are not edited. A result proved in this paper audit is not a Lean gate or a rerun of the interval calculation.

| Frozen observer prediction | p | Fate |
|---|---:|---|
| P_CERT_RATIFIED | 0.80 | CONFIRMED for the h4 certificate at its robust 1/500 threshold. Holomorphic continuation and padded transport are made explicit; radius-free last digits are not treated as directed endpoints. |
| P_THM4_256_SURVIVES | 0.90 | CONFIRMED_ON_PAPER; the same displayed constants actually permit 120. |
| P_SOURCE_IDENTITY_6_CLOSED | 0.45 | CONFIRMED_ON_PAPER by Section 4, with smoothing before trace and no L2 assumption on the cutoff Mellin wave. Independent review remains appropriate. |
| P_PACKET_PSD_CERTIFIED | 0.85 | CONFIRMED on the span of the four requested tests, equivalently their rank-three quotient; the lower threshold is greater than 1/1000. No invertible four-coordinate pencil is claimed. |
| P_CLASS_SUM_OF_SQUARES | 0.25 | NOT_ACHIEVED. A finite-span square and an infinite-dimensional positive neighborhood are obtained, not a whole-class construction. Mathematical impossibility of a compressed factorization is not asserted. |
| P_CLASS_DECISIVE_TEST_IS_FINITE_PACKET_PLUS_COMPLEMENT | 0.60 | CONFIRMED_WITH_DIRECTION_GUARD: the proposed computation is a parity-complete certified packet plus explicit complement control; a positive decision specifically requires a signed complement. Negative packet detection does not require one. |

### Earlier SCALARFLOOR registrations

| Frozen judge registration | p | Fate |
|---|---:|---|
| P_SF_SQUARE_AND_PACKET_IDENTITY_SURVIVES | 0.97 | CONFIRMED_ON_PAPER, now with the source trace domain proved in Section 4. |
| P_SF_BSTAR_GAP_AND_GRAM_TRANSFER_SURVIVES | 0.90 | RETAINED; not rescored from the new interval values, which do not test that separate representation. The source multiplier/isomorphism was checked. |
| P_SF_EXPLICIT_J_MAJORANT_SURVIVES | 0.91 | CONFIRMED_ON_PAPER by Theorem 1. |
| P_SF_H4_SCALAR_CERTIFICATE_POSITIVE | 0.75 | CONFIRMED by the pinned inverse-free certificate and the present budget/source audit, at the declared 1/500 threshold. |
| P_SF_POLYNOMIAL_LOWER_HIERARCHY_SURVIVES | 0.97 | CONFIRMED_ON_PAPER: the positive geometric-series identities in [SF1, (40)--(47)] agree with (24); numerical c200 agreement is not the proof. |
| P_SF_OPERATOR_FLOOR_REVIEW_SURVIVES | 0.99 | CONFIRMED_ON_PAPER for the source floor and packet ordering. |
| P_SF_IMAGE_GRAM_STABILIZATION_SURVIVES | 0.92 | RETAINED at its previous paper status; no new evaluation of that Gram construction is claimed. |
| P_SF_FROZEN_FULL_SCALAR_CERT_POSITIVE | 0.70 | PENDING_NOT_RUN. h4 is a different profile and does not decide this forecast. |

The earlier PHASEPROOF frozen-bump forecast likewise is not closed by substituting h4. No earlier artifact or score is rewritten.

The local registrations made after reading the request and initial scripts, but before this closeout, were `P_CF_TESTED_TRACE_DOMAIN_CLOSES` (0.78), `P_CF_PACKET_CERTIFICATE_SURVIVES_STATIC_AUDIT` (0.75), and `P_CF_ABSOLUTE_COMPLEMENT_BOUND_NOT_SUFFICIENT` (0.99). The three anticipated outcomes are supplied by Sections 4, 2, and 5.5 respectively. These were not blind predictions preceding the supplied diagnostics, and self-checking is not an independent acceptance gate.

New prospective registrations, for future independent checking:
```yaml
P_CF_SOURCE_NUCLEARITY_AND_MELLIN_LIMIT_SURVIVES:
  probability: 0.91
  event: independent_paper_review_accepts_14_through_24_on_the_same_source_domain
  fate: PENDING
P_CF_CONSTANT_120_SURVIVES:
  probability: 0.97
  event: independent_paper_review_accepts_12_and_the_serialization_budget_reallocation
  fate: PENDING
P_CF_FIRST_ODD_PACKET_HAS_NO_CERTIFIED_NEGATIVE_DIRECTION:
  probability: 0.60
  event: the_predeclared_j_1_3_5_7_odd_packet_has_nonnegative_certified_scalar_matrix
  fate: PENDING_NO_RUN
```

## 8. Exactly one CODEX DIRECTIVE and closeout

**Target:** construct and independently check the parity-complete eight-test scalar packet of Section 5.6, with the same source and full interval ledger. The first subcheck is the source trace proof in Section 4; return the first exact failure if it does not survive. Do not replace it by an empirical density comparison.

**Inputs:** the request pin; the already committed scalar evaluator and exact packet Gram machinery; equations (3)--(13), (24), and (29)--(33). Serialize all error constants as full balls or directed upper endpoints. Preserve the existing test/profile definitions and record the regularity extension.

**Success condition:** a declared rational coefficient vector with a strict negative upper scalar enclosure, or certified even/odd packet PSD with exact physical Gram and an explicit statement that the whole complement is still unsigned. The latter is finite progress, not a class proof. A subsequent class-PASS requires a signed source theorem, such as (28), (33), or an analytic all-dimensions compression theorem, not merely a small value of (29).

**Failure codes:** `CLASSFLOOR_SOURCE_TRACE_DOMAIN_GAP`; `CLASSFLOOR_INTERVAL_SERIALIZATION_GAP`; `CLASSFLOOR_SCALAR_NEGATIVE_DIRECTION_NOT_FULL_MARGIN`; `CLASSFLOOR_UNSIGNED_COMPLEMENT_ZERO_STRADDLE`. In a negative scalar case keep the positive correction (24) or [SF1]'s monotone hierarchy; failure of the sufficient floor is not failure of the actual margin.

**Execution boundary:** this verdict initiates no numerical process and writes no Lean source. The observer must authorize the subsequent bounded run. No lake command or axiom profile is applicable to this document-only transaction.

What became smaller: the numerical certificate no longer depends on an unproved tested Mellin-wave identity; the dependent packet has its correct quotient; the remaining whole-class question is separated from an explicit approximation error and from finite positivity. An actual infinite-dimensional neighborhood follows from the seed. What did not become smaller: the global all-test Weil obligation is not discharged.

Do not repeat: four-dimensional inversion of the rank-three Gram; upward rounding of lower bounds; a modulus-square continuation using literal complex `Re`; exact-zero inference from a near-zero finite spectrum; a positive compression plus unsigned tail as whole-class PSD; or replacement of the frozen-bump forecast by h4.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 5
  CURRENT_SMALLEST_GAP: signed_complement_or_explicit_frame_contraction_for_the_same_moment_null_class
  FINITE_RESULT: scalar_seed_and_rank_three_packet_ratified
  SOURCE_DOMAIN_RESULT: tested_trace_identity_and_Mellin_density_PAPER_proof
  CLASS_RESULT: positive_seed_neighborhood_not_whole_class
  NEXT_CHEAPEST_DECISIVE_TEST: parity_complete_scalar_packet_with_signed_upper_witness_gate
  ZERO_CONSISTENT_DISCRIMINATOR: actual_signed_Schur_complement_not_unsigned_norm_tail
  MEMORY:
    target: REQ-2026-09-07-CLASSFLOOR
    status: PROGRESS
    invariant_learned: smoothing_precedes_trace_and_compact_PSD_has_a_zero_boundary
    forbidden_future_move: infer_whole_class_PSD_from_a_positive_finite_head_and_small_unsigned_tail
    remaining_unknown: full_class_scalar_or_complete_margin_sign
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CLASS_FLOOR_REPRESENTATION_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_BLOB_HASHES: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_CLAIM
  COMMIT_AND_READBACK_BLOB: returned_in_publication_receipt
  READBACK_EFFECT: publication_verification_only
```

The verdict is one document. The request, prior verdicts, scripts, queue, predictions in old artifacts, and route state remain unchanged. New analytic proofs are PAPER and await independent review; reviewing a recorded Arb certificate does not mean its computation was rerun here.
