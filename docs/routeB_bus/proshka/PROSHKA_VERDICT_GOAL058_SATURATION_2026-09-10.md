# STATUS: TRY_BESSEL_POISSON_AFFINE_SATURATION
```yaml
OPERATIVE_CLASS: TRY_BESSEL_POISSON_AFFINE_SATURATION
PRIMARY_COUNT: 1
REQUEST_ID: REQ-2026-09-10-SATURATION
BOUNDARY_ID: GOAL058_FULL_WINDOW_AFFINE_SATURATION_AFTER_DENSITY
RESULT:
  Q1: PROOF_CANDIDATE_COMPLETE
  Q2: PROOF_CANDIDATE_COMPLETE
  Q3: PROOF_CANDIDATE_COMPLETE
  OVERALL: PROOF_CANDIDATE_COMPLETE
VERIFIER: PAPER
SCOPE: COFINAL_FAMILY
T_SQUARED_RATE_PROVED: true
LOWER_SIGN_PROVED: false
SOURCE_FAMILY_TRANSFER_VERIFIED: true
INDEPENDENT_CHECK_OF_THIS_NEW_PROOF: PENDING
LEAN_VERIFIED: false
PX_RH_CLAIM: NOT_MADE
REQUEST_LOCK:
  COMMIT: 6d8f7fac4b0973aef974025eda960b5af3babe75
  BLOB: 8233ea0deab7eb8b7f5f0f4ef862e09636c698e8
  SHA256: 211cf7e894c59c289ee017e8e20b16ee4766335bd9a7c79a9c2a0c0613c85c79
  BYTES: 13970
  LINES: 84
  FINAL_LF: true
  ATTACHMENT_HASHES_RECOMPUTED: true
  EXACT_COMMIT_CONNECTOR_READ: true
SOURCE_BASE: 57df552a4a12c7e557d0be2938e05c09060aa2e2
BOOTSTRAP_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
SHELF_VERIFICATION:
  PINNED_GIT_BLOBS_MATCH: 5
  FULL_SHA256_RECOMPUTED_MATCH: 4
  SCHUR_FULL_SHA256_RECOMPUTATION: NOT_COMPLETED_THIS_BATCH
  LIMITATION: section_0_2
PHASE_ID: PHASE_GOAL058_G1_G3_COFINAL_GROUND_TRACKING_2026_08_13
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SECOND_EXPRESSION
SOURCE_OBJECT_FAMILY_ID: CANONICAL_TEST_SIGNED_DIRICHLET_FORM
TERMINAL_CONSUMER_ID: published_Weil_criterion_on_all_complex_compact_smooth_tests
CONVENTION_LOCK_ID: GOAL058_COORD_MINUS_LZ_OVER_2PI_ETA_NORMALIZED
FIXED_WITNESSES:
  FULL_SPACE_MU: 57
  FULL_SPACE_K: 1408*pi^2*I*Dstar^2/k0^4
  SHELL_M: 2*K
  SHELL_NU: 57
  A0: least_integer_n_ge_1_with_q_a_ge_sqrt_I_for_every_real_a_ge_n
  A0_EXISTENCE: proved_by_q_a_tending_to_2_sqrt_I
  NUMERICAL_A0: NOT_COMPUTED
  DEGREE_GROWTH_RATE: NOT_CLAIMED
FIRST_INCORRECT_ASSERTION_L1_L5: NONE_FOUND
FIRST_FAILURE:
  Q1: NONE_REMAINING
  Q2_INITIAL_ATTEMPT: uncalibrated_Poisson_sum_is_not_in_E
  Q2_REPAIR: exact_zero_value_and_zero_mass_calibration_before_theta_summation
  Q2_FINAL: NONE_IDENTIFIED_IN_SUBMITTED_PAPER_PROOF
  Q3: NONE_REMAINING
PREDICTION_FATES:
  P1: CONFIRMED
  P2: CONFIRMED
  P3: CONFIRMED
  P4: REFUTED
EXECUTION:
  SOURCE_NUMERICAL_PROBE: NOT_RUN
  OLD_FINITE_TESTS_RERUN: false
  SYMBOLIC_AND_RATIONAL_CHECKS: performed_not_substitutes_for_analytic_proofs
  LEAN_EDIT: false
  LEAN_GATE: NOT_RUN
  STATE_QUEUE_REGISTRY_EDIT: false
PUBLICATION:
  EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SATURATION_2026-09-10.md
  AUTHORIZED_WRITE_SCOPE: VERDICT_DOC_ONLY
  BRANCH: rh_clean
  COMMIT_BLOB_SHA256_BYTES_LINES_AND_PUSH_STATUS: accompanying_verified_delivery_receipt
ROUTE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
BUS_010: VOID
```

## 0. Decision, provenance, and scope

**The unrestricted-degree upper-rate supplier has a complete paper candidate.** An explicit compact Bessel window supplies the missing exponential; a calibrated Poisson sum supplies an exact global radical; local shell density returns the trial to the original directions. The result concerns an upper trial energy, not the lower sign. Independent checking of the new construction is pending. The `true` rate flag means the paper proof below, not a Lean or Arb verification. [COFINAL_FAMILY][PAPER]

The principal construction is not an unknown eigenvector, a resolvent assumed positive, or a renamed infimum. For every sufficiently large real a it produces an actual affine function f_a and proves
\[
 |Q[f_a]|\le K e^{57a}T(a)^2.
\]
It then specifies finite original-shell coefficients with Q-energy at most twice that budget. The exponent 57 is deliberately crude and is not claimed optimal. [COFINAL_FAMILY][PAPER]

### 0.1 Source ledger

All five shelf paths below are pinned to SOURCE_BASE. The request itself is pinned separately as in the header. The complete attached request was read, its SHA-256, Git blob, byte count and LF count recomputed, and its Git blob matched the exact-commit connector response.

| Key | Repository path | SHA-256 | Git blob | This batch |
|---|---|---|---|---|
| L | `docs/routeB_bus/RADICAL_SHELL_DENSITY_2026-09-10.md` | `ddeefef881c753a217c70aa6633ed0512daa8a140896f243aa34b918a305c423` | `788e6a6e94861ee293a7e3591358d0957a0f1899` | READ full; both hashes recomputed; 12464 bytes, 154 lines |
| B | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_BRIDGE_2026-09-09.md` | `0d2117118585b58acc6f765f3692b5d536e3fb832039c29d9680e12ebbaf0550` | `24c934f63e3e28a448f3989014bbadca154a94bc` | READ relevant proofs in full local artifact; both hashes recomputed; pin matched; 47350 bytes, 605 lines |
| I | `docs/routeB_bus/BRIDGE_INDEPENDENT_CHECK_2026-09-10.md` | `222c166aa68d8fe3dc4fb7e2b074cd0b0a92a176f9e310c1276fd99b2e57ff82` | `a912123c7d99fbc566e0a5aeba7053a457d68377` | READ full; both hashes recomputed; 5853 bytes, 66 lines |
| S | `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SCHUR_2026-09-09.md` | `7717cb8106b543339909d734f0128f2e45d3d8df33bf384ff0c2476fa4e38cab` | `84c1ae8791f5124cf676426cfc927898e052d61e` | READ freshly fetched lines 130–204; pinned blob matched; full SHA not recomputed here |
| P | `docs/BATCH_PATTERNS.md` | `cded6dfd5950fd8dd230ad770ff0cf4a50a5bea9b2d5e91601b8eaa76120903b` | `cb63bab5fbff3d39bf63c0b0f081a2264e004f2b` | READ full; both hashes recomputed; 11341 bytes, 79 lines |

Reading a previous checker is not adopting its conclusions as axioms. The mathematical inputs used from B and L are rechecked below. Historical finite enclosures in I remain accepted report evidence, not computations performed here. No companion numerical JSON was used to establish a universal estimate. [ABSTRACT][PAPER]

### 0.2 Explicit integrity and version limitations

Four complete shelf SHA-256 checks were completed, not five. The complete SCHUR bytes were not independently rehashed in this batch; its SHA in the table is binding metadata and a prior verified receipt, not a fresh computation. Its pinned Git blob and the freshly read foundation passage agree with the verified BRIDGE source. No step below relies on an additional unexamined SCHUR assertion: the full-form continuity, radical interface, and tail estimate are restated and justified here and in byte-verified B. Direct raw-HTTP acquisition failed; that failed transport supplies no evidence.

The GitHub bootstrap was fetched on `rh_clean` and read, with blob `eba04b799176c9e6a1d5f7fc4061280cfbf96ad4`. The older uploaded bootstrap has a different blob and was not substituted for it. Only `docs/BATCH_PATTERNS.md` was opened outside the task's Route-B source tree.

The primary HTML served at `https://arxiv.org/html/2606.09096v1` was read at the introduction functional and (3.1). It still identifies v1 / 8 June 2026 in its header and “Version of August 24, 2026” in its body. It is not identified byte-for-byte with the checker's local June v1 PDF, nor with v2. Only the already-used geometric functional and explicit formula were cross-checked; no new external-paper theorem is imported. Current DLMF 10.32.1–3 and 10.9.4 were consulted for elementary Bessel normalizations. The crucial finite Fourier identity and all uniform estimates are derived below, not imported as a concentration theorem. No PDF was analyzed.

## 1. Frozen source and Q1: the local density transfer survives

### 1.1 Full form and the radical interface

**Scope of this subsection: [ABSTRACT][PAPER].** Pairings are antilinear first. Keep
\[
 \langle f,g\rangle_2=\int\overline f g,\quad U_tg(x)=g(x-t),\quad
 A_0(t)=\frac{e^{-t/2}}{1-e^{-2t}},
\]
\[
 \mathcal W[f]=\int e^{2|x|}|f(x)|^2dx,\qquad
 \mathcal D(f,g)=\int_0^\infty A_0(t)\langle U_tf-f,U_tg-g\rangle_2dt,
 \qquad \|f\|_E^2=\mathcal W[f]+\mathcal D[f].
\]
The Hilbert space E is complete: take the weighted L2 limit and the L2 limit of translation differences in the product-space graph norm; testing each fixed translation identifies the limits. The full form remains
\[
\begin{split}
Q(f,g)={}&\mathcal D(f,g)-c_A\langle f,g\rangle_2
 -\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}
 \{\langle f,U_{\log n}g\rangle_2+\langle f,U_{-\log n}g\rangle_2\}\\
 &+\overline{M_+(f)}M_-(g)+\overline{M_-(f)}M_+(g),\qquad
 c_A=\gamma_E+\log(8\pi)+\pi/2,
\end{split}                                                    \tag{A1}
\]
where M_±(f)=∫f(x)e^{±x/2}dx. Every prime power, both pole terms and all mixed products are retained.

Weighted Cauchy–Schwarz gives
\[
 |\langle f,U_tg\rangle_2|\le e^{-|t|}\sqrt{\mathcal W[f]\mathcal W[g]},
 \qquad |M_\pm(f)|\le\sqrt{4/3}\sqrt{\mathcal W[f]}.
\]
Together with c_A<7 and ∑_{n≥2}log(n)n^{-3/2}<6, this proves
\[
 |Q(f,g)|\le22\|f\|_E\|g\|_E,
 \quad |Q[f+e]-Q[f]|\le22\|e\|_E(2\|f\|_E+\|e\|_E).            \tag{A2}
\]
The latter follows by expanding the full sesquilinear expression, not its separate absolute components.

Write F_v(z)=∫v(x)e^{zx}dx. The already-fixed explicit formula is
\[
 Q(v,h)=\sum_\omega m_\omega
       \overline{F_v(-\overline\omega)}F_h(\omega),
 \quad h\in C_c^\infty(\mathbb R),\quad v\in E,                 \tag{A3}
\]
where ω ranges over centered nontrivial zeros, with multiplicities. To check its convention, swap the arguments of Suzuki (3.1) and use the centered Laplace variable; invariance of the zero set under reflection gives the displayed expression. Rewriting the introduction's archimedean term as translation differences adds log 2+π/2 to its point constant, giving exactly c_A in A1.

For completeness, A3 extends from compact smooth v as follows. Weighted strip evaluation is bounded by √(4/3)||v||_E for |Re z|≤1/2. The transform of fixed compact smooth h decays as O((1+|Im z|)^{-3}) uniformly in that strip. The unconditional zero count O(R log(2+R)) makes the series absolutely dominated. Compact smooth functions are dense in E: smooth cutoff errors converge in W; the cutoff commutator in D is dominated by ||v||_2² min(C²t²,4), integrable against A_0; then mollify on bounded support. Thus A2 and dominated convergence prove A3 for v∈E. Continuity extends a vanishing pairing to all second arguments in E. Consequently
\[
 F_v(\omega)=0\text{ at every centered nontrivial zero},\ v\in E
 \quad\Longrightarrow\quad Q(v,h)=0\quad(h\in E).                \tag{A4}
\]
No zero-location assumption or simplicity assumption occurs. A3 is not asserted as an absolutely convergent formula for every arbitrary pair in E×E.

Keep the source exactly
\[
 \Phi(x)=\sum_{n\ge1}(2\pi^2n^4e^{9x/2}-3\pi n^2e^{5x/2})
                    e^{-\pi n^2e^{2x}},\qquad I=\|\Phi\|_2^2>0,
\]
\[
 T(a)=\frac{\|1_{|x|>a}\Phi\|_2^2}{I},\quad
 N_a^2=I(1-T(a)),\quad p_a=1_{(-a,a)}\Phi/N_a.
\]
The Mellin computation gives F_Φ(z)=ξ(1/2+z)/2, not ξ. Theta inversion gives evenness and double-exponential decay of every fixed derivative. Hence Φ and the exact g_{2j}=(∂²−1/4)∂^{2j}Φ are global radical vectors by A4.

### 1.2 Sharp cuts, endpoints, and the annihilator proof

**For each fixed a>0: [FINITE_CELL][PAPER]; the general analytic-kernel lemma is [ABSTRACT][PAPER].** For a C1 profile v on [−a,a], put M_0=||v||_∞, M_1=||v'||_∞. Splitting the overlapping and nonoverlapping intervals gives, for 0<t≤1,
\[
 \|U_t(1_{(-a,a)}v)-1_{(-a,a)}v\|_2^2
 \le2at^2M_1^2+2tM_0^2.
\]
If t≥2a the disjoint intervals satisfy the same bound. Above t=1 use 8aM_0². Since A_0(t)≤4/(3t) on (0,1] and A_0(t)≤(4/3)e^{-t/2} above 1, integration gives precisely L3:
\[
 \|1_{(-a,a)}v\|_E^2\le
 (2ae^{2a}+8/3+64a/3)M_0^2+(4a/3)M_1^2.                       \tag{A5}
\]
Both endpoint jumps are included in the 2tM_0² term. Smooth inward tapers leave an error supported on length ≤2η, with bounded amplitude and variation ≤4M_0+2ηM_1. Its squared translation difference is bounded by the minimum of a constant times t and 8ηM_0². Integration at η and 1 gives O(η(1+|log η|)) in squared E-norm. This proves sharp-cut membership in V_a for smooth profiles. C1 profiles follow by C1 approximation and A5; this small extension will be used for the Bessel trial.

Now let g be a nonzero even Schwartz function holomorphic on a connected strip |Im z|<σ. Suppose the E-closed span of its cut even derivatives is proper in V_a^even. A nonzero continuous complex-linear functional L separates that closed span. Set
\[
 \mathscr T(\psi)=L\bigl(1_{(-a,a)}(\psi(x)+\psi(-x))/2\bigr).
\]
A5 makes this an even distribution of order at most one supported in [−a,a]. It is nonzero because the even compact smooth core is dense. It acts on any smooth profile by inserting a smooth cutoff equal to one near [−a,a].

The function z↦𝒯_x[g(x−z)] is holomorphic on the strip: the profile and its x-derivative are holomorphic in C1([−a,a]) on each compact parameter set. All its even derivatives at zero vanish by the separating assumption, and odd derivatives vanish by parity. The identity theorem makes it identically zero. On the real axis it is 𝒯*g, a Schwartz function. Thus
\[
 \widehat{\mathscr T}(\xi)\widehat g(\xi)=0\quad(\xi\in\mathbb R).
\]
The transform of compactly supported 𝒯 is entire. The continuous transform of nonzero g is nonzero on some open interval. The entire transform of 𝒯 vanishes there and hence everywhere. Fourier injectivity contradicts 𝒯≠0. This proves the general lemma. Spectral zeros of g-hat do not invalidate it; no nowhere-zero hypothesis was used.

For the actual g_0, the defining theta series and all derivatives converge normally on compact subsets of |Im z|<π/4. Its real tails are Schwartz by theta inversion. It is nonzero: otherwise Φ''=Φ/4, whose only Schwartz solution is zero, whereas Φ(0)>0 term by term. Apply the lemma to g_0 to prove L1.

The complex-linear projection P_pf=f−p⟨p,f⟩_2 is E-continuous; its norm is at most 1+||p||_E. Its image is V_a^even∩p^⊥, and
\[
 P_p(1_{(-a,a)}g_{2j})=1_{(-a,a)}(g_{2j}-\alpha_j\Phi)=d_j.
\]
The order of this scalar pairing is essential. Projecting approximants proves L2. Therefore p−∪_m S_{m,a} is E-dense in 𝒜_a.

With BRIDGE B2 and B17, continuity A2 now gives
\[
 D_\infty(a)=N_a^2\inf_{f\in\mathcal A_a}Q[f],                  \tag{A6}
\]
including −∞: approximate successively more negative affine trials if necessary. This is L5, with the N_a² factor preserved. It is local density, not global radical density and not exterior density. It proves no energy rate on its own.

For any actual f∈𝒜_a and b>0 with Q[f]≤b, choose a shell approximation with E-error e satisfying 22e(2||f||_E+e)≤b. Its energy is ≤2b. This is an existential implication for each window. With unrestricted m(a), no uniform degree approximation rate is required. **Q1 has no remaining incorrect assertion or missing premise.**

## 2. Q2 mechanism: a compact window, its Fourier reflection, and exact calibration

### 2.1 A failed first construction and its concrete repair

**[ABSTRACT][PAPER].** Merely adding a compact even function to its Fourier transform is not enough. Use the ordinary Fourier convention
\[
 \widehat h(\xi)=\int_{\mathbb R}h(t)e^{-2\pi i t\xi}\,dt.        \tag{A7}
\]
If k=h+hat h is self-Fourier and m=k(0)=∫k≠0, Poisson summation gives, for V(x)=e^{x/2}∑_{n≥1}k(ne^x),
\[
 V(x)-V(-x)=\frac m2(e^{-x/2}-e^{x/2}).                          \tag{A8}
\]
If V decays at +∞, its negative tail therefore grows like (m/2)e^{|x|/2}. It is not in E. Taking the positive window w below without calibration gives m=1+∫w>1, an exact counterexample to this first mechanism. This is a domain failure for that construction, not a counterexample to the theta target.

The repair is to enforce both k(0)=0 and ∫k=0 before theta summation. The same repair also fixes the limiting profile to the actual Φ. Set
\[
 P(t)=2\pi^2t^4-3\pi t^2,\quad h_*(t)=P(t)e^{-\pi t^2}.
\]
Direct differentiation of the Gaussian transform proves hat h_*=h_*; Gaussian moments give h_*(0)=∫h_*=0. Moreover
\[
 \Phi(x)=e^{x/2}\sum_{n\ge1}h_*(ne^x).                          \tag{A9}
\]
Thus this is a source identity, not a similarly shaped replacement of Φ.

### 2.2 Explicit Bessel window

**Definitions and finite-parameter identities: [ABSTRACT][PAPER].** Fix the integer order **8**, once and for all. For every λ≥1 put c=2πλ² and
\[
 w_\lambda(t)=
 \begin{cases}
 \displaystyle\frac{(1-t^2/\lambda^2)^4
 I_8(c\sqrt{1-t^2/\lambda^2})}{I_8(c)},& |t|<\lambda,\\
 0,&|t|\ge\lambda.
 \end{cases}                                                   \tag{A10}
\]
Here I_8 is the modified Bessel function, and its defining positive series is
I_8(z)=∑_{k≥0}(z/2)^{8+2k}/(k!(8+k)!). In particular I_8(c)>0, w_λ(0)=1 and w_λ≥0. The inside series starts with a constant times (1−t²/λ²)^8. The zero extension is C7, with derivatives through order 7 vanishing at ±λ.

Define, using real absolutely convergent integrals,
\[
 \beta_\lambda=\frac{\int P(t)w_\lambda(t)dt}{1+\int w_\lambda(t)dt},
 \quad h_\lambda=(P-\beta_\lambda)w_\lambda,
 \quad k_\lambda=h_\lambda+\widehat h_\lambda.                   \tag{A11}
\]
The denominator is ≥1. All these functions are real and even. Fourier inversion gives hat k_λ=k_λ, while
\[
 k_\lambda(0)=h_\lambda(0)+\int h_\lambda
 =-\beta_\lambda+\int Pw_\lambda-\beta_\lambda\int w_\lambda=0.
\]
Hence ∫k_λ=0 as well. The correction is exact, not an asymptotically small moment error. Ordinary value/mass cancellation for k is not the assertion M_±(V)=0; the pole terms of Q are not removed.

## 3. The new quantitative lemma: the Fourier tail has the required exponential

Every estimate in this section holds **for all λ≥1 and all ξ≥λ** where applicable. The constants are independent of both variables. [COFINAL_FAMILY][PAPER]

### 3.1 Exact Fourier identity, including the turning point

For α>−1/2 write S_α(r)=J_α(r)/r^α, understood by its entire power series in r², including r=0. Let W_λ=hat w_λ. Direct beta integration gives
\[
 W_\lambda(\xi)=\frac{\lambda\sqrt{2\pi}\,c^8}{I_8(c)}
 S_{17/2}\left(\sqrt{(2\pi\lambda\xi)^2-c^2}\right).             \tag{A12}
\]
Here and below the expression at ξ=λ is its regular series value, not division by zero.

A derivation fixes every factor. Expand I_8(c√(1−y²))(1−y²)^4 and e^{-ivy}, where y=t/λ and v=2πλξ. The coefficient of c^{8+2k}v^{2l} in the integral over [−1,1] is
\[
 \frac{(-1)^l\Gamma(l+1/2)}
 {2^{8+2k}k!(2l)!\Gamma(8+k+l+3/2)}
 =\frac{(-1)^l\sqrt\pi}
 {2^{8+2k+2l}k!l!\Gamma(8+k+l+3/2)}.
\]
The same coefficient in √(2π)c^8 S_{17/2}(√(v²−c²)) is the expression on the right. Both series converge normally on compact (c,v) sets; beta integration and rearrangement are therefore justified. Multiplication by λ/I_8(c) proves A12 for all real ξ, with analytic continuation through the turning point. This is not an imported prolate concentration theorem.

Differentiating the series proves
\[
 \frac{d}{dv}S_\alpha(\sqrt{v^2-c^2})=-vS_{\alpha+1}(\sqrt{v^2-c^2}).
\]
The derivative rows through order 5 are
\[
\begin{array}{c|l}
0&S_\alpha\\
1&-vS_{\alpha+1}\\
2&-S_{\alpha+1}+v^2S_{\alpha+2}\\
3&3vS_{\alpha+2}-v^3S_{\alpha+3}\\
4&3S_{\alpha+2}-6v^2S_{\alpha+3}+v^4S_{\alpha+4}\\
5&-15vS_{\alpha+3}+10v^3S_{\alpha+4}-v^5S_{\alpha+5}.
\end{array}                                                     \tag{A13}
\]
Their absolute coefficient sums are at most 26. No factor (v²−c²)^{-1/2} is introduced.

### 3.2 Uniform constants

Fix the following explicit positive constants:
\[
 d=\frac{e^{-1}}{2^{33/2}\sqrt\pi\,\Gamma(17/2)},\quad
 C_*=2^{14}13!,\quad
 C_W=\frac{2^{40}C_*}{d}(2\pi)^{20},\quad
 D_*=4(1+18/d)C_W,\quad k_0=2\pi^2-3\pi>0.                     \tag{A14}
\]
The positive integral representation
\[
 I_8(c)=\frac{(c/2)^8}{\sqrt\pi\Gamma(17/2)}
        \int_{-1}^{1}e^{cs}(1-s^2)^{15/2}ds
\]
follows by expanding the exponential and integrating beta moments. Restrict its integral to 1−1/c≤s≤1−1/(2c), for c≥1. On this interval e^{cs}≥e^{c−1} and 1−s²≥1/(2c). Thus
\[
 I_8(c)\ge d\,c^{-1/2}e^c.                                    \tag{A15}
\]
This lower bound, rather than an unquantified asymptotic, pays the exponential in the Fourier estimate.

The analogous oscillatory beta integral gives |S_{n+1/2}(r)|≤1 for real r≥0 and 0≤n≤13. For r≥1, start with J_{±1/2}(r)=√(2/(πr)) times sine/cosine. The recurrence
J_{n+1/2}=(2n−1)J_{n−1/2}/r−J_{n−3/2}
proves inductively |J_{n+1/2}(r)|≤2^{n+1}n!r^{-1/2}. Indeed the proposed constants dominate the recurrence, including n=1. Therefore
\[
 |S_{n+1/2}(r)|\le C_*\min(1,r^{-n-1}),\qquad 0\le n\le13.       \tag{A16}
\]
The smaller bound 1 can be used in the first part of the range.

For c≤v≤2c, A13 gives |∂_v^j S_{17/2}|≤26(2c)^5, j≤5. The prefactor in A12 is at most d^{-1}(2π)^9 λ^{18}e^{-c}; converting derivatives to ξ costs at most (2πλ)^5. Consequently
\[
 |W_\lambda^{(j)}(\xi)|\le
 26\cdot2^5 d^{-1}(2\pi)^{19}\lambda^{33}e^{-c}
 \quad(\lambda\le\xi\le2\lambda,\ 0\le j\le5).                \tag{A17}
\]
For v≥2c, r=√(v²−c²)≥v/2. Each term v^{j−2l}S_{17/2+j−l}(r) in A13 is bounded by C_*2^{14}v^{-9}, because its remaining power is v^{-9−l}. It follows that
\[
 |W_\lambda^{(j)}(\xi)|\le
 26 C_*2^{14}d^{-1}(2\pi)^5\lambda^5 e^{-c}(\xi/\lambda)^{-9}
 \quad(\xi\ge2\lambda,\ 0\le j\le5).                           \tag{A18}
\]
Here using the fifth-derivative factor for lower j enlarges the bound legitimately, since λ≥1.

In A17, 1+ξ≤3λ and (ξ/λ)^8≤2^8. In A18, multiplying one derivative by ξ costs λ(ξ/λ). The deliberately larger C_W in A14 therefore proves, for j=0,1,2,3,4,
\[
 |W_\lambda^{(j)}(\xi)|+\xi|W_\lambda^{(j+1)}(\xi)|
 \le C_W\lambda^{34}e^{-c}(\xi/\lambda)^{-8}.                   \tag{A19}
\]
This covers ξ=λ, ξ=2λ, and the whole unbounded exterior, not just a transition band.

### 3.3 Calibration is bounded and preserves the tail estimate

For integer 0≤j≤8, the elementary cosine representation gives I_j(s)≤I_0(s)≤e^s min(1,s^{-1/2}) for s>0; at s=0 use the first bound. For the square-root bound, use cos θ≤1−2θ²/π² in the integral for I_0 and extend the Gaussian integral to infinity. Its coefficient √π/(2√2) is <1.

Put q=1−t²/λ² on the inside. From A15, for each integer 0≤j≤8,
\[
 \frac{q^{j/2}I_j(c\sqrt q)}{I_8(c)}
 \le\frac{\sqrt2}{d}e^{-\pi t^2/2}.                            \tag{A20}
\]
To verify the uniformity, split q≥1/4 and q<1/4. In the first range the square-root factors cost at most √2, and c(1−√q)≥πt². In the second range the ratio is at most d^{-1}√c e^{-c/2}≤d^{-1}e^{-c/4}≤d^{-1}e^{-πt²/2}. The elementary inequality √c e^{-c/4}≤1 holds for all c≥0.

In particular w_λ≤(√2/d)e^{-πt²/2}. Gaussian moments then give
\[
 |\beta_\lambda|\le\int |P|w_\lambda\le18/d.                    \tag{A21}
\]
The denominator of β was bounded below by 1. Direct Fourier differentiation, with convention A7, gives exactly
\[
 \widehat h_\lambda
 =\frac{W_\lambda^{(4)}}{8\pi^2}
   +\frac{3W_\lambda''}{4\pi}-\beta_\lambda W_\lambda.
\]
Since 1/(8π²)+3/(4π)<1, A19–A21 imply the new uniform tail lemma
\[
 \boxed{
 |\widehat h_\lambda(\xi)|+\xi|\widehat h_\lambda'(\xi)|
 \le\frac{D_*}{4}\lambda^{34}e^{-2\pi\lambda^2}
              (\xi/\lambda)^{-8}
 \quad(\lambda\ge1,\ \xi\ge\lambda).}                         \tag{A22}
\]
All polynomial and mixed calibration contributions are included. Dropping the calibration is not allowed, even though its magnitude is bounded.

## 4. The Poisson radical and the physical affine denominator

### 4.1 The limiting source is the actual Φ

**[COFINAL_FAMILY][PAPER].** This subsection proves the nonvanishing normalization; it does not assume it as an extra supplier.

For fixed integer j≥0, the same positive integral used above, with u=c(1−s), gives
\[
 I_j(c)\sim e^c/\sqrt{2\pi c}\quad(c\to\infty).
\]
This asymptotic follows directly by dominated convergence: after extracting e^c c^{-1/2}, the integral tends to its gamma integral, with factor (1−u/(2c))^{j−1/2} on [0,2c]. For j≥1 it is dominated by u^{j−1/2}e^{-u}; this suffices for the orders 3 through 8 used next. No asymptotic is being used uniformly in a growing Bessel order.

For each fixed real t, A10 and this fixed-order calculation give w_λ(t)→e^{-πt²}. Derivatives through order 5 also converge pointwise to the Gaussian derivatives. To see this without differentiating an asymptotic, use the exact identity
\[
 \frac d{dt}\{q^{j/2}I_j(c\sqrt q)\}
 =-2\pi t\,q^{(j-1)/2}I_{j-1}(c\sqrt q).
\]
Repeated differentiation yields fixed polynomials in t multiplying the ratios in A20. Those ratios tend to e^{-πt²}; A20 bounds each derivative by a fixed polynomial times e^{-πt²/2}. Zero extension causes no derivative atoms through order 5 because A10 vanishes to order 8 at both endpoints.

Dominated convergence consequently gives convergence of w_λ and its derivatives through order 5 in every polynomially weighted L1 norm. A11 gives β_λ→0 because ∫P e^{-πt²}=0 and 1+∫w_λ→2. Thus h_λ→h_* in the same weighted derivative norms.

Fourier integration by parts now yields, uniformly in λ, bounds
\[
 |k_\lambda(t)|\le C(1+|t|)^{-4},\qquad
 |t k_\lambda'(t)|\le C(1+|t|)^{-4},                            \tag{A23}
\]
with a fixed finite C. For the second bound apply five integrations by parts to the transform of t h_λ; all boundary terms vanish. On bounded t use the corresponding L1 moment bounds. The compact part h_λ and its derivative satisfy stronger Gaussian-polynomial bounds. The same arguments give pointwise k_λ→2h_* and k_λ'→2h_*'. The constant C is used only for convergence, not for the quantitative exponential estimate A22.

### 4.2 Theta summation, domain, and radical membership

Define
\[
 V_\lambda(x)=e^{x/2}\sum_{n\ge1}k_\lambda(ne^x).                \tag{A24}
\]
The series and its first derivative converge locally uniformly by A23. Poisson summation is legitimate: k_λ is C1 with integrable polynomial tails, its Fourier transform is itself, and both sampled series converge absolutely. One proof is to periodize k_λ; its absolutely summable Fourier coefficients are u^{-1}k_λ(n/u), and uniqueness of the continuous Fourier series gives the Poisson identity. The calibration k_λ(0)=∫k_λ=0 eliminates its n=0 terms. Thus
\[
 V_\lambda(-x)=V_\lambda(x).                                   \tag{A25}
\]
In particular V_λ'(0)=0. From A23, on x≥0, both |V_λ(x)| and |V_λ'(x)| are bounded by a fixed constant times e^{-7x/2}; parity extends this to the negative half-line. Therefore V_λ∈E: its weighted mass is finite, and its H1 norm controls D by ||U_tv−v||_2≤t||v'||_2 below t=1 and by 2||v||_2 above it.

Pointwise dominated convergence in the sampled series, followed by the same tail majorant, proves
\[
 V_\lambda\longrightarrow2\Phi\quad\hbox{in }E
 \quad(\lambda\to\infty).                                     \tag{A26}
\]
For D, the H1 convergence just established suffices; for W use the exponential majorant. This is stronger than the L2 convergence needed for the denominator.

The Mellin identity is equally explicit. Set s=1/2+z and
\(\mathcal M k(s)=\int_0^\infty k(u)u^{s-1}du\).
For 1<Re s<4, absolute convergence permits exchanging sum and integral in A24, giving
\[
 F_{V_\lambda}(z)=\zeta(s)\mathcal M k_\lambda(s).               \tag{A27}
\]
Because k_λ is even, C2 and k_λ(0)=0, it is O(u²) at zero. A23 gives O(u^{-4}) at infinity. Its Mellin transform is analytic on −2<Re s<4; the pole at s=1 of ζ is canceled by 𝓜k_λ(1)=0. Analytic continuation therefore proves A27 across 0<Re s<1. Every nontrivial zeta zero makes the right side vanish. Apply A4, now that V_λ∈E has been established, to obtain
\[
 \boxed{Q(V_\lambda,h)=0\quad\hbox{for every }h\in E.}          \tag{A28}
\]
This is a global radical identity, not only Q[V_λ]=0. It uses no RH premise. It is also not a claim that all of E is a radical or that an uncut derivative family is globally dense.

The finite regularity of A10 is sufficient throughout: C7 for the compact kernel, five integrations by parts, and C1 for sharp-cut E membership. No theorem requiring a Schwartz compact kernel is silently applied to it.

### 4.3 Fixed affine normalization

For a>0 put λ=e^a and
\[
 q_a=\langle p_a,1_{(-a,a)}V_{e^a}\rangle_2
     =\langle p_a,V_{e^a}\rangle_2.
\]
Since p_a→Φ/√I in L2 and A26 gives V_{e^a}→2Φ in L2,
\[
 q_a\longrightarrow2\sqrt I>0.                                \tag{A29}
\]
The quantities are real. Consequently the set
\[
 \{n\in\mathbb Z_{\ge1}:\ \forall\hbox{ real }a\ge n,
                                \ q_a\ge\sqrt I\}
\]
is nonempty. Define a_0 to be its least element. This is a fixed existential witness obtained from a proved limit, not a new assumed estimate. No numerical value for a_0 is claimed.

For every real a≥a_0 define the actual trial
\[
 f_a=\frac{1_{(-a,a)}V_{e^a}}{q_a}.                              \tag{A30}
\]
By A5 and the C1 regularity, f_a∈V_a^even. Its physical affine normalization is exactly ⟨p_a,f_a⟩_2=1. There is no division by its own L2 norm and no use of an unknown ground state.

## 5. The uniform T-squared estimate and the exact-shell return

### 5.1 The exponential survives theta summation and the full form

**All inequalities here hold for every real a≥a_0: [COFINAL_FAMILY][PAPER].** For x≥a and u=e^x≥λ, compact support gives h_λ(nu)=0, including the continuous endpoint value when nu=λ. Thus A24 contains only hat h_λ in this range. From A22 and ∑n^{-8}<2, both V_λ and its x-derivative obey
\[
 |V_\lambda(a+s)|,\ |V_\lambda'(a+s)|
 \le A_\lambda e^{-15s/2}\quad(s\ge0),\qquad
 A_\lambda=D_*\lambda^{69/2}e^{-2\pi\lambda^2}.                 \tag{A31}
\]
The derivative includes both half the profile and nu times its derivative; A22 bounds their sum. Parity supplies the second tail. The coefficient D_* in A31 is larger than needed by a factor two, which is harmless.

The positive tail reference extends beyond finite derivative combinations: for any C1 profile v with the displayed integrable tails, the translation-jump proof gives
\[
 \|1_{|x|>a}v\|_E^2\le\mathfrak B_a[v],
\]
\[
 \mathfrak B_a[v]=\int_{|x|>a}
 [(e^{2|x|}+16a+16)|v|^2+3e^{-4a}|v'|^2]dx
 +6e^{-2a}(|v(a)|^2+|v(-a)|^2).                                \tag{A32}
\]
Indeed split the translation integral at δ=e^{-2a} and 1. Below δ, write the distributional derivative of the tail as its ordinary derivative plus the two jumps; the squared difference is at most 3t²||1_out v'||²+3t times the two squared traces. Use A_0(t)≤2/t. Above δ use the L2 difference bound. The resulting derivative, trace, middle and large-t coefficients are 3δ², 6δ, 16a and 16. This proof needs neither finite-span membership nor positivity of Q.

A31 gives, including both tails,
\[
 \mathcal W[1_{\rm out}V_\lambda]\le(2/13)\lambda^2 A_\lambda^2,
 \quad \|1_{\rm out}V_\lambda\|_2^2,
       \|1_{\rm out}V_\lambda'\|_2^2\le(2/15)A_\lambda^2,
\]
with squared trace sum ≤2A_λ². Since a+1≤e^{2a}=λ² and λ≥1,
\[
 \mathfrak B_a[V_\lambda]
 \le\left(\frac2{13}+\frac{32}{15}+\frac6{15}+12\right)
                      \lambda^2A_\lambda^2
 <16D_*^2\lambda^{71}e^{-4\pi\lambda^2}.                       \tag{A33}
\]
The rational coefficient is 2864/195<16.

By A28, the two sharp cuts of V_λ have exactly equal Q-energy. For clarity, writing V=u+t gives Q(V,u)=Q(V,t)=0, and expanding these two equalities gives Q[u]=Q[t]. Hence A2, A29–A33 prove
\[
 |Q[f_a]|=\frac{|Q[1_{\rm out}V_{e^a}]|}{q_a^2}
 \le\frac{352D_*^2}{I}\lambda^{71}e^{-4\pi\lambda^2}.           \tag{A34}
\]
No prime sum has been cut at λ² on the exterior. A2 controls the entire infinite sum. Both pole terms remain in the same continuity estimate.

### 5.2 Comparison with the fixed, true T(a)

For y=e^{2x}≥1, every theta summand is positive and the n=1 summand gives
\[
 \Phi(x)\ge k_0 y^{9/4}e^{-\pi y},\qquad k_0=2\pi^2-3\pi.
\]
After using both tails and dx=dy/(2y),
\[
 IT(a)\ge k_0^2\int_{\lambda^2}^\infty y^{7/2}e^{-2\pi y}dy
 \ge\frac{k_0^2}{2\pi}\lambda^7 e^{-2\pi\lambda^2}.
\]
Consequently
\[
 T(a)^2\ge\frac{k_0^4}{4\pi^2 I^2}
                    \lambda^{14}e^{-4\pi\lambda^2}.            \tag{A35}
\]
This is a proved lower envelope for the true theta mass fraction. It is not the T of the new Bessel profile.

Define once and for all
\[
 \boxed{K=\frac{1408\pi^2 I D_*^2}{k_0^4}>0,\qquad\mu=57.}     \tag{A36}
\]
Combining A34 and A35 gives the actual, unconditional upper trial estimate
\[
 \boxed{\forall a\ge a_0:\quad f_a\in\mathcal A_a,\qquad
                         |Q[f_a]|\le K e^{57a}T(a)^2.}         \tag{A37}
\]
Thus
\[
 \boxed{\forall a\ge a_0:\quad
       [\inf_{f\in\mathcal A_a}Q[f]]_+\le K e^{57a}T(a)^2,}     \tag{A38}
\]
with the prescribed convention at −∞. This proves Q2's quantitative assertion in the submitted paper candidate. The large constants do not alter its quantifiers or its exponent in e^{2a}.

### 5.3 Q3: actual coefficients in the exact original shells

Let b_a=K e^{57a}T(a)^2>0, z_a^*=p_a−f_a and
\[
 \eta_a=\min\left(1,\frac{b_a}{22(2\|f_a\|_E+1)}\right)>0.
\]
Then z_a^*∈V_a^even∩p_a^⊥. For every finite m take its **E-orthogonal projection** z_{m,a} onto the exact S_{m,a}. This is not a Q-positive projection. To specify its coefficients, put
\[
 H^{E}_{ij}=\langle d_i,d_j\rangle_E,\quad
 v^{E}_i=\langle d_i,z_a^*\rangle_E,\quad
 c^{(m,a)}=(H^{E})^{-1}v^{E},\qquad z_{m,a}=\sum_{j=0}^m c_j^{(m,a)}d_j.
                                                                    \tag{A39}
\]
H^E is positive definite because the d_j are independent. To recheck independence, a finite combination vanishing inside the interval extends analytically to the line; dividing its transform by nonzero F_Φ gives
(z²−1/4)∑c_jz^{2j}−∑c_jα_j=0. Evaluation at z=1/2 and then polynomial coefficients gives c=0. No sign of the signed matrix C is used.

By Q1, ||z_{m,a}−z_a^*||_E→0 as m→∞. Define m(a) to be the least m≥0 for which this error is ≤η_a. Its existence is proved by density, not assumed by defining a least degree. The final trial
\[
 f_a^{\rm shell}=p_a-z_{m(a),a}
\]
has exactly the original physical affine normalization. A2 gives
\[
 Q[f_a^{\rm shell}]\le Q[f_a]+22\eta_a(2\|f_a\|_E+\eta_a)
                   \le2K e^{57a}T(a)^2.                         \tag{A40}
\]
Thus M=2K, ν=57 and a_*=a_0 are fixed witnesses for the original-shell supplier. All coefficient integrals use the fixed source and the explicit f_a; no eigenvector or numerical solve is an input. Real coefficients can also be selected because all data here are real.

In BRIDGE's notation, A6 and A38 prove its ATOM with K, μ=57 and the same a_0. B18 then also gives the factor-two shell conclusion. It is the **same slack already used in A40**, not an extra factor to charge twice. The explicit E-projection prescription avoids every signed inverse branch.

This closes the permitted return from the enlarged intermediate representation. It does **not** prove S15 for its particular H-minimizer: inside E-density does not transfer an outside B-norm bound to a derivative combination. On any positive signed finite block containing the final trial, minimization gives S26 at that final budget. No claim about its reference coefficient c_B or S26b is needed.

## 6. Operator and singular-branch audit

**[ABSTRACT][PAPER].** The auxiliary reduction in the request is valid with the specified E-Hilbert space, not an unspecified L2 inverse. A1–A2 represent Q on H_a=V_a^even by a bounded self-adjoint B_a with norm ≤22. The normalization functional has a nonzero Riesz representative r_a because it equals one at p_a.

If Q[u]<0 for any u∈H_a, a nonzero normalization coupling makes u/⟨p_a,u⟩_2 an affine negative trial. If the coupling is zero, Q[p_a+tu]→−∞. Therefore the positive part of the affine infimum is zero in either case; the infimum is not claimed always −∞.

Otherwise B_a≥0. For ε>0, the spectral theorem gives
\[
 Z_\varepsilon=\langle r_a,(B_a+\varepsilon I)^{-1}r_a\rangle_E>0,
 \quad Z_\varepsilon\uparrow Z_0\in(0,\infty]
 \quad(\varepsilon\downarrow0).
\]
Cauchy–Schwarz in the positive (B_a+εI)-metric gives 1≤Z_ε(Q[f]+ε||f||_E²) for every affine f. Conversely the normalized resolvent vector is affine and has energy
\[
 \frac1{Z_\varepsilon}
 -\frac{\varepsilon\|(B_a+\varepsilon I)^{-1}r_a\|_E^2}{Z_\varepsilon^2}
 \le\frac1{Z_\varepsilon}.
\]
Taking ε↓0 for each fixed f proves inf_𝒜Q=1/Z_0, including 1/∞=0. This argument assumes neither invertibility of B_a nor attainment of the infimum.

A coupled null vector forces Z_0=∞. A decoupled nullspace does not decide Z_0: the spectral integral ∫t^{-1}d⟨r_a,E_B(t)r_a⟩ may still diverge at zero away from an atom. These branches remain distinct. The new A37 works in every branch without classifying it. As a consequence, on the nonnegative branch alone it proves Z_0(a)≥1/(K e^{57a}T(a)^2). Positivity is not introduced as a cofinal premise.

Nothing here bounds Q below on all tests. Small upper energies, even the stronger absolute bound for these selected trials, do not supply the lower-sign requirement of the Weil consumer.

## 7. Dependency ledger, predictions, and scope attacks

### 7.1 Complete dependency chain

Every row retains A1, the original Φ, physical normalization and real-window quantifier unless its output explicitly concerns an auxiliary ordinary Fourier variable.

| Supplier | Domain and quantifiers | Input → output; proof | Type and tags |
|---|---|---|---|
| Full-form continuity and radical interface | All v,h∈E; A3 initially h compact smooth | Full A1 and signed explicit formula → A2,A4 | Rechecked PAPER theorem; §1.1; [ABSTRACT][PAPER] |
| Fixed-window density | Every fixed real a>0 | Analytic g_0, compact annihilator → L1,L2,A6 and budget transfer | Rechecked PAPER theorem; §1.2; [FINITE_CELL][PAPER] |
| Explicit window identity | Every λ≥1, every real ξ | Bessel series and beta integral → A12,A13 | Proved analytic identity; §3.1; [ABSTRACT][PAPER] |
| Uniform Fourier tail | Every λ≥1, ξ≥λ | A12,A15,A16, calibration bound → A22 | New proved estimate; §3.2–3.3; [COFINAL_FAMILY][PAPER] |
| Calibrated Poisson radical | Every λ≥1 | A11,A23, Poisson, Mellin ζ factor → V_λ∈E and A28 | New proved mechanism; §4.1–4.2; [ABSTRACT][PAPER] |
| Affine denominator | Every sufficiently large real a | V_{e^a}→2Φ and p_a→Φ/√I → q_a≥√I | Proved nonvanishing; §4.3; [COFINAL_FAMILY][PAPER] |
| Full-space budget | Every a≥a_0 | Whole-tail bound, radical cut equality, true T lower bound → A37,A38 | New proved paper rate; §5.1–5.2; [COFINAL_FAMILY][PAPER] |
| Original-shell witnesses | Every a≥a_0, one finite m(a) and source coefficient vector | Exact E-projection and A2 → A40; equivalent B18 return | Proved existential transfer; §5.3; [COFINAL_FAMILY][PAPER] |

No unsupported cofinal step is labeled a finite identity. None of the rows is LEAN-verified. Independent review of this complete new chain remains mandatory before production admission.

### 7.2 Frozen predictions

| Frozen event | Fate | Evidence and scope |
|---|---|---|
| P1, 0.95: L1–L5 survive without a new degree-rate requirement | CONFIRMED | §1.2 rederives the annihilator proof, complex projection and both infimum inequalities; A39–A40 use pointwise density only. [ABSTRACT][PAPER] |
| P2, 0.80: qualitative completeness alone does not pay T² | CONFIRMED | The new A22 and A33 supply the exponential; density is used only after A37. No energy rate was inferred from completeness. [COFINAL_FAMILY][PAPER] |
| P3, 0.90: no lower-sign supplier follows from an upper trial | CONFIRMED | §6 distinguishes every operator branch, and only selected trial energies are bounded. [ABSTRACT][PAPER] |
| P4, 0.75: main outcome remains partial | REFUTED | The submitted outcome is a complete paper candidate with fixed K, μ=57, proved existence of a_0 and exact-shell return. This scores the submitted derivation; independent validation is still pending. [COFINAL_FAMILY][PAPER] |

The in-chat prediction registered before the symbolic cross-checks was that theta summation preserves e^{-4πe^{2a}} in the energy, with domain/pole calibration the main risk. A22–A34 confirm that predicted mechanism in the paper derivation. No probability or numerical forecast was invented afterward. The old 1.5 forecast and all a=.7 finite rows are untouched and are not rescored.

### 7.3 Strongest attack and boundary inventory

The most serious attack is that a superficially self-Fourier kernel may fail the global E-domain before its radical identity can be used. A8 makes that attack exact. Calibration A11 removes its growing pole mode, while A23–A28 prove the actual domain and radical membership. It is not permissible to omit those steps and simply say “Poisson gives a radical.” [ABSTRACT][PAPER]

The second attack is a lost factor in the Bessel turning scale. In A12 the square root is ((2πλξ)²−(2πλ²)²)^{1/2}; the exponential denominator is I_8(2πλ²), not I_8(πλ²). Squaring the tail amplitude gives exactly e^{-4πλ²}. A12 was proved coefficient-by-coefficient for all coefficients, not fitted from a scalar. [ABSTRACT][PAPER]

All boundaries used by the construction are covered: t=±λ and the zero extensions (C7 vanishing); ξ=±λ (regular series value), ξ=±2λ (both bounds apply); the sampled junctions x=log(λ/n) (zero endpoint derivatives of the compact kernel); x=0 (Poisson parity and C1 convergence); physical sharp cuts x=±a (two jump terms); and both transitions of each inward taper. Coverage is complete at the regularity used here. [ABSTRACT][PAPER]

The initial failed shape has failure type INCOMPATIBILITY, scope ATTEMPT, and evidence A8 with h=w_λ. Its diagnostic margin 1−(1+∫w_λ)=−∫w_λ is strictly negative. This rejects that uncalibrated construction only. It does not reject Poisson summation, the repaired construction, or the theta upper-rate family.

## 8. One directive, one next_decisive_test, and closeout

**Directive: independently audit the complete Bessel–Poisson affine construction before formalization.** No new numerical campaign, source modification or production-state transition is authorized by this directive.

The cheapest decisive target is the new uniform tail lemma A22. Its exact observable is
\[
 \mathfrak M(\lambda,\xi)=D_*/4-
 e^{2\pi\lambda^2}\lambda^{-34}(\xi/\lambda)^8
       (|\widehat h_\lambda(\xi)|+\xi|\widehat h_\lambda'(\xi)|),
 \qquad\lambda\ge1,\ \xi\ge\lambda.                            \tag{TEST}
\]
**Threshold: zero.** Independently reconstruct A12 from the integral and verify A13–A22 over the turning band and unbounded tail. As the mandatory domain control in this same audit, replacing calibrated h_λ by w_λ must trigger A8 and reject E-membership. Then follow the unchanged normalizer through A29–A40; do not replace the affine denominator by an L2 norm.

**ЕСЛИ_A:** an independent paper derivation establishes a lower envelope for TEST ≥0 on the full stated domain, confirms the calibration/domain control and the downstream constants, accept this upper-rate proof candidate for subsequent formalization. A finite nonnegative sample alone is not acceptance.

**ЕСЛИ_B:** locate the first incorrect equation or an exact/source-enclosed violation with strict negative upper envelope for TEST. Reject that equation or those constants at its precise scope and retain preceding valid lemmas. Do not infer theta-family death from failure of a sufficient bound. A zero-containing numerical enclosure remains inconclusive; its discriminator is the analytic A12/A13 endpoint formula plus a rigorous envelope for that same TEST, not another old shell ratio.

Stop this audit when the whole chain is accepted or one first incorrect assertion is supplied. Do not use it to launch repeated precision increases at a=.7. Its output is one independent report with equation locator, exact issue, weakest repair and all preserved dependencies.

Two nearest alternatives were considered, not silently assumed: a prolate concentration/Poisson construction (estimated kill-power 8/10, proof cost 8/10) and the exact E-Riesz resolvent spectral measure (8/10, 7/10). The former needs a source-specific concentration and normalization argument; the latter supplies a correct representation but no smallness mechanism. The explicit Bessel integral has estimated kill-power 9/10 and audit cost 4/10 because its turning point and tail can be checked without solving a spectrum. These are planning estimates, not mathematical probabilities.

```yaml
K8A:
  DOWNSTREAM_CONSUMER: published_Weil_criterion_on_all_complex_compact_smooth_tests
  ACTUAL_CONSUMER_REQUIREMENT: Q_nonnegative_on_every_test_in_that_class
  ORIGINAL_REQUESTED_OBJECT: cofinal_affine_T_squared_upper_rate
  ORIGINAL_OBJECT_IS: NOT_NECESSARY
  KNOWN_WEAKER_INTERFACES:
    - all_large_window_lower_envelope_lambda_a_ge_minus_epsilon_a_with_epsilon_a_to_zero
    - direct_nonnegativity_on_the_compact_smooth_core
  UPPER_RATE_IMPLIES_LOWER_SIGN: false
  FAILURE_TYPE: OTHER
  EPISTEMIC_STATUS: UNRESOLVED
  EPISTEMIC_DETAIL: upper_rate_has_complete_new_paper_proof_pending_independent_check
  NOVELTY_AXIS: explicit_Bessel_Fourier_tail_plus_calibrated_Poisson_radical_plus_local_shell_return
CLOSES_ON_PAPER:
  - UNIFORM_FULL_SOURCE_RECOVERY_SATURATION
  - fixed_window_source_family_transfer_L1_L5
OPENS: []
CARRIES_OPEN:
  - independent_validation_of_this_new_paper_candidate
  - all_large_window_lower_sign_supplier
S15_REFERENCE_MINIMIZER_RATE: NOT_PROVED_OR_REFUTED
iteration:
  target: GOAL058_FULL_WINDOW_AFFINE_SATURATION_AFTER_DENSITY
  status: PROGRESS
  progress_class: PROOF_PROGRESS
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: uncalibrated_self_Fourier_kernel_before_theta_summation
  invariant_learned: exact_value_mass_cancellation_precedes_global_E_radical_membership
  forbidden_future_move: omit_calibration_or_substitute_normalized_Rayleigh_for_affine_energy
  next_decisive_test: independent_uniform_A22_and_downstream_normalization_audit
  route_score: 5
```

**Publication handoff.** This is documentation only. The accompanying delivery receipt identifies the actual commit, blob, SHA-256, byte count, line count and remote-branch status; a file cannot contain its own final content hash. Only EXPECTED_VERDICT_PATH is to be written. No Lean gate was run, and no axiom-profile claim is made. A later independent paper check can change the admission status of this candidate, not the unchanged lower-sign or RH state.

## 9. Proshka's own line

The new density lemma changes which construction is worth attempting.
It permits an explicit full-window trial without pretending that it is already a finite derivative combination.
The final projection returns to the original family and keeps the physical affine equation exact.
I chose a Bessel window because its Fourier tail is an identity before it is an estimate.
Its denominator already has the exponential that the raw theta cut lacks.
The first nearby alternative was a prolate extremizer.
That would replace a concrete integral by a spectral concentration and normalization audit.
The second alternative was the exact Riesz resolvent.
That representation is correct, but its inverse moment does not grow merely because it has been named.
The failed positive-window construction was useful.
It made the omitted pole mode visible before any small energy was claimed.
The scalar calibration removes that mode exactly and tends to zero in the Gaussian limit.
The resulting Poisson profile converges to twice the actual theta source.
That last identity is what protects the affine denominator from collapsing.
The first move beyond this batch is independent verification of the Fourier-tail chain.
An incorrect turning scale or a lost derivative factor would kill the displayed rate proof immediately.
The second move is a bounded formalization of the accepted analytic and projection lemmas.
A formalization that changes the function family or weakens the affine budget must be rejected.
I would ask for an independent derivation of A12 and A22, not another ground-eigenvalue ratio.
I would also ask the checker to preserve the failed uncalibrated window as a domain control.
What surprised me is that an explicit nonspectral window can carry the required exponential.
The price paid here is an intentionally large polynomial, not a hidden inverse gap.
I distrust any attempt to read this upper trial as a lower sign.
I also distrust a claim that the original positive-reference minimizer has now been proved sufficient.
The density transfer is local and gives no outside-reference control for its final coefficients.
The result is a complete upper-rate candidate with a separate independent-check obligation.
It is not a proof of RH or a reason to promote the production route.

## 10. Research log

### 10.1 Sources actually consulted

| Locator | READ / RELAY | Taken or excluded |
|---|---|---|
| SATURATION request, exact commit and hashes in the header, all 84 lines | READ; bytes verified | Q1–Q3, fixed target, predictions and one-path write authority. |
| GitHub bootstrap `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md`, branch rh_clean, blob eba04b799176c9e6a1d5f7fc4061280cfbf96ad4 | READ through connector | Current operative-header, source and evidence protocol; old uploaded variant not substituted. |
| L, sections 1–7 / L1–L6, SOURCE_BASE | READ full; both hashes verified | Local density proof reconstructed; L6 is the target, not an assumption. |
| B, sections 1–2, 4–5 / B1,B2,B17,B18 and source/version ledger, SOURCE_BASE | READ relevant full local sections; complete artifact hashes verified and connector blob matched | Full Q, E, Φ, normalization, tail continuity and exact return. Old incomplete atom is not assumed. |
| I, all 66 lines, SOURCE_BASE | READ full; both hashes verified | Historical independent findings, finite test closure and version limitations; no numerical rerun. |
| S, freshly fetched lines 130–204 / S1–S5, SOURCE_BASE | READ scoped; pinned blob matched; full SHA not recomputed here | Foundation cross-check only; quantitative work below is independently derived from A1 and the verified B content. |
| P, all 79 lines, SOURCE_BASE | READ full; both hashes verified | Proof-batch and research-log requirements; not a mathematical premise. |
| Suzuki, arXiv:2606.09096v1, `https://arxiv.org/html/2606.09096v1`, introduction functional and (3.1) | READ primary HTML | Already-used signed explicit formula and conjugation/constant convention. Header/body version discrepancy retained; no new cofinal theorem imported. |
| Suzuki local June v1 PDF and v2 mentioned by the shelf | RELAY only | Not personally read here; neither version silently identified with the live HTML. |
| NIST DLMF, `https://dlmf.nist.gov/10.32`, (10.32.1)–(10.32.3) | READ primary HTML | I-Bessel integral normalizations; beta-series derivation and explicit lower bound supplied here. No historical-release claim. |
| NIST DLMF, `https://dlmf.nist.gov/10.9`, (10.9.4) | READ primary HTML | J-Bessel beta-integral normalization; the needed half-integer bounds and window identity proved here. |
| DLMF direct TeX requests for 10.32.E2 and 10.9.E4 | UNAVAILABLE | Direct TeX fetch failed; the HTML equations were available and read. |
| Raw GitHub acquisition attempts for the SCHUR file | UNAVAILABLE | DNS/web transport did not deliver bytes; therefore no fifth fresh SHA check is claimed. |
| Current branch metadata from GitHub | READ transport metadata | Existing rh_clean branch and request ancestry; not mathematical evidence. |

No external prolate, Kaiser-window concentration, RKHS or spectral theorem from a new research paper is inserted into the chain. General Fourier, distribution, Hilbert-space and complex-analysis facts are used with their hypotheses stated. The analytic estimates supplying the new rate are proved in this document.

### 10.2 Attempted and abandoned branches

| Candidate | First exact obstacle and disposition |
|---|---|
| Positive self-Fourier window with no value/mass correction | A8 gives a growing negative-log tail, so E-membership fails. Repaired by A11. |
| An I0 window with a nonzero hard endpoint, used with repeated Fourier differentiation | Its zero extension lacks the vanishing boundary derivatives required by this proof. Replaced before use by the order-eight window A10. No target-level impossibility is inferred. |
| Raw Gaussian/theta cut as the rate supplier | The already-checked BRIDGE scale is aT, not T²; not rerun or relabeled. |
| Exact resolvent formula as a proof of inverse-moment growth | The variational identity supplies no lower bound for Z_0 by itself. Retained only as a checked consequence/interface in §6. |
| Prolate eigenvector as an imported concentration supplier | No such new external-paper theorem is imported; the explicit Bessel integral avoids this dependency. |
| Direct promotion of A32 to S15 on the original H-minimizer | Inside E-approximation does not preserve outside B-norm. Not claimed. |
| Normalizing by ||f||_2 instead of ⟨p_a,f⟩_2 | It would change the affine target. A29–A30 are retained instead. |

### 10.3 Intermediate checks and reusable identities

The all-coefficient beta calculation in §3.1 is the proof of A12. An additional symbolic check compared 36 coefficient pairs, k,l=0,…,5, exactly; every difference was zero. That finite check is only a factor/sign control.

Symbolic differentiation independently reproduced all six rows in A13 and their maximum absolute coefficient sum 26. Exact Gaussian differentiation verified hat h_*=h_* and the zero integral. Rational arithmetic gave 2864/195<16 in A33 and the exponent subtraction 71−14=57. No floating source energy or interval eigensolve was performed.

A8 is reusable as a pole-calibration falsifier. A12–A22 provide a wholly explicit weighted Fourier-tail supplier. A24–A28 turn a calibrated almost time/frequency-localized kernel into an exact full-form radical with a controlled exterior. A29 separates physical affine nondegeneracy from arbitrary scaling. A39 is an explicit E-Gram coefficient prescription which does not assume positive signed C.

**Terminal scope:** the submitted complete paper proof supplies the cofinal affine T² upper rate and its existential exact-shell return. Independent validation and formalization are not claimed completed. The full lower-sign supplier and RH remain unproved by this batch.
