# STATUS: KILL_LITERAL_EVEN_TIME_SUZUKI_KERNEL_IDENTITY
```yaml
PRIMARY: KILL_LITERAL_EVEN_TIME_SUZUKI_KERNEL_IDENTITY
PRIMARY_COUNT: 1
OPERATIVE_CLASS: KILL_LITERAL_EVEN_TIME_SUZUKI_KERNEL_IDENTITY
RESULT: ATTEMPT_REFUTED_WITH_EXACT_COUNTEREXAMPLE
REQUEST_ID: REQ-2026-09-06-SECONDEXPR-B
BOUNDARY_ID: GOAL058_SECOND_EXPRESSION_SUZUKI_KERNEL_IDENTITY
REQUEST_LOCK:
  COMMIT: 4599fba36d77dc7e3b12f743e3142ffeb813baa4
  PATH: docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_SECOND_EXPRESSION_SUZUKI_KERNEL_IDENTITY_2026-09-06.txt
  GIT_BLOB: 65017079f9ca6893da94298f4b9f72c20b6a5616
  SHA256: 098eeae0c7fa924098b668d5dfa365727db929fe0ebb0df3a20d85adf94be2ec
  BYTES: 8846
  LINES: 86
  FINAL_LF: true
  SHA256_AND_GIT_BLOB_INDEPENDENTLY_RECOMPUTED: true
SOURCE_BASE: 93171b35
EXPECTED_VERDICT_PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_SECOND_EXPRESSION_SUZUKI_KERNEL_IDENTITY_2026-09-06.md
CLOSES: [REQ-2026-09-06-SECONDEXPR-B]
CLOSES_ANALYTIC_RH_SUPPLIERS: []
OPENS: []
KILL_SCOPE: LITERAL_ALL_REAL_TIME_DEFINITION_AND_IDENTITY
KILLED_ASSERTION: printed_even_time_S_satisfies_SE_on_all_real_t_u
UNIVERSAL_NO_ZEROS_FREE_METHOD_THEOREM: NOT_PROVED
INTENDED_SIGNED_TIME_REPAIR:
  STATUS: PROPOSED_EXPLICITLY_NOT_SILENTLY_SUBSTITUTED
  AUTHOR_CONFIRMED_ERRATUM: false
  GLOBAL_KERNEL_IDENTITY: OPEN
  RADICAL_CUTOFF_CHECK: PAPER_PROVED_FOR_REPAIRED_OBJECT
SOURCE_FINDINGS:
  EVEN_TIME_RULE_IN_ARXIV_V3_PDF: VERIFIED
  EVEN_TIME_RULE_IN_JOURNAL_HTML: VERIFIED
  LITERAL_TRANSFORM_ANNIHILATES_ALL_EVEN_TESTS: PAPER_PROVED
  STRICT_POSITIVE_SHORT_SUPPORT_COUNTEREXAMPLE: PAPER_PROVED
  LITERAL_F2_FOR_ALL_TRANSLATES: REFUTED_ON_PAPER
DIRECT_CALCULATION:
  VOLTERRA_IDENTITY: PAPER_PROVED_WITHOUT_ZERO_SUMS
  L2_EXISTENCE_AND_LOCAL_UNIFORM_BOUND: PAPER_PROVED_WITHOUT_RH
  GRAM_INTEGRAL_REDUCTION: PAPER_PROVED_WITHOUT_ZERO_SUMS
  PRIME_ATOMS_FROM_THE_GRAM_REMAINDER: NOT_PROVED
  EXACT_DISTRIBUTIONAL_REMAINDER: EXHIBITED_WITH_LOCAL_BUDGET
SCOPE: ABSTRACT
VERIFIER: PAPER
INDEPENDENT_KERNEL_VERIFICATION: false
LEAN_EDIT_PERFORMED: false
NUMERICAL_RUN_PERFORMED: false
ARISTOTLE_SUBMISSION: false
REPOSITORY_WRITE_SCOPE: EXPECTED_VERDICT_DOCUMENT_ONLY
QUEUE_OR_SHARED_STATE_EDIT: false
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
NEGATION_OF_RH_CLAIM: false
```

## 0. Verdict, source boundary and corrections to the request

The identity requested for **all real times**, with the functions literally defined in the pinned paper, is false. The obstruction is not the difficulty of RH: the printed extension to negative time makes the transform vanish on every even compact test. There are explicit such tests with strictly positive Weil form, proved below without any assertion about zeta zeros.

This is a source-definition defect, not a refutation of RH, not a refutation of every intended Suzuki construction, and not a theorem that a zero-free direct calculation is impossible. The request's parenthetical description of the third RESULT is stronger than what is proved: **the exact-counterexample RESULT is used for the literal identity, not for that methodological impossibility claim**.

The calculation does not stop at the defect. Sections 3–5 derive a root-free Volterra formula, compute the norm kernel down to bounded Fourier multipliers, and give its exact distributional remainder. Section 8 specifies a signed-time repair and proves its canonical radical-cutoff check. The repaired global identity remains open; it is not substituted into the request without notice.

I retract my earlier living-chat endorsement of (1.9)/(4.4) as a consistent all-real-time package without first checking this extension.

### Sources actually used

**[S1]** M. Suzuki, *On the Hilbert space derived from the Weil distribution*, arXiv:2301.00421v3, equations (1.1)–(1.9), (2.1), (3.2)–(3.9), Sections 4.1–4.3. The PDF's printed pages 3, 10–12 were inspected, including the negative-time sentence and (4.4)–(4.6).

**[S1J]** The published article, *Canadian Journal of Mathematics*, online 3 November 2025, DOI **10.4153/S0008414X25101739**. Its HTML independently repeats the same negative-time rule after (1.6), and the even extension of P after (3.2). This rules out treating the finding as merely a missing symbol in arXiv's HTML. The published article is CC BY 4.0; source formulas reproduced below are attributed to Suzuki. This audit is not an author-issued erratum.

**[S2]** Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, §2.5, for the distributional convention. We work in distributions on compactly supported tests; no assertion that a merely continuous, potentially exponentially growing function is tempered is needed.

**[R1]** `paper_weil/sections/setup.tex` at `93171b35`, blob `8637e3d973ba689c0cfd5d09a10e2dec3edd3caa`: literal Q, its polarization, c_A, and Fourier conventions.

**[R2]** `paper_weil/sections/groundstate.tex` at that pin, blob `1337eda8882f5e20f649878e3e71262776dff06d`: DOM and its domain.

**[R3]** `paper_weil/sections/canonical.tex` at that pin, blob `fd0c7512e742f504fd3b64736aad5dbaec99ab1f`: f_0, its Fourier identity, cutoff envelopes and radical proof.

**[R4]** `docs/WHY_NOT_YET.md` at that pin, blob `013f210a16af420940f074e3a4e4cd3c31a9f7b7`: admission filter, treated as a research policy to audit, not a mathematical premise.

Other shelf entries and diagnostic numbers are not dependencies of the proof below. Their kernel validation or numerical reproduction is not claimed. All new mathematical results in this verdict are PAPER results, not Lean results and not claims of worldwide novelty. Request bytes alone received the stated independent byte/hash verification; no claim is made to have independently hashed every shelf file.

### Two errors in the request that must not become premises

1. Failure of a proposed RH criterion would not contradict a finite list of verified zeros. Finite numerical evidence cannot establish the universal conclusion. Here the more immediate problem is that the printed criterion and printed definitions are inconsistent.
2. Formula (3.6) is not itself an RH-dependent orthonormal basis theorem. The meromorphic functions and the intended coefficient expansion are introduced in §3. Orthonormality is asserted in **Proposition 4.1**, and it is used in (4.5) and (4.9). The distinction matters below.

## 1. Exact objects and the first decisive counterexample

Use Suzuki's Fourier convention
\[
 \mathsf F_+\psi(z)=\int_{\mathbb R}\psi(t)e^{izt}\,dt,
 \qquad D\psi=i\psi',\qquad
 \langle F,G\rangle_2=\int F(x)\overline{G(x)}\,dx.
\]
Thus inner products are linear in their first argument. Put
\[
 X(z)=\xi(1/2-iz)=\Xi(z),\quad E=X+iX',\quad
 E^\sharp=X-iX',\quad\Theta=E^\sharp/E.
\]
For t >= 0 the source defines
\[
 S_t(z)=\frac{iX(z)}{X(z)-iX'(z)}P_t(z).                 \tag{1}
\]
The pinned PDF then explicitly prescribes, for negative t,
\[
                  S_t(z):=S_{-t}(z).                   \tag{EVEN}
\]
Throughout Sections 1–7, S means this **literal even-time object**. In particular, it does not mean the signed exponential continuation used later in the paper's proof.

The transform in (1.7) is
\[
 \widehat{\mathcal P}_{\phi}(x)=\int_{\mathbb R}
                  \overline{S_t(x)}\phi(t)\,dt.         \tag{2}
\]
Its integrals are well-defined as Bochner integrals for compact smooth phi; Section 3 supplies an independent bound.

### Lemma 1 — parity annihilation [ABSTRACT][PAPER]

For every even psi in C_c^infinity(R;C),
\[
                 \widehat{\mathcal P}_{D\psi}=0.        \tag{3}
\]
**Proof.** The L2-valued function S_t is even in t and psi' is odd. Their product in (2) is integrable and odd. Its integral is zero. No property of the zeros is used. QED.

### Lemma 2 — a strict positive test in an arbitrarily short window [ABSTRACT][PAPER]

Let
\[
 c_A=\gamma_{\!E}+\log(8\pi)+\pi/2,\qquad
 L=\exp[-2(c_A+2)]<\log2,
\]
and define the explicit real even smooth bump
\[
 \psi_L(t)=
 \begin{cases}
 \exp\{-1/[1-(2t/L)^2]\},& |t|<L/2,\\
 0,& |t|\ge L/2.
 \end{cases}                                          \tag{4}
\]
Then
\[
             Q(\psi_L)\ge2\|\psi_L\|_2^2>0.            \tag{5}
\]
**Proof.** In the exact form [R1], all prime correlations vanish: their shifts are >= log2 > L, the diameter of the support. Evenness gives A_+=A_-, so the pole term is nonnegative. For a(t)=e^{-t/2}/(1-e^{-2t}), disjoint supports at t >= L give
\[
 D(\psi_L)\ge2\|\psi_L\|_2^2\int_L^\infty a(t)dt.
\]
For 0<t<=1, 1-e^{-2t}<=2t and e^{-t/2}>1/2, hence a(t)>=1/(4t). Consequently
\[
 2\int_L^\infty a(t)dt\ge\tfrac12\log(1/L)=c_A+2.
\]
Subtracting c_A times the norm proves (5). Smoothness at the boundary is the usual flat exponential-bump calculation. QED.

Combining the two lemmas yields a strict, source-specific discrepancy:
\[
 \boxed{\|\widehat{\mathcal P}_{D\psi_L}\|_2^2
        -\pi Q(\psi_L)\le-2\pi\|\psi_L\|_2^2<0.}        \tag{KILL}
\]
This refutes the literal (1.9), hence the literal all-real (4.4) and (SE'). It also contradicts the claim in Lemma 3.2 that (3.9), with the printed definitions, is a norm on all compact tests.

A second check uses only kernel symmetry. Set R=K_ar-K_norm. By (EVEN), K_norm(t,t)=K_norm(t,-t). Since g is even and g(0)=0,
\[
                    R(t,t)-R(t,-t)=-g(2t).             \tag{6}
\]
The explicit g below is not zero: near zero it equals (1/2)|t|log|t|+O(|t|). Therefore R cannot vanish. The argument is independent of any norm calculation or RH.

**Interpretation:** this diagnoses the mathematical incompatibility of a particular printed extension with the later formulas. It is not a deduction of not-RH from a valid equivalence. The disputed equivalence is precisely what cannot be imported with these literal definitions.

## 2. Requested audit of every RH-dependent stage in Sections 3–4

Equation numbers refer to [S1]/[S1J]. This table distinguishes the intended signed-time argument from the literal source defect.

| Location | Actual use of RH | Classification and audit |
|---|---|---|
| §3.1, (3.2)–(3.4), Prop. 3.1 | None for t>=0 | Unconditional explicit-formula identity; the zero expansion is not a claim of real zeros. The even extension preserves that identity only with folded time. |
| §3.2, Prop. 1.2 proof | None | Existence in ordinary L2 and local-in-t bounds. Cancellation of real-axis poles is local algebra, not RH. A root-free alternative is proved in §3 below. |
| §3.3, (3.5) | None | Defines meromorphic F_gamma, not an orthonormal family without RH. |
| (3.6) | No reality is needed for an appropriately indexed meromorphic expansion | It is incompatible with (EVEN) when interpreted with signed t. With the prefactor i in (1.5), direct conjugation also requires a common minus sign and conjugated zero index; see (19). These are definition/algebra issues, not RH gaps. |
| (3.7), (3.8) | Intended to be unconditional Fourier identities | They integrate signed exponentials. For the printed even-time S they are false: (3) is a counterexample. RH cannot repair this parity mismatch. |
| (3.9), Lemma 3.2 | Intended unconditional nondegeneracy | Literal version fails by (3). A corrected signed transform needs its own proof; no H_0 norm completion is imported here. The closure of any image in ordinary L2 still exists. |
| §4.1, Prop. 4.1 | RH supplies Hermite–Biehler E, inner Theta, and the model-space spectral theorem | Existence of the indicated model/de Branges structure, and **orthonormality/completeness** of F_gamma in that space. This is the substantive geometric input. |
| (4.1), (4.2) | Algebra at a real zero is local and does not assert all zeros real | The formulas Theta'(gamma)/2=-i/m_gamma and F_gamma(gamma)=1/sqrt(pi m_gamma) do not independently give cross-inner-products or completeness. |
| §4.2, (4.3) | None | Defines g by arithmetic. Calling it a screw function on the whole real line, or choosing its positive representing measure tau_xi, does use RH. |
| Coefficient estimate before (4.5) | Real gamma gives bounded exponentials; summability itself does not require RH | Correct RH bound has **4 pi**, not pi, since abs(e^{-i gamma t}-1)<=2. Without RH the bound is pi(e^{abs(t)/2}+1)^2 sum m_gamma/abs(gamma)^2. Neither scalar bound grants orthonormality. |
| (4.5) | Prop. 4.1 removes all cross terms; real gamma makes translations multiply by unit phases | Identity and Hilbert-space convergence. This is the exact step to replace in a corrected proof. Also impossible for literal folded time. |
| (4.6) | None for the convergent paired complex-zero expression on compact t,u sets | An explicit-formula kernel identity; off-axis terms are not modulus squares. Treating it as positive is an additional use of RH. |
| (4.4), Thm. 4.2 | Inherits (4.5) | Intended Gram/arithmetic equality. Its printed all-real version conflicts with (EVEN). |
| (4.7), Cor. 4.3 | Forward direction uses the RH identity; converse uses the cited criterion from the earlier screw-function paper | Diagonal half-line statement, not a way to infer the all-real folded identity. This audit does not refute the independent intended positive-time diagonal criterion. |
| (4.8), (4.9), Thm. 4.4 forward | Orthonormal Parseval from Prop. 4.1 plus the signed coefficient expansion | **The norm becomes a sum of squares here.** This cannot be assumed in a direct arithmetic evaluation. |
| Thm. 4.4 converse | Assumes the proposed equality, then uses a nonreal-zero test to reach contradiction | Conditional implication, not an independent positive-form input. |
| (4.10) | None | Integration by parts relating the derivative kernel form and Weil form; valid independently of Gram equality. |
| Theorem 1.4 proof | D identifies compact smooth tests with compact smooth zero-integral tests; then uses Thm. 4.4 | D's bijection is unconditional. The equality it transports is not. |
| Cor. 1.5 proof, (1.10) | Uses real-zero sampling and the norm identity to identify the form of the output representative | Plancherel supplies factor 2, not preservation of the Weil form. The displayed final chain also confuses input and output norms; the correct chain is in §5. |
| (4.11), Thm. 4.5; Cor. 4.6 | Reuse (1.9) and the stated zero/Li test criterion | No new independent evaluation of the L2 norm. |

This answers §1(a),(b). Since (3.6) uses conjugated basis functions, the corresponding conjugate model space must also be tracked; conjugation preserves the ordinary L2 norm but does not supply orthogonality. No conditional orthonormal basis is used in the following direct calculation. Here “root-free” means no sum over zeros and no assumption about their reality, not an assumption that X has no zeros.

## 3. Explicit S and a direct Volterra/Parseval calculation

### 3.1 Source formula, without zeros

Let psi_d=Gamma'/Gamma and Phi denote the Hurwitz–Lerch function. For t>0, the source's P is
\[
\begin{aligned}
P_t(z)={}&\frac{4(e^{t/2}-1)}{1+2iz}+\frac{4(e^{-t/2}-1)}{1-2iz}\\
&+\frac{e^{-izt}-1}{iz}\frac{\zeta'}{\zeta}(1/2-iz)
+\sum_{n\le e^t}w_n\frac{e^{-iz(t-\log n)}-1}{iz}\\
&-\frac{\psi_d(1/4-iz/2)-\psi_d(1/4)}{2iz}\\
&-\frac{e^{-t/2}}{2iz}
 [\Phi(e^{-2t},1,1/4-iz/2)-\Phi(e^{-2t},1,1/4)].
\end{aligned}                                                        \tag{7}
\]
Removable values are filled by limits. Define g on t>=0 by its literal (4.3):
\[
\begin{aligned}
g(t)={}&-4(e^{t/2}+e^{-t/2}-2)+\sum_{n\le e^t}w_n(t-\log n)
+\frac{c_A t}{2}\\
&-\frac14[\Phi(1,2,1/4)-e^{-t/2}\Phi(e^{-2t},2,1/4)],
\end{aligned}                                                        \tag{8}
\]
and extend g evenly. It is continuous with g(0)=0. Away from prime hinges,
\[
 g'(t)=-4\sinh(t/2)+\sum_{n\le e^t}w_n+\frac{c_A}{2}
       -\frac12e^{-t/2}\Phi(e^{-2t},1,1/4).              \tag{9}
\]
In particular g' belongs to L2 on every compact interval: at zero it grows only logarithmically; at a prime hinge it has a finite jump. For t>=1 the elementary estimate Lambda(n)<=log n gives
\[
 |g'(t)|\le C(1+t)e^{t/2}.                              \tag{10}
\]
No prime-number asymptotic is used.

### Lemma 3 — first-order Volterra identity [ABSTRACT][PAPER]

With h(z)=X'(z)/X(z), for t>=0,
\[
 P_t(z)=h(z)\frac{e^{-izt}-1}{z}
             -\int_0^t e^{-iz(t-r)}g'(r)dr.             \tag{11}
\]
This is an identity of meromorphic functions, with removable values respected.

**Proof.** Apply partial_t+iz to (7). The two pole terms give
`4 sinh(t/2)-1/s-1/(s-1)`, where s=1/2-iz. The zeta term gives `-zeta'/zeta(s)`. Each prime hinge gives `-w_n` after it enters the sum; the boundary term at entry is zero because its numerator vanishes. The digamma and Lerch terms give
`-psi_d(s/2)/2+psi_d(1/4)/2+e^{-t/2}Phi(e^{-2t},1,1/4)/2`.

Using
\[
 ih(z)=\frac1s+\frac1{s-1}-\frac12\log\pi
       +\frac12\psi_d(s/2)+\frac{\zeta'}{\zeta}(s),
\quad \psi_d(1/4)=-\gamma_E-\pi/2-3\log2,
\]
the sum is exactly `-g'(t)-ih(z)`. These differentiations are justified on compact positive-t intervals by the uniformly convergent Lerch series and the locally finite prime sum. Thus
\[
        (\partial_t+iz)P_t=-g'-ih,\qquad P_0=0.
\]
The equation holds almost everywhere in t, across the continuous prime hinges, and g' is integrable at zero. Its integrating-factor solution is (11). Initially avoid the isolated poles in z; meromorphic continuation supplies the full stated identity. QED.

### Lemma 4 — bounded-multiplier L2 representation [ABSTRACT][PAPER]

For real x set
\[
 v(x)=\frac{X(x)}{X(x)-iX'(x)},\qquad
 u(x)=\frac{X'(x)}{X(x)-iX'(x)}.
\]
Both have removable values at common real zeros. Local factorization at a zero of any multiplicity shows v tends to 0 and u tends to i. Hence
\[
              |u|^2+|v|^2=1.                          \tag{12}
\]
For r>=0 put
\[
 a_r(s)=\mathbf1_{(0,r)}(s),\qquad
 b_r(s)=g'(r-s)\mathbf1_{(0,r)}(s),
\quad A_r=\mathsf F_-a_r,\quad B_r=\mathsf F_-b_r.
\]
Here F_- uses exp(-ixs), independently of the plus convention for the original test transform. Then (1),(11) imply
\[
                     S_r=uA_r-ivB_r.                 \tag{13}
\]
Consequently
\[
 \|S_r\|_2\le N(r):=\sqrt{2\pi}
       \left(\sqrt r+\|g'\|_{L^2(0,r)}\right).           \tag{14}
\]
**Proof.** The identity `(e^{-ixr}-1)/x=-i A_r(x)` gives (13). Equation (12), the triangle inequality and Plancherel give (14). Strong L2 continuity of a_r and b_r follows from translation continuity and g' in L2_loc, including their endpoint indicators. Thus S_r is strongly continuous and its norm is bounded uniformly for r in a compact interval. The literal even extension inherits these properties. This proves both L2 existence and the Bochner-integrability needed in (2), without a zero sum or RH. QED.

In addition (10) gives N(r)<=C(1+r)e^{r/2} for r>=1, which will control noncompact canonical tests.

### Lemma 5 — direct evaluation down to explicit Fourier multipliers [ABSTRACT][PAPER]

Define real bounded functions
\[
 \omega=\frac{X^2}{X^2+X'^2}=|v|^2\in[0,1],\qquad
 \eta=\frac{XX'}{X^2+X'^2}=u\bar v\in[-1/2,1/2]
\]
with removable values as above, and for r,s>=0 define
\[
V(r,s)=\frac1\pi\int_{\mathbb R}
 \left[\omega(B_r\overline{B_s}-A_r\overline{A_s})
   +i\eta(A_r\overline{B_s}-B_r\overline{A_s})\right]dx.    \tag{15}
\]
Every product is L1 by Cauchy–Schwarz. Then the **literal** kernel is exactly
\[
        K_{\rm norm}(t,u)=2\min(|t|,|u|)+V(|t|,|u|).     \tag{16}
\]
**Proof.** Multiply (13) by its conjugate at the other time. Replace |u|^2 by 1-omega, and note u bar(v)=eta is real. The resulting integrand is `A_r bar(A_s)` plus (15). Plancherel computes its first integral as `2pi min(r,s)`. Divide by pi and apply (EVEN). QED.

This is the requested direct evaluation attempt. It uses explicit arithmetic g and X, bounded real-axis multipliers and Parseval, with no zeros or RH-dependent basis. It does **not** pretend to have computed the remaining weighted Fourier integrals to the desired translation-invariant kernel.

## 4. Exact distributional remainder, including its nonzero witness

All distributions below belong to D'(R) or D'(R^2), with compact smooth test functions. Fix the finite-part scale by
\[
 \langle\operatorname{Pf}(1/|t|),\varphi\rangle
 =\lim_{\epsilon\downarrow0}
 \left[\int_{|t|>\epsilon}\frac{\varphi(t)}{|t|}dt
             +2\log\epsilon\,\varphi(0)\right].
\]
Directly differentiating (8), with its cusp treated in this convention, gives
\[
\boxed{
 T:=-g''=-\tfrac12\operatorname{Pf}(1/|t|)
 -(\gamma_E+\log(2\pi))\delta_0
 -\sum_{n\ge2}w_n(\delta_{\log n}+\delta_{-\log n})
 +r_*(t)dt,
}                                                                  \tag{17}
\]
where
\[
 r_*(t)=2\cosh(t/2)-a(|t|)+\frac1{2|t|}\quad(t\ne0),
 \qquad r_*(0)=7/4.
\]
The prime sum is locally finite; r_* is locally integrable. Notice the **minus** sign before the finite part and before the prime atoms in T. Their positive sign in DOM is a different, radical-subtracted representation.

**Verification of the delta constant.** The exact explicit-formula archimedean action is
\[
 -c_0\varphi(0)-\int_0^\infty a(t)
 [\varphi(t)+\varphi(-t)-2e^{-t/2}\varphi(0)]dt,
 \quad c_0=\gamma_E+\log(4\pi).
\]
Since
\[
 -2\int_\epsilon^\infty a(t)e^{-t/2}dt
       =\log\tanh(\epsilon/2),
\]
conversion to the displayed finite part leaves coefficient `log2-c_0=-gamma_E-log(2pi)`. Expanding a(t)=1/(2t)+1/4+O(t) gives r_*(0)=7/4. This verifies (17) independently of a verbal sign convention. [S2 §2.5; PAPER calculation here.]

By (16) and
\[
 2\min(|t|,|u|)=2|t|+2|u|-|t-u|-|t+u|,
\]
the precise discrepancy in (SE') is
\[
\boxed{
 \mathcal R:=T(t-u)-\partial_t\partial_uK_{\rm norm}
 =T(t-u)-2\delta(t-u)+2\delta(t+u)
       -\partial_t\partial_u V(|t|,|u|).
}                                                                  \tag{18}
\]
This is an explicit distribution: V is the absolutely defined bounded-multiplier integral (15), not an unspecified error. No unjustified differentiation under the L2 integral has occurred; derivatives are taken distributionally after constructing a continuous kernel.

For a test zeta supported in [-T0,T0]^2 put
`G(2T0)=max_{|r|<=2T0}|g(r)|`. Equations (14) and the anchored arithmetic kernel give the rigorous local budget
\[
 |\langle\mathcal R,\zeta\rangle|
 \le\left(4G(2T_0)+N(T_0)^2/\pi\right)
                \|\partial_t\partial_u\zeta\|_{L^1}.
\]
Both constants are given by the explicit arithmetic functions (8),(9). There is no assumed vanishing rate.

For the particular test `zeta(t,u)=psi_L(t)psi_L(u)`, integration by parts and Lemmas 1–2 give
\[
          \langle\mathcal R,\zeta\rangle
          =Q(\psi_L)-\pi^{-1}\|\widehat{\mathcal P}_{D\psi_L}\|^2
          \ge2\|\psi_L\|^2>0.
\]
Thus the remainder is demonstrably **nonzero**, not merely unestimated. We have computed the folded free-kernel contribution including its anti-diagonal delta. We have not reproduced the target prime atoms from V; writing them explicitly on the target side of (18) does not count as doing so.

## 5. F1, F4, F5 — admission, short windows, exact constants

**F1: ACCEPT the search shape, REJECT the literal identity.** An explicit L2 transform can be a legitimate independent second-expression candidate even when the desired equality is RH-equivalent. The transform's existence is not its isometry. Equivalence alone is not circularity. Here the literal source fails for the separate parity reason proved above. The filter in [R4] cannot overrule this distinction or turn an equivalence into an impossibility theorem.

**F4: NO.** Lemma 2 proves short-window positivity directly, with an explicit lower bound; Lemma 1 proves its literal Suzuki norm is zero. Consequently known positivity on small windows does not establish this particular norm identity. For a separately repaired transform, positivity still only ensures that *some* Gram representation of the restricted form exists, not that this previously fixed transform is isometric. No unconditional repaired short-support isometry has been proved here.

**F5: the dictionary is as follows.**

| Object | Exact relation |
|---|---|
| Centered xi | X(z)=xi(1/2-iz)=xi(1/2+iz)=Xi(z), by the functional equation. |
| Test Fourier transform | Suzuki F_+; project F_-. They are related by z -> -z. The complete zero multiset is symmetric, so diagonal Weil forms agree. |
| Polarization | Suzuki is linear first; project B is antilinear first. Suzuki <psi,v>_W = project B(v,psi). On the diagonal Suzuki <psi,psi>_W = Q(psi). |
| Kernel scale | K_norm=(1/pi)<S_t,S_u>. Thus an actual identity would give norm(P_hat(Dpsi))^2=pi Q(psi), not Q/pi. |
| Prime weights | Each atom of T at +/-log n has weight -Lambda(n)/sqrt(n). The quadratic form has -2w_n C_psi(log n). DOM has +w_n E_s(log n), after subtraction against the radical vector. |
| Archimedean constants | c_0=gamma_E+log(4pi) in the regularized correlation integral; c_A=gamma_E+log(8pi)+pi/2 in the difference energy; delta coefficient in (17) is -(gamma_E+log(2pi)). These are not interchangeable. |
| Mean-prime regrouping | d_A=c_A-4 belongs to the distinct mean-density regrouping in WEILPROOF. It is not the finite-part delta constant or a multiplicative adjustment to (4.4). |
| Compass | (X'+iX)/(X'-iX)=-Theta, by multiplying numerator/denominator by i. Correct but not a norm-identity proof. |

For completeness, if the **corrected** transform identity and its sampling-preservation statement were proved, and `h=F_+^{-1} P_hat(Dpsi_0)`, the legitimate Corollary 1.5 chain would be
\[
 Q(h)=Q(\psi_0)=\pi^{-1}\|\widehat{\mathcal P}_{D\psi_0}\|_2^2
             =\pi^{-1}\|\mathsf F_+h\|_2^2=2\|h\|_2^2.
\]
The first equality requires preservation of the full Weil pairing at the relevant samples; Plancherel supplies only the last equality. The printed proof's substitution of the Fourier norm of the input psi_0 for the output norm is not a valid justification. No scalar factor can repair (KILL), since its left norm is exactly zero.

## 6. F2 — the canonical radical test, with its actual limit

This section separates a direct Bochner-limit proof from an auxiliary zero-expansion audit. **Neither assumes RH.** The latter explicitly uses the entire zero multiset and is not advertised as a zero-free evaluation.

Let f=f_0 from [R3], normalized by F_+f=X/A with A>0. Fix q and the even smooth chi_R of that source. The derivative envelopes give
\[
 |f^{(j)}(t-q)|\le M_j e^{-a_qe^{2|t|}},\quad j=0,1,2,
 \qquad a_q=(\pi/2)e^{-2|q|}.
\]
By (14), the literal output on psi_R=chi_R U_qf converges in L2 to
\[
 L_q(x):=\int_{\mathbb R}\overline{S_{|t|}(x)}\,i f'(t-q)dt.
\]
The exact sufficient error budget is
\[
 \|\widehat{\mathcal P}_{D\psi_R}-L_q\|_2
 \le(M_1+2M_0)\int_{|t|\ge R}
        N(|t|)e^{-a_qe^{2|t|}}dt\longrightarrow0.        \tag{19}
\]
**Proof.** Differentiate chi_R f(t-q), subtract f'(t-q), use abs(chi'_R)<=2, then Minkowski and (14). The integrand is integrable by (10) and the double-exponential envelope. Dominated convergence gives the limit. QED.

For q=0 the output is identically zero by parity. That check is vacuous: every even test passes it, not just the canonical radical vector.

### Lemma 6 — some translated radical cutoffs fail F2 for literal S [ABSTRACT][PAPER]

There exists a real q for which `||L_q||_2>0`. Thus F2 as quantified over all translates is false for the printed even-time object.

**Proof.** We may use the unconditional positive-time identity of Prop. 3.1,
\[
 P_r(z)=\sum_\gamma m_\gamma
           \frac{e^{-i\gamma r}-1}{\gamma(z-\gamma)},\quad r\ge0,
 \qquad\sum_\gamma m_\gamma/|\gamma|^2<\infty,
\]
with all zeros, not assumed real. For fixed real x away from zeros and x!=0, put
\[
 j_\gamma(q)=\int\sin(\gamma|t|)f(t-q)dt.
\]
The cosine part and the constant part vanish when integrated against f'(t-q), because F_+f(gamma)=0. Therefore the literal definition gives
\[
 L_q(x)=-\frac{iX(x)}{E(x)}
       \sum_\gamma\frac{m_\gamma j_\gamma'(q)}{\gamma(x-\gamma)}.
                                                               \tag{20}
\]
The following estimates justify the calculation and the Fourier transform in q. Since abs(Im gamma)<1/2, abs(sin(gamma t))<=e^{|t|/2}. For q>=0, vanishing of the full exponential samples gives
`j_gamma(q)=-2 int_{t<0} sin(gamma t) f(t-q)dt`; for q<=0 use the other half-line. The same formula differentiated in q bounds j_gamma' by a double-exponential tail, uniformly in gamma, in L1(dq). The coefficients in (20) are bounded by a constant times m_gamma/|gamma|^2 apart from finitely many terms. Hence all indicated interchanges are absolutely justified.

Distributionally,
\[
 j_\gamma''+\gamma^2 j_\gamma=2\gamma f,
 \quad
 \mathsf F_qj_\gamma(r)=\frac{2\gamma X(r)}{A(\gamma^2-r^2)}.
\]
At real zeros the quotient is removable. Pairing gamma and -gamma in the logarithmic derivative of the even order-one function X gives
\[
 \sum_\gamma\frac{m_\gamma}{(\gamma^2-r^2)(x-\gamma)}
 =\frac{h(x)-x h(r)/r}{x^2-r^2},\qquad h=X'/X.
\]
Thus the Fourier transform of (20), initially off the removable exceptional points, is
\[
 \boxed{\mathsf F_q L_{\bullet}(x)(r)
 =\frac{2X(x)}{A E(x)}
       \frac{xX'(r)-r h(x)X(r)}{x^2-r^2}.}              \tag{21}
\]
This cannot vanish identically in r. Otherwise
`xX'(r)=r h(x)X(r)`, and the differential equation implies
`X(r)=X(0) exp(h(x)r^2/(2x))` everywhere by analyticity. This contradicts X being nonconstant of order one: a nonzero quadratic exponential has order two, and a zero coefficient gives a constant.

A source-defined allowed x is
\[
 x_0=\tfrac12\sqrt{\frac{\int f(t)dt}{\int t^2f(t)dt}}>0.
\]
The inequality cos u>=1-u^2/2 proves X(x_0)>=7X(0)/8>0. Hence (21) is a nonzero Fourier transform for x=x_0, so L_q(x_0)!=0 for at least one q. The uniform convergence of (20) on a real x-neighborhood away from zeros gives continuity there. Therefore L_q is nonzero on a set of positive measure and has positive L2 norm. Equation (19) proves failure of the required zero limit for that q. QED.

This is not a contradiction with the project radical theorem: that theorem concerns Q, whereas literal P_hat is not isometric for Q. Section 8 proves the radical check for an explicitly different, signed-time repair; these two objects must not be merged.

## 7. F3 — exact nonreal-zero plants and the step they prohibit

One cannot replace X by an arbitrary H while keeping the old zeta prime formula unchanged. That would compare unrelated objects. For these explicit even order-one plants, with known zeros gamma in a bounded horizontal strip, use the consistent definitions
\[
 g_H(t)=\sum_\gamma m_\gamma\frac{\cos(\gamma t)-1}{\gamma^2},\quad
 P^H_t(z)=\sum_\gamma m_\gamma\frac{e^{-i\gamma t}-1}{\gamma(z-\gamma)},\quad
 S^H_t=\frac{iH}{H-iH'}P^H_t,
\]
with paired sums where required, and
\[
 Q_H(v)=\sum_\gamma m_\gamma\widehat v(\gamma)
                              \overline{\widehat v(\bar\gamma)}.
\]
The sums for g_H and P^H converge locally, since sum m_gamma/abs(gamma)^2 is finite. These definitions use the explicit zeros of the plants, not hypothetical locations of zeta zeros. If a proposed L2 norm is undefined, the analogy already fails at existence; whenever it is defined, the following negative values exclude isometry. This is sufficient to test the asserted identity, without falsely assigning zeta's prime terms to another function.

### A compact interpolation lemma [ABSTRACT][PAPER]

If H is the plus Fourier transform of h in C_c^infinity and H(alpha)=0, then H(z)/(z-alpha) is also the transform of a compact smooth function. An explicit inverse is
\[
 u(t)=-i e^{-i\alpha t}\int_{-\infty}^t e^{i\alpha s}h(s)ds.
\]
It is compact because the total integral H(alpha) is zero. Direct differentiation gives `(i partial_t-alpha)u=h`. This proves the claim without an unproved localization assumption.

**Plant 1.** Take H_1(z)=(1+16z^2)cos(8z), delta=i/4, and any nonzero even nonnegative compact smooth bump b with B=F_+b. Then B(delta)>0. The function Z=H_1 B is the transform of a compact smooth function: polynomial factors give derivatives and exponentials give shifts. Define
\[
 V(z)=Z(z)\left[
 \frac{1}{Z'(\delta)(z-\delta)}
 -\frac{1}{Z'(\bar\delta)(z-\bar\delta)}\right].          \tag{22}
\]
The preceding lemma proves V=F_+v for a compact smooth v. It has V(delta)=1, V(bar(delta))=-1 and vanishes at every other zero of H_1. Consequently its canonical full zero-side Hermitian form is exactly
\[
                  Q_{H_1}(v)=-2.                     \tag{23}
\]
All terms except the conjugate pair vanish, so no tail estimate is needed.

**Plant 2.** One explicit admissible choice in H_2=B(z)(2+cos4z) is
\[
 B(z)=\prod_{j=1}^\infty\operatorname{sinc}(2^{-j}z).
\]
This is the Fourier transform of the probability distribution of the sum of independent uniform variables on [-2^{-j},2^{-j}]. The distribution is supported in [-1,1]. The product converges locally uniformly, and on the real line its first k factors bound it by C_k(1+|x|)^{-k} for every k. Fourier inversion therefore gives an even nonnegative C_c^infinity density. The product has only real zeros, since each factor does and uniform convergence plus the nonzero value at zero prevents extra nonreal zeros.

Now delta=(pi+i arcosh2)/4 is a simple nonreal zero of H_2 in the strip, and B(delta)!=0. H_2 itself is a compact smooth Fourier transform. Taking Z=H_2 in (22) produces a compact test with
\[
                  Q_{H_2}(v)=-2.                     \tag{24}
\]
Thus no positive L2 Gram representation can equal these canonical pairings on all tests.

**The exact obstructed step:** on evaluations at delta and bar(delta), the Weil pairing has matrix `[[0,1],[1,0]]`; vector (1,-1) has value -2. An ordinary Gram matrix is positive semidefinite. Replacing the crossed conjugate-zero pairing by the diagonal Parseval metric is precisely the forbidden step behind (4.5)/(4.9) without the real-zero geometry. This is an explicit plant, not a theorem that every contour or arithmetic proof must mention zeros.

The literal even-time construction has the additional defect of failing a true positive short-support test (Lemma 2). It therefore fails *before* it can serve as an RH-sensitive discriminator. The plant obstruction and the parity defect are distinct.

## 8. Explicit repair, what it proves, and the remaining computation

The smallest natural repair compatible with the positive-time source and signed exponential expansion is, for t>0,
\[
 P^{\rm sgn}_{-t}(z)=P_t(-z),\qquad
 S^{\rm sgn}_t(z)=\frac{iX(z)}{X(z)-iX'(z)}P^{\rm sgn}_t(z).
                                                               \tag{25}
\]
Equivalently `S^{sgn}_{-t}(z)=Theta^sharp(z) S_t(-z)`. Set P^{sgn}_t=P_t for t>=0; positive times are unchanged. **This is a proposed repair, not the literal source and not an author-confirmed correction.**

It agrees for every signed t with
`P^{sgn}_t(z)=sum_gamma m_gamma(e^{-i gamma t}-1)/(gamma(z-gamma))`, by the unconditional positive-time identity and the symmetry gamma -> -gamma. With the source's prefactor i, the correctly conjugated (3.6)-type expansion is
\[
 S_t^{\rm sgn}(z)=-\sum_\gamma\sqrt{\pi m_\gamma}
          \frac{e^{-i\bar\gamma t}-1}{\bar\gamma}F_\gamma^\sharp(z).
                                                               \tag{26}
\]
The common minus sign has no effect on Gram norms; the time orientation and conjugation do. None of this asserts orthogonality of F_gamma.

### Repaired radical check [ABSTRACT][PAPER]

The estimate (19) applies to the repaired transform as well: its negative-time Volterra representation has the same N(abs(t)). For a fixed real x away from the discrete exceptional set, the unconditional exponential series may be integrated against f'(t-q), by the exponential coefficient bound and the double-exponential envelope. Every term is zero because
\[
 \int(e^{i\gamma t}-1)f'(t-q)dt
   =-i\gamma e^{i\gamma q}X(\gamma)/A=0.
\]
The Bochner integral is thus zero almost everywhere in x. Therefore
\[
 \boxed{\|\widehat{\mathcal P}^{\rm sgn}_{D(\chi_R U_qf_0)}\|_2
 \le\epsilon_{q,R}\longrightarrow0\quad\text{for every fixed q},}
                                                               \tag{27}
\]
where epsilon_{q,R} is exactly the right side of (19).

This proves a genuinely unconditional necessary check for the **repaired** object. It uses the unconditional zero expansion and the exact canonical Fourier identity, with no reality assumption and no RH basis. It is not the requested zero-free computation of the whole Gram kernel, and it is not counted retrospectively as success of literal F2.

### Root-free remainder for the repaired object

There is also a signed Volterra representation not involving zeros. In (13) use
\[
 a_t(r)=\operatorname{sgn}(t)\mathbf1_{(\min(0,t),\max(0,t))}(r),
 \quad b_t(r)=g'(t-r)a_t(r),
\]
with zero functions at t=0. Formula (11), interpreted with oriented integration, proves it directly. Define A_t,B_t and V_sgn by (15) with these signed functions. Plancherel now gives
\[
 K_{\rm norm}^{\rm sgn}(t,u)
       =|t|+|u|-|t-u|+V_{\rm sgn}(t,u),
\]
so the remaining mixed-derivative target is exactly
\[
 \boxed{\partial_t\partial_u V_{\rm sgn}(t,u)
                =T(t-u)-2\delta(t-u)\quad\text{in D'(R^2)}.}      \tag{OPEN}
\]
All quantities on both sides are explicitly defined above; V_sgn has the same local distributional budget as in §4. The spurious anti-diagonal delta from folded time is gone.

The unproved step is to evaluate the omega- and eta-weighted Fourier products in V_sgn to **all** the finite-part, prime and regular terms on the right. Positivity of the Gram expression alone does not do this. A contour closure using analyticity/contractivity of Theta in an entire half-plane would reintroduce the missing real-zero input unless independently established.

No partial reproduction of the prime-atom component from V_sgn has been proved here. The positive-time Volterra identity, the free Gram part and (27) are proved; (OPEN) remains the precise analytic remainder, not a new assumed supplier. An exact second-expression mechanism remains worth investigating, but (25) must first be acknowledged as a source repair.

## 9. Prediction scoring, independent checks and scope closeout

The registered probabilities and event wording are not changed. Batch non-achievement is not described as a mathematical impossibility.

| Registered event | p | Fate | Reason |
|---|---:|---|---|
| P_SEB_COMPLETE: (SE') proved without RH | 0.02 | REFUTED_AS_BATCH_OUTCOME | Literal (SE') is contradicted by (KILL). The repaired version is not proved. |
| P_SEB_PRIME_ATOMS_REPRODUCED: prime atoms obtained from the norm kernel | 0.35 | NOT_ESTABLISHED | The target atoms in (17) are computed, not obtained from the weighted Gram remainder. |
| P_SEB_RADICAL_CHECK_PROVED: F2 proved from P_hat | 0.55 | REFUTED_FOR_LITERAL_OBJECT | q=0 is a parity zero; Lemma 6 proves failure for some translated cutoffs. Equation (27) belongs to the explicitly repaired object. |
| P_SEB_YOSHIDA_SUBCLASS_THEOREM: F4 yields the stated short-support isometry | 0.30 | REFUTED | The strictly positive short-support bump has literal norm zero. Positivity survives; isometry does not. |
| P_SEB_RH_STEP_LOCATED | 0.85 | CONFIRMED | Prop. 4.1 -> (4.5)/(4.9), with existence, convergence and identity roles separated in §2. |
| P_SEB_RESULT_REFUTED: theorem that direct computation cannot avoid zeros | 0.25 | NOT_ESTABLISHED | No such methodological impossibility is proved. Literal refutation is a different event and is not credited to this prediction. |

Before any independent check of the present derivations, register:
```yaml
P_SEB_INDEPENDENT_PARITY_WITNESS:
  probability: 0.98
  event: literal_even_time_rule_and_short_support_witness_survive_independent_check
  fate: PENDING
P_SEB_INDEPENDENT_VOLTERRA_GRAM_SIGNS:
  probability: 0.82
  event: equations_11_13_16_18_require_no_change_of_constants_or_signs
  fate: PENDING
P_SEB_INDEPENDENT_TRANSLATED_RADICAL_REPAIR:
  probability: 0.75
  event: equations_21_and_27_survive_independent_check_with_their_distinct_time_rules
  fate: PENDING
```
These are predictions for future checking, not claims that checks have occurred. No numerical experiment or Lean compilation was run in this adjudication.

### One bounded directive

Independently check the **negative-time convention** against the pinned PDF and journal, then check Lemmas 1–2 and the signed repair (25). Do not import Theorem 1.4/(4.4) as an all-real-time theorem until the convention is repaired. If proceeding with the repaired object, retain the exact (OPEN) target and the cutoff check (27); do not reinstate the even extension, a positive Gram assumption on the Weil form, or the RH orthonormal basis. This directive proposes a read-only mathematical verification, not a paid call, Lean edit, new queue entry or communication to the paper's author.

### Closeout

- **What was refuted:** the literal even-time all-real kernel identity, with a strict analytic witness.
- **What was computed:** the root-free first-order equation and Volterra solution; bounded-multiplier L2 representation; free Gram kernel and the exact local distributional remainder.
- **What was repaired explicitly:** signed negative times, with unconditional annihilation of canonical translated cutoffs for that different object.
- **What remains open:** (OPEN), the exact weighted Fourier calculation for the signed-time object. No universal no-method theorem and no RH conclusion is claimed.
- **What must not recur:** quote a theorem number while overlooking an incompatible definition; identify positivity with a prescribed isometry; claim finite verified zeros refute the possibility of not-RH; score a different event as the frozen prediction's success.
- **Repository action:** only this verdict at EXPECTED_VERDICT_PATH. The request, paper, Lean files, skills, prior verdicts and shared state remain untouched. The commit and file digest are returned separately after readback; the file cannot contain its own commit identifier recursively.

## 10. Readback clarification — 2026-09-06 (append-only)

Two local clarifications to the first committed text, without changing its source finding, counterexample, or prediction fates:

1. In the §2 table, the cross-reference in the (3.6) row should point to equation **(26)**, not (19).
2. In §8, the phrase about the same distributional budget as §4 applies to the **full signed discrepancy**
   `R_sgn = T(t-u) - partial_t partial_u K_norm^{sgn}`.
   Precisely, for zeta supported in [-T0,T0]^2,
   \[
   |\langle R_{\rm sgn},\zeta\rangle|
   \le(4G(2T_0)+N(T_0)^2/\pi)\|\partial_t\partial_u\zeta\|_1.
   \]
   For the derivative of V_sgn alone the directly justified budget is instead
   \[
   |\langle\partial_t\partial_u V_{\rm sgn},\zeta\rangle|
   \le(N(T_0)^2/\pi+2T_0)\|\partial_t\partial_u\zeta\|_1,
   \]
   because `0 <= |t|+|u|-|t-u| <= 2T0` on that square. No bound for V_sgn alone by the former constant is asserted. The proof of (27) and the unproved identity (OPEN) are unchanged.
