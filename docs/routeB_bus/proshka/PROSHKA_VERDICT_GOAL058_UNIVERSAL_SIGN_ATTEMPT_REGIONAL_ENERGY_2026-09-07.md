# STATUS: TRY_REGIONAL_ENERGY_SIGNED_MEAN_WITH_UNIVERSAL_HEAD_OPEN
```yaml
OPERATIVE_CLASS: TRY_REGIONAL_ENERGY_SIGNED_MEAN_WITH_UNIVERSAL_HEAD_OPEN
PRIMARY_COUNT: 1
TASK: OWNER_DIRECT_PROOF_FOLLOWUP_TO_REQ_2026_09_07_CHAIN
ORIGINAL_GOAL: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
ORIGINAL_GOAL_FORMULA: S_n(1/n)_positive_semidefinite_for_every_integer_n_ge_1
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
UNIVERSAL_SIGN_PROVED: false
UNIVERSAL_SIGN_REFUTED: false
TARGET_WEAKENED_AND_DECLARED_CLOSED: false
NEW_RESULTS:
  REGIONAL_LOG_ENERGY_EXACT_LEGENDRE_DIAGONALIZATION: PROVED_PAPER
  THREE_INDEPENDENT_LOBES_TOTAL_POLE_NULL_WEIL_FLOOR: PROVED_PAPER
  THREE_LOBE_LOWER_BOUND: 1/5_times_L2_norm_squared
  EXACT_RATIONAL_BUDGET: 9579/40000
  LOSSLESS_LOCALIZATION_PROPAGATION: REFUTED_THEOREM_SHAPE
  SOURCE_LOCALIZATION_DEFECT_IDENTITY: PROVED_PAPER
  REGULARIZER_MONOTONICITY_PROVES_TARGET: false
PARENT_LOCK:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: f47ed55c78f6d6964d05218d710f71e2cacc769d
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_FULL_CHAIN_TO_WEIL_2026-09-07.md
  GIT_BLOB: bf4a0cea683c524accde2b90d96a8ebd8b6bc815
  SHA256: 896995b0b1c12278b14540ea9cd0f63c8e1ef326afd2bb7728a67c09f90b0da0
  BYTES: 53180
  LINES: 684
  LOCAL_BYTES_HASHED_THIS_TURN: true
  CONNECTOR_PINNED_BLOB_MATCH: true
  ROLE: exact_source_form_and_target_not_assumed_global_sign
BOOTSTRAP:
  REF: rh_clean
  PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
  GIT_BLOB: eba04b799176c9e6a1d5f7fc4061280cfbf96ad4
CLOSES:
  - CHAIN_equation_C22_fixed_three_lobe_total_pole_null_floor_at_PAPER_level
OPENS: []
CLOSES_ANALYTIC_RH_SUPPLIERS: []
UNCHANGED_OPEN_ATOM: ALL_SUPPORT_SIGNED_SCHUR_HEAD_LOWER_BOUND
VERIFICATION:
  NEW_DERIVATIONS_SCOPE: ABSTRACT
  NEW_DERIVATIONS_VERIFIER: PAPER
  INDEPENDENT_REVIEW: pending
  LEAN_KERNEL_VERIFIED: false
  SOURCE_OPERATOR_NUMERICAL_EXPERIMENT: false
  INTERVAL_CERTIFICATE_RUN: false
  EXACT_RATIONAL_BUDGET_CHECK: Python_Fraction_no_floating_point
  OLD_CERTIFICATE_RERUN: false
PUBLICATION:
  PATH: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_UNIVERSAL_SIGN_ATTEMPT_REGIONAL_ENERGY_2026-09-07.md
  NEW_ARTIFACT_ONLY: true
  PARENT_VERDICT_OVERWRITTEN: false
  COMMIT_AND_READBACK_BLOB: delivery_receipt
  RECEIPT_IS_NOT_INDEPENDENT_MATHEMATICAL_VALIDATION: true
ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
RH_CLAIM: false
```

## 0. Result and the attempted universal proof

The requested all-support sign is **not proved in this attempt**. It has not been replaced by a local theorem and marked complete. The new local theorem below repairs the first exact obstruction exposed in CHAIN: its three-lobe target (C22) is proved, with a stronger constant 1/5 instead of 1/100, on the whole declared infinite-dimensional space. No smallness assumption is imposed on the previously free mean direction.

The attempted extension to arbitrary supports does not close. An exact localization calculation identifies the term that would have to be controlled. The proposed lossless version is refuted on the actual geometric source form, not just on a random indefinite matrix. This refutes that propagation rule, not the universal sign itself. Decreasing the Schur regularizer does not supply a second propagation mechanism: its exact derivative has the opposite useful direction.

The main mathematical work is Sections 2--6. The universal boundary and the unsuccessful propagation are Sections 7--8. The paper derivations have been checked internally, including exact rational arithmetic, but have not been independently reviewed or checked by Lean. No historical novelty claim is made.

**Source basis.** [CHAIN] means the pinned document in the header, read in full, especially (C1), (C2), (C10)--(C22). The local bytes match its connector blob and the recorded SHA-256. The task is the owner's explicit continuation asking to prove that target; no new queue request has been invented. The current bootstrap was fetched through GitHub. The classical digamma conventions were checked against NIST DLMF 5.4 and 5.7.6. The published Weil test-class implication was checked in Connes--Consani, arXiv:2006.13771v1, Introduction (1)--(2) and Appendix C. Those references are not global positivity suppliers.

The following sources were consulted as primary sources, not as substitutes for the pinned definitions:

- NIST DLMF, §5.4, special values of the digamma function; §5.7.6, its difference series.
- Connes--Consani, *Weil positivity and Trace formula, the archimedean place*, arXiv:2006.13771v1, Introduction and Appendix C.

The regional integral-operator identity used below is proved here rather than imported under an unverified theorem name.

## 1. The unchanged source form and the local claim

Let
\[
 A(t)=\frac{e^{-t/2}}{1-e^{-2t}},\quad
 c_A=\gamma_E+\log(8\pi)+\frac\pi2,\quad
 w_k=\frac{\Lambda(k)}{\sqrt k},\quad U_tf(x)=f(x-t).
\]
For a complex compact smooth function define
\[
 C_f(t)=\Re\int\overline{f(x)}f(x+t)\,dx,\qquad
 M_\pm(f)=\int f(x)e^{\pm x/2}\,dx,
\]
\[
 \boxed{\mathcal Q(f)=\mathcal D(f)-c_A\|f\|^2
 -2\sum_{k\ge2}w_k C_f(\log k)
 +2\Re\{M_+(f)\overline{M_-(f)}\},\quad
 \mathcal D(f)=\int_0^\infty A(t)\|U_tf-f\|^2dt.} \tag{U1}
\]
This is exactly [CHAIN, (C1)]. All integrals use Lebesgue measure in the logarithmic coordinate. Inner products are antilinear in the first variable. The prime-power sum is finite on a fixed compact support.

Set
\[
 a=\log2,\quad b=\log3,\quad
 \delta=\frac{b-a}{8},\quad I=(-\delta,\delta),\quad d=\frac{13}{125},
 \quad J=(-d/2,d/2).
\]
The following statement is local; it is not the statement that every S_n has the required sign.

**Theorem U1 (the three-profile repair).** For arbitrary complex
\(h_0,h_1,h_2\in C_c^\infty(I)\), put
\[
 v=h_0+U_a h_1+U_b h_2.
\]
If only the two **total** conditions \(M_+(v)=M_-(v)=0\) hold, then
\[
 \boxed{\mathcal Q(v)\ge\frac{9579}{40000}
       \sum_{i=0}^2\|h_i\|^2
       >\frac15\|v\|^2\quad(v\ne0).} \tag{U2}
\]
For v=0 use the non-strict inequality with 1/5. The lobes are disjoint, so the two norms in (U2) agree. Separate pole-nullity, evenness, a common envelope and any phase relation between the profiles are **not** hypotheses. [ABSTRACT][PAPER]

The support geometry is part of the proof. One has 2δ<d<1, d<b-a, and d<2a-b=log(4/3). Hence all three lobes are disjoint; the only active prime-power atoms are 2 between the first and second lobes and 3 between the first and third lobes. The lag b-a has an archimedean mixed term but no prime atom. Atoms k≥4 lie beyond the whole support diameter b+d<log4. No mixed entry is silently removed.

## 2. The energy that the previous coarse bound discarded

### 2.1 An exact regional integral identity

For a polynomial h on J define
\[
 (\mathscr L_J h)(x)=\int_J\frac{h(x)-h(y)}{|x-y|}\,dy.
\]
There is no principal-value ambiguity for a polynomial: the numerator cancels the diagonal singularity. Let ℓ_j be the L2(J)-orthonormal Legendre polynomials, with ℓ_0=d^{-1/2}, and put
\(\mathfrak h_0=0\), \(\mathfrak h_j=\sum_{r=1}^j1/r\).
Then
\[
 \mathscr L_J\ell_j=2\mathfrak h_j\ell_j,\qquad
 \int_{y<x\in J}\frac{|h(x)-h(y)|^2}{2(x-y)}\,dx\,dy
 =\sum_{j\ge1}\mathfrak h_j|\langle\ell_j,h\rangle|^2.
 \tag{U3}
\]
In particular,
\[
 \boxed{\int_{y<x\in J}\frac{|h(x)-h(y)|^2}{2(x-y)}dxdy
 \ge\|h\|^2-\frac{|\int_Jh|^2}{d}.} \tag{U4}
\]

**Proof.** Scaling J to [-1,1] leaves the integral operator unchanged. On that interval direct polynomial division gives
\[
 \mathscr L(x^j)=2\mathfrak h_j x^j
 -\sum_{r=0}^{j-1}\frac{1+(-1)^{r+1}}{r+1}x^{j-1-r}.
\]
Thus the operator preserves polynomial degree and has leading multiplier 2\mathfrak h_j. It is symmetric, since
\[
 \langle f,\mathscr L g\rangle
 =\frac12\iint\frac{\overline{f(x)-f(y)}(g(x)-g(y))}{|x-y|}dxdy.
\]
Orthogonality and triangularity therefore make the jth Legendre polynomial an eigenvector: all lower coefficients of \(\mathscr L\ell_j\) vanish when paired with lower-degree polynomials. The quadratic identity follows by expansion; its factor 1/2 relative to \(\langle h,\mathscr L h\rangle\) is important. Since \(\mathfrak h_j\ge1\) for j≥1, (U4) follows.

For smooth h, approximate in C1(J) by polynomials. This can be obtained by uniformly approximating h' and integrating, then matching one value. For the difference r between two such approximants, \(|r(x)-r(y)|\le\|r'\|_\infty|x-y|\); hence its regional energy tends to zero. Polynomial diagonality identifies the completion with the weighted coefficient space and proves (U3) there. Norms and means also converge. Apply to the real and imaginary parts, or directly to complex coefficients. This justifies (U3)--(U4) for the required tests without assuming any positivity of the Weil form. QED. [ABSTRACT][PAPER]

**Exact controls.** A constant h has zero regional energy, so omitting the mean subtraction in (U4) would be false. For h(x)=x on the centered interval J, the mean is zero and both sides of (U4) equal d³/12. Thus the constant 1 in (U4) is attained and cannot be replaced by 2. These controls check the null direction and the factor of two independently of the later Weil budget.

### 2.2 Exterior energy and the actual local floor

For h zero-extended from J, write
\[
 \beta_J(x)=\int_{x+d/2}^{\infty}A(t)dt+
                 \int_{d/2-x}^{\infty}A(t)dt.
\]
Splitting both points of a translated difference according to whether they lie in J gives the exact identity
\[
 \mathcal D(h)=\int_{y<x\in J}A(x-y)|h(x)-h(y)|^2dxdy
                 +\int_J\beta_J(x)|h(x)|^2dx. \tag{U5}
\]
The exterior term contains both boundary contributions; it is not discarded. Because A decreases, β_J has its minimum at the midpoint, and
\[
 \beta_J(x)\ge2\int_{d/2}^{\infty}A(t)dt.
\]
For 0<t≤d<1,
\[
 A(t)=\frac{e^{t/2}}{2\sinh t}\ge\frac1{2t}.
\]
Indeed \(\sinh(t)/t\le\cosh t\le e^{t^2/2}\le e^{t/2}\); the middle inequality follows by integrating tanh t≤t. The exact constants below show
\[
 2\int_{d/2}^{\infty}A(t)dt-c_A>\frac12. \tag{U6}
\]
Combining (U4)--(U6),
\[
 \boxed{\mathcal D(h)-c_A\|h\|^2
 \ge\frac32\|h\|^2-\frac{|\int_Jh|^2}{d}.} \tag{U7}
\]

The mechanism is not an extra assumed floor. An exact nonnegative remainder for (U7) is
\[
\begin{split}
 &\sum_{j\ge2}(\mathfrak h_j-1)|\langle\ell_j,h\rangle|^2\;+
 \int_{y<x}\left(A(x-y)-\frac1{2(x-y)}\right)|h(x)-h(y)|^2dxdy\\
 &\hspace{25mm}+\int_J\left(\beta_J(x)-c_A-\frac12\right)|h(x)|^2dx.
\end{split} \tag{U8}
\]
All three terms are nonnegative by the just-proved statements. The mean is the one direction not charged by the regional energy, and remains explicit. [ABSTRACT][PAPER]

### 2.3 Rational proof of the boundary constant

Elementary integration gives
\[
 2\int_{d/2}^{\infty}A(t)dt-c_A
 =\log\frac{\coth(d/8)}{8\pi}-\gamma_E-\arctan(\sinh(d/4)).
\]
Use coth x>1/x and π<22/7 to bound the logarithm below by log(875/286)>111/100. Also
\(\sinh(13/500)\le(13/500)/(1-(13/500)^2)<27/1000\).
Finally γ_E<29/50. A complete short justification of the latter is
\[
 \gamma_E<H_4-\log(9/2)=25/12-\log(9/2)<29/50.
\]
The first inequality follows by integrating the strictly convex function 1/x on unit intervals centered at the integers and then taking the limit defining γ_E. The second follows from log(9/2)>451/300. For x>1 all logarithm lower bounds used here follow from
\[
 \log x=2\sum_{j\ge0}\frac{z^{2j+1}}{2j+1},\quad z=(x-1)/(x+1).
\]
Three terms suffice for x=875/286 and seven for x=9/2. These are strict rational comparisons. Hence the left side of (U6) exceeds
\(111/100-29/50-27/1000=503/1000>1/2\).

For reference the elementary bounds 2/3<a<7/10 and 1<b<11/10 follow from the same series, bounding the remaining positive tail geometrically. Also log(3/2)<2(1/5+(1/5)^3/[3(1-1/25)])<52/125 proves 2δ<d. No rounded decimal from an operator computation enters these inequalities.

## 3. All cross terms, including the lag without a prime

Write
\[
 m_i=\int_Jh_i,\quad \mu_i=m_i/\sqrt d,\quad
 g_i=h_i-\mu_i d^{-1/2}1_J,
 \quad H=\sum_i\|h_i\|^2=\|\mu\|^2+\sum_i\|g_i\|^2.
\]
Thus each g_i has zero ordinary mean. It need not have zero pole moments.
Let
\[
 \Pi=\begin{pmatrix}0&-a/\sqrt2&-b/\sqrt3\\
                    -a/\sqrt2&0&0\\-b/\sqrt3&0&0\end{pmatrix}.
\]
The prime contribution is exactly the L2-valued quadratic form h*Πh. It splits without a mixed mean/mean-zero term:
\[
 h^*\Pi h=\mu^*\Pi\mu+g^*\Pi g,
 \quad g^*\Pi g\ge-\sqrt{a^2/2+b^2/3}\,\|g\|^2
 \ge-\frac{81}{100}\|g\|^2. \tag{U9}
\]
Here a²/2+b²/3<(7/10)²/2+(11/10)²/3=389/600<(81/100)².

For centers x_0=0,x_1=a,x_2=b, the exact archimedean cross contribution is
\[
 -2\Re\sum_{i<j}\iint_{J^2}
 A(x_j-x_i+y-x)\overline{h_i(x)}h_j(y)dxdy.
\]
(The simultaneous interchange of x,y gives the other common orientation, with the same estimates.) Replace A in each entry by its value at the exact center difference, retaining the error. Then its mean part is
\(-2d\sum_{i<j}A(x_j-x_i)\Re(\overline\mu_i\mu_j)\).
The absolute error is at most
\[
 2\sum_{i<j}e_{ij}\|h_i\|\|h_j\|,\quad
 e_{ij}=d^2\sup_{|u-(x_j-x_i)|\le d}|A'(u)|.
\tag{U10}
\]
No term at b-a is dropped.

We have the outward rational bounds
\[
 e_{01}<1/50,\qquad e_{02}<1/100,\qquad e_{12}<7/100.
\]
The symmetric error matrix consequently has norm less than 9/100, so the total absolute error is at most (9/100)H.

Here are full elementary derivative bounds. The expansion A(t)=Σ_{j≥0}e^{-(2j+1/2)t} shows that |A'| is decreasing. Moreover
\[
 |A'(t)|=\frac{e^{-t/2}}{1-e^{-2t}}
          \left(\frac12+\frac{2e^{-2t}}{1-e^{-2t}}\right).
\]
Use e^{d/2}≤250/237 and e^{2d}<5/4; the latter follows from log(5/4)>2/9>2d. At the lower endpoints a-d,b-d,b-a-d these give, respectively,
\[
 |A'(a-d)|\le\frac{250}{237}\frac57\frac{16}{11}\frac{31}{22}<\frac85,
\]
\[
 |A'(b-d)|\le\frac{250}{237}\frac35\frac{36}{31}\frac{51}{62}<\frac23,
\]
\[
 |A'(b-a-d)|\le\frac{250}{237}\frac56\frac94\,3<6.
\]
Multiplication by d² proves the e-bounds. Values at every point of each difference interval, not only its center, are covered. [ABSTRACT][PAPER]

Define the exact real symmetric mean matrix
\[
 M=\frac12 I_3+\Pi-d\begin{pmatrix}
 0&A(a)&A(b)\\A(a)&0&A(b-a)\\A(b)&A(b-a)&0
 \end{pmatrix}. \tag{U11}
\]
Combining the local energy (U7), (U9), and the cross error proves
\[
 \boxed{\mathcal Q(v)\ge\frac{69}{100}\|g\|^2
                    +\mu^*M\mu-\frac9{100}H.} \tag{U12}
\]
The pole term vanishes only because the total moments in Theorem U1 vanish.

## 4. Keep the free mean; bound its actual coupling

Let
\[
 V=\begin{pmatrix}1&\sqrt2&\sqrt3\\1&1/\sqrt2&1/\sqrt3\end{pmatrix},
 \qquad z=(-1,2\sqrt2,-\sqrt3)^t,\qquad u=z/\sqrt{12}.
\]
Then ker V is exactly the line spanned by u. Decompose
\(\mu=\tau u+r\), where r is orthogonal to u. This decomposition is used over C and does not impose a real phase.

The total moment equations yield Vμ=-e, with
\[
 e_\pm=d^{-1/2}\sum_i e^{\pm x_i/2}
                         \int_J h_i(x)(e^{\pm x/2}-1)dx.
\]
Putting η=e^{d/4}-1, Cauchy--Schwarz gives
\[
 \|e\|\le\eta\sqrt{47/6}\sqrt H.
\]
Now
\[
 VV^*=\begin{pmatrix}6&3\\3&11/6\end{pmatrix}\succ\frac14I_2:
 \quad\det(VV^*-I_2/4)=5/48>0.
\]
Therefore the least nonzero singular value of V exceeds 1/2, and
\[
 \|r\|\le2\eta\sqrt{47/6}\sqrt H
 <\frac3{20}\sqrt H. \tag{U13}
\]
Indeed η≤13/487 and sqrt(47/6)<14/5, and 2(13/487)(14/5)<3/20.

**This is not the false small-mean estimate.** The whole component τu is allowed to be as large as sqrt H. Only the row-space error r is bounded. The exact counterexample in [CHAIN, (C2)--(C3)] is accepted, not excluded. [ABSTRACT][PAPER]

## 5. The arithmetic mean direction has a positive signed value

The exact center values are
\[
 A(a)=\frac{2\sqrt2}{3},\quad
 A(b)=\frac{3\sqrt3}{8},\quad
 A(b-a)=\frac{3\sqrt6}{5}.
\]
Substitute these in M. Direct multiplication gives
\[
 \boxed{u^*Mu=\frac12+\frac{\log(4/3)}6
                       +\frac{1049d}{720}>\frac{69}{100}.} \tag{U14}
\]
The prime part contributes +log(4/3)/6; the archimedean mixed mean part contributes +1049d/720. These are signed cancellations, not estimates of their separate absolute values. For the last strict bound use log(4/3)>2/7 and d=13/125.

Two deliberately coarse norm bounds suffice:
\[
 \|M\|<2,\qquad \|Mu\|<1. \tag{U15}
\]
For the first, the absolute off-diagonal entries are bounded by
\[
 |M_{01}|<1/2+d,\quad
 |M_{02}|<33/50+21d/32,\quad
 |M_{12}|<3d/2.
\]
Every absolute row sum, including the diagonal 1/2, is less than 2. For the second, direct multiplication, before taking absolute values, gives
\[
 (Mz)_0=b-2a-1/2-37d/24,
\]
\[
 (Mz)_1=\sqrt2(1+a/2+37d/15),\qquad
 (Mz)_2=\sqrt3(b/3-1/2-81d/40).
\]
Using 2/3<a<7/10 and 1<b<11/10 gives
\(|(Mz)_0|<6/5\), \(|(Mz)_1|<5/2\), \(|(Mz)_2|<1\).
Thus
\(\|Mu\|^2<((6/5)^2+(5/2)^2+1)/12<1\).

This finite calculation is the source-specific sign used in the proof. It would not hold automatically for an arbitrary Hermitian matrix, and it keeps the otherwise lost mean null vector. [FINITE_CELL][PAPER]

## 6. Closing the local proof with one rational budget

From μ=τu+r, (U14)--(U15),
\[
 \mu^*M\mu\ge\frac{69}{100}|\tau|^2
                     -2|\tau|\|r\|-2\|r\|^2.
\]
Insert this in (U12), use H=||g||²+|τ|²+||r||², |τ|≤sqrt H, and (U13). It follows that
\[
\begin{split}
 \mathcal Q(v)&\ge
 \left[\frac{69}{100}-\frac9{100}-\frac3{10}
       -\left(\frac{69}{100}+2\right)\frac9{400}\right]H\\
 &=\frac{9579}{40000}H>\frac15H.
\end{split} \tag{U16}
\]
This proves Theorem U1. No floating-point eigenvalue or sign assumption on a source remainder was used. The upper envelopes for the three cross errors and the retained mean coupling pay all terms in (U1).

**Coverage.** The six physical support endpoints are covered by zero extension and the full boundary potential β_J. The t=0 singularity is canceled in squared differences. All of J×J, not finitely many profiles, is covered by (U3)--(U7). The mixed intervals centered at a,b,b-a, including both of their endpoints, are covered by the derivative bounds in Section 3. The atoms at log2 and log3 are evaluated exactly; all higher prime powers are excluded by the support inequalities, not truncated numerically. The two total pole functionals are kept until their exact equations are used. Complex mixed pairings are included throughout. [ABSTRACT][PAPER]

**Relation to the CHAIN packet.** The nine-generator, seven-dimensional total-moment-null packet in [CHAIN, (C25)] is a subspace of this theorem's class. Its mathematical floor follows from (U16). The earlier forecast asking for an actual interval computation and a returned numerical receipt is still a different event and is not retrospectively called executed.

## 7. The attempted universal step: an exact localization defect

The successful local mechanism does not yet prove the all-n signed heads. I tested the possible direct propagation: split a global test into already controlled local pieces and keep their positive forms. Here is the exact source calculation, including the terms that prevent that argument from closing automatically.

Let χ_1,...,χ_m be real smooth multipliers with Σ_jχ_j(x)²=1 on a neighborhood of supp f, and define
\[
 \Theta(x,y)=1-\sum_j\chi_j(x)\chi_j(y)
             =\tfrac12\sum_j(\chi_j(x)-\chi_j(y))^2\ge0,
\]
\[
 C_{\Theta,f}(t)=\Re\int\Theta(x,x+t)\overline{f(x)}f(x+t)dx.
\]
Straight expansion of (U1) gives
\[
 \boxed{\sum_j\mathcal Q(\chi_jf)-\mathcal Q(f)=\mathcal E_\chi(f),} \tag{U17}
\]
\[
 \boxed{\mathcal E_\chi(f)=
 2\int_0^\infty\bigl(A(t)-2\cosh(t/2)\bigr)C_{\Theta,f}(t)dt
 +2\sum_{k\ge2}w_k C_{\Theta,f}(\log k).} \tag{U18}
\]

**Proof and signs.** The norms sum exactly to ||f||², so the diagonal constant cancels. Localizing an autocorrelation multiplies its integrand by 1-Θ. The archimedean squared-difference contribution therefore adds +2∫A C_Θ. The negative prime term adds +2Σw_k C_Θ(log k). Finally
\(2\Re(M_+\overline{M_-})=4\int_0^\infty\cosh(t/2)C_f(t)dt\),
so localizing the pole term subtracts 4∫cosh C_Θ. This proves (U18). Near zero, Θ=O(t²), so the singularity is integrable. Compact support handles infinity and makes the prime sum finite. QED. [ABSTRACT][PAPER]

### 7.1 The lossless propagation rule is false on the source itself

Take the explicit nonnegative bump
\[
 f(x)=\begin{cases}e^{-1/(1-(40x)^2)},&|x|<1/40,\\0,&\text{otherwise},\end{cases}
 \qquad\chi_1(x)=\cos x,\quad\chi_2(x)=\sin x.
\]
Then Θ(x,x+t)=1-cos t. The correlation is positive for 0<t<1/20, there are no active prime atoms, and on this range A(t)≥1/(2t) while 2cosh(t/2)<3. Consequently
\[
 \boxed{\mathcal Q(f)-\sum_j\mathcal Q(\chi_jf)
 \le-4\int_0^{1/20}(1-\cos t)C_f(t)dt<0.} \tag{U19}
\]
This is a strict negative **upper** envelope for the proposed lossless-gluing margin. It does not claim Q(f)<0. It refutes the theorem shape Q(f)≥ΣQ(χ_j f), not Weil positivity and not all possible localization estimates. No RH premise or surrogate source was used.

There is a second exact geometric obstruction to making the defect disappear. For any cover whose individual supports have diameter at most L, if |x-y|>L then no χ_j can be nonzero at both points. Hence Θ(x,y)=1 there. All such long-range arithmetic and pole couplings remain in (U18) with their original size. Tuning the local partition alone cannot delete them.

Also, M_±(f)=0 does not imply M_±(χ_j f)=0. Applying Theorem U1 to arbitrary localized pieces without a moment-preserving construction would be a class error even before the defect estimate. Any moment correction must retain the induced finite-rank terms and their couplings. A signed estimate paying that full defect has not been obtained here.

### 7.2 Decreasing the positive regularizer is not a sign proof

For the original fixed-n blocks, differentiating the bounded resolvent gives
\[
 \frac{d}{d\varepsilon}S_n(\varepsilon)
 =G_n+E_n^*(B_n+\varepsilon I)^{-2}E_n\succ0. \tag{U20}
\]
Thus positivity at a larger regularizer propagates upward in ε, not downward to 1/n. For A=B=1,E=2,G=1 the exact example is
\(S(\varepsilon)=1+\varepsilon-4/(1+\varepsilon)\): it is positive at ε=2 but negative for 0≤ε<1. This falsifies the abstract automatic-descent step, not the source atom. No source head is declared negative by this example. [FINITE_CELL][PAPER]

## 8. What is still missing for the requested universal theorem

The original objects and target remain exactly [CHAIN, (C10)--(C16)]:
\[
 S_n(1/n)=A_n+n^{-1}G_n-E_n^*(B_n+n^{-1}I)^{-1}E_n\succeq0
 \quad\text{for every integer }n\ge1. \tag{U21}
\]
This attempt proves neither (U21) nor its negation. The tail B_n≥I is not the missing sign; the full signed head is. Theorem U1 does not prove a complete S_1, because its restricted union of three short intervals is not the full space of tests on (-1,1), even after translation.

For the source-defined residual candidate of [CHAIN, (C18)--(C20)], the first unproved inequality is still
\[
 C_n^{Y_n}-(1+1/n)^{-1}Z_n^*Z_n\succeq0\quad\forall n,
 \qquad Z_n=E_n+(B_n+n^{-1}I)Y_n,
\]
for an independently constructed family Y_n. No such family and no all-n sign bound have been produced in this attempt. In the attempted localization representation, the same missing control appears in (U18), together with the moment-correction blocks. Naming this equality does not count as proving its sign.

A full nonnegative head certificate for every n would finish the terminal argument in CHAIN. I have not added another analytic hypothesis and called that a solution. Conversely, the failure of (U19)'s gluing rule does not show that the universal sign cannot be proved by a better representation.

## 9. Ledger, falsifiers, and one validation directive

### 9.1 What was and was not registered

The living commentary registered, before the rational budget check, the forecast that the regional-energy/signed-mean repair would give a positive whole-class three-profile floor, p=0.55. Its present fate is DERIVED_ON_PAPER, NOT_INDEPENDENTLY_CONFIRMED. It was not a blinded benchmark and no probability of RH was assigned.

The following CHAIN events retain their original definitions:

| Frozen event | p | Current fate |
|---|---:|---|
| P_CHAIN_THREE_LOBE_MEAN_FALSIFIER_SURVIVES | 0.98 | No new independent gate. Its mean null vector is retained exactly in (U13)--(U14); no contradiction with CHAIN. |
| P_CHAIN_EXPLICIT_FULL_SUPPORT_TAIL_SURVIVES | 0.90 | Rechecked as background, not independently certified here. The new local proof does not use that tail. |
| P_CHAIN_FROZEN_SEVEN_DIMENSIONAL_THREE_LOBE_FLOOR | 0.65 | Mathematical floor follows from Theorem U1 if this proof passes review. The frozen computational certificate/receipt event has not been run. |

The localization counterexample and regularizer calculation are not presented as prospectively blinded predictions. They are exact self-derived falsifiers. Old artifact bytes and probabilities are unchanged.

New registrations for future independent review, not this self-review:
```yaml
P_REGIONAL_LOG_LEGENDRE_CONSTANT_SURVIVES:
  probability: 0.94
  event: independent_review_accepts_U3_to_U8_including_all_factors_of_two
  fate: PENDING
P_THREE_LOBE_ONE_FIFTH_FLOOR_SURVIVES:
  probability: 0.82
  event: independent_review_accepts_U2_and_U9_to_U16_for_arbitrary_complex_profiles
  fate: PENDING
P_LOCALIZATION_SOURCE_DEFECT_SURVIVES:
  probability: 0.96
  event: independent_review_accepts_U17_to_U19_with_the_full_pole_term
  fate: PENDING
```

### 9.2 Two representations; no automatic escalation

| Representation | What this attempt supplies | Discriminator | Estimated power / local audit cost |
|---|---|---|---|
| Regional logarithmic energy plus the exact signed mean matrix | Whole three-lobe proof, no source inverse or numerical certificate | Reproduce U3 and U14, then all cross-error and moment constants | 9/10 / 3/10 |
| Original full-support Schur residual | Correct original target retained, no all-n solve family | True upper/lower residual envelopes for exactly the same full head, not just its positive subspaces | 10/10 / unknown global cost |

For a zero-consistent attempted head certificate, the DISCRIMINATOR remains the true signed quadratic value on the same vector with a full residual enclosure: a nonnegative lower envelope certifies that instance, and a negative upper envelope refutes it. An incomplete lower budget cannot refute the sign. No large numerical experiment or packet enlargement is authorized by this document.

### 9.3 CODEX DIRECTIVE — one independent proof audit, not another wrapper

**Target:** independently check Theorem U1, with special attention to (U3)'s factor 1/2, the boundary potential in (U5), the exact prime alignments, and the unconstrained component τu. Verify every rational comparison in the appendix with exact arithmetic. Recompute the mean matrix M from (U1), not from its quoted value. Check both real and complex mixed pairings. Preserve the existing CHAIN and PROFILES artifacts.

Acceptance requires the exact statement (U2) for all three smooth profiles and only the total moment equations, without assuming the claimed floor, setting τ=0, or deleting the b-a archimedean entry. Report an exact first defect or a proof audit with its scope. A successful review may update the status of CHAIN (C22); it must not mark (U21), the full S_1, or RH closed. No Lean source, source-operator numerical run, or new round of positive packets is requested by this directive.

### 9.4 Dependency epistemics and closeout

DOWNSTREAM_CONSUMER is unchanged: the published Weil criterion on all complex compact smooth tests. ACTUAL_CONSUMER_REQUIREMENT is nonnegativity of (U1) on that full class. ORIGINAL_REQUESTED_OBJECT is (U21). This particular Schur representation is NOT_NECESSARY for the terminal criterion, while its sufficiency is inherited from the exact completed-square identity in CHAIN. KNOWN_WEAKER_INTERFACES include all-support lower errors tending to zero and the published finite-Mellin-constraint version, each with its exact class obligations.

For the unsuccessful universal proof the FAILURE_TYPE is NO_DERIVATION and EPISTEMIC_STATUS is RESEARCH_DEBT. For the lossless-localization rule alone the FAILURE_TYPE is COUNTEREXAMPLE, KILL_SCOPE is THEOREM_SHAPE, and KILL_EVIDENCE_KIND is the exact negative upper envelope (U19). For automatic descent in ε the evidence is the exact scalar in (U20). Neither is ROUTE_FAMILY death. Reopening the universal target requires an actual source sign estimate, not another declaration that a finite head exists.

The theorem in this attempt settles a genuine previously open whole-class cell. It does not shrink the universal quantifier to a finite list. That distinction is retained in the progress report.

```yaml
META_CLOSEOUT:
  PROGRESS_CLASS: PROOF_PROGRESS
  COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
  ROUTE_SCORE: 3
  WHAT_BECAME_SMALLER: CHAIN_C22_is_now_a_complete_new_PAPER_derivation
  WHAT_REMAINS_IDENTICAL: universal_all_support_signed_head_sign
  WHAT_WAS_REFUTED:
    - lossless_localization_Q_ge_sum_local_Q_on_the_full_geometric_source
    - automatic_descent_from_large_regularizer_positivity
  MUST_NOT_RECUR:
    - discard_the_true_three_center_mean_nullspace
    - count_positive_fixed_supports_as_a_universal_induction
    - infer_source_negativity_from_a_failed_sufficient_budget
    - call_exact_rational_budget_checks_a_Lean_or_Arb_source_certificate
    - use_local_moment_nullity_without_proving_it_after_localization
  GLOBAL_ATOM_STATUS: NOT_PROVED
  LOCAL_THEOREM_STATUS: PAPER_INDEPENDENT_REVIEW_PENDING
PUBLICATION_HANDOFF:
  BRANCH: rh_clean
  PATHS_WRITTEN:
    - docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_UNIVERSAL_SIGN_ATTEMPT_REGIONAL_ENERGY_2026-09-07.md
  LEAN_FILES_WRITTEN: []
  LEAN_GATE_COMMANDS: NOT_APPLICABLE_DOCUMENT_ONLY
  EXPECTED_AXIOM_PROFILE: NOT_APPLICABLE_NO_KERNEL_GATE
  COMMIT_AND_READBACK_BLOB: delivery_receipt
```

## Appendix. Reproducible exact arithmetic checks

The following uses only rational arithmetic. It checks the scalar ledger, not the functional-analysis derivations. In this code d is the fixed interval length 13/125; log_lower(x,m) is the sum of the first m positive terms of the displayed logarithm series. No source coefficient, prime weight or form value is numerically fitted.

```python
from fractions import Fraction as F

def log_lower(x: F, terms: int) -> F:
    if x <= 1 or terms < 1:
        raise ValueError("x must exceed 1 and terms must be positive")
    z = (x - 1) / (x + 1)
    return 2 * sum((z**(2*k + 1) / F(2*k + 1)
                    for k in range(terms)), F(0))

d = F(13, 125)
assert log_lower(F(875, 286), 3) > F(111, 100)
assert log_lower(F(9, 2), 7) > F(451, 300)
assert F(13, 500) / (1 - F(13, 500)**2) < F(27, 1000)
assert F(111, 100) - F(29, 50) - F(27, 1000) > F(1, 2)
assert F(7, 10)**2 / 2 + F(11, 10)**2 / 3 < F(81, 100)**2
assert 2 * F(13, 487) * F(14, 5) < F(3, 20)
assert F(1, 2) + F(1, 21) + F(1049)*d/720 > F(69, 100)
assert (F(6, 5)**2 + F(5, 2)**2 + 1)/12 < 1
assert F(250, 237)*F(5, 7)*F(16, 11)*F(31, 22) < F(8, 5)
assert F(250, 237)*F(3, 5)*F(36, 31)*F(51, 62) < F(2, 3)
assert F(250, 237)*F(5, 6)*F(9, 4)*3 < 6
assert d*d*F(8, 5) < F(1, 50)
assert d*d*F(2, 3) < F(1, 100)
assert 6*d*d < F(7, 100)
assert F(1, 2)+F(1, 2)+d+F(33, 50)+F(21, 32)*d < 2
assert F(1, 2)+F(1, 2)+d+F(3, 2)*d < 2
assert F(1, 2)+F(33, 50)+F(21, 32)*d+F(3, 2)*d < 2
assert 1-F(7, 5)-F(1, 2)-F(37, 24)*d > -F(6, 5)
assert F(11, 10)-F(4, 3)-F(1, 2)-F(37, 24)*d < 0
assert F(3, 2)*(1+F(7, 20)+F(37, 15)*d) < F(5, 2)
assert F(7, 4)*(F(1, 2)-F(1, 3)+F(81, 40)*d) < 1
assert F(11, 30)-F(1, 2)-F(81, 40)*d < 0
budget = (F(69, 100)-F(9, 100)-F(3, 10)
          -(F(69, 100)+2)*F(9, 400))
assert budget == F(9579, 40000)
assert budget > F(1, 5)
print("EXACT_RATIONAL_LEDGER_PASS", budget)
```

Only this new artifact is to be written. The parent verdicts, old predictions, source code, queue, and route state remain unchanged. Universal Schur positivity and RH are not claimed.
