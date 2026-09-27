# STATUS: KILL_GOAL058_SOURCE_CORE_FIXED_128_PROJECTED_MESH_INCREMENT_BUDGET

```yaml
OPERATIVE_CLASS: KILL_GOAL058_SOURCE_CORE_FIXED_128_PROJECTED_MESH_INCREMENT_BUDGET
OUTCOME: SOURCE_PATH_VARIANCE_AVERAGE_PROVED
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-FIXED-128-PATH-VARIANCE-COMPENSATION
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_FIXED_128_PATH_VARIANCE_COMPENSATION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 1fd62ec9d2874f80941c5cf8b0d45092980dde12
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_SHA256_LOCALLY_VERIFIED: fea58a67cbaa7ffe290700b3157e94e18c985b3c42369250ada2ad92788e37d4
REQUEST_BYTES: 6463
REQUEST_LF: 122
REQUEST_CR: 0
REQUEST_UTF8_BOM: false
REQUEST_FINAL_LF: true
REQUEST_GIT_BLOB_LOCALLY_COMPUTED: f4a75c94cb7ab2b87648c0b7e4a0c31492b3e0b0
PREDECESSOR: REQ-2026-09-27-SOURCE-CORE-FIXED-128-COUPLED-PROJECTED-DILATION-ACTION
PREDECESSOR_SHA256_LOCALLY_VERIFIED: 985de41a845deba4a534414ae93f7b43a3977f3aea2b31f07ebdfa93765b3cd9
PREDECESSOR_BYTES: 39929
PREDECESSOR_LF: 645
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: bfde45c0d44779e290b327dfd34ed34fde2295c7
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_GIT_BLOB_READ: 3b55b58afcd34c8344b677178ef357bebae033a7
AUDIT_SECTION: source_core_fixed_128_coupled_projected_dilation_action_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
VAVG128: PROVED_PAPER
NEW_VARIANCE_BOUND: SUM_w_m_4L_m_squared_Vpath_m_IS_O_D_M_OVER_log_M
FORWARD_BLOCK: PAID_BY_CONTINUOUS_FREQUENCY_MULTIPLICITY_UPPER_BOUND
BACKWARD_BLOCK: PAID_SEPARATELY_BY_FINITE_BAND_MULTIPLICITY_UPPER_BOUND
COMPLETE_WINDOW_CORRECTION: PAID_AT_SECOND_DERIVATIVE_ORDER
NEW_HARDY_Z_MOMENT_ORDER: 2
NEW_MOMENT_REFERENCE: Bui_Hall_BLMS_2023_equation_1_k_equals_l_equals_2
NEW_MOMENT_LEADING_CONSTANT: 1_OVER_80
HARDY_Z_MOMENT_ORDER_3_USED: false
DISCRETE_HARDY_MOMENT_ASSUMED: false
ASYMPTOTIC_ERROR_DIFFERENTIATED: false
KILL_SCOPE: THEOREM_SHAPE
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILLED_THEOREM_SHAPE: UNIVERSAL_OR_EVENTUAL_PIB128_ON_THE_ORIGINAL_SELECTED_FAMILY
KILL_EVIDENCE_KIND: COMPLETE_SOURCE_WEIGHTED_BLOCK_STRICT_NEGATIVE_UPPER_ENVELOPE
KILL_EVIDENCE_REFERENCE: sections_7_and_8_equations_31_through_35
WITNESS_QUANTIFIER: EVERY_SUFFICIENTLY_LARGE_INTEGER_M_HAS_AN_ADMITTED_m_IN_M_LE_m_LT_2M_WITH_Qscr_m_LT_MINUS_S_m
FIRST_WITNESS_EVALUATED: false
NUMERICAL_EVENTUAL_THRESHOLD_COMPUTED: false
MT128: OPEN
MG128: OPEN
C128: OPEN
PC: OPEN
COFINAL_MG128_DISJUNCTION_ARM_SELECTED: NONE
SV: OPEN
LAG: OPEN
SCHUR_FLOOR: OPEN
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: VAVG128_CLOSED_AND_ONLY_PIB128_THEOREM_SHAPE_REFUTED
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
NEW_PROOF_INDEPENDENTLY_AUDITED: false
NEXT_TASK: INDEPENDENT_PAPER_AUDIT_OF_VARIANCE_AVERAGE_AND_COFINAL_PIB128_REFUTATION
MATHEMATICAL_RUNTIME_EXECUTED: false
COEFFICIENT_NUMERICS_EXECUTED: false
SELECTED_CELL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_RUNTIME_USE: FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY
REPOSITORY_WRITTEN: false
SOURCE_INDEX_TRUNCATED: false
SOURCE_FAMILY_CHANGED: false
ORIGINAL_ENERGIES_OR_DENOMINATOR_CHANGED: false
ORIGINAL_CARRIER_Q_SPLICE_N_K_PANEL_CHANGED: false
PHYSICAL_EXTERIOR_DROPPED: false
CONDITIONAL_SQUARE_CONSTANTS_ACTIVATED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **SOURCE_PATH_VARIANCE_AVERAGE_PROVED.** For the complete source, the same positive weights and every sufficiently late integer block, the stronger quantitative bound is
\[
\boxed{0\le \mathcal C_M:=\sum_{M\le m<2M}w_m\,4L_m^2\mathscr V_m^{\rm path}
\le C_D\frac{M}{\log M},\qquad D=256.}
\tag{1}
\]
The constant is independent of \(M\); it depends only on the fixed source, the fixed shift, and the stated unconditional moment bounds. Thus \(\mathcal C_M=o(M\log M)\), exactly VAVG128.

Combined with the accepted action margin, this proves that **every sufficiently late original block contains an admitted cell with**
\[
\boxed{\mathscr Q_m<-S_m<0.}
\tag{2}
\]
This refutes universal PIB128 and every eventual version of that same sufficient inequality. It does not decide \(T_m\), MG128, C128, PC, SV, lag, Schur-floor, or RH.

The proof does not replace action by increment. It bounds their exact difference. The principal new steps are the complete-source second-window-derivative formula, its square-summable finite-window correction, and **upper frequency-multiplicity bounds for both existing projected blocks**. Only a continuous Hardy-\(Z''\) second moment is newly needed. No third-derivative moment or discrete sampling law is used. The new proof has not received independent review.

## 1. Source lock, accepted inputs, and registration

**[FINITE_CELL | PAPER — provenance]** The authoritative TXT was read in full: 6,463 bytes, 122 LF, valid UTF-8, no CR or BOM, and a final LF. Its locally computed SHA-256 is the stipulated `fea58a67cbaa7ffe290700b3157e94e18c985b3c42369250ada2ad92788e37d4`. The request ID, boundary, source pin and mathematical domain agree with the canonical instruction. No other request was selected. fileciteturn28file0L1-L19

The complete mounted predecessor was read through its final directive. Its local SHA-256 is exactly `985de41a845deba4a534414ae93f7b43a3977f3aea2b31f07ebdfa93765b3cd9`; its local Git blob agrees with the connector's blob at the current pin. This verifies the complete local text against the pinned repository, rather than treating the connector's opening excerpt as the entire proof. fileciteturn30file0L4-L5

The bootstrap was fetched from `rh_clean` and read through its response-format section. I read the entire named audit section in `docs/Codex/PAPER_CHAIN.md` at the source commit. It accepts only the predecessor's cofinal PDA128 refutation and its inputs. It does not certify the new variance estimate below. fileciteturn33file0L2-L2

**[COFINAL_FAMILY | PAPER — accepted inputs, not new claims of this verdict]** With the original weights, the predecessor supplies, for every sufficiently large integer \(M\),
\[
\sum_{M\le m<2M}w_m S_m<4M\log M,
\qquad
\sum_{M\le m<2M}w_m4L_m^2\mathscr A_m^+>12M\log M.
\tag{3}
\]
It also supplies the exact full-source transform and the exact receiver identities used below. These are the accepted inputs specified by the present request, not conclusions inferred merely from a negative action witness. fileciteturn28file0L56-L80

**[ABSTRACT | PAPER — registered prediction]** Before the second-derivative and multiplicity tests, I registered the prediction \(\mathcal C_M=O_D(M/\log M)\), with the two projected frequency blocks as the critical check. Sections 3–7 prove that rate. The higher moment is separately identified as an external theorem; it is not attributed to the project audit.

## 2. The exact variance and a legitimate derivative upper bound

### 2.1. Source, family, and Hilbert normalization

**[COFINAL_FAMILY | PAPER — unchanged source contract]** Fix the same \(P\), and put
\[
m=J_P+j+2,\quad j\ge1,\quad L=\log m\ge1536,
\quad L_+=\log(m+D),\quad L_-=\log(m-1).
\]
Set \(\delta_+=L_+-L\) and \(\delta_-=L-L_-\). Throughout \(D=256\). The complete source is
\[
\begin{aligned}
g(u)&=\sum_{\alpha\ge1}g_\alpha(u),\\
g_\alpha(u)&=e^{u/2}\mathcal P(\pi\alpha^2e^{2u})e^{-\pi\alpha^2e^{2u}},\\
\mathcal P(x)&=-64x^4+448x^3-660x^2+150x,\\
e_n(\lambda)&=\frac{2(-1)^n}{\sqrt\lambda}
 \int_0^{\lambda/2}g(u)\cos(2\pi nu/\lambda)\,du.
\end{aligned}
\tag{4}
\]
No individual theta summand is assumed even. The complete source is even by the accepted theta identity; its fixed-order derivatives have locally uniform Gaussian majorants in \(\alpha\), and superexponential decay on the positive half-line.

On \([-1/2,1/2]\), \(f_\lambda(x)=\sqrt\lambda g(\lambda x)\) has coefficients \(e_n(\lambda)\) in the orthonormal basis \((-1)^n e^{2\pi inx}\). The coefficients are real and even in \(n\). Parseval therefore charges each positive index twice. The original velocity lives in
\(\ell^2(\{n>m+D\})\oplus\mathbb R^{128}\), with the factors \(\sqrt2\) prescribed in the request.

Use \(s\in[0,1]\) for the path parameter in this proof, reserving \(t\) for frequency. Differentiating the actual velocity gives
\[
\mathbf z_m'(s)=\left(
 (\sqrt2\,\delta_+^2 e_n''(L+s\delta_+))_{n>m+D},
 (\sqrt2\,\delta_-^2e_{m+2\ell-1}''(L-s\delta_-))_{1\le\ell\le128}
\right).
\tag{5}
\]
The second component has a **plus** sign: its two minus signs cancel under differentiation. The original velocity itself retains its backward minus sign. The indices \(m+1,m+3,\ldots,m+255\) are exactly the existing odd-offset block; the even offsets through \(m+256\) are not moved into it. All window, carrier, splice and panel conventions remain those in the request. fileciteturn28file0L29-L54

### 2.2. Bound the actual variance, not the action

**[ABSTRACT | PAPER — Hilbert inequality]** For a continuously differentiable Hilbert-valued path \(z\), with \(\bar z=\int_0^1z\),
\[
\int_0^1\|z-\bar z\|^2
=\frac12\int_0^1\int_0^1\|z(s)-z(t)\|^2\,ds\,dt
\le\int_0^1\|z'(s)\|^2\,ds.
\tag{6}
\]
The last inequality follows directly from the fundamental theorem of calculus and Cauchy–Schwarz. The sharper constant is unnecessary.

**[COFINAL_FAMILY | PAPER]** Applying (6) to the original velocity, then changing the parameter separately on the two paths, proves
\[
\begin{aligned}
4L_m^2\mathscr V_m^{\rm path}\le8L_m^2\Bigg[&
\delta_+^3\int_L^{L_+}\sum_{n>m+D}|e_n''(\lambda)|^2\,d\lambda\\
&+\delta_-^3\int_{L_-}^{L}\sum_{\ell=1}^{128}
 |e_{m+2\ell-1}''(\lambda)|^2\,d\lambda\Bigg].
\end{aligned}
\tag{7}
\]
Thus the fourth powers of the path lengths in (5) become third powers after parameter integration. Neither block has been dropped. Section 3 verifies the Hilbert differentiability and all endpoint terms needed here.

## 3. Second window derivative, with both boundary terms retained

### 3.1. Differentiate the complete source before splitting its transform

**[COFINAL_FAMILY | PAPER — exact identities]** Define
\[
h(u)=ug'(u)+\tfrac12g(u),\qquad
k(u)=u h'(u)-\tfrac12h(u)
=u^2g''(u)+ug'(u)-\tfrac14g(u).
\]
Differentiating \(f_\lambda\) once and twice gives the combined formulas
\[
\boxed{
 e_n'(\lambda)=\frac{2(-1)^n}{\lambda^{3/2}}
       \int_0^{\lambda/2}h(u)\cos(t_nu)\,du,
\quad
 e_n''(\lambda)=\frac{2(-1)^n}{\lambda^{5/2}}
       \int_0^{\lambda/2}k(u)\cos(t_nu)\,du,
\quad t_n=2\pi n/\lambda.
}
\tag{8}
\]
They are identities for the complete finite-window source, not full-line approximations.

For an explicit boundary check, put
\(J_n=\int_0^{\lambda/2}u g(u)\sin(t_nu)\,du\) and
\(K_n=\int_0^{\lambda/2}u^2g(u)\cos(t_nu)\,du\).
The first derivative is
\[
e_n'=-\frac{e_n}{2\lambda}+\frac{g(\lambda/2)}{\sqrt\lambda}
 +\frac{4\pi n(-1)^n}{\lambda^{5/2}}J_n.
\]
Differentiating this exact expression gives
\[
\boxed{
e_n''=
\frac{3e_n}{4\lambda^2}
+\frac{g'(\lambda/2)}{2\sqrt\lambda}
-\frac{g(\lambda/2)}{\lambda^{3/2}}
-\frac{12\pi n(-1)^n}{\lambda^{7/2}}J_n
-\frac{8\pi^2n^2(-1)^n}{\lambda^{9/2}}K_n.
}
\tag{9}
\]
Here \(\sin(t_n\lambda/2)=0\) removes the boundary term when differentiating \(J_n\), while \(\cos(t_n\lambda/2)=(-1)^n\) supplies the nonzero boundary terms already displayed. Both \(g'\) and \(g\) terms in (9) remain. Integrating (8) by parts reproduces (9).

We never take separate infinite-tail norms of the individual terms in (9), or of the first derivative's endpoint and bulk. All estimates use their combined cosine transform (8).

On each compact parameter interval, smooth dependence of \(f_\lambda\) in \(L^2\), followed by the fixed orthogonal projections, proves the Hilbert differentiability in (5). Alternatively, \(k'(0)=0\) for the complete even source and two integrations by parts give \(e_n''=O_m(n^{-2})\) uniformly there. This establishes the square summability needed for (7).

All differentiations and fixed-cell source interchanges are justified by Gaussian majorants. More explicitly, the sum over \(\alpha\) of the relevant fixed-cell \(L^2\) norms of \(k_\alpha\) is finite. Cauchy–Schwarz then controls the sum of absolute inner products over \((\alpha,\beta)\). The source sums are completed before squares; no source cross term is deleted.

### 3.2. Verify the proposed full-line sign and formula

**[COFINAL_FAMILY | PAPER — exact differentiation of an accepted identity]** The predecessor's complete-source crosswalk is
\[
F(t)=\int_{\mathbb R}g(u)e^{itu}\,du
=4t^2\xi(\tfrac12+it)=-a(t)Z(t),
\quad
 a(t)=2t^2(t^2+\tfrac14)\pi^{-1/4}|\Gamma(\tfrac14+it/2)|.
\]
Write \(p(t)=a'(t)/a(t)\), \(c(t)=p(t)+1/(2t)\), and
\(U(t)=Z'(t)+c(t)Z(t)\). This is the same normalization as the request. fileciteturn28file0L56-L59 fileciteturn28file0L88-L99

For \(e_n^\infty(\lambda)=(-1)^n\lambda^{-1/2}F(t_n)\), exact differentiation yields
\[
(e_n^\infty)'=(-1)^n\lambda^{-3/2}a(t_n)t_nU(t_n),
\]
\[
\boxed{
(e_n^\infty)''=(-1)^{n+1}\lambda^{-5/2}a(t_n)t_n
 \big[(\tfrac52+t_np(t_n))U(t_n)+t_nU'(t_n)\big]
=(-1)^{n+1}\lambda^{-5/2}a(t_n)t_n^2Y(t_n),
}
\tag{10}
\]
where
\[
\boxed{Y(t)=Z''(t)+(2p(t)+3/t)Z'(t)
 +\big(p'(t)+p(t)^2+3p(t)/t+3/(4t^2)\big)Z(t).}
\tag{11}
\]
This verifies the suggested sign, factor \(5/2\), and all powers of \(\lambda\) and \(t_n\). It differentiates an exact function identity, not an error term.

Equivalently, direct Fourier calculus gives
\(\widehat k(t)=t^2F''(t)+3tF'(t)+3F(t)/4=-a(t)t^2Y(t)\).
The exact finite-window correction is therefore
\[
\boxed{
e_n''(\lambda)=(e_n^\infty)''(\lambda)-q_{k,n}(\lambda),
\qquad q_{k,n}(\lambda)=\frac{2(-1)^n}{\lambda^{5/2}}
 \int_{\lambda/2}^\infty k(u)\cos(t_nu)\,du.
}
\tag{12}
\]
The correction is combined and square summable. It is not the invalid separated Leibniz remainder.

## 4. External input: precisely one additional Hardy derivative moment

**[ABSTRACT | PAPER — external THEOREM, independently checked]** Bui–Hall, *On the derivatives of Hardy's function Z(t)*, BLMS 55 (2023), 2304–2323, DOI `10.1112/blms.12859`, equation (1), with equal derivative orders \(j=0,1,2\), states
\[
\int_0^T |Z^{(j)}(t)|^2\,dt
=\frac{T}{4^j(2j+1)}Q_{2j+1}\!\left(\log\frac{T}{2\pi}\right)
+O\!\left(T^{3/4}(\log T)^{2j+1/2}\right),
\tag{13}
\]
where the polynomial is monic of the indicated degree. The leading constants are \(1,1/12,1/80\). The order-two case is the new import here; it is unconditional. No order-three case is used. citeturn520884view0

Let
\(\mathcal H_2(t)=Z(t)^2+Z'(t)^2+Z''(t)^2\).
In particular (13) supplies the global bound
\[
\boxed{\int_0^T\mathcal H_2(t)\,dt\le C T\log^5(2+T),\qquad T\ge1.}
\tag{14}
\]
Only this upper bound is needed for the new variance proof. No differentiated moment remainder is invoked.

**[ABSTRACT | PAPER — gamma inputs and consequences]** DLMF 5.11.9 and 5.11.2 give
\[
a(t)\asymp t^{15/4}e^{-\pi t/4},\qquad p(t)=-\pi/4+O(t^{-1}).
\tag{15}
\]
The two-sided amplitude bound holds for all sufficiently large \(t\). These statements use the gamma and digamma formulas separately. citeturn520884view1

For completeness, with \(z=1/4+it/2\), exact logarithmic differentiation gives
\[
p'(t)=-2/t^2+\frac{2(1/4-t^2)}{(t^2+1/4)^2}-\tfrac14\operatorname{Re}\psi'(z).
\]
The trigamma series \(\psi'(z)=\sum_{r\ge0}(r+z)^{-2}\) bounds its absolute value by \(C/t\) on this vertical line for \(t\ge1\). Consequently \(p'\) is bounded, without differentiating (15). The series is DLMF 5.15.1. citeturn520884view2

It follows from (11) that, for sufficiently large \(t\),
\[
|Y(t)|^2\le C\mathcal H_2(t).
\tag{16}
\]
The mixed terms inside the exact \(Y^2\) are bounded by Cauchy–Schwarz in (16), not assumed to vanish. Also, for every fixed \(\gamma>0\), (14) implies
\[
\int_T^\infty (1+t)e^{-\gamma t}\mathcal H_2(t)\,dt
\le C_\gamma e^{-\gamma T/2}.
\tag{17}
\]
Indeed \(\int_0^\infty(1+t)e^{-\gamma t/2}\mathcal H_2(t)dt<\infty\) by (14); factor out \(e^{-\gamma T/2}\). Thus even the infinite-frequency remainder can be controlled using the continuous moment, without pointwise derivative bounds.

## 5. Uniform finite-window error at second derivative order

**[COFINAL_FAMILY | PAPER — complete-source error budget]** For each \(0\le r\le4\), the constant
\[
C_r=\sup_{u\ge0}e^{(\pi/2)e^{2u}}|g^{(r)}(u)|
\]
is finite. To verify this from (4), fixed differentiation produces a fixed polynomial in \(\pi\alpha^2e^{2u}\). Absorb it and the factor \(e^{u/2}\) into part of its Gaussian; sum the remaining Gaussian in \(\alpha\). These constants are determined by the source, not by the unknown variance ratio.

Since \(k'=u^2g'''+3ug''+3g'/4\) and
\(k''=u^2g^{(4)}+5ug'''+15g''/4\), their corresponding bounds have at most a factor \((1+u)^2\). For \(b=\lambda/2\), two integrations by parts give the exact exterior identity
\[
\int_b^\infty k(u)\cos(t_nu)\,du
=-\frac{k'(b)(-1)^n}{t_n^2}
 -\frac1{t_n^2}\int_b^\infty k''(u)\cos(t_nu)\,du.
\]
The first integration's boundary vanishes because \(\sin(t_nb)=0\); the displayed derivative boundary does not vanish. Using \(e^{2(b+v)}\ge e^{2b}(1+2v)\) to bound the remaining integral proves
\[
\boxed{|q_{k,n}(\lambda)|\le C\lambda^{3/2}n^{-2}
 e^{-(\pi/2)e^\lambda},\qquad \lambda\ge1,\quad n\ge1.}
\tag{18}
\]
This is uniform in the whole source and in the infinite spectral tail.

Write \(H=\log M\) and sum only the original integers \(M\le m<2M\). On both parameter paths, \(e^\lambda\ge m-1\), \(\lambda\asymp H\),
\(\delta_+\le D/m\), and \(\delta_-\le1/(m-1)\). From (15),
\(w_m\le C\exp(\pi^2m/L_m)\) eventually. Define \(\mathfrak E_M\) by the right side of (7), summed with \(w_m\), but with every \(e_n''\) replaced by \(q_{k,n}\). Then
\[
\boxed{\mathfrak E_M\le C_D M^{C_1}e^{-c_1M}=o(M/H),\qquad c_1>0.}
\tag{19}
\]
To check the exponent explicitly, each squared error has exponential factor at most
\(\exp[-\pi(m-1)+\pi^2m/L_m]\le C e^{-\pi m/2}\) eventually. The two path integrations supply fourth powers of their lengths; the tail uses \(\sum_{n>m+D}n^{-4}\le C m^{-3}\), and the backward block uses at most \(128m^{-4}\). All remaining powers and the sum over cells are absorbed by (19).

Let \(\mathcal P_M^\pm\) denote the two right-hand contributions of (7), summed with \(w_m\), using \((e_n^\infty)''\) instead. Applying \(|x-y|^2\le2|x|^2+2|y|^2\) to the exact decomposition (12) gives
\[
\boxed{\mathcal C_M\le2\mathcal P_M^++2\mathcal P_M^-+2\mathfrak E_M.}
\tag{20}
\]
Thus no full-line expression is substituted without a paid finite-window error. The physical exterior in \(S_m\) and \(O_m\) remains unchanged; it will be retained when the actual receiver is used in Section 8.

## 6. Upper frequency multiplicity: pay both projected blocks

### 6.1. A uniform amplitude bound on the actual paths

**[COFINAL_FAMILY | PAPER — source-relative weight comparison]** Put \(r=e^\lambda\), \(\tau(r)=2\pi r/\log r\), and \(t=2\pi n/\log r\). On a forward path, \(m\le r\le m+D\) and \(n>m+D\), so \(n>r\). On a backward path, \(m-1\le r\le m\), and \(n=m+2\ell-1\), so
\(0<n-r\le D\). In both cases \(|r-m|\le D\).

Boundedness of \(p\), together with \(|\tau(r)-\tau(m)|=O_D(H^{-1})\), gives
\(a(\tau(r))^2/a(\tau(m))^2\le C_D\) uniformly. From the two-sided estimate (15), for \(n>r\),
\[
w_m a(2\pi n/\log r)^2
\le C_D(n/r)^{15/2}\exp[-\pi^2(n-r)/\log r].
\]
For all \(r\in[M-1,2M+D]\) and sufficiently large \(M\), therefore,
\[
\boxed{(n/r)^4w_ma(2\pi n/\log r)^2
\le C_D\exp[-c(n-r)/H],\qquad c=\pi^2/4.}
\tag{21}
\]
Indeed the polynomial has power \(23/2\le12\), its logarithm is at most \(12(n-r)/r\), and \(\log r\le2H\), \(r\ge M/2\). Eventually \(24/M\le\pi^2/(4H)\), which proves (21) for **all** \(n>r\), not only near the carrier edge.

### 6.2. Forward block: original path overlap and the whole tail

**[COFINAL_FAMILY | PAPER]** From the definitions of \(\mathcal P_M^+\), (10), and (16), changing \(\lambda\) to \(r\) gives the upper bound
\[
\mathcal P_M^+
\le C\sum_{M\le m<2M} L_m^2\delta_+^3
\int_m^{m+D}\frac{1}{r(\log r)^5}
 \sum_{n>m+D} w_ma(t)^2t^4\mathcal H_2(t)\,dr.
\]
Here \(\delta_+\le C_D/r\), \(L_m\asymp\log r\asymp H\), and
\(t^4=(2\pi)^4n^4/(\log r)^4\). The coefficient is bounded by
\(C_DH^{-7}(n/r)^4\). At each real \(r\), at most \(D+1\) original forward paths occur. Using (21) and extending only the nonnegative upper envelope from \(n>m+D\) to \(n>r\) yields
\[
\boxed{\mathcal P_M^+\le\frac{C_D}{H^7}
 \int_M^{2M+D}\sum_{n>r}e^{-c(n-r)/H}
 \mathcal H_2(2\pi n/\log r)\,dr.}
\tag{22}
\]
This is a domination of the existing tail, not a new projection in the receiver. The real variable \(r\) is only a reparametrization inside the original paths; it is not a newly selected source cell.

For fixed \(n\), change variable again to frequency \(t\). Set
\[
r_n(t)=e^{2\pi n/t},\qquad q_n(t)=n-r_n(t),
\qquad \left|\frac{dr_n}{dt}\right|
=\frac{r_n(\log r_n)^2}{2\pi n}\le C H^2
\quad(n>r_n).
\tag{23}
\]
The integral in (22) is consequently at most
\[
CH^2\int_0^\infty \mathcal H_2(t)\,K_M^+(t)\,dt,
\quad
K_M^+(t)=\sum_{\substack{M\le r_n(t)\le2M+D\\q_n(t)>0}}
 e^{-cq_n(t)/H}.
\]
The following bound, rather than a discrete mean-square assumption, is the key:
\[
\boxed{
K_M^+(t)\le C\quad(0<t\le T_M),
\qquad K_M^+(t)\le C(1+t)e^{-\gamma t}\quad(t>T_M),
\quad T_M=32\pi M/H,
}
\tag{24}
\]
where \(\gamma>0\) and the constants are independent of \(M,t\).

To prove the first assertion, interpolate the index by a real variable \(x\). While \(r_x(t)\) lies in the permitted range,
\[
\frac{d}{dx}\big(x-r_x(t)\big)
=1-\frac{2\pi r_x(t)}t
\le1-\frac H{32}\le-\frac H{64}
\]
eventually; here \(r_x\ge M/2\) and \(t\le32\pi M/H\). Thus successive admissible integer indices give positive \(q_n\)'s separated by at least \(H/64\), in decreasing order. Their exponential weights sum to at most
\((1-e^{-c/64})^{-1}\). The same derivative bound holds between any two such indices because \(r_x\) is increasing in \(x\).

For the second assertion, \(r_n\le3M\), \(\log r_n\ge H/2\), and \(t>T_M\) imply
\(n=t\log r_n/(2\pi)\ge8M\), hence
\(q_n\ge n/2\ge tH/(8\pi)\).
The number of integers with \(r_n\) in the permitted range is at most \(C(1+t)\), since the interval for \(n\) has length
\(t\log((2M+D)/M)/(2\pi)\). Taking \(\gamma=c/(8\pi)\) proves the second assertion.

All tail frequencies have been covered by these two cases. Inserting (14), (17), and (24) in (22)–(23) gives
\[
\boxed{
\mathcal P_M^+
\le\frac{C_D}{H^5}\left(T_M\log^5(2+T_M)+e^{-\gamma T_M/2}\right)
\le C_D\frac{M}{H}.
}
\tag{25}
\]
The split at \(T_M\) is an analytic division of a fully retained frequency integral, not a fitted cutoff or a change of \(N,K\), carrier, or panel. No high-frequency remainder is discarded.

### 6.3. Backward block: its own windows and parity band

**[COFINAL_FAMILY | PAPER]** On the backward paths \(r\in[m-1,m]\), \(\delta_-\le C/r\), and the same calculation of powers yields
\[
\mathcal P_M^-\le\frac{C_D}{H^7}
\int_{M-1}^{2M}\sum_{0<n-r\le D}
 e^{-c(n-r)/H}\mathcal H_2(2\pi n/\log r)\,dr.
\tag{26}
\]
Here is the precise upper-envelope accounting. For almost every \(r\) there is only one original backward cell, \(m=\lceil r\rceil\). Its original indices are \(n=m+2\ell-1\). For fixed \(n\), their permitted \(r\)-intervals are
\([n-2\ell,n-2\ell+1]\), \(1\le\ell\le128\), intersected with the block's actual paths. They are disjoint. Extending that union to \(0<n-r\le D\) only adds nonnegative terms to an upper envelope; it neither changes the original odd block nor evaluates \(B_{m-1}\) at the wrong window.

After (23), the relevant density is bounded by the count
\[
K_M^-(t)\le
\#\{n:\ M-1\le r_n(t)\le2M,\quad0<q_n(t)\le D\}.
\]
Every occurring frequency satisfies \(t<T_M\) eventually: \(n\le2M+D\le3M\) and \(\log r_n\ge H/2\) give \(t\le12\pi M/H\). The same interpolation calculation as in (24), now on \([M-1,2M]\), separates successive \(q_n\)'s by \(H/64\). Hence
\[
K_M^-(t)\le1+64D/H\le1+64D.
\]
It follows that
\[
\boxed{\mathcal P_M^-\le\frac{C_D}{H^5}
 \int_0^{T_M}\mathcal H_2(t)\,dt
\le C_D\frac{M}{H}.}
\tag{27}
\]
This pays the backward block separately. It does not infer its estimate from the forward lower-coverage theorem in the predecessor.

### 6.4. Boundary and sampling audit of the change of variables

**[ABSTRACT | PAPER — geometry audit]** The outer ranges \([M,2M+D]\) and \([M-1,2M]\) contain the entire original forward and backward path ranges, including both ends of the summed block. The condition \(n>r\) in (22) includes every original forward term because \(r\le m+D<n\). The backward domain in (26) includes every original odd-offset term. Endpoints of these parameter intervals have measure zero; their inclusion does not remove a derivative boundary term from (8)–(12).

The bounded densities in (24) and (27) follow from the explicitly differentiated map \(x\mapsto x-e^{2\pi x/t}\). They are upper-multiplicity estimates for continuous path integrals, not asymptotic formulas for lattice samples of \(Z''\). Frequency gaps cause no problem for an upper bound. Frequencies beyond \(T_M\) in the infinite forward tail are paid using (17). Thus neither block requires a discrete Hardy moment or an order-three derivative to control sampling errors.

## 7. Close VAVG128 at the stated scale

**[COFINAL_FAMILY | PAPER — new quantified theorem]** Combining (19), (20), (25), and (27) gives
\[
0\le\mathcal C_M\le C_D M/H+C_D M^{C_1}e^{-c_1M}
\le C_D' M/H
\tag{28}
\]
for all sufficiently large integers \(M\). Therefore
\[
\boxed{\frac{1}{M\log M}\sum_{M\le m<2M}w_m4L_m^2\mathscr V_m^{\rm path}
=O_D((\log M)^{-2})\longrightarrow0.}
\tag{29}
\]
This proves VAVG128, with both projection blocks and the complete-source finite-window corrections paid. It is not a statement that each individual variance is small relative to its own energy. The bound is uniform in the integer block start \(M\), not merely along a chosen subsequence.

The use of (6) is legitimate here because its **projected second derivative** has been estimated at the required weighted scale. The argument never uses an unprojected source norm, and never bounds the non-square-summable Leibniz pieces separately. Qualitative positivity of \(\mathscr V_m^{\rm path}\) is not the source of the quantitative upper bound.

## 8. Return to the original receiver: only PIB128 is refuted

**[COFINAL_FAMILY | PAPER — exact receiver and strict upper sign]** The unchanged identities are
\[
\begin{aligned}
\mathscr R_m&=S_m-4L_m^2(\mathscr A_m^++\mathscr A_m^-)-2L_mO_m,\\
\mathscr Q_m&=\mathscr R_m+4L_m^2\mathscr V_m^{\rm path}
=S_m-4L_m^2W_m-2L_mO_m.
\end{aligned}
\tag{30}
\]
Take \(M\) sufficiently large that (3) holds and \(\mathcal C_M<M\log M\), as follows from (28). The actual backward action is nonnegative, and the actual exterior loss is positive. Consequently
\[
\boxed{\sum_{M\le m<2M}w_m\mathscr Q_m<-7M\log M,}
\tag{31}
\]
and, using the same energy upper bound once more,
\[
\boxed{\sum_{M\le m<2M}w_m(\mathscr Q_m+S_m)<-3M\log M<0.}
\tag{32}
\]
Both estimates use precisely the same positive weights on the actual quantities. Nothing is normalized by a substitute energy. The delayed \(E_{m-1}\) in \(S_m\), including at the first cell of the block, remains present. The predecessor's estimates (3) already paid that delayed edge, its original energy sampling step, and its window/exterior errors; none is replaced here.

Since every \(w_m>0\), (32) proves
\[
\boxed{\forall M\ge M_*(P),\ M\in\mathbb N:\quad
\exists m\in\mathbb Z\cap[M,2M),\qquad \mathscr Q_m<-S_m<0.}
\tag{33}
\]
Choose \(M_*(P)\) beyond all analytic thresholds and with
\(M_*(P)\ge J_P+3\), \(\log M_*(P)\ge1536\). Then every integer in every summed block is already an original admitted cell; \(j=m-J_P-2\ge1\). Real path parameters have never been treated as selected cells.

For a rigorously admitted unbounded witness sequence, put \(M_k=3^kM_*(P)\) and
\[
\boxed{m_k=\min\{m\in\mathbb Z\cap[M_k,2M_k):\ \mathscr Q_m<-S_m\},
\qquad j_k=m_k-J_P-2.}
\tag{34}
\]
The sets are nonempty by (32), before this definition is made. The blocks are disjoint and increasing, so \(m_k\to\infty\). No cell is evaluated or searched numerically; no explicit numerical threshold is asserted.

In particular the original normalized discriminator has the negative upper envelope
\[
\boxed{\mathscr Q_{m_k}/S_{m_k}<-1.}
\tag{35}
\]
Thus universal PIB128 and every eventual PIB128 on this original family are false. This is a theorem-shape refutation, not route-family death.

**[COFINAL_FAMILY | PAPER — scope boundary]** A negative \(\mathscr Q_m\) does not imply a negative \(T_m\): the exact formula for \(T_m\) contains further positive terms. Neither sign of MG128 follows. No MG128 cofinal-disjunction arm has been selected, and the older conditional weighted-recursion argument is not invoked. The present consequence uses only the accepted block inequalities (3) and the exact compensation identity (30). The requested distinctions between PIB128 and all downstream questions remain in force. fileciteturn28file0L70-L81

## 9. Strongest attacks, route map, and closeout

**[ABSTRACT | PAPER — self-audit]** The strongest objection would be an unjustified conversion of continuous Hardy moments into a spectral sampling estimate. Here there is no such conversion: (23) changes variables inside the original parameter integrals, and (24), (27) give explicit upper densities. The full infinite forward tail has a separate exponentially damped range. Both end ranges are included. A derivative-order-three moment is therefore unnecessary.

The next strongest objection is a hidden window error in \(e_n''\). Equations (8)–(12) display the exact combined derivative and its sign, (9) retains both physical boundary terms, and (18)–(20) bound the complete correction under the original weights. Neither an asymptotic remainder nor a separated endpoint norm is differentiated or used.

The proof uses a full-source transform before squaring. Replacing it by a finite theta model, deleting source cross terms, or claiming that the individual source terms are even would invalidate the argument. The mixed \(Z,Z',Z''\) terms in (11) are bounded, not erased. The constant in (28) is finite and independent of \(M\); it need not be small, because VAVG128 is a limit over all sufficiently late blocks.

The analytical enlargements in (22) and (26) are nonnegative upper envelopes for proof only. They do not redefine the actual projections, \(W_m\), \(\mathscr V_m^{\rm path}\), or either energy. Using an unprojected norm in their place would return to a method already refuted by the predecessor chain.

| Representation | Decisive power / cost | Status |
|---|---|---|
| **Projected path derivative and continuous frequency multiplicity.** **[COFINAL_FAMILY; PAPER]** | Closes the stated average using one additional continuous second moment and a complete-source second-derivative remainder. No numerical search or discrete moment is needed. | Completed here; new proof requires independent audit. |
| **Exact two-window Gram form for \(W_m\).** **[COFINAL_FAMILY; PAPER/CONDITIONAL]** | Still represents the receiver without an action relaxation; could investigate individual signs or a different consumer. Cost: the two actual cross-window pairings. | Not used to claim an individual classification beyond (33). |

**What became smaller.** VAVG128 is proved, and the actual universal/eventual PIB128 theorem shape is refuted. The proof has moved beyond a refutation of a stronger action budget: the positive variance correction has now been quantitatively paid in the required block average.

**What must not be inferred.** Neither \(T_m<0\), MG128 failure, PC failure, SV failure, nor RH follows from (35). No assertion is made that all cells have negative \(\mathscr Q_m\).

**Prediction scoring.** The request and predecessor hash checks passed. The registered \(O_D(M/\log M)\) prediction is confirmed by (28). The full-line second-derivative sign was checked by exact differentiation; both projected multiplicity tests passed. No numerical cell prediction or independent review is retrospectively claimed.

The three mathematical connections used are: Hilbert path variance to a projected derivative integral; exact Fourier/dilation calculus with a complete exterior correction; and bounded path-frequency multiplicity allowing a continuous analytic-number-theory moment. None is a finite-to-global numerical extrapolation.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: exact_Qscr_receiver_and_cofinal_failure_of_universal_PIB128
ACTUAL_CONSUMER_REQUIREMENT: a_strict_negative_actual_Qscr_in_arbitrarily_late_original_blocks
ORIGINAL_REQUESTED_OBJECT: VAVG128_on_all_sufficiently_large_integer_blocks
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: proved_sufficient_here_but_not_established_necessary_for_PIB128_refutation
KNOWN_WEAKER_INTERFACES:
  - limsup_normalized_variance_average_strictly_below_8_suffices_with_the_accepted_Rscr_margin
  - direct_negative_weighted_Qscr_without_a_separate_variance_upper_bound
  - direct_actual_two_window_Gram_witness_for_Qscr
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILL_SCOPE: THEOREM_SHAPE
KILLED_OBJECT: universal_or_eventual_PIB128_only
KILL_EVIDENCE_KIND: exact_compensation_identity_plus_strict_weighted_block_upper_sign
KILL_EVIDENCE_REFERENCE: equations_28_through_35_of_this_verdict_on_the_source_locked_request
NEW_EXTERNAL_INPUT: Bui_Hall_equation_1_at_derivative_pair_2_2
NEW_EXTERNAL_INPUT_HYPOTHESIS_RH: false
ORIGINAL_ROUTE_FAMILY_DEAD: false
OTHER_OPEN_CONSUMERS: MT128_MG128_C128_PC_SV_LAG_SCHUR_FLOOR
REOPEN_TRIGGER_FOR_NEW_PIB128_KILL: demonstrated_error_in_second_derivative_remainder_moment_import_frequency_density_or_block_transfer
RESEARCH_DEBT_AFTER_THIS_VERDICT: source_signs_for_the_unchanged_T_MG_PC_and_downstream_consumers
RESEARCH_DEBT_REOPEN_TRIGGER: an_independent_source_estimate_for_one_of_those_actual_receivers
NOVELTY_AXIS: quantitative_path_variance_is_two_log_powers_below_the_accepted_action_deficit_in_original_weighted_blocks
MEMORY_ENTRY:
  target: source_core_fixed_128_path_variance_compensation
  status: PROVED_VAVG128_AND_FATAL_FOR_PIB128_ONLY
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: infer_exact_increment_failure_from_action_failure_without_a_variance_budget
  invariant_learned: continuous_path_overlap_can_pay_projected_variance_without_a_discrete_Hardy_derivative_moment
  forbidden_future_move: promote_a_negative_Qscr_to_a_T_MG_PC_SV_or_RH_sign
  next_decisive_test: independent_PAPER_audit_of_equations_7_through_35
```

**[COFINAL_FAMILY | PAPER — preservation and verification boundary]** The low epsilon block, literal diagonal, zero node, final descent, paired logarithmic kernel, signed beta correction, exponent-one prime block, prime/square compensation, opposite-side correlation, transfer and Schur-floor are untouched. The original source, both Fourier signs, full exterior, original three windows, carrier, \(Q=\sqrt m\), \(5m\) splice, \(N,K\), and panel are unchanged. No conditional square constant is activated. No coefficient numerics, selected-cell search, mathematical runtime, Lean execution, repository write, route promotion, or RH claim occurred. Local execution was file I/O, text validation and hashing only. The new proof has not received independent review. fileciteturn28file0L113-L122

## CODEX DIRECTIVE

**Perform one read-only independent PAPER audit of this VAVG128 proof and its strictly scoped cofinal PIB128 refutation, against the same request hash and source commit.** Check the complete second-window-derivative identities and both boundary terms (8)–(12), the unconditional Bui–Hall order-two moment and coefficient \(1/80\) in (13), the uniform combined-window error (18)–(20), all powers of \(L_m,\delta_\pm,r,n\) in (21)–(27), the forward infinite-frequency density including its high-frequency remainder, and the separate backward odd-band density. Verify that all block ends are retained and no discrete Hardy moment is assumed. Then check the \(O_D(M/\log M)\) conclusion and the exact transfer through the accepted margins to \(\mathscr Q_m<-S_m\) in every sufficiently late original block, with admission as in (33)–(35). The only mathematical outcome to accept is `SOURCE_PATH_VARIANCE_AVERAGE_PROVED`, with the derived `KILL_SCOPE: THEOREM_SHAPE` applying solely to universal/eventual PIB128. If a step fails, report the first invalid estimate and withhold this new implication without altering the predecessor's accepted PDA128 result. Do not infer a sign for \(T_m\), MG128, C128, PC, SV, lag, Schur-floor or RH. No coefficient search, mathematical runtime, source deletion, new mask/panel, Lean, repository write, conditional-constant activation or route promotion is authorized.
