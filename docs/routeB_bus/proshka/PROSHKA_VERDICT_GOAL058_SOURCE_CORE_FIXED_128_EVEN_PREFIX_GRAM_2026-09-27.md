# STATUS: TRY_GOAL058_SOURCE_CORE_FIXED_128_EVEN_PREFIX_GRAM

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_FIXED_128_EVEN_PREFIX_GRAM
OUTCOME: SOURCE_EVEN_PREFIX_GRAM_DIAGONAL
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-FIXED-128-EVEN-PREFIX-GRAM
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_FIXED_128_EVEN_PREFIX_GRAM
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 4b64767dccf52e2a19acee736d6b7203a69a5311
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_SHA256_LOCALLY_VERIFIED: ee4f45bf26b7887b23d355770f85ecce58dda90e4d4b00eb9c50a5dbbd802686
REQUEST_BYTES: 5318
REQUEST_LF: 99
REQUEST_CR: 0
REQUEST_UTF8_VALID: true
REQUEST_UTF8_BOM: false
REQUEST_FINAL_LF: true
REQUEST_GIT_BLOB_LOCALLY_COMPUTED: 8be526fcacd42761af02f65ac9bd4f666a3306bb
SIGNED_BLOCK_SHA256_LOCALLY_VERIFIED: 4ff6bdeb6bc5d7aa2d76c8e19e6528f623436a8a395c54386e35fa75dfcea541
SIGNED_BLOCK_BYTES: 38162
SIGNED_BLOCK_LF: 633
SIGNED_BLOCK_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: b51023e2649672c3ee54b6612f7829408fbd8000
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
PAPER_CHAIN_GIT_BLOB_READ: 2e830069aad0475e742467c6be784c80c2c84387
PAPER_CHAIN_SHA256_IN_REQUEST: 14b44c3f1425576057367ca7e39f752f280c74a5ded69f5ab9b1f73b27ade82c
PAPER_CHAIN_SHA256_INDEPENDENTLY_REHASHED: false
PAPER_CHAIN_PROVENANCE: EXACT_COMMIT_CONNECTOR_READ_FINAL_TWO_SECTIONS
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
FIXED_PAIR_GRAM_LIMIT: G_M_over_M_TENDS_TO_IDENTITY_128
C_M: o_M
D_M: MINUS_246_M_PLUS_o_M
STRICT_EVENTUAL_UPPER_ENVELOPE: D_M_LT_MINUS_123_M
QUANTIFIER: EVERY_SUFFICIENTLY_LARGE_INTEGER_BLOCK_START_M_FOR_THE_SAME_FIXED_P
SECOND_C128_GATE_FAILURE: SOME_ORIGINAL_ADMITTED_CELL_IN_EVERY_SUFFICIENTLY_LATE_BLOCK
JOINT_C128_WITNESS: NOT_ESTABLISHED
JOINT_C128_EXCLUSION: NOT_ESTABLISHED
FIRST_AND_SECOND_GATE_WITNESSES_IDENTIFIED: false
NEW_DERIVED_CONTINUOUS_RESULT: COMPACT_UNIFORM_SINC_SHIFTED_HARDY_SECOND_MOMENT
SHIFT_NORMALIZATION: c_over_log_M_WITH_c_EQUALS_4pi_times_k_minus_ell
SHIFT_UNIFORMITY: EVERY_FIXED_COMPACT_SET_OF_REAL_c
NEW_PRODUCT_SAMPLING_RESULT: ACTUAL_TWO_PHASE_m_MESH_EULER_MACLAURIN_REMAINDER_TENDS_TO_ZERO
IMPORTED_SHIFTED_MOMENT: NONE
VERIFIED_EXTERNAL_INPUT: Bui_Hall_2304_05178v1_equation_1_FIXED_ORDER_CONTINUOUS_DERIVATIVE_MOMENTS
QUADRATURE_INPUT: DLMF_2_10_1_AND_24_8_1
DERIVATIVE_ORDER_GROWS_WITH_M: false
ORDER_OF_LIMITS: FIX_ORDERS_THEN_M_TO_INFINITY_THEN_AUXILIARY_ORDERS_TO_INFINITY
TWO_FINITE_WINDOW_ERRORS: RETAINED_AND_PAID_WITH_THE_ORIGINAL_COMMON_WEIGHT
SOURCE_INDEX_CROSS_TERMS: RETAINED
ORIGINAL_SOURCE_FAMILY_CHANGED: false
ORIGINAL_WEIGHTS_CHANGED: false
ORIGINAL_ENERGY_CHANGED: false
ORIGINAL_CARRIER_Q_SPLICE_N_K_PANEL_CHANGED: false
PHYSICAL_EXTERIOR_DROPPED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
COEFFICIENT_NUMERICS_EXECUTED: false
SELECTED_CELL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
LOCAL_RUNTIME_USE: FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY
NEW_PROOF_INDEPENDENTLY_AUDITED: false
PROGRESS_CLASS: PROOF_PROGRESS
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
NEXT_TASK: INDEPENDENT_PAPER_AUDIT_OF_FIXED_PAIR_GRAM_AND_SCOPED_DISPERSION_CONSEQUENCE
NEW_ROUTE_OR_C128_KILL: NONE
MG128_PREVIOUS_COFINAL_REFUTATION: PRESERVED_NOT_REPROVED
MT128: OPEN
C128: OPEN
PC: OPEN
SV: OPEN
LAG: OPEN
SCHUR_FLOOR: OPEN
CONDITIONAL_SQUARE_CONSTANTS_ACTIVATED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **SOURCE_EVEN_PREFIX_GRAM_DIAGONAL.** For the complete source, the original common weight, and every fixed pair \(1\le\ell,k\le128\), the new PAPER argument proves
\[
\boxed{
G_{\ell k}(M):=\sum_{M\le m<2M}w_mx_{\ell,m}x_{k,m}
=\delta_{\ell k}M+o(M).
}
\tag{1}
\]
The limit is along **all integer block starts**. Since there are only finitely many pairs, it also gives \(M^{-1}G(M)\to I_{128}\) in matrix operator norm. Consequently,
\[
\boxed{C_M=o(M),\qquad D_M=(-246+o(1))M.}
\tag{2}
\]
In particular, for some integer \(M_*(P)\),
\[
\boxed{D_M<-123M<0\qquad\text{for every integer }M\ge M_*(P).}
\tag{3}
\]
Each such block contains an **original admitted cell** at which \(J_m^{\rm disp}>8a_m^2\). This does not exclude an existential C128 event, and it does not identify that cell with any cell satisfying the first C128 gate.

The off-diagonal conclusion is not inferred from the accepted diagonals or from independence. Two new steps are proved below: a compact-uniform small-shift continuous moment, derived from the verified fixed-order moment family, and a product quadrature estimate on the actual two-phase mesh. Both finite-window errors and their mixed terms are then paid under the same original weight. The new proof has not received independent review.

## 1. Source lock, accepted record, and audit prediction

**[FINITE_CELL | PAPER — provenance]** The authoritative attachment was read completely, including its final preservation conditions. Its local SHA-256 is exactly the supplied digest; its byte and line counts are in the header. The request ID, boundary, and source commit agree with the canonical instruction. The request distinguishes the accepted diagonal asymptotics from the off-diagonal test. fileciteturn38file0L1-L17 fileciteturn38file0L19-L38

The bootstrap was fetched through the GitHub connector from `rh_clean` and read through its response-format section. The complete mounted signed-block verdict was read through its final directive. Its locally computed SHA-256 and Git blob match the stipulated digest and the blob fetched at the current source commit. fileciteturn41file0L4-L5

I read the final two sections of `docs/Codex/PAPER_CHAIN.md` at the exact source commit: the limited signed-block acceptance and the subsequent fixed-even-offset deduction. The connector identifies that file by Git blob `2e830069aad0475e742467c6be784c80c2c84387`. Its full-file SHA-256 is recorded as supplied by the request, **not claimed independently rehashed**; a raw local download was unavailable. This is distinct from the two local byte-hash checks above. No source-content discrepancy was found in the sections read. fileciteturn42file0L2-L5

**[COFINAL_FAMILY | PAPER — admitted inputs, not new conclusions]** The pinned record accepts
\[
G_{\ell\ell}(M)=M+o(M),\qquad
\sum_{M\le m<2M}w_mE_m=\left(\frac2{\pi^2}+o(1)\right)M\log M.
\]
It also records the resulting cofinal MG128 refutation and the existence of first-gate C128 cells in each late block. Neither is a joint C128 result. The present proof concerns the cross products at the **same** cell and window. fileciteturn42file0L2-L2

**[ABSTRACT | PAPER — prediction ledger]** After source intake and the candidate continuous calculation, but before the final product-sampling self-audit, the recorded prediction was \(G(M)/M\to I_{128}\). The final checks below test its two vulnerable steps: a nonvanishing critical-mesh remainder and an unpaid variable shift. This is a prediction for that self-audit, not a claim to have predicted the answer before deriving the candidate. The checks confirm the prediction. They are not an independent review.

## 2. Exact objects, parity, and complete-source convergence

**[COFINAL_FAMILY | PAPER]** Fix the same \(P\). For all sufficiently large integers \(M\), every integer \(M\le m<2M\) is already of the form
\[
m=J_P+j+2,\quad j\ge1,\quad L_m=\log m\ge1536.
\]
Write \(H=\log M\), and for an offset \(p\) define
\[
\phi_p(x)=\frac{2\pi(x+p)}{\log x},\qquad
\tau(x)=\phi_0(x).
\tag{4}
\]
In this proof \(p,q\) always denote two fixed members of \(\{2,4,\ldots,256\}\); they are offsets, not primes. Thus \(x_{\ell,m}=e_{m+2\ell}(L_m)\).

Retain exactly
\[
\begin{aligned}
g(u)&=\sum_{\alpha\ge1}g_\alpha(u),\\
g_\alpha(u)&=e^{u/2}\mathcal P(\pi\alpha^2e^{2u})e^{-\pi\alpha^2e^{2u}},\\
\mathcal P(X)&=-64X^4+448X^3-660X^2+150X,\\
e_n(\lambda)&=\frac{2(-1)^n}{\sqrt\lambda}
\int_0^{\lambda/2}g(u)\cos(2\pi nu/\lambda)\,du,\\
a_H(t)&=2t^2(t^2+1/4)\pi^{-1/4}|\Gamma(1/4+it/2)|,
\qquad w_m=a_H(\tau(m))^{-2}>0.
\end{aligned}
\tag{5}
\]
Here \(a_H\) denotes the request's \(a_{\rm Hardy}\), not the anchor \(a_m\). There is one common \(w_m\) in every product. fileciteturn38file0L40-L57

For each fixed derivative order, differentiation of a source term gives a polynomial in \(\pi\alpha^2e^{2u}\) times its Gaussian and \(e^{u/2}\). On \(u\ge0\), absorption of the polynomial into part of the exponential gives, for every fixed \(j\),
\[
|g^{(j)}(u)|\le K_j e^{-(\pi/2)e^{2u}},
\tag{6}
\]
with a finite source-defined constant. On compact real intervals the source series and each fixed derivative converge uniformly and absolutely. In particular, for a fixed cell and \(I_{\alpha,p}=\int_0^{L_m/2}g_\alpha(u)\cos(\phi_p(m)u)du\),
\[
\sum_{\alpha\ge1}|I_{\alpha,p}|
\le\sum_{\alpha\ge1}\int_0^{L_m/2}|g_\alpha(u)|du<\infty.
\]
Both source-index sums in the following **exact** expression are retained:
\[
G_{\ell k}(M)=4\sum_{M\le m<2M}\frac{w_m}{L_m}
\sum_{\alpha,\beta\ge1}I_{\alpha,2\ell}I_{\beta,2k}.
\tag{7}
\]
Absolute convergence of this double source sum follows from the product of the two absolute single sums. It is not a replacement by the source-index diagonal \(\alpha=\beta\).

The coefficient phases multiply to \((-1)^{2m+p+q}=1\), because both offsets are even. The coefficient product in (7) has factor **four**, from the two cosine coefficients. There is no additional factor two in the definition of \(G\). The different factor two in \(B_m=2\sum_\ell x_{\ell,m}^2\) still charges both Fourier-index signs. The original \(E_m=E_O(m)+2\sum_{n>m}e_n(L_m)^2\) is not changed or replaced by the Gram diagonal.

## 3. Verified continuous input and endpoint control

### 3.1. The exact external theorem being used

**[ABSTRACT | PAPER — external THEOREM]** Bui–Hall, *On the derivatives of Hardy's function \(Z(t)\)*, arXiv:2304.05178v1, Introduction, equation (1), gives in its equal-order specialization, for **each fixed** integer \(j\ge0\),
\[
\boxed{
\int_0^T |Z^{(j)}(t)|^2dt
=\frac{T}{4^j(2j+1)}Q_{2j+1}\!\left(\log\frac{T}{2\pi}\right)
+O_j\!\left(T^{3/4}(\log T)^{2j+1/2}\right),
}
\tag{8}
\]
where the polynomial is monic of degree \(2j+1\). The normalization is
\(Z(t)=e^{i\theta(t)}\zeta(1/2+it)\), with
\(\theta(t)=\operatorname{Im}\log\Gamma(1/4+it/2)-(t/2)\log\pi\).
This is unconditional. It is a continuous moment theorem, **not** a sampling theorem or a shifted-moment assertion. The formula and normalization were checked in the primary text. citeturn779545view0

Only this fixed-order family, already used by the accepted signed-block argument, is needed. The small-shift theorem in Section 4 is **derived here**. No external shifted theorem, independence principle, or growing-order moment estimate is imported.

For later reference set
\[
\gamma_j=\frac1{4^j(2j+1)}.
\]
On any interval \([A_M,B_M]\) with endpoints comparable to \(T_M=2\pi M/H\) and length \(\Delta_M\sim T_M\), subtraction of (8) at the actual endpoints gives
\[
\int_{A_M}^{B_M}|Z^{(j)}(t)|^2dt
=(\gamma_j+o_j(1))\Delta_M H^{2j+1}.
\tag{9}
\]
This uses \(\log T_M=H+O(\log H)\). The estimate is uniform under bounded multiples of \(H^{-1}\) added to either endpoint. For each fixed order, the primitive error is uniform throughout a comparable frequency band. No primitive error is differentiated.

### 3.2. Endpoint terms are smaller than their crude global bounds

**[ABSTRACT | PAPER — deduction from (8)]** For each fixed \(j\) and \(0<c<C<\infty\),
\[
\boxed{
\sup_{cT\le t\le CT}|Z^{(j)}(t)|^2
=o_j\!\left(T(\log T)^{2j+2}\right).
}
\tag{10}
\]
Here is the needed uniform argument. Fix a small \(\rho>0\) and use an interval of length \(2\rho T\) around \(t\), contained in a slightly larger positive comparable band. From (8), its order-\(j\) square integral is at most
\((C_j\rho+o_j(1))T(\log T)^{2j+1}\), uniformly in the center; the analogous assertion holds at order \(j+1\). Compare the value at \(t\) with a point of at most average square, and apply the fundamental theorem of calculus to the square. The resulting upper bound is an average of logarithmic size plus
\(2\int |Z^{(j)}Z^{(j+1)}|\). Cauchy–Schwarz bounds this latter term by
\((C_j'\rho+o_j(1))T(\log T)^{2j+2}\). First take \(T\to\infty\), and then \(\rho\downarrow0\). This proves (10).

Products, even at two distinct points in the same comparable band, therefore satisfy
\[
\sup_{s,t\in[cT,CT]}|Z^{(i)}(s)Z^{(j)}(t)|
=o_{i,j}\!\left(T(\log T)^{i+j+2}\right).
\tag{11}
\]
This will pay both block endpoints in the product quadrature. It also pays every integration-by-parts boundary used in the next section.

## 4. A derived shifted second moment with the required uniformity

### 4.1. Mixed moments at zero shift

**[ABSTRACT | PAPER — new derivation using the admitted moment family]** On the intervals in (9), put
\[
\eta_{2s}=\frac{(-1)^s}{4^s(2s+1)},\qquad \eta_{2s+1}=0.
\]
Repeated integration by parts and (9)–(11) give, for each fixed \(j\),
\[
\boxed{
\frac{1}{\Delta_M H^{j+1}}
\int_{A_M}^{B_M} Z(t)Z^{(j)}(t)dt\longrightarrow\eta_j.
}
\tag{12}
\]
For \(j=2s\), the integral is \((-1)^s\int (Z^{(s)})^2\), plus finitely many endpoint products whose total derivative order is \(2s-1\). Equation (11) bounds each endpoint product by \(o(T_M H^{2s+1})\). For \(j=2s+1\), integrate until the remaining integral is \(\int Z^{(s)}Z^{(s+1)}=\tfrac12[(Z^{(s)})^2]\); again every endpoint product has total derivative order \(j-1\), and is \(o(T_M H^{j+1})\). Thus both endpoints, not just the upper one, are paid. These formulas are also consistent with the mixed-order statement in Bui–Hall (1), but no additional mixed-order import is needed for this deduction.

### 4.2. Shift theorem, proved rather than assumed

**[ABSTRACT | PAPER — derived SHIFTED MOMENT]** For every fixed \(C>0\), uniformly for real \(|c|\le C\),
\[
\boxed{
\frac1{\Delta_M H}\int_{A_M}^{B_M}
Z(t)Z(t+c/H)dt
=\operatorname{sinc}(c/2)+o_C(1),
\qquad \operatorname{sinc}(y)=\begin{cases}\sin y/y,&y\ne0,\\1,&y=0.\end{cases}
}
\tag{13}
\]
The endpoints and \(\Delta_M\) have exactly the hypotheses of (9). The statement includes moving endpoints and all fixed compact sets of normalized shifts. In particular, taking \(C=508\pi\) covers every shift needed by the 128-by-128 Gram matrix.

To prove it, fix a Taylor order \(N\ge1\) **before** taking the large-\(M\) limit. The integral-remainder formula is exact:
\[
Z(t+c/H)=\sum_{j=0}^{N-1}\frac{(c/H)^j}{j!}Z^{(j)}(t)
+\frac{(c/H)^N}{(N-1)!}\int_0^1(1-v)^{N-1}Z^{(N)}(t+vc/H)dv.
\tag{14}
\]
It is valid also for negative \(c\). Minkowski's inequality and Cauchy–Schwarz, together with the uniform shifted-interval version of (9), give the **explicit limiting remainder bound**
\[
\boxed{
\limsup_{M\to\infty}\sup_{|c|\le C}
\frac{\left|\int_{A_M}^{B_M} Z(t)\,\mathrm{Rem}_N(t,c)dt\right|}
{\Delta_M H}
\le\frac{(C/2)^N}{N!\sqrt{2N+1}}.
}
\tag{15}
\]
Indeed \(\|Z\|_2=(1+o(1))\sqrt{\Delta_M H}\), while the shifted order-\(N\) norm is at most
\((1+o_N(1))\sqrt{\Delta_M}H^{N+1/2}/[2^N\sqrt{2N+1}]\). Integration of \((1-v)^{N-1}\) supplies the remaining \(1/N\). There is **no unspecified order-dependent multiplicative constant** in the limiting right side of (15).

For fixed \(N\), (12) evaluates the finite polynomial in (14), uniformly on \(|c|\le C\). Now let \(N\to\infty\). The bound (15) tends to zero, and the limiting series is
\[
\sum_{s\ge0}\frac{(-1)^s c^{2s}}{4^s(2s+1)(2s)!}
=\sum_{s\ge0}\frac{(-1)^s(c/2)^{2s}}{(2s+1)!}
=\operatorname{sinc}(c/2).
\tag{16}
\]
Uniform convergence on each fixed compact set proves (13). This is a Taylor-remainder argument with fixed orders, not a differentiation of a moment asymptotic or an assertion of uniform estimates when \(N\) grows with \(M\).

### 4.3. The actual variable shift and actual integration interval

**[COFINAL_FAMILY | PAPER]** For fixed even \(p,q\), set
\[
A_M=\phi_p(M),\quad B_M=\phi_p(2M),\quad
\Delta_M=B_M-A_M=(2\pi+o(1))M/H.
\]
The inverse \(x=x_p(t)\) is defined on this actual interval for all sufficiently large \(M\). The second phase is
\[
\phi_q(x_p(t))=t+s_M(t),\qquad
s_M(t)=\frac{2\pi(q-p)}{\log x_p(t)}.
\tag{17}
\]
With \(c=2\pi(q-p)\),
\[
\sup_{[A_M,B_M]}|s_M(t)-c/H|=O_{p,q}(H^{-2}).
\tag{18}
\]
This variable shift is not silently frozen. If the supremum in (18) is \(\varepsilon_M\), the fundamental theorem of calculus gives
\[
|Z(t+s_M(t))-Z(t+c/H)|^2
\le\varepsilon_M\int_{-\varepsilon_M}^{\varepsilon_M}
|Z'(t+c/H+v)|^2dv.
\]
Integrating over the full actual interval and enlarging it by the displayed small shifts yields
\[
\int_{A_M}^{B_M}|Z(t+s_M(t))-Z(t+c/H)|^2dt
=O_{p,q}(\varepsilon_M^2\Delta_M H^3)
=O_{p,q}(\Delta_M/H).
\tag{19}
\]
Both endpoint extensions are included in the enlarged integral and paid by (9). Pairing this with \(\int Z^2=O(\Delta_M H)\) shows that freezing the shift changes the product integral by \(O_{p,q}(\Delta_M)=o(\Delta_M H)\). This argument requires neither a discrete shift bound nor a pointwise derivative estimate on each tiny interval.

The Jacobian obeys
\[
\frac{dx_p}{dt}=\frac{H}{2\pi}(1+O_{p}(H^{-1}))
\]
uniformly. The absolute product integral is \(O_{p,q}(\Delta_M H)\), by (9), (19), and Cauchy–Schwarz. Hence replacing this Jacobian by \(H/(2\pi)\) costs only \(O_{p,q}(M)\). Applying (13) now gives
\[
\boxed{
\int_M^{2M}Z(\phi_p(x))Z(\phi_q(x))dx
=MH\operatorname{sinc}(\pi(q-p))+o_{p,q}(MH).
}
\tag{20}
\]
Every interval in this deduction is an auxiliary integration interval derived from the original \(m\)-mesh. No real parameter is declared to be a new admitted cell.

## 5. Critical product sampling on the actual mesh

Equation (20) is not yet the Gram law. A sampling error of size \(MH\) would change its leading coefficient. This section proves that this error is \(o(MH)\).

### 5.1. Marginal norms, without a discrete moment assumption

**[COFINAL_FAMILY | PAPER]** For each fixed offset \(p\) and derivative order \(j\), the spacings of \(\phi_p(m)\) are comparable to \(H^{-1}\). Applying the fundamental theorem of calculus to \(|Z^{(j)}|^2\) on disjoint intervals of that length around the sample points gives
\[
\sum_{M\le m<2M}|Z^{(j)}(\phi_p(m))|^2
\le C_j\left(H\int |Z^{(j)}|^2+\int |Z^{(j)}Z^{(j+1)}|\right)
=O_{p,j}(MH^{2j+1}).
\tag{21}
\]
The integrals are over one enlarged comparable frequency band, including the first and last short intervals. Formula (8) and Cauchy–Schwarz justify the last bound. This is a coarse upper bound derived from continuous moments, not an assumed discrete asymptotic.

For the real-\(x\) integrals a sharper marginal statement follows directly by change of variables and (9):
\[
\boxed{
\int_M^{2M}|Z^{(j)}(\phi_p(x))|^2dx
=(\gamma_j+o_{p,j}(1))MH^{2j+1}.
}
\tag{22}
\]
Consequently the integrated absolute product of orders \(j\) and \(r-j\), at the two different phases, is at most
\[
\left[\frac{1}{2^r\sqrt{(2j+1)(2r-2j+1)}}+o_{p,q,r}(1)\right]MH^{r+1}.
\tag{23}
\]
This use of Cauchy–Schwarz concerns marginal norms only. It does not assert a value or sign for their covariance.

### 5.2. Principal derivatives and the decaying remainder constant

**[ABSTRACT | PAPER — exact quadrature input]** For a fixed even \(r\ge2\), Euler–Maclaurin on the half-open integer block is
\[
\begin{aligned}
\sum_{m=M}^{2M-1}Y(m)-\int_M^{2M}Y(x)dx
={}&\frac{Y(M)-Y(2M)}2\\
&+\sum_{j=1}^{r/2}\frac{B_{2j}}{(2j)!}
\big(Y^{(2j-1)}(2M)-Y^{(2j-1)}(M)\big)+\mathrm{Err}_r,
\end{aligned}
\]
with
\[
|\mathrm{Err}_r|\le\frac{2\zeta(r)}{(2\pi)^r}\int_M^{2M}|Y^{(r)}(x)|dx.
\tag{24}
\]
The form with the last Bernoulli boundary separated follows from DLMF 2.10.1. The periodic Bernoulli Fourier series, DLMF 24.8.1, gives the displayed remainder constant. Both endpoints, including the omitted upper integer sample, appear explicitly. citeturn286296view1turn286296view2

**[COFINAL_FAMILY | PAPER — new PRODUCT SAMPLING]** Apply (24) to
\(Y(x)=Z(\phi_p(x))Z(\phi_q(x))\). For fixed offsets,
\[
\phi_p'(x)=\frac{2\pi}{H}(1+O_p(H^{-1})),\qquad
\phi_p^{(j)}(x)=O_{p,j}(M^{1-j}H^{-2})\quad(j\ge2).
\tag{25}
\]
The principal part of \(Y^{(r)}\) is
\[
\sum_{j=0}^{r}\binom rj
(\phi_p')^j(\phi_q')^{r-j}
Z^{(j)}(\phi_p)Z^{(r-j)}(\phi_q).
\tag{26}
\]
Using (23), its integrated absolute value is at most
\[
\left[(2\pi)^r\alpha_r+o_{p,q,r}(1)\right]MH,
\qquad
\alpha_r=2^{-r}\sum_{j=0}^{r}\binom rj
\frac1{\sqrt{(2j+1)(2r-2j+1)}}.
\tag{27}
\]
The leading coefficient is explicit. In particular it has no additional \(C_r\) which could spoil the subsequent order limit.

Every other chain-rule term contains at least one derivative \(\phi^{(j)}\) with \(j\ge2\). For fixed \(r\), (25) supplies at least one inverse power of \(M\) relative to the principal terms. The finitely many remaining factors have only fixed logarithmic powers. Applying the continuous marginal bounds as in (23) makes the sum of their absolute integrals \(o_{p,q,r}(MH)\). Large constants depending on the fixed order occur only in this vanishing error, not in the leading coefficient of (27).

To see explicitly why \(\alpha_r\) tends to zero, regard its binomial weights as those of \(J\sim\mathrm{Binomial}(r,1/2)\), solely as notation for a finite sum. On \(r/4\le J\le3r/4\), the reciprocal square root is at most \(2/r\). Outside, it is at most one and the variance bound gives probability at most \(4/r\). Thus
\[
\boxed{\alpha_r\le6/r\quad(r\ge4).}
\tag{28}
\]
This is not a probabilistic model for the source.

### 5.3. Both endpoints and the order of limits

**[COFINAL_FAMILY | PAPER]** By (11), a principal endpoint term of derivative order \(i\) has size
\[
O_{p,q,i}(H^{-i})\,
 o_i(T_M H^{i+2})=o_{p,q,i}(MH).
\]
Terms containing a higher phase derivative are smaller. This controls separately every term at \(M\) and \(2M\) in (24), for every fixed \(r\). No endpoint with a shifted phase is suppressed by notation.

Equations (24)–(28) therefore imply
\[
\limsup_{M\to\infty}
\frac{\left|\sum_{M\le m<2M}Z(\phi_p(m))Z(\phi_q(m))
-\int_M^{2M}Z(\phi_p(x))Z(\phi_q(x))dx\right|}{MH}
\le2\zeta(r)\alpha_r.
\tag{29}
\]
Take \(M\to\infty\) at each fixed even \(r\), and only then let even \(r\to\infty\). The right side tends to zero, proving
\[
\boxed{
\sum_{M\le m<2M}Z(\phi_p(m))Z(\phi_q(m))
=\int_M^{2M}Z(\phi_p(x))Z(\phi_q(x))dx+o_{p,q}(MH).
}
\tag{30}
\]
The proof applies to the cross product, not just to \(Z^2\). It uses separate marginal derivative moments to bound (26), and the exact signed product remains in (30). There is no assumption of independence and no substitution of a continuous theorem for the discrete conclusion.

Combining (20) and (30) already yields
\[
\sum_{M\le m<2M}Z(\phi_p(m))Z(\phi_q(m))
=MH\operatorname{sinc}(\pi(q-p))+o_{p,q}(MH).
\tag{31}
\]
The Taylor order in Section 4 and the quadrature order here are independent auxiliary fixed integers. For any requested error tolerance, choose both finite orders first and then take \(M\) beyond their thresholds. Neither order depends on \(M\).

## 6. Return to the exact finite-window coefficients

### 6.1. Two window errors and all their cross terms

**[COFINAL_FAMILY | PAPER — admitted transform, retained remainder]** The complete-source transform accepted in the signed-block source, its equation (9), is
\[
F(t)=\int_{\mathbb R}g(u)e^{itu}du
=4t^2\xi(1/2+it)=-a_H(t)Z(t).
\tag{32}
\]
It uses evenness of the **complete** source. An individual theta summand is not substituted for that source. fileciteturn44file0L2-L2

For an integer \(n\ge1\), set \(b=\lambda/2\), \(t_n=2\pi n/\lambda\). The exact finite-window formula is
\[
\begin{aligned}
e_n(\lambda)&=\widetilde e_n(\lambda)+\varepsilon_n(\lambda),\\
\widetilde e_n(\lambda)&=(-1)^{n+1}\lambda^{-1/2}a_H(t_n)Z(t_n),\\
\varepsilon_n(\lambda)&=-\frac{2(-1)^n}{\sqrt\lambda}
\int_b^\infty g(u)\cos(t_nu)du.
\end{aligned}
\tag{33}
\]
Two integrations by parts, with \(\sin(t_nb)=0\) and \(\cos(t_nb)=(-1)^n\), give
\[
\boxed{
\varepsilon_n(\lambda)=\frac{2}{\sqrt\lambda\,t_n^2}
\left[g'(b)+(-1)^n\int_b^\infty g''(u)\cos(t_nu)du\right].
}
\tag{34}
\]
The derivative endpoint is present, not declared zero. Equation (6) then gives the source-uniform bound
\[
|\varepsilon_n(\lambda)|\le C\lambda^{3/2}n^{-2}
 e^{-(\pi/2)e^\lambda}\qquad(\lambda\ge1,n\ge1).
\tag{35}
\]
This agrees with the accepted combined-window estimate. No separate infinite-tail endpoint and bulk norms are taken.

For completeness, if the original window coefficient is differentiated, its exact first derivative is
\[
e_n'(\lambda)=-\frac{e_n(\lambda)}{2\lambda}
+\frac{g(\lambda/2)}{\sqrt\lambda}
+\frac{4\pi n(-1)^n}{\lambda^{5/2}}
\int_0^{\lambda/2}u g(u)\sin(2\pi nu/\lambda)du.
\tag{36}
\]
Thus the nonzero moving endpoint has not been lost. The product quadrature above differentiates the exact full-line principal expression only **after** using (33)–(35) to bound its difference from each actual coefficient; it is not an assertion that (36) has no endpoint.

At the original \(\lambda=L_m\), the original weight obeys \(w_m\le C\exp(\pi^2m/L_m)\) for late \(m\), by the accepted gamma asymptotic for \(a_H\). Consequently, for each fixed offset \(p\),
\[
\sum_{M\le m<2M}w_m|\varepsilon_{m+p}(L_m)|^2
\le C_p M^{C_p}e^{-cM},\qquad c>0.
\tag{37}
\]
The coefficients \(\widetilde e\) have \(\sum w_m|\widetilde e_{m+p}|^2=O_p(M)\) by (21) and the amplitude ratio below. Therefore Cauchy–Schwarz pays **both** mixed errors and their product in
\[
e_{m+p}e_{m+q}-\widetilde e_{m+p}\widetilde e_{m+q}
=\varepsilon_{m+p}\widetilde e_{m+q}
+\widetilde e_{m+p}\varepsilon_{m+q}
+\varepsilon_{m+p}\varepsilon_{m+q}.
\tag{38}
\]
Their weighted sum is exponentially small, in particular \(o(M)\). This calculation neither drops a source-index cross term nor changes the finite window.

### 6.2. The common weight and the exact leading factor

**[COFINAL_FAMILY | PAPER]** The accepted gamma estimate is
\(a_H(t)=C_a t^{15/4}e^{-\pi t/4}(1+O(t^{-1}))\). fileciteturn44file0L2-L2 Applying it to the two fixed offsets at the same \(m\) gives
\[
\frac{a_H(\phi_p(m))a_H(\phi_q(m))}{a_H(\tau(m))^2}
=\exp\!\left(-\frac{\pi^2(p+q)}{2L_m}\right)
\big(1+O_{p,q}(H^2/M)\big).
\tag{39}
\]
All weights remain \(w_m\). In particular no weight at \(m+p\) or \(m+q\) is introduced. Since \(L_m=H+O(1)\),
\[
\frac1{L_m}\frac{a_H(\phi_p(m))a_H(\phi_q(m))}{a_H(\tau(m))^2}
=\frac1H\left(1+O_{p,q}(H^{-1})+O_{p,q}(H^2/M)\right).
\tag{40}
\]
The coarse product bound from (21) is
\(\sum_m|Z(\phi_p(m))Z(\phi_q(m))|=O_{p,q}(MH)\). It makes the total error in replacing (40) by \(1/H\) equal to \(o(M)\), even though the off-diagonal product has no prescribed sign.

For even offsets, the two phases in (33) multiply to one. Equations (31), (33), and (37)–(40) prove
\[
\boxed{
\sum_{M\le m<2M}w_m e_{m+p}(L_m)e_{m+q}(L_m)
=M\operatorname{sinc}(\pi(q-p))+o_{p,q}(M).
}
\tag{41}
\]
For \(p=2\ell,q=2k\), the sinc argument is \(2\pi(k-\ell)\). Its value is one on the diagonal and zero for distinct integer indices. This proves (1). It also cross-checks the accepted diagonal normalization without adding or deleting a factor two.

The family of pairs is finite. Taking the maximum of their normalized errors yields a function tending to zero; the operator norm is at most 128 times the largest absolute entry. Thus the matrix convergence stated after (1) follows without any claim for a prefix length growing with \(M\).

## 7. The dispersion consequence and its exact quantifiers

**[COFINAL_FAMILY | PAPER — new result for the requested scalar]** By definition,
\[
\begin{aligned}
\sum_{M\le m<2M}w_m J_m^{\rm disp}
&=\sum_{\ell=1}^{128}
\big(G_{\ell\ell}(M)+G_{11}(M)-2G_{1\ell}(M)\big)\\
&=254M+o(M).
\end{aligned}
\tag{42}
\]
There are 127 nontrivial differences. The \(\ell=1\) difference is exactly zero, not another diagonal contribution.

Also
\[
C_M=\sum_{\ell=2}^{128}G_{1\ell}(M)=o(M).
\]
Using either (42) or the request's exact expansion gives
\[
\boxed{
D_M=8G_{11}(M)-\sum_m w_mJ_m^{\rm disp}
=-246M+o(M).
}
\tag{43}
\]
The independent arithmetic check is \(-128-120+2=-246\) in the expanded form. This establishes the strict upper envelope (3) after increasing one threshold.

Choose an integer \(M_*(P)\) beyond the analytic thresholds with \(M_*(P)\ge J_P+3\) and \(\log M_*(P)\ge1536\). Then (3) holds for every integer block start \(M\ge M_*(P)\). Because every \(w_m>0\), each such block contains at least one original admitted cell with
\[
\boxed{8a_m^2-J_m^{\rm disp}<0.}
\tag{44}
\]
The proof does not compute the threshold or the first such cell. Existence on every sufficiently late block is obtained from a proved strict upper bound for the actual weighted sum, not from a numerical sample, an abstract vector, or a failed sufficient estimate.

This is exactly the permitted consequence of the diagonal Gram outcome. The first-gate witnesses accepted in the request can lie at different cells; no intersection is proved. A negative \(D_M\) also allows other cells with \(J_m^{\rm disp}\le8a_m^2\). Thus this result does **not** establish or exclude existential C128, and it does not decide PC, SV, or any later source sign. fileciteturn38file0L78-L86

## 8. Adversarial checks and route assessment

**[ABSTRACT | PAPER — zero-shift and phase checks]** At \(p=q\), (13) has \(c=0\), its normalized moment is one, and (41) reproduces the admitted \(M+o(M)\) diagonal. At \(p\ne q\), the actual difference is \(2\pi(q-p)/\log x\), not half that quantity; Section 4 pays its replacement by \(2\pi(q-p)/H\). For even offsets the coefficient phases are equal. These checks prevent a false sign or nonzero main term caused by a phase or factor-two error.

**[ABSTRACT | PAPER — planted sampling failure]** Integer spacing alone is not a quadrature theorem: for the diagnostic function \(Y_M(x)=H\cos(2\pi x)\) on the same integer block, its sum is \(MH\), while its integral is zero. Its normalized derivative remainder does not have the decay (28). This abstract diagnostic is not source evidence; it checks why the explicit leading constant in (27) and the order of limits in (29) are necessary.

**[COFINAL_FAMILY | PAPER — strongest objection and response]** The principal possible error is treating an unshifted diagonal sampling result as if it automatically covered a product. Equations (23), (26), and (27) explicitly bound the derivatives of the two-phase product and recover the same \(\alpha_r\), without multiplying its limiting coefficient by an uncontrolled order-dependent constant. Equations (11) and (29) pay the endpoints. Independently, (15) gives a factorial Taylor remainder with its exact leading norm constant; this is what allows a compact-uniform shifted moment rather than a guessed sinc profile. Neither limiting-order argument authorizes an order growing with \(M\).

**[COFINAL_FAMILY | PAPER — source and consequence objections]** Using \(F=-a_HZ\) without (33)–(38) would change the coefficients. Those equations keep the two source remainders, their endpoint terms, and all their cross terms. Inferring a joint C128 event from the first-gate average, or a C128 exclusion from (43), would change the quantifiers. Neither inference is made.

| Representation | Decisive power and cost | Status |
|---|---|---|
| **Derived compact-shift moment plus two-phase product quadrature. [COFINAL_FAMILY; PAPER]** | Determines every fixed Gram entry and the requested scalar. Cost: fixed-order moments, explicit Taylor and Bernoulli remainders, two window corrections. | Completed here; independent PAPER audit required. |
| **Direct complete-source double cosine kernel (7). [COFINAL_FAMILY; CONDITIONAL]** | Could determine the same cross products without a full-line transform, but must pay signed cancellation at the same original weighted scale. | Exact representation only; not claimed as a second proof or a new task. |

## 9. Closeout and dependency boundary

**[COFINAL_FAMILY | PAPER]** What became smaller is the actual fixed-prefix off-diagonal question: all 128-by-128 entries have a proved leading term, and the second-gate weighted block has a strict negative upper envelope. The accepted diagonal and MG128 results are preserved; they were not substituted for the new off-diagonal argument.

No route family or existential C128 claim is killed. In particular a result about the scalar \(D_M\) does not promote the original PC, transport, prime/square, or Schur-floor consumers. The prediction registered for the final self-audit is confirmed by the explicit shifted moment and product quadrature; neither a coefficient experiment nor independent review occurred.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: ORIGINAL_D_M_SECOND_C128_GATE_BLOCK_TEST
ACTUAL_CONSUMER_REQUIREMENT: C_M_upper_bound_strictly_below_123M_eventually_would_suffice
ORIGINAL_REQUESTED_OBJECT: FIXED_EVEN_PREFIX_GRAM_OR_DECISIVE_ANCHOR_ROW_BOUND
ORIGINAL_OBJECT_IS: NOT_NECESSARY
ORIGINAL_OBJECT_QUALIFICATION: full_diagonal_Gram_law_is_stronger_than_needed_for_negative_D_M
KNOWN_WEAKER_INTERFACES:
  - limsup_C_M_over_M_LT_123_implies_D_M_LT_0_eventually
  - direct_negative_upper_envelope_for_D_M_bypasses_full_matrix_convergence
FAILURE_TYPE: OTHER
FAILURE_TYPE_QUALIFICATION: no_failure_of_the_requested_Gram_proof_is_claimed
EPISTEMIC_STATUS: UNRESOLVED
EPISTEMIC_STATUS_SCOPE: joint_C128_and_downstream_source_receivers_only
REQUESTED_GRAM_TEST: CLOSED_PAPER_PENDING_INDEPENDENT_AUDIT
KILL_SCOPE: NONE
FIRST_UNPAID_COMPARISON_FOR_THIS_GRAM_TEST: NONE_IN_THE_PRESENT_PAPER_ARGUMENT
NEW_DISCRIMINATOR: MINUS_D_M_over_M_MINUS_123
DISCRIMINATOR_RESULT: STRICTLY_POSITIVE_EVENTUALLY
REOPEN_TRIGGER_FOR_GRAM_RESULT: error_in_compact_shift_remainder_product_quadrature_endpoint_or_window_product_budget
RESEARCH_DEBT: simultaneous_first_and_second_C128_gate_on_one_original_cell
RESEARCH_DEBT_REOPEN_TRIGGER: a_joint_source_estimate_not_separate_marginal_block_averages
NOVELTY_AXIS: explicit_fixed_order_moment_constants_pay_two_phase_critical_sampling_and_derive_sinc_orthogonality
MEMORY_ENTRY:
  target: source_core_fixed_128_even_prefix_Gram
  status: PROVED_FIXED_PAIR_GRAM_AND_NEGATIVE_DISPERSION_BLOCK
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: all_fixed_even_offsets_share_one_original_weight_but_have_a_nontrivial_shifted_product_to_be_proved
  forbidden_future_move: call_negative_average_dispersion_a_universal_or_existential_C128_decision
  next_decisive_test: independent_PAPER_audit_of_equations_12_through_43
```

**[COFINAL_FAMILY | PAPER — preservation]** The original complete source, carrier, \(Q=\sqrt m\), \(5m\) splice, \(N,K\), panel, literal diagonal, zero node, final descent, paired logarithmic kernel, and signed correction are unchanged. The physical exterior remains in the original \(E_m\), with both Fourier signs. The low epsilon block, prime/square block, opposite-side correlation, transfer, first \(\tau_j\) sign, Schur-floor, SV, lag, and RH are not decided here. No conditional square constant is activated. There was no mathematical runtime, coefficient or grid search, source truncation, fitted cutoff, Lean execution, repository write, or route promotion. Local execution was file reading, text writing, validation, and hashing only. fileciteturn38file0L91-L99

## CODEX DIRECTIVE

**Perform one read-only independent PAPER audit of this fixed-even-prefix Gram proof against the unchanged request hash and source commit.** Verify the exact normalization and fixed-order constants of (8); the endpoint deduction (10)–(12); the compact-uniform Taylor remainder (15), including negative shifts and the order of limits; the paid variable-shift and Jacobian errors (18)–(20); and especially the two-phase product derivatives (26), the leading remainder coefficient (27)–(29), and both half-open-block endpoint groups. No order-dependent constant may be hidden in front of the limiting \(\alpha_r\), and neither auxiliary order may grow with \(M\). Check both finite-window errors and their cross products (33)–(38), the original common weight and parity in (39)–(41), and the 127 nontrivial dispersion differences yielding \(-246\), not \(-248\) or a doubled coefficient. Accept only `SOURCE_EVEN_PREFIX_GRAM_DIAGONAL`, the fixed-pair law (1), and the consequence (44) in every sufficiently late original block if those checks pass. If a step fails, report the first invalid estimate and withhold this new Gram conclusion without silently changing the accepted pinned record. Do not infer a joint C128 witness or exclusion, identify the first-gate and second-gate cells, or promote PC, SV, lag, Schur-floor, or RH. No numerical search, mathematical runtime, source deletion, new mask/panel, Lean, repository write, conditional-constant activation, or route promotion is authorized.
