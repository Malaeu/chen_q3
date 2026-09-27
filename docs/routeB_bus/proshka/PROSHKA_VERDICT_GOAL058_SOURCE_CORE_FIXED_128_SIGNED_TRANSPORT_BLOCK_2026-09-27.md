# STATUS: TRY_GOAL058_SOURCE_CORE_FIXED_128_SIGNED_TRANSPORT_BLOCK

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_FIXED_128_SIGNED_TRANSPORT_BLOCK
OUTCOME: SOURCE_SIGNED_TRANSPORT_BLOCK_NONNEGATIVE
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-FIXED-128-SIGNED-TRANSPORT-BLOCK
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_FIXED_128_SIGNED_TRANSPORT_BLOCK
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 5a71229b32d63860188261b3678d9badedebf7fc
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_SHA256_LOCALLY_VERIFIED: 72189a47c5d8a09e1903b0fa991faf36b4d5e0a7a01182c7a84187c6edc1b2a3
REQUEST_BYTES: 6484
REQUEST_LF: 121
REQUEST_CR: 0
REQUEST_UTF8_BOM: false
REQUEST_FINAL_LF: true
REQUEST_GIT_BLOB_LOCALLY_COMPUTED: 4b0179703be0e3dcdf36dbd4eddeb4fa9249684b
PREDECESSOR: REQ-2026-09-27-SOURCE-CORE-FIXED-128-PATH-VARIANCE-COMPENSATION
PREDECESSOR_SHA256_LOCALLY_VERIFIED: 17cf49ca3958c270da791562fc8000c5e9a246460327f99b598cf09c4761e431
PREDECESSOR_BYTES: 37229
PREDECESSOR_LF: 620
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: ada9ae739191b1ba8ce34e2798d9fdbc3f2d63cc
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_GIT_BLOB_READ: de63bbd11fb350dd45771fc433a29c7031f105fe
AUDIT_SECTION: source_core_fixed_128_path_variance_compensation_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SIGNED_BLOCK_ASYMPTOTIC: BT_M_EQUALS_4_OVER_pi_squared_TIMES_M_log_M_PLUS_o_M_log_M
STRICT_EVENTUAL_LOWER_ENVELOPE: BT_M_GT_2_OVER_pi_squared_TIMES_M_log_M
QUANTIFIER: EVERY_SUFFICIENTLY_LARGE_INTEGER_BLOCK_START_M_FOR_THE_SAME_FIXED_P
ACTUAL_SIGNED_COVARIANCE_BLOCK: o_M_log_M
POSITIVE_L_W_BLOCK: O_D_M
EXTERIOR_L_O_BLOCK: EXPONENTIALLY_SMALL
DELAYED_ENERGY: KEPT_AT_ITS_ORIGINAL_WINDOW_AND_WITH_THE_SAME_w_m
NEW_SAMPLING_RESULT: CRITICAL_MESH_EULER_MACLAURIN_QUADRATURE_FOR_Z_squared_AND_ITS_FIRST_DERIVATIVE
NEW_USE_OF_EXTERNAL_INPUT: Bui_Hall_equation_1_FOR_EACH_FIXED_DERIVATIVE_ORDER
DERIVATIVE_ORDER_GROWS_WITH_M: false
ORDER_OF_LIMITS: FIX_EVEN_r_THEN_M_TO_INFINITY_THEN_r_TO_INFINITY
DISCRETE_HARDY_MOMENT_ASSUMED: false
ASYMPTOTIC_ERROR_DIFFERENTIATED: false
POINTWISE_MT128: OPEN
MG128: OPEN
MG128_DISJUNCTION_ARM_SELECTED: NONE
C128: OPEN
PC: OPEN
PREDECESSOR_PDA128_AND_PIB128_REFUTATIONS: PRESERVED
NEW_THEOREM_SHAPE_KILL: NONE
SV: OPEN
LAG: OPEN
SCHUR_FLOOR: OPEN
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: ORIGINAL_SIGNED_BLOCK_QUANTIFIER_CLOSED_ONLY
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
ROUTE_SCORE: 5
NEW_PROOF_INDEPENDENTLY_AUDITED: false
NEXT_TASK: INDEPENDENT_PAPER_AUDIT_OF_SIGNED_BLOCK_ASYMPTOTIC
MATHEMATICAL_RUNTIME_EXECUTED: false
COEFFICIENT_NUMERICS_EXECUTED: false
SELECTED_CELL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_RUNTIME_USE: FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY
REPOSITORY_WRITTEN: false
SOURCE_INDEX_TRUNCATED: false
SOURCE_FAMILY_CHANGED: false
ORIGINAL_WEIGHTS_OR_ENERGIES_CHANGED: false
ORIGINAL_CARRIER_Q_SPLICE_N_K_PANEL_CHANGED: false
CONDITIONAL_SQUARE_CONSTANTS_ACTIVATED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **SOURCE_SIGNED_TRANSPORT_BLOCK_NONNEGATIVE.** More precisely, for the complete source, the original positive weights, and every sufficiently large integer block start,
\[
\boxed{BT_M=\left(\frac4{\pi^2}+o(1)\right)M\log M.}
\tag{1}
\]
In particular, there is an integer \(M_*(P)\) such that
\[
\boxed{BT_M>\frac2{\pi^2}M\log M>0\qquad(M\ge M_*(P)).}
\tag{2}
\]
This is a **block-average fact only**. It neither proves pointwise MT128 nor selects a branch of the MG128 disjunction. The previously accepted PDA128 and PIB128 refutations remain intact.

The source-specific calculation is
\[
\begin{aligned}
\sum w_mS_m&=\left(\frac4{\pi^2}+o(1)\right)M\log M,\\
\sum w_m\,2L_m\langle u_m,v_m\rangle&=o(M\log M),\\
0\le\sum w_mL_mW_m&=O_D(M),\\
\sum w_mL_mO_m&=O(M^C e^{-cM}),\qquad c>0.
\end{aligned}
\tag{3}
\]
All sums in this file are over the original integers \(M\le m<2M\), unless another range is displayed. The covariance in (3) is the actual signed covariance, not action, variance, or an average of \(\mathscr Q_m\).

The new load-bearing step is an explicit **quadrature theorem**—a justified replacement of the prescribed discrete sums by integrals—for \(Z^2\) and \((Z^2)'\) at the logarithmic mesh. It uses the unconditional continuous derivative moments for each fixed order. The order is fixed before the large-block limit; no growing-order moment estimate is assumed. The proof below is new and has not received independent review.

## 1. Source lock, accepted evidence, and registration

**[FINITE_CELL | PAPER — provenance]** The authoritative attachment was read in full: 6,484 bytes, 121 LF, valid UTF-8, no CR or BOM, final LF present. Its locally computed SHA-256 is the stipulated `72189a47c5d8a09e1903b0fa991faf36b4d5e0a7a01182c7a84187c6edc1b2a3`. The ID, boundary, pin, and predecessor binding agree with the canonical request. The selected task is the new signed block, not the earlier pointwise transport question. fileciteturn34file0L1-L19 fileciteturn34file0L80-L106

The complete mounted predecessor was read through its final directive. Its local SHA-256 and Git blob match the stipulated digest and the connector's pinned blob, respectively. The file contains 37,229 bytes and 620 LF. Thus the complete local proof, not the connector's opening excerpt, is the text used here. fileciteturn36file0L4-L5

The bootstrap was fetched from `rh_clean` and read through its response-format section. I also read the complete named audit in `docs/Codex/PAPER_CHAIN.md` at the source commit. It accepts VAVG128 and the cofinal PIB128 refutation, not a sign of the signed transport. Its independent reviews do not cover this new argument. fileciteturn37file0L2-L2

**[ABSTRACT | PAPER — registration]** Before the new sampling proof was audited, the registered test was whether the signed covariance is lower-order on the original weighted blocks. Sections 5–7 close that test. The exact coefficient in (1) is a derived result, not a retrospectively registered prediction. No individual-cell sign was predicted or evaluated.

## 2. Exact source, two-window signs, and the quantity being estimated

**[COFINAL_FAMILY | PAPER — unchanged contract]** Fix the same \(P\), \(D=256\), and
\[
m=J_P+j+2,\quad j\ge1,\quad L=\log m\ge1536,
\quad L_+=\log(m+D),\quad L_-=\log(m-1).
\]
Write \(\delta_+=L_+-L\) and \(\delta_-=L-L_-\). Use the complete theta source and coefficients specified in the request:
\[
\begin{aligned}
g(u)&=\sum_{\alpha\ge1} e^{u/2}\mathcal P(\pi\alpha^2e^{2u})e^{-\pi\alpha^2e^{2u}},\\
\mathcal P(x)&=-64x^4+448x^3-660x^2+150x,\\
e_n(\lambda)&=\frac{2(-1)^n}{\sqrt\lambda}
 \int_0^{\lambda/2}g(u)\cos(2\pi n u/\lambda)\,du.
\end{aligned}
\tag{4}
\]
At every actual cell the energy remains
\[
E_s=E_O(s)+2\sum_{n>s}e_n(\log s)^2,
\quad E_O(s)=2\int_{(\log s)/2}^\infty g(u)^2du,
\quad S_m=E_m+E_{m-1}.
\tag{5}
\]
The factors two charge both Fourier-index signs. The complete source is even; no individual theta summand is assumed even. The contract fixes the same carrier, \(Q\), splice, \(N,K\), and panel throughout. fileciteturn34file0L31-L58

**[COFINAL_FAMILY | PAPER — normalization and signs]** For \(f_\lambda(x)=\sqrt\lambda g(\lambda x)\) on \([-1/2,1/2]\), the coefficients in the orthonormal basis \((-1)^n e^{2\pi inx}\) are \(e_n(\lambda)\). Parseval gives
\[
G-A_r(\lambda)=2\int_{\lambda/2}^\infty g^2
 +2\sum_{n>r}e_n(\lambda)^2,
\quad G=2\int_0^\infty g^2,
\quad A_r=e_0^2+2\sum_{n=1}^r e_n^2.
\]
The exact partition of \(m+1,\ldots,m+D\) into even and odd offsets gives
\(A_{m+D}-A_m=B_m(\lambda)+B_{m-1}(\lambda)\). Consequently,
\[
\Delta_m=-\int_L^{L_+}A_{m+D}'(\lambda)d\lambda
          -\int_{L_-}^{L}B_{m-1}'(\lambda)d\lambda.
\tag{6}
\]
Both signs are minus. In particular the actual \(B_{m-1}\) remains at \(L_-\).

Keep the request's fixed Hilbert space, vectors \(u_m,v_m\), and \(W_m=\|v_m\|^2\). Their norm partitions give
\[
\|u_m\|^2=E_m-E_O(m)-B_m(L)\le E_m,
\]
\[
\boxed{T_m=S_m-L_mO_m+2L_m\langle u_m,v_m\rangle+L_mW_m.}
\tag{7}
\]
The backward component of \(v_m\) points from \(L\) to \(L_-\). Neither that sign nor the finite odd block is absorbed into the forward tail. Equation (7), with its common original weight, is the receiver used below. fileciteturn34file0L60-L91

## 3. External input and consequences needed for sampling

### 3.1. Exact moment family and normalization

**[ABSTRACT | PAPER — external THEOREM]** Bui–Hall, *On the derivatives of Hardy's function Z(t)*, BLMS 55 (2023), 2304–2323, DOI `10.1112/blms.12859`, equation (1), gives, for every fixed integer \(j\ge0\),
\[
\boxed{\int_0^T |Z^{(j)}(t)|^2dt
=\frac{T}{4^j(2j+1)}Q_{2j+1}\!\left(\log\frac{T}{2\pi}\right)
+O_j\!\left(T^{3/4}(\log T)^{2j+1/2}\right),}
\tag{8}
\]
with a monic polynomial of the indicated degree. This is the equal-order specialization of their formula, without RH. Their normalization is
\(Z(t)=e^{i\theta(t)}\zeta(1/2+it)\),
\(\theta(t)=\operatorname{Im}\log\Gamma(1/4+it/2)-(t/2)\log\pi\).
The new use here is the **family of fixed orders**, rather than only orders zero through two. citeturn400733view0

The accepted complete-source identity and original weight are
\[
F(t)=\widehat g(t)=4t^2\xi(\tfrac12+it)=-a(t)Z(t),
\quad a(t)=2t^2(t^2+\tfrac14)\pi^{-1/4}|\Gamma(\tfrac14+it/2)|,
\quad w_m=a(2\pi m/\log m)^{-2}.
\tag{9}
\]
No new weight is selected. Gamma asymptotics and the separate digamma expansion give
\[
a(t)=C_a t^{15/4}e^{-\pi t/4}(1+O(t^{-1})),
\qquad p(t):=a'(t)/a(t)=-\pi/4+O(t^{-1}),
\tag{10}
\]
so \(p\) is bounded on the large frequencies in question. These follow from DLMF 5.11.9 and 5.11.2; an asymptotic error is not differentiated. citeturn400733view3

### 3.2. Product-derivative constants that tend to zero

The following are new deductions from (8), not quoted discrete moment theorems.

**[ABSTRACT | PAPER]** Put \(f(t)=Z(t)^2\), and for integers \(r\ge0\) define
\[
\alpha_r=2^{-r}\sum_{j=0}^r
\binom rj\frac1{\sqrt{(2j+1)(2r-2j+1)}}.
\tag{11}
\]
On an interval \(I\) whose endpoints are comparable with \(T\) and whose length is \((1+o(1))T\), the product rule, Cauchy–Schwarz, and (8) give
\[
\boxed{\int_I|f^{(r)}(t)|dt
\le (|I|+o_r(T))(\log T)^{r+1}\alpha_r.}
\tag{12}
\]
Indeed each product \(Z^{(j)}Z^{(r-j)}\) has the corresponding leading upper coefficient in (11). The derivatives act on the exact functions, not on a moment remainder.

Crucially, \(\alpha_r\to0\). If \(J\) is binomial with parameters \((r,1/2)\), (11) is the expectation of the displayed reciprocal square root. On \(r/4\le J\le3r/4\) it is at most \(2/r\); outside this range the probability is at most \(4/r\) by the variance bound, and the reciprocal is at most one. Thus
\[
\boxed{\alpha_r\le6/r\quad(r\ge4).}
\tag{13}
\]
This elementary random-variable notation describes only a finite binomial sum; it is not a random model for source coefficients.

### 3.3. Endpoint bounds derived from the same moments

**[ABSTRACT | PAPER]** For each fixed \(j\), (8) and the fundamental theorem of calculus imply
\[
|Z^{(j)}(t)|^2\le C_j t\log^{2j+2}(2+t)\qquad(t\ge1).
\tag{14}
\]
For example, compare its value with a point of at most average square on \([t/2,2t]\), then use \(2\int|Z^{(j)}Z^{(j+1)}|\).

A refinement which will pay all block endpoints is
\[
\boxed{\sup_{cT\le t\le CT}|Z^{(j)}(t)|^2
=o_j(T(\log T)^{2j+2})\quad(0<c<C<\infty).}
\tag{15}
\]
Here is a proof, rather than a pointwise conjecture. Fix a small \(\rho>0\) and use an interval of length \(2\rho T\) about any such \(t\), inside a slightly larger fixed band. Formula (8), subtracted at the interval endpoints, gives uniformly
\(\int |Z^{(j)}|^2\le(C_j\rho+o_j(1))T(\log T)^{2j+1}\),
and the analogous bound for order \(j+1\). The preceding fundamental-theorem estimate bounds the value by an average of order \((\log T)^{2j+1}\) plus
\((C_j'\rho+o_j(1))T(\log T)^{2j+2}\). Take \(T\to\infty\) first and then \(\rho\downarrow0\). This proves (15) uniformly. Product differentiation consequently gives
\[
\sup_{cT\le t\le CT}|f^{(r)}(t)|
=o_r(T(\log T)^{r+2}).
\tag{16}
\]
No separate subconvexity theorem is needed.

## 4. Complete finite-window errors and a paid linearization

### 4.1. Keep endpoint and bulk combined

**[COFINAL_FAMILY | PAPER]** The source constants
\(C_j=\sup_{u\ge0} e^{(\pi/2)e^{2u}}|g^{(j)}(u)|\), for \(0\le j\le4\), are finite. Fixed differentiation of every theta term yields a polynomial times its Gaussian; absorption into half the exponential and summation over \(\alpha\) prove this assertion. The same majorants justify the source interchanges used below, including absolute sums of source-pair inner products. All source sums are completed before squaring.

Let \(h=ug'+g/2\), \(k=u^2g''+ug'-g/4\). Exact differentiation on the fixed interval in the variable \(x=u/\lambda\) gives
\[
e_n'\!(\lambda)=\frac{2(-1)^n}{\lambda^{3/2}}
 \int_0^{\lambda/2}h(u)\cos(t_nu)du,
\quad
e_n''\!(\lambda)=\frac{2(-1)^n}{\lambda^{5/2}}
 \int_0^{\lambda/2}k(u)\cos(t_nu)du,
\quad t_n=2\pi n/\lambda.
\tag{17}
\]
In particular the first formula, integrated by parts, retains
\[
e_n'=-\frac{e_n}{2\lambda}
+\frac{g(\lambda/2)}{\sqrt\lambda}
+\frac{4\pi n(-1)^n}{\lambda^{5/2}}
 \int_0^{\lambda/2}u g(u)\sin(t_nu)du.
\tag{18}
\]
The endpoint in (18) is not zero. Separate infinite-tail norms of its endpoint and bulk are not used.

Define the full-line coefficient \(\widetilde e_n=(-1)^n\lambda^{-1/2}F(t_n)\) and \(\widetilde d_n=\widetilde e_n'\). Equations (9) and (17) give
\[
\widetilde e_n=(-1)^{n+1}\lambda^{-1/2}a(t_n)Z(t_n),
\qquad
\widetilde d_n=(-1)^n\lambda^{-3/2}a(t_n)t_nU(t_n),
\quad U=Z'+(p+1/(2t))Z.
\tag{19}
\]
For \(j=0,1,2\), the difference between the actual \(j\)-th derivative and its full-line counterpart is exactly the exterior cosine transform of \(g,h,k\), respectively, with prefactor \(2(-1)^n\lambda^{-j-1/2}\). Two integrations by parts in that exterior integral give
\[
\boxed{|e_n^{(j)}(\lambda)-\widetilde e_n^{(j)}(\lambda)|
\le C_j\lambda^{3/2}n^{-2}e^{-(\pi/2)e^\lambda},
\quad \lambda\ge1,\ n\ge1,\ j=0,1,2.}
\tag{20}
\]
The sine boundary vanishes at \(t_n\lambda/2=\pi n\); the derivative boundary is retained. For \(h\) and \(k\), the factors \((1+u)\) and \((1+u)^2\) are compensated by their respective powers of \(\lambda\). Thus (20) is uniform and square summable, including the infinite forward tail.

On the original paths, \(e^\lambda\ge m-1\) and \(w_m\le C e^{\pi^2m/L_m}\). Squaring (20) therefore leaves an exponential bounded by
\(C\exp[-\pi m+\pi^2m/L_m]\le C e^{-\pi m/2}\) eventually. All sums of these errors, with the polynomial factors in this proof, are exponentially small. The cross errors in products are paid by Cauchy–Schwarz and the coarse bounds in Sections 5–7. Similarly, the source bound proves
\[
\boxed{0<\sum w_m L_mO_m\le\sum w_mL_mE_O(m)
\le C M^C e^{-cM}.}
\tag{21}
\]
The full exterior remains in the actual energies; (21) estimates it rather than deleting it.

### 4.2. Linearize the increment only with its proved error

**[COFINAL_FAMILY | PAPER]** Let \(z_m(s)\) be the actual coupled velocity from the predecessor, with forward multiplier \(+\delta_+\) and backward multiplier \(-\delta_-\). Write
\[
v_m=z_m(0)+\eta_m,
\quad z_m(0)=\big((\sqrt2\delta_+e_n'(L))_{n>m+D},
(-\sqrt2\delta_-e_{m+2\ell-1}'(L))_{1\le\ell\le128}\big).
\tag{22}
\]
The predecessor's proof estimates not only variance, but the larger, explicitly displayed derivative integral:
\[
\boxed{\sum w_m4L_m^2\int_0^1\|z_m'(s)\|^2ds=O_D(M/\log M).}
\tag{23}
\]
Specifically, its equation (7) has right side exactly this integral, and its estimates (19)–(27) bound that right side. This is **not** inferred backwards from VAVG128 alone. Those estimates include both projected blocks and the second-window-derivative correction.

The fundamental theorem of calculus and Cauchy–Schwarz give
\(\|\eta_m\|^2\le\int_0^1\|z_m'\|^2\). Since \(\|u_m\|^2\le E_m\) and the accepted energy upper bound is \(\sum w_mS_m<4M\log M\), (23) yields
\[
\boxed{\sum w_m2L_m|\langle u_m,\eta_m\rangle|=O_D(M).}
\tag{24}
\]
Thus the covariance can be linearized at \(L\) at a paid lower-order cost. The original window shift and its endpoint have not been declared negligible merely because \(\delta_\pm\) are small.

## 5. The new discrete-to-continuous sampling proof

Set \(H=\log M\). For \(x\in[M,2M]\), \(1\le q\le H^2\), define
\[
\phi_q(x)=\frac{2\pi(x+q)}{\log x},
\qquad b_{q,s}(x)=(\log x)^{-s}e^{-\pi^2q/\log x}.
\tag{25}
\]
The two pairs needed are \((s,k)=(1,0)\) and \((2,1)\), acting on \(f^{(k)}\). Integer upper limits such as \(q\le H^2\) mean all integers satisfying the displayed inequality. This is only an analytic near/far partition of a fully retained spectral sum; it changes no source or receiver cutoff.

### 5.1. Coarse sampling, amplitude ratios, and the entire far tail

**[COFINAL_FAMILY | PAPER]** Uniformly for \(q\le H^2\), the spacing of \(\phi_q(m)\) is comparable to \(H^{-1}\). For every fixed \(j\), a local fundamental-theorem estimate on disjoint intervals of that length, followed by (8), proves
\[
\boxed{\sum_{M\le m<2M}|Z^{(j)}(\phi_q(m))|^2
\le C_j M H^{2j+1}.}
\tag{26}
\]
Indeed the sum is at most
\(C H\int |Z^{(j)}|^2+C\int|Z^{(j)}Z^{(j+1)}|\)
over a fixed comparable frequency band, including the first and last small intervals. This gives the claimed bound by the continuous moments. It is an inequality, not the sharp sampling assertion still to be proved.

Gamma asymptotics in (10) yield uniformly for the same range
\[
\boxed{w_ma(\phi_q(m))^2
=e^{-\pi^2q/L_m}(1+O(H^2/M)).}
\tag{27}
\]
For all \(q\ge1\), without a near-edge restriction, they also give
\[
w_ma(\phi_q(m))^2
\le C(1+q/m)^{15/2}e^{-\pi^2q/L_m}.
\tag{28}
\]
Using (14), the sums over **all** \(q>H^2\) that occur below in the energy, the scaled covariance, or the scaled squared linearized increment are bounded by
\[
\boxed{C_D M^2 H^{C_0}e^{-\pi^2H/4}=o(MH).}
\tag{29}
\]
Here is the uniform tail check. The additional factors are fixed powers of \(1+q/m\), \(\phi_q\), and \(\log(2+\phi_q)\). Write \(\phi_q\asymp (m/H)(1+q/m)\), and use \(\log(1+q/m)\le q/m\). For large \(M\), absorb all these fixed powers into the exponential in (28), leaving \(e^{-\pi^2q/(4H)}\), a polynomial in \(H\), and at most one remaining factor \(m\) from (14). Sum the geometric tail and then the \(M\) cells. Since \(\pi^2/4>2\), (29) follows. The same estimate holds for the corresponding real-\(x\) integrals. No part of the infinite forward tail is removed from the quantity being adjudicated.

### 5.2. Euler–Maclaurin with its actual remainder

**[ABSTRACT | PAPER — quadrature identity]** At every fixed even integer \(r\ge2\), Euler–Maclaurin for \(\sum_{M\le m<2M}F(m)\) has its integral, the endpoint corrections through order \(r-1\), and a remainder bounded by
\[
\frac{2\zeta(r)}{(2\pi)^r}\int_M^{2M}|F^{(r)}(x)|dx.
\tag{30}
\]
The constant follows from the Fourier series of the periodic Bernoulli polynomial. Both block endpoints are included. These identities are DLMF 2.10.1 and 24.8.1. citeturn400733view1turn400733view2

**[COFINAL_FAMILY | PAPER — new sampling lemma]** For either pair \((s,k)=(1,0),(2,1)\), and with either lower limit \(q=1\) or \(q=D+1\),
\[
\boxed{\sum_{q\le H^2}\left[
\sum_{M\le m<2M}b_{q,s}(m)f^{(k)}(\phi_q(m))
-\int_M^{2M}b_{q,s}(x)f^{(k)}(\phi_q(x))dx
\right]=o(MH).}
\tag{31}
\]
The displayed lower limit is understood in the sum. Removing a fixed initial set of offsets changes none of the estimates proving (31).

Here are the derivative, endpoint, and limit details. Uniformly for \(q\le H^2\),
\[
\begin{aligned}
\phi_q'&=(2\pi/H)(1+O(H^{-1})),\\
\phi_q^{(j)}&=O_j(M^{1-j}H^{-2})\quad(j\ge2),\\
|b_{q,s}^{(j)}|&\le C_{j,s}M^{-j}H^{-s}
 e^{-\pi^2q/(H+\log2)},\\
\sum_{q\le H^2}\sup_{[M,2M]}b_{q,s}
&\le(\pi^{-2}+o(1))H^{1-s}.
\end{aligned}
\tag{32}
\]
These are derivatives of the explicit elementary weights, not of the error in (27). All frequencies lie in a common interval \(I_M\) with
\(|I_M|=(2\pi+o(1))M/H\) and \(\log t=H+O(\log H)\).

For a fixed \(r\), the principal term in the \(r\)-th derivative of
\(b_{q,s}f^{(k)}(\phi_q)\) is exactly
\[
b_{q,s}(\phi_q')^r f^{(r+k)}(\phi_q).
\]
Every other term has a derivative of \(b\) or a higher derivative of \(\phi\). Equations (8), (12), and (32) show that the sum of their absolute integrals is
\(o_r(MH^{k+2-s})\): for fixed order each has at least one inverse power of \(M\), with only fixed logarithmic powers left. The constants in this lower-order error may depend on \(r\); that is harmless.

Changing to \(t=\phi_q(x)\) in the principal term and using the common interval in (12) gives the explicit remainder estimate
\[
\boxed{\limsup_{M\to\infty}
\frac{|\text{sum of Euler remainders}|}{MH^{k+2-s}}
\le\frac{2\zeta(r)}{\pi^2}\alpha_{r+k}.}
\tag{33}
\]
To check the constant without hiding order-dependent losses, multiply
\[
\frac{2\zeta(r)}{(2\pi)^r},\qquad
\frac{H^{1-s}}{\pi^2}(1+o_r(1)),\qquad
(2\pi/H)^{r-1}(1+o_r(1)),\qquad
(2\pi M/H)(1+o_r(1))H^{r+k+1}\alpha_{r+k}.
\]
No unspecified \(C_r\) multiplies \(\alpha_{r+k}\) in the limit. The chain-rule losses occur only in the already vanishing lower-order terms.

For each endpoint correction, (16) and (32) show that the sum over offsets is
\(o_r(MH^{k+2-s})\). For its principal derivative of order \(i\), the factors are
\(H^{1-s}H^{-i}\,o(T H^{i+k+2})\), with \(T=M/H\); this is precisely the claimed size. The differentiated-weight terms are smaller. This explicitly pays both \(M\) and \(2M\), including their shifted frequency endpoints.

For our two pairs, \(k+2-s=1\). Take the large-\(M\) limit **with \(r\) fixed**, and then let even \(r\to\infty\). Equations (13) and (33) prove (31). Equivalently, for a requested error \(\varepsilon\), choose one finite order first, then take \(M\) beyond its valid threshold. No derivative order grows with \(M\), no uniform-in-order remainder is assumed, and no continuous moment is silently declared to be a sampling law.

### 5.3. Evaluate the two continuous quantities

**[COFINAL_FAMILY | PAPER]** The zero-order moment in (8) says that the primitive of \(f\) is \(t\log t+O(t)\). Partial summation after \(t=\phi_q(x)\) gives
\[
\sum_{1\le q\le H^2}\int_M^{2M} b_{q,1}(x)f(\phi_q(x))dx
=(H+O(\log H))\int_M^{2M}\sum_{1\le q\le H^2}b_{q,1}(x)dx+O(M).
\]
For detail, the transformed weight is \(v_q=b_{q,1}/\phi_q'\). Its endpoint size plus total variation is bounded by a constant times
\(e^{-\pi^2q/(H+\log2)}\); their sum is \(O(H)\). The primitive remainder is \(O(M/H)\) on the common interval, proving the \(O(M)\) error. No derivative bound for that primitive remainder is used. The exact geometric sum gives
\[
\sum_{q\ge1}b_{q,1}(x)
=\frac{1}{\log x\,[e^{\pi^2/\log x}-1]}
=\frac1{\pi^2}+O(H^{-1}).
\]
Its part beyond \(H^2\) is negligible. Therefore, by (31),
\[
\boxed{\sum_{1\le q\le H^2}\sum_{M\le m<2M}
 b_{q,1}(m)Z(\phi_q(m))^2
=\left(\frac1{\pi^2}+o(1)\right)MH.}
\tag{34}
\]

For the signed derivative, use \(v_q=b_{q,2}/\phi_q'\) and integrate by parts exactly:
\[
\int_M^{2M}b_{q,2}(x)f'(\phi_q(x))dx
=[v_q f]_{\phi_q(M)}^{\phi_q(2M)}-\int v_q'(t)f(t)dt.
\]
Here \(\sum_q\sup|v_q|=O(1)\), and
\(\sum_q\sup|v_q'|=O(H/M)\). Formula (16) makes the total endpoint term \(o(MH)\). The integral term is \(O(H)\), since \(\int_{I_M} f=O(M)\). The bounds apply also when \(q\) starts at \(D+1\). With (31) this proves
\[
\boxed{\sum_{D<q\le H^2}\sum_{M\le m<2M}
 b_{q,2}(m)(Z^2)'(\phi_q(m))=o(MH).}
\tag{35}
\]
This is the signed sampling estimate needed for the covariance. It is stronger information than an unsigned first-derivative norm estimate.

## 6. The energy leading term, including the delayed window

**[COFINAL_FAMILY | PAPER]** Equations (19)–(21), (27), (29), and (34) give
\[
\boxed{\sum w_mE_m
=2\sum_{1\le q\le H^2}\sum_m b_{q,1}(m)Z(\phi_q(m))^2+o(MH)
=\left(\frac2{\pi^2}+o(1)\right)MH.}
\tag{36}
\]
The factor two is the original two-sign energy. To check the error from (27), (26) and the geometric weight sum bound the absolute near-range sums by \(O(MH)\); the uniform relative error \(O(H^2/M)\) is therefore negligible. The entire far spectral tail and the actual physical exterior are paid in (29) and (21). The full-window cross terms are paid using (20), not deleted.

For the delayed energy, the **common weight is still \(w_m\)**. With \(r=m-1\), (10) gives
\[
\frac{w_{r+1}}{w_r}=1+O(H^{-1})\qquad(M-1\le r<2M).
\tag{37}
\]
The same coarse bounds show that this produces only \(O(M)\) in the block energy sum. The proof of (34)–(36) applies unchanged to the integer interval \([M-1,2M-1)\): the derivative estimates and the endpoint proof (16), (32) are uniform under these bounded shifts. Alternatively, the two individual end energies are \(o(MH)\) by (15), (27), the geometric sum, and (29). Thus neither delayed endpoint is ignored, and
\[
\boxed{\sum w_mE_{m-1}=\left(\frac2{\pi^2}+o(1)\right)MH,
\qquad \sum w_mS_m=\left(\frac4{\pi^2}+o(1)\right)MH.}
\tag{38}
\]
In particular this is consistent with, and sharper than, the accepted upper bound \(4MH\). It does not assume that the two actual cell energies are pointwise equal.

## 7. Pay the actual covariance and the positive increment term

### 7.1. Signed covariance, with its backward orientation

**[COFINAL_FAMILY | PAPER]** Equations (22)–(24) give
\[
\sum w_m2L_m\langle u_m,v_m\rangle
=\sum_m w_m\left[
4L_m\delta_+\sum_{q>D}e_{m+q}(L_m)e_{m+q}'(L_m)
-4L_m\delta_-\sum_{\substack{1\le q<D\\q\text{ odd}}}
 e_{m+q}(L_m)e_{m+q}'(L_m)\right]+O_D(M).
\tag{39}
\]
The second minus sign is the backward orientation. It has not been changed by using a common expansion window; (24) is the paid error for that expansion.

From (19), at \(t=\phi_q(m)\),
\[
\widetilde e_{m+q}\widetilde d_{m+q}
=-L_m^{-2}a(t)^2t\,[Z(t)Z'(t)+c(t)Z(t)^2],
\quad c=p+1/(2t).
\tag{40}
\]
The minus sign follows from the opposite coefficient phases. The function \(c\) is bounded. All finite-window products in (39) can be replaced by (40) with exponentially small total error by (20) and the coarse bounds; the infinite tail is square summable before taking products.

For \(q\le H^2\),
\[
\frac{4\delta_+t}{L_m}w_ma(t)^2
=\frac{8\pi D}{L_m^2}e^{-\pi^2q/L_m}(1+O_D(H^2/M)).
\tag{41}
\]
The uniform error is harmless even in absolute covariance sums: by (26) and Cauchy–Schwarz, the near-range sum with this coefficient and \(|ZZ'|\) is \(O_D(MH)\). The far range has already been paid in (29).

The forward \(ZZ'\) term in (39) is consequently
\[
-4\pi D\sum_{D<q\le H^2}\sum_m b_{q,2}(m)(Z^2)'(\phi_q(m))+o(MH)=o(MH)
\]
by the **signed** result (35). The forward \(cZ^2\) term is \(O_D(M)\): use bounded \(c\), (26) at order zero, the coefficient \(O_D(H^{-2})\), and the \(O(H)\) sum of exponential weights.

In the backward block there are only 128 original offsets. Its coefficient is \(O_D(H^{-2})\), since \(\delta_-=m^{-1}(1+O(m^{-1}))\). Equations (26) and Cauchy–Schwarz therefore bound its entire signed \(ZZ'+cZ^2\) contribution in absolute value by \(O_D(M)\). This estimates the finite odd block separately, rather than using a forward-tail estimate for it.

Together with (24), these calculations prove
\[
\boxed{\sum w_m2L_m\langle u_m,v_m\rangle=o(MH).}
\tag{42}
\]
An unsigned Cauchy–Schwarz estimate for the forward \(ZZ'\) term alone would have given only \(O_D(MH)\), with no useful sign. The new quadrature step is what removes that obstruction.

### 7.2. The positive \(L_mW_m\) is lower-order too

**[COFINAL_FAMILY | PAPER]** For the forward part of \(z_m(0)\), (19) gives, after multiplying by \(w_m\),
\[
2\delta_+^2L_m^{-3}a(t)^2t^2U(t)^2w_m
\le C_DH^{-5} e^{-\pi^2q/(H+\log2)}
\big(Z'(t)^2+Z(t)^2\big)
\]
for \(q\le H^2\). The coarse sampled moments (26) imply
\[
\sum w_m\|z_m(0)\|^2\le C_D M/H.
\tag{43}
\]
The finite backward block obeys the same bound, and (20), (29) pay the corrections and far tail. The powers are important: \(\delta_+^2t^2=O_D(H^{-2})\), in addition to \(L_m^{-3}\).

By (23), \(\sum w_m\|\eta_m\|^2=O_D(M/H^3)\). Hence
\[
\boxed{0\le\sum w_mL_mW_m
\le2\sum w_mL_m(\|z_m(0)\|^2+\|\eta_m\|^2)
=O_D(M).}
\tag{44}
\]
This is an upper bound for the actual squared increment. It does not replace the covariance with action, and it does not assert that \(4L_m^2W_m\) is lower-order. Indeed the latter is at the scale relevant to the previous PIB128 refutation.

## 8. The signed block conclusion and its exact scope

**[COFINAL_FAMILY | PAPER — new quantified result]** Insert (21), (38), (42), and (44) into the exact identity (7), keeping the same original \(w_m\) on every term. This proves
\[
BT_M=\sum w_mT_m
=\left(\frac4{\pi^2}+o(1)\right)M\log M.
\tag{45}
\]
Take an integer \(M_*(P)\) beyond all analytic thresholds, with \(M_*(P)\ge J_P+3\) and \(\log M_*(P)\ge1536\), and sufficiently large that the absolute normalized error in (45) is less than \(2/\pi^2\). Then (2) holds for **every integer** \(M\ge M_*(P)\). All cells in every such block are already original admitted cells. No real interpolation parameter is treated as a new selected cell, and no numerical threshold is asserted.

This closes the requested eventual block sign. It does **not** infer signs for all individual \(T_m\) from their positive weighted sum. In particular it proves neither MT128 nor its negation and selects no MG128 disjunction arm. Negative \(\mathscr Q_m\) cells can coexist with (45), because their positive-square correction in the exact \(T_m\) identity remains present. The request explicitly distinguishes these outcomes. fileciteturn34file0L94-L106

## 9. Strongest attacks, route map, and closeout

**[ABSTRACT | PAPER — strongest attack: an unpaid sampling law]** The possible fatal error would be replacing a continuous Hardy moment by a discrete one at nearly critical spacing. Equation (31) is proved instead, with an explicit remainder coefficient (33). The decisive feature is \(\alpha_r\to0\), which follows from the exact continuous derivative-moment constants. Mere mesh density would not suffice: the elementary test \(F(x)=\cos(2\pi x)\) has constant samples at integer points but zero bulk integral; its corresponding normalized derivative remainders do not tend to zero. That diagnostic is not an actual source counterexample.

The order of limits is mandatory. Any implementation claiming a uniform Bui–Hall error with derivative order increasing with \(M\) would not be justified by this proof. Here each even \(r\) is fixed, its moment and endpoint errors disappear as \(M\to\infty\), and only then does (13) let the limiting quadrature bound vanish. The explicit leading coefficient in (33), not a hidden order-dependent constant, makes this legitimate.

**[COFINAL_FAMILY | PAPER — strongest attack: a changed source or receiver]** The full-line coefficient is used only with (20). Its exterior errors are square summable and exponentially small under the original weights. The source sum is never truncated. The analytic partition \(q\le H^2\) versus \(q>H^2\) retains the latter in (29); it is not a new mask, carrier, or panel. The correction in (24) is obtained from the predecessor's proved projected second-derivative bound, not from qualitative small displacement or from VAVG128 in the wrong direction. The delayed window and the common weight are separately paid in (37)–(38).

| Representation | Decisive power and cost | Status |
|---|---|---|
| **Actual covariance, full-source transform, critical-mesh quadrature. [COFINAL_FAMILY; PAPER]** | Gives the original signed block's leading term. Cost: fixed-order moment family, explicit Euler remainder, full tail and window budgets. | Completed here; independent audit required. |
| **Exact two-window energy shift (6), followed by reindexing the weighted energies. [COFINAL_FAMILY; CONDITIONAL]** | Could compute the same block but must pay cancellation between the shifted-energy and parity-block terms at their large common scale. Does not bypass sampling. | Retained as a check, not asserted as a second proof. |

**What became smaller.** The eventual sign of the original signed transport block is determined, with leading coefficient \(4/\pi^2\) and a strict lower envelope. The signed covariance is paid at its actual scale rather than replaced by a norm deficit.

**What was killed.** No new theorem shape is killed by this positive block result. The earlier universal/eventual PDA128 and PIB128 refutations are not reversed. Pointwise MT128 and the other downstream source signs remain separate.

**Prediction scoring.** The registered lower-order covariance test is confirmed by (42). The byte locks and the two increment orientations were checked. The leading coefficient is the outcome of (34), (36), and (38), not a numerical fit. No selected-cell prediction, computation, or independent review is being retrospectively claimed.

The three mathematical connections used are exact Fourier/dilation calculus with its boundary remainder, Hilbert path differentiation with a paid linearization error, and Euler–Maclaurin quadrature controlled by the full fixed-order moment family. The identity \((Z^2)'=2ZZ'\) removes the bulk of the signed continuous covariance only after sampling and both endpoint terms have been paid.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: original_BT_block_classification_only
ACTUAL_CONSUMER_REQUIREMENT: a_valid_eventual_block_sign_on_the_same_original_weights_and_cells
ORIGINAL_REQUESTED_OBJECT: signed_transport_block_at_M_log_M_scale
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: block_fact_proved_but_not_established_necessary_or_sufficient_for_pointwise_MT128_or_MG128
KNOWN_WEAKER_INTERFACES:
  - a_strict_positive_lower_envelope_would_suffice_without_the_full_asymptotic
  - a_direct_exact_two_window_block_estimate_could_replace_the_covariance_decomposition
FAILURE_TYPE: OTHER
FAILURE_TYPE_QUALIFICATION: no_failure_of_the_requested_block_sign_proof_is_claimed
EPISTEMIC_STATUS: UNRESOLVED
EPISTEMIC_STATUS_SCOPE: pointwise_MT128_MG128_and_other_downstream_receivers_only
REQUESTED_BLOCK_QUESTION: CLOSED_PAPER_PENDING_INDEPENDENT_AUDIT
NEW_KILL_SCOPE: NONE
NEW_EXTERNAL_USE: all_fixed_orders_of_the_unconditional_Bui_Hall_equal_derivative_second_moment
NEW_EXTERNAL_INPUT_HYPOTHESIS_RH: false
NEW_DISCRIMINATOR: BT_M_over_M_log_M_minus_2_over_pi_squared
DISCRIMINATOR_RESULT: strictly_positive_eventually
REOPEN_TRIGGER_FOR_NEW_BLOCK_RESULT: error_in_fixed_order_moment_constants_Euler_remainder_endpoints_tail_or_covariance_linearization
RESEARCH_DEBT: actual_pointwise_T_m_sign_and_separate_MG128_PC_SV_consumers
RESEARCH_DEBT_REOPEN_TRIGGER: an_independent_estimate_for_those_original_receivers_not_a_positive_block_average
NOVELTY_AXIS: moment_constant_decay_pays_critical_mesh_signed_covariance_without_assuming_a_discrete_Hardy_law
MEMORY_ENTRY:
  target: source_core_fixed_128_signed_transport_block
  status: PROVED_EVENTUAL_POSITIVE_BLOCK_ONLY
  cognitive_operator_used: REPRESENTATION_SHIFT
  failed_strategy: infer_signed_transport_from_a_negative_quadratic_norm_certificate
  invariant_learned: the_norm_deficit_scale_and_the_signed_covariance_scale_are_different
  forbidden_future_move: infer_universal_MT128_or_a_MG128_disjunction_arm_from_positive_BT
  next_decisive_test: independent_PAPER_audit_of_equations_11_through_45
```

**[COFINAL_FAMILY | PAPER — preservation and verification boundary]** The original source, both Fourier signs, infinite forward tail, finite odd backward block, physical exterior, three actual windows, carrier, \(Q=\sqrt m\), \(5m\) splice, \(N,K\), and panel remain unchanged. The low epsilon block, literal diagonal, zero node, final descent, paired logarithmic kernel, signed beta correction, exponent-one prime block, prime/square compensation, opposite-side correlation, transfer, and Schur-floor are untouched. No conditional square constant is activated. There was no coefficient or grid search, mathematical runtime, Lean execution, repository write, route promotion, or RH claim. Local execution was file I/O, text validation, and hashing only. The new proof has not received independent review. fileciteturn34file0L108-L121

## CODEX DIRECTIVE

**Perform one read-only independent PAPER audit of this signed-block asymptotic against the unchanged request hash and source pin.** Check the unconditional fixed-order moment family (8), its exact constants in (11)–(13), the endpoint deduction (15)–(16), and especially the new Euler–Maclaurin sampling proof (30)–(35): its principal remainder must have the order-independent limiting factor shown in (33), both endpoint corrections must be paid, and the order of limits must remain fixed \(r\), then \(M\to\infty\), then even \(r\to\infty\). Verify the complete finite-window correction (20), the retained far tail (29), the use of the predecessor's actual projected derivative bound in (23) rather than a converse of VAVG128, the forward product sign and backward minus orientation in (39)–(41), and the delayed energy with the same weight in (37)–(38). Accept only `SOURCE_SIGNED_TRANSPORT_BLOCK_NONNEGATIVE`, strengthened to (45) and the strict eventual lower envelope (2), if these checks pass. If any step fails, report the first invalid estimate and withhold this new block conclusion without altering the predecessor's accepted results. Do not infer any universal individual-cell sign, MT128, an MG128 disjunction arm, C128, PC, SV, lag, Schur-floor, or RH. No numerical search, mathematical runtime, source deletion, new mask/panel, Lean, repository write, conditional-constant activation, or route promotion is authorized.
