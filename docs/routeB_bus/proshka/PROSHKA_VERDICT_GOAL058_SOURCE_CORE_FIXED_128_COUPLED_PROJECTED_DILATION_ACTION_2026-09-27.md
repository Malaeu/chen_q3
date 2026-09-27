# STATUS: KILL_GOAL058_SOURCE_CORE_FIXED_128_COUPLED_PROJECTED_DILATION_ACTION

```yaml
OPERATIVE_CLASS: KILL_GOAL058_SOURCE_CORE_FIXED_128_COUPLED_PROJECTED_DILATION_ACTION
OUTCOME: SOURCE_COUPLED_ACTION_BUDGET_REFUTED
REQUEST_ID: REQ-2026-09-27-SOURCE-CORE-FIXED-128-COUPLED-PROJECTED-DILATION-ACTION
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_FIXED_128_COUPLED_PROJECTED_DILATION_ACTION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 5d466f50b4bdbe28606cce402268df972fad6547
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
HONESTY_STATE: CHALLENGER_NOT_RH
REQUEST_SHA256_LOCALLY_VERIFIED: c1a3503e063d4119d7786fac4b2531aa7b261284ead8d5aecb10fe4d1ccb4b36
REQUEST_BYTES: 6122
REQUEST_LF: 115
REQUEST_CR: 0
REQUEST_UTF8_VALID: true
REQUEST_UTF8_BOM: false
REQUEST_FINAL_LF: true
REQUEST_GIT_BLOB_LOCALLY_COMPUTED: 01a1a71f2ab4acd397a09a3fb203c468d7fb31f2
PREDECESSOR: REQ-2026-09-27-SOURCE-CORE-FIXED-128-PROJECTED-MESH-INCREMENT-BUDGET
PREDECESSOR_SHA256_LOCALLY_VERIFIED: b43493e3bfe6ce83a440dde89e732f09882d7940feb4c831b9c4d812d6010b4b
PREDECESSOR_BYTES: 33970
PREDECESSOR_LF: 543
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: ee2a548b7559c3bdb5a04609258b617a9342d19e
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_GIT_BLOB_READ: 4be1cbcffc9d622365d7b98871740d0e4ee9d49e
AUDIT_SECTION: source_core_fixed_128_projected_mesh_increment_budget_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
KILL_SCOPE: THEOREM_SHAPE
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILLED_THEOREM_SHAPE: PDA128_ON_ALL_STATED_CELLS_OR_ON_ANY_EVENTUAL_SELECTED_TAIL
KILL_EVIDENCE_KIND: COMPLETE_SOURCE_WEIGHTED_BLOCK_STRICT_NEGATIVE_MARGIN
KILL_EVIDENCE_REFERENCE: sections_4_through_8_equations_12_through_35_in_this_verdict
WITNESS_QUANTIFIER: EVERY_SUFFICIENTLY_LARGE_INTEGER_M_HAS_AN_ADMITTED_m_IN_M_LE_m_LT_2M_WITH_Rscr_m_LT_MINUS_2_S_m
WITNESS_SEQUENCE: SECTION_8_EQUATION_35
EXPLICIT_FIRST_WITNESS_EVALUATED: false
EXPLICIT_ASYMPTOTIC_THRESHOLD_COMPUTED: false
NEW_EXTERNAL_THEOREM_IMPORT: UNCONDITIONAL_HARDY_Z_SECOND_MOMENTS_FOR_DERIVATIVE_ORDERS_0_AND_1
IMPORT_REFERENCE: Bui_Hall_2023_BLMS_equation_1_DOI_10.1112_blms.12859
IMPORT_USES_RH: false
NEW_PROOF_INDEPENDENTLY_AUDITED: false
PIB128: OPEN
MT128: OPEN
MG128: OPEN
C128: OPEN
PC: OPEN
COFINAL_DISJUNCTION_ARM_SELECTED: NONE
PROGRESS_CLASS: FALSIFICATION_PROGRESS
PROGRESS_QUALIFICATION: ACTUAL_PDA128_THEOREM_SHAPE_NOT_JUST_AN_APPROXIMATION_METHOD
COGNITIVE_OPERATOR_USED: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 4
NEXT_TASK: PAPER_AUDIT_COFINAL_PDA128_REFUTATION_AND_PRESERVE_EXACT_INCREMENT_RECEIVER
MATHEMATICAL_RUNTIME_EXECUTED: false
COEFFICIENT_NUMERICS_EXECUTED: false
SELECTED_CELL_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_RUNTIME_USE: FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY
REPOSITORY_WRITTEN: false
SOURCE_INDEX_TRUNCATED: false
SOURCE_FAMILY_CHANGED: false
ORIGINAL_ENERGY_OR_DENOMINATOR_CHANGED: false
ORIGINAL_CARRIER_Q_N_K_PANEL_CHANGED: false
WINDOW_REMAINDER_DROPPED: false
CONDITIONAL_SQUARE_CONSTANTS_ACTIVATED: false
SV: OPEN
LAG: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **SOURCE_COUPLED_ACTION_BUDGET_REFUTED.** The complete source violates PDA128 on an unbounded sequence of the original admitted cells. More precisely, for the same fixed \(P\),
\[
\boxed{\exists M_*(P)\ \forall M\in\mathbb N,\ M\ge M_*(P):\quad
\exists m\in\mathbb Z\cap[M,2M),\quad
m=J_P+j+2,\ j\ge1,\ \log m\ge1536,\quad
\mathscr R_m<-2S_m<0.}
\tag{1}
\]
This is an existence proof with a strict original-source margin, not an evaluated cell, a coefficient model, or a failed upper estimate. No numerical value for the first witness or the eventual threshold is claimed.

The proof changes direction: it uses **averaged oscillation of the complete source**, rather than imposing another stronger norm estimate. One new, publicly verified, unconditional input is the second-moment theorem for Hardy's function and its first derivative. The source-to-Hardy crosswalk, finite-window error accounting, upper sampling estimate, and lower moving-window coverage argument are supplied below. These new arguments are not covered by the predecessor's independent reviews.

**Only PDA128 is refuted.** The exact receiver remains
\[
\mathscr Q_m=\mathscr R_m+4L_m^2\mathscr V_m^{\rm path},\qquad
\mathscr V_m^{\rm path}>0.
\tag{2}
\]
The positive correction has not been bounded above at the witnesses. Consequently neither \(\mathscr Q_m<0\) nor \(T_m<0\) follows. No MG128 disjunction arm is selected.

## 1. Source lock and evidence boundary

**[FINITE_CELL | PAPER — provenance]** The authoritative TXT was read completely. Its locally recomputed SHA-256 is the stipulated `c1a3503e063d4119d7786fac4b2531aa7b261284ead8d5aecb10fe4d1ccb4b36`: 6,122 bytes, 115 LF, valid UTF-8, no CR or BOM, and a final LF. Its ID, boundary and pin are the present coupled-action request. fileciteturn24file0L1-L15

The complete mounted predecessor was read through its final directive. Its 33,970 bytes and SHA-256 match the request. Its locally computed Git blob `ee2a548b7559c3bdb5a04609258b617a9342d19e` matches the GitHub connector at the current pin. The complete local text, not the connector's opening excerpt, supplied the argument. fileciteturn26file0L4-L5

The bootstrap was fetched from `rh_clean` and read through its response-format section. The specifically requested audit in `docs/Codex/PAPER_CHAIN.md` was read at the pin. It accepts endpoint cancellation, the action/variance identity and qualitative strict variance; it expressly does not supply an action-budget sign. Its two reviews do not cover this verdict's new Mellin and weighted-block proof. fileciteturn27file0L2-L2

**[ABSTRACT | PAPER — test registration]** Before the new sign argument, the announced test was a refutation-oriented averaged-source-oscillation route, with the moving-window coverage identified as its critical check. No individual source cell, numerical threshold, or final constant was predicted in advance. The closeout scores this route and the byte checks, not a retrospectively invented cell forecast.

## 2. Preserve the source, projections, endpoints and variance

**[COFINAL_FAMILY | PAPER — admitted contract and checks]** Set \(D=256\), only as an abbreviation for the original shift. For the fixed \(P\), use
\[
m=J_P+j+2,\quad j\ge1,\quad L_m=\log m\ge1536,
\quad L_- =\log(m-1),\quad L_+=\log(m+D).
\]
The current carrier, \(Q=\sqrt m\), \(5m\) splice, \(N=\lceil L_m\rceil\), \(K=N+\lceil L_m^4\rceil\), and panel are unchanged. The neighbouring cells have original indices \(j-1\) and \(j+D\); the first can be zero as an energy input. Real parameters between their windows are not new selected cells. fileciteturn24file0L29-L35

Keep the exact complete \(g,h,e_n,d_n,E_s,E_O(s),S_m,O_m\) of the TXT. Complete-source theta symmetry makes \(g\) even and real analytic. Each fixed derivative has polynomial-Gaussian local majorants in the theta index and superexponential decay on the positive real half-line. These facts also follow from the theta identity used in Section 3; no individual theta summand is asserted to be even.

On \(I=[-1/2,1/2]\), put \(f_\lambda(x)=\sqrt\lambda\,g(\lambda x)\). In the orthonormal basis \((-1)^n e^{2\pi i n x}\), its coefficients are the real even \(e_n(\lambda)\). Thus Parseval retains
\[
\|f_\lambda\|_2^2=e_0(\lambda)^2+2\sum_{n\ge1}e_n(\lambda)^2,
\qquad
\partial_\lambda f_\lambda(x)=\lambda^{-1/2}h(\lambda x).
\]
In particular,
\[
d_n(\lambda)=\frac{2(-1)^n}{\lambda^{3/2}}
 \int_0^{\lambda/2}h(u)\cos(2\pi nu/\lambda)\,du,
\quad h=ug'+\tfrac12g.
\tag{3}
\]
Integrating \(ug'\) by parts returns the full Leibniz formula
\[
d_n=-\frac{e_n}{2\lambda}+\frac{g(\lambda/2)}{\sqrt\lambda}
 +\frac{4\pi n(-1)^n}{\lambda^{5/2}}
       \int_0^{\lambda/2}u g(u)\sin(2\pi nu/\lambda)\,du.
\tag{4}
\]
The endpoint in (4) is not zero. We use the combined formula (3), never separate infinite-tail norms of the endpoint and bulk. Two integrations by parts in (3), with \(h'(0)=0\), give \(d_n=O_m(n^{-2})\), uniformly on the cell's compact parameter interval. This verifies the required Hilbert-space finiteness.

With \(\delta_+=L_+-L_m\) and \(\delta_-=L_m-L_-\), the original velocity has forward factor \(+\sqrt2\delta_+\) and backward factor \(-\sqrt2\delta_-\). Its integral is the original increment. The action is exactly
\[
\begin{aligned}
\mathscr A_m&=\mathscr A_m^++\mathscr A_m^-,\\
\mathscr A_m^+&=2\delta_+\int_{L_m}^{L_+}
                         \sum_{n>m+D}d_n(\lambda)^2\,d\lambda,\\
\mathscr A_m^-&=2\delta_-\int_{L_-}^{L_m}
                         \sum_{\ell=1}^{128}d_{m+2\ell-1}(\lambda)^2\,d\lambda.
\end{aligned}
\tag{5}
\]
Inserting (3) gives exactly the two factors \(8\delta_\pm\lambda^{-3}\) in the request. Squaring removes the backward orientation from the action, not from the integrated vector. The two sets of offsets, \(1,3,\ldots,255\) and \(2,4,\ldots,256\), still partition precisely 256 indices. In particular \(B_{m-1}\) is evaluated at \(L_-\), not at \(L_m\). fileciteturn24file0L51-L76

For every fixed cell, the sum of the \(L^2([0,1];\mathcal H_m)\) norms of its complete theta-index velocity contributions is finite, by cosine Parseval and the Gaussian majorant. Consequently the sum over pairs of source indices of the absolute integrated inner products is finite. This justifies source interchange and retains all source cross terms in (5); it does not give an energy-scale estimate.

For \(x\ge8\),
\(\mathcal P(x)=-64x^3(x-7)-30x(22x-5)<0\).
Thus the complete source is negative throughout the physical exterior in this domain, and
\[
O_m=2\int_{L_m/2}^{L_+/2}|g(u)|^2\,du>0,
\qquad E_O(s)>0.
\tag{6}
\]
The backward action and this exterior cost are retained. In a **lower bound for the cost**, they can only strengthen refutation; we will not need to estimate them above.

The identity \(\mathscr A_m=W_m+\mathscr V_m^{\rm path}\) follows by expanding the square about \(\int_0^1\mathbf z_m\). Its strictness is independently checked as follows. Zero variance would make the continuous forward velocity constant, so all coefficients beyond \(m+D\) of
\[
\partial_\lambda^2f_\lambda(x)=\lambda^{-3/2}k(\lambda x),
\qquad k(u)=u^2g''(u)+ug'(u)-g(u)/4
\]
would vanish at an interior parameter. Evenness then makes the restriction a finite trigonometric polynomial. Real analyticity continues that equality to the whole real line. Decay forces the periodic polynomial to vanish. The Euler equation \(k=0\) has only \(c_1u^{1/2}+c_2u^{-1/2}\) on \(u>0\); superexponential decay forces \(g=0\), contradicting (6). Therefore the variance in (2) is strictly positive. This is qualitative nonvanishing, not an estimate that could offset the negative action margins below.

## 3. Exact complete-source Mellin crosswalk and explicit external inputs

### 3.1. The full source, not a truncated theta model

**[COFINAL_FAMILY | PAPER — new derivation]** Define, for this calculation only,
\[
p(u)=e^{u/2}\sum_{\alpha\ge1}e^{-\pi\alpha^2e^{2u}},
\qquad \partial=\frac{d}{du}.
\]
Direct differentiation of each term gives
\(g=(\partial^2-4\partial^4)p\), with exactly the polynomial in the TXT. The theta transformation gives \(p(-u)=p(u)+\sinh(u/2)\); the displayed differential operator annihilates the added term, which verifies evenness and the negative-side decay of \(g\).

For \(\operatorname{Re}z>1/2\), an absolutely convergent Mellin integral, with \(s=1/2+z\), gives
\[
\int_{\mathbb R}p(u)e^{zu}\,du
=\tfrac12\pi^{-s/2}\Gamma(s/2)\zeta(s).
\]
All integrations by parts are justified in that half-plane. Since
\((z^2-4z^4)=-4z^2s(s-1)\), continuation of the entire transform of \(g\) yields
\[
\boxed{F(t):=\int_{\mathbb R}g(u)e^{itu}\,du
=4t^2\xi(1/2+it).}
\tag{7}
\]
The convention here is \(\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\), as in DLMF 25.4.4. This fixes the factor four and the frequency coordinate; in particular there is no substitution \(t\mapsto t/2\). citeturn629541view3

Let \(Z(t)=e^{i\theta(t)}\zeta(1/2+it)\) be real Hardy \(Z\), with \(\theta(t)=\arg\Gamma(1/4+it/2)-(t/2)\log\pi\). For \(t>0\), define the **positive gamma amplitude**
\[
a(t)=2t^2(t^2+1/4)\pi^{-1/4}|\Gamma(1/4+it/2)|>0.
\]
Equation (7) becomes \(F(t)=-a(t)Z(t)\). The full transform of the complete generator is therefore
\[
\boxed{\widehat h(t)=-\tfrac12F(t)-tF'(t)
=a(t)t\,U(t),\qquad
U(t)=Z'(t)+c(t)Z(t),\quad
c(t)=a'(t)/a(t)+1/(2t).}
\tag{8}
\]
These are exact full-source identities. No theta index is deleted, and squaring them retains the interference of the complete source.

### 3.2. New theorem import, independently identifiable and unconditional

**[ABSTRACT | PAPER — external THEOREM input]** Bui–Hall, *On the derivatives of Hardy's function Z(t)*, BLMS 55 (2023), 2304–2323, equation (1), DOI `10.1112/blms.12859`, gives, at derivative pairs \((0,0)\) and \((1,1)\),
\[
\int_0^T Z(t)^2dt=T\log T+O(T),\qquad
\int_0^T Z'(t)^2dt=\frac{T\log^3T}{12}+O(T\log^2T).
\tag{9}
\]
Their displayed polynomial formula and smaller error imply these versions. These statements are unconditional; no zero hypothesis or discrete-sampling theorem is imported. This input is new to this verdict, not attributed to the pinned project audit. citeturn616673view0

**[ABSTRACT | PAPER — external THEOREM input]** The gamma and logarithmic-derivative expansions in DLMF 5.11.1–2 and 5.11.9 imply
\[
a(t)=a_0t^{15/4}e^{-\pi t/4}(1+O(t^{-1})),\quad a_0>0,
\qquad a'(t)/a(t)=-\pi/4+O(t^{-1}).
\tag{10}
\]
The derivative assertion uses the logarithmic-derivative expansion, not differentiation of an unspecified asymptotic remainder. In particular \(c(t)\) in (8) is bounded eventually. citeturn629541view1turn629541view2

**[ABSTRACT | PAPER — consequence used below]** Put \(H=\log M\) and \(\tau(x)=2\pi x/\log x\). For intervals whose endpoints are \(\tau(M)+O(H)\) and \(\tau(2M)+O(H)\), uniformly under those shifts, subtraction in (9) gives
\[
\int Z^2=(2\pi+o(1))M,
\qquad
\int Z'^2=(\pi/6+o(1))MH^2,
\qquad
\int U^2=(\pi/6+o(1))MH^2.
\tag{11}
\]
Indeed the interval length is \((2\pi+o(1))M/H\) and \(\log t/H\to1\). For the last equality, boundedness of \(c\) and Cauchy–Schwarz bound the cross term by \(O(MH)\), and the \(c^2Z^2\) term by \(O(M)\). No cancellation of that cross term is assumed.

The positive weights used in the proof are
\[
\boxed{w_m=a(\tau(m))^{-2}.}
\tag{12}
\]
They depend on the explicit gamma amplitude, not on an unknown target ratio. Multiplying the original inequalities by these weights and adding over original cells does not change their denominators, source family or truth conditions. In particular \(S_m\) remains the original \(E_m+E_{m-1}\).

## 4. Pay the complete finite-window remainder before using (7)

**[COFINAL_FAMILY | PAPER — new error accounting]** With \(t_n(\lambda)=2\pi n/\lambda\), define the full-transform expressions
\[
e_n^\infty(\lambda)=(-1)^n\lambda^{-1/2}F(t_n(\lambda)),
\quad
d_n^\infty(\lambda)=(-1)^n\lambda^{-3/2}a(t_n(\lambda))t_n(\lambda)U(t_n(\lambda)).
\]
They are not substituted without their errors. Exactly,
\[
\begin{aligned}
e_n(\lambda)&=e_n^\infty(\lambda)-q_{g,n}(\lambda),&
q_{g,n}&=\frac{2(-1)^n}{\sqrt\lambda}\int_{\lambda/2}^\infty g(u)\cos(t_nu)\,du,\\
d_n(\lambda)&=d_n^\infty(\lambda)-q_{h,n}(\lambda),&
q_{h,n}&=\frac{2(-1)^n}{\lambda^{3/2}}\int_{\lambda/2}^\infty h(u)\cos(t_nu)\,du.
\end{aligned}
\tag{13}
\]
Both errors are combined exterior cosine transforms, not the non-square-summable Leibniz pieces.

For \(r=0,1,2,3\), the complete-source constants
\(\sup_{u\ge0}e^{(\pi/2)e^{2u}}|g^{(r)}(u)|\)
are finite. This follows directly by absorbing fixed polynomial factors into half of each Gaussian and summing the remaining Gaussian in \(\alpha\). The derivatives \(h',h''\) satisfy the same bounds with an additional factor \(1+u\).

At \(b=\lambda/2\), \(\sin(t_nb)=0\). Two integrations by parts on \([b,\infty)\), including the \(p'(b)\cos(t_nb)\) term for \(p=g,h\), yield a source-defined constant \(C\) such that, for \(\lambda\ge1\), \(n\ge1\),
\[
|q_{g,n}(\lambda)|+|q_{h,n}(\lambda)|
\le C\lambda^{3/2}n^{-2}e^{-(\pi/2)e^\lambda},
\qquad E_O(s)\le C e^{-\pi s}.
\tag{14}
\]
For example, the integral of a derivative majorized by \((1+u)e^{-(\pi/2)e^{2u}}\) is bounded after \(u=b+v\) using \(e^{2v}\ge1+2v\). Thus its bound is a constant times \((1+b)e^{-(\pi/2)e^{2b}}/e^{2b}\). This proves (14) without a source cutoff.

On \(M\le m<2M\), the relevant parameters have \(e^\lambda\ge m-1\) and \(\lambda\asymp H\). Summing \(n^{-4}\) over the prescribed tails and using (10) shows that all weighted squared errors needed for the two energies and the forward action are bounded by
\[
M^{C_1}\exp(-c_1M)=o(MH),\qquad C_1,c_1>0.
\tag{15}
\]
For clarity, the exponential in an individual weighted error is at most a polynomial times
\(\exp[-\pi(m-1)+\pi^2m/\log m]\); it decays exponentially in \(m\). The factors \(L_m^2\), the path lengths, and the sum over \(M\) cells are absorbed by the displayed polynomial. The shifted \(m-1\) energy obeys the same estimate. Physical \(E_O\) is included in (15), not declared zero.

To transfer upper bounds to the actual energies use
\(|x-y|^2\le(1+H^{-1})|x|^2+(1+H)|y|^2\).
For a lower bound on actual forward action use
\(|x-y|^2\ge(1-H^{-1})|x|^2-H|y|^2\).
Both are applied in the existing weighted Hilbert spaces. Equation (15) pays the error terms. No lower bound for an actual projection is inferred from an unprojected norm.

## 5. An upper bound for the sum of the original energies

**[COFINAL_FAMILY | PAPER — new weighted upper envelope]** For integer \(M\to\infty\), write \(H=\log M\) and sum over integers \(M\le m<2M\). We prove
\[
\boxed{\limsup_{M\to\infty}
\frac{\sum_{M\le m<2M}w_mS_m}{MH}
\le C_S:=\frac4{\pi^2}\left(1+\frac{2\pi}{\sqrt3}\right)<4.}
\tag{16}
\]
This is an upper bound for an explicitly weighted sum of the **actual** original energies, not an upper bound for an alternative denominator.

For the full-transform part of \(E_m\), set
\[
t_{m,k}=\frac{2\pi(m+k)}{\log m},\qquad k\ge1.
\]
Its weighted value is exactly
\[
\frac2{L_m}\sum_{k\ge1}
 \frac{a(t_{m,k})^2}{a(\tau(m))^2}Z(t_{m,k})^2.
\tag{17}
\]
For \(1\le k\le H^2\), (10) gives, uniformly in \(m,k\),
\[
\frac{a(t_{m,k})^2}{a(\tau(m))^2}
=(1+o(1))e^{-\pi^2k/L_m}
\le(1+o(1))e^{-\pi^2k/(H+\log2)}.
\tag{18}
\]
The polynomial ratio tends to one uniformly, since \(k/m\le H^2/M\to0\).

Here is the required **upper sampling inequality**, rather than an assumed discrete mean-square law. For each such fixed \(k\), successive points \(t_{m,k}\) have spacing
\[
t_{m+1,k}-t_{m,k}=\frac{2\pi}{H}(1+o(1))
\tag{19}
\]
uniformly on the block. This follows by differentiating \(2\pi(x+k)/\log x\). Make disjoint midpoint intervals around these points, using the adjacent points outside the block to close the two end intervals. Their lengths are \((2\pi/H)(1+o(1))\). For a real \(C^1\) function \(v\), a point \(x\) in an interval \(I\) satisfies
\[
v(x)^2\le |I|^{-1}\int_Iv^2+\int_I|(v^2)'|.
\]
Apply this to \(Z\), sum the intervals, and use Cauchy–Schwarz. Their total range has endpoints \(\tau(M)+O(H)\), \(\tau(2M)+O(H)\), uniformly for \(k\le H^2\). Equations (9)–(11) then give
\[
\begin{aligned}
\sum_{M\le m<2M}Z(t_{m,k})^2
&\le \frac{H}{2\pi}(1+o(1))\int Z^2
       +2\left(\int Z^2\int Z'^2\right)^{1/2}\\
&\le\left(1+\frac{2\pi}{\sqrt3}+o(1)\right)MH.
\end{aligned}
\tag{20}
\]
No assertion of equidistribution, independence of samples, or asymptotic equality for this discrete sum is used.

The range \(k>H^2\) in (17) is also paid. An elementary full-zeta bound is \(|Z(t)|\le C(1+t)\): for \(\operatorname{Re}s>0\), continuation of
\[
\zeta(s)=\frac{s}{s-1}-s\int_1^\infty\{x\}x^{-s-1}\,dx
\]
gives this on \(s=1/2+it\). Stirling gives, for all \(k\ge1\) and sufficiently large \(M\),
\[
\frac{a(t_{m,k})^2}{a(\tau(m))^2}
\le C(1+k/m)^8e^{-\pi^2k/L_m}.
\]
Split the exponential into equal halves. One half on \(k>H^2\) is at most
\(e^{-\pi^2H^2/[2(H+\log2)]}\).
The remaining polynomial-geometric sum is bounded by \(CM^2H\), because \(H/M\to0\). Including \(2/L_m\), this gives a per-cell bound
\(O(M^{2-\pi^2/2+o(1)})\), hence a total \(o(MH)\). This is a bound for the full omitted range of the infinite sum, not a spectral truncation. The analytic split at \(H^2\) changes neither the original \(K\) nor any panel or projection.

Finally,
\[
\sum_{k\ge1}e^{-\pi^2k/(H+\log2)}=(1+o(1))H/\pi^2.
\]
Combining (17)–(20), the infinite-range bound, and the actual-window error (15), proves
\[
\limsup\frac{\sum_{M\le m<2M}w_mE_m}{MH}
\le\frac2{\pi^2}\left(1+\frac{2\pi}{\sqrt3}\right).
\tag{21}
\]
The same estimate holds on the block shifted by one integer. Moreover
\(w_m/w_{m-1}=1+O(H^{-1})\) uniformly, by (10) and
\(\tau(m)-\tau(m-1)=O(H^{-1})\). This proves (16) for \(S_m=E_m+E_{m-1}\), retaining the delayed energy at the lower edge. Its constant is strictly below four: \(\pi>3\), \(\pi<22/7\), and \(\sqrt3>1\) give
\(C_S<(4/9)\,8=32/9<4\).

## 6. A lower bound from the actual forward projected action

### 6.1. Reorder the original parameter paths, not the selected family

**[COFINAL_FAMILY | PAPER — new weighted lower envelope]** We prove
\[
\boxed{\liminf_{M\to\infty}
\frac{\sum_{M\le m<2M}w_m4L_m^2\mathscr A_m^+}{MH}
\ge C_A:=\frac83\pi^2D^2e^{-\pi^2}>24.}
\tag{22}
\]
Only the forward component is needed for this lower bound. The actual total cost remains larger because \(\mathscr A_m^-\ge0\) and \(O_m>0\).

First use \(d_n^\infty\) from (13); Section 4 will transfer the lower bound back. The weighted sum of its forward action is exactly
\[
P_M^\infty=\sum_{M\le m<2M}8w_mL_m^2\delta_+
\int_{\log m}^{\log(m+D)}\lambda^{-3}
 \sum_{n>m+D}a(2\pi n/\lambda)^2(2\pi n/\lambda)^2
 U(2\pi n/\lambda)^2\,d\lambda.
\tag{23}
\]
All terms here are nonnegative. Put \(r=e^\lambda\) and use Tonelli. For almost every real \(r\in[M+D,2M-D]\), exactly \(D\) integers satisfy
\(r-D\le m\le r\), and all belong to the summed block. They are the original cells whose forward parameter intervals contain \(\log r\).

Among the existing tail terms, consider those satisfying
\[
D<n-r<D+\log r.
\tag{24}
\]
Every such \(n\) satisfies \(n>m+D\) for each of those \(D\) cells. We are taking a lower bound using terms already in the original nonnegative tail, not replacing the tail or introducing a trial mask. All other tail terms remain nonnegative contributions to the actual action.

Uniformly on (24), with \(\lambda=\log r\),
\[
\begin{gathered}
\delta_+=(D/r)(1+o(1)),\qquad L_m/\lambda=1+o(1),
\qquad n/r=1+o(1),\\
0\le 2\pi n/\lambda-\tau(m)\le2\pi+o(1),\qquad
\frac{a(2\pi n/\lambda)^2}{a(\tau(m))^2}
\ge(1-o(1))e^{-\pi^2}.
\end{gathered}
\tag{25}
\]
For the frequency bound, use \(r-m\le D\) and \(n-r<D+\log r\); the errors from these fixed \(D\) shifts vanish as \(H\to\infty\). The amplitude inequality follows from (10), not from an assumption about \(Z\).

After the \(D\)-fold path overlap, the coefficient in (23), including \(d\lambda=dr/r\), is
\[
\frac{8D^2}{r^2\lambda}(1+o(1))\cdot
\frac{4\pi^2r^2}{\lambda^2}
=\frac{32\pi^2D^2}{H^3}(1+o(1)).
\]
Consequently
\[
P_M^\infty\ge
\frac{32\pi^2D^2e^{-\pi^2}}{H^3}(1-o(1))\,\mathcal J_M,
\quad
\mathcal J_M=\int_{M+D}^{2M-D}
 \sum_{D<n-r<D+\log r}U(2\pi n/\log r)^2\,dr.
\tag{26}
\]
This is where the original shift \(D=256\) supplies \(D^2\): one factor from the path length and one from the number of original paths covering the parameter. Neither factor comes from choosing a new source or a numerical fit.

### 6.2. Continuous frequency coverage: the essential non-sampling check

**[ABSTRACT | PAPER — exact geometry with uniform asymptotic bounds]** For sufficiently large integer \(n\), let \(r_n>1\) be the unique root
\[
r_n+\log r_n=n-D.
\]
The \(r\)-interval specified by (24) is precisely
\((r_n,n-D)\). Under \(t=2\pi n/\log r\), it maps onto
\[
I_n=(\alpha_n,\beta_n),\qquad
\alpha_n=\frac{2\pi n}{\log(n-D)},\quad
\beta_n=\frac{2\pi n}{\log r_n}.
\tag{27}
\]
These intervals **overlap**. To verify rather than assume coverage, put \(q=\log n\). Elementary Taylor estimates, uniform as \(n\to\infty\), give
\[
\begin{aligned}
\alpha_n&=\tau(n)+\frac{2\pi D}{q^2}+O(n^{-1}),\\
\beta_n&=\tau(n)+\frac{2\pi}{q}+\frac{2\pi D}{q^2}+O(n^{-1}),\\
\alpha_{n+1}&=\tau(n)+\frac{2\pi}{q}
                    +\frac{2\pi(D-1)}{q^2}+O(n^{-1}).
\end{aligned}
\]
For the second line use
\(\log r_n=q-(D+q)/n+O(q^2/n^2)\).
Thus
\[
\boxed{\beta_n-\alpha_{n+1}=\frac{2\pi}{(\log n)^2}+O(n^{-1})>0
\quad\text{eventually}.}
\tag{28}
\]
The positive overlap is much larger than its stated error. It is not an unverified assertion that samples approximate an integral.

Restrict to those \(n\) for which the full interval \((r_n,n-D)\) lies in \([M+D,2M-D]\). The excluded end indices number \(O(H+D)\). Their frequency extent is bounded, and the expansions above show that the retained intervals cover
\[
[\tau(M)+10\pi,\ \tau(2M)-10\pi]
\tag{29}
\]
for every sufficiently large \(M\). For example the smallest retained index is \(M+H+2D+O(1)\), whose lower frequency endpoint is \(\tau(M)+2\pi+o(1)\); the upper end is treated by the same expansions. The fixed margins in (29) deliberately exceed both end losses.

On all retained intervals,
\[
\left|\frac{dr}{dt}\right|=\frac{r(\log r)^2}{2\pi n}
=(1+o(1))\frac{H^2}{2\pi}
\tag{30}
\]
uniformly. Summing the nonnegative integrals over the overlapping intervals and using (11) now proves
\[
\begin{aligned}
\mathcal J_M
&\ge(1-o(1))\frac{H^2}{2\pi}
 \int_{\tau(M)+10\pi}^{\tau(2M)-10\pi}U(t)^2\,dt\\
&\ge\left(\frac1{12}+o(1)\right)MH^4.
\end{aligned}
\tag{31}
\]
This proof covers every frequency in a real interval before applying a mean-square theorem. It requires no distribution law for values at the original spectral lattice.

### 6.3. Return to the actual finite-window source

**[COFINAL_FAMILY | PAPER]** Equations (26) and (31) give the constant in (22) for \(P_M^\infty\). The lower Young inequality and (15) give the same limiting lower bound for the actual finite-window \(\mathscr A_m^+\). Thus (22) is about the original projected action, with its nonzero window remainder paid.

The strict constant check is elementary, not numerical: \(\pi^2<10\), \(e<3\), and
\[
e^{\pi^2}<3^{10}=59049<65536=D^2.
\]
Hence \(D^2e^{-\pi^2}>1\), and \(C_A>(8/3)\,9=24\). In particular, (16) and (22) imply that for all sufficiently large integer \(M\),
\[
\boxed{
\sum_{M\le m<2M}w_mS_m<4MH,
\qquad
\sum_{M\le m<2M}w_m4L_m^2\mathscr A_m^+>12MH.
}
\tag{32}
\]
The loose constants four and twelve leave a strict margin after all the uniform errors. No optimal constants are needed.

## 7. The strict original discriminator sign

**[COFINAL_FAMILY | PAPER — actual theorem-shape refutation]** Keep the original
\(\mathscr R_m=S_m-4L_m^2(\mathscr A_m^++\mathscr A_m^-)-2L_mO_m\).
The backward block and exterior have nonnegative cost. From (32),
\[
\sum_{M\le m<2M}w_m\mathscr R_m<-8MH,
\qquad
\boxed{\sum_{M\le m<2M}w_m(\mathscr R_m+2S_m)<0.}
\tag{33}
\]
Every weight is strictly positive. If all cells in that finite block had \(\mathscr R_m+2S_m\ge0\), the second sum could not be negative. Therefore
\[
\boxed{\exists m\in\mathbb Z\cap[M,2M):\quad
\mathscr R_m<-2S_m<0.}
\tag{34}
\]
This proof does not assert that every cell in the block is negative. It does prove an actual-source witness in **each sufficiently late block**, which is stronger than refuting a single proof method.

## 8. Admission, the cofinal witness sequence, and the unchanged receiver

**[COFINAL_FAMILY | PAPER — quantifier closure]** Choose an integer \(M_*(P)\) larger than the eventual thresholds in the preceding estimates and large enough that
\(M_*(P)\ge J_P+3\) and \(\log M_*(P)\ge1536\).
These thresholds exist by the uniform estimates and the unconditional asymptotics; their numerical values have not been computed.

Put \(M_k=3^kM_*(P)\). In each finite, nonempty witness set supplied by (34), choose its least element:
\[
\boxed{m_k=\min\{m\in\mathbb Z\cap[M_k,2M_k):
                         \mathscr R_m<-2S_m\},\qquad
j_k=m_k-J_P-2.}
\tag{35}
\]
The nonemptiness was proved by (33), not assumed in this definition. The disjoint blocks make \(m_k\) strictly increasing and unbounded. Every \(j_k\ge1\), every \(L_{m_k}\ge1536\), and \(j_k-1,j_k+D\) remain indices of the original consecutive family. This establishes (1) and supplies the requested rigorously admitted sequence. It is not a selected-cell scan or a new cofinal family substituted for the source; it is a proved witness subsequence of the fixed original family.

**[COFINAL_FAMILY | PAPER — receiver scope]** The exact and still unresolved original increment comparison is
\[
\boxed{\mathscr Q_m=\mathscr R_m+4L_m^2\mathscr V_m^{\rm path}.}
\tag{36}
\]
At the witnesses in (35), PIB128 would require compensation
\(4L_m^2\mathscr V_m^{\rm path}\ge-\mathscr R_m\).
The proof above neither establishes nor excludes that compensation. A strictly negative \(\mathscr R_m\) must not be relabelled as a negative \(\mathscr Q_m\). The same prohibition applies to \(T_m\). This is the failure scope specified in the authoritative request. fileciteturn24file0L78-L102

For an explicit return to the two-window **Gram form**, use the same reference interval and the same two-sign projections \(P_{>m+D}\) and \(P_{\rm odd}\). The second selects exactly \(m+1,m+3,\ldots,m+255\), not all odd integers. Then
\[
\begin{aligned}
W_m={}&\|P_{>m+D}f_{L_+}\|^2+\|P_{>m+D}f_{L_m}\|^2
 -2\langle P_{>m+D}f_{L_+},P_{>m+D}f_{L_m}\rangle\\
&+\|P_{\rm odd}f_{L_-}\|^2+\|P_{\rm odd}f_{L_m}\|^2
 -2\langle P_{\rm odd}f_{L_-},P_{\rm odd}f_{L_m}\rangle.
\end{aligned}
\tag{37}
\]
No sign for \(S_m-4L_m^2W_m-2L_mO_m\) is claimed. Both cross-window inner products in (37) are essential; replacing them by another derivative-action upper estimate would return to the refuted sufficient theorem shape.

The older cofinal MG128 conditional is **not invoked** in this refutation. Its delayed weighted boundary and two-sided energy envelopes remain as previously accepted; no antecedent \(T_m\ge0\) has been supplied here. Thus its disjunction remains unselected.

## 9. Strongest attacks and proof audit

**[ABSTRACT | PAPER — self-audit of the new proof]** The principal risks were not signs in a scalar Cauchy inequality, but changes of object and quantifier.

**Discrete versus continuous mean squares.** Applying (9) directly to \(Z(t_{m,k})\) would be unjustified at this lattice scale. Equation (20) uses only an upper sampling inequality with a paid derivative term. The lower action estimate first proves continuous coverage in (27)–(30). No discrete Hardy moment is assumed.

**Coverage at the joins.** An uncovered fraction of the frequency interval could invalidate the lower bound, since the derivative energy could concentrate there. Equation (28) gives strictly positive overlap at every sufficiently late join. Equation (29) explicitly removes both finite end losses. These are the complete relevant coverage boundaries.

**Full-line versus finite-window coefficients.** The Mellin identity (7) is not an identity for \(e_n(\lambda)\) by itself. The two exact corrections in (13), their square-summable bounds, physical exterior, and weighted errors (14)–(15) are retained. Their suppression is relative to the same positive weights used on both sides of the original inequality.

**Illegitimate separated endpoint norms.** The proof does not take those norms. Its split is into a full transform and an exterior cosine-transform correction, each square summable with its boundary terms paid. This differs from separating the non-square-summable terms of (4).

**Source interference.** Equation (7) evaluates the transform of the complete source, and (8) differentiates that exact transform. The \(Z^2\) and \(U^2\) factors are squares after completion. No sum of theta squares replaces the square of the theta sum. The mixed term inside \(U^2\) is controlled in (11), not silently removed.

**New masks and discarded positive costs.** The original \(\mathscr A_m\) is never redefined. Restricting nonnegative terms of (23) for a lower bound and retaining an upper-bound remainder in (17) are inequalities within the original sums, not new panels, sources or projection operators. The backward block and \(O_m\) strengthen the negative upper envelope (33); their signs and definitions are unchanged.

**Existence versus a numerical certificate.** Equation (35) is a nonconstructive but rigorously admitted sequence following a strict finite-block sign theorem. It does not provide a decimal cell or an effective threshold. This is sufficient for the requested cofinal refutation, not an ARB interval certificate.

**The external import.** Equation (9) is an unconditional, published theorem, explicitly cited and kept separate from the project audit. A formalization would need its own trusted implementation. The new result is PAPER, not LEAN, and has not received an independent review.

## 10. Route map, closeout and dependency ledger

**[COFINAL_FAMILY | PAPER — decision]** What became smaller is an actual named source theorem: uniform PDA128, and even an eventual version of PDA128, are false. The proof does not merely refute an unprojected or separated-endpoint method. The unchanged original increment problem remains open.

| Representation | Decisive power / cost | Status and risk |
|---|---|---|
| **Complete-source Mellin transform plus weighted path coverage.** **[COFINAL_FAMILY; PAPER]** | Refutes the actual action budget on arbitrarily late admitted blocks. Cost: two classical continuous moments, an elementary upper sampling inequality, and a proved interval-cover lower estimate. | Completed here on PAPER; new proof and imports require independent audit. |
| **Exact cross-window Gram form (37).** **[COFINAL_FAMILY; CONDITIONAL]** | Can decide the original PIB128 comparison without the refuted action strengthening. Cost: preserve and estimate two actual cross-window inner products. | Source sign still open; no new norm relaxation is authorized. |
| **Action minus exact path variance (36).** **[COFINAL_FAMILY; CONDITIONAL]** | Makes the possible compensation at each action witness explicit. Cost: an energy-scale estimate of the actual variance, not qualitative positivity. | Equivalent original receiver; no variance-scale estimate has been proved. |

The cross-domain connections used in the completed proof are an exact Mellin/Fourier identity for the theta source, Hilbert/Sobolev control of sampled energy, and a positive moving-window covering argument that permits unconditional continuous moment theorems. No generating identity makes the requested residual zero; instead the positive weighted-block test proves it strictly negative somewhere in every late block.

**Prediction and check scoring.** Both byte checks match. The registered averaged-oscillation attack closes as a cofinal action refutation; its critical coverage test passes by (28). No success is claimed for an unregistered numerical cell prediction. The predecessor's qualitative strict variance remains valid, but it is not credited as an estimate for the compensation in (36). The project audit remains limited to the predecessor.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: original_Qscr_or_T_m_receiver_not_the_action_relaxation
ACTUAL_CONSUMER_REQUIREMENT: original_PIB128_or_an_eventual_nonnegative_T_tail_or_a_direct_MG128_witness
ORIGINAL_REQUESTED_OBJECT: PDA128_for_all_selected_j_GE_1_and_log_m_GE_1536
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_but_not_established_necessary_for_the_unchanged_consumer
KNOWN_WEAKER_INTERFACES:
  - Qscr_equals_Rscr_plus_4L_squared_Vpath_with_the_compensation_retained
  - exact_two_window_Gram_formula_for_W_then_original_Qscr_comparison
  - direct_original_T_m_sign_without_PDA128
FAILURE_TYPE: COUNTEREXAMPLE
EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
KILL_SCOPE: THEOREM_SHAPE
KILLED_OBJECT: universal_or_eventual_PDA128_only
KILL_EVIDENCE_KIND: strict_actual_source_weighted_block_upper_sign
KILL_EVIDENCE_REFERENCE: equations_16_22_32_33_34_35_on_the_request_source_at_SOURCE_COMMIT
FIRST_UNPAID_ORIGINAL_COMPARISON: compensation_in_equation_36_equivalently_the_Gram_comparison_37
ORIGINAL_INCREMENT_EPISTEMIC_STATUS: RESEARCH_DEBT
REOPEN_TRIGGER: independent_energy_scale_control_of_the_exact_variance_or_cross_window_Gram_terms
PDA128_REOPEN_TRIGGER: a_demonstrated_error_in_the_new_crosswalk_moment_import_sampling_cover_or_error_accounting
NOVELTY_AXIS: complete_source_derivative_oscillation_and_original_path_overlap_give_an_actual_cofinal_action_counterexample
MEMORY_ENTRY:
  target: source_core_fixed_128_coupled_projected_dilation_action
  status: FATAL_FOR_PDA128_ONLY
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  failed_strategy: demand_an_eventual_uniform_PDA128_action_budget
  invariant_learned: continuous_projected_action_cannot_replace_the_exact_increment_without_its_source_variance
  forbidden_future_move: promote_a_negative_Rscr_to_Qscr_or_replace_the_failed_action_budget_by_an_automatic_stronger_norm_bound
  next_decisive_test: independent_PAPER_audit_of_the_cofinal_action_refutation_then_the_unchanged_exact_increment_receiver
```

**[COFINAL_FAMILY | PAPER — preservation boundary]** The low epsilon block, literal diagonal, zero node, final descent, paired logarithmic kernel, signed beta correction, exponent-one prime block, prime/square compensation, opposite-side correlation, transfer, Schur-floor, SV and lag remain untouched. No conditional square constants are activated. All original windows, both Fourier signs, the infinite action tail, source cross terms, physical exterior, and selected-family quantifiers are retained. No route or RH promotion follows. fileciteturn24file0L108-L115

No coefficient numerics, selected-cell/grid search, mathematical runtime, fitted cutoff, theta-source truncation, Lean execution, or repository write occurred. Local execution was file I/O, text validation and hashing only. The result has not received independent review.

## CODEX DIRECTIVE

**Perform one read-only, independent PAPER audit of the cofinal PDA128 refutation in this file, against the same request SHA-256 and source commit.** Check the exact complete-source identity (7), the unconditional moment import (9), finite-window corrections (13)–(15), the upper sampling constant in (16)–(21), the factor \(D^2\) in (23)–(26), every interval join and both end losses in (27)–(30), and the strict original-source sign and admission argument (32)–(35). The acceptance target is only `SOURCE_COUPLED_ACTION_BUDGET_REFUTED`, with `KILL_SCOPE: THEOREM_SHAPE` and the cofinal margin \(\mathscr R_m<-2S_m\). If an inequality fails, identify the first invalid step and withhold this new refutation; do not alter the predecessor's accepted results. If the audit passes, return to the unchanged exact receiver (36) or (37), retaining the path variance or cross-window inner products—do not infer a PIB128, MT128 or MG128 sign and do not commission a stronger norm budget. Preserve the original family, energies, windows, projections, carrier, \(Q\), splice, \(N,K\), panel and all signed corrections. No coefficient search, mathematical runtime, source deletion, new mask/panel, Lean, repository write, conditional-constant activation, route promotion or RH claim is authorized.
