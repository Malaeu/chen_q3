# STATUS: TRY_GOAL058_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION
OUTCOME: OPEN_SOURCE_CORE_LAG_DECAY
REQUEST_ID: REQ-2026-09-26-SOURCE-CORE-CONTINUOUS-LAG-DECAY
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_CONTINUOUS_LAG_DECAY
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 2838c9482b1218cf1548ccd575f23520ab5796bd
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-INTERIOR-SQUARE-CORE-AFTER-ENDPOINT
REQUEST_SHA256_LOCALLY_VERIFIED: cd80d75610ffc45c85e29904663ba5df72718aba351990b28a6f139798d363aa
PREDECESSOR_VERDICT_SHA256_LOCALLY_VERIFIED: 0e8280d2b5a739e56f07ae29f8c6f28ade7ba21a190edea8333dcbe06c659cf1
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: e994d55602109dbe182f8d00110533b97d76ab54
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_READ: docs/Codex/PAPER_CHAIN.md_interior_square_core_test_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
FIXED_CONSTANT: 16
FIXED_SELECTED_THRESHOLD: 65536
FULL_FIXED_LAG_CANDIDATE: NOT_ESTABLISHED
FIXED_SOURCE_COUNTEREXAMPLE: NOT_ESTABLISHED
NEW_CLOSED_DOMAIN: ALL_REQUESTED_LAGS_WHEN_log_m_LE_120
NEW_MARGIN_ON_CLOSED_DOMAIN: D_m_t_GE_9_OVER_80_TIMES_E11
ADDITIONAL_CLOSED_DOMAIN: ALL_SELECTED_m_WHERE_ELEMENTARY_OVERLAP_ENVELOPE_IS_NONNEGATIVE
NEW_EXACT_REPRESENTATIONS:
  - SOURCE_COEFFICIENT_FIRST_DIFFERENCES_WITH_EXPLICIT_CARRIER_EDGE
  - HALF_LINE_SPECTRAL_DENSITY_AND_ITS_WEAK_DERIVATIVE
NEXT_TEST: TEST_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION
NEXT_TEST_STATUS: CONDITIONAL_NOT_PROVED
NEXT_TEST_IS_NECESSARY_FOR_ORIGINAL: false
C0_128: CONDITIONAL_NOT_ACTIVATED
C_INT_134: CONDITIONAL_NOT_ACTIVATED
C2_146: CONDITIONAL_NOT_ACTIVATED
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: PROPER_DOMAIN_QUANTIFIERS_CLOSED_NOT_FULL_LAG_OR_SQUARE_SAVING
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
ROUTE_SCORE: 3
DISCRIMINATOR: D_m_t_EQUALS_16_E11_MINUS_1_PLUS_t_TIMES_ABS_A_m_t
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_CUTOFF_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
DENOMINATOR_CHANGED: false
NEW_SEED_SELECTED: false
HONESTY_STATE: CHALLENGER_NOT_RH
EXPONENT_ONE_PRIME_BLOCK: OPEN_SEPARATE
PRIME_SQUARE_COMPENSATION: OPEN_SEPARATE
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
TRANSFER_T: OPEN
ACTUAL_J_SIGN: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SOURCE_CORE_LAG_DECAY.** I have neither a proof of the fixed candidate on its entire selected tail nor a source-based violation. In particular, the square-saving constants **128, 134 and 146 remain conditional**.

There is a proved proper-domain result, not a changed threshold: the original candidate holds, with the explicit positive margin
\[
16E-(1+t)|A_m(t)|\ge \frac9{80}E,
\]
for **every admitted selected** \(65536\le m\le e^{120}\) and every requested lag. A separate elementary envelope also certifies a specified set of lags for every larger selected \(m\). The original requirement remains every selected \(m\ge65536\); these partial results do not close it.

For the remaining domain, I give two exact representations. The first exposes the actual coefficient jump at the carrier edge without deleting the low \(\varepsilon_m\) block. The second replaces the lag-dependent correlation by the Fourier transform of its **half-line spectral density**. It yields one explicit, lag-free sufficient lemma: a bound on the density's **total variation** plus its mass. That source-specific inequality is still unpaid. It is stronger than the original candidate, not equivalent to it or necessary for it.

## 1. Source lock, audit boundary, and unchanged objects

**[FINITE_CELL | PAPER — transport and source record]** The authoritative TXT was read in full: **5,809 bytes, 117 LF**. The attached predecessor Markdown was read in full: **29,578 bytes, 640 LF**. Their locally computed SHA-256 hashes are in the header. The predecessor's local Git blob is `e994d55602109dbe182f8d00110533b97d76ab54`, matching the blob returned by the GitHub connector at the requested commit. Thus the complete local predecessor used here is byte-locked to the requested hash and to the pinned repository object. The request's ID, boundary and predecessor binding agree. fileciteturn8file0L1-L20 fileciteturn10file0L3-L5

The bootstrap was fetched from `rh_clean` and read through its response-format section. I also opened the specifically requested `docs/Codex/PAPER_CHAIN.md` at the pinned commit, including the section headed **“interior square core test.”** Its limited audit accepts the preceding Fourier identities, energy upper bound, complete-\(S_3\) obstruction, and conditional arithmetic transfer. It does **not** accept the continuous-lag candidate as proved. The obstruction concerns a separate lower-order budget for \(S_3\), not the sign or size of the complete four-block core. fileciteturn11file0L2-L2

**[COFINAL_FAMILY | PAPER — admitted source contract]** Fix the same \(P\) and selected indices
\[
m=J_P+j+2\ge65536,
\qquad L=\log m,\quad b=L/2,\quad Q=\sqrt m,\quad X_2=m^{1/4}.
\]
Keep the original \(5m\) splice and carrier \(-m\le n\le m\). All logarithms are natural. The source remains
\[
\begin{aligned}
h_*(x)&=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},\\
G(u)&=e^{u/2}\sum_{r\ge1}h_*(re^u),\qquad g=G'',\\
h&=T_mg,\qquad f=h-g,\qquad E=E_{11}=\|f\|_{L^2(\mathbb R)}^2>0,\\
\varepsilon_m&=2G'(b)/\sqrt L,\qquad
 d=\varepsilon_m\sum_{|n|\le m}\psi_{n,L},\qquad k=f-d,\\
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u),
\qquad \omega_n=2\pi n/L.
\end{aligned}
\tag{1}
\]
The same source is real and even. The requested scalar is
\[
A_m(t)=\int_0^{b-t}k(u)k(u+t)\,du,
\qquad 0\le t\le b,
\tag{2}
\]
and the unchanged discriminator is
\[
\boxed{D_m(t)=16E-(1+t)|A_m(t)|,
\qquad 2\log L\le t\le b.}
\tag{3}
\]
The denominator is always the original \(E\), including the physical exterior. Auxiliary masses below are not replacement denominators. These are the objects and quantifiers in the authoritative request. fileciteturn8file0L30-L68

## 2. A paid norm identity, with the physical exterior retained

### 2.1. The endpoint norm is source-controlled

**[COFINAL_FAMILY | PAPER]** Put
\[
E_O=2\int_b^\infty |g(u)|^2du,
\qquad B=G'(b),\qquad D_d=\|d\|_2^2.
\]
The exterior input used here is exactly
\[
F(u):=-g(u)>0,\qquad
F(u+s)\le e^{-\pi ms}F(u),
\quad u\ge b,\ s\ge0.
\tag{4}
\]
It is not extended into the window. This is the previously admitted source input recorded in the pinned audit. It can also be checked directly from the predecessor's polynomial calculation: with
\[
\mathcal P(v)=-64v^4+448v^3-660v^2+150v,
\qquad \mathcal A(v)=-\mathcal P(v),
\]
one has, for \(v\ge32\),
\[
32v^4\le\mathcal A(v)\le128v^4,
\qquad \mathcal A'(v)\le264v^3.
\]
Each positive summand of \(F\) then has logarithmic derivative
\[
\frac12+\frac{2v\mathcal A'(v)}{\mathcal A(v)}-2v
\le17-2v\le-v.
\]
On \(u\ge b\), \(v=\pi r^2e^{2u}\ge\pi m\). Integration gives (4), term by term and then after summing. All source indices \(r\ge1\) remain. The preceding source polynomial and exterior calculation are among the audited inputs; no full-core estimate is imported with them. fileciteturn11file0L2-L2

The source's polynomial-Gaussian decay gives \(G'(\infty)=0\), so
\[
B=\int_b^\infty F(u)\,du>0.
\]
Consequently,
\[
\begin{aligned}
B^2
&=2\int_b^\infty F(u)\int_u^\infty F(v)\,dv\,du\\
&\le\frac2{\pi m}\int_b^\infty F(u)^2du
=\frac{E_O}{\pi m}
\le\frac E{\pi m}.
\end{aligned}
\tag{5}
\]
Orthonormality of the unchanged carrier gives
\[
\boxed{D_d=(2m+1)\varepsilon_m^2
       =\frac{4(2m+1)B^2}{L}<\frac{3E}{L}.}
\tag{6}
\]
For the last numerical constant it suffices that
\(4(2m+1)/(\pi m)<3\), which holds on the stated tail using \(\pi>3\).

### 2.2. Orthogonality belongs to \(f\), not to \(k\)

**[COFINAL_FAMILY | PAPER]** On the original window, \(f\) is orthogonal to the carrier, and \(d\) belongs to that carrier. Thus
\[
\langle f,d\rangle_{[-b,b]}=0,
\qquad
\|k\|_{L^2([-b,b])}^2=E-E_O+D_d.
\tag{7}
\]
This is not an assertion that \(k\) is orthogonal to the carrier. It is precisely the opposite low-block bookkeeping required by the request. fileciteturn8file0L45-L52

Let
\[
v_m(u)=\mathbf1_{[0,b]}(u)k(u),
\qquad
\mathcal M_m=\|v_m\|_2^2.
\]
Evenness and (6)–(7) yield the exact mass and its paid upper bound:
\[
\boxed{\mathcal M_m=\frac12(E-E_O+D_d)
\le\kappa_m E,
\qquad \kappa_m=\frac12\left(1+\frac3L\right).}
\tag{8}
\]
In particular, the \(E_O\) term has not been dropped from the original error norm. The quantity \(\mathcal M_m\) is only the positive-half-window mass of the specified algebraic difference.

## 3. Quantifiers that do close without a source-phase estimate

### 3.1. The two overlap intervals matter

**[COFINAL_FAMILY | PAPER — new proper-domain bounds]** For every \(0\le t\le b\), Cauchy–Schwarz gives
\[
|A_m(t)|
\le\left(\int_0^{b-t}|k(u)|^2du\right)^{1/2}
   \left(\int_t^b|k(u)|^2du\right)^{1/2}
\le\mathcal M_m.
\tag{9}
\]
When \(b/2\le t\le b\), these two intervals are disjoint up to a measure-zero endpoint. Their energies sum to at most \(\mathcal M_m\). The arithmetic-geometric mean inequality therefore improves (9) to
\[
\boxed{|A_m(t)|\le\mathcal M_m/2,
\qquad b/2\le t\le b.}
\tag{10}
\]
At \(t=b\), the integral is exactly zero, a stronger statement than (10).

It follows, for every \(0\le t\le b\), that
\[
\begin{aligned}
(1+t)|A_m(t)|
&\le(1+b/2)\mathcal M_m\\
&\le\left(\frac L8+\frac78+\frac3{2L}\right)E.
\end{aligned}
\tag{11}
\]
Indeed, for \(t\le b/2\) use (9); for \(t\ge b/2\) use
\((1+t)\mathcal M_m/2\le(1+b)\mathcal M_m/2\le(1+b/2)\mathcal M_m\).
No sign of the correlation is assumed.

### 3.2. Every requested lag is certified on a bounded selected-index range

**[FINITE_CELL | PAPER — uniform bounded-index subdomain]** On the requested tail, \(L\ge8\). The function
\[
L\longmapsto L/8+7/8+3/(2L)
\]
is increasing for \(L\ge8\), because its derivative is
\(1/8-3/(2L^2)>0\). At \(L=120\), it is exactly
\[
15+\frac78+\frac1{80}=16-\frac9{80}.
\]
Therefore
\[
\boxed{
D_m(t)\ge\frac9{80}E>0,
\quad 65536\le m=J_P+j+2\le e^{120},
\quad 2\log L\le t\le b.
}
\tag{12}
\]
This is a universal paper argument on that entire subdomain, not a computation over selected cells. It is nevertheless a **bounded-index result**, not the eventual family result requested in (TEST). The condition \(m\ge65536\) has not been replaced by a new one.

### 3.3. Specified lag regions are certified for every selected \(m\)

**[COFINAL_FAMILY | PAPER]** Define the elementary envelope
\[
\eta_m(t)=
\begin{cases}
\kappa_m,&0\le t<b/2,\\
\kappa_m/2,&b/2\le t<b,\\
0,&t=b.
\end{cases}
\]
Then
\[
\boxed{D_m(t)\ge[16-(1+t)\eta_m(t)]E.}
\tag{13}
\]
In particular, every requested lag satisfying
\[
t\le\tau_m:=\frac{32L}{L+3}-1
\tag{14}
\]
is paid for every selected \(m\). For \(t\ge b/2\), the additional paid condition is
\[
t\le\sigma_m:=\frac{64L}{L+3}-1.
\tag{15}
\]
These are consequences of the fixed constant 16, not fitted cutoffs. Together with \(t=b\), they explicitly include their respective boundary points.

The original question can now be restricted, without losing an unpaid point, to
\[
\boxed{
\mathcal R=\left\{
(m,t):
\begin{array}{l}
m=J_P+j+2,\ L>120,\\
2\log L\le t<b,\\
(1+t)\eta_m(t)>16
\end{array}\right\}.
}
\tag{16}
\]
An upper envelope larger than 16 on this set is not a counterexample. It only marks the portion not certified by (13).

## 4. Exact source coefficient differences: the carrier edge is not the whole tail

**[FINITE_CELL | PAPER — new representation]** Retain the request's coefficients
\[
c_{m,n}=\begin{cases}
\varepsilon_m,&|n|\le m,\\
e_n,&|n|>m,
\end{cases}
\qquad
k=-\sum_{n\in\mathbb Z}c_{m,n}\psi_{n,L}
\quad\text{in }L^2([-b,b]).
\tag{17}
\]
The source is real and even, so \(c_{m,-n}=c_{m,n}\in\mathbb R\). For clarity, the high coefficients are the actual source integrals
\[
\boxed{
e_n=\frac{2(-1)^n}{\sqrt L}
\sum_{r\ge1}\int_0^b
 e^{u/2}\mathcal P(\pi r^2e^{2u})e^{-\pi r^2e^{2u}}
 \cos(\omega_nu)\,du.
}
\tag{18}
\]
All \(r\ge1\) are present. On any fixed window, polynomial-Gaussian majorants justify this interchange and the real derivatives used below. This provides no uniform relative estimate by itself.

Set
\[
q_m(z)=k(b-z),\qquad 0\le z\le b,
\]
and define the **first differences**, which are changes between neighboring source coefficients,
\[
\delta_{m,n}=\begin{cases}
\varepsilon_m-e_{m+1},&n=m,\\
e_n-e_{n+1},&n>m.
\end{cases}
\tag{19}
\]
The carrier-edge difference is explicit. The subsequent differences are not discarded.

To justify the summation identity, evenness gives \(g(b)=g(-b)\). Two integrations by parts imply, for \(n\ne0\),
\[
e_n=
\frac{2g'(b)}{\sqrt L\,\omega_n^2}
-\frac1{\omega_n^2}
\int_{-b}^b g''(u)\overline{\psi_{n,L}(u)}\,du.
\tag{20}
\]
For each fixed \(m\), this proves \(e_n=O_m(n^{-2})\). The constant here is not claimed small relative to \(E\). Hence \(\sum|e_n|<\infty\), \(e_n\to0\), and \(\sum_{n\ge m}|\delta_{m,n}|<\infty\).

For a finite symmetric sum, ordinary summation by parts gives
\[
\sum_{|n|\le N}c_{m,n}e^{-in\theta}
=
\sum_{n=m}^{N-1}\delta_{m,n}D_n(\theta)+c_{m,N}D_N(\theta),
\qquad
D_n(\theta)=\sum_{r=-n}^n e^{ir\theta}.
\]
The last term tends to zero: \(|D_N|\le2N+1\) and \(c_{m,N}=O_m(N^{-2})\). Thus, for \(0<z\le b\),
\[
\boxed{
q_m(z)=-\frac{N_m(z)}{\sqrt L\,\sin(\pi z/L)},
\qquad
N_m(z)=\sum_{n\ge m}\delta_{m,n}
             \sin\!\left(\frac{(2n+1)\pi z}{L}\right).
}
\tag{21}
\]
At \(z=0\), the quotient is understood through the original continuous Fourier sum, not by assigning a value to a zero denominator. No integral endpoint is removed.

The low block survives in a particularly simple exact check:
\[
\boxed{\sum_{n\ge m}\delta_{m,n}=\varepsilon_m.}
\tag{22}
\]
Thus dropping either the edge correction or the subsequent differences changes the source. There is no vanishing identity here.

Reflection of the overlap interval, not a change of the selected source, yields
\[
\boxed{
A_m(t)=\frac1L\int_0^{b-t}
\frac{N_m(z)N_m(z+t)}
{\sin(\pi z/L)\sin(\pi(z+t)/L)}\,dz,
\quad 0<t\le b.
}
\tag{23}
\]
This is an exact reformulation of the complete correlation. It does not replace it by the carrier-edge term alone. Absolute values taken before preserving the cancellation at \(z=0\) can even create a nonintegrable majorant. Neither (20) nor \(\sum|\delta_{m,n}|<\infty\) supplies a bound at the original \(E\) scale.

## 5. A lag-free spectral identity with all source indices retained

### 5.1. The density and its derivative are well-defined without a contour argument

**[FINITE_CELL | PAPER — exact Fourier identities]** Use the unitary Fourier convention
\[
\Psi_m(\xi)=(2\pi)^{-1/2}\int_0^b k(u)e^{-i\xi u}\,du,
\qquad \rho_m(\xi)=|\Psi_m(\xi)|^2.
\tag{24}
\]
The positive-half-window function is exactly \(v_m\) from (8); it is not the full-line transform of \(k\). Plancherel and translation give
\[
\boxed{
\int_{\mathbb R}\rho_m(\xi)d\xi=\mathcal M_m,
\qquad
A_m(t)=\int_{\mathbb R}e^{i\xi t}\rho_m(\xi)d\xi.
}
\tag{25}
\]
For \(0\le t\le b\), the second identity has precisely the overlap \([0,b-t]\). For \(t>b\), the overlap is empty. The factor in (25) is one, with no extra \(2\pi\), because it is an inner-product Plancherel identity under the unitary convention.

Since \(v_m\) is supported on a finite interval, both \(v_m\) and \(u v_m\) belong to \(L^2\). Consequently \(\Psi_m\in H^1(\mathbb R)\) and
\[
\rho_m'=2\operatorname{Re}(\Psi_m'\overline{\Psi_m})\in L^1(\mathbb R).
\]
Here **\(H^1\)** means that the function and its weak first derivative are square-integrable. The density belongs to **\(W^{1,1}\)**: it and its weak derivative are integrable. Define its **total variation** by
\[
\mathcal V_m:=\int_{\mathbb R}|\rho_m'(\xi)|\,d\xi.
\tag{26}
\]
This is finite for every selected cell. Since an integrable \(W^{1,1}\) function has zero limits at both infinities, integration by parts in (25) has no missing frequency-boundary term:
\[
tA_m(t)=i\int_{\mathbb R}e^{i\xi t}\rho_m'(\xi)d\xi.
\tag{27}
\]
Therefore
\[
\boxed{|A_m(t)|\le\mathcal M_m,\qquad
       t|A_m(t)|\le\mathcal V_m,\qquad
       (1+t)|A_m(t)|\le\mathcal M_m+\mathcal V_m.}
\tag{28}
\]
These statements hold for the actual source but do not yet bound \(\mathcal V_m\) by a fixed multiple of \(E\).

No complex contour has been moved in (24)–(28). The source strip estimate from the predecessor is not needed here. In particular, its energy upper bound \(E\le2^{56}e^{-m/L}\) has not been used as a lower bound for the denominator.

### 5.2. The remaining variation is an explicit pairing of source moments

**[FINITE_CELL | PAPER]** Define
\[
J_0(\lambda,b)=\int_0^b e^{i\lambda u}du,
\qquad
J_1(\lambda,b)=\int_0^b u e^{i\lambda u}du.
\]
Their literal diagonal values are
\[
J_0(0,b)=b,\qquad J_1(0,b)=b^2/2.
\tag{29}
\]
Put \(a=b/2\), and for \(N\ge m\) set
\[
\begin{aligned}
S_{0,N}(\xi)&=\sum_{|n|\le N}c_{m,n}(-1)^nJ_0(\omega_n-\xi,b),\\
S_{1,N}(\xi)&=\sum_{|n|\le N}c_{m,n}(-1)^n
 [J_1(\omega_n-\xi,b)-aJ_0(\omega_n-\xi,b)].
\end{aligned}
\tag{30}
\]
These are source sums, not fitted profiles. The limits
\[
\Psi_m=-\frac1{\sqrt{2\pi L}}\lim_{N\to\infty}S_{0,N},
\qquad
\widehat{(u-a)v_m}=-\frac1{\sqrt{2\pi L}}
                         \lim_{N\to\infty}S_{1,N}
\tag{31}
\]
hold in \(L^2(\mathbb R)\), by the request's windowed \(L^2\) expansion and boundedness of multiplication by \(u-a\) on the window.

Multiplying \(\Psi_m\) by the phase \(e^{ia\xi}\) does not change \(\rho_m\). Differentiating that phase-centered transform gives
\[
\rho_m'=2\operatorname{Re}
 \left[-i\widehat{(u-a)v_m}\,\overline{\Psi_m}\right].
\]
Products of the two \(L^2\) limits converge in \(L^1\). Thus
\[
\boxed{
\mathcal V_m=
\lim_{N\to\infty}\frac1{\pi L}
\int_{\mathbb R}
\left|\operatorname{Im}\bigl(S_{1,N}(\xi)
                           \overline{S_{0,N}(\xi)}\bigr)\right|d\xi.
}
\tag{32}
\]
The two sums in this product have independent indices. The low coefficients \(c_{m,n}=\varepsilon_m\), the high coefficients (18), all source indices, and the diagonal values (29) are retained. This argument uses \(L^2\)-to-\(L^1\) continuity of products, not an unsupported absolute infinite-double-sum interchange.

The generic norm estimate gives only
\[
\mathcal V_m
\le2\|(u-b/2)v_m\|_2\|v_m\|_2
\le b\mathcal M_m.
\tag{33}
\]
Its resulting budget grows with \(L\). Equation (33) supplies neither the desired source-specific variation bound nor its negation. The unpaid issue is the actual imaginary-part pairing in (32), not the mere existence of its moments.

## 6. The first unpaid comparison and exactly one narrower PAPER lemma

### 6.1. Original fixed candidate: still unpaid on \(\mathcal R\)

**[COFINAL_FAMILY | PAPER — open comparison identified]** The exact first unpaid comparison for the original candidate remains
\[
\begin{aligned}
16E\ \ge\ (1+t)\Bigg|\lim_{N\to\infty}\frac1L\operatorname{Re}
\sum_{|n|,|q|\le N}
&\overline{c_{m,n}}c_{m,q}(-1)^{q-n}e^{i\omega_qt}\\[-2mm]
&\cdot J(\omega_q-\omega_n,b-t)\Bigg|,
\qquad (m,t)\in\mathcal R.
\end{aligned}
\tag{34}
\]
The diagonal still has \(J(0,b-t)=b-t\), and the moving upper boundary is unchanged. This is the request's original finite-window correlation after removing only the domains actually paid by (12)–(15). fileciteturn8file0L54-L68

The old coefficient support, the exterior decay, the energy upper bound, and the separate-\(S_3\) obstruction do not give a signed or absolute source comparison for (34). The elementary estimates above do not produce a negative upper envelope for \(D_m(t)\) anywhere either. **No permitted source pair or selected counterexample sequence is supplied.**

### TEST_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION

**[COFINAL_FAMILY | CONDITIONAL — proposed lemma, not proved]** On the unchanged selected family, restricted only to the still-needed cells \(L>120\), test
\[
\boxed{
\mathcal V_m\le16E-\mathcal M_m
=\frac{31}{2}E+\frac12E_O-\frac12D_d,
\qquad m=J_P+j+2,\quad \log m>120.
}
\tag{SV}
\]
Here \(\mathcal V_m\) is **exactly** the source-moment integral (32), \(\mathcal M_m\) is the explicit mass (8), and \(E\) is the original error energy. The budget is derived from the existing constant 16; it is not a constant defined by an unknown supremum or selected after a cutoff search.

The discriminator for this stronger lemma is
\[
\boxed{\Delta_m^{\rm var}=16E-\mathcal M_m-\mathcal V_m.}
\tag{35}
\]
A proved nonnegative lower envelope for (35) on every stated selected cell proves (SV). Equations (28) and (12) then prove the **original** fixed candidate on every selected \(m\ge65536\), with the original constant 16 and every original lag, including both endpoints.

This is a narrower **analytic object**, one lag-free, nonnegative spectral integral per cell rather than a two-parameter signed overlap. It is deliberately a **stronger sufficient hypothesis**, not a logically weaker or equivalent version of (TEST). It combines the four source blocks before estimation; it is not a separate budget for any of them. Its failure would reject this particular sufficient interface only. A source-based refutation of the original candidate still requires a negative upper envelope for (3) at an allowed pair.

The rough estimate (33) is not a proof of (SV). The required source estimate is the right-hand side of (32) against the right-hand side of (SV), with their exact constants. That is the only next lemma commissioned.

### Two representations and their actual discriminating power

| Representation | What a successful estimate would decide | PAPER cost and main risk |
|---|---|---|
| **Chosen: half-line density variation**, (24)–(32), with (SV). | A uniform source upper bound closes every unpaid lag at once and, with (12), proves the original fixed candidate. A lower violation refutes only this stronger interface. | One source-dependent integral of a first-moment pairing per selected cell; no arithmetic weights or lag grid. Generic Cauchy–Schwarz loses the required uniform budget. |
| **Alternative: source coefficient differences**, (19)–(23). | A source-derived bound for the complete numerator pairing can act directly on (34); a rigorous negative margin for (3) can refute the fixed candidate. | Must control the carrier-edge term jointly with all subsequent differences and the cancellation at the endpoint. Keeping only the edge is not source-locked. |

These are two representations of the same unresolved front, not authorization for a second campaign or numerical search.

## 7. Adversarial controls and exact downstream accounting

### 7.1. The variation lemma must not be declared necessary

**[ABSTRACT | PAPER — planted failure of a false converse]** A simple diagnostic distinguishes (SV) from the original lag requirement. It is **not** the theta source and is not a source counterexample.

For a large window, let \(a=\log L\) and take the diagnostic positive-half function \(v=\mathbf1_{[0,a]}\), with diagnostic normalization \(E_{\rm diag}=2a\). For sufficiently large \(L\), \(a<b\). Its correlation is zero at every lag \(t\ge2\log L=2a\). Thus the requested-band lag inequality holds trivially for this diagnostic.

Its Fourier density has
\[
\rho(0)=\frac{a^2}{2\pi},\qquad \mathcal M=a,
\qquad \mathcal V\ge2\rho(0)=\frac{a^2}{\pi}.
\]
The variation inequality follows because the nonnegative density tends to zero at both infinities. If \(a>31\pi\), then
\[
\mathcal M+\mathcal V>32a=16E_{\rm diag}.
\]
Thus a true lag statement can coexist with failure of the proposed stronger variation budget. This deliberately breaks any claimed converse before it can be used on the source. The request's generic high-pass cosine control likewise remains a diagnostic only, not a permitted theta-source witness. fileciteturn8file0L70-L75

### 7.2. Boundary and transformation inventory

**[FINITE_CELL | PAPER]** The domain checks are explicit. At \(t=b\), the overlap is empty and \(D_m(b)=16E\). At \(t=b/2\), the two intervals used in (10) meet at one point only, so the improved bound includes the junction. The lower endpoint \(t=2\log L\) is retained wherever it lies in the original band. All zero denominators in the Fourier moments are assigned their integral values (29), and the Abel quotient at \(z=0\) is interpreted through its original continuous sum.

The Fourier transform in (24) is of \(\mathbf1_{[0,b]}k\), not of the full-line function. Its frequency derivative is justified by compact support in \(u\); no complex strip, contour deformation, or unproved high-frequency asymptotic is used. The exterior estimate (4) is used only on \(u\ge b\). The source \(G\), selected family, finite carrier, physical support, dilation boundary \(Q\), denominator, evenness and homogeneity are preserved throughout. The phase centering in (31) changes neither \(\rho_m\) nor its variation.

### 7.3. The arithmetic constants are still conditional

**[COFINAL_FAMILY | PAPER — admitted conditional transfer]** The source identity and weight bound are
\[
V_m^{[0]}=4\sum_{p\in\mathcal P_m}w_p A_m(t_p),
\qquad
\sum_{p\le X_2}\frac{\log p}{p(1+2\log p)}\le2(1+\log L).
\tag{36}
\]
Only a proof of the complete fixed candidate, for example through a proved (SV), would therefore give
\[
|V_m^{[0]}|\le128(1+\log L)E.
\tag{37}
\]
The exact paid transfer continues to be
\[
\boxed{
U_m^{(2)}=V_m^{[0]}+R_{\varepsilon,m}
+U_{m,\mathrm{small}}^{(2)}+X_{m,\mathrm{large}}
-L_{m,\mathrm{large}}^{(2)}.
}
\tag{38}
\]
Its low-frequency subtraction is negative, and
\[
|R_{\varepsilon,m}|<6E,
\qquad
|U_m^{(2)}-V_m^{[0]}|
\le[12(1+\log L)+r_\varepsilon(m)]E.
\tag{39}
\]
Thus **128, 134 and 146 are not activated by this OPEN verdict**. The bounded-index result (12) does not turn (37) into an eventual-family theorem. These transfer identities and the distinction between a sufficient lag lemma and the arithmetic target are part of the request. fileciteturn8file0L96-L106

## 8. Closeout and dependency epistemics

**[COFINAL_FAMILY | PAPER] What became smaller.** The whole requested lag interval is now certified on the bounded selected-index domain \(65536\le m\le e^{120}\), and the additional elementary regions (13)–(15) are certified for every selected \(m\). The first potentially unpaid domain is explicitly (16). Two exact source representations identify the carrier-edge cancellation and the lag-free first-moment pairing without replacing the original source.

**What was not closed or killed.** The full fixed candidate, a source counterexample, the full square saving, and any downstream sign remain open. No requested theorem shape has been refuted. In particular, a growing generic upper bound for \(\mathcal V_m\) is not a lower bound on its actual value.

**Prediction accounting.** The predecessor's fixed lag candidate remains unresolved; it is not scored as confirmed or refuted. The announced summation-by-parts check produced an exact carrier-edge representation, but not a paid remainder at the target scale. No directional prediction was registered for the newly found elementary-domain estimates before their derivation, so they receive no retrospective prediction credit. The next variation test is proposed but has not been executed or passed. The older independently audited separate-\(S_3\) obstruction is an input, not a newly scored result.

The cross-domain bridge is the exact Fourier correlation identity (25), followed by the integration-by-parts transfer (27). The attempted vanishing route is blocked by the exact nonzero low-block identity (22). The family-deciding sufficient object proposed here is the source density variation budget (SV); its proof would close the remaining lag quantifier in one step, while its failure would leave weaker arithmetic interfaces available.

```yaml
DOWNSTREAM_CONSUMER: high_frequency_prime_square_supplier_for_the_same_side_head
ACTUAL_CONSUMER_REQUIREMENT: paid_control_of_the_complete_signed_square_contribution
ORIGINAL_REQUESTED_OBJECT: fixed_constant_16_continuous_lag_bound_on_original_selected_tail
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: not_proved_necessary_for_arithmetic_weighted_core_saving
KNOWN_WEAKER_INTERFACES:
  - direct_arithmetic_weighted_core_bound_implies_square_saving_through_paid_transfer
  - bounds_only_at_prime_square_lags_can_suffice_without_all_real_lags
  - joint_prime_and_square_control_can_allow_compensation
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: equation_34_on_domain_16
MINIMAL_MISSING_IDENTITY_OR_ESTIMATE: actual_c_weighted_lag_envelope_on_R_or_a_source_bound_for_SV
NEW_CLOSED_QUANTIFIERS:
  - all_selected_65536_LE_m_LE_exp_120_and_all_requested_lags_satisfy_margin_12
  - all_selected_m_and_every_lag_with_nonnegative_envelope_13_satisfy_TEST
NEW_EXACT_REPRESENTATIONS:
  - equations_19_to_23_keep_the_carrier_edge_and_all_source_differences
  - equations_24_to_32_keep_the_half_line_density_and_source_moment_pairing
NEXT_TEST: TEST_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION
NEXT_TEST_DOMAIN: unchanged_selected_m_with_log_m_GT_120
NEXT_TEST_DISCRIMINATOR: Delta_var_EQUALS_16_E11_MINUS_mass_MINUS_density_total_variation
NEXT_TEST_SUCCESS_IMPLICATION: SV_plus_equation_12_proves_original_TEST_with_constant_16_and_threshold_65536
NEXT_TEST_FAILURE_IMPLICATION: refutes_only_SV_not_original_TEST_or_core_saving
ORIGINAL_DISCRIMINATOR: D_m_t_EQUALS_16_E11_MINUS_1_PLUS_t_TIMES_ABS_A_m_t
REOPEN_TRIGGER: source_proof_of_SV_or_direct_lag_envelope_on_R_or_a_permitted_source_violation_of_D
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: overlap_geometry_closes_proper_domains_and_source_moment_pairing_removes_lag_parameter
MEMORY_ENTRY:
  target: fixed_source_core_continuous_lag_decay
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: low_block_and_half_line_window_survive_both_Abel_and_spectral_density_transforms
  forbidden_future_move: promote_variation_bound_failure_or_a_generic_diagnostic_to_a_theta_source_counterexample
  next_decisive_test: TEST_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION
```

The exponent-one prime block and prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor and RH remain open. No independent audit of this new argument, mathematical runtime, Lean execution or repository write was performed. fileciteturn8file0L108-L117

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION`, on PAPER, on the unchanged selected cells with \(\log m>120\).** Verify the elementary-domain certificate (8)–(16), then test the single source inequality (SV), using the literal coefficients (17)–(18) and moment pairing (29)–(32). A source-derived nonnegative lower envelope for \(\Delta_m^{\rm var}\) on every such cell, combined with (12), proves the original fixed constant-16 candidate on the original threshold \(m\ge65536\); only then activate \(C_0=128\), \(C_{\rm int}=134\), \(C_2=146\). A rigorous negative upper envelope for \(\Delta_m^{\rm var}\) rejects only this stronger variation interface and leaves the original lag candidate OPEN unless an actual permitted pair with \(D_m(t)<0\) is independently proved. Retain the original \(E\), the physical exterior, the low \(\varepsilon_m\) block, independent Fourier indices, literal diagonal values, all source summation indices, moving overlap endpoints, and the negative low-frequency term in (38). Do not infer source decay from coefficient support, drop the post-edge differences, or assign a separate lower-order budget to the full \(T_3\) block. No mathematical runtime, numerical cutoff search, Lean, repository write, new seed, source/carrier/\(Q\)/denominator replacement, route promotion or RH claim.
