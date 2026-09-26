# STATUS: TRY_GOAL058_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP
OUTCOME: OPEN_PRIME_SQUARE_HIGH_FREQUENCY
REQUEST_ID: REQ-2026-09-26-PRIME-SQUARE-HIGH-FREQUENCY
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_PRIME_SQUARE_HIGH_FREQUENCY
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: d366554d34c2feaf31926381aa9649e1217b2025
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-SAME-SIDE-DILATION-HEAD
REQUEST_SHA256_VERIFIED: 5da56ef35f51339f796e6dcc4f6869a96608ee4852217f5d2ca9cb2d9f6e4f06
PREDECESSOR_VERDICT_SHA256_VERIFIED: 39b02d5663ff7c918f8e0875375bd152d05148fc1f3a80c887529a8f93fe9ca2
PREDECESSOR_GIT_BLOB_VERIFIED: dd39ad32a88511c0d6889c86feef9b95e82a806b
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_READ: docs/Codex/PAPER_CHAIN.md_answer_9_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
PRIME_SQUARE_HIGH_FREQUENCY_SAVED: NOT_ESTABLISHED
PRIME_SQUARE_HIGH_FREQUENCY_LEADING: NOT_ESTABLISHED
EXTERIOR_INVOLVING_PHYSICAL_SQUARE_CORRELATIONS: BOUNDED_BY_7_E11_FOR_EVERY_SELECTED_m_GE_16
SQUARE_FREQUENCY_SHOULDER: BOUNDED_BY_E11_OVER_2_FOR_EVERY_SELECTED_m_GE_256
SMALL_PRIME_BASES_LE_LOG_M: BOUNDED_AT_ONE_PLUS_LOG_LOG_M_SCALE
REMAINING_SOURCE_COMPARISON: LARGE_PRIME_SQUARE_INTERIOR_INTERIOR_ERROR_OVERLAP
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: PROPER_SQUARE_CONTRIBUTIONS_BOUNDED_NOT_THE_FULL_REQUESTED_BLOCK
CLOSED_REQUESTED_SAVING_OR_LEADING_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
NEW_SEED_SELECTED: false
EXPONENT_ONE_PRIME_BLOCK: OPEN_SEPARATE
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
TRANSFER_T: OPEN
SOURCE_J_SIGN: OPEN
COMPRESSION_DOMINANCE: OPEN
ACTUAL_VECTOR_ACTIVITY: OPEN
PLANE_AXIS_GAP: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_PRIME_SQUARE_HIGH_FREQUENCY.** I have not proved the requested eventual square saving or an unbounded selected-source leading contribution. No constant for the full block is inferred from its coefficient sum.

There are two new estimates for proper contributions. First, the **exterior-involving part of the exact physical square correlation** has a uniform relative bound: distinct prime-square shifts separate the rapidly decaying exterior profiles, and their ordinary Gram matrix has a uniformly bounded row sum. Second, the admitted projection estimate pays a larger continuous-frequency shoulder for squares than for the whole head. Neither estimate determines the remaining interior–interior correlation.

After also accounting for the small prime bases, the unresolved comparison is reduced, with an explicit lower-order remainder, to the actual error overlap for
\[
\log m<p\le m^{1/4},\qquad 0\le u\le b-2\log p.
\]
This is the only next test commissioned below. No exterior term, endpoint correction, or low-frequency subtraction is silently lost.

## 1. Source lock and exact requested scalar

**[COFINAL_FAMILY | PAPER]** The complete authoritative TXT was read: **5,482 bytes, 105 LF**. The complete predecessor Markdown was read: **30,547 bytes, 544 LF**. Its locally computed SHA-256 and Git blob match the request and the blob returned at the pinned commit. The bootstrap was fetched from `rh_clean` and read through its response-format section. I also opened the requested `docs/Codex/PAPER_CHAIN.md`, specifically its limited independent audit of answer 9. That audit accepts the previous low-frequency, exponent-at-least-three, and decomposition results, not a square or whole-head saving. fileciteturn78file0L13-L27 fileciteturn81file0L3-L5 fileciteturn86file0L2-L2

Fix the same P. Every assertion below about selected cells means
\[
m=J_P+j+2
\]
on the already admitted family, additionally restricted by the displayed explicit lower bound on m. Keep
\[
L=\log m,\quad b=L/2,\quad Q=\sqrt m,\quad X_2=m^{1/4},\quad
\omega_n=2\pi n/L,
\]
the original 5m splice, and the carrier \(-m\le n\le m\). Here \(X_2\) is only the maximal prime base of a square in the requested range; it is not a change of Q or a selected-vector norm.

Write
\[
g=G'',\quad h=T_mg,\quad f=h-g,\quad E=E_{11}=\|f\|_2^2>0,
\quad \ell_m=\log((m+1)/L).
\]
The source functions and projection remain real and even. Their exact coefficients are
\[
\begin{aligned}
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u),\\
b_n&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}G(u)e^{-i\omega_nu}\,du,\\
e_n&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}g(u)e^{-i\omega_nu}\,du
=-\omega_n^2b_n+\epsilon_m,\qquad
\epsilon_m=2G'(b)/\sqrt L,\\
h&=\sum_{n=-m}^{m}e_n\psi_{n,L}.
\end{aligned}
\tag{1}
\]
In particular, the constant in every \(e_n\) remains. These are exactly the objects fixed by the request, not reference functions. fileciteturn78file0L30-L55

**[FINITE_CELL | PAPER]** For compact notation only, let
\[
\begin{aligned}
\mathcal H_m(\xi)&=\frac1{\sqrt L}\sum_{n=-m}^{m}e_n(-1)^n
\mathcal J(\omega_n-\xi,b),\\
\mathcal G_+(\xi)&=\sum_{r\ge1}r^{-s_\xi}
\mathcal H_2(s_\xi;r,\infty),\qquad s_\xi=\tfrac12-i\xi,\\
\Phi_m(\xi)&=(2\pi)^{-1/2}[\mathcal H_m(\xi)-\mathcal G_+(\xi)].
\end{aligned}
\tag{2}
\]
The functions \(h_2,\mathcal H_2,\mathcal J\) have exactly their meanings in the authoritative TXT; in particular \(\mathcal J(0,b)=b\), and the upper limit infinity retains the full positive physical tail. Thus the unpaid source scalar is exactly
\[
\boxed{
\mathscr U_m^{(2)}=\frac2\pi\operatorname{Re}
\sum_{\substack{p\le X_2\\p\text{ prime}}}\frac{\log p}{p}
\int_{|\xi|>\sqrt m}e^{2i\xi\log p}
\left[|\mathcal H_m|^2-\overline{\mathcal H_m}\mathcal G_+
-\overline{\mathcal G_+}\mathcal H_m+|\mathcal G_+|^2\right]d\xi.
}
\tag{3}
\]
The two mixed products in (3) are retained. The finite self-product has independent indices n,q in the original carrier, including n=q. Each of the source factors retains its positive-integer summation index. The expressions are evaluated as the indicated functions; no unsupported termwise integration of an infinite squared series is needed. The admitted half-line Fourier formula and Plancherel identity are precisely those in the request and predecessor. fileciteturn78file0L45-L63 fileciteturn82file0L2-L2

## 2. New estimate: the entire exterior-involving physical square block

This is an estimate for a term in an **exact physical representation** of (3). A continuous-frequency cutoff is not a spatial cutoff: the low-frequency subtraction is kept explicitly in Section 5.

### 2.1. Split the physical overlap without changing either mixed domain

**[FINITE_CELL | PAPER]** For each prime \(p\le X_2\), set
\[
t_p=2\log p,\qquad a_p=b-t_p\ge0,\qquad w_p=\frac{\log p}{p}.
\]
The exact half-line correlation splits as
\[
\begin{aligned}
I_p&=\int_0^\infty f(u)f(u+t_p)du=I_p^{\rm in}+I_p^{\rm out},\\
I_p^{\rm in}&=\int_0^{a_p}f(u)f(u+t_p)du,\\
I_p^{\rm out}&=-\int_{a_p}^{\infty}f(u)g(u+t_p)du.
\end{aligned}
\tag{4}
\]
Only in the last line is the shifted argument always exterior. At the endpoint \(a_p=0\), the interior integral is zero and the exterior integral is still retained.

To verify the bookkeeping, expanding the two parts gives
\[
\begin{aligned}
I_p^{\rm in}={}&\int_0^{a_p}hh_{t_p}
-\int_0^{a_p}hg_{t_p}
-\int_0^{a_p}gh_{t_p}
+\int_0^{a_p}gg_{t_p},\\
I_p^{\rm out}={}&-\int_{a_p}^{b}hg_{t_p}
+\int_{a_p}^{\infty}gg_{t_p},
\end{aligned}
\tag{5}
\]
where \(g_t(u)=g(u+t)\), and similarly for h. Their sum has exactly the original two different mixed domains: the \(hg_t\) term runs to b, and the \(gh_t\) term runs only to \(b-t\). The source-source integral still runs to infinity. Thus (4)–(5) reorganize all four terms; they do not drop a strip of a mixed integral. Those domains are load-bearing in the predecessor. fileciteturn81file0L2-L2

### 2.2. The actual exterior profiles have an almost diagonal Gram matrix

**[COFINAL_FAMILY | PAPER] New derivation.** Use only the admitted exterior estimate
\[
F(u):=-g(u)>0,\qquad F(u+s)\le e^{-\pi ms}F(u),
\qquad u\ge b,\ s\ge0,\ m\ge16.
\tag{6}
\]
Its domain is not extended into the window. The predecessor and the requested audit explicitly retain this as a previously accepted source input. fileciteturn82file0L2-L2 fileciteturn86file0L2-L2

Let
\[
E_O=2\int_b^\infty F(u)^2du\le E,
\qquad v_p(u)=\mathbf1_{[a_p,\infty)}(u)F(u+t_p),\quad u\ge0.
\]
Then \(I_p^{\rm out}=\langle f_+,v_p\rangle\), where \(f_+=\mathbf1_{[0,\infty)}f\), and
\[
\|v_p\|_2^2=E_O/2,\qquad \|f_+\|_2^2=E/2.
\]
For \(p<q\), the common support of \(v_p,v_q\) starts at \(a_p\). Using (6) there gives
\[
0\le\langle v_p,v_q\rangle
\le\frac{E_O}{2}e^{-\pi m(t_q-t_p)}.
\tag{7}
\]
This positivity belongs to an ordinary Gram matrix of nonnegative exterior functions, not to a Weil form or to the signed correlation with f.

Enumerate any subset of the primes in \([2,X_2]\) in increasing order as \(p_1,\ldots,p_s\). Since these are distinct integers,
\[
t_{p_j}-t_{p_i}=2\int_{p_i}^{p_j}\frac{dx}{x}
\ge\frac{2(p_j-p_i)}{X_2}
\ge\frac{2(j-i)}{X_2},\qquad j>i.
\]
Consequently, putting
\[
q_m=e^{-2\pi m^{3/4}},\qquad B_m^{\rm ext}=\frac{1+q_m}{1-q_m},
\]
the sum of the normalized absolute entries in every row of this Gram matrix is at most \(B_m^{\rm ext}\). Explicitly, its off-diagonal row sum is bounded by \(2\sum_{k\ge1}q_m^k\). For arbitrary real coefficients \(c_i\), the inequality \(2|c_ic_j|\le c_i^2+c_j^2\) therefore proves
\[
\boxed{
\left\|\sum_i c_i v_{p_i}\right\|_2^2
\le\frac{E_O}{2}B_m^{\rm ext}\sum_i c_i^2.
}
\tag{8}
\]
The estimate is uniform in the size and choice of the subset. For \(m\ge16\), \(q_m<1/3\), so \(B_m^{\rm ext}<2\).

### 2.3. The square weights are square-summable on this Gram matrix

**[COFINAL_FAMILY | PAPER]** Unlike their absolute sum, the squared square weights have a finite bound:
\[
\begin{aligned}
\sum_p\left(\frac{\log p}{p}\right)^2
&\le\sum_{n=2}^{\infty}\frac{(\log n)^2}{n^2}\\
&\le\int_1^\infty\frac{[\log(x+1)]^2}{x^2}dx
\le C_w:=2+2\log2+(\log2)^2<5.
\end{aligned}
\tag{9}
\]
For the integral comparison, on \([n-1,n]\) both \(\log(x+1)\ge\log n\) and \(x^{-2}\ge n^{-2}\). For the last bound use \(\log(x+1)\le\log x+\log2\), and integrate the resulting quadratic polynomial in \(\log x\).

For any subset \(\mathcal P\) of the prime bases \(p\le X_2\), define the actual exterior-involving contribution
\[
\mathscr X_m(\mathcal P)=4\sum_{p\in\mathcal P}w_p I_p^{\rm out}.
\]
Combining (8), (9), and ordinary Cauchy–Schwarz gives
\[
\boxed{
|\mathscr X_m(\mathcal P)|
\le2\sqrt{EE_O}\left(B_m^{\rm ext}\sum_{p\in\mathcal P}w_p^2\right)^{1/2}
\le2\sqrt{B_m^{\rm ext}C_w}\,E<7E,
\quad m\ge16.
}
\tag{10}
\]
This is a **source-relative uniform bound for the whole exterior-involving square contribution**, not a termwise coefficient-sum bound for (SQ). Its saving comes from the overlap estimate (7). Summing the separate bounds \(|I_p^{\rm out}|\le E/2\) would lose that information and return an order-\(\log m\) coefficient sum.

There is a sharper version for the large bases used below. For \(m\ge256\), \(L\ge4\), and \((\log x)^2/x^2\) is decreasing for \(x\ge L\). Including a first-term allowance for a noninteger L,
\[
\sum_{p>L}w_p^2\le W_L:=
\frac{(\log L)^2}{L^2}
+\frac{(\log L)^2+2\log L+2}{L}.
\]
Hence
\[
\boxed{
|\mathscr X_m(\{L<p\le X_2\})|
\le r_{\rm ext}(m)E,
\quad r_{\rm ext}(m)=2\sqrt{B_m^{\rm ext}W_L}\longrightarrow0.
}
\tag{11}
\]
The uniform bound 7 from (10) remains available even where the explicit expression in (11) is larger. Every square in the chosen arithmetic range is retained; the infinite sum in (9) or (11) is only a positive majorant.

## 3. A larger frequency shoulder is paid for squares

**[COFINAL_FAMILY | PAPER]** This uses the predecessor's already proved pointwise projection estimate, rather than repeating its proof. For \(m\ge16\), with \(\Omega_m=2\pi(m+1)/L\), it states
\[
|\Phi_m(\xi)|^2\le\frac{E}{2\pi}
\left(\frac{8L^3\xi^2}{27\pi^4m^3}+\frac1{\pi m}\right),
\qquad |\xi|\le\Omega_m/2.
\tag{12}
\]
Both the interior orthogonality and the exterior contribution are included in this estimate. Its source proof and audit do not assert it for arbitrary higher frequencies. fileciteturn82file0L2-L2 fileciteturn86file0L2-L2

Take the predetermined analytical split
\[
\Xi_*(m)=\frac{m}{L^{4/3}}.
\]
For \(m\ge256\),
\[
\sqrt m<\Xi_*(m)<\Omega_m/2.
\]
For the first inequality, at m=256 use \(L=8\log2<8\), and then the fact that \(\sqrt m/L^{4/3}\) increases whenever \(L>8/3\). The second follows directly from \(\pi L^{1/3}>1\).

Integrating (12) on this valid interval gives
\[
\int_{|\xi|\le\Xi_*}|\Phi_m(\xi)|^2d\xi
\le E\left[\frac8{81\pi^5L}+\frac1{\pi^2L^{4/3}}\right].
\tag{13}
\]
The predecessor's elementary prime-weight estimate is
\[
\sum_{p\le x}\frac{\log p}{p}\le2\log x+2\log2,
\qquad x\ge2.
\tag{14}
\]
It is an upper bound, not a signed-correlation result. fileciteturn83file0L2-L2

For any subset \(\mathcal P\subseteq\{p\le X_2\}\) and any measurable frequency set \(\mathcal I\subseteq[-\Xi_*,\Xi_*]\), (13)–(14) imply
\[
\begin{aligned}
\left|4\operatorname{Re}\sum_{p\in\mathcal P}w_p
\int_{\mathcal I}e^{it_p\xi}|\Phi_m(\xi)|^2d\xi\right|
&\le(2L+8\log2)
\left[\frac8{81\pi^5L}+\frac1{\pi^2L^{4/3}}\right]E\\
&<\frac12 E,\qquad m\ge256.
\end{aligned}
\tag{15}
\]
For an explicit constant check, \(L\ge4\) implies \(2L+8\log2\le4L\). The resulting coefficient is at most
\(32/(81\pi^5)+4/(\pi^2L^{1/3})<32/19683+4/9<1/2\).

In particular, (15) pays the **actual high-frequency shoulder**
\[
\sqrt m<|\xi|\le m/L^{4/3}
\]
of the requested square block. It also bounds its own square low-frequency contribution. No estimate on \(|\xi|>\Xi_*\) follows. The original target cutoff remains \(\sqrt m\); this is an internal integral decomposition, not a new source, carrier, or Q.

## 4. Small prime bases are lower-order; the rest are not decided

**[COFINAL_FAMILY | PAPER]** Split only the prime-base set, deterministically, at L. Empty sets are permitted. On the original high-frequency region, the mass identity \(\int|\Phi_m|^2=E/2\) and (14) give
\[
\boxed{
\left|4\operatorname{Re}\sum_{p\le\min(L,X_2)}w_p
\int_{|\xi|>\sqrt m}e^{it_p\xi}|\Phi_m(\xi)|^2d\xi\right|
\le4(\log L+\log2)E.
}
\tag{16}
\]
This is a valid lower-order bound for a **proper arithmetic subblock**. It is expressly not a proof of the same bound for the full square range. Using (14) up to \(X_2\) instead of L gives only the predecessor's order-\(L E\) bound.

Both newly chosen boundaries, L in prime-base space and \(m/L^{4/3}\) in continuous frequency, are explicit analytic splits. There is no numerical search or adjustment of either boundary, and neither changes the fixed support boundary \(p^2\le Q\).

## 5. Exact remainder: the still-unpaid interior error overlap

### 5.1. The remaining comparison is on a strictly smaller physical/arithmetic domain

**[FINITE_CELL | PAPER]** Define
\[
\boxed{
\mathscr V_m=
4\sum_{\substack{L<p\le X_2\\p\text{ prime}}}\frac{\log p}{p}
\int_0^{b-2\log p}f(u)f(u+2\log p)du.
}
\tag{17}
\]
It uses the actual difference \(f=h-g\) in both slots; neither slot is replaced by h alone.

Let \(\mathscr U_{m,\rm small}^{(2)}\) denote the small-base high-frequency term in (16), and let
\[
\mathscr L_{m,\rm large}^{(2)}=
4\operatorname{Re}\sum_{\substack{L<p\le X_2\\p\text{ prime}}}w_p
\int_{|\xi|\le\sqrt m}e^{it_p\xi}|\Phi_m(\xi)|^2d\xi.
\]
The exact same-side Fourier correlation identity gives
\[
\boxed{
\mathscr U_m^{(2)}=
\mathscr V_m+
\mathscr U_{m,\rm small}^{(2)}+
\mathscr X_m(\{L<p\le X_2\})-
\mathscr L_{m,\rm large}^{(2)}.
}
\tag{18}
\]
This is where the low-frequency subtraction is accounted for. A physical square head has not been silently identified with its high-frequency part. Its sign in (18) is minus. The predecessor's low-frequency estimate applies to this arithmetic subcollection, because its proof uses the same positive coefficient majorant. fileciteturn78file0L74-L80 fileciteturn82file0L2-L2

Combining (10), (16), and the admitted \(\rho_{\rm low}\) bound proves
\[
\boxed{
|\mathscr U_m^{(2)}-\mathscr V_m|
\le[4(\log L+\log2)+7+\rho_{\rm low}(m)]E
\le12(1+\log L)E,
\qquad m\ge16.
}
\tag{19}
\]
Here \(\rho_{\rm low}\le Lm^{-1/4}/2\le2/e<1\), and \(\log L>0\). For \(m\ge256\), the term 7 can additionally be replaced by the smaller of 7 and \(r_{\rm ext}(m)\). The refined bound (11) tends to zero. The larger shoulder bound (15) is a separate proper-block result; it is not added twice to the remainder in (19).

**The first unpaid selected-source comparison after these estimates is the magnitude and sign of (17), with the full indexed cancellation below, at the actual E scale.** No relative upper bound of order \((1+\log L)E\), or leading lower bound on an unbounded selected set, is established for it.

### 5.2. Full source indices, diagonal, and all four terms of the interior remainder

**[FINITE_CELL | PAPER]** Write \(s_n=1/2-i\omega_n\). For \(\nu=p^2\), define
\[
\begin{aligned}
\widetilde T_{0,p}={}&\frac1{Lp}\operatorname{Re}
\sum_{n,q=-m}^{m}\overline{e_n}e_q(-1)^{q-n}
 e^{2i\omega_q\log p}
\mathcal J(\omega_q-\omega_n,b-2\log p),\\
\widetilde T_{1,p}={}&\frac1{\sqrt L}\operatorname{Re}
\sum_{n=-m}^{m}\sum_{r\ge1}\overline{e_n}(-1)^n
(rp^2)^{-s_n}\mathcal H_2(s_n;rp^2,rQ),\\
\widetilde T_{2,p}={}&\frac1{\sqrt L}\operatorname{Re}
\sum_{n=-m}^{m}\sum_{r\ge1}\overline{e_n}(-1)^n
(p^2)^{s_n-1}r^{-s_n}\mathcal H_2(s_n;r,rQ/p^2),\\
\widetilde T_{3,p}={}&\sum_{r,s\ge1}
\int_1^{Q/p^2}h_2(rx)h_2(sp^2x)dx.
\end{aligned}
\tag{20}
\]
Then the fully source-indexed remaining expression is
\[
\boxed{
\mathscr V_m=4\sum_{\substack{L<p\le X_2\\p\text{ prime}}}
(\log p)[\widetilde T_{0,p}-\widetilde T_{1,p}
-\widetilde T_{2,p}+\widetilde T_{3,p}].
}
\tag{21}
\]
The factor p from \(u=\log x\) cancels the factor \(1/p\) in the weight, exactly as in the predecessor's dilation formula. This does not replace square weights by prime weights in the original variable.

The diagonal is explicitly
\[
(\widetilde T_{0,p})_{n=q}=
\frac{b-2\log p}{Lp}\sum_{n=-m}^{m}|e_n|^2
\cos(2\omega_n\log p).
\tag{22}
\]
No divided-difference convention supplies it. The \(n\ne q\) terms are the full remaining terms in (20), not omitted error terms.

For exact comparison with the predecessor's four terms, define
\(H_+(x)=x^{-1/2}h(\log x)\) on \([1,Q]\) and zero outside, and
\(F_+(x)=\sum_{r\ge1}h_2(rx)\). The original first mixed integral is
\(\int_1^Q H_+(x)F_+(p^2x)dx\), whereas the new interior first mixed integral stops at \(Q/p^2\). Their difference is **retained**, not equated to zero:
\[
\begin{aligned}
T_{1,p}^{\rm full}-\widetilde T_{1,p}
&=\int_{Q/p^2}^{Q}H_+(x)F_+(p^2x)dx,\\
T_{3,p}^{\rm full}-\widetilde T_{3,p}
&=\int_{Q/p^2}^{\infty}F_+(x)F_+(p^2x)dx.
\end{aligned}
\tag{23}
\]
The sum of minus the first strip and plus the second, with weights \(4\log p\), is exactly the exterior term bounded in (10). The other mixed term and the self term have the same upper limit as before. Thus (20)–(23) preserve the two original mixed domains through an explicit, paid remainder.

At \(p^2=Q\), when this occurs for an integer prime base, all four integrals in (20) have zero length. The original nonzero mixed/source strips are still in (23), covered by (10). At a boundary \(p=L\), if L were a prime integer, that prime belongs to the small-base block. No term is missing between the two sets.

The reverse mixed term still has its moving inverse-dilation boundary. For example its sum over the large bases is
\[
\int_1^Q H_+(y)
\sum_{\substack{L<p\le X_2\\p^2\le y,\ p\text{ prime}}}
\frac{\log p}{p^2}F_+(y/p^2)dy.
\tag{24}
\]
No all-divisor identity or replacement by \(\log k\) has been applied. A forward rearrangement would likewise have to keep its actual square-divisor restrictions, including the truncated integration boundary.

In (20)–(24), \(-m\le n,q\le m\), \(r,s\ge1\), and all source-series arguments are at least one. The same polynomial-Gaussian majorants as in the predecessor justify these fixed-cell interchanges; the only newly shortened integrations have smaller domains. The phases, complex conjugates, original polynomial signs, and \(\epsilon_m\) in every \(e_n\) remain. The full positive exterior, and by source evenness both original physical tails, have been bounded in (10), not deleted.

## 6. Why the requested saving and leading alternatives are still open

**[COFINAL_FAMILY | PAPER]** Three specific gaps prevent an unjustified promotion.

First, (7) is available only when the shifted argument is exterior. In (17), both arguments are in the original window. The rapidly decaying, separated functions \(v_p\) are not the interior translated error functions. Their Gram estimate cannot be transplanted to \(I_p^{\rm in}\).

Second, (12) controls a frequency interval ending at \(\Omega_m/2\). The new bound (15) lies inside that interval. Neither (12) nor the integral mass \(E/2\) supplies a signed estimate for the remaining source-weighted square moment beyond \(\Xi_*\). In particular, no pointwise or sign claim for the prime-square multiplier has been imported.

Third, the coefficient-sum bound controls the small-base part because the upper limit there is L. Applied to all prime bases up to \(X_2\), it still yields only
\[
|\mathscr U_m^{(2)}|\le(L+4\log2)E.
\tag{25}
\]
This is not a finite \(C_2(1+\log L)E\) bound on a cofinal family. It is not a lower bound either. The positive arithmetic weights multiply signed correlations. Equation (25), even combined with all the admitted lower-frequency, higher-power, and exterior estimates, therefore does not establish either requested quantifier. The predecessor states this distinction explicitly. fileciteturn83file0L2-L2

Bounding the four terms of (21) separately would again lose the cancellation between the projection and its exact source. None of the available absolute integrability or coefficient estimates gives a relative bound for that complete signed four-term sum. This is a failure to derive the requisite estimate, **not** a proof that it is impossible.

There is consequently no value of \(C_2\) and no threshold \(m_2\) claimed for the whole (SQ), and no \(c_2>0\) or unbounded leading set claimed. The first unpaid expression has been narrowed to (21) up to the explicit remainder (19).

## 7. One strictly narrower falsifiable PAPER test

### TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP

**[COFINAL_FAMILY | CONDITIONAL]** Test only \(\mathscr V_m\) in (17), with its exact source formula (20)–(24), on the unchanged selected family. For definiteness begin on \(m\ge65{,}536\), in addition to the admitted source threshold. At this explicit point \(L<X_2\), and that inequality persists, so the arithmetic interval is not identically empty for large m. No claim of a prime in every such interval is needed.

The two discriminating possible deliveries are:
\[
|\mathscr V_m|\le C_{\rm int}(1+\log L)E
\quad\text{on an explicit selected tail,}
\tag{26}
\]
with a proved finite source constant and threshold; or
\[
|\mathscr V_m|\ge c_{\rm int}\ell_m E
\quad\text{on an explicitly proved unbounded selected-index set,}
\qquad c_{\rm int}>0.
\tag{27}
\]
These are **not results of this review**. They must be obtained from the actual projection/source cancellation, not by defining constants from unknown ratios.

Unlike a raw leading subcomponent in the earlier head decomposition, a leading result (27) would now reach the requested square outcome: the remainder (19) is lower-order. Specifically, after discarding the finite initial part where
\[
12(1+\log L)>\tfrac12c_{\rm int}\ell_m,
\]
(19) gives \(|\mathscr U_m^{(2)}|\ge(c_{\rm int}/2)\ell_mE\) on the same remaining unbounded set. The deterministic inequality displayed here holds eventually because \((1+\log L)/\ell_m\to0\).

Similarly, a proof of (26) would give the requested square saving with
\[
C_2=C_{\rm int}+12
\]
and the larger of the proved source threshold and the thresholds used above. This is an exact conditional implication with a paid remainder; it does not assert either antecedent.

The next test is strictly narrower in two concrete respects: it removes every prime base at most \(\log m\), and it removes all overlaps with a shifted argument outside the physical window. Their contributions have explicit bounds. It does not select another trial or simply rename a source ratio. The larger frequency shoulder (15) is also available, but does not authorize discarding further frequencies without accounting for their contribution.

Even a proved square result would leave the exponent-one block \(\mathscr U_m^{(1)}\) open. A leading square result could be canceled by that block at the whole-head level. The opposite-side term would still be separate, and neither transfer nor any later sign follows. These non-implications are part of the authoritative boundary. fileciteturn78file0L90-L105

### Two representations of this one test

| Representation | Discriminating power | PAPER cost and principal risk |
|---|---|---|
| **Chosen: large-base interior overlap (17), expanded jointly by (20)–(24).** | A saving or leading witness decides the square test through the paid remainder (19), without any exterior-tail or small-base uncertainty. | One restricted square sum, its exact finite self term and both source mixed terms. The cancellation remains relative to E, and the inverse-dilation boundary cannot be flattened. |
| **Alternative: the same residual through the one-sided density (2), subtracting the explicitly bounded exterior and small-base terms.** | The shoulder estimate (15) removes another specified spectral region; any remaining source oscillatory estimate can be transferred through (18). | Must retain the high-frequency cutoff's nonlocality. No argument may simultaneously discard an exterior contribution and replace the half-line density by a full-line transform. |

Only the named test is commissioned. No computation, extra arithmetic search, or second campaign is authorized.

## 8. Adversarial checks and closeout

**[ABSTRACT | PAPER]** The strongest possible misuse of the new estimate would be to replace the full translated errors by the positive exterior profiles in (7). The former have interior support and signed oscillations; the latter start at their translated exterior thresholds and share a proved exponential decay rate. Equation (5) explicitly identifies the interior term that such a replacement would lose. Therefore (10) cannot be read as a bound for the full square correlation.

The Gram estimate's dependence is also testable. Without the separation \(t_{p_j}-t_{p_i}\ge2(j-i)/X_2\) and the source exponential decay, its row sum need not remain bounded as the number of translates grows. Merely invoking positivity of a Gram matrix would not prove (8). The geometric row-sum calculation is the indispensable step.

**[FINITE_CELL | PAPER]** The cutoff checks are explicit: the original frequency boundary remains \(\sqrt m\), both endpoints of the larger shoulder lie inside (12)'s domain, \(p^2=Q\) is handled by (23), and all \(\mathcal J(0,a)\) values use a rather than a quotient. The half-line boundary at zero is not removed. The exact source check \(\Phi_m(0)=G'(b)/\sqrt{2\pi}>0\), accepted in the predecessor, remains consistent with every split. No zero-frequency vanishing was assumed.

**Prediction scoring.** Before the exterior-profile check, the registered expectation was that separated exterior translates would have a uniform Gram bound and hence pay only the exterior-involving contribution. Equations (7)–(10) confirm precisely that expectation. They do not establish a square saving. The larger shoulder estimate is an additional deduction from the already admitted pointwise bound, not a retrospective prediction of the requested outcome. The predecessor's accepted low-frequency and higher-prime-power results are inputs, not rescored new results.

**What closed:** a uniform relative bound for every exterior-involving square subcollection; a vanishing bound for its large-base portion; and a uniform bound for the enlarged square frequency shoulder. **What remains:** the source-signed interior–interior four-term correlation (21), at a lower-order scale or with a genuinely leading lower witness. No requested full-square quantifier has closed, and no selected-source theorem shape has been killed.

The cross-domain bridge is a translated-profile Gram estimate using the source exterior decay and integer spacing of prime bases. The attempted vanishing mechanism is the existing projection orthogonality, which pays a specified frequency shoulder but does not kill the interior correlation. The family-deciding object is now (21), with all discarded portions paid by (19). These distinctions prevent another absolute norm bound from being misreported as a source cancellation.

```yaml
DOWNSTREAM_CONSUMER: high_frequency_prime_square_supplier_for_the_same_side_head
ACTUAL_CONSUMER_REQUIREMENT: joint_prime_and_square_head_control_then_opposite_side_and_symbol_contributions_kept_separate
ORIGINAL_REQUESTED_OBJECT: lower_order_full_high_frequency_square_bound_or_unbounded_square_leading_witness
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: separate_square_saving_is_not_proved_necessary_for_whole_head_or_full_arithmetic_saving
KNOWN_WEAKER_INTERFACES:
  - joint_U1_plus_U2_control_can_allow_leading_square_and_prime_components
  - joint_complete_arithmetic_and_multiplier_control_can_bypass_separate_square_saving
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: equation_21_with_all_four_indexed_terms_20_at_actual_E11_scale
MINIMAL_MISSING_ESTIMATE: selected_large_prime_square_interior_error_overlap_bound_26_or_leading_witness_27
NEW_CLOSED_QUANTIFIERS:
  - every_admitted_selected_m_GE_16_and_every_square_subcollection_satisfy_exterior_bound_10
  - every_admitted_selected_m_GE_256_satisfies_large_base_exterior_bound_11
  - every_admitted_selected_m_GE_256_and_every_square_subcollection_satisfy_frequency_shoulder_bound_15
NEXT_TEST: TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP
DISCRIMINATOR: source_signed_interior_overlap_21_after_paid_remainder_19
NEXT_TEST_STRICT_SCOPE: prime_bases_log_m_LT_p_LE_m_quarter_and_0_LE_u_LE_b_minus_2_log_p
REOPEN_TRIGGER: paid_source_tail_bound_26_or_unbounded_source_lower_witness_27
SQUARE_SAVING_MECHANISM_DEAD: false
SAME_SIDE_HEAD_MECHANISM_DEAD: false
DIVISOR_CORRELATION_MECHANISM_DEAD: false
TRANSFER_CERTIFICATE_DEAD: false
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: source_exterior_translate_Gram_bound_plus_square_specific_frequency_shoulder_with_exact_interior_remainder
MEMORY_ENTRY:
  target: selected_prime_square_high_frequency_correlation
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: exterior_translate_near_orthogonality_does_not_extend_to_interior_error_overlaps
  forbidden_future_move: identify_full_physical_square_head_with_SQ_without_its_low_frequency_subtraction
  next_decisive_test: TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP`, on paper, for the unchanged selected source, using (17) and the full indexed expression (20)–(24).** Seek the eventual relative saving (26), or the genuinely unbounded selected-source leading witness (27). Use the already proved remainder (19) to transfer a successful result to (SQ); do not reinterpret a failed bound as a negation. Keep all four terms, the n=q diagonal, the original Q5/Q6 coefficient, square-prime restrictions and the inverse-dilation boundary. The removed exterior strips are exactly (23), not zero; the low-frequency subtraction has the minus sign in (18). A successful square result leaves the exponent-one block and the full arithmetic/transfer chain separate. No mathematical runtime, numerical cutoff search, Lean, repository write, new seed, source/carrier/Q replacement, route promotion, transfer pass, actual-J sign, compression dominance, vector activity, axis gap, first-tau-sign, Schur-floor, or RH claim is authorized.
