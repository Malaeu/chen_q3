# STATUS: TRY_GOAL058_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION
OUTCOME: OPEN_SOURCE_LOG_SYMBOL_TRANSFER
REQUEST_ID: REQ-2026-09-26-LOG-SYMBOL-TRANSFER
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_LOG_SYMBOL_TRANSFER
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 7ef70edc4c67b4dce7b20947bca5a07c5cb281f0
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-COMPRESSION-SPECTRAL-SPREAD
REQUEST_SHA256_VERIFIED: 20ce52918516fbd3cea8b3def110619f021c440a1cab3ca81f93afd3d3f6a6a8
PREDECESSOR_VERDICT_SHA256_VERIFIED: de75515ca7cc2372a9645ded33bd5792b249ebbc82d1b1521f3373af89fe8692
PREDECESSOR_GIT_BLOB_VERIFIED: b771a60813654aa69a2d70dfe02787c62517e469
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
TEST_ORDER: N11_FIRST
N11_QUARTER_SCALE_BOUND: NOT_ESTABLISHED
N11_UNBOUNDED_STRICT_REVERSE: NOT_ESTABLISHED
N00_AND_N01_QUARTER_SCALE_BOUNDS: NOT_ESTABLISHED
SOURCE_LOG_SYMBOL_TRANSFER_PASS: NOT_ESTABLISHED
SOURCE_LOG_SYMBOL_TRANSFER_KILL: NOT_ESTABLISHED
DERIVATIVE_POLE_RELATIVE_ENVELOPE: PROVED_BELOW_FOR_m_GE_16
DERIVATIVE_RETURNED_PRIME_TAIL_RELATIVE_ENVELOPE: PROVED_BELOW_FOR_m_GE_16
COMBINED_POLE_AND_RETURNED_TAIL_THRESHOLD: m_GE_65536_ON_THE_ADMITTED_SELECTED_TAIL
COMBINED_RELATIVE_BOUND: abs_POLE_minus_PRIME_GT_m_LT_ell_m_E11_div_16
COMPLETE_PRIME_ACTION_ON_G_SECOND_DERIVATIVE: EXACT_DIVISOR_COLLAPSE_PROVED_BELOW
FINITE_PRIME_VERSUS_MULTIPLIER_JOINT_BOUND: NOT_ESTABLISHED
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: TWO_RELATIVE_COMPONENT_ENVELOPES_NOT_THE_REQUESTED_TRANSFER
CLOSED_REQUESTED_TRANSFER_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
COLUMN_UNITS_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
NEW_RANK_ONE_SEED_SELECTED: false
SOURCE_J_SIGN: OPEN
COMPRESSION_DOMINANCE: OPEN
ACTUAL_VECTOR_ACTIVITY: OPEN
PLANE_AXIS_GAP: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SOURCE_LOG_SYMBOL_TRANSFER.** The first requested diagonal estimate, for **the actual \(N_{11}\)**, is neither proved on a selected tail nor strictly refuted on an unbounded selected set. Consequently the three-entry quarter-scale certificate **(T) remains unproved, not refuted**. The other two entries are not credited with a pass while this first test remains open.

There is a source-relative result, stronger than an absolute continuity budget. On the unchanged selected tail with \(m\ge2^{16}\), the **pole contribution together with every returned prime power \(\nu>m\)** has absolute value less than
\[
\boxed{\frac1{16}\ell_m E_{11}.}
\]
The proof uses the admitted exterior decay and the actual projection's orthogonality. Neither physical exterior tail is removed. It leaves the **joint difference between the integrated multiplier deviation and the finite-prime correlations** as the unpaid quantity.

A separate exact arithmetic calculation collapses the complete prime translates of the source \(G''\) to one **log-weighted source series**, using \(\sum_{d\mid r}\Lambda(d)=\log r\). That identity does not estimate the remaining finite-window cancellation and does not prove (T).

## 1. Source lock, notation, and the inherited boundary

**[COFINAL_FAMILY | PAPER]** Read the authoritative TXT in full: **4,473 bytes**. Read the complete local predecessor: **29,445 bytes**. Its SHA-256 matches the request, and its local Git blob matches the blob returned at the requested pin. The bootstrap was fetched from `rh_clean` and read through its response-format section. The request admits the predecessor's geometric suppliers but explicitly does not admit its relative transfer. fileciteturn63file0L20-L26 fileciteturn66file0L3-L5

Fix the same \(P\), with
\[
m=J_P+j+2,\qquad L=\log m,\qquad b=L/2,\qquad
\omega_n=2\pi n/L,\qquad \ell_m=\log\frac{m+1}{L}.
\]
The original \(5m\) splice, Fourier carrier \(-m\le n\le m\), and column units remain fixed. The recurrence endpoint \(6m-1\) is not a Fourier cutoff in this argument.

For the first diagonal only, use the following local notation:
\[
g=G'',\qquad h_m=T_mg,\qquad f_m=h_m-g=\Delta_1,
\qquad E=E_{11}=\|f_m\|_2^2.
\tag{1}
\]
Here \(h_m\) is the projection of the actual derivative column, not a new trial or a replacement for the selected \(x\). The admitted lower scale gives \(E>0\) for \(m\ge16\). No proof of the prior \(E_{00}/E_{11}\) estimate is repeated. fileciteturn66file0L2-L2

The exact source columns are retained:
\[
\begin{aligned}
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u),\\
b_n&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}G(u)e^{-i\omega_nu}\,du,\\
e_n&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}G''(u)e^{-i\omega_nu}\,du
=-\omega_n^2b_n+\epsilon_m,\\
\epsilon_m&=2G'(b)/\sqrt L,\qquad
h_m=\sum_{n=-m}^{m}e_n\psi_{n,L}.
\end{aligned}
\tag{2}
\]
Both columns and \(h_m,f_m\) are real and even. The complex Fourier convention in (2) has not been replaced by a different transform. In particular, the Q5/Q6 edge term remains in every \(e_n\). The finite-to-global error-form identity in the request is used as admitted, without replacing \(K_j\) by a positive operator. fileciteturn63file0L29-L43

## 2. Separate the three contributions before estimating their sum

**[FINITE_CELL | PAPER]** Write the full derivative-error correlation as
\[
\Gamma_m(t)=\operatorname{Re}\int_{\mathbb R}
\overline{f_m(u)}[f_m(u+t)+f_m(u-t)]\,du.
\]
Use the unitary continuous Fourier transform of the predecessor. Set
\[
\begin{aligned}
\mathscr A_m&=\int_{\mathbb R}
[\mathfrak a(\xi)-\ell_m]|\widehat f_m(\xi)|^2\,d\xi,\\
\mathscr O_m&=\int_0^\infty2\cosh(t/2)\Gamma_m(t)\,dt,\\
\mathscr P_m^{\le}&=\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\Gamma_m(\log\nu),\\
\mathscr P_m^{>}&=\sum_{\nu>m}\frac{\Lambda(\nu)}{\sqrt\nu}
\Gamma_m(\log\nu).
\end{aligned}
\tag{3}
\]
Thus the literal requested residual is
\[
\boxed{N_{11}=\mathscr A_m+\mathscr O_m-
\mathscr P_m^{\le}-\mathscr P_m^{>}.}
\tag{4}
\]
The archimedean subtraction and constant are incorporated in the exact \(\mathfrak a\), not dropped. Formula (4) is precisely the request's complete global residual, with the prime range separated only for estimation. Its convergence is inherited from the admitted source form-domain result. fileciteturn63file0L34-L43 fileciteturn66file0L2-L2

### Fully indexed source correlation

**[FINITE_CELL | PAPER]** Define
\[
\begin{aligned}
Q_m(t)={}&\sum_{n=-m}^{m}2(1-t/L)e_n^2\cos(\omega_nt)\\
&+\sum_{-m\le n<q\le m}2e_ne_q
\frac{\sin(\omega_qt)-\sin(\omega_nt)}{\pi(n-q)},
\qquad 0\le t\le L,\\
V_m(t)={}&\operatorname{Re}\sum_{n=-m}^{m}e_n
\int_{-b}^{b}\overline{\psi_{n,L}(u)}
[g(u+t)+g(u-t)]\,du,\\
U(t)={}&\int_{\mathbb R}g(u)[g(u+t)+g(u-t)]\,du.
\end{aligned}
\tag{5}
\]
Extend \(Q_m(t)\) by zero for \(t>L\). The separate diagonal is the first line of \(Q_m\). The off-diagonal sum is the literal source sine kernel, not a limiting diagonal convention. This is the predecessor's finite contraction kernel with the exact \(e\) column inserted.

Polarization, using the proved reality and evenness only, gives
\[
\boxed{\Gamma_m(t)=Q_m(t)-2V_m(t)+U(t).}
\tag{6}
\]
The integrations in \(V_m\) retain the shifted source values outside the window; \(U\) retains both full physical half-lines. No cancellation is estimated by bounding its three terms independently.

For the continuous-frequency part, the exact expression is
\[
\boxed{
\widehat f_m(\xi)=
\frac{2\sin(b\xi)}{\sqrt{2\pi L}}
\sum_{n=-m}^{m}\frac{e_n}{\xi-\omega_n}
+\xi^2\widehat G(\xi).
}
\tag{7}
\]
Each apparent singularity at \(\xi=\omega_n\) is removable by its original window integral. Those points and \(\xi=0\) are included. This follows directly from (2) and \(\widehat{G''}=-\xi^2\widehat G\); no high-frequency approximation is used.

Equations (2), (5)–(7), with \(-m\le n,q\le m\), all \(u\in\mathbb R\) where shown, and every \(2\le\nu\le m\) in (3), are the full indexed source formula for the unpaid correlation below. The entire source \(G=\mathcal E h_*\) is unchanged. Its arithmetic series index is not an extra Fourier carrier index.

## 3. A paid relative bound for the pole term

### 3.1. Its exact sign and factor

**[FINITE_CELL | PAPER]** Since \(f_m\) is real and even and has the admitted weighted decay, Fubini gives
\[
\boxed{
\mathscr O_m=2\left(\int_{\mathbb R}f_m(u)\cosh(u/2)\,du\right)^2\ge0.
}
\tag{8}
\]
Indeed, if \(c(t)=\int f_m(u)f_m(u+t)du\), then \(\Gamma_m=2c\), and the bilateral exponentially weighted correlation integral is the product of the two exponential moments. Evenness makes those two moments equal. This positivity concerns the pole contribution only, not \(N_{11}\) or \(\mathcal W\).

Put
\[
E_I=\int_{-b}^{b}|f_m|^2,
\qquad E_O=\int_{|u|>b}|g(u)|^2,
\qquad E=E_I+E_O.
\]
The actual projection gives \(f_m|_{[-b,b]}\perp\psi_{n,L}\) for every retained \(n\). For \(\phi(u)=\cosh(u/2)\) restricted to the window, its exact coefficient is
\[
\phi_n=\frac{\sinh(L/4)}{\sqrt L(\omega_n^2+1/4)}.
\]
Hence
\[
\left|\int_{-b}^{b}f_m\phi\right|
\le\sqrt{E_I\,q_I(m)},
\qquad
\boxed{q_I(m)=\frac{L^3\sinh^2(L/4)}{24\pi^4m^3}.}
\tag{9}
\]
The estimate uses \(\sum_{n>m}n^{-4}\le(3m^3)^{-1}\), not a bound on the low modes of \(f_m\) in the continuous Fourier transform. No band-limitation of the global error is asserted.

### 3.2. The exterior moment is controlled relative to its own energy

**[COFINAL_FAMILY | PAPER]** Use the predecessor's admitted source decay, without repeating its geometric proof. With \(F(t)=-G''(t)\), for \(m\ge16\), \(t\ge b\), and \(s\ge0\),
\[
F(t)>0,\qquad F(t+s)\le e^{-\pi m s}F(t).
\tag{10}
\]
This comes from the exact source polynomial series, not from a Gaussian replacement. fileciteturn67file0L2-L2

Here is the weighted estimate needed for (8). Let \(c=\pi m>1\) and \(F_b(s)=F(b+s)\). The tail inequality
\(\int_s^\infty F_b(v)^2dv\le F_b(s)^2/(2c)\)
implies, by integration by parts and absorption,
\[
\int_0^\infty e^{(c+1)s}F_b(s)^2ds
\le\frac{2c}{c-1}\int_0^\infty F_b(s)^2ds.
\]
Weighted Cauchy–Schwarz therefore gives
\[
\left(\int_0^\infty e^{s/2}F_b(s)ds\right)^2
\le\frac{E_O}{c-1}.
\]
Both half-lines and \(\cosh((b+s)/2)\le\cosh(b/2)e^{s/2}\) now yield
\[
\left|\int_{|u|>b}f_m(u)\cosh(u/2)du\right|
\le\sqrt{E_O\,q_O(m)},
\qquad
\boxed{q_O(m)=\frac{4\cosh^2(L/4)}{\pi m-1}.}
\tag{11}
\]
The exterior value here is the exact \(-G''\); it is not continued by zero.

Combining (9) and (11) by ordinary two-component Cauchy–Schwarz gives the actual-source envelope
\[
\boxed{
0\le\mathscr O_m\le p_m E,
\qquad p_m=2\bigl(q_I(m)+q_O(m)\bigr),\qquad m\ge16.
}
\tag{12}
\]
All constants in this envelope are specified independently of the desired transfer sign.

## 4. Every returned prime power has a relative tail envelope

**[COFINAL_FAMILY | PAPER]** For \(t\ge L\), any pair of points separated by \(t\) has at least one member outside \((-t/2,t/2)\). Splitting the correlation integral according to which member is outside and applying ordinary Cauchy–Schwarz gives
\[
|\Gamma_m(t)|\le4\sqrt E
\left(\int_{|u|\ge t/2}|f_m(u)|^2du\right)^{1/2}.
\]
For these outer points \(f_m=-G''\). Applying (10) to both half-lines,
\[
\int_{|u|\ge t/2}|f_m(u)|^2du
\le e^{-\pi m(t-L)}E_O\le e^{-\pi m(t-L)}E.
\]
Thus
\[
\boxed{|\Gamma_m(t)|\le4E e^{-\pi m(t-L)/2}\qquad(t\ge L).}
\tag{13}
\]
This includes the boundary \(t=L\). It does not assert that \(\Gamma_m(L)=0\).

Use \(0\le\Lambda(\nu)\le\log\nu\), which retains prime powers rather than replacing the arithmetic support by primes only. The function
\(x\mapsto (\log x)x^{-\pi m/2-1/2}\) is decreasing for \(x\ge m\ge16\). The decreasing integral comparison therefore gives
\[
\begin{aligned}
|\mathscr P_m^{>}|
&\le4E\sum_{\nu>m}\frac{\log\nu}{\sqrt\nu}
\left(\frac{\nu}{m}\right)^{-\pi m/2}\\
&\le r_m E,
\end{aligned}
\]
\[
\boxed{
r_m=\frac{8\sqrt m\,L}{\pi m-1}
+\frac{16\sqrt m}{(\pi m-1)^2},\qquad m\ge16.
}
\tag{14}
\]
This is an explicit bound for the **complete returned range \(\nu>m\)**. It is a paid remainder, not authorization to delete that range in an identity. The elementary Mangoldt bound follows immediately from its prime-power definition. citeturn207815view0

### Explicit combined threshold

**[COFINAL_FAMILY | PAPER]** The estimates above have the following convenient, deliberately conservative simplification. For \(m\ge16\), \(L\ge2\) and \(L\le\sqrt m\). From (9), \(q_I\le m^{-1/2}\). Also
\[
4\cosh^2(L/4)=\sqrt m+2+m^{-1/2}
\le\tfrac{25}{16}\sqrt m,
\qquad \pi m-1\ge\tfrac{47}{16}m,
\]
so \(q_O\le25/(47\sqrt m)<m^{-1/2}\). Consequently
\[
p_m\le\frac4{\sqrt m},\qquad
r_m\le\frac{4L+1}{\sqrt m},\qquad
p_m+r_m\le\frac{4L+5}{\sqrt m}.
\]
Since \(\ell_m\ge L-\log L\ge L/2\),
\[
\boxed{
\frac{p_m+r_m}{\ell_m}\le\frac{13}{\sqrt m},\qquad
|\mathscr O_m-\mathscr P_m^{>}|
\le(p_m+r_m)E<\frac1{16}\ell_m E
\quad(m\ge2^{16}).
}
\tag{15}
\]
The last strict comparison is exact: \(13/256<1/16\). Thus the threshold **65,536** is proved, not fitted. The family scope is every \(j\) on the admitted selected tail with \(J_P+j+2\ge65,536\). This threshold belongs to (15), **not to a claimed proof of (T)**.

A useful one-sided version, retaining the sign in (8), is
\[
-r_m E\le\mathscr O_m-\mathscr P_m^{>}
\le(p_m+r_m)E.
\tag{16}
\]

## 5. The first exact unpaid source comparison

**[COFINAL_FAMILY | PAPER]** Define only for locating this remaining debt
\[
\mathscr C_m=\mathscr A_m-\mathscr P_m^{\le}.
\]
Its complete formula is
\[
\boxed{
\begin{aligned}
\mathscr C_m={}&\int_{\mathbb R}[\mathfrak a(\xi)-\ell_m]
\left|\frac{2\sin(b\xi)}{\sqrt{2\pi L}}
\sum_{n=-m}^{m}\frac{-\omega_n^2b_n+\epsilon_m}{\xi-\omega_n}
+\xi^2\widehat G(\xi)\right|^2d\xi\\
&-\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\left[Q_m(\log\nu)-2V_m(\log\nu)+U(\log\nu)\right].
\end{aligned}}
\tag{17}
\]
The kernels, conjugation convention, diagonal, and ranges in (2), (5)–(7) are part of this formula. In the squared expression, each Fourier sum retains its own independent index in \(-m,\ldots,m\). The removable points in (7) are included, and both physical endpoints remain in \(\epsilon_m\), \(V_m\), and \(U\).

The proved source enclosure is now
\[
\boxed{
\mathscr C_m-r_mE\le N_{11}
\le\mathscr C_m+(p_m+r_m)E.
}
\tag{18}
\]
**No source-derived upper and lower bounds for (17) strong enough to decide the requested quarter-scale comparison have been established here.** In particular, the integrated continuous-frequency deviation is not estimated by replacing \(\mathfrak a\) with its pointwise leading logarithm, and the finite-prime term is not assigned a sign from its positive weights.

For orientation only, \(|\mathscr C_m|\le3\ell_mE/16\), together with (15), would certify the first diagonal. A sufficiently separated strict reverse would refute that diagonal. These are consequences of the paid remainder, **not new results or a renamed next task**.

### Why the available estimates do not pay (17)

**[COFINAL_FAMILY | PAPER]** The previous absolute continuity budget gives a bound containing \(\ell_mE\) before any cancellation is resolved, already larger than the requested quarter-scale. The predecessor explicitly leaves this relative estimate unproved. Its positive \(L^2\) error geometry and lower scale ensure a meaningful denominator, not a bound for the signed difference (17). fileciteturn66file0L2-L2

A uniform special-function bound makes the other missing input visible. DLMF 5.9.13 gives the integral for \(\psi(z)-\log z\). Because
\(0<(1-e^{-t})^{-1}-t^{-1}<1\), it implies
\(|\psi(1/4+i\xi/2)-\log(1/4+i\xi/2)|\le4\). Therefore, with \(\Omega_m=2\pi(m+1)/L\),
\[
|\mathscr A_m|\le4E+
\underbrace{\int_{\mathbb R}
\left|\log\frac{\sqrt{\xi^2+1/4}}{\Omega_m}\right|
|\widehat f_m(\xi)|^2d\xi}_{\mathscr L_m}.
\tag{19}
\]
This is an integral against the actual error, not a pointwise replacement of the symbol. **No adequate source-relative bound for \(\mathscr L_m\) is supplied.** Its finiteness does not establish the required scale. The only external special-function input here is the stated integral identity; it supplies no source estimate. citeturn964236view0

Likewise, \(|\Gamma_m(t)|\le2E\) for arbitrary shifts only gives a coarse finite-prime bound. It discards the source's signed correlations and does not establish their cancellation with (19). The new estimate (13) applies at \(t\ge L\), not throughout \(\log2\le t\le L\); extrapolating it inward would be an invalid domain change.

**Disposition of (T).** The \(11\) entry has not passed and has not been killed. There is consequently no claim of compatible \(00\) and \(01\) estimates, no threshold for all three (T), and no invocation of the predecessor's conditional positive \(J_m\) conclusion. This is the stopping point required by the ordered test. fileciteturn63file0L45-L61

## 6. A distinct arithmetic mechanism: collapse the global-source prime action

The following calculation concerns the actual source derivative inside the prime correlations. It does not choose a new seed, alter the carrier, or make a positivity assumption.

### 6.1. The logarithmic source series

**[COFINAL_FAMILY | PAPER]** Write the fixed source as requested:
\[
h_*(x)=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},
\qquad G(u)=e^{u/2}\sum_{r\ge1}h_*(re^u).
\]
Define the exact differentiated source function
\[
h_2=(x\partial_x+\tfrac12)^2h_*.
\]
In terms of \(v=\pi x^2\), it is
\[
h_2(x)=(-64v^4+448v^3-660v^2+150v)e^{-v},
\qquad
g(u)=e^{u/2}\sum_{r\ge1}h_2(re^u).
\tag{20}
\]
This is the same derivative polynomial appearing in the pinned source, with its original sign. It is not a Gaussian trial substituted for \(G\). The given \(G=\mathcal E h_*\) is global; its evenness is unchanged. fileciteturn63file0L29-L34 fileciteturn67file0L2-L2

For each fixed real \(u\), Gaussian decay in the source's summation index makes the following rearrangement absolutely convergent:
\[
\begin{aligned}
\sum_{\nu\ge2}\frac{\Lambda(\nu)}{\sqrt\nu}g(u+\log\nu)
&=e^{u/2}\sum_{\nu\ge2}\sum_{r\ge1}
\Lambda(\nu)h_2(r\nu e^u)\\
&=e^{u/2}\sum_{k\ge1}
\left(\sum_{\substack{\nu\mid k\\\nu\ge2}}\Lambda(\nu)\right)h_2(ke^u).
\end{aligned}
\]
Prime factorization gives \(\sum_{\nu\mid k}\Lambda(\nu)=\log k\): each factor \(p^a\) contributes \(a\log p\). Thus
\[
\boxed{
Z_g(u):=\sum_{\nu\ge2}\frac{\Lambda(\nu)}{\sqrt\nu}g(u+\log\nu)
=e^{u/2}\sum_{k\ge1}(\log k)h_2(ke^u).
}
\tag{21}
\]
The prime-power definition is essential to this collapse. For \(k=p^2\), both \(p\) and \(p^2\) must contribute; a primes-only replacement already fails this exact check. citeturn207815view0

### 6.2. Collapse all source-containing pieces, not the finite-window term

**[FINITE_CELL | PAPER]** For real even \(a,b\), denote the complete arithmetic pairing by
\[
\mathscr P[a,b]=\sum_{\nu\ge2}\frac{\Lambda(\nu)}{\sqrt\nu}
\int a(u)[b(u+\log\nu)+b(u-\log\nu)]du.
\]
For \(a=h_m\) or \(a=g\), evenness and (21) give
\[
\mathscr P[h_m,g]=2\int_{-b}^{b}h_m(u)Z_g(u)du,
\qquad
\mathscr P[g,g]=2\int_{\mathbb R}g(u)Z_g(u)du.
\]
The \(h_m,h_m\) pairing has exactly zero correlation beyond \(L\), because both functions are window-supported. Consequently
\[
\boxed{
\begin{aligned}
\mathscr P_m^{\rm all}
:=\mathscr P_m^{\le}+\mathscr P_m^{>}
={}&\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}Q_m(\log\nu)\\
&-4\int_{-b}^{b}h_m(u)Z_g(u)du
+2\int_{\mathbb R}g(u)Z_g(u)du.
\end{aligned}}
\tag{22}
\]
This is an exact formula for the complete prime pairing of \(f_m=h_m-g\), including every returned prime power. Only the compact \(h_m,h_m\) part has a finite arithmetic range. The two terms containing \(Z_g\) must not be truncated at \(m\).

Here are the convergence boundaries. For any two of \(h_m,g,f_m\), put \(A_1(a)=\|e^{|u|}a\|_2<\infty\). The inequality \(|u|+|u+t|\ge t\) gives
\[
\left|\int a(u)b(u+t)du\right|\le e^{-t}A_1(a)A_1(b).
\]
It follows that the prime sum can be interchanged with these integrated pairings, since \(\sum_{\nu\ge2}(\log\nu)\nu^{-3/2}<\infty\). The pointwise source rearrangement in (21) is justified separately.

**No claim is made that the individual log-weighted source summands in (21) may be integrated absolutely over the whole real line.** Keep \(Z_g\) grouped in (22). In particular, it is not declared an unweighted \(L^2\) function. This prevents a new domain error from replacing the old correlation estimate.

### 6.3. One next falsifiable PAPER test

**`TEST_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION`**

**[COFINAL_FAMILY | CONDITIONAL]** Test whether the entire grouped source expression (22) is genuinely lower order than the proposed logarithmic principal scale. A concrete certificate to attempt is: derive a finite constant \(C_{\rm div}\), independent of \(m\), and a proved selected threshold \(m_{\rm div}\), such that
\[
\boxed{
|\mathscr P_m^{\rm all}|
\le C_{\rm div}(1+\log\log m)E_{11}(m)
\quad\text{for every selected }m\ge m_{\rm div}.
}
\tag{23}
\]
The proof must use the cancellation between the three source terms in (22), with the exact log-weighted series (21). Separate bounds of their original, much larger scales do not certify (23). A constant defined from their unknown ratio is not a delivery.

This is **not (T) under another name**: it contains no digamma multiplier, no pole term, no \(A\), and no comparison of the two error columns. It tests the independent mechanism “the complete arithmetic correlation is lower order,” which could be false even when its joint cancellation with the archimedean term makes (T) true.

A concrete way to falsify this lower-order mechanism is a source-derived \(c>0\) and a proved unbounded selected set with
\[
|\mathscr P_m^{\rm all}|\ge c\,\ell_m E_{11}(m).
\tag{24}
\]
Such a result would exclude every finite \(C_{\rm div}\) in (23), since \(\ell_m/(1+\log\log m)\to\infty\). It would require retaining a leading arithmetic contribution in the joint test (17). **It would not by itself refute (T)**: the multiplier deviation might compensate it.

Neither (23) nor (24) is established in this verdict. A successful saving (23) would still require the independent integrated symbol estimate, and then compatible estimates for \(N_{00},N_{01}\), before any transfer pass. The nonnegative logarithmic-moment bound (19) is one possible separate interface for that symbol estimate, not an already paid supplier.

## 7. Adversarial audit, route map, and closeout

**[ABSTRACT | PAPER]** The strongest objection to the new relative tail bounds is that the exterior energy may be much smaller than total error energy. That is harmless: (11) and (13) first use the actual \(E_O\), then only the valid inequality \(E_O\le E\). They do not require a lower bound for the exterior fraction. The interior pole estimate uses orthogonality only on its actual window, not a false global band-limitation.

**[FINITE_CELL | PAPER]** The remaining boundary checks are explicit. The source tail estimate covers \(t=L\) without declaring the full correlation zero there. The \(\nu=m\) term remains in (17). The \(\nu>m\) terms remain in (14) and (22). The Q5 constant remains in every \(e_n\). The archimedean endpoint subtraction remains in \(\mathfrak a\), while the jump-induced continuous-frequency tail remains in (7) and (19). The finite kernel's diagonal remains the first line of (5). The exact zero of the compact correlation at \(t=L\) is not transferred to the noncompact error.

**[COFINAL_FAMILY | PAPER]** Prediction scoring: the announced test was whether the exterior decay and projection orthogonality could make the pole and returned-prime range small relative to \(\ell_mE_{11}\). Equations (12)–(16) confirm that prediction, with a proved threshold. No sign for the finite-prime correlation, no integrated multiplier bound, and no transfer pass or kill was predicted as obtained. The divisor collapse is an additional exact source calculation, not a retrospectively scored prediction of arithmetic smallness.

| Candidate representation | Decisive power / scope | PAPER cost and principal risk |
|---|---|---|
| **Chosen: complete arithmetic pairing after the divisor collapse (20)–(24).** | Can establish a lower-order arithmetic supplier or exclude the entire lower-order-arithmetic mechanism on an unbounded selected set. Neither outcome alone decides (T). | One finite-prime quadratic term and two explicit grouped source integrals. Their cancellation, rather than prime-tail convergence, is load-bearing. |
| **Alternative: actual continuous-frequency logarithmic moment (7), (19).** | Can quantify the integrated symbol error without a pointwise substitution. It cannot estimate the arithmetic correlation. | One positive frequency-weighted source integral, with removable sampling points and both continuous-frequency tails. Finiteness alone is insufficient. |

Only the first next test is commissioned. No numerical evaluation, larger carrier, or analytic cutoff search is commissioned.

**What became smaller:** for the first diagonal, two entire source contributions now have explicit relative envelopes; the remaining arithmetic source action also has an exact divisor-collapsed formula. **What did not close:** the joint comparison (17), any of the three requested (T) bounds, a strict reverse on an unbounded selected set, or the actual \(J_m\) sign. No source theorem shape was killed.

The structural checks are distinct: the bridge is source exterior localization plus exact projection orthogonality; the arithmetic generating identity is the complete divisor collapse; the next falsifier tests whether the arithmetic contribution is genuinely lower order, rather than renaming the full transfer. The source \(x\), its MIX terms, and the later activity problem are not modified by eliminating them from this compression-only test.

```yaml
DOWNSTREAM_CONSUMER: eventual_positive_necessary_J_m_test_then_separate_rank_one_and_axis_obligations
ACTUAL_CONSUMER_REQUIREMENT: source_information_sufficient_for_the_needed_compression_not_necessarily_quarter_scale_transfer
ORIGINAL_REQUESTED_OBJECT: three_compatible_quarter_scale_log_symbol_transfer_bounds_T
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_certificate_not_proved_necessary_for_J_positive_or_the_actual_plane_axis
KNOWN_WEAKER_INTERFACES:
  - direct_joint_source_determinant_to_trace_bounds_can_decide_J_without_T
  - different_paid_entrywise_relative_constants_can_suffice_for_the_necessary_J_test
  - a_direct_actual_projective_sector_can_bypass_the_rank_one_package
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_CORRELATION: equation_17_with_complete_source_equations_2_and_5_to_7
MINIMAL_MISSING_ESTIMATE: one_sided_joint_integrated_multiplier_and_finite_prime_bounds_at_the_E11_scale
NEW_CLOSED_QUANTIFIER: every_selected_m_GE_65536_has_the_pole_plus_returned_prime_remainder_below_ell_E11_div_16
NEW_EXACT_SOURCE_IDENTITY: complete_prime_action_on_G_second_derivative_equals_grouped_log_weighted_source_series
TRANSFER_CERTIFICATE_DEAD: false
SPECTRAL_OBSTRUCTION: NOT_ESTABLISHED
RANK_ONE_PACKAGE_DEAD: false
WHOLE_CONE_CERTIFICATE_DEAD: false
ACTUAL_FIXED_MIXTURE_KILLED: false
DISCRIMINATOR: TEST_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION
REOPEN_TRIGGER: source_relative_joint_envelopes_for_17_or_a_strict_reverse_T_inequality_on_an_unbounded_selected_set
NOVELTY_AXIS: relative_pole_and_returned_prime_envelopes_plus_exact_arithmetic_divisor_collapse
MEMORY_ENTRY:
  target: selected_source_log_symbol_transfer
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: the_returned_prime_tail_is_paid_relatively_but_the_retained_prime_correlation_and_symbol_deviation_must_still_be_compared_jointly
  forbidden_future_move: extrapolate_exterior_shift_decay_to_t_less_than_log_m_or_infer_T_from_a_small_pole_and_returned_tail
  next_decisive_test: TEST_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_DIVISOR_COLLAPSED_PRIME_CORRELATION`, on paper, for the unchanged derivative error \(T_mG''-G''\).** Use the exact source \(h_2\), the complete divisor identity (21), and the grouped arithmetic expression (22). Attempt the explicit lower-order bound (23) with a source-derived finite constant and a proved selected threshold, or a source witness (24) excluding that lower-order mechanism. Keep all three terms jointly, including the literal finite-prime diagonal, the full Q5/Q6 edge, both physical tails, and every prime power encoded in the log-weighted source series. Do not interchange its summation with a whole-line integral without a separate justification. A saving is an arithmetic supplier only; a failure is not a transfer kill, a spectral obstruction, or a rank-one-package kill. Preserve the separate unpaid integrated symbol estimate and both remaining entries of (T). No new seed, source replacement, arbitrary selected vector, numerical diagnostics, mathematical runtime, Lean, repository write, cutoff escalation, first-tau-sign, Schur-floor, route promotion, or RH claim is authorized.
