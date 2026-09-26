# STATUS: TRY_GOAL058_SOURCE_SAME_SIDE_DILATION_HEAD

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_SAME_SIDE_DILATION_HEAD
OUTCOME: OPEN_DIVISOR_CORRELATION
REQUEST_ID: REQ-2026-09-26-DIVISOR-COLLAPSED-PRIME-CORRELATION
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_DIVISOR_COLLAPSED_PRIME_CORRELATION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: a0e13520bd902cbdd1a9c0a7728176e1c34d241b
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-LOG-SYMBOL-TRANSFER
REQUEST_SHA256_VERIFIED: c956f984464e53cad6d9f91013a2db3f3913029e51b1ffc9c0d34079586350ee
PREDECESSOR_VERDICT_SHA256_VERIFIED: 3e5e27a0b903abcb66e1f5beb027c23d25b0b92710674bf056769932c508d444
PREDECESSOR_GIT_BLOB_VERIFIED: 67dac465f2dffca8e1c0404cbfade8f575328ac1
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DIVISOR_CORRELATION_SAVED: NOT_ESTABLISHED
DIVISOR_CORRELATION_KILLED: NOT_ESTABLISHED
FULL_ARITHMETIC_RELATIVE_BOUND: OPEN
WHOLE_LINE_SOURCE_SERIES_INTERCHANGE: JUSTIFIED_FOR_THE_SPECIFIED_PAIRINGS_BELOW
GLOBAL_SOURCE_CONTRACTION: ABSOLUTELY_CONVERGENT_RECIPROCAL_DIVISOR_SERIES
UNWEIGHTED_Z_G_IN_L2: FALSE_FOR_THE_ACTUAL_SOURCE
SAME_SIDE_PRIME_RANGE_ABOVE_SQRT_M: EXPLICIT_RELATIVE_ENVELOPE_TENDING_TO_ZERO_FOR_m_GE_16
SAME_SIDE_HEAD_AT_OR_BELOW_SQRT_M: OPEN
OPPOSITE_SIDE_CORRELATION: OPEN
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: SOURCE_INTERCHANGE_AND_ONE_RELATIVE_CORRELATION_SUBRANGE_NOT_FULL_ARITHMETIC_SAVING
CLOSED_REQUESTED_SAVING_OR_KILL_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_SAME_SIDE_DILATION_HEAD
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
NEW_SEED_SELECTED: false
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
N00_AND_N01: OPEN_SEPARATE
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

Ы. **OPEN_DIVISOR_CORRELATION.** I have not proved a finite source-derived \(C_{\rm div}\) and an eventual threshold for the requested lower-order bound. I have not proved a leading arithmetic contribution on an unbounded selected-index set either. **The lower-order-arithmetic mechanism remains unproved, not refuted.**

There are two new source calculations. First, the whole-line source contraction can be expanded absolutely after using the source's exact reflection symmetry; it becomes an explicit divisor-weighted multiplicative-convolution series. This is a convergence and representation result, not a relative saving. The same calculation also gives a precise warning: **the actual \(Z_g\) is not an unweighted \(L^2(\mathbb R)\) function**.

Second, split the actual error correlation according to whether its two arguments lie on the same or opposite physical half-lines. For the **same-side part**, every prime power above \(\sqrt m\) has a source-derived bound
\[
\boxed{\left|\mathscr S_m^{>\sqrt m}\right|
\le \mathfrak r_{\rm side}(m)E_{11}(m),\qquad
\mathfrak r_{\rm side}(m)\longrightarrow0.}
\]
The explicit function is in (18). This does **not** bound the opposite-side part or the same-side head. The single next test isolates that head; it is not another request for the full three-term cancellation under a new symbol.

## 1. Source lock and the first unpaid cancellation

**[COFINAL_FAMILY | PAPER]** All **4,486 bytes** of the authoritative TXT and all **29,884 bytes** of the local predecessor were read. The predecessor's SHA-256 equals the requested hash; its locally calculated Git blob equals the blob returned at the pinned commit. The bootstrap was fetched from `rh_clean` and read in full. The authoritative request admits the earlier relative pole/returned-prime estimates and divisor identities, but not an arithmetic saving or the transfer. fileciteturn68file0L21-L27 fileciteturn71file0L3-L5

Keep one fixed \(P\) and
\[
m=J_P+j+2,\quad L=\log m,\quad b=L/2,\quad
\omega_n=2\pi n/L,\quad \ell_m=\log\frac{m+1}{L}.
\]
The original \(5m\) splice and Fourier carrier \(-m,\ldots,m\) are unchanged. Write
\[
g=G'',\qquad h=T_mg,\qquad f=h-g,\qquad E=E_{11}=\|f\|_2^2>0.
\]
These are exactly the request's functions, not replacement trials. fileciteturn68file0L29-L35

### 1.1. Retain the actual Fourier coefficients and the literal diagonal

**[FINITE_CELL | PAPER]** Use
\[
\begin{aligned}
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u),\\
e_n&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}g(u)e^{-i\omega_nu}\,du
=-\omega_n^2b_n+\epsilon_m,\\
\epsilon_m&=\frac{2G'(b)}{\sqrt L},\qquad
h=\sum_{n=-m}^{m}e_n\psi_{n,L}.
\end{aligned}
\tag{1}
\]
The source coefficients are real and even in \(n\); complex conjugation is nevertheless retained where an inner product is used. The Q5/Q6 constant in (1) is not set to zero. The predecessor records precisely these coefficients and their boundary convention. fileciteturn72file0L2-L2

For \(0\le t\le L\), the complete compact self-correlation is
\[
\begin{aligned}
Q_m(t)={}&2\left(1-\frac tL\right)
\sum_{n=-m}^{m}e_n^2\cos(\omega_nt)\\
&+2\sum_{-m\le n<q\le m}e_ne_q
\frac{\sin(\omega_qt)-\sin(\omega_nt)}{\pi(n-q)}.
\end{aligned}
\tag{2}
\]
For \(t>L\), \(Q_m(t)=0\). The first line of (2) is its separate diagonal; it is not obtained by assigning a divided-difference limit to the second line. This is the inherited finite-source kernel, not a newly chosen correlation. fileciteturn72file0L2-L2

Define the finite incomplete Mellin moment of the **actual source polynomial**
\[
\mathcal H_2(s;a,c)=\int_a^c h_2(x)x^{s-1}\,dx,
\qquad s_n=\tfrac12-i\omega_n,
\]
and the exact log-source window coefficients
\[
\boxed{
z_n=\frac{(-1)^n}{\sqrt L}
\sum_{k=1}^{\infty}(\log k)k^{-s_n}
\mathcal H_2\left(s_n;\frac{k}{\sqrt m},k\sqrt m\right).
}
\tag{3}
\]
Thus \(z_n=\langle\psi_{n,L},Z_g\rangle_{[-b,b]}\). The justification for passing this series through the integral is supplied in §2, not assumed. Both lower and upper physical limits occur in (3).

Let
\[
\mathcal C_g=2\int_{\mathbb R}g(u)Z_g(u)\,du.
\]
Then the first unpaid source cancellation in the requested identity (D) is explicitly
\[
\boxed{
\begin{aligned}
\mathscr P_m^{\rm all}={}&
\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\left\{2\left(1-\frac{\log\nu}{L}\right)
\sum_{n=-m}^{m}e_n^2\cos(\omega_n\log\nu)\right.\\[-2pt]
&\left.\hspace{19mm}
+2\sum_{-m\le n<q\le m}e_ne_q
\frac{\sin(\omega_q\log\nu)-\sin(\omega_n\log\nu)}{\pi(n-q)}\right\}\\
&-4\operatorname{Re}\sum_{n=-m}^{m}\overline{e_n}z_n+\mathcal C_g.
\end{aligned}}
\tag{4}
\]
Here \(e_n\) is (1), \(z_n\) is the complete \(k\ge1\) sum (3), and \(\mathcal C_g\) includes both full physical half-lines. The three terms, including their factors and signs, are those in the authoritative (D). Only the compact self term has a prime range ending at \(m\). fileciteturn68file0L37-L60

**[COFINAL_FAMILY | PAPER]** No upper envelope for the absolute value of the **joint** expression (4), at \((1+\log\log m)E(m)\) scale, has been established. No lower envelope for its absolute value at \(\ell_mE(m)\) scale on an unbounded selected set has been established. Those are the two requested, different family conclusions; neither follows from knowing (4) exactly. fileciteturn68file0L62-L75

## 2. Source-series interchanges that can actually be justified

### 2.1. Compact window: absolute domination for every selected cell

**[FINITE_CELL | PAPER]** Put
\[
h_2(x)=\sum_{a=1}^{4}c_a(\pi x^2)^a e^{-\pi x^2},
\qquad(c_1,c_2,c_3,c_4)=(150,-660,448,-64).
\tag{5}
\]
These are the fixed coefficients in the request. Their absolute sum is \(1322\). On \(-b\le u\le b\), \(k\ge1\),
\[
e^{u/2}|h_2(ke^u)|
\le1322\pi^4m^{17/4}k^8e^{-\pi k^2/m}.
\tag{6}
\]
Indeed, \(k/\sqrt m\le ke^u\le k\sqrt m\); use the lower endpoint in the Gaussian exponential and the upper endpoint in each of the four powers. Multiplication by \(\log k\) leaves a summable majorant for each fixed \(m\).

Since \(h\) is a finite Fourier sum on this compact interval, (6) justifies termwise integration of \(hZ_g\), and also gives (3) after \(x=ke^u\). It does not give a uniform *relative* bound for (4): its purpose is to justify the representation with all terms retained.

### 2.2. Whole line: use the reciprocal source, not two forward expansions

**[ABSTRACT | PAPER]** The source is exactly even, so
\[
g(u)=e^{-u/2}\sum_{r=1}^{\infty}h_2(re^{-u}).
\]
Combining this expression with the divisor-collapsed expression for \(Z_g\) gives a reciprocal product. Define
\[
\mathcal B_2(v)=\int_0^\infty h_2(x)h_2(v/x)\,\frac{dx}{x},
\qquad v>0.
\tag{7}
\]
If the product series is absolutely integrable, the change of variable \(x=ke^u\) gives
\[
\int_{\mathbb R}g(u)Z_g(u)du
=\sum_{r,k\ge1}(\log k)\mathcal B_2(rk).
\]
The needed absolute integrability follows from the explicit bound below.

Writing \(K^{\rm Bes}_a\) for the modified Bessel function, to distinguish it from the CCM matrix, direct substitution \(x^2=vz\) in (7) yields
\[
\boxed{
\mathcal B_2(v)=
\sum_{a,b=1}^{4}c_ac_b(\pi v)^{a+b}
K^{\rm Bes}_{a-b}(2\pi v).
}
\tag{8}
\]
The only external special-function formula used here is the real integral representation
\(K^{\rm Bes}_q(z)=\int_0^\infty e^{-z\cosh t}\cosh(qt)dt\), for real \(z>0\). Its equivalent two-sided form gives exactly (8). No Bessel asymptotic is imported as a source bound. citeturn924768view0

For \(v\ge1\), \(|a-b|\le3\), use \(\cosh t\ge1+t^2/2\) and \(\cosh(qt)\le e^{|q|t}\). Completing the square in the remaining Gaussian integral gives
\[
K^{\rm Bes}_{a-b}(2\pi v)
\le v^{-1/2}\exp\left(-2\pi v+\frac9{4\pi v}\right).
\]
Consequently the same calculation with absolute polynomial coefficients proves
\[
\boxed{
\int_0^\infty|h_2(x)h_2(v/x)|\frac{dx}{x}
\le C_B v^{15/2}e^{-2\pi v},\qquad
C_B=1322^2\pi^8e^{9/(4\pi)}.
}
\tag{9}
\]
In particular,
\[
\sum_{r,k\ge1}(\log k)
\int_0^\infty|h_2(x)h_2(rk/x)|\frac{dx}{x}<\infty.
\]
For example, group by \(v=rk\), use \(d(v)\le v\) and \(\log v\le v\), and compare with the convergent series \(\sum v^{19/2}e^{-2\pi v}\). This is a Tonelli/Fubini justification for the reciprocal expansion of the whole-line contraction.

The divisor pairing \(k\leftrightarrow v/k\) gives
\(\sum_{k\mid v}\log k=\tfrac12d(v)\log v\), where \(d(v)\) is the number of positive divisors. Therefore
\[
\boxed{
\mathcal C_g=
\sum_{v=2}^{\infty}d(v)(\log v)\mathcal B_2(v),
}
\tag{10}
\]
with absolute convergence proved by (9). Equation (10) is the exact last term of (4), not a replacement constant fitted to that cancellation. No sign is assigned to \(\mathcal B_2(v)\): the coefficients in (8) have both signs.

This use of evenness is consequential. It changes the Gaussian product to one involving \(x\) and \(v/x\), whose absolute bound decays in their product index. No claim is made that expanding both factors in the forward variable permits the same whole-line interchange.

### 2.3. An exact reason not to use an unweighted norm of \(Z_g\)

**[ABSTRACT | PAPER]** Let \(q(x)=(\log x)h_2(x)\), with \(q(0)=0\), and let
\[
V_q=\int_0^\infty|q'(x)|dx<\infty.
\]
This is a fixed explicit source integral: near zero \(q'(x)=O(x\log x)\), and at infinity it is a polynomial-logarithm times a Gaussian.

For \(\operatorname{Re}s>0\), the Mellin integral of the displayed source polynomial is
\[
\int_0^\infty h_2(x)x^{s-1}dx
=2s(1-s)(s-\tfrac12)^2\pi^{-s/2}\Gamma(s/2).
\]
This follows either by four Gaussian integrals or by twice integrating \(x\partial_x+1/2\) by parts. Differentiating at \(s=1\) is justified by the same integrable source majorants and gives
\[
\int_0^\infty q(x)dx=-\tfrac12.
\]
For every \(x>0\), the elementary interval-by-interval Riemann-sum estimate is
\[
\left|\sum_{k\ge1}q(kx)-x^{-1}\int_0^\infty q(y)dy\right|\le V_q.
\]
Apply it with \(x=e^u\), and use \(\log k=\log(ke^u)-u\). This proves the exact decomposition and uniform error bound
\[
\boxed{
Z_g(u)=-\tfrac12e^{-u/2}-u\,g(u)+\rho(u),
\qquad |\rho(u)|\le V_qe^{u/2},\quad u\in\mathbb R.
}
\tag{11}
\]
By the source's even, rapidly decreasing \(g\),
\[
\lim_{u\to-\infty}e^{u/2}Z_g(u)=-\tfrac12.
\]
Thus **\(Z_g\notin L^2(\mathbb R)\)**. This refutes an unweighted-\(L^2\) interface for this actual source, not the requested lower-order mechanism. The predecessor did not assume that interface: it explicitly kept the whole-line source grouped. Equations (7)–(10) justify the required pairing without introducing it. fileciteturn71file0L2-L2

## 3. Why the requested relative comparison remains unpaid

**[COFINAL_FAMILY | PAPER]** The source now permits the fully indexed expression (4), with (3) and (10), and justified integration of its source series. But these formulas give neither a lower bound nor a relative upper bound for the cancellation between its compact self term, mixed log-source term, and global source term.

The distinction is not cosmetic. An absolute majorant for (3) or (10) is not coupled to the error denominator \(E(m)\); no proved comparison here turns it into a finite uniform \(C_{\rm div}\). The source polar term (11) also rules out the tempting estimate using \(\|Z_g\|_2\). Weighted convergence of a pairing does not supply the missing ratio.

The elementary correlation estimate illustrates the current loss. It gives
\[
|\Gamma_m(t)|\le2E,
\qquad
\left|\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\Gamma_m(\log\nu)\right|
\le4\sqrt m(\log m)E.
\tag{12}
\]
Here only \(\Lambda(\nu)\le\log\nu\) and \(\sum_{\nu\le m}\nu^{-1/2}\le2\sqrt m\) were used. This upper bound is far larger than the requested scale, and it gives no lower bound because the correlations are signed. Its inadequacy is not a counterexample.

The predecessor already pays the complete range \(\nu>m\) relatively. That bound cannot be extrapolated into \(2\le\nu\le m\); its proof uses a shift at least as long as the full window. The authoritative request expressly keeps this remaining cancellation open. fileciteturn68file0L21-L27 fileciteturn68file0L56-L60

The integrated archimedean deviation, the pole term, and \(N_{00},N_{01}\) are not part of the arithmetic estimate asserted here. No sign of the total transfer or of \(J_m\) is inferred from any component in this verdict. fileciteturn68file0L78-L84

## 4. A narrower source split: same-side dilation versus opposite-side product

### 4.1. Exact split of the actual error, with both half-lines included

**[FINITE_CELL | PAPER]** For \(t\ge0\), real even \(f\) satisfies
\[
\Gamma_m(t)=
4\int_0^\infty f(u)f(u+t)du
+2\int_0^t f(u)f(t-u)du.
\tag{13}
\]
To check the factors, partition \(\int_{\mathbb R}f(u)f(u+t)du\) into \(u\ge0\), \(u\le-t\), and \(-t<u<0\). The first two pieces coincide by reflection; the middle crossing interval gives the second integral in (13). Then use \(\Gamma_m=2\int f(u)f(u+t)du\).

Accordingly define
\[
\begin{aligned}
\mathscr S_m&=4\sum_{\nu\ge2}\frac{\Lambda(\nu)}{\sqrt\nu}
\int_0^\infty f(u)f(u+\log\nu)du,\\
\mathscr H_m&=2\sum_{\nu\ge2}\frac{\Lambda(\nu)}{\sqrt\nu}
\int_0^{\log\nu}f(u)f(\log\nu-u)du.
\end{aligned}
\]
Then
\[
\boxed{\mathscr P_m^{\rm all}=\mathscr S_m+\mathscr H_m.}
\tag{14}
\]
Both sums converge absolutely for each selected cell: with \(A_1(f)=\|e^{|u|}f\|_2<\infty\), the absolute integral of any of the partitioned pieces is bounded by \(e^{-t}A_1(f)^2\). The resulting prime majorant is \(\sum_{\nu\ge2}(\log\nu)\nu^{-3/2}<\infty\). The factors in (13), not an omitted half-line, account for the reflection.

To expose the source domains, put \(Q=\sqrt m=e^b\) and, for \(x\ge1\), define
\[
\begin{aligned}
F_+(x)&=\sum_{r\ge1}h_2(rx),\\
H_{m,+}(x)&=\frac{\mathbf1_{[1,Q]}(x)}{\sqrt L}
\sum_{n=-m}^{m}e_n(-1)^n x^{-1/2+i\omega_n},\\
\varphi_m(x)&=H_{m,+}(x)-F_+(x)=x^{-1/2}f(\log x).
\end{aligned}
\tag{15}
\]
These are exact restrictions and changes of variable of the original source. In particular, for \(x>Q\), \(\varphi_m(x)=-F_+(x)\), not zero.

The two components now have distinct multiplicative geometries:
\[
\boxed{
\begin{aligned}
\mathscr S_m&=4\sum_{\nu\ge2}\Lambda(\nu)
\int_1^\infty\varphi_m(x)\varphi_m(\nu x)dx,\\
\mathscr H_m&=2\sum_{\nu\ge2}\Lambda(\nu)
\int_1^\nu\varphi_m(x)\varphi_m(\nu/x)\frac{dx}{x}.
\end{aligned}}
\tag{16}
\]
The \(\sqrt\nu\) factors have canceled with the change of variables; they have not been dropped. The first expression pairs a point with its dilation, while the second pairs two points with fixed product. Only the compact \(H_{m,+}H_{m,+}\) piece of the first can occur for \(\nu<Q\); the compact piece of the second can occur up to \(\nu<m\). All the noncompact error terms remain in both expressions.

### 4.2. All same-side prime powers above \(\sqrt m\) are paid relatively

**[COFINAL_FAMILY | PAPER]** Use the admitted source exterior estimate, for \(m\ge16\),
\[
-g(t)>0,\qquad |g(t+s)|\le e^{-\pi m s}|g(t)|
\quad(t\ge b,\ s\ge0).
\tag{17}
\]
This is the source estimate used in predecessor (10)–(14), not a new assumption on \(f\) inside the window. The request accepts that relative-tail proof. fileciteturn68file0L21-L25

Let \(E_O=2\int_b^\infty|g(u)|^2du\le E\). For \(t\ge b\), the second argument of the same-side integral is always exterior, so \(f(u+t)=-g(u+t)\). Therefore
\[
\begin{aligned}
\left|\int_0^\infty f(u)f(u+t)du\right|
&\le \sqrt{E/2}\left(\int_t^\infty|g(v)|^2dv\right)^{1/2}\\
&\le\tfrac12\sqrt{EE_O}\,e^{-\pi m(t-b)}
\le\tfrac12 E e^{-\pi m(t-b)}.
\end{aligned}
\]
This includes \(t=b\); it does not assert vanishing there.

Set \(c=\pi m\). For all integer prime powers \(\nu>Q\), not just primes,
\[
\left|\mathscr S_m^{>Q}\right|
\le2E\sum_{\nu>Q}\frac{\log\nu}{\sqrt\nu}
(\nu/Q)^{-c}.
\]
The summand, continued as a real function, decreases on \([Q,\infty)\). Because \(Q\) need not be an integer, retain a first-term allowance as well as the integral. Evaluation gives
\[
\boxed{
\begin{aligned}
\left|\mathscr S_m^{>Q}\right|&\le\mathfrak r_{\rm side}(m)E,\\
\mathfrak r_{\rm side}(m)
&=\frac{L}{m^{1/4}}
+\frac{m^{1/4}L}{\pi m-1/2}
+\frac{2m^{1/4}}{(\pi m-1/2)^2},\qquad m\ge16.
\end{aligned}}
\tag{18}
\]
For example, the integral used here is
\[
Q^c\int_Q^\infty(\log x)x^{-c-1/2}dx
=Q^{1/2}\left[\frac{\log Q}{c-1/2}+\frac1{(c-1/2)^2}\right].
\]
All constants in (18) are independent of the unknown correlation and its sign. Also
\[
\boxed{\mathfrak r_{\rm side}(m)\le2Lm^{-1/4}\longrightarrow0.}
\tag{19}
\]
For this elementary simplification use \(\pi m-1/2\ge2m\), \(m^{1/2}\ge4\), and \(L\ge2\). In particular \(\mathfrak r_{\rm side}<4\), since \(L m^{-1/4}\le4/e<2\).

This is a relative estimate for an entire arithmetic subrange of the **same-side component**. It does not imply the analogous estimate for \(\mathscr H_m^{>Q}\): in the product geometry, two interior points can still be separated across the origin when \(Q<\nu<m\). That distinction prevents using (18) as a full-prime saving.

## 5. Exactly one narrower PAPER test

### TEST_SOURCE_SAME_SIDE_DILATION_HEAD

**[COFINAL_FAMILY | CONDITIONAL]** Test the one remaining same-side quantity
\[
\boxed{
\mathscr S_m^{\le Q}
=4\sum_{2\le\nu\le Q}\Lambda(\nu)
\int_1^\infty\varphi_m(x)\varphi_m(\nu x)dx,
\qquad Q=\sqrt m,
}
\tag{20}
\]
with \(\varphi_m\) exactly (15). The proposed saving to adjudicate is a finite source-derived \(C_{\rm side}\) and selected threshold for
\[
|\mathscr S_m^{\le Q}|
\le C_{\rm side}(1+\log\log m)E(m).
\tag{21}
\]
A falsifying alternative for this **component-saving mechanism** is a proved \(c_{\rm side}>0\) and an unbounded selected set with
\[
|\mathscr S_m^{\le Q}|\ge c_{\rm side}\ell_m E(m).
\tag{22}
\]
Neither (21) nor (22) is asserted in this verdict.

If (21) is paid, (18) pays the whole same-side contribution, with the explicit enlarged constant \(C_{\rm side}+4\) for \(m\ge16\). The opposite-side product correlation \(\mathscr H_m\) remains a distinct unpaid term. If (22) is paid, the same-side contribution itself must be retained at leading scale; the full lower-order mechanism could still survive by cancellation with \(\mathscr H_m\). Thus (22) is **not** a `DIVISOR_CORRELATION_KILLED` certificate.

This is narrower than the present request: it excludes the entire opposite-side product integral from its target, and its self-interaction involves only \(\nu\le\sqrt m\), a boundary forced by support. It does not enlarge the carrier, introduce a seed, or ask for a cutoff search. The exact complete identity (14) remains in force.

### Source formula to use, with all four head terms retained

**[FINITE_CELL | PAPER]** Expanding only the actual difference in (15), the head is
\[
\boxed{
\begin{aligned}
\tfrac14\mathscr S_m^{\le Q}
=\sum_{2\le\nu\le Q}\Lambda(\nu)\Bigg[
&\int_1^{Q/\nu}H_{m,+}(x)H_{m,+}(\nu x)dx\\
&-\int_1^{Q}H_{m,+}(x)F_+(\nu x)dx\\
&-\int_1^{Q/\nu}F_+(x)H_{m,+}(\nu x)dx\\
&+\int_1^\infty F_+(x)F_+(\nu x)dx\Bigg].
\end{aligned}}
\tag{23}
\]
The two mixed integrals are not identified: their domains differ. At \(\nu=Q\), when \(Q\) is an integer, the integrals with upper limit \(Q/\nu\) vanish by zero interval length, while the other terms are retained.

For an explicit finite-index check, define
\[
\mathcal J(\eta,a)=\int_0^a e^{i\eta u}du
=\begin{cases}(e^{i\eta a}-1)/(i\eta),&\eta\ne0,\\a,&\eta=0.\end{cases}
\]
The first term in the head, including its factor four, is exactly
\[
\frac4L\operatorname{Re}
\sum_{2\le\nu\le Q}\frac{\Lambda(\nu)}{\sqrt\nu}
\sum_{n,q=-m}^{m}\overline{e_n}e_q(-1)^{q-n}
 e^{i\omega_q\log\nu}
\mathcal J(\omega_q-\omega_n,b-\log\nu).
\tag{24}
\]
The case \(n=q\) is explicitly \(\mathcal J(0,b-\log\nu)=b-\log\nu\). No diagonal is lost, and every \(e_n\) still contains (1)'s Q5/Q6 constant.

The forward source dilation in the second term of (23) has the exact restricted divisor collapse
\[
\sum_{2\le\nu\le Q}\Lambda(\nu)F_+(\nu x)
=\sum_{k\ge1}L_Q(k)h_2(kx),
\quad
L_Q(k)=\sum_{\substack{\nu\mid k\\2\le\nu\le Q}}\Lambda(\nu).
\tag{25}
\]
Here \(0\le L_Q(k)\le\log k\), but **\(L_Q(k)\) is not replaced by \(\log k\)** unless all its contributing divisors are actually included. The other mixed term instead has a moving inverse-dilation domain. After \(y=\nu x\), its summed expression is
\[
\int_1^Q H_{m,+}(y)
\sum_{2\le\nu\le y}\frac{\Lambda(\nu)}{\nu}F_+(y/\nu)\,dy.
\tag{26}
\]
Equations (25) and (26) exhibit why the full divisor identity alone did not settle the projection cancellation. A forward dilation and an inverse dilation with a moving boundary are different source terms.

All source-series arguments in (23), (25), and (26) are at least one. The Gaussian polynomial (5) therefore supplies absolute convergence of their displayed series and integrations; the only finite Fourier indices are still \(-m\le n,q\le m\). A future estimate must keep the four-term cancellation, not bound the two mixed terms independently and call the result relative.

## 6. Adversarial checks, route map, and closeout

**[ABSTRACT | PAPER]** The strongest attack on the whole-line expansion is that the divisor source grows at one end. Equation (11) confirms that objection to an unweighted norm argument. It does not invalidate the pairing: the reciprocal majorant (9) proves its absolute integrability directly. These are different assertions, and both have been retained.

**[FINITE_CELL | PAPER]** The source convention checks are explicit. In (3), \(s_n=1/2-i\omega_n\) comes from the conjugated Fourier basis. The pair \(n,-n\) makes the required scalar real; it does not replace conjugation by a modulus. The four polynomial coefficients remain signed in (8). In (16), the dilation and fixed-product integrals carry different measures, \(dx\) and \(dx/x\). The integer boundary near \(\sqrt m\) has its first-term allowance in (18); the exact boundary term has not been discarded. Both physical half-lines appear through the exact partition (13).

**[COFINAL_FAMILY | PAPER]** The pre-check expectation for the reciprocal-variable expansion was absolute summability without a promised relative saving. Equations (7)–(10) confirm that expectation. The support check for the same-side projected overlap gives the boundary \(\sqrt m\); (18) supplies an additional quantitative exterior estimate. No prediction of a full arithmetic saving or a leading unbounded contribution was registered, and neither is retrospectively scored as achieved. The predecessor's accepted identities and tail bounds are inputs, not new results credited again.

| Candidate representation | Discriminating power | PAPER cost / main risk |
|---|---|---|
| **Chosen: same-side dilation head (20), with exact four-term source expansion (23).** | Decides whether this one component can be absorbed into a lower-order ledger; (18) already covers its entire complementary prime range. A leading head would force explicit cancellation with the opposite-side component. | Finite prime range forced by \(\sqrt m\), two actual mixed source terms, and rapidly convergent source series on \(x\ge1\). Still needs a relative estimate; no sign follows from positive arithmetic weights. |
| **Alternative: complete finite-Mellin/reciprocal-divisor representation (3), (4), (10).** | Could decide the original request directly if its three signed terms were jointly enclosed at the error-energy scale. | All source interchanges are now justified, but computing the global constant accurately does not control the cancellation with the two \(m\)-dependent terms. No numerical evaluation or second campaign is commissioned. |

**What closed:** justified whole-line source expansion; the exact non-\(L^2\) diagnosis for \(Z_g\); and a relative envelope for every same-side prime power above \(\sqrt m\), on every admitted selected cell with \(m\ge16\). **What did not close:** the saving or kill quantifier for the complete arithmetic correlation. The original three-term cancellation (4), equivalently the remaining joint same-side-head/opposite-side problem in (14), is still open.

The bridge used here is multiplicative convolution of the actual reflected source. The exact divisor identity is retained, including all prime powers. The attempted family-deciding information is still a relative source correlation, not mere normal convergence. A failed component estimate cannot be promoted to death of the full arithmetic mechanism, much less to death of the transfer or route.

```yaml
DOWNSTREAM_CONSUMER: one_arithmetic_supplier_for_the_N11_log_symbol_transfer
ACTUAL_CONSUMER_REQUIREMENT: joint_source_N11_control_with_symbol_deviation_and_pole_then_compatible_N00_N01_bounds
ORIGINAL_REQUESTED_OBJECT: lower_order_complete_arithmetic_correlation_bound
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_component_mechanism_not_proved_necessary_for_full_transfer_or_J_positive
KNOWN_WEAKER_INTERFACES:
  - joint_multiplier_minus_arithmetic_control_can_allow_a_leading_arithmetic_term
  - different_paid_relative_entry_constants_can_suffice_for_the_necessary_spectral_test
  - direct_source_compression_or_actual_direction_estimates_can_bypass_the_log_transfer
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_CANCELLATION: equation_4_with_exact_source_coefficients_1_moments_3_and_global_series_10
MINIMAL_MISSING_ESTIMATE: joint_relative_control_of_complete_arithmetic_correlation_at_the_actual_E11_scale
NEW_CLOSED_QUANTIFIER: every_selected_m_GE_16_has_the_same_side_prime_GT_sqrt_m_envelope_18
SOURCE_INTERFACE_REFUTED: unweighted_Z_g_membership_in_L2_R
SOURCE_INTERFACE_REFUTATION_SCOPE: THEOREM_SHAPE_ONLY_NOT_THE_ARITHMETIC_MECHANISM
SOURCE_INTERFACE_EVIDENCE: source_polar_limit_in_equation_11
DIVISOR_CORRELATION_MECHANISM_DEAD: false
TRANSFER_CERTIFICATE_DEAD: false
SPECTRAL_OBSTRUCTION: NOT_ESTABLISHED
RANK_ONE_PACKAGE_DEAD: false
ACTUAL_FIXED_MIXTURE_KILLED: false
DISCRIMINATOR: TEST_SOURCE_SAME_SIDE_DILATION_HEAD
REOPEN_TRIGGER: paid_full_three_term_relative_bound_or_full_leading_arithmetic_witness_with_requested_quantifiers
NOVELTY_AXIS: reciprocal_source_Tonelli_and_explicit_polar_term_plus_same_side_dilation_tail_at_sqrt_m
MEMORY_ENTRY:
  target: selected_divisor_collapsed_complete_prime_correlation
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: divisor_collapse_does_not_remove_the_moving_projection_boundaries_or_supply_relative_cancellation
  forbidden_future_move: use_unweighted_Z_g_L2_or_apply_the_same_side_sqrt_m_tail_bound_to_opposite_side_correlations
  next_decisive_test: TEST_SOURCE_SAME_SIDE_DILATION_HEAD
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_SAME_SIDE_DILATION_HEAD`, on paper, for the unchanged derivative error.** Adjudicate (21), or a component-leading witness (22), using the exact source expression (23)–(26) and the already paid complementary same-side range (18). Keep the original \(e_n\), Q5/Q6 edge, the literal diagonal in (24), both distinct mixed terms, and every prime power in its stated range. The boundary \(\sqrt m\) comes from support; it does not change the Fourier carrier or the source family. Do not substitute \(\log k\) for the restricted divisor weight \(L_Q(k)\), or delete the opposite-side term from the full identity (14). A saving here pays only the same-side component; a leading component requires subsequent joint cancellation analysis and is not a full divisor-correlation kill. No numerical cutoff search, mathematical runtime, Lean, repository write, new seed, source replacement, transfer pass, positive-J claim, compression-dominance claim, activity claim, axis-gap claim, first-tau-sign, Schur-floor, route promotion, or RH claim is authorized.
