# STATUS: TRY_GOAL058_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_HEAD

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_HEAD
OUTCOME: OPEN_SAME_SIDE_HEAD
REQUEST_ID: REQ-2026-09-26-SAME-SIDE-DILATION-HEAD
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SAME_SIDE_DILATION_HEAD
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: fa0bdcde32572eaddb4885153c6344fb605a5175
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-DIVISOR-COLLAPSED-PRIME-CORRELATION
REQUEST_SHA256_VERIFIED: 386241af0dcb7f2d2c74624e568c806656bcdb293553521c876bf1d13fdca640
PREDECESSOR_VERDICT_SHA256_VERIFIED: 2a02d6bc989b4a990f81ab5eff2d277897fd28657df5fff91e3df037a63292eb
PREDECESSOR_GIT_BLOB_VERIFIED: f5cf39fe68261effb0b18dee6f90ab0895a7039e
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SAME_SIDE_HEAD_SAVED: NOT_ESTABLISHED
SAME_SIDE_HEAD_LEADING: NOT_ESTABLISHED
LOW_CONTINUOUS_FREQUENCY_HEAD: PAID_RELATIVE_ENVELOPE_FOR_ABS_XI_LE_SQRT_M_AND_m_GE_16
PRIME_POWERS_EXPONENT_GE_3: PAID_UNIFORM_RELATIVE_ENVELOPE
HIGH_FREQUENCY_PRIMES_AND_PRIME_SQUARES_JOINT_CORRELATION: OPEN
ENTIRE_SAME_SIDE_LOWER_ORDER_BOUND: OPEN
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: TWO_PROPER_HEAD_SUBCONTRIBUTIONS_BOUNDED_NOT_THE_REQUESTED_WHOLE_HEAD
CLOSED_REQUESTED_SAVING_OR_LEADING_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: DUALIZE
DISCRIMINATOR: TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION
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

Ы. **OPEN_SAME_SIDE_HEAD.** Neither a source-derived eventual lower-order bound for the whole head nor a leading lower bound on an unbounded selected-index set is established. **The component-saving mechanism is unproved, not refuted.**

Two proper contributions can be bounded. The exact half-line Fourier representation, with the original projection and both physical tails retained, gives an explicit relative bound tending to zero for the part with continuous frequencies \(|\xi|\le\sqrt m\). Separately, every prime power of exponent at least three has a uniform absolute bound at the \(E_{11}\) scale. What remains is the **joint high-frequency contribution of primes and prime squares**, evaluated against the actual error's spectral density. Its two terms may cancel; neither is assigned a sign.

The one narrower next test concerns only the high-frequency prime-square contribution. It does not repeat the whole head under another name: it excludes exponent-one primes, every exponent at least three, and the already bounded low-frequency region.

## 1. Source lock and unchanged domain

**[COFINAL_FAMILY | PAPER]** All **4,798 bytes** of the authoritative TXT and all **30,279 bytes** of the predecessor Markdown were read. The predecessor's locally computed SHA-256 agrees with the request, and its locally computed Git blob agrees with the pinned GitHub response. The bootstrap was fetched from `rh_clean`; its response-format and dependency rules were read. The request accepts the predecessor's convergence statements and its same-side range above \(Q\), not a saving for the head or the opposite-side contribution. fileciteturn73file0L13-L27 fileciteturn76file0L3-L5

Fix the same \(P\) and all admitted selected cells
\[
m=J_P+j+2,\qquad L=\log m,\quad b=L/2,\quad Q=\sqrt m,
\quad \omega_n=2\pi n/L.
\]
Use exactly
\[
g=G'',\qquad h=T_mg,\qquad f=h-g,\qquad E=E_{11}=\|f\|_2^2>0,
\quad \ell_m=\log\frac{m+1}{L}.
\]
The source \(G\), original \(5m\) splice, Fourier carrier \(-m\le n\le m\), and coefficients
\[
e_n=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}g(u)e^{-i\omega_nu}\,du
=-\omega_n^2b_n+\epsilon_m,
\qquad \epsilon_m=\frac{2G'(b)}{\sqrt L},
\tag{1}
\]
are unchanged. Reality and evenness are source facts, not assumptions about a replacement vector. In particular, the endpoint constant in (1) is not removed. fileciteturn73file0L29-L50

Below, a split of a **continuous Fourier integral** is only a way of estimating a correlation. It does not change \(T_m\), the discrete carrier, the dilation boundary \(Q\), or the error \(f\).

## 2. The first unpaid cancellation, fully indexed

**[FINITE_CELL | PAPER]** Retain the source polynomial
\[
h_2(x)=\bigl(-64v^4+448v^3-660v^2+150v\bigr)e^{-v},
\qquad v=\pi x^2,
\]
and define
\[
\mathcal H_2(s;a,c)=\int_a^c h_2(x)x^{s-1}\,dx,
\qquad s_n=\tfrac12-i\omega_n,
\]
\[
\mathcal J(\eta,a)=\int_0^a e^{i\eta u}\,du
=\begin{cases}(e^{i\eta a}-1)/(i\eta),&\eta\ne0,\\ a,&\eta=0.\end{cases}
\]
For each integer \(2\le\nu\le Q\), write the four terms in the request as \(T_{0,\nu},T_{1,\nu},T_{2,\nu},T_{3,\nu}\), in their stated order. Their explicit source expansions are
\[
\begin{aligned}
T_{0,\nu}={}&\frac1{L\sqrt\nu}\operatorname{Re}
\sum_{n,q=-m}^{m}\overline{e_n}e_q(-1)^{q-n}
 e^{i\omega_q\log\nu}
 \mathcal J(\omega_q-\omega_n,b-\log\nu),\\
T_{1,\nu}={}&\frac1{\sqrt L}\operatorname{Re}
\sum_{n=-m}^{m}\sum_{r\ge1}\overline{e_n}(-1)^n
(r\nu)^{-s_n}\mathcal H_2(s_n;r\nu,r\nu Q),\\
T_{2,\nu}={}&\frac1{\sqrt L}\operatorname{Re}
\sum_{n=-m}^{m}\sum_{r\ge1}\overline{e_n}(-1)^n
\nu^{s_n-1}r^{-s_n}\mathcal H_2(s_n;r,rQ/\nu),\\
T_{3,\nu}={}&\sum_{r,s\ge1}\int_1^\infty
 h_2(rx)h_2(s\nu x)\,dx.
\end{aligned}
\tag{2}
\]
Here \(n,q\) are independent finite Fourier indices, and \(r,s\) in the last line are positive integer source-series indices. The complex conjugates in (2) match the stated Fourier convention; the quantities are real because the source functions are real. Choosing the conjugate expression for a real \(H_{m,+}\) does not change it.

The first unresolved comparison is for the **complete signed sum**
\[
\boxed{
\mathscr S_m^{\rm head}
=4\sum_{2\le\nu\le Q}\Lambda(\nu)
\bigl(T_{0,\nu}-T_{1,\nu}-T_{2,\nu}+T_{3,\nu}\bigr).
}
\tag{3}
\]
Equations (2) are direct substitutions into the predecessor's four-term identity; they do not estimate the terms separately. The required domains and signs are explicit in the authoritative request and the pinned predecessor. fileciteturn73file0L52-L71 fileciteturn76file0L2-L2

In particular, the diagonal of the first term is literally
\[
(T_{0,\nu})_{n=q}
=\frac{b-\log\nu}{L\sqrt\nu}
\sum_{n=-m}^{m}|e_n|^2\cos(\omega_n\log\nu).
\tag{4}
\]
It is not a limit assigned to the off-diagonal terms. At an integer boundary \(\nu=Q\), \(T_{0,\nu}=T_{2,\nu}=0\) by their zero-length intervals. Neither \(T_{1,\nu}\) nor \(T_{3,\nu}\) is set to zero.

All source-series arguments in (2) are at least one. The signed polynomial times Gaussian supplies absolute convergence for each fixed selected cell. For example, a double-product majorant is a constant times
\[
r^8s^8\nu^8 x^{16}e^{-\pi(r^2+s^2\nu^2)x^2},\qquad x\ge1;
\]
its integral is summable in \(r,s\). Thus these interchanges do not require the invalid unweighted \(L^2\) assumption for \(Z_g\).

The forward and reverse mixed terms remain different:
\[
\sum_{2\le\nu\le Q}\Lambda(\nu)F_+(\nu x)
=\sum_{k\ge1}L_Q(k)h_2(kx),
\quad L_Q(k)=\sum_{\substack{\nu\mid k\\2\le\nu\le Q}}\Lambda(\nu),
\tag{5}
\]
whereas the reverse mixed term has \(\nu\le y\) after \(y=\nu x\). Nothing below substitutes \(\log k\) for \(L_Q(k)\), or changes that moving boundary. The two exterior half-lines are retained through the even source and the original factor four in (3). fileciteturn76file0L2-L2

**[COFINAL_FAMILY | PAPER]** Neither
\[
|\text{right-hand side of (3)}|
\le C_{\rm side}(1+\log\log m)E
\]
on an eventual selected tail, nor a positive lower bound at \(\ell_mE\) scale on an unbounded selected set, is proved in this review. The bounds below concern specified proper pieces only.

## 3. An exact one-sided spectral representation

### 3.1. The half-line restriction isolates this component, not the full arithmetic form

**[FINITE_CELL | PAPER]** Put
\[
f_+(u)=\mathbf1_{[0,\infty)}(u)f(u),\qquad
\Phi_m(\xi)=\frac1{\sqrt{2\pi}}\int_0^\infty f(u)e^{-i\xi u}\,du.
\tag{6}
\]
The source gives \(f_+\in L^1\cap L^2\), with
\[
\int_{\mathbb R}|\Phi_m(\xi)|^2d\xi=\|f_+\|_2^2=E/2.
\]
Translation and Plancherel give, for every \(t\ge0\),
\[
\int_0^\infty f(u)f(u+t)\,du
=\int_{\mathbb R}\cos(\xi t)|\Phi_m(\xi)|^2d\xi.
\tag{7}
\]
These are the standard unitary Fourier identities; the convention here uses \(e^{-i\xi u}\), obtained from the corresponding positive-sign convention by reversing \(\xi\). No source estimate is imported with those identities. citeturn215542search0

Define the finite real multiplier
\[
D_Q(\xi)=\sum_{2\le\nu\le Q}\frac{\Lambda(\nu)}{\sqrt\nu}
\cos(\xi\log\nu).
\]
Then the same head (3) is exactly
\[
\boxed{\mathscr S_m^{\rm head}
=4\int_{\mathbb R}D_Q(\xi)|\Phi_m(\xi)|^2d\xi.}
\tag{8}
\]
The measure \(|\Phi_m|^2d\xi\) is nonnegative; \(D_Q\) is not assigned a sign. Equation (8) therefore gives no positivity assertion. Also \(\Phi_m\) is the transform of the **half-line restriction**, not the transform of the even error on the whole line. Replacing it by the latter would reintroduce the opposite-side term.

### 3.2. Its density is still fully source-defined

**[FINITE_CELL | PAPER]** For \(s_\xi=1/2-i\xi\), the exact source expression is
\[
\boxed{
\Phi_m(\xi)=\frac1{\sqrt{2\pi}}
\left[
\frac1{\sqrt L}\sum_{n=-m}^{m}e_n(-1)^n
\mathcal J(\omega_n-\xi,b)
-\sum_{r\ge1}r^{-s_\xi}\mathcal H_2(s_\xi;r,\infty)
\right].
}
\tag{9}
\]
The last term is \(\int_0^\infty g(u)e^{-i\xi u}du\), not a complete Mellin integral starting at zero. Its lower limit is \(r\), and its upper limit includes the whole positive physical tail. The series is absolutely integrable because \(re^u\ge r\) for \(u\ge0\). Every \(e_n\) still contains (1).

The apparent quotient at \(\xi=\omega_n\) uses \(\mathcal J(0,b)=b\). Thus (9) covers the entire real frequency line, including all removable points. Expanding its squared modulus retains the original self, two mixed, and source-source terms; it is not a Gaussian or midpoint replacement for their cancellation.

## 4. A relative source bound for the low continuous-frequency contribution

This is a new estimate, derived here. It uses the actual projection's orthogonality, not a generic norm bound for an arbitrary error.

### 4.1. Orthogonality on the positive half-window

**[FINITE_CELL | PAPER]** Split the actual energy as
\[
E_I=2\int_0^b|f(u)|^2du,\qquad
E_O=2\int_b^\infty|g(u)|^2du,\qquad E=E_I+E_O.
\]
Since \(g,h,f\) are even and \(h=T_mg\),
\[
\int_0^b f(u)\cos(\omega_nu)du=0,
\qquad n=0,1,\ldots,m.
\tag{10}
\]
Let \(P_m^{\cos}\) be the orthogonal projection on this cosine span in \(L^2(0,b)\). This notation only describes the already existing orthogonality; it does not replace the source projection. Cosine-series Parseval supplies the norm of its orthogonal remainder. citeturn215542search2

For \(n>m\), an exact integral is
\[
\int_0^b e^{-i\xi u}\cos(\omega_nu)du
=\frac{i\xi[1-(-1)^ne^{-i\xi b}]}{\omega_n^2-\xi^2}.
\tag{11}
\]
Both endpoints are visible. Set \(\Omega_m=2\pi(m+1)/L\). For \(|\xi|\le\Omega_m/2\),
\[
\left|\int_0^b e^{-i\xi u}\cos(\omega_nu)du\right|
\le\frac{8|\xi|}{3\omega_n^2}.
\]
Using the orthonormal cosine functions \((2/b)^{1/2}\cos(\omega_nu)\) for \(n\ge1\), and \(\sum_{n>m}n^{-4}\le1/(3m^3)\), gives
\[
\boxed{
\|(I-P_m^{\cos})e^{-i\xi u}\|_{L^2(0,b)}^2
\le\frac{16L^3\xi^2}{27\pi^4m^3}.
}
\tag{12}
\]
Therefore the interior part of (6) satisfies
\[
\left|\int_0^bf(u)e^{-i\xi u}du\right|
\le\sqrt{E_I}\left(\frac{8L^3\xi^2}{27\pi^4m^3}\right)^{1/2}.
\tag{13}
\]
No half-window sine moment was set to zero. Instead, the entire exponential was projected onto the cosine basis, which is why both endpoint terms survive in (11).

### 4.2. The exterior contribution is bounded, not discarded

**[COFINAL_FAMILY | PAPER]** The admitted source estimate for \(m\ge16\) is
\[
F(u):=-g(u)>0,\qquad F(u+s)\le e^{-\pi ms}F(u),
\quad u\ge b,\ s\ge0.
\tag{14}
\]
It is the predecessor's exterior estimate, not an estimate inside the head-overlap interval. fileciteturn77file0L2-L2

With \(M_F(u)=\int_u^\infty F(v)dv\), (14) gives \(M_F(u)\le F(u)/(\pi m)\). Hence
\[
\left(\int_b^\infty|g(u)|du\right)^2
=2\int_b^\infty F(u)M_F(u)du
\le\frac{E_O}{\pi m}.
\tag{15}
\]
Combine (13) and (15) by ordinary Cauchy–Schwarz in the two numbers \(\sqrt{E_I},\sqrt{E_O}\). This yields
\[
\boxed{
|\Phi_m(\xi)|^2
\le\frac{E}{2\pi}
\left(\frac{8L^3\xi^2}{27\pi^4m^3}+\frac1{\pi m}\right),
\quad |\xi|\le\Omega_m/2,\quad m\ge16.
}
\tag{16}
\]
As a check at zero, orthogonality to the constant mode gives the exact value
\[
\boxed{\Phi_m(0)=\frac{G'(b)}{\sqrt{2\pi}}>0.}
\tag{17}
\]
Indeed, the interior integral of \(f\) vanishes and the exterior integral is \(-\int_b^\infty g=G'(b)\). Setting the exterior to zero would already contradict (17). The Q5/Q6 endpoint information has not disappeared in the half-line representation.

### 4.3. All head prime powers in this frequency region are paid together

**[COFINAL_FAMILY | PAPER]** Choose the analytical frequency boundary
\(\Xi_m=\sqrt m\). For \(m\ge16\), \(\Xi_m\le\Omega_m/2\); for example \(\log m<\sqrt m\) suffices. Integrating (16) gives
\[
\boxed{
\int_{|\xi|\le\Xi_m}|\Phi_m(\xi)|^2d\xi
\le E\left[
\frac{8L^3}{81\pi^5m^{3/2}}+\frac1{\pi^2\sqrt m}
\right].
}
\tag{18}
\]
The elementary finite multiplier bound is
\[
|D_Q(\xi)|\le\sum_{2\le\nu\le Q}\frac{\log\nu}{\sqrt\nu}
\le 2\sqrt Q\log Q=Lm^{1/4}.
\]
Consequently, for the exact low-frequency part of (8),
\[
\boxed{
\begin{aligned}
\left|\mathscr S_m^{\rm low}\right|
&:=\left|4\int_{|\xi|\le\Xi_m}D_Q(\xi)|\Phi_m(\xi)|^2d\xi\right|
\le\rho_{\rm low}(m)E,\\
\rho_{\rm low}(m)
&=\frac{32L^4}{81\pi^5m^{5/4}}+
\frac{4L}{\pi^2m^{1/4}}
\le\frac12Lm^{-1/4}\longrightarrow0.
\end{aligned}
}
\tag{19}
\]
For the last bound, divide by \(Lm^{-1/4}\), use
\(L^3/m\le27/e^3\), \(\pi>3\), and \(e>2\): the resulting coefficient is less than \(4/9+4/729<1/2\). This threshold and every constant are independent of the unknown head ratio.

Equation (19) includes **all** prime powers \(2\le\nu\le Q\) in this continuous-frequency region. The same upper estimate applies to any subcollection of them. It is not a bound for the remaining integral \(|\xi|>\Xi_m\), and it is not a bandlimiting claim about \(f_+\).

## 5. Prime-power decomposition and the two remaining high-frequency terms

### 5.1. Exponents at least three have a uniform relative budget

**[ABSTRACT | PAPER]** Use the literal von Mangoldt convention \(\Lambda(p^a)=\log p\) for prime \(p\) and integer \(a\ge1\), with zero weight off prime powers. This includes prime squares and higher powers, rather than replacing the arithmetic sum by primes alone. citeturn215542search1

Decompose the finite multiplier exactly as
\[
\begin{aligned}
D_Q^{(1)}(\xi)&=\sum_{p\le Q}\frac{\log p}{\sqrt p}\cos(\xi\log p),\\
D_Q^{(2)}(\xi)&=\sum_{p^2\le Q}\frac{\log p}{p}\cos(2\xi\log p),\\
D_Q^{(\ge3)}(\xi)&=\sum_{\substack{p\ {
m prime},\ a\ge3\\p^a\le Q}}
\frac{\log p}{p^{a/2}}\cos(a\xi\log p).
\end{aligned}
\tag{20}
\]
There is no overlap: a prime power has one prime base and one exponent.

For every real \(\xi\) and every finite \(Q\),
\[
|D_Q^{(\ge3)}(\xi)|
\le\frac1{1-2^{-1/2}}\sum_{n=2}^\infty\frac{\log n}{n^{3/2}}
\le B_3:=\frac{4+2\log2}{1-2^{-1/2}}.
\tag{21}
\]
The last series bound follows by comparing the \(n\)-th summand with
\(\int_{n-1}^n\log(x+1)x^{-3/2}dx\), then using \(\log(x+1)\le\log x+\log2\) for \(x\ge1\). The integral is \(4+2\log2\).

Since \(\int|\Phi_m|^2=E/2\), for the whole frequency line or any measurable part of it,
\[
\boxed{
\left|4\int D_Q^{(\ge3)}(\xi)|\Phi_m(\xi)|^2d\xi\right|
\le C_3E,\qquad
C_3:=2B_3<48.
}
\tag{22}
\]
This controls every exponent at least three in the stated source sum. The infinite positive majorant in (21) is an error bound, not a change of its finite arithmetic range.

### 5.2. Exact remaining cancellation

**[FINITE_CELL | PAPER]** Set
\[
\mathscr U_m^{(a)}
=4\int_{|\xi|>\Xi_m}D_Q^{(a)}(\xi)|\Phi_m(\xi)|^2d\xi,
\qquad a=1,2.
\tag{23}
\]
Then (8), (19), and (22) give the exact decomposition and proved enclosure
\[
\boxed{
\mathscr S_m^{\rm head}
=\mathscr U_m^{(1)}+\mathscr U_m^{(2)}+\mathcal R_m,
\qquad
|\mathcal R_m|\le[C_3+\rho_{\rm low}(m)]E.
}
\tag{24}
\]
The remainder is the low-frequency contribution of the whole head plus the high-frequency contribution of exponents at least three. Thus no frequency/arithmetic block is counted twice.

The first unpaid four-term cancellation (3) is now equivalently located in the **joint** expression \(\mathscr U_m^{(1)}+\mathscr U_m^{(2)}\), up to the explicit bounded remainder. Each term uses the full source density (9), not only its finite-window self term. A leading term in either one alone could be canceled by the other.

**[COFINAL_FAMILY | PAPER]** Combining only with the predecessor's admitted complementary same-side range gives
\[
\boxed{
\left|\mathscr S_m-igl(\mathscr U_m^{(1)}+\mathscr U_m^{(2)}\bigr)\right|
\le[C_3+\rho_{\rm low}(m)+r_{\rm side}(m)]E,
\quad m\ge16.
}
\tag{25}
\]
Here \(r_{\rm side}\) is exactly predecessor (18); in particular
\(\rho_{\rm low}+r_{\rm side}\le(5/2)Lm^{-1/4}\to0\).
This is what is established for the **entire same-side component**. It is not the requested lower-order estimate, because the sum in parentheses is still unbounded at that scale by the present proof. The opposite-side term in the full arithmetic identity remains separate. fileciteturn73file0L57-L61 fileciteturn77file0L2-L2

## 6. Why neither requested family verdict follows

**[COFINAL_FAMILY | PAPER]** The available projection argument controls (16) only for a specified frequency region; after integration with the full multiplier it pays (19), not (23). The exterior decay input is valid only beyond the physical boundary. Applying it to \(0<u<b-\log\nu\) would remove precisely the interior-interior head correlation that remains open.

Bounding the four terms in (3) separately uses absolute source integrals that are not relatively bounded here by \(E\). The restricted divisor identity (5) still leaves the moving boundary of the reverse mixed term. Convergence of those integrals therefore does not imply a value of \(C_{\rm side}\).

Even after passing to (8), the general estimates only give
\[
|\mathscr S_m^{\rm head}|
\le 2Lm^{1/4}E.
\tag{26}
\]
This is much larger than the requested \((1+\log\log m)E\) scale. It gives no leading lower bound, because the cosine multiplier can have either sign on the actual spectral density.

The square block illustrates the first remaining arithmetic distinction. A completely elementary dyadic estimate gives
\[
\sum_{p\le X}\frac{\log p}{p}\le2\log X+2\log2,
\qquad X\ge2.
\tag{27}
\]
Indeed, the product of the primes in \((2^{j-1},2^j]\) divides
\(\binom{2^j}{2^{j-1}}\le2^{2^j}\). Each dyadic block thus contributes at most \(2\log2\) after division by its lower endpoint; summing up to \(\lceil\log_2X\rceil\) proves (27). No prime number theorem is used.

Since \(X=Q^{1/2}=m^{1/4}\), (27) proves only
\[
\boxed{|\mathscr U_m^{(2)}|\le(L+4\log2)E.}
\tag{28}
\]
The bound is at the scale where a leading contribution is possible. It is neither the lower-order bound nor a witness that a leading contribution actually occurs. Extending (21) to exponent two no longer supplies a convergent majorant: replacing prime bases by all integers gives the divergent series \(\sum_{n\ge2}(\log n)/n\). Thus that argument cannot supply a fixed square-block constant.

There is no proved source cancellation estimate for the remaining weighted prime or prime-square cosine moments in (23), and no proved unbounded-index lower witness for their sum. This is **NO_DERIVATION**, not a claim that such estimates are impossible. In particular, no inference is made about the integrated archimedean deviation, transfer entries, \(J_m\), or any later sign.

## 7. Exactly one strictly narrower next PAPER test

### TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION

**[FINITE_CELL | PAPER]** Test only
\[
\boxed{
\mathscr U_m^{(2)}
=4\operatorname{Re}\sum_{p\le m^{1/4}}\frac{\log p}{p}
\int_{|\xi|>\sqrt m}e^{2i\xi\log p}
\left|\frac1{\sqrt{2\pi}}
\left[
\frac1{\sqrt L}\sum_{n=-m}^{m}e_n(-1)^n
\mathcal J(\omega_n-\xi,b)
-\sum_{r\ge1}r^{-s_\xi}\mathcal H_2(s_\xi;r,\infty)
\right]\right|^2d\xi.
}
\tag{29}
\]
Every \(p\) in (29) is prime. The arithmetic numbers being tested are exactly \(\nu=p^2\le Q\), with their original Mangoldt weights. The fixed carrier, Q5/Q6 term, and full source tail remain inside the same squared difference. The integral is absolutely convergent because the multiplier is a finite bounded function and the density is in \(L^1\).

An equivalent physical target is the complete four-term expression (3) restricted to \(\nu=p^2\), minus its low-frequency contribution. The latter already has absolute bound \(\rho_{\rm low}E\). Thus this test may be attacked in either representation without deleting either mixed term or the \(\nu\le y\) boundary.

**Proposed test outcomes, not results:** obtain a finite source-derived \(C_2\) and an explicit selected threshold with
\[
|\mathscr U_m^{(2)}|\le C_2(1+\log\log m)E
\tag{30}
\]
on that whole selected tail; or obtain a source-derived \(c_2>0\) and a proved unbounded selected-index set with
\[
|\mathscr U_m^{(2)}|\ge c_2\ell_mE.
\tag{31}
\]
Constants defined by an unknown supremum or ratio do not satisfy (30). Positive weights in (29) do not prove (31). The unfixed-sign sum of all source terms must be estimated.

This is strictly narrower than the current request in two ways: its arithmetic set contains **only prime squares**, not primes or higher prime powers; its spectral domain excludes the entire region already paid in (19). It is the borderline exponent left after the summable range (22), and its prime bases run only to \(m^{1/4}\). This is a fixed subproblem, not a cutoff search.

A result (30) would pay all higher-prime-power contributions to this head, using (19) and (22), while leaving the exponent-one contribution \(\mathscr U_m^{(1)}\) open. A result (31) would instead force explicit cancellation with \(\mathscr U_m^{(1)}\) for a whole-head saving to remain possible. **Neither outcome alone is `SAME_SIDE_HEAD_SAVED` or `SAME_SIDE_HEAD_LEADING`.** Still less is it a full divisor-correlation kill.

The main risk is exactly the present one in a smaller domain: a norm bound for the density and an absolute coefficient sum only reproduce (28). The test needs the actual source-weighted oscillatory correlation, not another application of that norm bound.

### Two representations; only test (29) is commissioned

| Representation | Discriminating power | PAPER cost and principal risk |
|---|---|---|
| **Chosen: the one-sided spectral density (9) paired with the prime-square multiplier (29).** | Distinguishes a lower-order square contribution from a source-leading square contribution without touching primes or opposite-side correlations. | One finite arithmetic multiplier and the actual squared source difference. The density must not be replaced by a point mass, a fitted frequency, or a generic norm bound. |
| **Alternative: omitted cosine coefficients of the same error on \([0,b]\), plus its exact exterior \(-g\).** | Evaluates the same square contribution through the explicit oscillatory overlap kernel, with diagonal and off-diagonal tail pairs separate. | At fixed \(m\), the omitted cosine series converges in \(L^2\), so each shifted correlation follows by Cauchy–Schwarz; uniform relative estimates for its signed sums remain required. No truncation-depth escalation or second test is commissioned. |

## 8. Adversarial checks and closeout

**[ABSTRACT | PAPER]** The strongest objection is that a half-line Fourier restriction creates a boundary at zero. It does. The proof never assumes that \(f_+\) is even or smoothly joined to zero there. It uses Plancherel for the actual restriction, and (11) retains the endpoint at zero explicitly. In particular, \(\Phi_m(0)\) is the nonzero source value (17), not zero. The original two physical tails are still represented through evenness and the correct factors of two and four.

**[ABSTRACT | PAPER]** A calibration for the essential projection condition is a nonzero constant function on \([0,b]\), with zero exterior. It would have a nonzero transform at zero, whereas (13) at zero would force the interior contribution to vanish. Such a function is not orthogonal to the retained constant mode, so it is correctly excluded by (10). This is a detector check, not a selected-source counterexample.

**[FINITE_CELL | PAPER]** No \(\mathcal J\) denominator is divided through at zero. The exact integer boundary \(\nu=Q\) is covered as described after (4). All \(r\ge1\) source terms in (9) remain. In (20), cubes and higher powers are counted by their unique prime base and exponent, not mistaken for square terms. No Cauchy inequality for an indefinite Weil form is invoked: every norm estimate here is an ordinary \(L^2\) estimate.

**Prediction scoring.** The initial check asked whether projection orthogonality would control the shifted head while respecting its moving cutoff. It did **not** establish that full claim. Its verified output is the narrower frequency-localized estimate (19); this is not scored as a successful whole-head prediction. No prediction of either requested family sign or saving was registered, and neither is credited retroactively. The prime-power bound (22) is reported as a proved additional estimate, not as a previously registered head verdict. The predecessor's accepted tail and convergence claims are inputs, not new results.

**What closed:** for every admitted selected \(m\ge16\), the exact low-frequency part of this head obeys (19); all exponent-at-least-three contributions obey (22). **What remains:** the joint source-weighted prime and prime-square contribution in (23), equivalently the unpaid four-term cancellation (3) at the requested relative scale. No selected saving/leading quantifier for the whole head has closed.

The three structural checks are explicit. The bridge is one-sided Fourier autocorrelation. The exact vanishing mechanism is orthogonality to the retained cosine modes, which removes their interior contributions but not the exterior term or high-frequency arithmetic. The family-deciding object is still the actual weighted spectral moment, not the mass of its density. The next test is a proper arithmetic/frequency subblock, with a defined implication and a defined non-implication.

```yaml
DOWNSTREAM_CONSUMER: lower_order_entire_same_side_component_then_joint_complete_arithmetic_correlation
ACTUAL_CONSUMER_REQUIREMENT: control_of_head_plus_paid_same_side_tail_with_opposite_side_cancellation_kept_separate
ORIGINAL_REQUESTED_OBJECT: eventual_lower_order_same_side_head_bound_or_unbounded_component_leading_witness
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: a_separately_saved_head_is_not_proved_necessary_for_saved_full_arithmetic_or_joint_transfer
KNOWN_WEAKER_INTERFACES:
  - joint_head_and_opposite_side_control_can_allow_leading_components
  - joint_multiplier_minus_complete_arithmetic_control_can_bypass_a_separate_arithmetic_saving
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_CANCELLATION: equation_3_with_all_four_indexed_terms_in_2_and_coefficients_1
MINIMAL_MISSING_ESTIMATE: joint_high_frequency_prime_and_prime_square_source_moment_in_23_at_the_actual_E11_scale
NEW_CLOSED_QUANTIFIERS:
  - every_admitted_selected_m_GE_16_satisfies_low_frequency_relative_envelope_19
  - every_finite_Q_and_every_selected_error_satisfy_the_exponent_GE_3_relative_envelope_22
DISCRIMINATOR: TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION
NEXT_TEST_STRICT_SCOPE: nu_is_prime_squared_LE_sqrt_m_and_abs_xi_GT_sqrt_m_only
REOPEN_TRIGGER: paid_source_bounds_for_29_or_joint_bounds_for_23_with_the_required_selected_quantifiers
SAME_SIDE_HEAD_MECHANISM_DEAD: false
DIVISOR_CORRELATION_MECHANISM_DEAD: false
TRANSFER_CERTIFICATE_DEAD: false
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: one_sided_projection_orthogonality_pays_low_continuous_frequencies_and_prime_power_summability_isolates_exponents_1_and_2
MEMORY_ENTRY:
  target: selected_same_side_dilation_head
  status: OPEN
  cognitive_operator_used: DUALIZE
  invariant_learned: half_line_spectral_mass_is_positive_but_its_arithmetic_cosine_multiplier_is_signed
  forbidden_future_move: apply_low_frequency_or_exponent_GE_3_bounds_to_the_unpaid_prime_square_or_prime_block
  next_decisive_test: TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION`, on paper, with the exact source expression (29).** Seek (30), or the properly quantified square-component witness (31), without replacing the source density by a norm bound, a point frequency, or a reference trial. A physical-coordinate derivation must retain all four terms (2) with \(\nu=p^2\), the separate diagonal, both mixed domains, the restricted divisor weights, and the original Q5/Q6 edge. Use (19) only on its stated low-frequency region and (22) only for exponents at least three. A square saving leaves the exponent-one prime block open; a leading square contribution requires joint cancellation analysis and is not a whole-head or full-arithmetic kill. No mathematical runtime, numerical cutoff search, Lean, repository write, new seed, source/carrier/Q replacement, route promotion, transfer pass, actual-J sign, compression dominance, activity, axis gap, first-tau-sign, Schur-floor, or RH claim is authorized.
