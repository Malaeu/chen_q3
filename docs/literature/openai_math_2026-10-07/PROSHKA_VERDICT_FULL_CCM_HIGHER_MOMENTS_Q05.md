# STATUS: TRY_RH_SOURCE_ARITHMETIC
```yaml
OPERATIVE_CLASS: TRY_RH_SOURCE_ARITHMETIC
VERDICT_CODE: FULL_CCM_MOMENT_Q05_SHORT_SOURCE_HIGH_MOMENTS_PAID_LONG_CYCLIC_SIGN_OPEN
REQUEST: PROSHKA_CCM_MOMENT_Q05.txt
REQUEST_BYTES: 429473
REQUEST_SHA256: 61d077e0f0379f14986254f021cd11dde467972681fa5ea322fd41e3995d86a6
SOURCE_BASELINE: b8764caf
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
ROUTE_ID: RH_SOURCE_ARITHMETIC
FRONT_ID: FULL_CCM_COUPLED_MOMENT_DRIFT
SOURCE_OBJECT_FAMILY_ID: CCM_LITERAL_FULL_MATRIX_N_EQUALS_M
TERMINAL_CONSUMER_ID: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: CCM_LITERAL_EQ4_2_TO4_4_ALL_MODES_FULL_PRIME_HISTORY
SELECTED_INTERFACE: ENDPOINT_FULL_EVEN_MOMENT_OF_ORIGINAL_BOUNDARY_ZERO_COMPRESSION
ADJUDICATION: INCONCLUSIVE_FOR_ORDER_INDEPENDENT_FULL_MOMENT_BOUND
REQUESTED_UNIFORM_EXPONENT: NOT_PROVED
FULL_FLOOR_IMPROVEMENT: NONE
SP_STATUS: OPEN
RH_STATUS: OPEN
PX_RH_CLAIM: NOT_MADE
EXECUTED_CALCULATION: "Actual coefficient convolution on the original grid; exact cyclic expansion; nonnegative quadratic-insertion credit; explicit budget for zero, one and two long-source insertions."
ARITHMETIC_CUTOFF: "x=m^(1/(p-1)); an exact source split, not a changed physical matrix or a normalization"
NEW_SHORT_MOMENT: "Tr|U|^(2p-2) <= A_(p-1)*m*(log m)^(p^2+1)"
NEW_PARTIAL_MOMENT_INEQUALITY: "Tr(S_-^p) <= Tr(S^p) <= C_p*m^(3/2)*(log m)^(p^2+1) + R_(p,m) - Ccredit_(p,m)"
NEW_NONNEGATIVE_CREDIT: "Ccredit_(p,m)>=0; at p=4 it equals norm_HS([U,V])^2"
PAID_EXPONENT: "3/2"
PAID_EXPONENT_IS_FULL_TARGET: false
FIRST_UNPAID: "R_(p,m)-Ccredit_(p,m), with all words containing at least three actual long-source insertions retained"
NEW_ESTIMATE_SCOPE: COFINAL_FAMILY
NEW_ESTIMATE_VERIFIER: PAPER
CONDITIONAL_INPUTS_FOR_NEW_CALCULATION: NONE_BEYOND_ACCEPTED_LITERAL_SOURCE_AND_PREVIOUS_PAPER_BOUNDS
ZF78_STATUS: REPORTED_ZETA_ONLY_COMPARATOR_ACCEPTED_NOT_RERUN_NOT_NEEDED_FOR_NEW_ESTIMATES
DIRICHLET_HECKE_SIEGEL_IMPORTS: NONE
ADAPTIVE_WEIGHT_SUBSTITUTION: NONE
AFFINE_DRIFT_COMPANION_DISPOSITION: "Not invoked: the header explicitly permits the endpoint full-even-moment alternative."
FULL_SOURCE_RETURN: "Accepted Q4 endpoint norm correction <=300*(log m)^(7/2), used once per endpoint, never summed as a drift fee."
REPO_EDITS: NONE
LEAN_RUN: NONE
COMPARATOR_RUN: NONE
ARB_INTERVAL_RUN: NONE
NUMERICAL_DIAGNOSTICS: FLOATING_POINT_ONLY_NOT_CERTIFICATES
EVIDENCE_STATE: PAPER_DERIVED_PENDING_INDEPENDENT_AUDIT
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: SHORT_SOURCE_AND_ZERO_ONE_TWO_LONG_INSERTION_SECTORS_ONLY
CONSUMER_PROGRESS: NO_PROGRESS
ROUTE_SCORE: 3
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE_FOR_ACTUAL_CCM_OR_SP
INDEPENDENT_AUDIT_TARGET: "Theorem Q05-M, equation (25), including its actual-source definitions and the nonnegative credit (16). Acceptance is only of an inequality with the explicitly unbounded remainder (24)."
```

## 1. Result and exact limitation

**The requested order-independent bound for the full negative moment is not proved. No full-floor improvement, SP conclusion, or RH claim is made.**

The executed calculation gives a new higher-moment estimate for a specified short part of the **original arithmetic source**, on the **unchanged full frequency grid**. It then uses that estimate and the accepted full-source mean square to pay every cyclic term with zero, one, or two long-source insertions. The two-insertion calculation also retains a genuinely nonnegative credit. The terms with three or more long-source insertions remain in one explicit signed expression, not in an omitted error.

Here is the resulting statement, with all its terms defined and calculated below. For every fixed even \(p\ge4\), every integer \(m\ge2^{p-1}\), and \(S=\Pi_mK_m\Pi_m\),

\[
\boxed{
0\le\operatorname{Tr}(S_-^p)
\le\operatorname{Tr}(S^p)
\le C_p m^{3/2}(\log m)^{p^2+1}
   +\mathfrak R_{p,m}-\mathfrak C_{p,m},
\qquad \mathfrak C_{p,m}\ge0.
}\tag{R}
\]

**[COFINAL_FAMILY | PAPER]** The exponent \(3/2\) in the paid term is independent of \(p\). **It is not an exponent for the whole moment**, because no adequate upper bound for \(\mathfrak R_{p,m}-\mathfrak C_{p,m}\) is supplied. At \(p=4\), that remainder is exactly

\[
\boxed{
\operatorname{Tr}(V^4)-4\operatorname{Tr}(UV^3)
       -\|[U,V]\|_{\mathrm{HS}}^2.
}\tag{R4}
\]

The matrices \(U,V\) are specified parts of the actual full source, not generic or random replacements. In particular, the mixed cubic term in (R4) and the negative commutator credit are not deleted.

The authoritative attachment has **429,473 bytes** and the stated SHA-256. It was read completely, including the nested original source, previous verdicts, all new attempts, and the external appendix. The current protocol was fetched through the GitHub connector with the blob recorded above. The packet accepts Q4 only for its boundary comparison and expressly changes this question to the endpoint moment alternative. That is the interface used here. fileciteturn24file0L1-L12

## 2. Source lock and the exact arithmetic split

### 2.1 Original objects and inherited inputs

**[FINITE_CELL | PAPER: source-locked definitions]** Write

\[
I_m=\{-m,\ldots,m\},\qquad d=2m+1,\qquad L=\log m,
\qquad \omega_j=2\pi j/L.
\]

Retain the literal matrix kernel

\[
Q(s)_{jk}=
\begin{cases}
2(1-s/L)\cos(\omega_js),&j=k,\\[1mm]
\displaystyle\frac{\sin(\omega_ks)-\sin(\omega_js)}{\pi(j-k)},&j\ne k,
\end{cases}
\quad 0\le s\le L,
\quad Q(0)=2I,\quad Q(L)=0.
\tag{1}
\]

The production matrix is

\[
\begin{split}
K_m&=\mathsf B_m-\mathsf C_m,\\
\mathsf C_m&=\int_{[0,L]}Q(s)\,d\nu(s),\\
d\nu(s)&=\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)
               -e^{s/2}\,ds+e^{-s/2}\,ds,\\
\mathsf B_m&=\mathsf A_{\mathrm{arch},m}-c_AI+2\mathsf R_m.
\end{split}\tag{2}
\]

Thus both continuous terms retain their signs. For completeness of the source inventory, rather than a new background proof,

\[
\begin{split}
\mathsf A_{\mathrm{arch},m}
 &=\int_0^L J(s)(2I-Q(s))\,ds+2I\int_L^\infty J(s)\,ds,\\
J(s)&=\frac{e^{-s/2}}{1-e^{-2s}},\\
\mathsf R_m&=\int_0^L e^{-s/2}Q(s)\,ds,
\qquad c_A=\gamma+\log(8\pi)+\pi/2.
\end{split}
\]

In particular, the archimedean tail beyond \(L\), the constant, and the two retained decaying copies in the background all remain in \(\mathsf B_m\). Equations (1)–(2) are the supplied literal source, not an alternate definition. fileciteturn24file0L284-L317

**[COFINAL_FAMILY | PAPER: independently accepted inputs]** Use, without re-proving them,

\[
\begin{gathered}
\|Q(s)\|\le2,\qquad \|\mathsf B_m\|\le50L,\\
\operatorname{Tr}(K_m^2)\le10000dL^7,\\
\sup_{1\le y\le m}\left\|(\Phi_j(y))_{j\in I_m}\right\|_2
       \le12\sqrt m\,L^{5/2},
\end{gathered}\tag{3}
\]

where the actual joint primitive is

\[
\Phi_j(y)=\sum_{n\le y}\frac{\Lambda(n)}{n^{1/2+i\omega_j}}
 -\frac{y^{1/2-i\omega_j}-1}{1/2-i\omega_j}
 +\frac{1-y^{-1/2-i\omega_j}}{1/2+i\omega_j}.
\tag{4}
\]

The new flat-direction extension supplies the mean square in (3); the prefix bound and background bound are inherited from Q4. The extension does not assert positive energy for arbitrary phase choices. fileciteturn24file0L20-L42 fileciteturn24file0L378-L406 fileciteturn24file0L445-L461

Also retain the accepted deterministic sampling inequality, for arbitrary coefficients supported on any subset of the integers \(2,\ldots,m\):

\[
\sum_{j=-m}^{m}
\left|\sum_{n=2}^{m}a_ne^{-2\pi ij\log n/L}\right|^2
\le5mL^2\sum_{n=2}^{m}|a_n|^2.
\tag{5}
\]

The circular endpoint \(n=m\) is included. There is no \(n=1\) coefficient duplicating its phase. This is the actual-integer estimate, not an average over an invented prime process. fileciteturn24file0L342-L374

### 2.2 Split arithmetic length, not the production carrier

Fix even \(p\ge4\). Put

\[
q=p-1,\qquad x=m^{1/q},\qquad \ell_x=L/q,
\qquad m\ge2^q.
\]

Here \(q\) is a moment-convolution order, not a prime. Define

\[
\begin{split}
\mathsf C_{\le x}&=\int_{[0,\ell_x]}Q(s)\,d\nu(s),\\
\mathsf C_{>x}&=\int_{(\ell_x,L]}Q(s)\,d\nu(s),\\
\Pi&=I-bb^*,\qquad b=\mathbf1/\sqrt d,\\
U&=\Pi(\mathsf B_m-\mathsf C_{\le x})\Pi,\\
V&=\Pi\mathsf C_{>x}\Pi,\qquad
S=U-V=\Pi K_m\Pi.
\end{split}\tag{6}
\]

**[FINITE_CELL | PAPER]** This is an exact identity on the full original \(d\)-dimensional coefficient space. The notation \(U,V\) is local to this calculation. Neither matrix is presumed positive. Both annihilate \(b\); they retain all couplings within its orthogonal complement.

An atom exactly at \(x\), when \(x\) is an integer prime power, belongs to the short piece. The long interval is open there. The atom at \(m\) is retained with its actual kernel value zero. Every older proper power is present in exactly one piece. Both continuous terms are split at the same point. **The kernel in the short piece is still \(Q_{m,\log m}\), not \(Q_{x,\log x}\).** The number of modes, their frequencies, physical support, and normalization have not changed.

The external methodological lookup was the elementary powering operation in Terence Tao's *254A, Notes 6*, proof of Corollary 4: powering a Dirichlet polynomial replaces its coefficients by their Dirichlet convolution and raises its length to that power. No theorem about deleted frequency intervals or character families is imported. Here (5), supplied for the exact CCM grid, is the sampling tool. citeturn506553view0

## 3. Execute a higher moment of the short joint source

### 3.1 Multiplicative coincidences are counted, not declared independent

For \(1\le y\le x\), put

\[
P_j(y)=\sum_{2\le n\le y}\frac{\Lambda(n)}{\sqrt n}e^{-i\omega_j\log n}.
\]

Raise this polynomial to its integer power \(q\) **before** any absolute-value estimate:

\[
\begin{split}
P_j(y)^q&=\sum_{2\le N\le m}a_{q,y}(N)e^{-i\omega_j\log N},\\
a_{q,y}(N)&=\frac1{\sqrt N}
\sum_{\substack{n_1\cdots n_q=N\\2\le n_i\le y}}
      \prod_{i=1}^q\Lambda(n_i).
\end{split}\tag{7}
\]

The support bound is exactly \(N\le y^q\le x^q=m\). All ordered prime-power factorizations occur; different factorizations of the same product are combined with their actual coefficients. No assertion that only permutations or pairings occur is made.

Let \(\tau_k(N)\) denote the number of ordered \(k\)-tuples of positive integers with product \(N\). We need the elementary inequality

\[
\tau_q(N)^2\le\tau_{q^2}(N).
\tag{8}
\]

**[ABSTRACT | PAPER]** To prove (8), first take \(N=\ell^a\) with \(\ell\) prime. An ordered \(q\)-factorization is a weak composition of \(a\) into \(q\) parts. Any ordered pair of such compositions is the row-margin and column-margin pair of at least one nonnegative integer \(q\)-by-\(q\) matrix: greedily fill a row and column until one of their remaining margins is exhausted, then continue. All those matrices have total sum \(a\), and the number of matrices is \(\tau_{q^2}(\ell^a)\). Their margin map is surjective onto the pairs being counted, proving the prime-power inequality. Multiplication over the prime factors of \(N\) proves (8).

Since \(\Lambda(n_i)\le\log n_i\le L\), (7)–(8) imply

\[
\begin{split}
\sum_{N\le m}|a_{q,y}(N)|^2
&\le L^{2q}\sum_{N\le m}\frac{\tau_q(N)^2}{N}\\
&\le L^{2q}\sum_{N\le m}\frac{\tau_{q^2}(N)}{N}\\
&\le L^{2q}\left(\sum_{a\le m}\frac1a\right)^{q^2}
\le L^{2q}(1+L)^{q^2}.
\end{split}\tag{9}
\]

The penultimate inequality only enlarges the actual product-constrained sum to the box in which each factor is at most \(m\). It introduces no independence assumption and no \(m^{\varepsilon p}\) loss.

Apply (5) to the coefficients in (7). Because \(L>1\),

\[
\boxed{
\sup_{1\le y\le x}\sum_{j=-m}^{m}|P_j(y)|^{2q}
\le5\,2^{q^2}\,mL^{q^2+2q+2}.
}\tag{10}
\]

**[COFINAL_FAMILY | PAPER]** The polynomial exponent here is **one**, independent of \(q\). The constant and logarithmic exponent may depend on the fixed order. This is a short-source higher moment on the original grid, not the forbidden interpolation of the full \(K_m\) from its operator norm.

### 3.2 Restore both continuous terms in the higher moment

Write \(\Phi_j(y)=P_j(y)-I_j(y)\), where

\[
I_j(y)=\int_0^{\log y}(e^{s/2}-e^{-s/2})e^{-i\omega_js}\,ds.
\]

This is the specified joint subtraction, including the decaying term. Before bounding it, the full signed higher moment also has the exact finite-measure expression

\[
\sum_j|\Phi_j(y)|^{2q}
=\iint\mathcal D_m((s-t)/L)\,
          d(\nu_y^{*q})(s)\,d(\nu_y^{*q})(t),
\quad
\mathcal D_m(u)=\sum_{j=-m}^{m}e^{2\pi iju},
\tag{11}
\]

where \(\nu_y\) is the restriction to \([0,\log y]\). Its signed convolution includes all atomic/continuous mixtures. Formula (11) is not replaced by its atomic diagonal.

For the quantitative short-source budget it suffices to bound the continuous contribution explicitly. The two rational endpoint expressions give

\[
|I_j(y)|\le\frac{\sqrt x+3}{\sqrt{1/4+\omega_j^2}}
\le\frac{4\sqrt x}{\sqrt{1/4+\omega_j^2}}.
\]

Using the inherited elementary decreasing-sum estimate
\(\sum_j(1/4+\omega_j^2)^{-1}\le4+L\), and then
\((1/4+\omega_j^2)^{-q}\le4^{q-1}(1/4+\omega_j^2)^{-1}\), gives

\[
\sum_j|I_j(y)|^{2q}
\le16^q x^q4^{q-1}(4+L)
\le5\,64^q mL.
\]

Define the explicit constants

\[
E_q=q^2+2q+2,
\qquad
D_q=5\,2^{2q-1}(2^{q^2}+64^q).
\]

The scalar inequality \(|a-b|^{2q}\le2^{2q-1}(|a|^{2q}+|b|^{2q})\), applied only after the exact joint expression is fixed, now proves

\[
\boxed{
\sup_{1\le y\le x}\sum_{j=-m}^{m}|\Phi_j(y)|^{2q}
\le D_qmL^{E_q}.
}\tag{12}
\]

**[COFINAL_FAMILY | PAPER]** No favorable sign was claimed for a separated prime sum. Both continuous terms were paid at the same order-independent polynomial scale. The relation \(x^q=m\) is essential in this calculation.

### 3.3 Return the higher moment to the complete short-source matrix

Let \(\mathsf H_{jk}=1/(j-k)\) for \(j\ne k\), with zero diagonal; its inherited norm is \(\|\mathsf H\|\le\pi\). The exact short-source Hilbert coordinates, still at window \(L\), are

\[
\begin{split}
h_j^{\le x}&=\Im\Phi_j(x),\\
d_j^{\le x}&=\frac2L\Re\int_0^L\Phi_j(\min(e^u,x))\,du,\\
\mathsf C_{\le x}
&=\operatorname{diag}(d^{\le x})
   +\pi^{-1}[\operatorname{diag}(h^{\le x}),\mathsf H].
\end{split}\tag{13}
\]

For the diagonal, interchanging the two finite integrals gives the exact factor \(2(1-s/L)\). For the off-diagonal, \(h_j^{\le x}=-\int\sin(\omega_js)d\nu\) gives the sine difference in (1), with its original sign. Thus this is a restriction of the supplied Hilbert identity, not a replacement off-diagonal formula. fileciteturn24file0L411-L423

For every \(s\ge1\), the Schatten ideal inequality and Minkowski give

\[
\|\mathsf C_{\le x}\|_{\mathcal S_s}
\le\|d^{\le x}\|_{\ell^s}+2\|h^{\le x}\|_{\ell^s}
\le4\sup_{y\le x}\|(\Phi_j(y))\|_{\ell^s}.
\]

Take \(s=2q\) and use (12). Orthogonal compression is contractive for these norms. Adding the **entire** \(\mathsf B_m\), not just its diagonal, proves

\[
\boxed{
\operatorname{Tr}|U|^{2q}\le\mathsf A_qmL^{E_q},
\qquad
\mathsf A_q=2^{2q-1}\bigl(3\cdot50^{2q}+4^{2q}D_q\bigr).
}\tag{14}
\]

Indeed \(\|\Pi\mathsf B_m\Pi\|_{\mathcal S_{2q}}^{2q}\le d(50L)^{2q}\le3\cdot50^{2q}mL^{E_q}\). This verifies the background and compression return within the claimed moment bound. For the chosen \(q=p-1\), \(E_q=p^2+1\).

## 4. Exact cyclic expansion and the retained nonnegative credit

### 4.1 Count the noncommuting words correctly

**[FINITE_CELL | PAPER]** For \(1\le r\le p\), let \(\mathcal W_r\) be the sum of traces of all length-\(p\) words containing exactly \(r\) copies of \(V\), with all remaining letters equal to \(U\). Then

\[
\boxed{
\mathcal W_r
=\frac pr\sum_{\substack{n_1,\ldots,n_r\ge0\\n_1+\cdots+n_r=p-r}}
\operatorname{Tr}(U^{n_1}V\cdots U^{n_r}V),
\qquad
\operatorname{Tr}(S^p)=\operatorname{Tr}(U^p)+\sum_{r=1}^p(-1)^r\mathcal W_r.
}\tag{15}
\]

To check the factor, mark one of the \(r\) occurrences of \(V\) in each word and rotate the marked word so that its marked occurrence is last. Cyclicity preserves its trace. The gaps of \(U\)'s are the displayed weak composition. Averaging the marked position over the \(p\) positions yields \(r\mathcal W_r=p\) times the displayed sum. This argument counts marked occurrences rather than distinct necklaces; **periodic words introduce no exceptional multiplicity**.

In particular,

\[
\mathcal W_1=p\operatorname{Tr}(U^{p-1}V),\qquad
\mathcal W_2=\frac p2\sum_{\ell=0}^{p-2}
       \operatorname{Tr}(U^\ell VU^{p-2-\ell}V).
\]

No commutative binomial expansion has been applied to \(U-V\).

### 4.2 The two-insertion sector has a favorable signed remainder

Put \(n=p-2\), which is even. For real \(a,b\), define

\[
\Delta_n(a,b)=\frac{n+1}{2}(a^n+b^n)
             -\sum_{\ell=0}^{n}a^\ell b^{n-\ell}.
\]

The exact polynomial identity

\[
\sum_{\ell=0}^{n}a^\ell b^{n-\ell}
=(n+1)\int_0^1((1-t)a+tb)^n\,dt
\]

and convexity of the even power show \(\Delta_n(a,b)\ge0\). Repeated values give \(\Delta_n(a,a)=0\), without a divided-by-zero convention.

Choose an orthonormal eigenbasis of the **actual** \(U\), with eigenvalues \(a_\alpha\); let \(V_{\alpha\beta}\) be the actual matrix of \(V\) in that basis. Define

\[
\boxed{
\mathfrak C_{p,m}
=\frac p2\sum_{\alpha,\beta}
\Delta_{p-2}(a_\alpha,a_\beta)|V_{\alpha\beta}|^2\ge0.
}\tag{16}
\]

This quantity is basis-independent within repeated eigenspaces. Expanding the traces in this eigenbasis proves the exact identity

\[
\boxed{
\mathcal W_2
=\frac{p(p-1)}2\operatorname{Tr}(U^{p-2}V^2)
       -\mathfrak C_{p,m}.
}\tag{17}
\]

The sign can also be checked by two scalar integrations by parts. The trapezoid remainder for a twice differentiable \(f\) is

\[
\frac{f(0)+f(1)}2-\int_0^1f(t)dt
=\frac12\int_0^1t(1-t)f''(t)dt.
\]

Consequently

\[
\begin{split}
\mathfrak C_{p,m}
={}&\frac{p(p-1)(p-2)(p-3)}4
\sum_{\alpha,\beta}(a_\alpha-a_\beta)^2|V_{\alpha\beta}|^2\\
&\hspace{6mm}\cdot\int_0^1t(1-t)
       ((1-t)a_\alpha+ta_\beta)^{p-4}\,dt.
\end{split}\tag{18}
\]

Every summand in (18) is nonnegative. At \(p=4\), the integral is \(1/6\), and

\[
\mathfrak C_{4,m}=\sum_{\alpha,\beta}(a_\alpha-a_\beta)^2|V_{\alpha\beta}|^2
                  =\|[U,V]\|_{\mathrm{HS}}^2.
\]

**[FINITE_CELL | PAPER]** This is a genuine favorable sign in the cyclic calculation. It does not assert that a physical CCM increment is generated by phase averaging. There is no such increment in this endpoint argument, and no dephasing replacement of the source. Nor does (16) bound the remaining long-source cycles.

Combining (15)–(17) gives the exact equality

\[
\begin{split}
\operatorname{Tr}(S^p)
={}&\underbrace{\operatorname{Tr}(U^p)
 -p\operatorname{Tr}(U^{p-1}V)
 +\frac{p(p-1)}2\operatorname{Tr}(U^{p-2}V^2)}_{\mathcal P_{p,m}}\\
&+\sum_{r=3}^p(-1)^r\mathcal W_r-\mathfrak C_{p,m}.
\end{split}\tag{19}
\]

The sign of the linear term in (19) is retained before estimating it. The \(\mathsf B_m\) inside \(U\) has not been removed from any cyclic word.

## 5. Pay the zero-, one-, and two-long-insertion terms

### 5.1 The full-source second moment controls the exact long piece

Using (13) at Schatten order two and the accepted prefix bound (3),

\[
\|\mathsf C_{\le x}\|_{\mathrm{HS}}\le48\sqrt m L^{5/2},
\qquad
\|U\|_{\mathrm{HS}}\le98\sqrt dL^{5/2}.
\]

Since \(V=U-S\) and \(\|S\|_{\mathrm{HS}}\le\|K_m\|_{\mathrm{HS}}\),

\[
\boxed{\operatorname{Tr}(V^2)\le40000dL^7.}\tag{20}
\]

This uses the supplied **full-source** second moment. It does not assume that the short and long pieces are orthogonal, independent, or positive.

We also need an elementary operator estimate for the short piece alone. Its total variation is at most

\[
\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}
 +\int_0^{\log x}(e^{s/2}-e^{-s/2})ds
\le2\sqrt x\log x+2\sqrt x.
\]

The first sum follows from \(\Lambda(n)\le\log x\) and the integral bound for \(\sum n^{-1/2}\); the continuous expression is \(2(\sqrt x+x^{-1/2}-2)\). Thus, using \(\|Q\|\le2\), \(\log x\le L\), \(L>1\), and \(\|\mathsf B_m\|\le50L\),

\[
\boxed{\|U\|\le60\sqrt x L.}\tag{21}
\]

Only this specified short matrix receives the factor \(\sqrt x\). No full-source \(\|K\|^{p-2}\operatorname{Tr}K^2\) argument is being relabelled as a gain.

### 5.2 Explicit bounds with a common exponent independent of order

Abbreviate \(E=E_q=p^2+1\), \(A=\mathsf A_q\), with \(q=p-1\).

For the zero-insertion term, finite Hölder applied to the **newly proved short-source moment** (14), with \(\theta=p/(2q)<1\), gives

\[
\operatorname{Tr}(U^p)
\le d^{1-\theta}(AmL^E)^\theta
\le(3+A)mL^E.
\]

The last step uses \(d\le3m\), \(L>1\), and
\(3^{1-\theta}A^\theta\le3+A\). It is not interpolation from the old full-source mean square.

For the linear term, trace Cauchy–Schwarz, (14), and (20) give

\[
\begin{split}
p|\operatorname{Tr}(U^{p-1}V)|
&\le p\,[\operatorname{Tr}|U|^{2p-2}]^{1/2}
            [\operatorname{Tr}V^2]^{1/2}\\
&\le200p\sqrt{3A}\,mL^{(E+7)/2}
\le200p\sqrt{3A}\,mL^E.
\end{split}
\]

For the commuting upper part of the quadratic sector, \(U^{p-2}\) is positive semidefinite since \(p-2\) is even. Hence

\[
\begin{split}
\frac{p(p-1)}2\operatorname{Tr}(U^{p-2}V^2)
&\le\frac{p(p-1)}2\|U\|^{p-2}\operatorname{Tr}V^2\\
&\le60000p(p-1)60^{p-2}
 m^{1+(p-2)/(2(p-1))}L^{p+5}\\
&\le60000p(p-1)60^{p-2}m^{3/2}L^E.
\end{split}\tag{22}
\]

The negative credit in (17) was **not** absorbed into this bound or assigned value zero.

Define

\[
\boxed{
C_p=3+\mathsf A_{p-1}
  +200p\sqrt{3\mathsf A_{p-1}}
  +60000p(p-1)60^{p-2}.
}\tag{23}
\]

**[COFINAL_FAMILY | PAPER]** More precisely, put
\(C_p^{(0,1)}=3+\mathsf A_{p-1}+200p\sqrt{3\mathsf A_{p-1}}\) and
\(C_p^{(2)}=60000p(p-1)60^{p-2}\). The separate paid budgets are

\[
\mathcal P_{p,m}
\le C_p^{(0,1)}mL^{p^2+1}
 +C_p^{(2)}m^{3/2-1/(2(p-1))}L^{p+5}
\le C_pm^{3/2}L^{p^2+1}.
\tag{23a}
\]

This holds for every fixed even \(p\ge4\) and every integer \(m\ge2^{p-1}\). In particular the new convolution moment pays the zero- and one-long-insertion terms at exponent **one**, not just the coarser common exponent. The quadratic upper envelope has the displayed exponent strictly below \(3/2\); its supremum over the orders is \(3/2\). All other \(p\)-dependence is in fixed constants, logarithmic exponents, and the permitted starting index.

The price is that \(\mathcal P_{p,m}\) is only the specified part of the full expansion (19). Bounding it does not bound the whole moment.

## 6. The exact unpaid source sum and Theorem Q05-M

### 6.1 Restore every long prime-power and continuous sector

Define

\[
\boxed{
\begin{split}
\mathfrak R_{p,m}
={}&\sum_{r=3}^{p}(-1)^r\frac pr
\sum_{\substack{n_1,\ldots,n_r\ge0\\n_1+\cdots+n_r=p-r}}
\int_{(L/(p-1),L]^r}\\
&\operatorname{Tr}\!\left[
U^{n_1}\Pi Q(s_1)\Pi\,
U^{n_2}\Pi Q(s_2)\Pi\cdots
U^{n_r}\Pi Q(s_r)\Pi\right]
\prod_{a=1}^{r}d\nu(s_a).
\end{split}
}\tag{24}
\]

The same \(U\) from (6), including all its source dependence, occurs in every factor. The convention is \(U^0=I_d\). The explicit \(\Pi\)'s remain, including between consecutive long insertions with zero intervening power.

All the integrals in (24) are finite-dimensional integrals of bounded matrix functions against finite signed measures on the displayed compact interval. Fubini and the finite cyclic expansion are therefore justified without an infinite-contour interchange, gap hypothesis, or random averaging assumption.

In each coordinate the measure is precisely

\[
\sum_{x<n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}
-\mathbf1_{(\log x,L]}e^{s/2}ds
+\mathbf1_{(\log x,L]}e^{-s/2}ds.
\]

Thus its tensor product retains all \(3^r\) choices of atomic, growing-continuous, and decaying-continuous factors, with a minus sign for each growing-continuous choice and the outer \((-1)^r\) in (24). These signed terms must be combined; no atomic-only expression is identified with the full remainder. An atom at \(m\) has exact zero matrix in every insertion. An atom at the internal split, when present, was already included in \(U\).

### 6.2 The one audit theorem

**Theorem Q05-M. [COFINAL_FAMILY | PAPER]** Let \(p\ge4\) be even, \(m\ge2^{p-1}\) an integer, and let \(S,U,V\) be the original-source matrices (6). With \(C_p\) in (23), the signed sum (24), and the nonnegative credit (16),

\[
\boxed{
0\le\operatorname{Tr}(S_-^p)
\le\operatorname{Tr}(S^p)
=\mathcal P_{p,m}+\mathfrak R_{p,m}-\mathfrak C_{p,m}
\le C_pm^{3/2}L^{p^2+1}
       +\mathfrak R_{p,m}-\mathfrak C_{p,m}.
}\tag{25}
\]

**Proof.** Since \(S\) is Hermitian and \(p\) is even, its full even moment is the sum of the \(p\)-th powers of the absolute values of all eigenvalues and dominates the negative moment. The equality is (19) with the exact measure expansion of \(V\) in every long insertion. Section 5 bounds \(\mathcal P_{p,m}\). Equation (16), or equivalently (18), proves the credit sign. This proves every inequality and equality in (25). It proves no upper bound for the last two terms together.

There is **no ZF78 dependency** in this theorem. Its source inputs are the packet's accepted PAPER bounds (3), (5), and the exact Hilbert identity. ZF78 retains its reported zeta-only Comparator scope for the pre-existing conditional floor, but it is not used to fill the new long-source estimate. No Comparator or Lean run was performed. fileciteturn24file4L291-L302

### 6.3 The first unproved estimate, already at order four

At \(p=4\), (15) gives \(\mathcal W_3=4\operatorname{Tr}(UV^3)\) and \(\mathcal W_4=\operatorname{Tr}(V^4)\). Thus the complete calculation is

\[
\boxed{
\begin{split}
\operatorname{Tr}(S^4)
={}&\operatorname{Tr}(U^4)-4\operatorname{Tr}(U^3V)
       +6\operatorname{Tr}(U^2V^2)\\
&+\left[\operatorname{Tr}(V^4)-4\operatorname{Tr}(UV^3)
               -\|[U,V]\|_{\mathrm{HS}}^2\right].
\end{split}
}\tag{26}
\]

The bracket is not assumed nonpositive. It is the first unpaid combination after the displayed payment. In literal arithmetic terms its cubic factor is

\[
\operatorname{Tr}(UV^3)
=\int_{(L/3,L]^3}
\operatorname{Tr}[U\Pi Q(s_1)\Pi Q(s_2)\Pi Q(s_3)\Pi]
\,d\nu(s_1)d\nu(s_2)d\nu(s_3),
\]

with the four-factor counterpart for \(\operatorname{Tr}V^4\). All of the short prime history and the full archimedean matrix also enter \(U\). Replacing this by a sum over four prime indices alone would change the object.

For arbitrarily large fixed even orders, one sufficient remaining statement is

\[
\boxed{
\begin{gathered}
\exists A_0<\infty\text{ independent of the unbounded set of fixed even orders }p,\\
\forall p\text{ in that set}\ \exists\widetilde C_p,\widetilde B_p,m_0(p):\\
\mathfrak R_{p,m}-\mathfrak C_{p,m}
\le\widetilde C_pm^{A_0}(\log m)^{\widetilde B_p}
\quad\text{for every }m\ge m_0(p).
\end{gathered}
}\tag{27}
\]

**[COFINAL_FAMILY | CONDITIONAL: OPEN obligation]** Equation (27) is **not proved**. Choosing \(A_0=3/2\) would match the paid exponent, but no particular value is made mandatory. Any fixed finite \(A_0\), independent of those orders, would be sufficient through (25). The constants and logarithmic exponents may depend on \(p\).

The exact signed equality in (25) is a weaker interface than estimating the remainder separately. The user's negative-moment target is weaker still than the full positive-moment bound selected here. Failure to bound (27) therefore does not establish that the negative-moment target, SP, or this source family is false.

### 6.4 Strongest attack: the second moment has not paid the retained long cycles

**Objection to any claimed closure:** the pure-long word has coefficient one in every even order. The short-input estimate and the quadratic credit do not bound it together with the remaining mixed words. The scope of (25) must therefore retain exactly the remainder (24); suppressing that remainder would be a false full-moment inference.

The new arithmetic gain in (10) depends on the product support \(y^q\le m\). Applying the same step to the entire prime history produces products as large as \(m^q\). That is **outside the hypothesis of (5)** on the original grid. It is not repaired by calling the frequencies independent or discarding nonidentical products.

Similarly, (20) controls only two long insertions. Applying an operator envelope to every extra \(V\) in (24) produces a power of \(m\) growing with their number; the existing fixed-power zeta floor does not turn that into an order-independent exponent. Such a bound is not an SP gain. Nor does the fact that \(\mathfrak C_{p,m}\ge0\) establish that it dominates the signed sum (24).

The point of (24)–(27) is to expose this exact failure location after a real higher-moment calculation. **The unbounded remainder is not a new supplied theorem.**

## 7. Full-source and account return

The calculation used the expressly permitted endpoint alternative, not the earlier affine-path recurrence. Consequently it did not replace the affine weight \(\overline W_{p,m}\) by a generic weight, and it did not invoke a companion cancellation. The source matrix \(S\) in every trace is exactly \(\Pi_mK_m\Pi_m\); its negative spectral moment is the true functional calculus of that matrix. The full positive even moment bounds that exact negative moment pointwise.

**[COFINAL_FAMILY | PAPER: accepted endpoint return]** The supplied Q4 correction is

\[
K_m=S+J_m^\partial,\qquad
\|J_m^\partial\|\le300L^{7/2}=:b_m^\partial.
\tag{28}
\]

It follows, with no sum over cells, that

\[
\lambda_{\min}(K_m)\ge-\|S_-\|-b_m^\partial.
\tag{29}
\]

This is the accepted endpoint comparison, not a repeated boundary proof. fileciteturn24file0L183-L197 fileciteturn24file0L570-L604

For an explicit moment-level return, ordered-eigenvalue perturbation and \((a+b)^p\le2^{p-1}(a^p+b^p)\) give

\[
\boxed{
\operatorname{Tr}(K_m)_-^p
\le2^{p-1}\left[\operatorname{Tr}S_-^p
                +d(300L^{7/2})^p\right].
}\tag{30}
\]

The added term has polynomial exponent **one**, independently of \(p\); its logarithmic exponent and constant depend on \(p\), as permitted. There is no \(m^{ap}\) normalization. Equation (30) is only the return of a moment estimate once supplied; it does not supply (27).

The original fixed-basis diagonal account, if a return to it is desired, satisfies its inherited scalar Jensen bound
\(\sum_j(-K_{m,jj})_+^p\le\operatorname{Tr}(K_m)_-^p\). Hence its omission from the endpoint proof is not an assumption that it vanishes. The present proof does not claim its affine drift has been paid.

No Q2 contour truncation or Q3 zero cutoff was introduced in (6)–(30), so their truncation fees are neither incurred nor silently set to zero. All of their original terms have already returned through the **literal source (1)–(2)** used here. The only compression fee needed in this endpoint route is (28), paid once. No adjacent-cell transport assertion is used.

## 8. Source-sensitive countercheck and external-mechanism boundary

### 8.1 Actual prime powers do not have termwise Fourier orthogonality

**[FINITE_CELL | PAPER: arithmetic subterm only]** There is a direct control using actual von Mangoldt coefficients on an original grid. Take \(m=16\), \(p=4\), so \(x=16^{1/3}<3\). The four integers

\[
3,\quad13,\quad5,\quad8
\]

are all actual prime powers in the long part, strictly below the endpoint. Their products \(3\cdot13=39\) and \(5\cdot8=40\) differ. The expansion of the fourth moment of the atomic long primitive contains the ordered term

\[
\frac{\Lambda(3)\Lambda(13)\Lambda(5)\Lambda(8)}{\sqrt{1560}}
\mathcal D_{16}\!\left(\frac{\log(40/39)}{\log16}\right).
\tag{31}
\]

Its coefficient is strictly positive; in particular \(\Lambda(8)=\log2\), not zero. Put \(\alpha=\log(40/39)/\log16\). Since
\(0<\log(1+1/39)<1/39\) and \(\log16>2\),
\(0<\alpha<1/78\), hence \(33\alpha<1/2\). Therefore

\[
\mathcal D_{16}(\alpha)
=\frac{\sin(33\pi\alpha)}{\sin(\pi\alpha)}
\ge\frac{66}{\pi}>0.
\tag{32}
\]

Thus the precise shortcut “the actual mode sum annihilates each nonidentical multiplicative product” is false, already for actual coefficients. If its claimed zero upper bound is written as a margin, (31)–(32) give a strictly negative upper envelope for that margin.

**Scope:** this is a countercheck of termwise orthogonality only. It is not a lower bound for the complete atomic fourth moment after all other off-diagonal terms are included, not a lower bound for the signed measure expression (24), and not a negative-spectrum counterexample. The continuous terms, full source matrices, and their cyclic weights can still cancel it. No prime model or actual adaptive density is substituted.

### 8.2 Why the Ramanujan mechanism is not a supplied contraction here

The embedded graph proof has a genuine probability space of allowed transitions, survival-conditional signed means, low-square estimates, and path-coefficient contractions. Its high-moment argument uses those hypotheses before combining its accounts. They are not consequences of the CCM mean-square estimate. fileciteturn29file0L557-L585 fileciteturn30file0L599-L631 fileciteturn30file0L828-L866

Here the actual replacement for a short-input averaging estimate is the proved discrete sampling/convolution calculation (7)–(14). The replacement for higher long-input contraction would have to bound the signed words (24), with the credit (16) retained. **No such graph-to-CCM contraction hypothesis was presumed.**

Likewise, the packet's independently checked phase-mixing identity has an unbounded actual-source remainder. This proof does not rediscover it or declare that the long part equals a dissipative phase increment. The credit (16) comes from the exact polynomial two-insertion sum, not a surrogate evolution. fileciteturn24file0L77-L102

## 9. One precise independent audit target

**Audit Theorem Q05-M, equation (25), as an inequality with its displayed signed remainder—not as a full moment estimate.** The exact scope is every fixed even \(p\ge4\) and every integer \(m\ge2^{p-1}\), on the original \(N=m,L=\log m\) source.

The load-bearing new checks are: the product-support cutoff in (7); the divisor-pair inequality (8) and harmonic sum (9); application of the accepted original-grid sampling estimate; both continuous terms and constants in (12); the diagonal and off-diagonal return (13); the full-background Schatten budget (14); cyclic multiplicity \(p/r\), including periodic words; the sign and factor of the credit (16)–(18); and the constants paying \(\mathcal P_{p,m}\) in (20)–(23). The measure expansion in (24) must preserve every prime power, all atomic/continuous mixtures, all \(\Pi\) insertions, and the full archimedean matrix inside \(U\).

**Acceptance proves only (25).** It does not prove (27), improve the full negative floor, or close SP. A defect should be reported as the first false equality, constant, or quantified domain, with a correction where possible. The accepted Q4 endpoint comparison is an input and is not the new audit target.

### Diagnostic record and registered predictions

Before the calculations and checks, the registered questions were whether coefficient-product counting supplies an order-independent short-input budget, and which signed long terms survive the cyclic expansion. The expected diagnostic identities were the cyclic multiplicities and the retained quadratic credit against the literal source; no successful full-moment or SP prediction was registered.

The PAPER outcomes are (10)–(14), the exact expansion (19), and the credit sign (16). The original-grid product-support restriction is explicit. The first two long-insertion sectors are paid in (23); the higher sectors are not.

Local floating-point diagnostics, **not interval or kernel certificates**, assembled the literal \(W_{0,2}-W_{\mathbb R}-\mathrm{Prime}\) matrix independently of the \(\mathsf B-\mathsf C\) assembly. At \((m,p)=(8,4)\) and \((32,6)\), source reconstruction differed by less than \(2.1\times10^{-13}\) entrywise. Direct matrix powers and the complete rooted cyclic formula differed by less than \(8.1\times10^{-16}\) relative to the full even moment. The \(p=4\) credit agreed with the squared Hilbert–Schmidt commutator norm within \(5.8\times10^{-15}\).

Flipping the credit sign changed the identity by approximately 4.56% and 5.28% of the respective moments. Deleting the pure-long word changed it by approximately 5.06% and 5.00%. A separate deliberately indefinite three-by-three real control also checked the cyclic algebra at orders 4, 6, and 8; that control is not a CCM matrix.

The numerical negative parts at these small cells were near the floating-point floor; **no exact-zero or positivity conclusion is taken from them**. Likewise a scalar credit entry of order \(-10^{-14}\) at order six is numerical cancellation near its exact nonnegative polynomial, not a certified negative value. Equations (8), (16), and (32), not floating-point observations, supply their stated PAPER quantifiers.

The previous Q4 prediction now has the attachment's bounded independent PASS disposition, restricted to its boundary comparison. Its acceptance does not transfer to the present open moment bound. The registered prediction for the requested new independent audit is that (25) survives with its conservative constants; the highest-risk checks are the cutoff product length, the \(p/r\) multiplicity, and the sign of the credit.

## 10. Discriminator and two bounded alternatives

### DISCRIMINATOR

**[FINITE_CELL | CONDITIONAL: proposed interval test, not executed]** For a specified fixed-order proposed remainder bound, define

\[
F_{p,m}=\widetilde C_pm^{A_0}L^{\widetilde B_p}
          -\mathfrak R_{p,m}+\mathfrak C_{p,m}.
\tag{33}
\]

Compute the remainder independently from the literal source through
\(\operatorname{Tr}S^p-\mathcal P_{p,m}\), as well as by the complete word sum, preserving the same \(U,V\). A nonnegative lower enclosure certifies only the stated finite-cell bound. A negative upper enclosure rejects only that specified finite-cell inequality, not a permitted later starting index or a different bound. A straddling enclosure remains inconclusive. A finite prefix does not prove the common-exponent quantifier in (27).

For a purported vanishing negative moment, the discriminating functional is the **actual** \(\operatorname{Tr}[(\Pi K_m\Pi)_-^p]\), using certified spectral enclosures rather than clipping tiny eigenvalues. For the proposed nonnegative credit, the polynomial integral (18) provides an exact sign certificate, including degeneracies; it does not certify the sign of the combined remainder.

### Candidate A: retain the actual negative spectral projector in the word expansion

The selected full-even-moment route is stronger than needed. One alternative is to insert the exact projector \(E_-=\mathbf1_{(-\infty,0)}(S)\) and expand

\[
\operatorname{Tr}S_-^p
=\sum_{\epsilon\in\{0,1\}^p}(-1)^{|\epsilon|}
\operatorname{Tr}\bigl(E_-W_{\epsilon_1}\cdots W_{\epsilon_p}\bigr),
\quad W_0=U,\quad W_1=V.
\]

This preserves the actual negative density and need not control a large positive spectral sector. **Do not reuse the rooted factor \(p/r\) from (15) without a new proof:** \(E_-\) commutes with \(S\), not necessarily with \(U\) or \(V\), so rotating a word also moves the projector. The needed result is an actual source-weighted signed bound, not a generic PSD insertion.

**Kill-power/cost:** high against false adaptive cyclicity or a positive-spectrum loss; low finite algebra setup and high arithmetic-correlation cost. The cheapest decisive check is the full fourth-order expansion with the actual projector retained in every position. No such estimate is supplied here.

### Candidate B: fixed-window signed closed-path/product fibers

Expand the long insertions in (24) through the original finite-window translation operators, retaining the finite Fourier projections between insertions. Group by the partial translation path and its signed multiplicative displacement before comparing atomic and continuous factors. The intervals visited by the partial path and every projection remainder must remain; replacing the finite projections by identities would change the source.

The intended gain would be a bound for the **combined** near-balanced product fibers and their continuous comparison, together with the archimedean \(U\) factors and credit (16). Equation (32) is the first required falsifier against a claim that only exactly balanced products survive. This is a fixed-endpoint calculation, not another old/new physical-window transport argument.

**Kill-power/cost:** high against missing product fibers or discarded projection returns; medium analytic setup and high signed arithmetic-estimate cost. A usable result must bound the full remainder (or a genuinely weaker negative-density expression) with a uniform polynomial exponent. Merely producing the path representation would not be progress.

These are the two candidate changes of representation required by the inconclusive outcome; neither authorizes a large numerical scan or a new unverified mathematical premise. The three concrete bridges tested in this calculation were coefficient-convolution sampling, cyclic matrix-moment algebra with a convexity credit, and the external selected-pair contraction architecture. The first two supply the limited estimates above; the third has no established transfer for the long-source words.

## 11. Claim ledger and closeout

| Claim | Scope | Verifier | Disposition |
|---|---|---|---|
| Full-source flat-vector/mean-square bounds, Q4 boundary return | COFINAL_FAMILY | PAPER | Inherited with reported independent audit; not counted as new |
| Exact source split (6), with original grid and full background | FINITE_CELL | PAPER | All terms retained; no altered carrier |
| Divisor-pair counting inequality (8) | ABSTRACT | PAPER | Derived for every integer and order |
| Short-source joint higher moment (12), full short matrix moment (14) | COFINAL_FAMILY | PAPER | New quantified bounds; polynomial exponent one |
| Rooted cyclic formula (15), credit identity and sign (16)–(18) | FINITE_CELL | PAPER | Exact for the actual matrices; no dephasing substitution |
| Payment of zero-, one-, and two-long-insertion sectors (23) | COFINAL_FAMILY | PAPER | New bounded sector; common exponent 3/2 |
| Full-source partial inequality Q05-M (25) | COFINAL_FAMILY | PAPER | New audit target with explicit unbounded signed remainder |
| Uniform-exponent estimate for (24) minus (16), equation (27) | COFINAL_FAMILY | CONDITIONAL | OPEN obligation; not a supplied theorem |
| Endpoint moment return (30) | COFINAL_FAMILY | PAPER | Complete return from accepted Q4 fee; not a drift sum |
| Actual-prime-power termwise orthogonality countercheck (31)–(32) | FINITE_CELL | PAPER | Rejects that shortcut only; not a CCM spectral counterexample |
| Full-floor improvement, SP, RH | COFINAL_FAMILY | CONDITIONAL | Not established; no claim made |

**What became smaller:** an original-grid short arithmetic input now has a higher Schatten moment with polynomial exponent one, for every fixed order used here. That estimate and the accepted full mean square pay the first two long-insertion sectors with a common exponent \(3/2\), while retaining a nonnegative quadratic credit. The first unpaid part has at least three long insertions.

**What did not become smaller:** the established exponent of the full negative floor. The remainder may contain the entire difficult part of the full source. The quantified partial sector is not an order-independent estimate of the full moment. The requested consumer remains **NO_PROGRESS**.

**What was ruled out:** termwise annihilation of all unequal multiplicative products on the actual mode grid. No actual negative-spectrum assertion or route family was killed.

**What must not be tried again:** treating (5) as valid with product length \(m^{p-1}\) at no cost; treating the flat-vector bounds as a full-span polylogarithmic norm; replacing the actual long-source factors by independent ones; dropping \(\mathfrak R\), the mixed cubic term, or the quadratic credit; or summing the endpoint correction as a drift fee.

**Smallest unpaid sum:** \(\mathfrak R_{p,m}-\mathfrak C_{p,m}\) in (24), (16), with the literal order-four bracket (26) as its first instance. A uniform upper bound for it is one sufficient interface, not a necessary one for the original negative-moment target.

**Minimal missing estimate:** (27), or a source-aligned negative-projector estimate that directly bounds \(\operatorname{Tr}S_-^p\) with a common polynomial exponent. This is an OPEN mathematical obligation, not an external theorem imported by name.

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
  ACTUAL_CONSUMER_REQUIREMENT: "For every eta>0, an eventual bound lambda_min(K_m)>=-C_eta*m^eta on every original full cell. No RH export is made."
  ORIGINAL_REQUESTED_OBJECT: "An order-independent polynomial exponent for arbitrarily large fixed even negative moments of Pi_m*K_m*Pi_m, with the accepted full-source endpoint return."
  ORIGINAL_OBJECT_IS: PROVED_NECESSARY
  NECESSITY_NOTE: "At the dependency-contract level only: SP implies the requested negative-moment shape with exponent 2 by choosing eta=1/p and using d<=3m; conversely the already-known receiver and Q4 endpoint return apply. This is not new supplier progress. Necessity of the selected full positive-moment estimate, the short cutoff, or the separate remainder bound (27) is UNKNOWN."
  KNOWN_WEAKER_INTERFACES:
    - "A bound on the exact signed total in (25), without separately upper-bounding its remainder, can imply the full positive-moment target."
    - "A bound on the actual negative spectral moment alone need not control the positive spectral sector and reaches the requested interface through (28)-(30)."
    - "A direct every-eta lower floor on the unchanged full K_m reaches the consumer without this moment split."
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "Actual prime-power convolution on the original grid pays a short-source high moment; cyclic counting retains a nonnegative quadratic credit and explicitly budgets the first two long-insertion sectors."
  REOPEN_TRIGGER: "An order-independent upper bound for the full signed long-cycle remainder with its credit retained, or a weaker actual negative-density estimate with a complete source return."
  MATHEMATICAL_IMPOSSIBILITY_EVIDENCE: NONE_FOR_CCM_MOMENT_TARGET_OR_SP
AUXILIARY_COUNTERCHECK:
  REJECTED_SHORTCUT: "The original finite mode sum annihilates every unequal multiplicative-product cross term of the actual atomic long primitive."
  SCOPE: FINITE_CELL
  VERIFIER: PAPER
  EVIDENCE: "Equations (31)-(32), m=16, actual prime powers 3,13,5,8."
  MARGIN_UPPER_ENVELOPE: "0 minus the positive lower bound for the displayed ordered cross term; strictly negative."
  DOES_NOT_REJECT: "Cancellation of the complete signed source; an eventual moment bound; any actual negative spectral density estimate."
PREDICTION_FATES:
  ORIGINAL_GRID_SHORT_PRODUCT_BUDGET: REGISTERED_TEST_QUESTION_RESOLVED_BY_PAPER_CALCULATION_NO_PRIOR_DIRECTIONAL_FORECAST_CLAIMED
  ROOTED_CYCLIC_MULTIPLICITIES: CONFIRMED_BY_PAPER_IDENTITY_AND_NONCERTIFYING_DIAGNOSTICS
  QUADRATIC_CREDIT_SIGN_AND_RETURN: CONFIRMED_BY_PAPER_CALCULATION_PENDING_INDEPENDENT_AUDIT
  PRIOR_Q4_BOUNDARY_COMPARISON: REPORTED_INDEPENDENT_PASS_WITH_BOUNDARY_ONLY_SCOPE
  FULL_MOMENT_SUCCESS: NOT_REGISTERED_AND_NOT_OBTAINED
MEMORY_ENTRY:
  iteration: FULL_CCM_MOMENT_Q05
  target: ORIGINAL_FULL_SOURCE_ORDER_INDEPENDENT_HIGH_MOMENTS
  status: OPEN
  cognitive_operator_used: LITERATURE_BRIDGE
  consumer_progress: NO_PROGRESS
  paid_term: "Short-source 2(p-1)-moment; all zero/one/two-long insertion words up to a retained nonnegative credit."
  failed_strategy: "Extending a coefficient-length-limited mean-square estimate to unrestricted higher long-source cycles."
  smallest_unpaid_input: "R_(p,m)-Ccredit_(p,m), with all source signs and projections retained."
  invariant_learned: "Powering length x consumes length x^(p-1); actual finite mode sums do not erase every unequal product."
  forbidden_future_move: "Calling the m^(3/2) partial-sector budget a bound for the full moment, or treating the p-dependent short cutoff as deletion of the long history."
  next_decisive_test: "One PAPER audit of Q05-M (25); any later consumer advance requires a genuinely signed bound on the retained long-cycle sum or a weaker exact negative-density target."
```

**Final proposal:** retain the proved short-input moment and the explicit partial cyclic inequality as bounded results. Submit (25) to the single independent audit. Do not infer the full order-independent moment bound from it, and do not count another representation of the same unbounded long-cycle sum as a consumer advance.

## CODEX DIRECTIVE

Independently audit **Theorem Q05-M, equation (25), only**, for the original full CCM source, every fixed even \(p\ge4\), and every integer \(m\ge2^{p-1}\). Check the exact arithmetic split, product-support sampling, divisor-pair count, both continuous terms, full archimedean contribution, cyclic factor \(p/r\), nonnegative credit, and constants in the paid partial bound. Verify that the complete long-source tensor sum and the accepted one-endpoint boundary return are retained. Return either this PAPER inequality **with its unbounded remainder explicitly present**, or the first false identity, coefficient, or domain and a corrected statement. Acceptance must not be reported as a full moment bound, a better full floor, SP, or RH. Do not run Lean or Comparator, edit the repository, or substitute a generic/random spectral weight.
