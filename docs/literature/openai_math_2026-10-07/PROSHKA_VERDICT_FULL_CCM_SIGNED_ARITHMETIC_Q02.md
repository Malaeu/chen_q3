# STATUS: TRY_RH_SOURCE_ARITHMETIC

```yaml
OPERATIVE_CLASS: TRY_RH_SOURCE_ARITHMETIC
VERDICT_CODE: FULL_CCM_MOMENT_Q02_SIGNED_RESOLVENT_PAIRING_SUMMABLE_TRUNCATION_MAIN_SIGN_OPEN
REQUEST: PROSHKA_CCM_MOMENT_Q02.txt
REQUEST_SHA256: 28140eaa6a68afa3c70e8749dd6f21ec6fbae999d0b923924dce7839beea085f
REQUEST_BYTES: 257339
SOURCE_BASELINE: eae28f4c
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
FRONT: FULL_CCM_COUPLED_MOMENT_DRIFT
SOURCE_OBJECT: CCM_LITERAL_FULL_MATRIX_N_EQUALS_M
SCHEDULE: "m integer; N=m; L=log(m); every sufficiently late original cell"
HONESTY_STATE: CHALLENGER_NOT_RH
ADJUDICATION: INCONCLUSIVE_FOR_REQUESTED_SIGNED_GAIN
REQUESTED_DRIFT_GAIN: NOT_OBTAINED
FULL_FLOOR_IMPROVEMENT: NONE
NEW_REPRESENTATION: "exact two-channel inverse-Laplace contraction of the full adaptive weight on both grids"
NEW_PAID_TERM: "full source-specific Perron truncation error at height (m+1)^2 is bounded by a summable coefficient times Tr(T)"
NEW_PAID_TERM_SCOPE: COFINAL_FAMILY
NEW_PAID_TERM_VERIFIER: CONDITIONAL
CONDITIONAL_INPUT: "ZF78, in the packet's reported zeta-only Comparator scope; the log-derivative consequence is stated explicitly"
FIRST_UNPAID: "finite-height signed pairing J_(sigma,(m+1)^2) minus the original new-mode credit; alternatively minus Gamma"
FIRST_UNPAID_BUDGET: "J-credit <= Z_p(m)/(p*m) + v_(p,m)*Z_p(m)/p; v>=0; sum v<infinity"
SP_STATUS: OPEN
RH_STATUS: OPEN
PX_RH_CLAIM: NOT_MADE
KILL_SCOPE: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ZF78_STATUS: REPORTED_ZETA_COMPARATOR_ACCEPTED_NOT_RERUN_HERE
DIRICHLET_HECKE_SIEGEL_IMPORTS: NONE
REPO_EDITS: NONE
LEAN_RUN: NONE
ARB_INTERVAL_RUN: NONE
EVIDENCE_STATE: PAPER_DERIVED_NOT_INDEPENDENTLY_AUDITED
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CONSUMER_PROGRESS: NO_NEW_SIGNED_DRIFT_OR_FLOOR_BOUND
ROUTE_SCORE: 3
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
INDEPENDENT_AUDIT_TARGET: "Theorem (18), including the causal two-channel identity (7), integer-spacing error, both endpoint artifacts, and contour deformation"
```

## 1. Result and boundary

**The requested signed central estimate is not proved. There is no improvement of the full floor exponent and no SP conclusion.** The concrete calculation below replaces the full adaptive prime–pole contraction by an exact, two-channel resolvent integral. It then pays the entire truncation error at height \((m+1)^2\) with a summable original-schedule budget. The unresolved part is a single explicitly displayed finite-height signed integral, with the original new-mode credit—or the larger full credit—still attached.

This is not another proof of Q1's background inequality, the moment criterion, or spectral commutation. Those are accepted inputs, with exactly the restrictions recorded in the packet. In particular, substituting \(K=B-C\) into the full credit gives back the endpoint moment increment; that substitution is not used as a signed supplier here. The task and the independently checked exclusion of that shortcut are in Q02, lines 4–10 and 20–65. fileciteturn3file0L4-L10 fileciteturn3file0L20-L65

The attachment was read in full. Its 257,339 bytes have the requested SHA-256. The bootstrap was fetched anew from `Malaeu/chen_q3`, branch `rh_clean`, and has the blob recorded above. No repository file was edited, and no Lean, Comparator, or interval-verification run was performed.

**What is new, quantitatively.** Fix \(0<\epsilon<1/8\), set \(\sigma=3/8+\epsilon\), and let \(A_\epsilon\ge1\) be the explicitly specified logarithmic-derivative constant in (9). For \(m\ge6\), put \(M=m+1\), \(L=\log m\), \(L_+=\log M\). The derived estimate is

\[
\boxed{
 \left|\Xi_{p,m}-\mathcal J_{\sigma,M^2}(\mathsf T)\right|
 \le r_{\epsilon,m}\operatorname{Tr}\mathsf T,
 \quad
 r_{\epsilon,m}=16M^{-3/2}
 +(10000L_++300A_\epsilon+20)M^{-5/2}.
} \tag{1}
\]

Here \(\mathsf T=\overline W_{p,m}\) is the **actual full adaptive weight**, not an independent or frozen surrogate. Its definition and the completely explicit integral \(\mathcal J\) are given below. For each fixed \(\epsilon\), \(\sum_m r_{\epsilon,m}<\infty\). The elementary truncation argument on the absolutely convergent Dirichlet-series line is unconditional; moving that line to \(\sigma\) uses the named zeta input.

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** Equation (1) is a paid error estimate, not the missing signed estimate for its central integral. Its multiplication by a fixed moment order \(p\) remains summable. No claim is made that its smallness makes the central integral small.

## 2. Only the inherited definitions needed for this calculation

**[FINITE_CELL | PAPER]** Let \(I_r=\{-r,\ldots,r\}\), \(d_r=2r+1\), \(L_r=\log r\), and

\[
 \omega_j^{(r)}=\frac{2\pi j}{L_r}.
\]

Use the literal source kernel

\[
 Q_{r,L_r}(s)_{jk}=
 \begin{cases}
 2(1-s/L_r)\cos(\omega_j^{(r)}s),&j=k,\\[1mm]
 \dfrac{\sin(\omega_k^{(r)}s)-\sin(\omega_j^{(r)}s)}{\pi(j-k)},&j\ne k,
 \end{cases}
 \quad 0\le s\le L_r. \tag{2}
\]

Its branches, carrier, and normalization are locked by the attached constructor. The original paper likewise uses the zero-extended Fourier basis on \([0,L]\); no different test class is introduced. fileciteturn3file0L334-L345 fileciteturn3file0L2111-L2132 citeturn355102view0

The joint measure and arithmetic matrix are

\[
 d\nu(s)=\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}\delta_{\log q}(ds)
 -(e^{s/2}-e^{-s/2})\,ds,
 \qquad
 \mathsf C_r=\int_{[0,L_r]}Q_{r,L_r}(s)\,d\nu(s).
 \tag{3}
\]

This is Q1's exact \(K_r=\mathsf B_r-\mathsf C_r\) decomposition. Every prime power remains present with its actual von Mangoldt weight; the growing and decaying continuous terms have their original relative signs. fileciteturn3file0L361-L379

Retain the full affine endpoint path and weight

\[
\begin{split}
 H_t&=\widehat K_m+t(K_M-\widehat K_m),\\
 G_t&=(H_t)_-^{p-1},\qquad
 D_t=\operatorname{diag}\bigl((-H_{t,jj})_+^{p-1}\bigr),\\
 \mathsf T&=\int_0^1(G_t+D_t)\,dt\succeq0,\\
 \Xi_{p,m}&=\operatorname{Tr}\bigl(\mathsf T(\mathsf C_M-\widehat{\mathsf C}_m)\bigr).
\end{split} \tag{4}
\]

The hats mean zero-padding onto the two new labels. The source matrices are real symmetric, so \(\mathsf T\) is real symmetric and positive semidefinite; this does not restrict the original complex carrier. The old block \(\mathsf T_{oo}\) is the principal block of this **full** weight. It is not replaced by a spectral function of an isolated old block. These are exactly the inherited objects. fileciteturn3file0L607-L650

The two admissible credits are kept separate:

\[
 c_{p,m}=\frac L{64}\operatorname{Tr}(P_{\rm new}\mathsf T),
 \qquad
 \Gamma_{p,m}=\operatorname{Tr}\!\left[
 \mathsf T\left(\Delta\mathsf B+\frac{5000}{mL}I\right)\right]
 \ge c_{p,m}.
 \tag{5}
\]

Neither credit is set to zero or re-derived. fileciteturn3file0L816-L827

## 3. Execute the source contraction: two causal resolvent channels

### 3.1 The source transform and the cancelled pole

**[ABSTRACT | PAPER]** For \(\Re z>1/2\), absolute convergence gives

\[
\begin{split}
 \mathfrak a(z)&:=\int_0^\infty e^{-zs}\,d\nu(s)\\
 &=-\frac{\zeta'}{\zeta}\left(\frac12+z\right)
   -\frac1{z-1/2}+\frac1{z+1/2}.
\end{split} \tag{6}
\]

At \(z=1/2\), the residue of the first term is \(+1\), and the residue of the second is \(-1\). Thus the growing pole cancels **before** contour movement or an absolute estimate. The rational continuous contribution is

\[
 -\frac1{z-1/2}+\frac1{z+1/2}=-\frac1{z^2-1/4}.
\]

The latter identity will also pay the continuous-tail error without splitting the two continuous terms into unrelated bounds.

### 3.2 A finite-section identity with both branches intact

Define, for \(j\in I_r\),

\[
 b_{r,\pm}(z)_j=\frac1{z\pm i\omega_j^{(r)}},
 \qquad
 \mathsf S_r(z)=\frac1{L_r}
 \left(b_{r,+}(z)b_{r,+}(z)^{\mathsf T}
      +b_{r,-}(z)b_{r,-}(z)^{\mathsf T}\right).
\]

The superscript \(\mathsf T\) is **transpose**, not conjugate transpose. Each integrand has at most two channels; the integrated matrix is not asserted to have rank two.

**[FINITE_CELL | PAPER]** On any line \(\Re z=c>1/2\),

\[
\boxed{
 \mathsf C_r=\frac1{2\pi i}\int_{c-i\infty}^{c+i\infty}
 r^z\mathfrak a(z)\mathsf S_r(z)\,dz.
} \tag{7}
\]

Here is the direct source calculation, including the diagonal, rather than a formal transform substitution. For two mode frequencies define

\[
 k_{jk}^{\pm}(u)=
 \begin{cases}
 u e^{\mp i\omega_j u},&u\ge0,\ j=k,\\[1mm]
 \dfrac{e^{\mp i\omega_j u}-e^{\mp i\omega_k u}}
 {\pm i(\omega_k-\omega_j)},&u\ge0,\ j\ne k,\\[1mm]
 0,&u<0.
 \end{cases}
\]

This is the causal convolution of \(e^{\mp i\omega_j u}\mathbf1_{u\ge0}\) and \(e^{\mp i\omega_k u}\mathbf1_{u\ge0}\). Its Laplace transform is

\[
 \frac1{(z\pm i\omega_j)(z\pm i\omega_k)}.
\]

At \(u=L_r-s\), the exact integer-grid identity \(e^{\pm i\omega_j L_r}=1\) yields

\[
 \frac{k_{jk}^+(L_r-s)+k_{jk}^-(L_r-s)}{L_r}
 =Q_{r,L_r}(s)_{jk}.
 \tag{8}
\]

For \(j=k\), this is precisely \(2(1-s/L_r)\cos(\omega_js)\). For \(j\ne k\), summing the two exponentials gives the off-diagonal branch in (2), with denominator \(\pi(j-k)\) and its original sign.

Insert (6) into (7). Termwise inverse transformation is justified on \(c>1/2\): the Dirichlet coefficients are absolutely summable there, while the fixed finite-section transfer matrix decays as \(|\Im z|^{-2}\). Equation (8) recovers the entire prime-power sum and both continuous integrals in (3). Terms with \(q>r\) have \(L_r-\log q<0\) and vanish by causality. At \(q=r\), the causal convolution is exactly zero, including its repeated-pole diagonal branch. This proves (7).

This return to the sharp cutoff matters. The infinite Euler product in (6) is an analytic device, not a replacement prime process: all terms beyond the original endpoint return exactly zero in the untruncated formula. At a truncated height their return error is paid in Section 5.

### 3.3 Contour movement and the explicit zeta dependency

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** Fix \(0<\epsilon<1/8\) and \(\sigma=3/8+\epsilon\). Use the following quantitative consequence of the packet's zeta-only input:

\[
\boxed{
 \exists A_\epsilon\ge1\ \forall x\in[\sigma,3/2]\ \forall t\in\mathbb R:
 \quad |\mathfrak a(x+it)|\le A_\epsilon\log(|t|+3).
} \tag{9}
\]

The first argument of \(\zeta'/\zeta\) is at least \(7/8+\epsilon\), separated by \(\epsilon\) from every nontrivial zero. The local zero-count/partial-fraction argument already supplied in the packet gives (9) at large heights; compactness gives its remaining bounded-height constant after the pole in (6) is cancelled. This is the same zeta log-derivative input, not a character-family estimate. The relevant source transfer and proof of the local partial-fraction bound are attached. fileciteturn3file0L1205-L1223 fileciteturn3file0L1519-L1533

The packet reports a successful zeta-only Comparator check and lists its trust boundary. That reported scope is retained. It was not rerun here, and no Dirichlet, Hecke, or Siegel conclusion is inferred. The `CONDITIONAL` tags in this derivation expose the named dependency; they do not replace the packet's accepted report with the older statement-inspection status. fileciteturn3file0L1264-L1318

There is no pole of \(\mathfrak a(z)\mathsf S_r(z)\) between \(\Re z=c\) and \(\Re z=\sigma\). The poles of \(\mathsf S_r\) lie on \(\Re z=0\); the growing zeta pole was cancelled. On horizontal sides the integrand is \(O_{r,\epsilon}(\log |t|/t^2)\). Therefore (7) also holds on \(\Re z=\sigma\), with an absolutely convergent vertical integral.

## 4. The full adaptive pairing and its actual grid motion

**[FINITE_CELL | PAPER, with (7) on the chosen admissible line]** Define the explicit scalar transfer

\[
\boxed{
\begin{split}
 U_{p,m}(z)
 ={}&\frac{M^z}{L_+}\sum_{\pm}
       b_{M,\pm}(z)^{\mathsf T}\mathsf T b_{M,\pm}(z)\\
 &-\frac{m^z}{L}\sum_{\pm}
       b_{m,\pm}(z)^{\mathsf T}\mathsf T_{oo}b_{m,\pm}(z).
\end{split}
} \tag{10}
\]

Then the requested signed arithmetic contraction is exactly

\[
\boxed{
 \Xi_{p,m}=\frac1{2\pi}\int_{-\infty}^{\infty}
 \mathfrak a(\sigma+it)U_{p,m}(\sigma+it)\,dt.
} \tag{11}
\]

This is an identity for the actual adaptive \(\mathsf T\). Holding its already defined value fixed while executing a linear integral does not assume independence between \(\mathsf T\) and the source that generated it.

### 4.1 Both new modes and every cross coupling

For one sign, let \(b_o(\ell,z)\) have coordinates \((z\pm2\pi ij/\ell)^{-1}\), \(j\in I_m\). At \(\ell=L_+\), let \(b_n(z)\) be the two coordinates labelled \(-M,M\). The corresponding summand of (10) is exactly

\[
\begin{split}
 &\int_L^{L_+}\frac{e^{z\ell}}\ell
 \left[
 \left(z+\frac1\ell\right)b_o^{\mathsf T}\mathsf T_{oo}b_o
 -\frac{2z}\ell(b_o^{\circ2})^{\mathsf T}\mathsf T_{oo}b_o
 \right]d\ell\\
 &\quad+\frac{M^z}{L_+}
 \left[2b_o(L_+,z)^{\mathsf T}\mathsf T_{on}b_n(z)
       +b_n(z)^{\mathsf T}\mathsf T_{nn}b_n(z)\right].
\end{split} \tag{12}
\]

Here \(b_o^{\circ2}\) means componentwise squaring, and the block order is old labels followed by the two new labels. To verify the formula, differentiate

\[
 \partial_\ell b_o=\ell^{-1}(b_o-zb_o^{\circ2})
\]

and then differentiate \(e^{z\ell}b_o^{\mathsf T}\mathsf T_{oo}b_o/\ell\). The final line of (12) is the exact block expansion at the new endpoint. No neighboring modes are omitted.

Equation (12) is a calculation of the real grid change, not a new path defining the production matrices. It may be used inside the finite-height integral below. Its differentiated summands must not be bounded separately in the infinite tail: doing so would destroy the extra cancellation obtained by the exact \(\ell\)-integration.

The old principal block in (10), followed by the explicit mixed blocks in (12), also prevents the forbidden \(h\)-padding shortcut. It never replaces the padded old source by a full-size Hilbert commutator of a padded \(h\)-vector. The nonzero interface recorded in Q1 is consequently retained, not cancelled by notation. fileciteturn3file0L737-L749

### 4.2 What the eigenvalue-changing weight actually does

Choose a real orthonormal eigenbasis \(H_tu_\alpha(t)=\lambda_\alpha(t)u_\alpha(t)\). For either channel,

\[
\begin{split}
 b^{\mathsf T}\mathsf T b
 =\int_0^1\Bigg[
 &\sum_\alpha(-\lambda_\alpha(t))_+^{p-1}
       \bigl(u_\alpha(t)^{\mathsf T}b\bigr)^2\\
 &+\sum_j(-H_{t,jj})_+^{p-1}b_j^2
 \Bigg]dt.
\end{split} \tag{13}
\]

For the old channel, use the old coordinates of the same full eigenvectors. Within a repeated eigenspace the entire projector contribution is retained; the expression is independent of the real basis chosen in that eigenspace.

Thus the computation has not discarded the eigenvalue-changing residual. It has expressed it as explicit squared rational evaluations against the full negative spectral density and the separate diagonal density. The second line of (13) remains present. Spectral commutation does not erase it, and the first line is not a commutator trace either.

## 5. A signed integer-lattice calculation pays the truncation error

The gain in this section comes from performing the oscillatory tail integral **before** taking the absolute prime sum. Bounding \(\mathfrak a\) absolutely on the left line would not give this summable error at height \(M^2\).

### 5.1 Tail kernels before the absolute sum

**[FINITE_CELL | PAPER]** Set

\[
 H=M^2,\qquad c=\frac12+\frac1{L_+}.
\]

For \(m\ge6\), both grids satisfy \(H\ge2\max_j|\omega_j^{(r)}|\), \(r=m,M\). Indeed, \(x/\log x\) is increasing for \(x>e\), and \(M\log M\ge7\log7>4\pi\). For \(|t|\ge H\),

\[
 \|\mathsf S_r(c+it)\|\le\frac{8d_r}{L_rt^2},
 \qquad
 \left\|\frac d{dt}\mathsf S_r(c+it)\right\|
 \le\frac{32d_r}{L_r|t|^3}.
 \tag{14}
\]

Indeed, each channel vector has norm at most \(2\sqrt{d_r}/|t|\), and its derivative has norm at most \(4\sqrt{d_r}/t^2\). Apply the product rule to both transpose outer products. These are finite-section operator-norm estimates; there is one factor \(d_r\), not \(d_r^2\).

For a prime-power index \(q\), put \(u=\log(r/q)\). Its omitted inverse-transform tail is bounded by

\[
\boxed{
 \left\|\frac1{2\pi}\int_{|t|>H}
 (r/q)^c e^{itu}\mathsf S_r(c+it)\,dt\right\|
 \le (r/q)^c\frac{d_r}{\pi L_r}
 \min\left(\frac8H,\frac{24}{H^2|u|}\right).
} \tag{15}
\]

For \(u=0\), use the first bound. For \(u\ne0\), integrate by parts separately on the two tails. On one tail, the boundary contribution costs \(8d_r/(L_rH^2|u|)\), and the integrated derivative costs \(16d_r/(L_rH^2|u|)\). Two tails and the factor \(1/(2\pi)\) give \(24\). This is the point at which the actual oscillatory sign is used.

### 5.2 The sharp integer endpoint and all other integers

The endpoint \(q=r\) has zero **full** kernel value by (8), but its truncated inverse integral need not be zero. Its error must therefore be paid rather than silently omitted. Its contribution to the error bound for \(\mathsf C_r\) is

\[
 \frac{8d_r}{\pi L_rH}\frac{\Lambda(r)}{\sqrt r}.
\]

This is an inverse-transform truncation artifact, not a new atom or jump in the physical moment. In particular, \(q=m\) is a zero endpoint for the old matrix but remains an ordinary, generally nonzero historical term in the new matrix.

For every other integer, define

\[
 S_r(c)=\sum_{q\ge2,\,q\ne r}
 \frac{\Lambda(q)}{\sqrt q}(r/q)^c\frac1{|\log(r/q)|}.
\]

**[COFINAL_FAMILY | PAPER]** The elementary integer-spacing estimate is

\[
 \boxed{S_r(c)\le100\sqrt r\,L_+^2,
 \qquad r=m,M,\quad m\ge6.} \tag{16}
\]

Proof: write \(\kappa=1/L_+\le1\). In \(r/2\le q\le2r\), \(q\ne r\), use

\[
 |\log(r/q)|\ge\frac{|r-q|}{2r},\qquad
 \frac{\Lambda(q)}{\sqrt q}(r/q)^c
 \le\frac{4\log(2r)}{\sqrt r}.
\]

The two harmonic sums are at most \(2(1+\log r)\). This part is at most

\[
 16\sqrt r\log(2r)(1+\log r)\le64\sqrt rL_+^2.
\]

Outside that interval the logarithmic denominator is at least \(\log2\). Also,

\[
 \sum_{q\ge2}\frac{\log q}{q^{1+\kappa}}
 \le\int_1^\infty\frac{\log2+\log x}{x^{1+\kappa}}\,dx
 =\frac{\log2}{\kappa}+\frac1{\kappa^2}
 \le\frac2{\kappa^2}.
\]

Since \(r^c\le e\sqrt r\), the far part is at most
\(2e\sqrt rL_+^2/\log2<8\sqrt rL_+^2\). The displayed constant \(100\) safely covers the sum. This argument retains every proper prime power; using \(\Lambda(q)\le\log q\) is an upper bound, not a change of source.

### 5.3 Both continuous pole terms, together

On \(\Re z=c\), their combined transform is \(-1/(z^2-1/4)\), whose modulus is at most \(|t|^{-2}\). Consequently their omitted tail has norm at most

\[
 \frac{8r^cd_r}{3\pi L_rH^3}
 \le\frac{8e\sqrt r\,d_r}{3\pi L_rH^3}.
\]

Combining the preceding bounds, the error for one endpoint on the line \(c\) is at most

\[
 E_r^{\rm right}\le
 \frac{8d_r\Lambda(r)}{\pi L_r\sqrt rH}
 +\frac{2400d_r\sqrt rL_+^2}{\pi L_rH^2}
 +\frac{8e\sqrt r\,d_r}{3\pi L_rH^3}.
 \tag{17}
\]

This step is an unconditional estimate on the entire sharp-cutoff source. The apparently future terms \(q>r\) occur only in estimating the truncation error of the Euler-product representation; their exact causal return was already proved zero.

### 5.4 Move the finite rectangle, with its horizontal return paid

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** Use (9) on the two horizontal segments from \(\sigma\pm iH\) to \(c\pm iH\). The width is less than one for \(m\ge6\). Their combined normalized contribution for endpoint \(r\) is at most

\[
 E_r^{\rm horizontal}
 \le\frac{8eA_\epsilon d_r\sqrt r}{\pi L_rH^2}\log(H+3).
\]

The cancelled growing pole creates no residue. No zero is crossed. The transfer poles remain on the imaginary axis to the left of both lines.

Now contract the new-endpoint error with \(\mathsf T\succeq0\), and the old-endpoint error with \(\mathsf T_{oo}\succeq0\). Use \(\operatorname{Tr}\mathsf T_{oo}\le\operatorname{Tr}\mathsf T\), \(d_r\le3r\), \(L_+/L\le2\), and \(\log(M^2+3)\le3L_+\). With \(H=M^2\), the two-endpoint coefficient is at most

\[
 16M^{-3/2}+10000L_+M^{-5/2}
 +14L^{-1}M^{-9/2}+250A_\epsilon M^{-5/2}.
\]

Therefore the following complete statement is proved in PAPER form:

\[
\boxed{
\begin{gathered}
 \forall\epsilon\in(0,1/8)\ \exists A_\epsilon\ge1\text{ satisfying (9)},\\
 \forall m\ge6\ \forall\mathsf T=\mathsf T^{\mathsf T}\succeq0:\\
 \left|\operatorname{Tr}\bigl[\mathsf T(\mathsf C_M-\widehat{\mathsf C}_m)\bigr]
       -\mathcal J_{\sigma,M^2}(\mathsf T)\right|
 \le\left[16M^{-3/2}+(10000L_++300A_\epsilon+20)M^{-5/2}\right]
       \operatorname{Tr}\mathsf T,\\
 \mathcal J_{\sigma,H}(\mathsf T)
 :=\frac1\pi\Re\int_0^H
     \mathfrak a(\sigma+it)U_{p,m}(\sigma+it)\,dt.
\end{gathered}
} \tag{18}
\]

The notation \(U_{p,m}\) records the application to the adaptive weight; the formula is linear in any displayed \(\mathsf T\). Its real-conjugation symmetry justifies replacing the symmetric integral by twice the real part on \([0,H]\).

For example, a completely explicit tail budget is

\[
\begin{split}
 \sum_{m\ge n}r_{\epsilon,m}\le{}&32n^{-1/2}\\
 &+10000n^{-3/2}\left(\frac23\log n+\frac49\right)
 +\frac23(300A_\epsilon+20)n^{-3/2},\qquad n\ge6.
\end{split} \tag{19}
\]

Thus the paid estimate is genuinely cofinal and summable; finite diagnostics play no role in its quantifier.

## 6. Return to the original residual, without spending a credit twice

**[FINITE_CELL | PAPER / COFINAL_FAMILY | CONDITIONAL: ZF78 for the error]** Define

\[
 \mathcal R_{p,m}^{\epsilon}
 =\mathcal J_{\sigma,M^2}(\mathsf T)
       -\frac L{64}\operatorname{Tr}(P_{\rm new}\mathsf T).
\]

Equations (4), (5), and (18) give the executed residual estimate

\[
\boxed{
 \Omega_{p,m}=\mathcal R_{p,m}^{\epsilon}+\mathcal E_{p,m},
 \qquad |\mathcal E_{p,m}|\le r_{\epsilon,m}\operatorname{Tr}\mathsf T.
} \tag{20}
\]

For the weaker full-credit version, exactly the same statement holds with

\[
 \widetilde{\mathcal R}_{p,m}^{\epsilon}
  =\mathcal J_{\sigma,M^2}(\mathsf T)-\Gamma_{p,m},
 \qquad
 \Xi_{p,m}-\Gamma_{p,m}
  =\widetilde{\mathcal R}_{p,m}^{\epsilon}+\mathcal E_{p,m}.
 \tag{21}
\]

No value of \(\Gamma\) was obtained by substituting the desired endpoint moment change.

For clarity about the return cost, use Q1's already accepted bounds
\(\operatorname{Tr}\mathsf T\le Z_p(m)+Z_p(M)\) and
\(b_{p,m}=5000p/(mL)\). They give, directly from its paid-background inequality,

\[
 (1-b_{p,m}-pr_{\epsilon,m})Z_p(M)
 \le(1+b_{p,m}+1/m+pr_{\epsilon,m})Z_p(m)
       +p\mathcal R_{p,m}^{\epsilon}.
 \tag{22}
\]

This is only the algebraic return of the new error budget, not a new derivation of the moment criterion. Since \(pr_{\epsilon,m}\) is summable for each fixed \(p\), it can be absorbed after a finite \(p\)-dependent starting index. Q1's trace bound and original signed consumer are recorded in the packet. fileciteturn3file0L97-L124

### First unpaid arithmetic expression

**[COFINAL_FAMILY | CONDITIONAL: OPEN hypothesis]** The still-needed statement is

\[
\boxed{
 \begin{gathered}
 \text{For arbitrarily large fixed even }p,
 \text{ there exist }m_0(p),\ v_{p,m}\ge0,\\
 \sum_{m\ge m_0(p)}v_{p,m}<\infty,\qquad
 \frac1\pi\Re\int_0^{(m+1)^2}
 \mathfrak a(3/8+\epsilon+it)U_{p,m}(3/8+\epsilon+it)\,dt\\
 \hspace{8mm}-\frac{\log m}{64}\operatorname{Tr}(P_{\rm new}\mathsf T)
 \le\frac{Z_p(m)}{pm}+\frac{v_{p,m}}pZ_p(m).
 \end{gathered}
} \tag{23}
\]

Replacing the displayed credit by \(\Gamma_{p,m}\) gives the weaker sufficient interface. A single fixed \(\epsilon\), for example \(1/16\), suffices to formulate this target; no improvement of ZF78 is silently assumed.

For a check of constants in the interface only: eventually
\(b_{p,m}+pr_{\epsilon,m}\le1/(2m)\). Inserting (23) into (22) then gives
\(Z_p(M)\le(1+4/m+2v_{p,m})Z_p(m)\). This explains why the new truncation fee is admissible, without re-proving the inherited high-moment receiver. **The premise (23) remains unproved.**

An alternative sufficient tail statement is convergence of

\[
 \sum_m\left(\frac{p\mathcal R_{p,m}^{\epsilon}}{Z_p(m)}-\frac1m\right)_+,
 \tag{24}
\]

or its full-credit version. Its finite-height integrand is now explicit in (6), (10), and (13), and all contour-return costs have already been budgeted. This is the remaining arithmetic–spectral correlation, not a condition on an arbitrary replacement matrix.

## 7. Attempted sign extraction and the precise point where it fails

### 7.1 The available magnitude does not pay the central pairing

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** After the signed calculation above, one can audit what the available absolute input buys. For real \(\mathsf T\succeq0\),

\[
 |b^{\mathsf T}\mathsf T b|\le b^*\mathsf T b.
\]

The Laplace representation of each channel and Plancherel give

\[
 \int_{\mathbb R}b_{r,\pm}(\sigma+it)^*\mathsf T_r
                       b_{r,\pm}(\sigma+it)\,dt
 \le\frac{2\pi L_r}{1-e^{-2\sigma L_r}}\operatorname{Tr}\mathsf T_r.
 \tag{25}
\]

Indeed, the time-side integrand is a nonnegative trigonometric polynomial of period \(L_r\). Sum its geometrically damped periods and bound the first weighted period by its unweighted integral, which is \(L_r\operatorname{Tr}\mathsf T_r\). This pays the entire mode count without an unrecorded dimension factor.

Using (9) on the finite interval yields

\[
\begin{split}
 |\mathcal J_{\sigma,H}(\mathsf T)|
 \le2A_\epsilon\log(H+3)\bigg[
 &\frac{M^\sigma}{1-M^{-2\sigma}}\operatorname{Tr}\mathsf T\\
 &+\frac{m^\sigma}{1-m^{-2\sigma}}\operatorname{Tr}\mathsf T_{oo}
 \bigg].
\end{split} \tag{26}
\]

This still spends an \(m^{3/8+\epsilon}\) magnitude scale. It supplies neither the \(1/m\) drift scale nor the required independence from large \(p\). Subtracting the retained new-mode credit does not fix that: no lower bound on its adaptive spectral mass relative to the first term has been supplied.

Equation (26) is recorded as the failed price of the central absolute estimate, **not** as a new full-floor improvement. The packet already declares that magnitude scale spent. Its inability to prove (23) does not prove that the actual correlation violates (23).

### 7.2 The tempting positive-Gram replacement is algebraically false

**[ABSTRACT | PAPER]** The factors in (13) are analytic squares, not modulus squares. Even with the positive rank-one control \(\mathsf T=e_0e_0^{\mathsf T}\), take \(z=a+2ia\), \(a>0\). The zero-mode channel gives

\[
 \boxed{
 \Re\bigl(b_0(z)^2\bigr)=-\frac3{25a^2}<0,
 \qquad |b_0(z)|^2=\frac1{5a^2}>0.
 } \tag{27}
\]

The first expression has an exact negative upper envelope. Thus positive semidefiniteness of the spectral weight does not turn the analytic integrand into a positive Gram integrand. Nor would positivity of a replacement Gram factor control the complex multiplier \(\mathfrak a(\sigma+it)M^{it}\).

This rejects only that algebraic replacement. The control weight in (27) is not asserted to be the actual negative spectral weight of any CCM cell. It is not a counterexample to the requested CCM estimate, not a refutation of SP, and not a family-impossibility claim.

The independent commutation audit in the request remains fully respected: there has been no attempt to erase the fixed-basis diagonal account or the eigenvalue-changing compression by a unitary gauge. The concrete obstruction in this attempt is different and explicit: the remaining analytic-square pairing in (23) has no supplied arithmetic sign bound.

## 8. Alternatives, discriminator, and one independent audit target

### Two candidate re-representations

**A. Contour-to-zero-residue representation.** Keep the exact \(U_{p,m}\) of (10) and move a finite rectangle from \(\Re z=\sigma\) to a chosen \(b\in(0,\sigma)\). Provided no pole lies on its boundary, the new terms are

\[
 -\sum_{\substack{\rho:\ b<\Re\rho-1/2<\sigma\\|\Im\rho|<H}}
 \operatorname{mult}(\rho)\,U_{p,m}(\rho-1/2),
\]

together with the complete left vertical integral and both horizontal returns. Conjugate zeros pair by real parts. Boundary poles require explicit indentation and its cost. The left-line estimate and the sign of these actual adaptive residue evaluations are **OPEN**; no off-critical zero is asserted to exist.

**Kill-power/cost:** high against a false pole cancellation, missing zero residue, or mistaken modulus square; medium PAPER setup cost, potentially high arithmetic-estimate cost. A favorable signed bound could reach the unchanged consumer without proving a stronger zero-free strip. Merely moving the line and leaving the residues unpaid would not be progress.

**B. Negative-energy Schur-resolvent representation of the adaptive weight.** For the actual full path write
\(H_t=\bigl[\begin{smallmatrix}A_t&B_t\\B_t^*&D_t\end{smallmatrix}\bigr]\), with the complete two-mode new block. At a nonreal spectral parameter \(\lambda\), its exact Schur matrix is

\[
 D_t-\lambda I-B_t^*(A_t-\lambda I)^{-1}B_t.
\]

Recover the spectral part of \(\mathsf T\) from the resolvent spectral measure, and insert the two rational channel vectors into that block formula. Keep the fixed-basis diagonal part separately. No positivity of \(D_t\), inverse-gap estimate, or negligible \(B_t\) is assumed.

**Kill-power/cost:** high against omitted negative spectral mass, discarded new-mode coupling, or an assumed spectral gap; medium algebraic setup and high full finite spectral cost. The old block remains \((2m+1)\)-dimensional: a two-by-two Schur matrix does not make that cost disappear. The missing output is a signed bound on its contraction with the same prime–pole transfer, not an isolated resolvent norm.

The executed cross-domain checks are thus explicit: causal convolution gives (7)–(8); signed Perron tail integration plus integer spacing gives (18); spectral functional calculus gives (13) and the exact sign discriminator (27). The only vanishing identities established here are the genuine pole cancellation and causal endpoint/complement cancellations—not vanishing of the central residual.

### DISCRIMINATOR

**[FINITE_CELL | CONDITIONAL: proposed interval audit, not executed]** For a candidate zero-error instance of (23), enclose

\[
 F_{p,m}^{\epsilon}
 =\frac{Z_p(m)}{pm}
  +\frac L{64}\operatorname{Tr}(P_{\rm new}\mathsf T)
  -\mathcal J_{\sigma,M^2}(\mathsf T).
 \tag{28}
\]

Use (10) and the independent block/grid identity (12) with the same full adaptive weight. To certify the corresponding original \(\Omega\) inequality, also subtract the worst-case error \(r_{\epsilon,m}\operatorname{Tr}\mathsf T\) from the lower envelope; add it to the upper envelope when testing for failure. Use \(\Gamma\) instead of the smaller credit when testing that interface.

A lower envelope at least zero certifies only the specified finite-cell inequality. An upper envelope strictly below zero refutes only that finite-cell, zero-error inequality. A straddling interval remains inconclusive. Neither a finite prefix nor an all-zero floating-point negative part proves the eventual convergence in (24). The discriminator must control the actual spectral functional, path integration, and complex contour integration.

### Registered checks and their outcomes

Before the explicit diagnostic checks, the registered expectations were that the two-channel formula would reproduce the literal diagonal and off-diagonal kernels and the padding interface, and that the high-height return would admit a summable budget. The causal calculation (8), complete grid expansion (12), and bound (18) establish the claimed PAPER statements. They still require the independent audit below. No prediction that the central target (23) was true was registered or substituted retroactively.

A pre-delivery bandwidth audit corrected the draft lower threshold from \(m\ge3\) to \(m\ge6\): at \(m=3\), \(H=16\) does not dominate \(2\omega_{4}^{(4)}\), whereas \(M\log M\ge4\pi\) holds for \(M\ge7\). The final theorem uses the corrected cofinal domain. This rejects the earlier tail-proof domain, not the CCM source or its signed target.

Local floating-point diagnostics, **not interval certificates**, gave a maximum discrepancy below \(7.6\times10^{-15}\) between (2) and the causal inverse kernels, including both endpoints; direct finite Laplace integrals agreed with their closed rational expressions within \(2.3\times10^{-15}\). Formula (12) agreed with (10) within \(9\times10^{-17}\).

A planted real, positive, reflection-symmetric weight of trace one on the actual \(m=8\to9\) source detected the forbidden omissions: deleting old/new arithmetic couplings changed its contraction by approximately \(-0.0120831\); deleting the proper-power history \(4,8\) changed it by approximately \(+0.135161\). This weight was used only to test the identities and their sensitivity, not as a substitute for the actual adaptive weight. No finite-cell CCM sign conclusion is drawn.

**One precise independent-audit target:** audit Theorem (18), with the original literal kernel (2) as the reference. Verify the causal repeated-pole diagonal and both off-diagonal signs in (8); the exact sharp-cutoff return of every prime power; the constants \(8,32,24\) in (14)–(15); the integer-spacing bound (16); both artificial endpoint-tail contributions; the combined rational pole tail; and the two horizontal contour returns under precisely (9). The final result to accept or reject is (18) with the displayed \(r_{\epsilon,m}\), uniformly on the full \(N=m\) and \(N=m+1\) grids. Success pays only this truncation term. It does not certify (23).

## 9. Claim ledger and closeout

| Claim | Scope | Verifier | Disposition |
|---|---|---|---|
| Literal kernel, joint measure, full adaptive path, and inherited credits | FINITE_CELL | PAPER | Source-locked inputs; no new background proof |
| Causal two-channel identity (7)–(8) on \(c>1/2\) | FINITE_CELL | PAPER | Derived for every finite section |
| Log-derivative bound (9) and movement to \(\sigma\) | COFINAL_FAMILY | CONDITIONAL | Explicit zeta-only dependency, with the packet's reported Comparator provenance |
| Exact both-grid contraction and full adaptive expansion (10)–(13) | FINITE_CELL | PAPER | Derived; no sign conclusion |
| Integer-spacing and right-line truncation bounds (14)–(17) | COFINAL_FAMILY | PAPER | Derived; all prime powers and both continuous terms retained |
| Complete summable contour-return bound (18)–(19) | COFINAL_FAMILY | CONDITIONAL | Derived under (9); not independently audited |
| Original-credit residual return (20)–(22) | COFINAL_FAMILY | CONDITIONAL | Summable fee restored to the original moments |
| Required central signed estimate (23), or full-credit variant | COFINAL_FAMILY | CONDITIONAL | OPEN hypothesis; not supplied |
| Absolute central estimate (26) | COFINAL_FAMILY | CONDITIONAL | Does not improve the admitted fixed-power scale |
| Analytic-square control (27) | ABSTRACT | PAPER | Rejects only the positive-Gram substitution |
| SP and RH | COFINAL_FAMILY | CONDITIONAL | OPEN; no claim made |

**What became smaller:** within this representation, the entire arithmetic truncation and contour-return fee is no longer unpaid. The remaining sign problem lies in one finite-height, two-channel contraction with the exact adaptive weight and the original credits. Its definition contains no hidden cutoff, mode, or normalization return.

**What did not become smaller:** the available full-floor exponent, the required central cancellation, and the SP consumer. No quantitative gain at the requested drift scale was obtained. This is representation progress with a paid error term, not closure of the main arithmetic estimate.

**What was excluded:** only the algebraic identification of an analytic square with a nonnegative modulus square. No actual CCM theorem or route family was killed.

**Do not repeat:** treating the full-credit substitution as an independent supplier; deleting the diagonal account by spectral commutation; replacing the two actual grids by one; changing a transpose to an adjoint to manufacture positivity; or treating summability of the contour error as summability of the central signed residual.

**Minimal missing inequality:** (23), or its strictly weaker full-credit version, for the explicit transfer (10) with the true spectral evaluations (13). The earliest diagnosis-changing mathematical test is a one-sided estimate of this paired integral that beats (26) at the required scale while retaining both the old-grid derivative and every new-mode term in (12).

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
  ACTUAL_CONSUMER_REQUIREMENT: "forall eta>0, exists C_eta,m0: lambda_min(K_m)>=-C_eta*m^eta for every m>=m0"
  ORIGINAL_REQUESTED_OBJECT: "source-specific signed estimate on Q1 Omega or Xi-Gamma, sufficient for its recurrence or a genuinely improved full floor"
  ORIGINAL_OBJECT_IS: UNKNOWN
  NECESSITY_NOTE: "Neither the chosen companion nor the one-step contour interface is asserted necessary for SP."
  KNOWN_WEAKER_INTERFACES:
    - "The full-credit version of (23) is sufficient and is weaker than the retained-new-mode-credit version."
    - "A direct every-eta floor on the unchanged full K_m reaches the consumer without these moments."
    - "A same-family large-even-order moment bound with exponent independent of p reaches the inherited receiver."
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "exact adaptive two-channel source contraction plus signed integer-spacing truncation error summable on the original schedule"
  REOPEN_TRIGGER: "a signed estimate for the central pairing (23), or a weaker consumer-spendable estimate on the same full source"
  MATHEMATICAL_IMPOSSIBILITY_EVIDENCE: NONE
MEMORY_ENTRY:
  iteration: FULL_CCM_MOMENT_Q02
  target: FULL_ADAPTIVE_SIGNED_PRIME_POLE_DRIFT
  status: OPEN
  failed_strategy: "positive-Gram or absolute-magnitude extraction from the analytic contour pairing"
  cognitive_operator_used: REPRESENTATION_SHIFT
  paid_term: "full Perron truncation and rectangle return at height (m+1)^2"
  smallest_unpaid_input: "central finite-height signed two-channel pairing minus the original credit"
  invariant_learned: "the channel factors are analytic transpose squares; all physical modes return through a causal inverse transform, not a rank-two source approximation"
  forbidden_future_move: "manufacturing positivity by conjugating the second channel factor or discarding new-mode/history return terms"
  next_decisive_test: "independent audit of Theorem (18), followed only by a genuinely signed bound on its central pairing"
PREDICTION_FATES:
  KERNEL_AND_INTERFACE_RECONSTRUCTION: CONFIRMED_BY_PAPER_IDENTITY_AND_NONCERTIFYING_DIAGNOSTICS
  SUMMABLE_HIGH_HEIGHT_RETURN: CONFIRMED_BY_PAPER_DERIVATION_PENDING_INDEPENDENT_AUDIT
  INITIAL_M3_TAIL_PROOF_DOMAIN: REFUTED_BY_BANDWIDTH_AUDIT_CORRECTED_TO_M6
  CENTRAL_TARGET_SIGN: NO_POSITIVE_OUTCOME_PREDICTION_REGISTERED_AND_NO_BOUND_OBTAINED
```

**Final proposal:** retain (10) as the executed source representation and (18) as its single audit target. The next arithmetic supplier must bound (23) or its full-credit variant, not produce another isolated \(m^{3/8+\epsilon}\) norm. No enlarged numerical scan, Lean run, repository edit, or route promotion is authorized by this verdict.

## CODEX DIRECTIVE

Independently audit **Theorem (18) only**, from the literal full CCM kernel and actual \(N=m\) schedule, checking the causal diagonal/off-diagonal return, all prime-power endpoints, integer-spacing constant, both continuous pole terms, both grids, and the horizontal contour cost under the explicitly named zeta bound (9). Return either the verified PAPER inequality with its exact dependency scope, or the first false identity/constant and a corrected bound. Do not substitute an adaptive weight from an isolated block, run Lean, edit the repository, infer the central estimate (23), or make an SP/RH claim.
