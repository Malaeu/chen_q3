# STATUS: TRY_RH_SOURCE_ARITHMETIC

```yaml
OPERATIVE_CLASS: TRY_RH_SOURCE_ARITHMETIC
VERDICT_CODE: FULL_CCM_MOMENT_Q01_BACKGROUND_PAID_SIGNED_SOURCE_CORRELATION_OPEN
REQUEST: PROSHKA_CCM_MOMENT_Q01.txt
REQUEST_SHA256: 4b51de0ab0cd0b06ec26cf8d762c9034d331c7e8740822651fdc401fe65b95e5
SOURCE_BASELINE: 0a3ca3bc036f7f74f6fb5c5ab68574de1774c08e
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
FRONT: FULL_CCM_COUPLED_MOMENT_DRIFT
SOURCE_OBJECT: CCM_LITERAL_FULL_MATRIX_N_EQUALS_M
SCHEDULE: "m integer; N=m; L=log(m); every sufficiently late original cell"
HONESTY_STATE: CHALLENGER_NOT_RH
EVIDENCE_STATE: PAPER_DERIVED_NOT_LEAN_CHECKED
SP_STATUS: OPEN
RH_STATUS: OPEN
PX_RH_CLAIM: NOT_MADE
ADJUDICATION: INCONCLUSIVE_FOR_SP
NEW_ESTIMATE: "B_(m+1)-pad(B_m) >= (log m)/64 P_new -5000/(m log m) I, log m >= 256"
NEW_ESTIMATE_SCOPE: COFINAL_FAMILY
NEW_ESTIMATE_VERIFIER: PAPER
EXECUTED_COMPANION: "D_p(m)=(2m+1)+sum_j(-K_m[j,j])_+^p"
FIRST_UNPAID: "Omega_(p,m)=Xi_(p,m)-(log m)/64 Tr(P_new Wbar_(p,m)); Xi is the full signed source increment"
MISSING_BUDGET: "Omega_(p,m) <= Z_p(m)/(p m) + u_(p,m) Z_p(m)/p; u>=0; sum u<infinity"
MISSING_BUDGET_VERIFIER: CONDITIONAL
KILL_SCOPE: NONE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
ZF78_STATUS: REPORTED_ZETA_COMPARATOR_ACCEPTED_NOT_RERUN_HERE
DIRICHLET_HECKE_SIEGEL_IMPORTS: NONE
REPO_EDITS: NONE
LEAN_RUN: NONE
ARB_INTERVAL_RUN: NONE
PROGRESS_CLASS: REPRESENTATION_PROGRESS_WITH_ANCILLARY_COFINAL_PAPER_ESTIMATE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
INDEPENDENT_AUDIT_TARGET: "Section 3, complete-background actual-schedule increment, constant 5000"
```

## 1. Result and source boundary

**The combined calculation is executed below. It does not establish the required signed arithmetic estimate.** It does establish a uniform, source-shaped estimate that pays the complete separated background—archimedean term plus the retained decaying-pole term—including its two new modes and couplings. After that payment, one explicit signed arithmetic correlation remains.

The new estimate is

\[
\boxed{\quad
 \mathsf B_{m+1}-\widehat{\mathsf B}_m
 \succeq\frac{\log m}{64}\mathsf P_{\rm new}-\frac{5000}{m\log m}I,
 \qquad \log m\ge256.
\quad}                                                     \tag{1}
\]

Here \(K_m=\mathsf B_m-\mathsf C_m\) is an **exact decomposition of the literal matrix**; the hat means zero-padding on the two new coordinates, not deleting their couplings. Here \(\mathsf P_{\rm new}\) is the orthogonal projection onto the two new mode coordinates. The growing pole remains paired with the primes in \(\mathsf C_m\). The decaying term left in \(\mathsf B_m\) has a favorable derivative. Definitions and the proof of (1) follow.

For an actual nonnegative companion, the resulting full-step inequality is

\[
\boxed{
 Z_p(m+1)\le\left(1+\frac2m\right)Z_p(m)
       +\frac{p}{1-b_{p,m}}\,\Omega_{p,m},\qquad
 b_{p,m}=\frac{5000p}{m\log m},
}                                                           \tag{2}
\]

for every fixed even \(p\ge4\), once \(\log m\ge\max(256,20000p)\). The coefficient \(2\) is independent of \(p\). **The last term in (2) has not been bounded at the required scale.** It includes both old-entry motion and all arithmetic new-mode interactions, with their signs intact, and retains the positive new-mode credit in (1).

**[COFINAL_FAMILY | PAPER]** Equation (1), and the reduction (2), are the new mathematical outputs. There is no new subpolynomial estimate for the arithmetic term and no SP or RH conclusion.

The attached request was read in full and its SHA-256 matches the requested value. Its target is the full literal family, not the deferred Suzuki or cubic phases. The schedule, event distinction, and required quantitative output are fixed by the packet. fileciteturn0file0L3-L16 The public CCM source also fixes the zero-extended Fourier carrier and its correlation kernel; no alternate test class is being used. citeturn171860view0

The **ZF78** premise is treated with its updated provenance: the packet reports a successful zeta-only Comparator run, rather than merely statement inspection. I did not rerun that log, the Comparator, or Lean. The mathematical use of ZF78 below is explicit; no Dirichlet, Hecke, or Siegel conclusion is imported. fileciteturn0file0L255-L276 fileciteturn0file0L291-L302

## 2. Exact decomposition and preserved structure

**[FINITE_CELL | PAPER]** Write

\[
 I_N=\{-N,\ldots,N\},\qquad
 e_j^{(L)}(x)=L^{-1/2}e^{2\pi ijx/L}\mathbf1_{[0,L]}(x).
\]

Let \(Q_{N,L}(s)\) denote the matrix with the packet's literal entries

\[
 Q_{jk}(s)=
 \begin{cases}
 2(1-s/L)\cos(2\pi js/L),&j=k,\\[1mm]
 \dfrac{\sin(2\pi ks/L)-\sin(2\pi js/L)}{\pi(j-k)},&j\ne k,
 \end{cases}
 \qquad 0\le s\le L.                                      \tag{3}
\]

In particular \(Q(0)=2I\) and \(Q(L)=0\). These are the literal diagonal and off-diagonal branches, not an off-diagonal formula extended incorrectly onto the diagonal. fileciteturn0file0L1095-L1116

Put

\[
 J(s)=\frac{e^{-s/2}}{1-e^{-2s}},\qquad
 c_A=\gamma+\log(8\pi)+\frac\pi2,
\]

and define

\[
\begin{aligned}
 \mathsf A_N(L)
   &=\int_0^L J(s)(2I-Q_{N,L}(s))\,ds
                  +2I\int_L^\infty J(s)\,ds,\\
 \mathsf R_N(L)&=\int_0^L e^{-s/2}Q_{N,L}(s)\,ds,\\
 \mathsf B_N(L)&=\mathsf A_N(L)-c_AI+2\mathsf R_N(L),\\
 d\nu(s)&=\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}\,
                  \delta_{\log q}(ds)
                    -(e^{s/2}-e^{-s/2})\,ds,\\
 \mathsf C_N(L)&=\int_{[0,L]}Q_{N,L}(s)\,d\nu(s).
\end{aligned}                                               \tag{4}
\]

All measures here are used only on the displayed finite interval. The sum includes **every prime power**, with its actual von Mangoldt weight.

Then the literal source is exactly

\[
 K_N(L)=\mathsf B_N(L)-\mathsf C_N(L).                         \tag{5}
\]

To check constants directly, the pole entry is
\(\int_0^L(e^{s/2}+e^{-s/2})Q(s)\,ds\), which is the packet's closed \(W_{0,2}\) entry. Also
\(\mathsf A_N(L)-c_AI=-W_{\mathbb R,N}(L)\). The latter follows by subtracting the literal integrands and using

\[
\begin{aligned}
 c_A={}&\gamma+\log(4\pi\tanh(L/2))\\
 &+2\int_0^L\left[J(s)-\frac1{e^s-e^{-s}}\right]ds
     +2\int_L^\infty J(s)\,ds.
\end{aligned}                                               \tag{6}
\]

The right side is independent of \(L\). At infinity its extra integral is

\[
 2\int_0^\infty\frac{e^{s/2}-1}{e^s-e^{-s}}\,ds
 =4\int_0^1\frac{dy}{(1+y)(1+y^2)}
 =\log2+\frac\pi2.
\]

Thus (5) is also a direct check against the literal \(W_{0,2}-W_{\mathbb R}-\mathrm{Prime}\) constructor. fileciteturn0file0L1104-L1156 It agrees with the packet's existing joint-source decomposition. fileciteturn0file0L621-L637

Production always means
\(\mathsf B_m=\mathsf B_m(\log m)\),
\(\mathsf C_m=\mathsf C_m(\log m)\), and
\(K_m=K_m(\log m)\).
All matrices act on the full complex carrier; real symmetry does not impose a restriction to real or reflection-even vectors.

## 3. Proof of the complete-background increment bound

### 3.1 Old-entry motion: the full archimedean derivative has a uniform budget

**[FINITE_CELL | PAPER]** With Fourier convention
\(\widehat f(\xi)=\int f(x)e^{-i\xi x}dx\), the exact archimedean form has multiplier

\[
 a(\xi)=2\int_0^\infty J(s)(1-\cos\xi s)\,ds
       =2\sum_{r\ge0}
        \frac{\xi^2}{\alpha_r(\alpha_r^2+\xi^2)},
 \qquad \alpha_r=2r+\tfrac12.                               \tag{7}
\]

The kernel of \(\mathsf R\) is \(e^{-|x-y|/2}\), with multiplier
\((1/4+\xi^2)^{-1}\). Thus the fixed physical multiplier for \(\mathsf B\) is

\[
 b(\xi)=a(\xi)-c_A+\frac2{1/4+\xi^2}.                       \tag{8}
\]

Under the unitary dilation from \([0,L]\) to \([0,1]\), the multiplier becomes \(b(\zeta/L)\). This treats the entire zero-extended function, including its boundary jumps. Therefore

\[
 L\mathsf B_N'(L)
 =\operatorname{compression}\left[
       -\xi a'(\xi)+\frac{4\xi^2}{(1/4+\xi^2)^2}\right].     \tag{9}
\]

The second term is nonnegative. The first satisfies

\[
 0\le\xi a'(\xi)
    =4\sum_{r\ge0}\frac{\alpha_r\xi^2}
                           {(\alpha_r^2+\xi^2)^2}
    \le10.                                                 \tag{10}
\]

Here is an elementary uniform bound. For \(|\xi|\le1/2\), the sum is at most
\(4\xi^2\sum_r\alpha_r^{-3}\le9\), because the first term in that last sum is \(8\) and the remaining decreasing sum is at most its integral \(1\). For \(|\xi|\ge1/2\), apply the mesh bound

\[
 \sum_{r\ge0}f(2r+1/2)
       \le\tfrac12\int_0^\infty f(t)dt+2\sup f
\]

to the nonnegative unimodal function
\(f(t)=4t\xi^2/(t^2+\xi^2)^2\). Its integral is \(2\) and its maximum is \(3\sqrt3/(4|\xi|)\). The resulting bound is less than \(7\). The round constant \(10\) works throughout. Boundedness of the differentiated multiplier justifies differentiation of the finite forms.

Set \(M=m+1\), \(L=\log m\), \(L_+=\log M\). Integrating (9) gives

\[
 \mathsf B_m(L_+)-\mathsf B_m(L)
       \succeq-10\log(L_+/L)I
       \succeq-\frac{10}{mL}I.                             \tag{11}
\]

This bound includes every old mode. It is not obtained by differentiating an undifferentiated operator-norm error.

### 3.2 The actual two-column background coupling is small

**[FINITE_CELL | PAPER]** For \(j\ne k\), direct integration of (3) gives

\[
 (\mathsf B_N(L))_{jk}
       =\frac{v_L(j)-v_L(k)}{\pi(j-k)},\qquad
 v_L(x)=\int_0^L\bigl(J(s)-2e^{-s/2}\bigr)
                       \sin(2\pi xs/L)\,ds.               \tag{12}
\]

For \(L\ge1\),

\[
 |v_L(x)|\le8,\qquad |xv_L'(x)|\le9\quad(x\ne0).           \tag{13}
\]

For the first estimate, the complete sine transform of \(J\) has modulus at most \(1+\pi/4\); this follows from its series
\(\sum_r\xi/(\alpha_r^2+\xi^2)\), bounding the first term by \(1\) and the rest by the decreasing-function integral. The truncated tail is at most
\(2e^{-L/2}/(1-e^{-2L})<1.5\) for \(L\ge1\). The twice-weighted decaying integral costs at most \(4\). Their sum is below \(8\).

For the second estimate let \(w(s)=J(s)-2e^{-s/2}\). Integration by parts gives, with \(\omega=2\pi x/L\),

\[
 xv_L'(x)=Lw(L)\sin(\omega L)
             -\int_0^L(sw(s))'\sin(\omega s)\,ds.           \tag{14}
\]

The function \(sJ(s)\) is positive and unimodal: its logarithmic derivative is
\(1/s+1/2-\coth s\), strictly decreasing. Also
\(sJ(s)\le(s+1/2)e^{-s/2}<1\), and its total variation on the positive half-line is less than \(2\). The function \(se^{-s/2}\) likewise has maximum below \(1\) and total variation below \(2\). Boundary value plus variation in (14) therefore costs at most \(3+2\cdot3=9\). This argument includes noninteger \(x\); it does not incorrectly set \(\sin(2\pi x)=0\) between two mode labels.

Let \(E_m\) be the \((2m+1)\)-by-\(2\) block of \(\mathsf B_M(L_+)\) joining \(I_m\) to \(\{-M,M\}\). For \(k=M\) and \(j\ge M/2\), (13) gives

\[
 |v_{L_+}(M)-v_{L_+}(j)|\le18(M-j)/M.
\]

For the other old labels, \(|M-j|\ge M/2\) and the first estimate in (13) applies. Consequently every entry of either column is bounded by \(32/(\pi M)\), using reflection for \(k=-M\). Hence

\[
 \boxed{
 \|E_m\|^2\le\|E_m\|_{\mathrm F}^2
       \le\frac{4096}{\pi^2 M}<\frac{512}{m}.
 }                                                         \tag{15}
\]

No neighboring band is omitted. This is a bound for every entry in both new columns.

### 3.3 The complete new background block is positive with logarithmic slack

**[COFINAL_FAMILY | PAPER]** Use the packet's previously proved full-window estimate

\[
 \|\mathsf A_N(L)-\operatorname{diag}(a(2\pi j/L))\|\le20,
 \qquad L\ge1.                                            \tag{16}
\]

Its proof controls the diagonal error and the complete Hilbert commutator uniformly in the number of modes, so it applies to the full \(N=M\) matrix here. fileciteturn0file0L663-L725

For \(\xi\ge1/2\), keeping the terms \(\alpha_r\le\xi\) in (7) gives

\[
 a(\xi)\ge\sum_{\alpha_r\le\xi}\frac1{\alpha_r}
          \ge\frac12\log(2\xi).                            \tag{17}
\]

In the last inequality the decreasing sum dominates its integral through one more unit interval. At \(\xi=2\pi M/L_+\), and \(L_+\ge256\), this yields \(a(\xi)\ge L_+/4\). Since \(c_A<6\) and \(\mathsf R\succeq0\), the full two-mode background block \(F_m\) satisfies

\[
 F_m\succeq(a(2\pi M/L_+)-26)I_2
          \succeq\frac{L_+}{8}I_2.                         \tag{18}
\]

This uses the block's least eigenvalue, not just its two diagonal entries.

### 3.4 Pay the cross terms by completing the square

**[COFINAL_FAMILY | PAPER]** After reordering old and new labels,

\[
 \mathsf B_M-\widehat{\mathsf B}_m
 =\begin{pmatrix}
  \mathsf B_m(L_+)-\mathsf B_m(L)&E_m\\ E_m^*&F_m
 \end{pmatrix}.                                           \tag{19}
\]

For arbitrary old and new vectors \(u,w\), (11), (15), and (18) give

\[
\begin{aligned}
 \langle(u,w),(\mathsf B_M-\widehat{\mathsf B}_m)(u,w)\rangle
 &\ge-\frac{10}{mL}\|u\|^2
       +2\Re\langle u,E_mw\rangle+\frac L8\|w\|^2\\
 &\ge-\left(\frac{10}{mL}+\frac{8\|E_m\|^2}{L}\right)\|u\|^2\\
 &\ge-\frac{4106}{mL}\|u\|^2.
\end{aligned}
\]

This already proves the weaker lower bound without a positive new-mode credit. To retain such a credit, reserve \(L\|w\|^2/64\) in the first line. The remaining coefficient is at least \(7L/64\); completing the square now costs

\[
 \frac1{mL}\left(10+\frac{64\cdot512}{7}\right)
 <\frac{5000}{mL}.
\]

This proves the stronger (1), with its positive \(L\mathsf P_{\rm new}/64\) term. This is the **Schur-complement payment**: positivity of the actual new background block pays both coupling columns and leaves logarithmic new-mode slack. Rank or reflection alone would not have paid them.

## 4. An actual nonnegative companion and the combined full-step drift

**[FINITE_CELL | PAPER]** For a Hermitian matrix \(H\), let \(H_-\) be its **negative part**, with eigenvalues \((-\lambda)_+\), and put

\[
 \mathcal M_p(H)=\operatorname{Tr}(H_-^p),\qquad
 \mathcal E_p(H)=\sum_j(-H_{jj})_+^p.
\]

For the production family choose

\[
 \boxed{
 D_p(m)=(2m+1)+\mathcal E_p(K_m),\quad
 \kappa_p=1,\quad
 Z_p(m)=1+\mathcal M_p(K_m)+D_p(m).
 }                                                         \tag{20}
\]

This is nonnegative and computed from the actual matrix. Unlike \(\mathcal M_p\), the diagonal account is basis-dependent: it is defined in the literal CCM mode basis and is not transported through arbitrary unitary changes of basis. Scalar Jensen in a spectral decomposition gives

\[
 0\le\mathcal E_p(H)\le\mathcal M_p(H).
\]

Thus the companion has no concealed normalization or return loss:
\(1+(2m+1)+\mathcal M_p(K_m)\le Z_p(m)
\le1+(2m+1)+2\mathcal M_p(K_m)\).
The additive dimension pays lower-order trace terms; it is not multiplication by \(m^{ap}\).

Embed \(K_m\) by zeros on the two new modes. Set

\[
 \Delta K=K_M-\widehat K_m,
 \quad\Delta\mathsf B=\mathsf B_M-\widehat{\mathsf B}_m,
 \quad\Delta\mathsf C=\mathsf C_M-\widehat{\mathsf C}_m,
 \quad H_t=\widehat K_m+t\Delta K.                           \tag{21}
\]

The affine path is used **only for the exact fundamental theorem of calculus between the two production matrices**. It is not identified with the physical path \(K_N(L)\). All actual old-entry motion is retained in \(\Delta K\); no frozen-old-block estimate is substituted. No bound on an averaged substitute is being returned. Its old block, two new modes, and both coupling blocks all move together.

Define the positive matrix

\[
 W_{p,t}=(H_t)_-^{p-1}
          +\operatorname{diag}\bigl((-H_{t,jj})_+^{p-1}\bigr),
 \qquad \overline W_{p,m}=\int_0^1W_{p,t}\,dt\succeq0.       \tag{22}
\]

Trace differentiation and scalar differentiation give the exact combined identity

\[
\boxed{
 Z_p(M)-Z_p(m)
 =2-p\operatorname{Tr}(\overline W_{p,m}\Delta\mathsf B)
        +p\operatorname{Tr}(\overline W_{p,m}\Delta\mathsf C).
}                                                           \tag{23}
\]

The \(2\) is precisely the change in the dimension account. The moment part of (23) is the same endpoint difference as the packet's old-block integral plus \(\mathcal M_p(C)+G_p\). Those two nonnegative terms have not been discarded; the full path in (21) includes them. fileciteturn0file0L38-L55

Put

\[
 \Xi_{p,m}=\operatorname{Tr}(\overline W_{p,m}\Delta\mathsf C).
                                                               \tag{24}
\]

The combined correlation used in (2) is

\[
 \boxed{\Omega_{p,m}=\Xi_{p,m}
       -\frac{L}{64}\operatorname{Tr}(\mathsf P_{\rm new}\overline W_{p,m}).}
                                                               \tag{24a}
\]

Thus the arithmetic update is not required to pay the new modes without their actual logarithmic background slack.

For \(r\ge0\), \(r^{p-1}\le1+r^p\). Write
\(Y(H)=\mathcal M_p(H)+\mathcal E_p(H)\) and \(d=2m+3\).
Convexity gives \(Y(H_t)\le(1-t)Y(\widehat K_m)+tY(K_M)\). Consequently

\[
\begin{aligned}
 \operatorname{Tr}\overline W_{p,m}
 &\le2d+\frac{Y(\widehat K_m)+Y(K_M)}2\\
 &=\frac{Z_p(m)+Z_p(M)}2+d\\
 &\le Z_p(m)+Z_p(M).
\end{aligned}                                               \tag{25}
\]

The last inequality uses \(Z_p(m)+Z_p(M)\ge2d\). Applying the full lower bound (1), including its new-mode credit, to the positive weight in (23) now yields

\[
 Z_p(M)-Z_p(m)
 \le2+b_{p,m}(Z_p(m)+Z_p(M))+p\Omega_{p,m}.                    \tag{26}
\]

For \(\log m\ge20000p\), \(b_{p,m}\le1/(4m)\). Also
\(2\le Z_p(m)/m\). Absorbing the next-step term gives exactly (2), since

\[
 \frac{1+b_{p,m}+1/m}{1-b_{p,m}}\le1+\frac2m.
\]

**The order-dependent background cost is therefore paid.** The allowed \(p\)-dependent starting index, rather than an illicit \(p\)-dependent power of \(m\), absorbs it.

## 5. Execute the arithmetic contraction without splitting its signs

### 5.1 Endpoint primitive and Hilbert coordinates

**[FINITE_CELL | PAPER]** For \(r=m,M\), put \(L_r=\log r\),
\(\omega_j^{(r)}=2\pi j/L_r\), and use the exact primitive

\[
 \Phi_r(\omega;y)=
 \sum_{q\le y}\frac{\Lambda(q)}{q^{1/2+i\omega}}
 -\frac{y^{1/2-i\omega}-1}{1/2-i\omega}
 +\frac{1-y^{-1/2-i\omega}}{1/2+i\omega}.
\]

Set

\[
 d_j^{(r)}=\frac2{L_r}\Re\int_0^{L_r}
                    \Phi_r(\omega_j^{(r)};e^u)\,du,
 \qquad h_j^{(r)}=\Im\Phi_r(\omega_j^{(r)};r).
\]

Let \(\mathsf H_r\) have entries \(1/(j-k)\) off the diagonal and zero on it. The exact source identity is

\[
 \mathsf C_r=\operatorname{diag}(d^{(r)})
       +\frac1\pi[\operatorname{diag}(h^{(r)}),\mathsf H_r]. \tag{27}
\]

These are precisely the packet's signed primitive and dimension-free Hilbert representation. fileciteturn0file0L375-L443

Write \(T=\overline W_{p,m}\), let \(T_{oo}\) be its old principal block, and define

\[
 \theta_j^{(M)}=([\mathsf H_M,T])_{jj},\qquad
 \theta_j^{(m)}=([\mathsf H_m,T_{oo}])_{jj}.
\]

Cyclicity of the finite trace executes (24) as

\[
\boxed{
\begin{aligned}
 \Xi_{p,m}={}&
 \sum_{j\in I_M}d_j^{(M)}T_{jj}
       -\sum_{j\in I_m}d_j^{(m)}T_{jj}\\
 &+\frac1\pi\left[
     \sum_{j\in I_M}h_j^{(M)}\theta_j^{(M)}
       -\sum_{j\in I_m}h_j^{(m)}\theta_j^{(m)}\right].
\end{aligned}
}                                                           \tag{28}
\]

This is one signed endpoint contraction, not separate estimates for primes and poles or old and new sectors. Both frequency grids are their actual grids. The matrix \(T\) depends on the entire coupled path (21), not on isolated diagonal entries.

**An important padding defect is explicit.** Extending the old \(h\)-vector by zeros does not extend its Hilbert commutator by zeros. For an old label \(j\) and new label \(k\), the extra entry is

\[
 \left(\frac1\pi[\operatorname{diag}(\widehat h^{(m)}),
              \mathsf H_M]
          -\widehat{\frac1\pi[\operatorname{diag}(h^{(m)}),
              \mathsf H_m]}\right)_{jk}
       =\frac{h_j^{(m)}}{\pi(j-k)}.                         \tag{29}
\]

Equation (28) retains this interface contribution automatically.

The diagonal companion in (22) contributes nothing to the diagonal of
\([\mathsf H,W]\). Thus its weight cannot directly tune away the Hilbert term in (28). For any fixed positive \(\kappa_p\) multiplying this particular diagonal companion, the off-diagonal contraction is unchanged. This does **not** rule out cancellation between the complete diagonal and off-diagonal sums, or a different companion.

### 5.2 Equivalent full prime-history correlation

**[FINITE_CELL | PAPER]** A second exact form makes the retained arithmetic history visible. Define

\[
 \rho_{p,m}(s)=\operatorname{Tr}(TQ_{M,L_+}(s))
       -\mathbf1_{s\le L}\operatorname{Tr}(T_{oo}Q_{m,L}(s)),
 \qquad 0\le s\le L_+.
\]

Then (28) is exactly

\[
\boxed{
 \Xi_{p,m}=
 \sum_{q\le M}\frac{\Lambda(q)}{\sqrt q}\rho_{p,m}(\log q)
       -\int_0^{L_+}(e^{s/2}-e^{-s/2})\rho_{p,m}(s)\,ds.
}                                                           \tag{30}
\]

The function is continuous at \(s=L\), because the subtracted old kernel vanishes there. It satisfies
\(\rho_{p,m}(L_+)=0\) and
\(\rho_{p,m}(0)=2\operatorname{Tr}(T_{nn})\), where \(nn\) is the new principal block. A prime power \(q=M\) therefore has zero value contribution, but every older prime power remains in the first sum and in the spectral weight that generated \(T\).

As an additional event check, hold \(N\) fixed at \(L_q=\log q\), and write
\(\alpha_q=2\Lambda(q)/(L_q\sqrt q)\), \(v=\mathbf1\). For the chosen companion, the derivative jump of the two moment accounts is exactly

\[
 \left[\frac d{dL}(\mathcal M_p(K_N(L))+\mathcal E_p(K_N(L)))\right]_{L_q}
 =p\alpha_q\left(v^*(K_N(L_q))_-^{p-1}v
                 +\sum_j(-K_N(L_q)_{jj})_+^{p-1}\right)\ge0.
\]

Thus this companion supplies no automatic cancellation of prime-event slopes. No event atom has been added. These are not jumps of the moment itself. Zero-eigenvalue crossings are harmless for the \(C^1\) trace functions. fileciteturn0file0L60-L78

### 5.3 The first unpaid estimate

**[COFINAL_FAMILY | CONDITIONAL]** One sufficient source-specific statement, after the proved background payment, is:

\[
\boxed{
 \begin{gathered}
 \text{For arbitrarily large fixed even }p,
 \text{ there are }m_0(p)\text{ and }u_{p,m}\ge0,\\
 \sum_{m\ge m_0(p)}u_{p,m}<\infty,\qquad
 \Omega_{p,m}\le\frac{Z_p(m)}{pm}
                    +\frac{u_{p,m}}p Z_p(m)
 \quad(m\ge m_0(p)).
 \end{gathered}
}                                                           \tag{31}
\]

Together with (2), this gives

\[
 Z_p(m+1)\le\left(1+\frac4m+2u_{p,m}\right)Z_p(m),           \tag{32}
\]

with coefficient \(4\) independent of \(p\), and hence reaches the packet's already-known high-moment receiver. I do not count that receiver as a new result.

**Equation (31), for the explicit adaptive prime–pole correlation (28)/(30) minus the retained credit (24a), is not proved here.** It is the first unpaid signed source-specific estimate in this executed attempt.

An even weaker sufficient interface retains all remaining favorable background motion. Define

\[
 \Gamma_{p,m}=\operatorname{Tr}\!\left[\overline W_{p,m}
       \left(\Delta\mathsf B+\frac{5000}{mL}I\right)\right]
 \ge\frac L{64}\operatorname{Tr}(\mathsf P_{\rm new}\overline W_{p,m}).
                                                               \tag{31a}
\]

The exact identity (23) becomes
\(\Delta Z=2+5000p\operatorname{Tr}(\overline W)/(mL)+p(\Xi-\Gamma)\).
Consequently (31) may be weakened further by replacing \(\Omega\) with \(\Xi-\Gamma\). This fully retained credit is not assumed small or zero. Conversely, a bound on \(\Xi\) alone would be stronger than needed. None of these sufficient interfaces, nor this particular companion, is asserted necessary for SP.

## 6. What ZF78 actually contributes to this attempt

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** Use the packet's existing twisted-Perron transfer, without adding any character-family uniformity. For every fixed \(\epsilon>0\),

\[
 \mathcal R_r\ll_\epsilon r^{3/8+\epsilon},\qquad
 \|\mathsf C_r\|\le4\mathcal R_r,
 \qquad K_r\succeq-c_AI-C_\epsilon r^{3/8+\epsilon}I.
                                                               \tag{33}
\]

The retained frequency range is the original \(|\omega|\le2\pi r/\log r\), and the transfer keeps the sharp cutoff and both continuous terms. fileciteturn0file0L187-L207

In the present calculation this gives the actual full-update envelope

\[
 \|\Delta\mathsf C\|\le4(\mathcal R_M+\mathcal R_m).
\]

With \(a=(p-1)/p\), trace Hölder for the two positive summands in (22), followed by scalar concavity, yields

\[
\boxed{
 |\Xi_{p,m}|\le4(\mathcal R_M+\mathcal R_m)(2d)^{1/p}
       \left(\frac{Y(\widehat K_m)+Y(K_M)}2\right)^{(p-1)/p},
 \qquad d=2m+3.
}                                                           \tag{34}
\]

Indeed \(\operatorname{Tr}W_{p,t}\le(2d)^{1/p}Y(H_t)^{(p-1)/p}\), and (21) plus convexity controls its integral. This is a legitimate bound on the exact arithmetic contraction. Keeping the new-mode credit gives only

\[
 \Omega_{p,m}\le4(\mathcal R_M+\mathcal R_m)(2d)^{1/p}
       \left(\frac{Y(\widehat K_m)+Y(K_M)}2\right)^{(p-1)/p}
       -\frac L{64}\operatorname{Tr}(\mathsf P_{\rm new}\overline W_{p,m}).
\]

ZF78 supplies no lower bound on the last spectral mass that turns this into the signed \(1/(pm)\) budget in (31). No correlation between that mass and the first term is being silently assumed.

Also, (33) supplies a floor along the entire affine path, since positive order is preserved under its convex combinations. It gives only

\[
 Z_p(m)\ll_{p,\epsilon}m^{1+(3/8+\epsilon)p},                \tag{35}
\]

not an exponent bounded independently of large \(p\). Equations (34)–(35) are the result of actually spending the available ZF78 envelope in this representation. They do not improve its floor exponent. The failure of this upper envelope to prove (31) is not evidence that the actual correlation violates (31).

## 7. External mechanism mapping and the remaining alternatives

### 7.1 What transfers, and what does not

**[ABSTRACT | PAPER: source mapping, not certification of the external proof]** The external accounts are averages of powers of entries of a normalized inverse error, not negative spectral trace moments of a growing CCM matrix. Its high-moment argument separately establishes self-drift and cross-account transfer estimates before choosing the asymmetric weight. fileciteturn0file0L4088-L4099 fileciteturn0file0L4254-L4286

| External load-bearing mechanism | CCM disposition in this calculation |
|---|---|
| Exact selected-pair inverse update | Replaced by the exact full-endpoint identity (23); no random transition or choice of primes is assumed. |
| Survival-conditional centered signed means | No corresponding CCM averaging identity is supplied. The actual replacement to estimate is (28)/(30). |
| Uniform self-drift from row power sums and \(h^p,h^{2p}\) | The complete background self-drift is paid by (1)–(2). Arithmetic self-drift is not paid. |
| Low-square interpolation and near-endpoint uniqueness | No such hypotheses have been established for \((H_t)_-^{p-1}\). The external entrywise expansion cannot be assigned to it. |
| Asymmetric weighting of transfers | It does not control an unpaid self-drift. For the companion (20), the Hilbert contraction is independent of its diagonal weight. |

The external conclusion explicitly uses \(h\le q^{-1/2}\) and keeps every \(p\)-dependent reverse-transfer coefficient in summable errors. Neither is a free CCM import. fileciteturn0file0L4483-L4521 This is a missing contraction/averaging estimate, not an impossibility result.

### 7.2 Two re-representations and their discriminating power

**[FINITE_CELL | PAPER]** The two next candidate representations are explicit; neither licenses a larger computation before its return cost is checked.

**A. Endpoint Hilbert/primitive contraction — selected representation.** Use (28) and, independently, (30). The first exposes adjacent-mode phase coherence; the second tests it against the actual integer prime-power history. Its kill-power is high against omitted sectors, wrong grids, wrong pole signs, and false zero-padding. Analytic setup cost is low because only the existing \(d,h\) primitives and one positive spectral weight are needed. A direct dense finite implementation has cubic spectral cost; interval certification would require its own enclosure design. The risk is losing the signed interaction by bounding the two lines of (28) separately.

**B. Full trace-Hessian representation.** For \(E=\Delta K\) and the path (21), the exact second-order identity is

\[
 Y(K_M)-Y(\widehat K_m)
   =-p\operatorname{Tr}(W_{p,0}E)
       +\int_0^1(1-t)\mathcal H_{p,H_t}(E)\,dt,             \tag{36}
\]

where, in an eigenbasis \(H_tu_i=\lambda_i u_i\), with
\(g(x)=(-x)_+^{p-1}\),

\[
 \mathcal H_{p,H}(E)=
 -p\sum_{i,j}g[\lambda_i,\lambda_j]|\langle u_i,Eu_j\rangle|^2
 -p\sum_jg'(H_{jj})E_{jj}^2\ge0.                            \tag{37}
\]

Repeated eigenvalues use \(g'\). This is valid across zero for \(p\ge4\). It follows by differentiating the first derivative; decreasing \(g\) gives the sign. The mixed old/new entries absent from a first-order calculation at zero-padded \(K_m\) reappear in (37). Its kill-power is high against first-order-only cancellation claims. Symbolic setup is low cost; full finite evaluation again requires spectra. The risk is a positive curvature cost as large as the proposed arithmetic gain. No bound eliminating that cost is claimed.

The three bridge checks are therefore concrete: external conditional-expectation architecture has no established arithmetic transfer; unitary dilation gives the proved background bound; spectral divided differences expose, rather than remove, the full nonlinear return cost. None produces a vanishing identity for (30).

## 8. Tests, discriminator, and one independent audit target

### Registered prediction scoreboard

**[COFINAL_FAMILY | PAPER]** The prediction registered before completing the background estimate was that its actual-schedule increment has lower bound \(-C/(m\log m)\), including new-mode couplings. **Confirmed by the proof in Section 3**, with the conservative constant \(5000\). No SP prediction was registered or retroactively substituted.

The subsequent registered fault test was that deliberately omitting couplings would be detected. Floating-point checks did detect those omissions; they are diagnostic evidence only, not an ARB certificate or an asymptotic argument.

For bookkeeping, a local implementation independently assembled the literal \(W_{0,2}-W_{\mathbb R}-\mathrm{Prime}\) matrix and the decomposition (4), at \(m=4,8,16\). Maximum entrywise reconstruction discrepancies were below \(1.7\times10^{-13}\). On a **planted indefinite control** obtained by shifting each production matrix by \(-10I\), the \(p=4\) full-endpoint trace identity agreed to relative error below \(4\times10^{-15}\). This shift is a control for the diagnostic, not a counterexample to CCM and not a premise in Sections 2–6.

At the planted \(m=8\to9\) control, deleting the arithmetic old/new coupling block changed \(\Xi\) by about \(-114.663\); naïve zero-padding of \(h\) changed it by about \(-39.479\); deleting the old proper powers \(4,8\) changed it by about \(-407.314\). The independent full-kernel pairing (30) agreed with (28) to relative error below \(10^{-15}\). These observations show that the diagnostic is not blind to the forbidden deletions. They do not certify any sign for actual CCM.

### DISCRIMINATOR

**[FINITE_CELL | CONDITIONAL: proposed certification, not executed]** For a candidate local zero-error version of (31), enclose

\[
 \mathfrak F_{p,m}=\frac{Z_p(m)}{pm}-\Omega_{p,m},               \tag{38}
\]

using both (28) and (30), with the full nonlinear weight (22) and the positive new-mode credit (24a). A lower envelope \(L\ge0\) certifies only that specified finite-cell inequality. An upper envelope \(U<0\) refutes only that zero-error inequality at that cell. It does not refute SP, an eventual statement with a later starting index, or a recurrence with summable errors. A zero-straddling enclosure is inconclusive; refinement must control the negative-part spectral functional and the path integration, not declare tiny eigenvalues exactly zero.

For an eventual positive-excess claim, the additionally relevant quantity is

\[
 \sum_m\left(\frac{p\Omega_{p,m}}{Z_p(m)}-\frac1m\right)_+.
                                                               \tag{39}
\]

A finite prefix never certifies convergence of this series. A proved tail estimate for (39), for arbitrarily large fixed even \(p\), is a directly usable supplier for (31).

### One precise independent audit target

**Audit Section 3 only:** prove or locate the first failure in

\[
 \forall m\in\mathbb N,\quad \log m\ge256
 \Longrightarrow
 \mathsf B_{m+1}-\widehat{\mathsf B}_m
          \succeq\frac{\log m}{64}\mathsf P_{\rm new}
                   -\frac{5000}{m\log m}I,
\]

where \(\mathsf B\) is defined by (4), with all \(N=m\) and \(N=m+1\) modes. The check must verify the literal archimedean constant in (6), the dilation derivative and sign in (9), the bound \(|xv_L'(x)|\le9\) for noninteger intermediate \(x\), both coupling columns in (15), the two-mode least-eigenvalue bound (18), and the reserved \(L/64\) credit in Section 3.4. Success closes exactly this nonarithmetic update budget; a counterexample or algebraic defect reopens it. It does not change the status of (31). No Lean run or repository modification is requested.

## 9. Claim ledger and closeout

| Claim | Scope | Verifier | Disposition |
|---|---|---|---|
| Literal decomposition (4)–(6) | FINITE_CELL | PAPER | Derived; retains every source term |
| Complete-background increment (1) | COFINAL_FAMILY | PAPER | Derived, \(\log m\ge256\) |
| Nonnegative companion and full-step identity (20)–(26) | FINITE_CELL | PAPER | Derived |
| Independent-of-order paid background coefficient in (2) | COFINAL_FAMILY | PAPER | Derived; starting index may depend on \(p\) |
| Exact signed contraction (28) and (30) | FINITE_CELL | PAPER | Derived; no sign conclusion |
| ZF78 envelopes (33)–(35) | COFINAL_FAMILY | CONDITIONAL | Uses named zeta premise with reported Comparator provenance |
| Required signed estimate (31) | COFINAL_FAMILY | CONDITIONAL | Missing |
| Implication (31) to (32) | COFINAL_FAMILY | PAPER | Valid conditional receiver; not a proof of its premise |
| SP and RH | COFINAL_FAMILY | CONDITIONAL | OPEN; neither claimed |

**What became smaller:** the full separated background update is no longer an unpaid contribution to this particular moment attempt. Old-entry motion, the new positive background block, both background coupling columns, and the dimension account have a common original-schedule budget. The remaining unknown is the explicit signed adaptive prime–pole correlation (28)/(30) with the retained new-mode credit (24a); the still weaker full-credit interface (31a) is also admissible.

**What was killed:** no CCM theorem, no companion class, and no route family. The deliberate faults reject omission shortcuts in the diagnostic, not the actual family. There is no counterexample to SP here.

**What must not be tried again:** importing the external asymmetric weight as though it also supplied self-drift; bounding the prime and pole histories separately before contraction; or zero-padding \(h\) as though its finite Hilbert commutator had no interface term.

**Minimal missing identity/estimate:** a source-specific bound on (30) together with its retained credit, strong enough to prove (31) or its full-credit version, or a genuinely weaker original-family high-moment bound reaching SP. In particular, a proof of a summable tail in (39) would close this chosen receiver.

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
  ACTUAL_CONSUMER_REQUIREMENT: "forall eta>0, exists C_eta,m0: lambda_min(K_m)>=-C_eta*m^eta for all m>=m0"
  ORIGINAL_REQUESTED_OBJECT: "actual full-CCM coupled moment estimate with growth exponent independent of fixed even p"
  ORIGINAL_OBJECT_IS: UNKNOWN
  NECESSITY_NOTE: "No necessity is asserted for the chosen companion or one-step recurrence."
  KNOWN_WEAKER_INTERFACES:
    - "Tr((K_m^-)^p)<=C_p*m^c*(log m)^A_p, arbitrarily large fixed even p, c independent of p => SP"
    - "A direct every-eta lower bound for the unchanged full K_m => SP"
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "full original-schedule background payment plus one exact adaptive signed-source contraction"
  REOPEN_TRIGGER: "a signed supplier for (31)/(39), or a weaker genuine SP estimate on the same family"
  MATHEMATICAL_IMPOSSIBILITY_EVIDENCE: NONE
MEMORY_ENTRY:
  target: FULL_CCM_COUPLED_MOMENT_DRIFT
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  paid_input: "complete-background actual-schedule increment"
  smallest_unpaid_input: "Omega_(p,m) signed adaptive prime-pole budget with new-mode credit; or the weaker Xi-Gamma budget"
  invariant_learned: "basis-growth background coupling is paid by logarithmic new-block slack; Hilbert h-padding creates a nonzero interface"
  forbidden_future_move: "importing graph self-drift or discarding that interface"
  next_decisive_test: "independent audit of Section 3, then a signed supplier for the unchanged correlation (30)"
```

**Final proposal:** retain the actual companion (20) and the fully coupled endpoint correlation (28)/(30) as the executed receiver. Submit the single background lemma above for independent audit. Further arithmetic work must estimate that correlation with its spectral weights and background credits attached; another norm bound of size \(m^{3/8+\epsilon}\) would not change this conclusion.
