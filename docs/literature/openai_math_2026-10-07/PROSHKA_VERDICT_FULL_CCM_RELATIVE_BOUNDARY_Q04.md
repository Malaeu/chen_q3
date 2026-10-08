# STATUS: TRY_RH_SOURCE_ARITHMETIC
```yaml
OPERATIVE_CLASS: TRY_RH_SOURCE_ARITHMETIC
VERDICT_CODE: FULL_CCM_MOMENT_Q04_SOURCE_BOUNDARY_RELATIVE_FORM_CENTRAL_GAIN_OPEN
REQUEST: PROSHKA_CCM_MOMENT_Q04.txt
REQUEST_BYTES: 363603
REQUEST_SHA256: 6d7a90d70cbfd6ce0c978061af7485db905d558d5618774c8927a0c851c8ccce
SOURCE_BASELINE: ecb8fc85
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
FRONT: FULL_CCM_COUPLED_MOMENT_DRIFT
SOURCE_OBJECT: CCM_LITERAL_FULL_MATRIX_N_EQUALS_M
SCHEDULE: "r integer; N=r; L_r=log(r); m to m+1 uses both original full matrices"
HONESTY_STATE: CHALLENGER_NOT_RH
ADJUDICATION: INCONCLUSIVE_FOR_REQUESTED_CONSUMER_SUFFICIENT_SIGNED_GAIN
REQUESTED_FULL_SIGNED_ESTIMATE: NOT_PROVED
FULL_FLOOR_IMPROVEMENT: NONE
SP_STATUS: OPEN
RH_STATUS: OPEN
PX_RH_CLAIM: NOT_MADE
EXECUTED_CALCULATION: "actual-integer Fourier sampling -> full-source boundary image and positive boundary form -> relative-form contraction with the unchanged adaptive density"
NEW_SOURCE_BOUNDARY_IMAGE: "norm(K_r*b_r)<=100*(log r)^(7/2), r>=4; b_r=ones/sqrt(2r+1)"
NEW_SOURCE_BOUNDARY_POSITIVITY: "b_r^*K_r*b_r >= (log r)/16, log r>=1024"
NEW_RELATIVE_FORM: "K_r >= Pi_r*K_r*Pi_r + (log r)/32*E_r - 320000*(log r)^6*Pi_r; E_r=b_r*b_r^*, Pi_r=I-E_r"
NEW_BOUNDARY_ESTIMATE_SCOPE: COFINAL_FAMILY
NEW_BOUNDARY_ESTIMATE_VERIFIER: PAPER
ACTUAL_ADAPTIVE_DENSITY: RETAINED_AND_BOUNDARY_CONTRACTION_ESTIMATED
DIAGONAL_COMPANION: RETAINED_IN_ORIGINAL_BASIS
FIRST_UNPAID: "the signed boundary-zero bulk increment together with its explicitly restored boundary return, at the rate in (33)"
CONDITIONAL_INPUTS: "Only inherited Q2/Q3 zeta-only bounds for the finite-contour/residue return; no ZF78 is needed for (6)-(24)."
ZF78_STATUS: REPORTED_ZETA_COMPARATOR_ACCEPTED_NOT_RERUN_HERE
DIRICHLET_HECKE_SIEGEL_IMPORTS: NONE
REPO_EDITS: NONE
LEAN_RUN: NONE
COMPARATOR_RUN: NONE
ARB_INTERVAL_RUN: NONE
EVIDENCE_STATE: PAPER_DERIVED_PENDING_INDEPENDENT_AUDIT
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: BOUNDARY_SECTOR_AND_ITS_SOURCE_FORM_RETURN_ONLY
CONSUMER_PROGRESS: NO_PROGRESS
ROUTE_SCORE: 3
COGNITIVE_OPERATOR: LITERATURE_BRIDGE
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE_FOR_ACTUAL_ADAPTIVE_CCM_OR_SP
INDEPENDENT_AUDIT_TARGET: "Theorem Q04-R, inequality (30), including the full-source estimates (12),(16),(18) that pay its boundary return"
```

## 1. Result and boundary of the result

**The requested consumer-sufficient signed estimate is not proved. There is no improved full-floor exponent and no SP conclusion.** The calculation does prove a source-specific relative-form estimate with a positive boundary credit, and it estimates the boundary contraction of the **actual** negative spectral density. The remaining signed bulk term is not bounded at the required moment-drift scale.

This is not a new contour or residue representation. The arithmetic step is a finite Fourier mean-square calculation using the actual integers and actual von Mangoldt coefficients. It shows that the full source acts only polylogarithmically on its normalized endpoint-evaluation direction. A second direct calculation shows that this direction has positive **full-source** energy. These two statements pay a boundary correction in the original source-form norm, rather than assuming polynomial zero-extension transport.

For
\[
 b_r=\frac{\eta_r}{\sqrt{d_r}},\qquad
 \eta_r=(1,\ldots,1)^{\mathsf T},\qquad d_r=2r+1,
 \qquad E_r=b_rb_r^*,\quad \Pi_r=I-E_r,
\]
the new estimates are
\[
 \|K_rb_r\|\le100(\log r)^{7/2}\quad(r\ge4),
 \qquad b_r^*K_rb_r\ge\frac{\log r}{16}
       \quad(\log r\ge1024),
\]
and therefore
\[
 \boxed{K_r\succeq\Pi_rK_r\Pi_r+rac{\log r}{32}E_r
                    -320000(\log r)^6\Pi_r,
          \qquad\log r\ge1024.}
 \tag{R}
\]
**[COFINAL_FAMILY | PAPER]** This is a lower bound for the full literal source relative to its boundary-zero compression. It is not a lower bound for that compression. The positive term is a genuine boundary credit; the last term is a real, unpaid-in-the-drift logarithmic charge, not zero.

The calculation also finds a further obstruction: even after exact endpoint cancellation, an original edge mode retains at least \(1/(2\sqrt2\pi\log(m+1))\) projection leakage. Thus finite squared-frequency energy alone does not rescue a uniform polynomial transport rate on this boundary-zero subspace. This rejects that transport theorem shape only, not an estimate for the actual adaptive density.

The entire authoritative packet was read, including its nested source and external sections. Its byte count and SHA-256 match the request. The current bootstrap was fetched through the GitHub connector and has the blob recorded above. No repository edit, Lean run, Comparator rerun, or interval certification was performed. The attachment itself requires retention of the actual weight and all returns, and explicitly leaves the central sign open after the accepted Q3 enclosure. fileciteturn16file0L1-L10

## 2. Inherited objects, with no change of source or weight

**[FINITE_CELL | PAPER: source-locked inputs]** Write
\[
 I_r=\{-r,\ldots,r\},\quad L_r=\log r,\quad
 \omega_j^{(r)}=2\pi j/L_r,
 \quad e_j^{(L_r)}(x)=L_r^{-1/2}e^{i\omega_j^{(r)}x}\mathbf1_{[0,L_r]}(x).
 \tag{1}
\]
For \(f_c=\sum_{j\in I_r}c_je_j^{(L_r)}\), its two interior endpoint traces are
\[
 f_c(0)=f_c(L_r)=\frac{\eta_r^{\mathsf T}c}{\sqrt{L_r}}.
 \tag{2}
\]
Thus \(\Pi_rc\) has zero endpoint traces. This is one codimension-one subspace of the original complex carrier. It is not a restriction to real or even functions, and it is not a replacement definition of \(K_r\).

Retain the exact decomposition \(K_r=\mathsf B_r-\mathsf C_r\), where
\[
 \mathsf B_r=\mathsf A_r-c_AI+2\mathsf R_r,
 \qquad
 \mathsf C_r=\int_{[0,L_r]}Q_{r,L_r}(s)\,d\nu(s),
\]
\[
 d\nu(s)=\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}\delta_{\log q}(ds)
               -(e^{s/2}-e^{-s/2})\,ds.
 \tag{3}
\]
Here \(Q\) has the literal two branches, \(Q(0)=2I\), \(Q(L_r)=0\), \(\|Q(s)\|\le2\); \(c_A<6\), and \(0\preceq\mathsf R_r\preceq4I\). The complete archimedean matrix has the inherited bound
\[
 \|\mathsf A_r-\operatorname{diag}(a(\omega_j^{(r)}))\|\le20,
 \quad
 a(\xi)=2\sum_{k\ge0}\frac{\xi^2}{\alpha_k(\alpha_k^2+\xi^2)},
 \quad\alpha_k=2k+\tfrac12.
 \tag{4}
\]
The source branches and joint measure are unchanged, and (4) is used as an already established input, not re-proved as new progress. fileciteturn16file0L1165-L1188 fileciteturn16file0L2318-L2327

For \(M=m+1\), keep exactly
\[
\begin{split}
 H_t&=\widehat K_m+t(K_M-\widehat K_m),\\
 G_t&=(H_t)_-^{p-1},\\
 D_t&=\operatorname{diag}((-H_{t,jj})_+^{p-1}),\\
 T&=\int_0^1(G_t+D_t)\,dt,
 \qquad \tau=\operatorname{Tr}T,\\
 \Xi&=\operatorname{Tr}(T\Delta\mathsf C),\\
 e_m&=5000/(m\log m),\\
 \Gamma&=\operatorname{Tr}[T(\Delta\mathsf B+e_mI)],\\
 c&=(\log m)/64\,\operatorname{Tr}(P_{\rm new}T).
\end{split}
\tag{5}
\]
The old block \(T_{oo}\) is the principal block of this **full** \(T\). No spectral function of an isolated old block is substituted. The diagonal account is evaluated in the original mode basis throughout. The credit ordering \(\Gamma\ge c\) is used only on its inherited domain. fileciteturn16file0L263-L282

The only outside methodological reference used here is finite Fourier sampling on a circle and its dual matrix formulation, as developed in Kedlaya's additive-large-sieve chapter. Below I prove an elementary, weaker bound directly by a Dirichlet-kernel row sum. No unproved prime-distribution estimate, character-family bound, or random averaging rule is imported. citeturn317847view0

## 3. Actual integer spacing controls the full boundary image

### 3.1 The sampling estimate, including the circular endpoint

**[COFINAL_FAMILY | PAPER]** Fix \(r\ge4\), and abbreviate \(L=L_r\), \(d=d_r\). For each integer \(2\le q\le r\), put
\[
 \alpha_q=\frac{\log q}{L}\pmod1.
\]
These points are separated on the circle by
\(\delta=(rL)^{-1}\). Indeed, for \(2\le k<q\le r\),
\[
 \frac{\log(q/k)}L\ge\frac{q-k}{rL}\ge\delta,
 \qquad
 1-\frac{\log(q/k)}L
 =\frac{\log(rk/q)}L\ge\frac{\log2}L\ge\delta.
\]
The point \(q=r\) is the circle endpoint \(0\), not a duplicate: \(q=1\) is absent and has von Mangoldt coefficient zero anyway.

For any subset of these integers and arbitrary complex coefficients \(a_q\), expansion of the square gives
\[
 \sum_{j=-r}^r\left|\sum_q a_qe^{-2\pi ij\alpha_q}\right|^2
 =\sum_{q,k}a_q\overline{a_k}\,\mathcal D_r(\alpha_k-\alpha_q),
\]
where
\[
 \mathcal D_r(u)=\sum_{j=-r}^re^{2\pi iju},\qquad
 |\mathcal D_r(u)|\le\min\{d,(2\|u\|_{\mathbb R/\mathbb Z})^{-1}\}.
\]
In each of the two half-circles about a fixed point, the successive occupied distances are at least \(\delta,2\delta,\ldots\). The absolute off-diagonal row sum of this Gram matrix is therefore at most \(\delta^{-1}H_{r-1}\), where \(H_n=\sum_{k=1}^n1/k\). Its diagonal is \(d\). The Hermitian row-sum bound consequently proves
\[
 \boxed{
 \sum_{j=-r}^r\left|\sum_q a_qe^{-2\pi ij\alpha_q}\right|^2
 \le[d+rLH_{r-1}]\sum_q|a_q|^2
 \le5rL^2\sum_q|a_q|^2.}
 \tag{6}
\]
For the final inequality, use \(d\le3r\), \(H_{r-1}\le1+L\), and \(L\ge1\). This is a deterministic inequality for the actual integer phases. No independence of primes, spectral vectors, or consecutive matrices appears.

### 3.2 Apply the estimate before taking the boundary image

Retain the inherited joint primitive
\[
 \Phi_r(\omega;y)=
 \sum_{q\le y}\frac{\Lambda(q)}{q^{1/2+i\omega}}
 -\frac{y^{1/2-i\omega}-1}{1/2-i\omega}
 +\frac{1-y^{-1/2-i\omega}}{1/2+i\omega}.
 \tag{7}
\]
For every \(1\le y\le r\), (6), with \(a_q=\Lambda(q)/\sqrt q\) on the actual prefix, applies without changing its grid. Moreover,
\[
 \sum_{q\le r}\frac{\Lambda(q)^2}{q}
 \le\sum_{q=2}^r\frac{(\log q)^2}{q}
 \le\int_1^r\frac{(\log(2x))^2}{x}\,dx
 \le4L^3.
\]
The integral bound follows on each interval \([q-1,q]\) from \(2x\ge q\) and \(x\le q\). Thus the vector of prime-prefix evaluations has norm at most \(\sqrt{20r}\,L^{5/2}\).

Both continuous terms in (7) are retained. Their combined norm is bounded by
\[
 (\sqrt r+3)
 \left[\sum_{j=-r}^r\frac1{1/4+(2\pi j/L)^2}\right]^{1/2}
 \le(\sqrt r+3)\sqrt{4+L}.
\]
For the last inequality, compare the positive-frequency decreasing sum with its integral and include the zero mode, which contributes 4. Since \(\sqrt r+3\le3\sqrt r\) and \(4+L\le5L\),
\[
 \boxed{
 \sup_{1\le y\le r}
 \left\|\bigl(\Phi_r(\omega_j^{(r)};y)\bigr)_{j\in I_r}\right\|_2
 \le12\sqrt r\,L^{5/2}.}
 \tag{8}
\]
Taking an upper envelope of these already specified terms is not a replacement prime process. Every proper power remains in (7). This estimate controls a vector of all grid evaluations, not the much more expensive supremum of one arbitrary spectral contraction.

Define the inherited real vectors
\[
 h_j=\Im\Phi_r(\omega_j^{(r)};r),\qquad
 d_j^{\rm ar}=\frac2L\Re\int_0^L\Phi_r(\omega_j^{(r)};e^u)\,du.
\]
With \(\mathsf H_{jk}=1/(j-k)\) off the diagonal, and zero on it, the exact source identity is
\[
 \mathsf C_r=\operatorname{diag}(d^{\rm ar})
       +\pi^{-1}[\operatorname{diag}(h),\mathsf H],
 \qquad\|\mathsf H\|\le\pi.
 \tag{9}
\]
These are the original joint Hilbert coordinates, not a new source definition. fileciteturn16file0L2490-L2512 fileciteturn16file0L3235-L3260

Let
\[
 R_j=(\mathsf H\eta_r)_j=H_{r+j}-H_{r-j}.
\]
Then \(|R_j|\le H_{2r}\le3L\), and the exact boundary image is
\[
 \mathsf C_rb_r=rac1{\sqrt d}
 \left[d^{\rm ar}+\pi^{-1}(h\circ R-\mathsf Hh)\right].
 \tag{10}
\]
Equation (8) gives \(\|h\|_2\le12\sqrt rL^{5/2}\) and
\(\|d^{\rm ar}\|_2\le24\sqrt rL^{5/2}\). Therefore
\[
 \|\mathsf C_rb_r\|
 \le\frac{12\sqrt r}{\sqrt d}L^{5/2}(3+3L/\pi)
 \le40L^{7/2}.
 \tag{11}
\]
The division by \(\sqrt{2r+1}\) is essential. We are estimating the **normalized** boundary direction. No estimate for the unnormalized physical trace is obtained by forgetting that factor.

### 3.3 Add the entire background, not just its diagonal

For \(\xi\ge1\), the \(k=0\) term of (4) is at most 4. For \(k\ge1\), its summand is at most
\(\min(1/k,\xi^2/(4k^3))\). Splitting at \(n=\lfloor\xi\rfloor\ge\xi/2\) gives
\[
 a(\xi)\le4+H_n+rac{\xi^2}{8n^2}
       \le6+\log\xi.
\]
The multiplier is increasing in \(|\xi|\). At the top grid frequency,
\(\log(2\pi r/L)\le L+2\), so (4) implies
\[
 \|\mathsf B_r\|\le L+8+20+6+8\le50L.
\]
In particular, (11) proves
\[
 \boxed{\|K_rb_r\|\le\mathfrak b_r:=100L_r^{7/2},
                       \qquad r\ge4.}
 \tag{12}
\]
This is a new full-source estimate, independent of ZF78.

For a later two-coordinate return we also record an elementary whole-matrix envelope. From (3),
\[
 \|\mathsf C_r\|
 \le2\sum_{q\le r}\frac{\Lambda(q)}{\sqrt q}
       +2\int_0^L(e^{s/2}-e^{-s/2})ds
 \le8\sqrt rL.
\]
Consequently
\[
 \|K_r\|\le40\sqrt rL\qquad(r\ge4).
 \tag{13}
\]
This coarse bound is used only after multiplying by the norm of a specified two-coordinate correction. It is not advertised as a new spectral floor.

## 4. The boundary energy is positive for the full arithmetic source

### 4.1 Execute the scalar contraction of the literal kernel

**[COFINAL_FAMILY | PAPER]** Put
\(\kappa_r(s)=b_r^*Q_{r,L}(s)b_r\) and \(u=s/L\). Summing the literal diagonal and off-diagonal branches gives
\[
 \kappa_r(s)=\frac2d\left[
 (1-u)\sum_{j=-r}^r\cos(2\pi ju)
 -\frac1\pi\sum_{j=-r}^rR_j\sin(2\pi ju)\right].
 \tag{14}
\]
The minus sign comes from the column sums of \(\mathsf H\) being the negatives of its row sums. This calculation uses the full kernel; in particular it does not extend its off-diagonal branch onto the diagonal.

The sequence \(R_j\) increases from \(-H_{2r}\) to \(H_{2r}\) and has total variation \(2H_{2r}\). Discrete summation by parts therefore gives
\[
 \left|\sum_{j=-r}^rR_je^{2\pi iju}\right|
       \le\frac{2H_{2r}}{|\sin\pi u|}.
\]
Use this, the Dirichlet-kernel bound, \(H_{2r}\le3L\), and
\(\sin(\pi u)\ge2\min(u,1-u)\). Together with \(\|Q(s)\|\le2\), they imply
\[
 \boxed{|\kappa_r(s)|\le
 \min\left\{2,\frac{4L^2}{r\min(s,L-s)}\right\},
 \quad0<s<L;
 \qquad \kappa_r(0)=2,\quad\kappa_r(L)=0.}
 \tag{15}
\]
Endpoint values are stated separately. The estimate does not insert an endpoint atom or delete a historical one.

### 4.2 Pay every prime and both continuous terms in this contraction

Assume \(L\ge8\). For \(2\le q\le r/2\), both distances in (15) are at least \(\log2\), and
\(\sum_{q\le r}\Lambda(q)/\sqrt q\le2\sqrt rL\). This part costs at most \(12L^3/\sqrt r\).

For \(r/2<q<r\), the smaller distance is \(\log(r/q)\ge(r-q)/r\). Each coefficient is at most \(\sqrt2L/\sqrt r\), so the harmonic sum costs at most \(12L^4/\sqrt r\). The atom at \(q=r\) has its exact value \(\kappa_r(L)=0\). Thus the full prime contribution has absolute value at most \(24L^4/\sqrt r\). A prime power \(q=m\) is, of course, an ordinary retained historical term when the endpoint becomes \(m+1\).

For the continuous pair, put \(A=4L^2/r\le L\). Then
\[
 \int_0^{L/2}\min(2,A/s)ds
 =A[1+\log(L/A)]\le8L^3/r.
\]
On the first half-window, \(e^{s/2}\le r^{1/4}\); on the second, it is at most \(\sqrt r\). Since \(0\le e^{s/2}-e^{-s/2}\le e^{s/2}\), the **specified paired integral** has absolute value at most \(16L^3/\sqrt r\). Combining the actual terms yields
\[
 \boxed{|b_r^*\mathsf C_rb_r|\le50L_r^4r^{-1/2},
                         \qquad L_r\ge8.}
 \tag{16}
\]
There is no assumed prime cancellation here: the gain follows from summing all mode branches first and then applying actual integer endpoint spacing. It does not bound \(\mathsf C_r\) on the entire carrier.

### 4.3 Retain the resulting positive full-source energy

At least a fraction \(2/5\) of the labels satisfy \(|j|\ge r/2\). For these labels, the inherited lower bound
\(a(\xi)\ge\tfrac12\log(2\xi)\) gives
\(a(\omega_j^{(r)})\ge L/4\) for \(L\ge8\). All other multiplier entries are nonnegative. Hence (4), positivity of \(\mathsf R_r\), and (16) give
\[
 a_r:=b_r^*K_rb_r
 \ge L/10-26-50L^4e^{-L/2}.
\]
For \(L\ge1024\), the last term is at most 1. One can check this at 1024 using \(e>2\), and then use the negative derivative of \(L^4e^{-L/2}\). Also \(L/10-27\ge L/16\) on this domain. Therefore
\[
 \boxed{a_r\ge L_r/16\qquad(L_r\ge1024).}
 \tag{17}
\]
Unlike the inherited Q1 background estimate, (17) includes the entire prime–pole contraction. This is the favorable signed input for the following relative form.

## 5. A paid boundary correction in the original form norm

Let \(z_r=K_rb_r\), \(y_r=\Pi_rz_r\), and define the exact correction
\[
 J_r^\partial:=K_r-\Pi_rK_r\Pi_r
 =b_rz_r^*+z_rb_r^*-a_rb_rb_r^*.
\]
For \(x=w+\alpha b_r\), \(w\perp b_r\),
\[
 x^*K_rx=w^*K_rw+2\Re(\overline\alpha\,y_r^*w)+a_r|\alpha|^2.
\]
Reserve \(L_r|\alpha|^2/32\). The remaining boundary coefficient is at least \(L_r/32\), by (17). Completing the scalar square and using (12) proves
\[
 \boxed{
 K_r\succeq\Pi_rK_r\Pi_r+rac{L_r}{32}E_r
            -\frac{32\mathfrak b_r^2}{L_r}\Pi_r
 =\Pi_rK_r\Pi_r+rac{L_r}{32}E_r-320000L_r^6\Pi_r,
 \quad L_r\ge1024.}
 \tag{18}
\]
**[COFINAL_FAMILY | PAPER]** This square completion is justified by the calculated **full-source** boundary column and its positive energy. No small Schur dimension or assumed positive arithmetic perturbation is used.

The exact correction also satisfies
\[
 \boxed{\|J_r^\partial\|\le3\mathfrak b_r=300L_r^{7/2}
                         \qquad(r\ge4).}
 \tag{19}
\]
Thus the two-sided form return is polylogarithmic even though the one-sided positive-credit comparison in (18) has the larger \(L_r^6\) charge. These are different estimates, not interchangeable error prices.

For every positive semidefinite weight \(W\) on the endpoint carrier, put
\[
 \tau_r(W)=\operatorname{Tr}W,\qquad
 \beta_r(W)=b_r^*Wb_r,
 \qquad
 j_r(W)=\operatorname{Tr}(WJ_r^\partial)
       =2\Re(b_r^*Wz_r)-a_r\beta_r(W).
\]
The exact mixed term remains signed. Weighted Cauchy–Schwarz and (12) give
\[
 \boxed{|j_r(W)|\le3\mathfrak b_r
             \sqrt{\beta_r(W)\tau_r(W)}.}
 \tag{20}
\]
Indeed the mixed term costs at most \(2\mathfrak b_r\sqrt{\beta_r\tau_r}\), while \(|a_r|\beta_r\le\mathfrak b_r\sqrt{\beta_r\tau_r}\), since \(0\le\beta_r\le\tau_r\). The corresponding one-sided estimate is
\[
 j_r(W)\ge\frac{L_r}{32}\beta_r(W)
                   -320000L_r^6\operatorname{Tr}(W\Pi_r).
 \tag{21}
\]
This estimate applies to the actual \(T\) and its principal block without pretending that either is independent of the source.

For completeness, the exact floor return is
\[
 \lambda_{\min}(K_r)\ge
 \min\{0,\lambda_{\min}(K_r|_{b_r^\perp})\}-300L_r^{7/2}.
 \tag{22}
\]
Here \(K_r|_{b_r^\perp}\) means the compressed quadratic form on that subspace. This shows that a genuinely improved full-floor estimate on the compressed form would return to the original family with a subpolynomial fee. **No such estimate for the compression is proved here.** Equation (22) is not a full-floor improvement by itself.

## 6. Estimate the actual adaptive boundary density

### 6.1 Both endpoint directions along the full affine path

**[COFINAL_FAMILY | PAPER]** Set
\[
 L=\log m,\quad L_+=\log M,\quad d=d_M,
 \quad \mathfrak b_*:=200L_+^{7/2}.
\]
The old matrix, acting on the new normalized boundary vector, gives exactly
\[
 \widehat K_mb_M=\sqrt{d_m/d_M}\,\widehat{K_mb_m}.
\]
Therefore \(\|H_tb_M\|\le\mathfrak b_M\). To control the old direction inside the full path, retain the explicit two-coordinate correction
\[
 \widehat b_m=\sqrt{d_M/d_m}\,b_M
                   -\frac{e_{-M}+e_M}{\sqrt{d_m}}.
\]
Equations (12) and (13) give
\[
 \|K_M\widehat b_m\|
 \le\sqrt{d_M/d_m}\,\mathfrak b_M
       +40\sqrt M L_+\sqrt{2/d_m}
 \le\tfrac65\mathfrak b_M+50L_+\le\mathfrak b_*.
\]
At the other endpoint the norm is bounded by \(\mathfrak b_m\). Convexity of the vector norm now proves
\[
 \boxed{\|H_tv\|\le\mathfrak b_*,
   \quad v\in\{b_M,\widehat b_m\},\quad0\le t\le1,\quad m\ge4.}
 \tag{23}
\]
Both new coordinates and all their source columns were paid by the explicit second term, not dropped. This is not the already excluded zero-padding rule for an \(h\)-commutator.

For \(L\ge1024\), (17) also gives
\[
 a_t:=b_M^*H_tb_M
 =(1-t)(d_m/d_M)a_m+ta_M\ge L/32.
\]
Put \(y_t=(I-b_Mb_M^*)H_tb_M\). If \(H_tu=-xu\), \(x\ge s>0\), then
\((a_t+x)u^*b_M=-u^*y_t\). Summing over the entire spectral subspace, including all multiplicities, proves
\[
 \boxed{
 \|\mathbf1_{(-\infty,-s]}(H_t)b_M\|^2
 \le\frac{\mathfrak b_*^2}{(s+L/32)^2}.}
 \tag{24}
\]
This is an actual negative-spectral-density estimate, not a bound for a planted replacement matrix. It holds for every \(s>0\); taking \(s\) down to zero gives the strict negative projector. Zero eigenvalues have zero moment weight.

The estimate controls a **normalized coordinate**. For a spectral subspace with coefficient vectors \(u_\alpha\), its physical endpoint density is
\[
 \sum_\alpha|f_{u_\alpha}(0)|^2
 =\frac{d_M}{L_+}\sum_\alpha|b_M^*u_\alpha|^2.
\]
The factor \(d_M/L_+\) must be restored. In particular, the envelope from (24) at \(s=m^a\) has scale \(m^{1-2a}\) times logarithms after this restoration. No boundary-layer concentration or small physical transport error follows for arbitrary positive \(a\).

### 6.2 The exact moment-weighted estimate, including the diagonal companion

For every fixed even \(p\ge4\), functional calculus gives
\[
 G_t=H_t(H_t)_-^{p-3}H_t.
\]
Consequently (23) implies
\[
 v^*G_tv\le\mathfrak b_*^2
          \mathcal M_p(t)^{(p-3)/p},
 \qquad \mathcal M_p(t):=\operatorname{Tr}(H_t)_-^p,
 \quad v\in\{b_M,\widehat b_m\}.
\]
This uses \(\|(H_t)_-^{p-3}\|\le\mathcal M_p(t)^{(p-3)/p}\), not a carrier-wide projection hypothesis.

Let
\[
 \beta_M=b_M^*Tb_M,
 \qquad\beta_m=\widehat b_m^*T\widehat b_m=b_m^*T_{oo}b_m,
 \qquad\tau_m=\operatorname{Tr}T_{oo}.
\]
The fixed-basis account contributes exactly its diagonal sums, so
\[
 \boxed{
 \begin{split}
 \beta_M&\le\mathfrak b_*^2\int_0^1\mathcal M_p(t)^{(p-3)/p}dt
                +\frac1{d_M}\int_0^1\operatorname{Tr}D_t\,dt,\\
 \beta_m&\le\mathfrak b_*^2\int_0^1\mathcal M_p(t)^{(p-3)/p}dt
                +\frac1{d_m}\int_0^1\sum_{j\in I_m}D_{t,jj}\,dt.
 \end{split}}
 \tag{25}
\]
There is no claim that the second terms vanish. For example, its boundary-form return at endpoint \(r\), on a diagonal weight, is exactly
\[
 j_r(D)=\sum_{j\in I_r}D_{jj}
        \left(\frac{2(z_r)_j}{\sqrt{d_r}}-\frac{a_r}{d_r}\right),
\]
which is not a commutator cancellation.

A useful explicit cost ledger follows. Put
\(S_{p,m}=\int_0^1\mathcal M_p(t)dt\). Scalar Jensen in an eigenbasis and finite Hölder give
\[
 \tau\le2d_M^{1/p}S_{p,m}^{1-1/p},
 \quad
 \beta_m,\beta_M\le
 \mathfrak b_*^2S_{p,m}^{1-3/p}
       +\frac{d_M^{1/p}}{d_m}S_{p,m}^{1-1/p}.
\]
Using (20), define the nonnegative boundary-return envelope
\[
 \mathcal B_{p,m}:=
 3\mathfrak b_m\sqrt{\beta_m\tau_m}
       +3\mathfrak b_M\sqrt{\beta_M\tau}.
\]
Then the actual signed boundary difference obeys
\[
 \boxed{
 \begin{split}
 |j_m(T_{oo})-j_M(T)|\le\mathcal B_{p,m}
 \le{}&6\sqrt2\,\mathfrak b_M\mathfrak b_*
             d_M^{1/(2p)}S_{p,m}^{1-2/p}\\
 &+\frac{6\sqrt2\,\mathfrak b_M d_M^{1/p}}{\sqrt{d_m}}
             S_{p,m}^{1-1/p}.
 \end{split}}
 \tag{26}
\]
The two powers of \(S\) distinguish the spectral and fixed-basis returns. They are not combined by pretending that \(D_t\) commutes with \(H_t\). All expressions are zero when \(S=0\).

**What is paid:** an explicit full-source boundary form, its positive one-sided credit, and its contraction with the actual adaptive density. **What is not paid:** a summable original-schedule bound for (26), or a bound for the bulk increment below. Lower moment order does not by itself supply the missing factor \(1/m\).

## 7. Restore the complete signed residue increment and all return costs

### 7.1 Use the accepted enclosure, not another completion proof

**[COFINAL_FAMILY | CONDITIONAL: inherited zeta-only Q2/Q3 inputs]** Fix \(0<\epsilon<1/8\), \(\sigma=3/8+\epsilon\), and the inherited constant \(A_\epsilon\) satisfying \(\left|\mathfrak a(x+it)\right|\le A_\epsilon\log(|t|+3)\) for \(x\in[\sigma,3/2]\). Keep the fixed classical zero-count constant \(C_N\) of Q3. Use the accepted matrices
\(F_r^Y=\mathsf P_r^Y-\mathsf N_r^Y\), with every critical pair and off-critical quartet counted exactly as in Q3. At \(Y=M^3\), its proof supplies endpoint error bounds whose sum is at most
\[
 q_m=2000C_NM^{-13/8}.
\]
The accepted Q2 fee is
\[
 r_{\epsilon,m}=16M^{-3/2}
       +(10000L_++300A_\epsilon+20)M^{-5/2}.
\]
The full source-return normalization, multiplicities and tails are inherited, not re-proved here. The packet expressly accepts only this enclosure, not the retained signed energy. fileciteturn16file0L148-L170 fileciteturn16file0L642-L676

With the **unchanged** \(T\), define
\[
 \begin{split}
 \mathscr D^\circ_{p,m}(Y)=\operatorname{Tr}T\bigl[
 &\widehat{\Pi_m\mathsf P_m^Y\Pi_m}-\Pi_M\mathsf P_M^Y\Pi_M\\
 &+\Pi_M\mathsf N_M^Y\Pi_M
               -\widehat{\Pi_m\mathsf N_m^Y\Pi_m}\bigr].
 \end{split}
 \tag{27}
\]
This keeps the old positive energy, the new positive credit, the new negative energy and the old negative credit with their original signs. No separate bound for \(\mathsf N_r^Y\) has been substituted.

Define also the finite, signed boundary return
\[
 j_r^Y(W)=\operatorname{Tr}\left[W(F_r^Y-\Pi_rF_r^Y\Pi_r)\right].
\]
The exact finite identity is
\[
 \mathscr D_{p,m}(Y)
 =\mathscr D^\circ_{p,m}(Y)+j_m^Y(T_{oo})-j_M^Y(T).
 \tag{28}
\]
It is merely the ledger that restores the correction; it is not counted as a new signed supplier. In particular, the positive old boundary energy cannot be thrown away.

Since \(\|A-\Pi_rA\Pi_r\|\le2\|A\|\), the accepted endpoint errors give
\[
 |(j_m^Y-j_M^Y)-(j_m-j_M)|\le2q_m\tau.
\]
A more economical return to the exact source uses the projected endpoint errors directly. They are still bounded by their original norms, so
\[
 \boxed{
 \begin{split}
 \Xi-\Gamma
 &=\mathscr D^\circ_{p,m}(Y)+j_m(T_{oo})-j_M(T)-e_m\tau
                                      +\mathcal E^\circ_{p,m},\\
 |\mathcal E^\circ_{p,m}|&\le q_m\tau,\\
 \mathcal J_{\sigma,M^2}(T)-\Gamma
 &=\mathscr D^\circ_{p,m}(Y)+j_m(T_{oo})-j_M(T)-e_m\tau
                                      +\widetilde{\mathcal E}^\circ_{p,m},\\
 |\widetilde{\mathcal E}^\circ_{p,m}|&\le(q_m+r_{\epsilon,m})\tau.
 \end{split}}
 \tag{29}
\]
The better coefficient here is \(q_m\), not \(3q_m\), because the proof compares the **projected** full sources directly with their residue sums. The factor \(3q_m\) will be needed only when returning through Q3's already widened sufficient envelope in (33).

### 7.2 Theorem Q04-R: the actual-weight relative-form inequality

Apply (21) at the new endpoint to \(W=T\), while retaining the old boundary return with its sign. Equation (29) proves:

**Theorem Q04-R. [COFINAL_FAMILY | CONDITIONAL: inherited Q2/Q3 zeta-only return]** For \(\log m\ge1024\), every fixed even \(p\ge4\), and the original full adaptive \(T\),
\[
 \boxed{
 \begin{split}
 \mathcal J_{\sigma,M^2}(T)-\Gamma
 \le{}&\mathscr D^\circ_{p,m}(M^3)+j_m(T_{oo})
          -\frac{L_+}{32}\beta_M\\
 &+320000L_+^6\operatorname{Tr}(T\Pi_M)
          -(e_m-q_m-r_{\epsilon,m})\tau.
 \end{split}}
 \tag{30}
\]
This is an executed simultaneous relative-form estimate for the full signed residue return. The boundary credit is positive because (17) was established for the **actual prime source**, not because the residue increments were assumed monotone. Its bulk charge is displayed and has not been paid at the moment-drift scale.

For the exact original \(\Xi-\Gamma\), omit \(r_{\epsilon,m}\) from (30). For the smaller credit, the exact rule is
\[
 \mathcal J-c=(\mathcal J-\Gamma)+(\Gamma-c),
 \qquad \Xi-c=(\Xi-\Gamma)+(\Gamma-c).
 \tag{31}
\]
The nonnegative \(\Gamma-c\), on the inherited late domain, must therefore be **added** to the upper bound. It is not discarded or spent twice.

### 7.3 All couplings and the fixed-basis account still occur

For either projected or unprojected new-endpoint source matrix \(A_M\),
\[
 \operatorname{Tr}(TA_M)
 =\operatorname{Tr}(T_{oo}A_{oo})
   +2\Re\operatorname{Tr}(T_{no}A_{on})
   +\operatorname{Tr}(T_{nn}A_{nn}).
 \tag{32}
\]
The old subtraction affects only the old block. The \(\Pi_M\) in (27) itself mixes all \(2M+1\) coordinates, including the new pair; no new-mode block is frozen. Both full boundary returns in (29) use those same weights. Equations (25) and the displayed formula for \(j_r(D)\) retain the diagonal companion separately.

The primes have not been exchanged for a modified zero process: (12), (16) and (17) were computed using their original coefficients, and (27)-(29) use the independently accepted return to that same source. All continuous, archimedean and endpoint terms have the exact signs in (3) and (29). No contour height or physical bandwidth was changed.

### 7.4 First OPEN hypothesis; no consumer gain is claimed

To reach specifically Q3(23), use (28) and the \(2q_m\tau\) boundary-return error. One sufficient, now fully costed statement is
\[
 \boxed{
 \begin{gathered}
 \mathscr D^\circ_{p,m}(M^3)+\mathcal B_{p,m}
       -(e_m-3q_m-r_{\epsilon,m})\tau\\
 \le\frac{Z_p(m)}{pm}+\frac{v_{p,m}}pZ_p(m),\qquad
 v_{p,m}\ge0,\quad\sum_m v_{p,m}<\infty,
 \end{gathered}}
 \tag{33}
\]
for arbitrarily large fixed even \(p\), after a permitted \(p\)-dependent starting index. The weaker signed interface retains
\(j_m^Y-j_M^Y\) exactly in (28) instead of replacing it by \(\mathcal B+2q_m\tau\). A direct bound through (29) likewise need not pay the redundant widening through Q3(23).

**[COFINAL_FAMILY | CONDITIONAL: OPEN hypothesis, not a theorem]** Equation (33) is not established. It is the first unsupported source-specific estimate in this calculation. The bulk quantity in (27), contracted with the full adaptive density, has no supplied favorable sign or rate. The signed version of (33) is also open.

In particular, a per-endpoint \((\log m)^{7/2}\) correction is subpolynomial for a **floor return**, but cannot simply be summed as an admissible **one-step drift error**. The actual-density bound (26) has lower moment order but lacks a proved original-schedule \(1/m\) or summable factor. Replacing it by \(3(\mathfrak b_m+\mathfrak b_M)\tau\) would be still worse. Neither (18) nor (30) therefore gives an order-independent moment exponent.

This remains research debt, not evidence that (33), its weaker signed form, or SP is false. The narrower boundary estimate is proved; the demanded full signed gain is not. No improved full-floor exponent follows from an improved bound on one column.

## 8. Exact transport obstruction survives endpoint cancellation

### 8.1 A corrected original edge mode

**[COFINAL_FAMILY | PAPER: original carrier, control vector only]** The packet rules out polynomial full-space leakage before boundary correction. The following test asks whether exact endpoint vanishing repairs that failure; it does not. The overlap and its existing scope are inherited. fileciteturn16file0L20-L33 fileciteturn16file0L58-L73

Use the centered **production** basis
\[
 \varphi_{r,j}(x)=(-1)^jL_r^{-1/2}e^{2\pi ijx/L_r},
 \qquad |x|\le L_r/2.
\]
The diagonal phase \((-1)^j\) is important: this is the translate of (1), so its endpoint trace is still the sum of coefficients. With
\(a=L/L_+\), \(h=1-a\), the exact extension coefficients are
\[
 \widetilde O_{kj}=(-1)^{j+k}\sqrt a\,
                    \operatorname{sinc}(\pi(j-ak)).
 \tag{34}
\]
Let
\[
 g_m=\Pi_me_m=e_m-\eta_m/d_m,
 \qquad\|g_m\|^2=1-1/d_m,
 \qquad\eta_m^{\mathsf T}g_m=0.
\]
Its physical function vanishes at both old endpoints. Its zero extension is continuous and has a square-integrable weak first derivative. Thus this is not the packet's nonvanishing-endpoint constant example.

Take the first omitted new label \(k=m+2\), and write
\(\varepsilon=kh\). For \(m\ge16\), the elementary bounds already used in the packet give
\[
 0<\varepsilon\le\tfrac12,\qquad a\ge\tfrac12,
                  \qquad\varepsilon\ge1/L_+.
\]
For every old \(j\), direct simplification of (34) yields
\[
 \widetilde O_{kj}=-\frac{c_\varepsilon}{ak-j},
 \qquad c_\varepsilon=\frac{\sqrt a\sin(\pi\varepsilon)}\pi>0.
\]
Consequently
\[
 |(\widetilde O g_m)_k|
 =c_\varepsilon\left[
       \frac1{2-\varepsilon}
       -\frac1{d_m}\sum_{j=-m}^m\frac1{ak-j}\right].
\]
Here \(ak-j\ge1+(m-j)\), so the sum is at most \(H_{d_m}\). For \(d_m\ge33\),
\(H_{d_m}/d_m\le1/4\): use \(H_d\le1+\log d\), verify the bound at 33, and then its monotonicity. The bracket is therefore at least \(1/4\). Finally
\(\sin(\pi\varepsilon)\ge2\varepsilon\) gives
\[
 \boxed{
 \|(I-P_M)E f_{g_m}\|_2
 \ge |(\widetilde O g_m)_{m+2}|
 \ge\frac1{2\sqrt2\pi L_+},\qquad m\ge16.}
 \tag{35}
\]
Normalizing \(g_m\) can only increase this lower bound, since \(\|g_m\|<1\).

For a proposed uniform return bound \(Cm^{-b}\), define its margin to be the proposed upper bound minus the actual leakage of the normalized \(g_m\). Equation (35) gives the explicit upper envelope
\[
 U_m=Cm^{-b}-\frac1{2\sqrt2\pi\log(m+1)}<0
\]
eventually, for every fixed \(C,b>0\). Thus that control violates the proposed rate. The exact scope is **the theorem shape of carrier-wide polynomial L2 return on the endpoint-zero subspace**. This control is not a negative eigenvector of the CCM source and not the actual adaptive weight. It does not refute the requested source-form estimate.

### 8.2 The actual-weight energy entrance cannot be silently assumed

There is also an exact density-level version of the uncorrected energy obstruction. Fix \(m\), and let \(W\succeq0\) be a matrix on the old carrier, in particular \(W=T_{oo}\). The large-\(|k|\) expansion of (34) is
\[
 \widetilde O_{kj}
 =\frac{(-1)^k\sin(\pi ak)}{\pi\sqrt a\,k}
          +O_m(k^{-2}),
\]
uniformly over the finitely many old labels. Therefore
\[
 \boxed{
 \lim_{R\to\infty}\frac1R
  \sum_{1\le|k|\le R}k^2
       (\widetilde O W\widetilde O^*)_{kk}
 =\frac{\eta_m^*W\eta_m}{\pi^2a}.}
 \tag{36}
\]
Indeed, the leading positive and negative \(k\) sums each have mean \(1/2\), because \(0<a<1\) makes the elementary geometric sum of \(e^{2\pi iak}\) bounded. The remainder is \(O_m(\log R)\), hence vanishes after division by \(R\). No irrationality assertion about a logarithm ratio is used.

For the actual old density,
\[
 \eta_m^*T_{oo}\eta_m
 =\int_0^1\left[
 \widehat\eta_m^*G_t\widehat\eta_m
             +\sum_{j\in I_m}D_{t,jj}\right]dt.
\]
A strictly positive value makes the original weighted Fourier energy infinite. We have not proved that this value is positive or zero for the actual source. Equation (25) bounds it after normalization; it does not make it exactly zero. A positive diagonal companion contribution alone would suffice for strict positivity here.

After correction by \(\Pi_m\), the endpoint trace vanishes and the squared-frequency energy is finite, but (35) shows that finiteness alone does not give a polynomial rate. This is why the source-form correction (19)-(30), rather than an unbudgeted appeal to an H1 projection theorem, was needed. The user's independently checked energy obstruction and its restricted scope remain intact. fileciteturn16file0L103-L135

## 9. One audit target, discriminators and bounded next choices

### One precise independent-audit target

**Audit Theorem Q04-R, inequality (30), as one actual-source relative-form statement.** The exact target is
\[
 \forall m:\log m\ge1024,\quad
 \mathcal J_{\sigma,(m+1)^2}(T)-\Gamma
 \le \mathscr D^\circ_{p,m}((m+1)^3)+j_m(T_{oo})
 -\frac{\log(m+1)}{32}b_{m+1}^*Tb_{m+1}
 +320000\log^6(m+1)\operatorname{Tr}(T\Pi_{m+1})
 -(e_m-q_m-r_{\epsilon,m})\operatorname{Tr}T,
\]
for the unchanged full adaptive weight and inherited zeta-only Q2/Q3 inputs.

The load-bearing new checks are the circle spacing and actual-prefix mean-square estimate (6)-(8), the full Hilbert boundary image including its normalization (10)-(12), the literal kernel contraction and complete arithmetic scalar budget (14)-(17), and the square completion in (18). The return check must retain the old signed boundary term, both endpoint projectors, every old/new coupling, the diagonal account, and the \(q_m+r_{\epsilon,m}\) rather than an invented zero return. Report the first false inequality, sign, normalization or constant, with a correction if available.

Acceptance proves this boundary-sector comparison only. It does **not** prove (33), a better full-floor exponent, SP, or RH. The reported Q3 audit is an input; no independent audit of Q04-R has been run here.

### DISCRIMINATOR

**[FINITE_CELL | CONDITIONAL: proposed enclosure, not executed]** Keep the finite signed boundary terms when testing Q3's zero-extra-error margin:
\[
 F_{p,m}^{Y}
 =\frac{Z_p(m)}{pm}
  -\mathscr D^\circ_{p,m}(Y)
  -j_m^Y(T_{oo})+j_M^Y(T)
  +(e_m-q_m-r_{\epsilon,m})\tau.
\]
This is the same finite Q3 sufficient margin, with no newly discarded sector. A nonnegative lower envelope certifies only that finite-cell sufficient inequality. A strictly negative upper envelope rejects only that specified inequality, not a later-start or summable-error cofinal statement. To test the original source residual or the finite contour directly through (29), use its stated two-sided error width instead of silently treating the sufficient envelope as necessary.

For zero-consistent boundary-density results, the discriminating functional is
\(\eta_m^*T_{oo}\eta_m\), with the full spectral path and diagonal account retained. Equation (36) distinguishes an exact zero from any positive value, however small. Floating-point clipping of negative eigenvalues cannot certify that this quantity vanishes.

### Two next re-representations; neither is a supplied estimate

**A. Boundary-zero transport in the logarithmic source-form norm, not L2 or H1 alone.** Apply the exact physical/prime translation form to the residual of an endpoint-zero test function, retaining the main/residual cross form and residual/residual form together. Contract that signed return with the actual spectral and diagonal densities. The needed output is a form comparison with a cofinal drift budget, not just a Fourier tail bound. **Kill-power/cost:** high against an invalid small-transport inference, with (35) as the first mandatory control; medium analytic setup, high source-correlation cost. Boundary correction is now paid by (19)-(29), but the bulk transport sign is still open.

**B. A dissipative double-commutator certificate in original frequency coordinates.** Use a specified real diagonal multiplier \(A\) on the original mode labels and the exact spectral sign of \(\operatorname{Tr}[G_t[A,[A,H_t]]]\le0\). In an eigenbasis of \(H_t\), this sign follows from the decreasing function \((-x)_+^{p-1}\); in the original basis the diagonal of the double commutator is zero, so its contraction with D_t is exactly zero. The diagonal account still contributes to any unmatched remainder and must be retained there. Seek a source-derived decomposition of the actual arithmetic increment into a favorable multiple of this insertion plus an independently bounded remainder. **Kill-power/cost:** high against a missing eigenvalue-changing term or a fabricated commutator cancellation; low finite algebra cost, high arithmetic remainder cost. The first test is the literal neighboring-mode coefficient and its old/new interface, not an arbitrary replacement matrix. No such decomposition or remainder estimate has been established here.

The three cross-domain checks actually used in this answer were finite Fourier sampling on the actual integer lattice, a full-source relative quadratic-form comparison, and a Sobolev/trace transport falsifier on the corrected original edge mode. They close the boundary column and its form return, not the remaining arithmetic bulk.

## 10. Claim ledger and closeout

| Claim | Scope | Verifier | Disposition |
|---|---|---|---|
| Q1 complete-background increment | COFINAL_FAMILY | PAPER | Inherited with its reported independent audit; not re-proved |
| Q2 truncation and Q3 residue enclosure | COFINAL_FAMILY | CONDITIONAL | Inherited with their named zeta dependencies and reported independent audits; not re-proved |
| Actual modes, histories, full affine T and both credits | FINITE_CELL | PAPER | Unchanged source inputs |
| Actual-integer circle sampling and joint vector bound (6)-(8) | COFINAL_FAMILY | PAPER | New derivation for every original r>=4 and every prefix |
| Full-source normalized boundary image (12) | COFINAL_FAMILY | PAPER | New, unconditional relative to the accepted literal source inputs |
| Complete arithmetic boundary self-return (16) | COFINAL_FAMILY | PAPER | New, all primes/powers and both continuous terms included |
| Positive full-source boundary energy (17) and relative form (18) | COFINAL_FAMILY | PAPER | New, log r>=1024 |
| Exact boundary correction and form-norm return (19)-(22) | COFINAL_FAMILY | PAPER | Paid; not a bound for the compressed bulk |
| Actual adaptive spectral and companion boundary bounds (23)-(26) | COFINAL_FAMILY | PAPER | New, full H_t and original diagonal account retained |
| Simultaneous signed return (27)-(29) | COFINAL_FAMILY | CONDITIONAL | Exact ledger using inherited Q2/Q3 error suppliers |
| Theorem Q04-R, (30) | COFINAL_FAMILY | CONDITIONAL | New PAPER audit target; boundary credit with explicit bulk charge |
| Consumer-sufficient central estimate (33) | COFINAL_FAMILY | CONDITIONAL | OPEN hypothesis; not a supplier |
| Endpoint-zero edge leakage lower bound (35) | COFINAL_FAMILY | PAPER | Rejects a uniform transport theorem shape only |
| Actual-weight Fourier-energy discriminator (36) | FINITE_CELL | PAPER | Exact identity for fixed m; actual positivity/vanishing not decided |
| Full-floor improvement / SP / RH | COFINAL_FAMILY | CONDITIONAL | Not established; no claim made |

**What became smaller:** the normalized endpoint-evaluation direction and its complete source-form coupling now have a polylogarithmic bound; its full-source Rayleigh quotient has a proved positive sign on an explicit cofinal domain. Removing that direction from either endpoint has a fully restored source-form cost. The actual negative density has the quantitative boundary bounds (24)-(26).

**What did not become smaller:** the proved exponent of the full negative spectrum and the missing bulk adaptive arithmetic drift. Neither the positive boundary credit nor the paid source correction closes (33). This is proof progress on a boundary sector and **NO_PROGRESS for the requested central consumer**.

**What was ruled out:** carrier-wide polynomial L2 return remains false even on the endpoint-zero subspace. The proof uses an original corrected edge vector and a single exact omitted coefficient. No claim is made that this vector is selected by the source's negative spectral density.

**Do not repeat:** another bare zero-residue identity; substitution of the endpoint moment increment for a sign estimate; a polynomial full-space transport assertion; the implication “finite H1 energy, therefore uniform polynomial return”; deletion of the fixed-basis diagonal account; or promotion of a polylogarithmic per-endpoint fee to a summable per-step fee.

### Registered checks and their outcomes

The working update selected the normalized boundary source image as the next quantity to estimate, rather than a general-vector transport norm. The resulting bound is (12), with the physical normalization restored in Section 6. No successful central-drift prediction was registered.

Before the local diagnostics, the stated checks were the sign of the boundary return against the literal matrix and whether endpoint cancellation repairs polynomial projection transport. The exact calculations (20) and (35) settle those questions: the return keeps its negative self-energy term, and endpoint cancellation does not repair the proposed rate. The edge calculation is an explicit theorem-shape countercheck, not a retroactive prediction of central success.

Local floating-point diagnostics, **not interval certificates**, independently assembled both the literal W02-WR-prime source and B-C at r=4,8,16,32. Their maximum entry discrepancy was below 9.6e-15. The scalar kernel contraction (14) disagreed by less than 3.5e-15, and the boundary-correction identity by less than 6.4e-15. These small cells do not test the cofinal threshold in (17).

On a deliberately shifted source-path detector, with -10I added solely to create nonzero negative weights, the boundary-return identity and negative-functional identity agreed within 1.9e-12. Flipping the boundary self-energy sign produced discrepancy about 3737.14; deleting the diagonal companion produced discrepancy about 805.09. The artificial shift is not a premise, a production matrix, or a CCM counterexample. Corrected-edge coefficient checks at m=16,32,64,128,1024 agreed with the exact factorization; the proof of (35), not these checks, supplies the quantifier.

The previous Q3 enclosure prediction now has the attachment's independent PASS disposition. It remains a truncation/return acceptance only. The new audit prediction is that Theorem Q04-R survives with the stated conservative constants; its highest-risk checks are the normalization by sqrt(d), the scalar kernel's Hilbert-row sign, and the old/new boundary-return orientation.

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
  ACTUAL_CONSUMER_REQUIREMENT: "For every eta>0, an eventual bound lambda_min(K_m)>=-C_eta*m^eta on every original full cell."
  ORIGINAL_REQUESTED_OBJECT: "A source-specific relative-form estimate for the complete signed residue increment with actual adaptive T, sufficient for Q3(23) or a genuinely better full floor."
  ORIGINAL_OBJECT_IS: UNKNOWN
  NECESSITY_NOTE: "Neither this boundary correction, this companion nor this one-step relative interface is asserted necessary for SP."
  KNOWN_WEAKER_INTERFACES:
    - "The exact signed-error full-credit form of (29) can suffice without the stronger upper envelope (33)."
    - "A bound for K_r compressed to b_r-perp returns to the full floor via (22), with an explicit polylogarithmic fee. That compressed bound is not supplied."
    - "A direct same-source every-eta floor or order-independent large-even-moment exponent reaches the unchanged consumer without this transport method."
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "Actual integer sampling pays the full boundary source image; its actual prime contraction is small and its full energy positive; actual adaptive boundary density and full signed returns are estimated."
  REOPEN_TRIGGER: "A proved cofinal bound for the joint boundary-zero bulk and restored boundary terms, or a better floor for that bulk, without an assumed carrier-wide polynomial transport rate."
  MATHEMATICAL_IMPOSSIBILITY_EVIDENCE: NONE_FOR_CCM_OR_SP
AUXILIARY_THEOREM_SHAPE_FINDING:
  CLAIM_REJECTED: "There exist fixed C,b>0 such that old-to-new L2 projection leakage is <=C*m^(-b) for every endpoint-zero unit vector in the original full old space, eventually."
  KILL_SCOPE: THEOREM_SHAPE
  FAILURE_TYPE: COUNTEREXAMPLE
  EPISTEMIC_STATUS: MATHEMATICALLY_DEAD
  KILL_EVIDENCE_KIND: NEGATIVE_UPPER_ENVELOPE_FOR_PROPOSED_LEAKAGE_MARGIN
  PINNED_EVIDENCE: "This artifact, (34)-(35), g_m=Pi_m e_m, with the request's literal overlap (1)."
  SCOPE: COFINAL_FAMILY
  VERIFIER: PAPER
  ACTUAL_ADAPTIVE_WEIGHT_COUNTEREXAMPLE: false
  REPAIR: "Require and prove a restriction on the actual spectral density, or estimate the complete signed source-form return instead of uniform L2 leakage."
MEMORY_ENTRY:
  iteration: FULL_CCM_MOMENT_Q04
  target: FULL_ADAPTIVE_RELATIVE_SIGNED_ARITHMETIC_DRIFT
  status: OPEN
  cognitive_operator_used: LITERATURE_BRIDGE
  consumer_progress: NO_PROGRESS
  paid_term: "Full-source boundary image, positive boundary energy, and exact source-form return with actual adaptive-density bounds."
  failed_strategy: "Inferring a complete drift estimate from removal of endpoint traces and finite Fourier energy."
  smallest_unpaid_input: "Signed bulk residue increment and restored boundary terms in (33), or the weaker exact signed version."
  invariant_learned: "One normalized boundary direction is source-controlled, but physical trace restores d/L and endpoint-zero edge modes still have logarithmic leakage."
  forbidden_future_move: "Calling a per-endpoint polylogarithmic correction summable per step, or treating the new relative bound as a bound for its still-uncontrolled bulk."
  next_decisive_test: "One independent PAPER audit of Theorem Q04-R (30); then only a genuine bulk signed supplier changes the consumer."
```

**Final proposal:** submit the single actual-weight relative-form inequality (30) to the audit below. A successful audit accepts the calculated boundary comparison, not (33). A failure reopens that comparison at the first erroneous sign or constant; it does not establish a negative answer for the original source. Another representation with the same uncontrolled bulk should not be counted as a consumer advance.

## CODEX DIRECTIVE

Independently audit **Theorem Q04-R, inequality (30)** for the literal full CCM source and unchanged adaptive T. Check the actual-integer sampling bound, the complete normalized boundary image, the scalar prime–pole boundary estimate and positive full-source energy, then their relative-form contraction and Q2/Q3 return with every old/new coupling and diagonal-account term. Return either this PAPER inequality with exactly its named dependencies and explicit charges, or the first false equality/inequality and a corrected statement. Do not infer (33), a full-floor improvement, SP or RH; do not run Lean, edit the repository, or substitute a generic control weight for the actual T.
