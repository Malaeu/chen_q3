# STATUS: TRY_GOAL058_SOURCE_LOG_SYMBOL_COMPRESSION_TRANSFER

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_LOG_SYMBOL_COMPRESSION_TRANSFER
OUTCOME: OPEN_SPECTRAL_SPREAD
REQUEST_ID: REQ-2026-09-26-COMPRESSION-SPECTRAL-SPREAD
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_COMPRESSION_SPECTRAL_SPREAD
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 49bf42b6267c2ac1cf5a0571272318866834b104
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-FIRST-OMITTED-COMPRESSION
REQUEST_SHA256_VERIFIED: 6375cf87c0175f15f913fdd1343f39489f95e53065f32d4e3957e18e8d800ad9
PREDECESSOR_VERDICT_SHA256_VERIFIED: 2e4c9122664351489d288bfe6eed3df630566a0e1474f3de6451562874e5912e
PREDECESSOR_GIT_BLOB_VERIFIED: 87307c3d21383e45a2b7cec904a3c715c0d55f78
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SOURCE_J_EVENTUAL_POSITIVE_LOWER_BOUND: NOT_ESTABLISHED
SOURCE_J_UNBOUNDED_NEGATIVE_UPPER_BOUND: NOT_ESTABLISHED
SOURCE_DETERMINANT_SIGN: NOT_ESTABLISHED
EXACT_THREE_CONTRACTIONS: EXPANDED_WITH_FULL_SOURCE_AND_DIAGONAL
Q5_EDGE_IN_DETERMINANT: RETAINED_THROUGH_SECOND_ORDER
L2_ERROR_GRAM_ANISOTROPY: PROVED_FOR_ALL_m_GE_16_IN_ORIGINAL_COLUMN_UNITS
L2_ERROR_GRAM_EQUALS_WEIL_COMPRESSION: false
LOG_SYMBOL_RELATIVE_TRANSFER: NOT_ESTABLISHED
R_CONDITION_NUMBER_EVENTUALLY_BOUNDED: PROVED_FROM_SOURCE_L2_DATA
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: L2_ERROR_GEOMETRY_ONLY_NOT_THE_REQUESTED_WEIL_SPECTRAL_SIGN
CLOSED_REQUESTED_SIGN_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_LOG_SYMBOL_TRANSFER_ON_FIXED_ERROR_COLUMNS
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
COLUMN_UNITS_CHANGED: false
NEW_RANK_ONE_SEED_SELECTED: false
COMPRESSION_DOMINANCE: NOT_ESTABLISHED
PLANE_AXIS_GAP: NOT_ESTABLISHED
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SPECTRAL_SPREAD.** No eventual positive lower bound for the actual \(J_m\), and no negative upper bound on an unbounded selected-index set, is established here. The first unresolved comparison is the complete signed determinant contraction in (8)–(10), jointly with the trace-square expression (9). **The strict rank-one package is not refuted, and it has not passed this necessary test.**

There is a new source estimate, but it concerns a different, explicitly identified matrix. For the **ordinary \(L^2\) Gram matrix of the exact projection errors**, the original derivative-column units force
\[
0<\mathsf E_{00}(m)\le \frac{4}{\Omega_m^4}\mathsf E_{11}(m),
\qquad \Omega_m=\frac{2\pi(m+1)}{\log m},\qquad m\ge16.
\tag{G}
\]
Both physical exterior tails and the Q5 edge term are used in proving this inequality. They are not discarded. **There is no established transfer of (G) to the indefinite Weil compression \(A\).** The distinct next test isolates that transfer through the complete archimedean multiplier, pole term, and prime-power correlations; it neither chooses a new seed nor raises an analytic cutoff.

## 1. Source lock and decision boundary

**[COFINAL_FAMILY | PAPER]** Read all **4,197 bytes** of the authoritative TXT and all **31,411 bytes** of the predecessor. Their local SHA-256 values are recorded above. The predecessor's local Git blob agrees with the blob fetched at the requested commit. The bootstrap was fetched from `rh_clean` and read through its response-format section. The request accepts the earlier convergence and necessary-condition algebra, not the selected-source sign. Those results are used without repeating their proofs. fileciteturn55file0L20-L25 fileciteturn58file0L3-L5

Keep the same fixed \(P\), selected indices \(m=J_P+j+2\), recurrence endpoint \(N=6m-1\), original \(5m\) splice, and Fourier carrier \(-m,\ldots,m\). Write
\[
L=\log m,\quad b_L=L/2,\quad \omega_n=2\pi n/L,
\quad B=[b,e],\quad e_n=-\omega_n^2b_n+\epsilon_m,
\quad \epsilon_m=2G'(b_L)/\sqrt L.
\tag{1}
\]
The columns are the inherited projections of the exact even functions \(G,G''\). They are real and even in \(n\). No relative rescaling, whitening, trial substitution, or change of \(x\) is made. The source identities Q5/Q6 retain precisely the boundary term in (1). fileciteturn61file0L2-L2

The seed-independent compression test does not use the selected activity vector. Its absence from the following formulas is elimination of that variable from a **necessary** test, not replacement by an arbitrary \(x\). The full selected row and its MIX terms remain unchanged downstream.

The three outcomes have the scope fixed by the request: a strictly negative upper bound on an unbounded selected set excludes the proposed package on every eventual tail; an eventual positive lower bound only passes the necessary test. Neither outcome would itself prove an axis gap. fileciteturn55file0L56-L75

## 2. Evaluation of the three complete source contractions

### 2.1. Grouped scalar source functional, including the diagonal

**[FINITE_CELL | PAPER]** For real even carrier vectors \(u,v\), define
\[
\begin{aligned}
Q_m[u,v](t)={}&
\sum_{n=-m}^{m}2(1-t/L)u_nv_n\cos(\omega_nt)\\
&+\sum_{-m\le n<q\le m}(u_nv_q+u_qv_n)
\frac{\sin(\omega_qt)-\sin(\omega_nt)}{\pi(n-q)},
\qquad 0\le t\le L.
\end{aligned}
\tag{2}
\]
In particular, \(Q_m[u,v](0)=2\sum_nu_nv_n\). Put
\[
c_m^{\rm ar}=\gamma_{\rm EM}+\log\!\left(4\pi\frac{m-1}{m+1}\right),
\qquad p_L(u)=\sum_{n=-m}^{m}\frac{u_n}{L^2+16\pi^2n^2}.
\]
Then the literal full source contraction is
\[
\boxed{
\begin{aligned}
\mathcal C_m(u,v)={}&32L^3\sinh^2(L/4)\,p_L(u)p_L(v)
-c_m^{\rm ar}\sum_{n=-m}^{m}u_nv_n\\
&-\int_0^L\frac{e^{t/2}Q_m[u,v](t)-2\sum_nu_nv_n}{e^t-e^{-t}}\,dt\\
&-\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}\,Q_m[u,v](\log\nu).
\end{aligned}}
\tag{3}
\]
This is an exact reduction to the source sums and integrals, **not a numerical evaluation or a sign estimate**. The odd factor in the second rank-one part of W02 pairs to zero with even \(u,v\); only that exact parity cancellation was used in its first line. The complete matrix was not replaced by W02. The integral's subtraction stays grouped at zero, and the separate diagonal is the first line of (2), not a divided-difference limit. These are the inspected CCM entry definitions at the pin. fileciteturn59file0L2-L2

For clarity, the kernel appearing in any minor below is exactly
\[
\begin{aligned}
K_{nn'}={}&\frac{32L\sinh^2(L/4)(L^2-16\pi^2nn')}
{(L^2+16\pi^2n^2)(L^2+16\pi^2n'^2)}
-c_m^{\rm ar}\delta_{nn'}\\
&-\int_0^L\frac{e^{t/2}Q_{nn'}(t)-2\delta_{nn'}}{e^t-e^{-t}}\,dt
-\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}Q_{nn'}(\log\nu),
\end{aligned}
\tag{4}
\]
where \(Q_{nn}(t)=2(1-t/L)\cos(\omega_nt)\) and, for \(n\ne n'\),
\(Q_{nn'}(t)=[\sin(\omega_{n'}t)-\sin(\omega_nt)]/[\pi(n-n')]\).
Every finite-source prime power occurs, with its original sign.

### 2.2. Q5 exposes the determinant's boundary dependence

**[FINITE_CELL | PAPER]** Set \(f_n=\omega_n^2b_n\), and use only the following six complete source contractions:
\[
\begin{array}{lll}
U=\mathcal C_m(b,b),& V=\mathcal C_m(b,f),& W=\mathcal C_m(f,f),\\
C=\mathcal C_m(b,\mathbf1),& D=\mathcal C_m(f,\mathbf1),& E=\mathcal C_m(\mathbf1,\mathbf1).
\end{array}
\tag{5}
\]
These letters are local contraction labels, not recurrence moments or the error Gram matrix \(\mathsf E\). Equation (3) evaluates each with the full finite ranges.

The three requested entries, with the conjugate convention reduced only by the proved reality of the columns, are therefore
\[
\boxed{
A_{00}=U,\qquad A_{01}=-V+\epsilon_m C,\qquad
A_{11}=W-2\epsilon_mD+\epsilon_m^2E.
}
\tag{6}
\]
The corresponding exact Gram entries are
\[
\begin{aligned}
R_{00}&=\sum_nb_n^2,\\
R_{01}&=-\sum_n\omega_n^2b_n^2+\epsilon_m\sum_nb_n,\\
R_{11}&=\sum_n\omega_n^4b_n^2-2\epsilon_m\sum_n\omega_n^2b_n
+(2m+1)\epsilon_m^2.
\end{aligned}
\tag{7}
\]
Thus the source boundary term also stays in \(\kappa_R\), which is computed in these original units.

The determinant and trace-square become the **joint** expressions
\[
\boxed{
D_A=(UW-V^2)+2\epsilon_m(VC-UD)+\epsilon_m^2(UE-C^2),
}
\tag{8}
\]
\[
\boxed{
T_A=U^2+2(-V+\epsilon_m C)^2+(W-2\epsilon_mD+\epsilon_m^2E)^2.
}
\tag{9}
\]
In particular, the edge does not disappear as an algebraic identity. No actual-source sign or nonvanishing is assigned to any coefficient in (8).

### 2.3. Full minor comparison and the earliest unpaid step

**[FINITE_CELL | PAPER]** For \(I=(n<q)\) in the carrier, the exact two-row minor is
\[
w_I=(\omega_n^2-\omega_q^2)b_nb_q+\epsilon_m(b_n-b_q).
\]
The inherited minor expansion specializes to
\[
\boxed{
D_A=\sum_{\substack{-m\le n<q\le m\\-m\le r<s\le m}}
 w_{nq}w_{rs}\,[K_{nr}K_{qs}-K_{ns}K_{qr}].
}
\tag{10}
\]
The sums include every ordered choice of \(I,J\), including overlapping pairs. All diagonal appearances of K use (4). Reflection makes \(w_{n,-n}=0\), but gives no sign to the other minors. Formula (10) is the predecessor's permitted determinant identity with the literal Q5 rows inserted. fileciteturn58file0L2-L2

**[COFINAL_FAMILY | PAPER]** The earliest unclosed comparison in this evaluation is a one-sided enclosure of the complete compound contraction (10), **jointly with** (6) and (9). For example, the negative outcome would require a proved lower separation
\[
\left|(UW-V^2)+2\epsilon_m(VC-UD)+\epsilon_m^2(UE-C^2)\right|
-\frac{2\kappa_R}{4\kappa_R^2+1}
\left[U^2+2(-V+\epsilon_mC)^2+(W-2\epsilon_mD+\epsilon_m^2E)^2\right]
\ge\frac{h(m)}{4\kappa_R^2+1}>0
\tag{11}
\]
on an explicitly unbounded selected-index set. The positive outcome needs the reverse strict separation on the whole selected tail. **Neither separation is obtained.** The formula specifies the unpaid minor comparison; it is not offered as a new test under a new name.

A sign for \(D_A\) alone would not decide (11). Nor is proving \(A_{00}\ne0\) a necessary prerequisite for every possible proof: another entry can carry the compression. No such unnecessary interface is imposed.

## 3. What the available bounds do—and do not—decide

**[COFINAL_FAMILY | PAPER]** The admitted continuity theorem and its analytic tail estimates bound absolute form errors. They can transfer a **future signed estimate** of a finite analytic approximant, but they do not already supply a relative determinant estimate for (8). The predecessor explicitly leaves this source sign open. fileciteturn58file0L2-L2 fileciteturn62file0L2-L2

In particular, separate upper bounds for \(T_A\) and \(|D_A|\) decide neither orientation of their difference. Smallness of all entries also does not fix their spread: both terms in \(J_m\) scale quadratically under a common scaling of A. No estimate is inferred from replacing the full source by its positive pole part or by its diagonal-blind commutator.

If \(A=0\), then \(J_m=0\); this is not either requested strict outcome. If \(D_A=0\) but \(A\ne0\), then \(J_m=2\kappa_RT_A>0\) at that cell, but no such selected-family identity is proved. If an enclosure straddles zero, it is not an equality certificate. No finite cell was numerically tested.

## 4. A source-specific geometric result, not a Weil-sign result

### 4.1. The exact error Gram matrix

**[FINITE_CELL | PAPER]** Let
\[
\Delta_0=T_mG-G,\qquad \Delta_1=T_mG''-G'',
\qquad \mathsf E_{ab}=\langle\Delta_a,\Delta_b\rangle_{L^2(\mathbb R)}.
\tag{12}
\]
The matrix \(\mathsf E\) is an ordinary \(L^2\) Gram matrix. It is **not** \(A_{ab}=\operatorname{Re}\mathcal W(\Delta_a,\Delta_b)\). For \(G_0=G,G_1=G''\), Parseval and the exact exterior values give
\[
\mathsf E_{ab}=
\sum_{|n|>m}\overline{\widetilde G_{a,n}}\widetilde G_{b,n}
+\int_{|t|>b_L}G_a(t)G_b(t)\,dt.
\tag{13}
\]
Both exterior half-lines occur. The finite carrier has not been enlarged: the infinite sum only represents its projection error.

### 4.2. The exterior derivative energy pays for the Q5 constant

**[COFINAL_FAMILY | PAPER] New derivation.** The exact source kernel, not a replacement trial, is
\[
G(t)=e^{t/2}\sum_{r=1}^{\infty}(24v_r-16v_r^2)e^{-v_r},
\qquad v_r=\pi r^2e^{2t}\quad(t\ge0).
\tag{14}
\]
This is the inherited \(G=\mathcal E h_*\). Its evenness and source normalization are unchanged. fileciteturn61file0L2-L2

Twice differentiating this normally convergent tail series gives
\[
F(t):=-G''(t)=e^{t/2}\sum_{r\ge1}Q_2(v_r)e^{-v_r},
\quad Q_2(v)=64v^4-448v^3+660v^2-150v.
\tag{15}
\]
For \(v\ge16\),
\[
Q_2(v)\ge36v^4>0,\qquad Q_2'(v)\le262v^3,
\qquad \frac12+\frac{2vQ_2'(v)}{Q_2(v)}-2v\le-v.
\]
Consequently, for \(m\ge16\), \(t\ge b_L\), and \(s\ge0\),
\[
F(t)>0,\qquad F(t+s)\le e^{-\pi e^{2t}s}F(t)
\le e^{-\pi m s}F(t).
\tag{16}
\]
The bound follows termwise from its logarithmic derivative and then by summation; it is uniform on the entire exterior half-line.

Write \(E_{11}^{\rm out}=2\int_{b_L}^{\infty}F(t)^2dt>0\). Since G and G' vanish at infinity, \(G'(b_L)=\int_{b_L}^{\infty}F\). For \(M_F(t)=\int_t^\infty F\), (16) gives \(M_F(t)\le F(t)/(\pi m)\). Hence
\[
G'(b_L)^2=2\int_{b_L}^{\infty}F(t)M_F(t)dt
\le \frac{E_{11}^{\rm out}}{\pi m},
\qquad
\epsilon_m^2\le\frac{4E_{11}^{\rm out}}{\pi mL}.
\tag{17}
\]
Also
\[
|G(t)|=\int_t^\infty(u-t)F(u)du\le \frac{F(t)}{(\pi m)^2},
\qquad
E_{00}^{\rm out}\le(\pi m)^{-4}E_{11}^{\rm out}.
\tag{18}
\]
Thus the boundary term is controlled by the **actual exterior derivative energy**, not set to zero.

### 4.3. All omitted modes, without a seed or a cutoff increase

**[COFINAL_FAMILY | PAPER] New derivation.** For every \(|n|>m\), Q5 can be rearranged as the square-summable identity
\[
\widetilde b_n=\frac{\epsilon_m-\widetilde e_n}{\omega_n^2}.
\]
This rearrangement is legal: both \((\widetilde e_n/\omega_n^2)\) and \((\epsilon_m/\omega_n^2)\) are in \(\ell^2\). It is not the prohibited separation of two nonsummable terms in \(\widetilde e_n=-\omega_n^2\widetilde b_n+\epsilon_m\).

Put \(\Omega_m=2\pi(m+1)/L\) and
\[
q_m=\frac{8}{3\pi L}\left(1+\frac1m\right)^4,
\qquad c_m^{\rm out}=\left[\frac{2(1+1/m)}{L}\right]^4.
\]
Because
\[
\sum_{|n|>m}\omega_n^{-4}\le\frac{L^4}{24\pi^4m^3},
\]
(17) implies
\[
\sqrt{E_{00}^{\rm in}}\le\Omega_m^{-2}
\left(\sqrt{E_{11}^{\rm in}}+\sqrt{q_mE_{11}^{\rm out}}\right),
\qquad
E_{00}^{\rm out}\le\Omega_m^{-4}c_m^{\rm out}E_{11}^{\rm out}.
\]
Ordinary Cauchy–Schwarz therefore gives
\[
\mathsf E_{00}\le\Omega_m^{-4}(1+q_m+c_m^{\rm out})\mathsf E_{11}
\le4\Omega_m^{-4}\mathsf E_{11},\qquad m\ge16.
\tag{19}
\]
For the last constant use \(L\ge2\), \(\pi>3\), and \((17/16)^4<2\), giving \(q_m<8/9\) and \(c_m^{\rm out}<2\). This proves (G) for every selected m in the stated range, in the original column units.

Both diagonal masses are nonzero. In fact \(\mathsf E\) is positive definite: if a linear combination of the errors vanished, its exterior part would give \(aG+bG''=0\) on a half-line. The local version of (18) gives \(|G(t)|\le F(t)/(\pi e^{2t})^2\), while both G and F are nonzero there. Thus \(|G''/G|\to\infty\), excluding any constant proportionality. **This is positivity of an \(L^2\) Gram matrix, not positivity of the Weil form.**

An explicit source lower scale, useful only for a future transfer, follows from the r=1 summand of (15):
\[
\boxed{
\mathsf E_{11}\ge E_{11}^{\rm out}\ge e_*(m):=
\frac{1296(\pi m)^8}{\sqrt{\pi(\pi m+1)}}e^{-2\pi m-2}>0.
}
\tag{20}
\]
Indeed, after \(v=\pi e^{2t}\), retain just the interval \([\pi m,\pi m+1]\) in
\(\pi^{-1/2}\int_{\pi m}^{\infty}Q_2(v)^2v^{-1/2}e^{-2v}dv\).

### 4.4. The original Gram condition number stays controlled

**[COFINAL_FAMILY | PAPER]** Let \(R_\infty=(\langle G_a,G_b\rangle)_{a,b=0,1}\), with eigenvalues \(r_+\ge r_->0\). The preceding independence also proves \(r_->0\). Orthogonality of the actual projection gives
\[
R=R_\infty-\mathsf E.
\]
Using the predecessor's source coefficient constants \(d_a(m)\), define the explicit bound
\[
\varepsilon_R(m)=E_{00}^{\rm out}+E_{11}^{\rm out}
+\frac{2[d_0(m)^2+d_1(m)^2]}{3m^3}.
\tag{21}
\]
Then \(\operatorname{tr}\mathsf E\le\varepsilon_R(m)\to0\): the exterior terms vanish and \(d_a=O(L^{3/2})\) follows directly from their fixed source derivative integrals. These are the already supplied coefficients, not fitted rates. fileciteturn62file0L2-L2

On the explicitly specified source tail \(\varepsilon_R(m)\le r_-/2\),
\[
\boxed{1\le\kappa_R\le K_*:=2r_+/r_-<\infty.}
\tag{22}
\]
The constants are fixed \(L^2\) source data, independent of J and of a desired sign. No column whitening is performed.

## 5. One distinct falsifiable PAPER test: transfer the log symbol, not the seed

### TEST_SOURCE_LOG_SYMBOL_TRANSFER_ON_FIXED_ERROR_COLUMNS

The results above say that the **error geometry** is strongly anisotropic. They do not say whether the complete signed Weil form respects that geometry. The next test addresses exactly this different mechanism.

### 5.1. Full-source residual against a prescribed scale

**[FINITE_CELL | PAPER]** Use the unitary continuous Fourier transform
\(\widehat f(\xi)=(2\pi)^{-1/2}\int f(t)e^{-i\xi t}dt\), and keep the full error correlations
\[
\Gamma_{ab}(t)=\operatorname{Re}\int_{\mathbb R}
\left[\overline{\Delta_a(u)}\Delta_b(u+t)+\overline{\Delta_a(u)}\Delta_b(u-t)\right]du.
\]
The archimedean part of the admitted global form has the exact multiplier
\[
\mathfrak a(\xi)=-(\gamma_{\rm EM}+\log4\pi)
+2\int_0^\infty\frac{1-e^{t/2}\cos(\xi t)}{e^t-e^{-t}}dt
=\operatorname{Re}\psi(1/4+i\xi/2)-\log\pi.
\tag{23}
\]
Here \(\psi\) is the **digamma function**, the logarithmic derivative of the gamma function. This external special-function identification uses only the integral identity for psi and its value at 1/2; it supplies no source sign. Substitution \(u=2t\) gives \(\operatorname{Re}\psi(1/4+i\xi/2)-\psi(1/2)\) for the integral term. citeturn291102view0turn291102view1

The Fourier representation is legitimate for these exact errors: they are smooth on each side of the two physical boundaries, rapidly decreasing outside, and have finite jumps. Their transforms are bounded near zero and \(O(1/|\xi|)\) at infinity. The logarithmic multiplier is integrable against their Fourier products. The diagonal identity can also be obtained by the nonnegative \(1-\cos\) integral and then polarized. No positivity of W is used, and no unproved insertion of an L² Fourier series into W is made. The large-frequency expansion of psi explains the prescribed scale below but is not used as a uniform error bound. citeturn658078view2

Set, independently of A,
\[
\ell_m=\log\frac{m+1}{L}>0\quad(m\ge16).
\]
Define the **complete residual matrix**
\[
\boxed{
\begin{aligned}
\mathcal N_{ab}(m)={}&
\operatorname{Re}\int_{\mathbb R}
[\mathfrak a(\xi)-\ell_m]\overline{\widehat{\Delta_a}(\xi)}
\widehat{\Delta_b}(\xi)d\xi\\
&+\int_0^\infty2\cosh(t/2)\Gamma_{ab}(t)dt
-\sum_{\nu=2}^{\infty}\frac{\Lambda(\nu)}{\sqrt\nu}\Gamma_{ab}(\log\nu).
\end{aligned}}
\tag{24}
\]
Thus \(A=\ell_m\mathsf E+\mathcal N\) exactly. The archimedean constant and endpoint subtraction have been incorporated into (23), not deleted. Both exterior physical tails remain in every correlation and Fourier transform. Every returned prime power, including \(\nu>m\), remains in (24). The global/finite equivalence is the admitted radical-error identity; it is not a redefinition of finite K.

The next falsifiable target is the following three **entrywise, compatible relative bounds**, on an explicitly specified selected tail:
\[
\boxed{
|\mathcal N_{00}|\le\tfrac14\ell_m\mathsf E_{00},\qquad
|\mathcal N_{11}|\le\tfrac14\ell_m\mathsf E_{11},\qquad
|\mathcal N_{01}|\le\tfrac14\ell_m\sqrt{\mathsf E_{00}\mathsf E_{11}}.
}
\tag{25}
\]
They concern the two original error columns, not a new unit seed or an arbitrary selected vector. They are stronger than necessary for J>0 and are **not established here**. They do not assume that A or W is positive. In particular, the entrywise conditions need not make A positive definite.

### 5.2. Why this would decide the spectral test

**[COFINAL_FAMILY | CONDITIONAL]** If (25) holds, then
\[
A_{11}\ge\tfrac34\ell_m\mathsf E_{11}>0,\quad
|A_{00}|\le\tfrac54\ell_m\mathsf E_{00},\quad
|A_{01}|\le\tfrac54\ell_m\sqrt{\mathsf E_{00}\mathsf E_{11}}.
\]
Only the last inequality uses ordinary L² Cauchy–Schwarz for \(\mathsf E\). It does not use a Cauchy inequality for W.

For the actual singular values of A, set \(z=s_2/s_1\). Using \(s_1\ge A_{11}\), the determinant identity, and (19),
\[
z=\frac{|D_A|}{s_1^2}
\le\frac{|A_{00}|}{A_{11}}+\frac{|A_{01}|^2}{A_{11}^2}
\le\frac{40}{9}\frac{\mathsf E_{00}}{\mathsf E_{11}}
\le\frac{160}{9\Omega_m^4}.
\tag{26}
\]
This works for an indefinite A as well. It bounds the determinant **relative to the same surviving diagonal scale**, not by unrelated absolute estimates.

On the tail also satisfying (22) and
\(\Omega_m^4\ge640K_*/9\), one has \(z\le1/(4K_*)\). The exact scalar factorization gives
\[
J_m=s_1^2(2\kappa_R-z)(1-2\kappa_Rz)
\ge\frac78s_1^2
\ge\boxed{\frac{63}{128}\ell_m^2e_*(m)^2>0.}
\tag{27}
\]
All functions in this conditional margin come from independent source geometry and the prescribed scale, not from an unknown minimum of J. The selected index scope would be those j with m=J_P+j+2 beyond the admitted rank-two threshold, m≥16, (21)≤r_-/2, the displayed frequency threshold, and the proved tail of (25).

**Equation (27) is not a `SPECTRAL_SPREAD_POSITIVE` result:** its essential premise (25) is unproved. If that premise were proved, the first separate original obligation would still be nonzero alpha for the original first-omitted seed, followed by its relative couplings and the activity of the actual selected vector. Passing J would settle none of those by itself.

### 5.3. Why the existing absolute estimates do not supply (25)

**[COFINAL_FAMILY | PAPER]** For instance, the accepted continuity bound gives only
\[
|\mathcal N_{11}|\le C_WU_1(m)^2+\ell_m\mathsf E_{11}.
\tag{28}
\]
That supplied right-hand side is at least \(\ell_m\mathsf E_{11}\), already larger than the quarter-scale required in (25). This particular triangle-bound attempt therefore cannot certify even the second inequality. **It does not prove that the actual residual violates it.** The same difficulty remains for the mixed entry.

The mechanism to investigate is the joint cancellation in (24): the continuous-frequency archimedean deviation together with the complete pole and prime correlations. The periodic omitted-mode expansion does not make the errors band-limited on the real line. Their window jumps and exterior functions create continuous-frequency leakage. Replacing \(\mathfrak a(\xi)\) by \(\ell_m\) pointwise, discarding those frequencies, or truncating the returned prime sum at m would invalidate the test.

Thus this is not J under a different name. It is a proposed quantitative transfer from a newly proved, nondegenerate source L² scale to the full signed form. It can fail while J remains positive. A source failure refutes only this transfer certificate; it is not the negative spectral-spread outcome.

## 6. Adversarial checks, route map, and closeout

**[ABSTRACT | PAPER]** The strongest objection is the attempted jump from L² anisotropy to Weil anisotropy. That jump is explicitly unpaid: (25) is exactly the missing relative input. A positive Gram matrix by itself places no corresponding restriction on an unrelated signed bilinear form. No such substitution is made.

The boundary-erasure check also matters. In (8), the coefficient of \(\epsilon_m^2\) is \(UE-C^2\); it is not identically zero. For the abstract calibration K=I and a nonconstant real b, it equals \(\|b\|^2\|\mathbf1\|^2-(b^T\mathbf1)^2>0\). This calibrates the proposed erasure, not the selected matrix. No arbitrary K is used as a source counterexample.

**[COFINAL_FAMILY | PAPER]** Registration and scoring: the announced boundary check found surviving linear and quadratic edge contributions, but did not determine their source signs. No source-sign prediction was registered. Before checking the supplied absolute bounds against the new relative scale, the expectation was that a relative debt would remain; (28) confirms that limitation of this particular bounding attempt. No successful transfer or spectral outcome is scored retrospectively.

| Re-representation | Discriminating power | PAPER cost and risk |
|---|---|---|
| **Chosen: exact error L² geometry plus full log-symbol residual (12)–(25).** | A proved relative transfer would force an eventual positive J in the original units, with (27), without selecting a seed. | Three source-relative residual estimates. Main risk: prime correlations and continuous-frequency leakage are not small at the required scale. |
| **Alternative: full compound-matrix determinant (3)–(11).** | A joint negative upper certificate for J could still exclude every rank-one seed satisfying the package. | All signed diagonal and off-diagonal minors, with correlated trace control. No minor positivity or independent coarse budgets are available. |

Only the first next test is commissioned. Neither route authorizes numerical diagnostics or an analytic cutoff campaign.

The structural bridge used here is projection-error geometry to a Fourier multiplier with an explicitly retained arithmetic remainder. The tested vanishing mechanism was edge cancellation; it did not remove the determinant's boundary terms. The family-deciding candidate is now (25), not another leading-vector rotation.

**What closed:** the source L² anisotropy estimate (19), its exterior lower scale (20), and eventual boundedness of the original Gram condition number (22). **What did not close:** either requested sign of J, the source determinant comparison (11), or the log-symbol transfer. No source theorem shape was killed. This is a geometric supplier result, not a compression-dominance or spectral-sign pass.

```yaml
DOWNSTREAM_CONSUMER: necessary_spectral_test_for_the_strict_rank_one_compression_package
ACTUAL_CONSUMER_REQUIREMENT: J_m_positive_is_necessary_only_not_a_full_dominance_certificate
ORIGINAL_REQUESTED_OBJECT: selected_source_sign_of_J_m_with_strict_family_envelopes
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
ORIGINAL_OBJECT_QUALIFICATION: J_m_gt_zero_is_necessary_only_for_the_named_strict_package_not_for_the_true_axis_or_fixed_mixture
KNOWN_WEAKER_INTERFACES:
  - direct_paid_actual_projective_sector_without_a_rank_one_package
  - direct_actual_axis_quadratic_bound_without_a_whole_cone_certificate
  - actual_fixed_mixture_or_full_quartic_bound_without_this_spectral_filter
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: full_compound_contraction_10_or_8_jointly_with_trace_square_9_in_11
MINIMAL_MISSING_ESTIMATE: a_one_sided_joint_source_envelope_for_the_determinant_to_trace_comparison
NEW_CLOSED_QUANTIFIER: every_selected_m_GE_16_has_E00_LE_4_Omega_to_minus4_E11_for_the_exact_L2_errors
L2_RESULT_PROMOTED_TO_WEIL_SIGN: false
DISCRIMINATOR: TEST_SOURCE_LOG_SYMBOL_TRANSFER_ON_FIXED_ERROR_COLUMNS
REOPEN_TRIGGER: source_proof_of_25_or_a_direct_strict_joint_source_envelope_deciding_11
KILLED_REQUESTED_THEOREM_SHAPE: NONE
RANK_ONE_PACKAGE_DEAD: false
WHOLE_CONE_CERTIFICATE_DEAD: false
ACTUAL_FIXED_MIXTURE_KILLED: false
NOVELTY_AXIS: exact_exterior_energy_pays_Q5_edge_and_yields_uniform_L2_error_anisotropy_without_a_seed
MEMORY_ENTRY:
  target: selected_compression_spectral_spread
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: original_column_error_geometry_is_anisotropic_but_the_complete_Weil_form_needs_an_independent_relative_transfer
  forbidden_future_move: erase_epsilon_from_the_determinant_or_identify_L2_error_Gram_with_Weil_compression
  next_decisive_test: TEST_SOURCE_LOG_SYMBOL_TRANSFER_ON_FIXED_ERROR_COLUMNS
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_LOG_SYMBOL_TRANSFER_ON_FIXED_ERROR_COLUMNS`, on paper, for the unchanged source errors \(T_mG-G\) and \(T_mG''-G''\).** Independently check the new geometric supplier (15)–(22), then adjudicate the three compatible residual bounds (25) using the exact complete residual (24) and the prescribed \(\ell_m=\log((m+1)/\log m)\). Keep the original column units, both window jumps, both exterior physical tails, the archimedean subtraction encoded in (23), and every returned prime power. Prove any tail threshold from explicit source estimates. A successful delivery may invoke (26)–(27) to report only an eventual positive necessary spectral test; it may not report compression dominance. A failure of (25) refutes only this particular transfer certificate, not J>0 or the rank-one package. No new seed, numerical diagnostics, mathematical runtime, Lean, repository write, source replacement, arbitrary selected x, first-tau-sign, Schur-floor, route promotion, or RH claim is authorized.
