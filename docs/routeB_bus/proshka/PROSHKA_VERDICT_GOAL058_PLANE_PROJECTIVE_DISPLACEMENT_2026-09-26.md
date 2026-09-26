# STATUS: TRY_GOAL058_SOURCE_PLANE_PROJECTIVE_DISPLACEMENT

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_PLANE_PROJECTIVE_DISPLACEMENT
OUTCOME: OPEN_PLANE_DIRECTION
REQUEST_ID: REQ-2026-09-26-PLANE-PROJECTIVE-DISPLACEMENT
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_PLANE_PROJECTIVE_DIRECTION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: d9cbb345c015acc51326685efe5c978935464f4a
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-CONE-AXIS-GROUND-ANGLE
REQUEST_SHA256_VERIFIED: 2d47a7afc44920ab5e67012fe28441dac8c31fe7c89180171d0dc154e0574e7a
PREDECESSOR_VERDICT_SHA256_VERIFIED: 51312b0e7c883a74609e9ab074083b2b01644680624f5e01ffdd21ef34772445
PREDECESSOR_GIT_BLOB_VERIFIED: 7298ac232d6f11ef643cddd8ea51461c292a87af
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
ACTUAL_HOMOGENEOUS_COORDINATES: FULL_DIAGONAL_PLUS_DIVIDED_DIFFERENCE_CONTRACTIONS_BELOW
NONZERO_SOURCE_PROJECTIVE_CHART: NOT_ESTABLISHED
PAID_SOURCE_DIRECTIONAL_SECTOR: NOT_ESTABLISHED
PLANE_AXIS_GAP: NOT_ESTABLISHED
PLANE_AXIS_OBSTRUCTION: NOT_ESTABLISHED
SOURCE_FIRST_OMITTED_FOURIER_PAIR: NONZERO_FROM_EXACT_Q5_EDGE
FIRST_OMITTED_TRANSVERSE_COEFFICIENT: EXACTLY_ZERO_IN_SOURCE_DEFINED_ROTATED_BASIS
OMITTED_PAIR_COMPRESSION_DOMINANCE: NOT_ESTABLISHED
WHOLE_CONE_CERTIFICATE: UNPROVED_NOT_REFUTED
ACTUAL_FIXED_MIXTURE_DISCRIMINANT: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
PROGRESS_CLASS: NO_PROGRESS
PROGRESS_QUALIFICATION: NO_REQUESTED_AXIS_QUANTIFIER_CLOSED_NEW_EXACT_REPRESENTATIONS_ONLY
ROUTE_SCORE: 2
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_FIRST_OMITTED_PAIR_COMPRESSION_DOMINANCE
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_PLANE_DIRECTION.** I did not obtain a source-derived projective sector for the actual plane axis, an eventual paid axis gap, or an unbounded axis obstruction. In particular, **neither the plane-axis test nor the whole-cone certificate is refuted**.

The displacement test reduces the two actual homogeneous coordinates to the explicit signed contractions (5)–(8) below. Its mixed-entry cancellation removes a displacement pair, **not the physical edge term**. The first unpaid object is the diagonal-complete contraction giving the proposed chart denominator, together with the corresponding directional comparison—not invertibility of the plane Gram matrix.

One different next test is specified in §6. It uses exact errors of the two global radical lifts and a source-defined first-omitted Fourier pair. The pair is provably nonzero, and its transverse combination has an exactly zero first-omitted coefficient. **Dominance of that pair in the full signed compression remains a hypothesis to test**, not an axis result.

## 1. Source lock and the precise target

**[COFINAL_FAMILY | PAPER]** Read all **4,358 bytes** of the authoritative TXT and all **26,804 bytes** of the local predecessor Markdown. The predecessor's computed SHA-256 matches the request; its computed Git blob matches `7298ac232d6f11ef643cddd8ea51461c292a87af`, returned at the requested pin. The bootstrap was fetched from `rh_clean` and read through its response-format section. The request admits the predecessor only as a representation, not as an axis-sign result. fileciteturn39file0L20-L27 fileciteturn42file0L2-L5

The repository evidence read for this review was:

| Path, relative to the repository root | Use and read boundary |
|---|---|
| `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` | Bootstrap on `rh_clean`; full protocol read. |
| `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_CONE_AXIS_GROUND_ANGLE_2026-09-26.md` | Predecessor at the pinned commit; complete local bytes read and matched by blob. |
| `q3.lean.aristotle/Q3/Proofs/RouteB/CCMFiniteWeilSourceMatrixN1.lean` | Pinned literal entry definitions, repository lines 35–125; no Lean execution. |
| `docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_NULLPLANE_LEAKAGE_SIGN_2026-09-25.md` | Pinned inherited Q5/Q6, positive endpoint derivative, radical/error-form and global-tail formulas, repository lines 180–400. |

Fix the same P and work on its admitted rank-two tail:
\[
m=J_P+j+2,\qquad N=6m-1,\qquad -m\le n\le m.
\]
The original splice is still 5m. Keep the entire selected x, the Euclidean CCM norm, and the original source phase. No recurrence moment M, \(\beta=S_N-1\), V, a, d, or \(\vartheta_m=d/(a^2+d)\) is replaced by a limit. The requested target is the actual value \(r^TP_mr\), not positivity of \(P_m\) on the whole plane. fileciteturn39file0L29-L61

Write \(b_L=L/2\), \(L=\log m\), \(\omega_n=2\pi n/L\), and \(\gamma_L=(2\pi/L)^2\). The two source columns remain
\[
 b_n=\frac{(-1)^n}{\sqrt L}\int_{-b_L}^{b_L}G(t)e^{-i\omega_nt}\,dt,
 \qquad e_n=-\gamma_Ln^2b_n+\epsilon_m,
 \quad \epsilon_m=\frac{2G'(b_L)}{\sqrt L}.
\tag{1}
\]
The accepted parity and reflection facts make B, R, A, y and r real in this convention; no parity or commutator proof is repeated. Complex conjugations in the source transforms remain in force. The Q6 template is still
\[
\mathbf d=\left(1-\frac{15}{64\pi m}\right)b-\frac{1}{16\pi m}e;
\]
**x is not replaced by this template**. Equation (1) carries both physical endpoints. fileciteturn42file0L2-L2

## 2. The actual homogeneous coordinates, without a chart assumption

**[FINITE_CELL | PAPER]** Let
\[
R=B^*B=\begin{pmatrix}R_{00}&R_{01}\\R_{01}&R_{11}\end{pmatrix},
\quad \Delta_R=\det R>0,
\quad J_R=\operatorname{adj}(R)
=\begin{pmatrix}R_{11}&-R_{01}\\-R_{01}&R_{00}\end{pmatrix}.
\]
Labels 0 and 1 here mean G and G'', not the two forcing-cone axes. Define
\[
y=B^*x,\qquad \sigma=J_Ry,
\qquad z^{x}=B\sigma=\Delta_R\Pi x,
\]
\[
q^{[0]}=R_{11}b-R_{01}e,
\qquad q^{[1]}=-R_{01}b+R_{00}e.
\tag{2}
\]
These are test vectors for contractions. They are **not replacements for the actual axis** \(u^{(1)}=\Pi K_j\Pi x\), nor for the original cell vector \(q_j\).

The requested homogeneous vector has the exact coordinates
\[
\boxed{\widehat r_a=\operatorname{Re}\langle q^{[a]},K_jz^{x}\rangle,
\qquad a=0,1.}
\tag{3}
\]
Indeed, this is simply the componentwise expansion of \(J_RB^*K_jBJ_Ry\), using real symmetric \(J_R\). The inherited relation \(\widehat r=\Delta_R^2r\) is retained. fileciteturn44file0L2-L2

All dependence on the full selected x is explicit:
\[
\sigma_a=\sum_{c=0}^1(J_R)_{ac}
\sum_{l=-m}^{m}\overline{B_{lc}}
\sum_{k'=1}^{N}F_{lk'}c_{k'},
\qquad
z^x_n=\sigma_0b_n+\sigma_1e_n.
\tag{4}
\]
Thus MIX has not been removed by a new trial vector or a separately recomputed forcing.

### 2.1. Full finite-index source contractions

**[FINITE_CELL | PAPER]** Put
\[
\mathfrak d_n=K_{j,nn},\qquad
\mathcal K_{nn'}=\frac{\mathfrak b_n-\mathfrak b_{n'}}{n-n'}\quad(n\ne n').
\]
Substitution into (3) gives
\[
\boxed{
\begin{aligned}
\widehat r_a={}&
\sum_{n=-m}^{m}\mathfrak d_n q^{[a]}_n z^x_n\\
&+\sum_{-m\le n<n'\le m}\mathcal K_{nn'}
\left(q^{[a]}_n z^x_{n'}+q^{[a]}_{n'}z^x_n\right).
\end{aligned}}
\tag{5}
\]
The real form of (5) uses the inherited reality just stated; (3)–(4) retain the conjugate-linear convention. In particular,
\[
\begin{aligned}
q^{[0]}_n&=(R_{11}+\gamma_LR_{01}n^2)b_n-R_{01}\epsilon_m,\\
q^{[1]}_n&=-(R_{01}+\gamma_LR_{00}n^2)b_n+R_{00}\epsilon_m,\\
z^x_n&=(\sigma_0-\gamma_L\sigma_1n^2)b_n+\sigma_1\epsilon_m.
\end{aligned}
\tag{6}
\]
There is no omitted central term: the n=0 contribution to the proposed denominator is
\[
\mathfrak d_0(R_{11}b_0-R_{01}\epsilon_m)
(\sigma_0b_0+\sigma_1\epsilon_m).
\]
Its sign is not known. Pairs with \(n'=-n\) are included in the second line of (5); none is treated as a diagonal limit.

Here are the complete source entries used in (5), with \(\gamma_{\rm EM}\) denoting the Euler–Mascheroni constant:
\[
\begin{aligned}
\mathfrak b_n={}&32L\sinh^2(L/4)\frac{n}{L^2+16\pi^2n^2}\\
&+\frac1\pi\int_0^L\frac{e^{t/2}\sin(\omega_nt)}{e^t-e^{-t}}\,dt
+\frac1\pi\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\sin(\omega_n\log\nu),
\end{aligned}
\tag{7}
\]
\[
\begin{aligned}
\mathfrak d_n={}&32L\sinh^2(L/4)
\frac{L^2-16\pi^2n^2}{(L^2+16\pi^2n^2)^2}
-\gamma_{\rm EM}-\log\!\left(4\pi\frac{m-1}{m+1}\right)\\
&-\int_0^L\frac{2e^{t/2}(1-t/L)\cos(\omega_nt)-2}{e^t-e^{-t}}\,dt\\
&-2\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\left(1-\frac{\log\nu}{L}\right)\cos(\omega_n\log\nu).
\end{aligned}
\tag{8}
\]
These are the predecessor's complete source data, checked against the pinned entry constructor. The plus signs in (7), the minus signs and subtraction at zero in (8), and every finite-source prime power are retained. No divided-difference continuation is substituted for (8). fileciteturn43file0L2-L2 fileciteturn45file0L2-L2

The full ranges are \(a,c\in\{0,1\}\), \(-m\le n,n',l\le m\), \(1\le k'\le6m-1\), \(2\le\nu\le m\), and \(0<t<L\) in (7)–(8), with the accepted removable-endpoint convention. All nonzero divided-difference denominators are separated explicitly from the diagonal.

### 2.2. What the derivative action actually cancels

**[FINITE_CELL | PAPER]** Use the accepted action formula, without rederiving its commutator:
\[
V=K_jb,\qquad W=K_j\mathbf1,\qquad
K_je=-\gamma_LD_F^2V+
\gamma_L\{\chi(\mathbf1^Tb)-\mathbf1(\chi^Tb)\}+\epsilon_mW.
\]
The two displacement terms cancel upon pairing with b. Consequently
\[
\boxed{
\begin{aligned}
A_{00}&=\sum_n b_nV_n,\\
A_{01}&=-\gamma_L\sum_n n^2b_nV_n+\epsilon_m\sum_nV_n,\\
A_{11}&=-\gamma_L\sum_n n^2e_nV_n
+\gamma_L\left[(e^T\chi)(\mathbf1^Tb)-(e^T\mathbf1)(\chi^Tb)\right]
+\epsilon_m e^TW.
\end{aligned}}
\tag{9}
\]
The equality \(b^TW=\mathbf1^TV\) uses symmetry of the literal K. The last term in the second line **does not cancel by that symmetry**. It is not declared nonzero either: its value is another full-source contraction. The last line retains both its displacement contribution and its physical edge contribution. The accepted derivative action is exactly the one specified in the request. fileciteturn39file0L38-L45 fileciteturn44file0L2-L2

In particular, the two coordinates in (3) are also
\[
\begin{aligned}
\widehat r_0&=(R_{11}A_{00}-R_{01}A_{01})\sigma_0
 +(R_{11}A_{01}-R_{01}A_{11})\sigma_1,\\
\widehat r_1&=(R_{00}A_{01}-R_{01}A_{00})\sigma_0
 +(R_{00}A_{11}-R_{01}A_{01})\sigma_1.
\end{aligned}
\tag{10}
\]
Equations (5) and (9)–(10) agree; neither is a one-sided estimate.

## 3. The first unpaid signed source inequality

**[COFINAL_FAMILY | PAPER]** The proposed G chart first needs a certified nonzero value of **the complete expression (5) with a=0**. A sign-separated enclosure, for example,
\[
s_0(m)\widehat r_0\ge L_0(m)>0,
\qquad s_0(m)\in\{-1,1\},
\tag{11}
\]
would establish that chart. Neither a source-derived \(L_0\) nor an alternative sign-separation certificate has been obtained here. The analogous expression with a=1 has not been certified nonzero either.

After (11), a directional interval would still require joint signed estimates for \(\widehat r_1-t_\pm\widehat r_0\), with the inequality orientation fixed by the certified sign of \(\widehat r_0\). Those expressions are again (5), with \(q^{[1]}-t_\pm q^{[0]}\) in the first slot and the **same** \(z^x\) in the second. The unknown is therefore a specific full-source cancellation, not a missing definition of a ratio.

This identifies the first unpaid contraction of the requested chart method. It does **not** make (11) necessary for every homogeneous proof of the axis sign: the G'' chart or a homogeneous sector could avoid it. Neither such alternative was completed.

**Why the admitted information does not pay it.** Rank two of B proves \(\Delta_R>0\), not nonvanishing of \(J_RA J_Ry\). The displacement representation supplies both terms of (5), but no lower envelope for their sum. An upper estimate such as
\( |\langle q^{[a]},K_jz^x\rangle|\le\|q^{[a]}\|\|K_j\|\|z^x\|\)
contains zero and loses the relative information needed for a chart. The previously designated Ferrers budget B(m) concerns an omitted recurrence tail, not these retained-carrier contractions. The recurrence moments determine \(\vartheta_m\), not the direction selected by A and the full y. Finally, the accepted global radical identities do not assert \(K_jB=0\); their finite-projection errors remain. The predecessor explicitly leaves this cancellation and the axis sign open. fileciteturn43file0L2-L2 fileciteturn44file0L2-L2

This is **NO_DERIVATION**, not a proof that suitable source estimates cannot exist. No lower or upper source envelope deciding the requested sign is supplied by this review.

## 4. Complete directional validation, including zero cases

**[FINITE_CELL | PAPER]** Keep the exact transformed-plane data
\[
\begin{aligned}
\mathcal I_{kn}&=\frac{m^{1/4}}{\sqrt L}
\sum_{v=1}^{m}v^{-\overline{s_n}}
\int_{v/m}^{1}\mathsf P_{2k}(t)t^{\overline{s_n}-1}\,dt,
\quad s_n=\tfrac12-i\omega_n,\\
Z_{ka}&=(-1)^k\sum_{n=-m}^{m}\mathcal I_{kn}B_{na},\\
\ell_a&=\operatorname{Re}\sum_{k=1}^{N}p_kZ_{ka},\qquad
S_{ab}=\operatorname{Re}\sum_{k=1}^{N}
\frac{\overline{Z_{ka}}Z_{kb}}{\mu_k},\\
P_m&=\vartheta_m M S-\ell\ell^T.
\end{aligned}
\tag{12}
\]
The finite lower limits, conjugation, phases, and full ranges \(1\le k\le N\), \(-m\le n\le m\), \(1\le v\le m\) have not changed. Neither lower coherent moment is deleted by converting an incomplete integral into a complete one. In the plane-axis Green representation both moments are retained, and only their previously proved plane-specific relation \(\Sigma_1^{(1)}=-\Sigma_0^{(1)}/2\) may be applied. No such identification is made for the full forcing. fileciteturn43file0L2-L2 fileciteturn44file0L2-L2

If \(\widehat r_0\ne0\), set t=\(\widehat r_1/\widehat r_0\) and define
\[
\phi_m(t)=P_{00}+2P_{01}t+P_{11}t^2,
\qquad
\psi_m(t)=S_{00}+2S_{01}t+S_{11}t^2.
\]
Then, exactly,
\[
\mathfrak F_1=\frac{\widehat r_0^2}{\Delta_R^4}\phi_m(t),
\qquad G_{11}=\frac{\widehat r_0^2}{\Delta_R^4}\psi_m(t).
\tag{13}
\]
For a **proved** interval \([t_-,t_+]\), a quadratic check must include both endpoints and the stationary point \(-P_{01}/P_{11}\) when \(P_{11}\ne0\) and that point lies inside. The analogous check applies to \(\psi_m\); a linear or constant polynomial is handled without dividing by its zero quadratic coefficient. For coefficient enclosures, the check must cover all coefficient values actually allowed by those enclosures, not just midpoint vertices.

**[COFINAL_FAMILY | CONDITIONAL]** If source-derived functions give \(\phi_m\ge h(m)>0\) and \(\psi_m\le s(m)>0\) on the entire certified sector, then \(\eta_1=h/(Ms)\) is a paid gap. Positivity of \(\phi_m\) already forces \(\psi_m>0\), because \(P_m=\vartheta_mMS-\ell\ell^T\). For an obstruction one instead needs a proved upper bound \(\phi_m\le0\) and independently \(\psi_m>0\) at the actual direction on an unbounded selected-index set. **No such sector or functions h,s were derived here.**

**[FINITE_CELL | PAPER]** The degenerate cases are not charts to divide through:

- If r=0, then \(u^{(1)}=0\), \(G_{11}=c_1=\mathfrak F_1=0\). This is a vacuous axis, not either requested nonzero-axis verdict.
- If \(\widehat r_0=0\) but \(\widehat r_1\ne0\), use the G'' chart. At that exact point \(\mathfrak F_1=\widehat r_1^2P_{11}/\Delta_R^4\), and \(G_{11}=\widehat r_1^2S_{11}/\Delta_R^4\). A neighborhood crossing the G chart boundary must be covered by this chart or homogeneous coordinates.
- If r is nonzero but \(r^TSr=0\), the transformed axis is zero, so \(\ell^Tr=0\) as well. Rank two of B alone does not prove S is positive definite. This case is also vacuous.

There is no obtained directional sector to compare with P in this review. Replacing that missing sector by every plane direction would silently strengthen and change the requested test.

## 5. Strongest attack and the representation boundary

**[ABSTRACT | PAPER]** The decisive objection to a displacement-only shortcut is already admitted: the commutator does not determine the diagonal. Here the more specific obstruction to an attempted proof is visible in (5). Both the literal diagonal and the off-diagonal contribution are signed; smallness of their sum cannot fix the direction of the resulting two-vector. Their cancellation must be estimated jointly. Equations (7)–(9) do not bypass that requirement.

**[FINITE_CELL | PAPER]** The pre-test prediction was that symmetry might simplify a mixed contraction without removing the directional cancellation. The displacement pair in \(A_{01}\) does cancel in (9); the term \(\epsilon_m\sum_nV_n\) remains. Thus the algebraic simplification is confirmed. No prediction of an axis gap or obstruction was registered, and none is retrospectively scored as obtained.

The unsuccessful step is the transition from this exact algebra to a source-uniform signed envelope for (5). This is why the progress header does not promote the new formulas into a successful directional certificate.

## 6. One distinct next PAPER test: the first omitted Fourier pair

### TEST_SOURCE_FIRST_OMITTED_PAIR_COMPRESSION_DOMINANCE

This is a test of the **compression of exact projection errors**, before any projective ratio or angular inequality is evaluated. It is not a new choice of x, K, U, or an arbitrary plane direction.

### 6.1. Exact error representation, with global tails retained

**[FINITE_CELL | PAPER]** Let T_m be the inherited finite Fourier projection on the physical window, followed by zero extension. Put
\[
\Delta_0=T_mG-G,\qquad \Delta_1=T_mG''-G''.
\]
Using the already accepted radical identities for G and G'', including their admitted extension to finite syntheses plus these global lifts,
\[
\boxed{A_{ab}=\operatorname{Re}\mathcal W(\Delta_a,\Delta_b),
\qquad a,b\in\{0,1\}.}
\tag{14}
\]
This is an exact alternative representation of the same three entries in (9), not positivity of the error form. The source distinguishes precisely these errors from a kernel of the finite matrix. fileciteturn46file0L2-L2 fileciteturn47file0L2-L2

For use in this representation only, extend the window coefficient definitions (1) to every integer n, writing \(\widetilde b_n,\widetilde e_n\); on the original carrier they equal b_n,e_n. The exact Q5 identity still gives
\[
\widetilde e_n=-\omega_n^2\widetilde b_n+\epsilon_m.
\tag{15}
\]
Inside the window,
\[
\Delta_0=-\sum_{|n|>m}\widetilde b_n\psi_{n,L},\qquad
\Delta_1=-\sum_{|n|>m}\widetilde e_n\psi_{n,L}
\quad\text{in }L^2(-b_L,b_L).
\tag{16}
\]
Outside it, the errors are exactly \(-G\) and \(-G''\). **Neither exterior part is discarded.** No interchange of these L² series with the Weil form is asserted without the required stronger convergence estimates.

### 6.2. A nonzero source seed that includes the edge

**[COFINAL_FAMILY | PAPER]** Set \(n_*=m+1\), the first omitted **Fourier** index; it is unrelated to the recurrence endpoint \(N=6m-1\). Define
\[
\zeta_*=(\widetilde b_{n_*},\widetilde e_{n_*})^T,
\qquad \rho_*=\|\zeta_*\|_2.
\]
The inherited source result \(G'(b_L)>0\) for \(m\ge2\) gives \(\epsilon_m>0\). Consequently (15) proves
\[
\boxed{\rho_*>0.}
\tag{17}
\]
Both entries cannot vanish, since that would imply \(\epsilon_m=0\). This does not require either individual Fourier coefficient to be nonzero. The positivity input for the exact G is explicitly present in the pinned source chain. fileciteturn46file0L2-L2

Set
\[
\nu=\zeta_*/\rho_*,\qquad
\nu^\perp=(-\widetilde e_{n_*},\widetilde b_{n_*})^T/\rho_*,
\]
\[
E_\parallel=\nu_0\Delta_0+\nu_1\Delta_1,
\qquad E_\perp=\nu_0^\perp\Delta_0+\nu_1^\perp\Delta_1.
\]
The first omitted coefficients of these **actual error combinations** are exactly
\[
\boxed{
\operatorname{coeff}_{\pm n_*}(E_\parallel)=-\rho_*,
\qquad
\operatorname{coeff}_{\pm n_*}(E_\perp)=0.
}
\tag{18}
\]
For every omitted n the transverse coefficient is
\[
\frac{\widetilde e_{n_*}\widetilde b_n-
\widetilde b_{n_*}\widetilde e_n}{\rho_*}
=
\frac{\widetilde b_{n_*}(\omega_n^2-\omega_{n_*}^2)\widetilde b_n
+\epsilon_m(\widetilde b_n-\widetilde b_{n_*})}{\rho_*}.
\tag{19}
\]
Keep the numerator grouped. Splitting the constant-edge term off as a separate infinite Fourier series would destroy its cancellation with the other term.

This supplies a concrete discriminator against an edge-free seed: the simpler combination \(\Delta_1+\omega_{n_*}^2\Delta_0\) has first-omitted coefficient \(-\epsilon_m\ne0\), not zero. Equation (18) is the corrected, source-defined cancellation. It says nothing yet about the size or sign of the full error energies.

### 6.3. The falsifiable compression hypothesis

**[FINITE_CELL | PAPER]** Define the three real signed form values
\[
\alpha_E=\mathcal W(E_\parallel,E_\parallel),\qquad
\beta_E=\operatorname{Re}\mathcal W(E_\parallel,E_\perp),\qquad
\gamma_E=\mathcal W(E_\perp,E_\perp).
\]
They give the exact matrix decomposition
\[
A=\alpha_E\nu\nu^T+
\beta_E(\nu(\nu^\perp)^T+\nu^\perp\nu^T)
+\gamma_E\nu^\perp(\nu^\perp)^T.
\tag{20}
\]
No Cauchy inequality for \(\mathcal W\) or positivity of these scalars is used.

The next test is to **prove or falsify relative suppression of the two transverse form entries**, using (16)–(19) and the exact exterior tails. A sufficient, deliberately explicit target is a source-derived set of bounds
\[
\alpha_E\ne0,\qquad
|\beta_E|\le\delta_1(m)|\alpha_E|,\qquad
|\gamma_E|\le\delta_2(m)|\alpha_E|,
\tag{21}
\]
together with actual-source activity
\[
t^{\rm sel}=R^{-1}y\ne0,\qquad
|\nu^Tt^{\rm sel}|\ge g_*(m)\|t^{\rm sel}\|_2,
\quad g_*(m)>0,
\tag{22}
\]
and the paid comparison
\[
\boxed{
\|R\|\,\|R^{-1}\|\,
\frac{2\delta_1(m)+\delta_2(m)}{g_*(m)}<\frac12.
}
\tag{23}
\]
Every function in these bounds must come from an independently proved estimate; defining it to be the unknown relative error is not a delivery. In particular, (18) alone does not prove (21), and a nonzero error function does not prove \(\alpha_E\ne0\) for an indefinite form.

**[COFINAL_FAMILY | CONDITIONAL]** To check what this would buy, write
\(\xi_0=\nu^Tt^{\rm sel}\), \(\xi_1=(\nu^\perp)^Tt^{\rm sel}\). Then
\[
r=\alpha_E\xi_0R^{-1}\nu+
R^{-1}\left[\beta_E\xi_1\nu+
(\beta_E\xi_0+\gamma_E\xi_1)\nu^\perp\right].
\tag{24}
\]
Under (21)–(23), the norm of the second term divided by that of the first is at most the left side of (23). This follows from \(|\xi_i|\le\|t^{\rm sel}\|\) and \(\|R^{-1}\nu\|\ge1/\|R\|\). Thus the actual projective direction lies in a paid neighborhood of \(R^{-1}\nu\), with the unknown overall real sign irrelevant projectively. The original sector-versus-P test must still be performed; (23) is **not itself a PLANE_AXIS_GAP**.

If \(\alpha_E=0\), or the actual activity factor in (22) vanishes, this particular rank-one reference has no active leading term. An exact failure of (21)–(23) refutes only this proposed dominance certificate, not the axis result. The potential benefit is that the target is now an **error-form coupling with a planted zero Fourier coefficient**, independent of the ground-angle matrix P. It is not another request for the same projective ratio under a new label.

### 6.4. The full form must accompany this change of representation

**[FINITE_CELL | PAPER]** For two of the admissible error functions f,g, let
\[
\Gamma_{fg}(t)=\operatorname{Re}\int_{\mathbb R}
\left[\overline{f(s)}g(s+t)+\overline{f(s)}g(s-t)\right]ds.
\]
The full real bilinear form used for (14), (20)–(21) is the polarization of the inherited source formula:
\[
\begin{aligned}
\operatorname{Re}\mathcal W(f,g)={}&
\int_0^\infty 2\cosh(t/2)\Gamma_{fg}(t)\,dt
-\frac{\gamma_{\rm EM}+\log(4\pi)}2\Gamma_{fg}(0)\\
&-\int_0^\infty\frac{e^{t/2}\Gamma_{fg}(t)-\Gamma_{fg}(0)}{e^t-e^{-t}}\,dt
-\sum_{\nu=2}^{\infty}\frac{\Lambda(\nu)}{\sqrt\nu}\Gamma_{fg}(\log\nu).
\end{aligned}
\tag{25}
\]
In this representation the errors have the explicit noncompact exterior tails from (16). Therefore \(\Gamma_{fg}(0)\) is not assumed zero, the endpoint subtraction is retained, and prime powers **above m return**. They may not be truncated again. This is an exact re-expression of the same finite compression through the accepted radical identity, not a modification of the finite K. fileciteturn47file0L2-L2

This is also the main risk of the proposed test: elimination of one omitted Fourier pair does not control either the remaining Fourier tail, the two physical exterior tails, or their signed cross contributions to (25). All must be paid together.

### Two candidate re-representations; only the first test is commissioned

| Representation | Discriminating power | Analytic cost / principal failure risk |
|---|---|---|
| **Chosen: exact radical-error compression in the first-omitted-pair basis, (14)–(25).** | A uniform relative-coupling certificate can localize the actual direction before testing P; a source violation kills that dominance certificate. | Three signed error-form entries and actual-source activity. Requires simultaneous control of omitted Fourier modes, physical tails, and returned prime powers. |
| **Alternative: the physical boundary-jet combination \(G'(b_L)G''-G'''(b_L)G\).** | Its first derivative vanishes at both physical endpoints, potentially improving integration-by-parts tail bounds without changing the plane. | Needs derivative and exterior-tail estimates. It does not generally cancel the first omitted Fourier coefficient; endpoint cancellation alone cannot be promoted to compression dominance. Not commissioned. |

No numerical or formalization escalation is authorized by either representation.

## 7. Closeout and dependency ledger

**[COFINAL_FAMILY | PAPER]** What remains unpaid is the actual direction, starting with the signed source contractions (5)–(8), and its separation from the null directions of P. No selected tail gap and no unbounded selected obstruction has been obtained. Neither S-positivity nor small compression norm supplies that separation. No particular coordinate chart is elevated into a necessary mathematical interface.

The new error representation has two exact checks: the first-omitted coefficient pair cannot be zero, and the transverse combination (18) annihilates that pair while retaining the Q5 edge. These checks make a different test falsifiable; they do not close the requested axis quantifier. The branch point is **relative signed compression of the surviving errors**, not another algebraic identity for the cone.

The structural bridge is the already admitted radical-to-error form identity. The tested vanishing mechanism is (18), not a false assertion that all errors vanish. The family-collapsing candidate is dominance of the source-defined first-omitted-pair compression, with activity in the actual y. Its relative estimates are explicitly unproved. This review has not killed a requested theorem shape or the route.

```yaml
DOWNSTREAM_CONSUMER: strict_whole_source_cone_angular_certificate_for_the_ground_centered_moment_method
ACTUAL_CONSUMER_REQUIREMENT: paid_axis_gaps_and_the_mixed_condition_on_a_selected_tail
ORIGINAL_REQUESTED_OBJECT: actual_plane_axis_projective_direction_sufficient_to_sign_rT_P_r
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: a_projective_sector_is_a_sufficient_method_not_a_proved_necessary_interface
KNOWN_WEAKER_INTERFACES:
  - direct_homogeneous_bounds_on_rT_P_r_and_rT_S_r_without_any_nonzero_coordinate_chart
  - actual_fixed_mixture_alignment_control_without_the_whole_cone_certificate
  - direct_full_source_quartic_margin_without_the_moment_certificate
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_ESTIMATE: source_signed_directional_envelope_for_equations_5_to_8_with_the_actual_y
FIRST_UNPAID_SOURCE_CONTRACTION: equation_5_a_0_for_the_proposed_G_chart_or_a_1_for_the_alternate_chart
DISCRIMINATOR: TEST_SOURCE_FIRST_OMITTED_PAIR_COMPRESSION_DOMINANCE
REOPEN_TRIGGER: paid_actual_directional_sector_or_a_direct_homogeneous_axis_certificate
NEW_TEST_REOPEN_TRIGGER: verified_relative_error_form_bounds_21_and_actual_source_activity_22_with_23
KILLED_REQUESTED_THEOREM_SHAPE: NONE
WHOLE_CONE_CERTIFICATE_DEAD: false
ACTUAL_D_KILLED: false
NOVELTY_AXIS: diagonal_complete_actual_dual_contractions_and_exact_source_first_omitted_pair_error_basis
PREDICTION_SCORE:
  mixed_displacement_pair_cancellation: CONFIRMED
  derivative_edge_automatically_disappears: NOT_CLAIMED_AND_NOT_OBTAINED
  registered_family_axis_sign_prediction: NONE
MEMORY_ENTRY:
  target: selected_plane_projective_direction
  status: OPEN
  cognitive_operator_used: REPRESENTATION_SHIFT
  invariant_learned: physical_edge_terms_and_first_omitted_Fourier_coefficients_are_different_boundaries_and_both_survive_the_source_transfer
  forbidden_future_move: infer_nonzero_projective_coordinates_from_R_invertibility_or_treat_an_error_L2_series_as_a_Weil_form_series_without_justification
  next_decisive_test: TEST_SOURCE_FIRST_OMITTED_PAIR_COMPRESSION_DOMINANCE
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_FIRST_OMITTED_PAIR_COMPRESSION_DOMINANCE`, on paper, on the unchanged selected family.** Keep the exact source pair \((\widetilde b_{m+1},\widetilde e_{m+1})\), its Q5 edge, the error functions in (14)–(19), the actual \(t^{\rm sel}=R^{-1}B^*x\), and the complete polarized form (25). Attempt source-derived relative suppression (21), nonzero actual-source activity (22), and the paid comparison (23), or provide an exact source failure of that dominance certificate with its proper index scope. Validate the planted first-omitted coefficients (18) before any estimate; keep the grouped coefficients (19), both physical tails, diagonal/archimedean subtraction, and all returned prime powers. Do not count the rotated identity (20), an unknown minimum, or an L² norm estimate alone as success. A successful compression test still needs the original P-sector check before any plane-axis verdict. No Lean, mathematical runtime, numerical diagnostics, repository write, source replacement, whole-plane positivity substitution, first-tau-sign claim, Schur-floor claim, route promotion, or RH claim.
