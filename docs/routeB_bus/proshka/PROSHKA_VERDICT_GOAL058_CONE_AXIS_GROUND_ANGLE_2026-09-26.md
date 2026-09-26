# STATUS: TRY_GOAL058_PLANE_AXIS_SOURCE_DISPLACEMENT

```yaml
OPERATIVE_CLASS: TRY_GOAL058_PLANE_AXIS_SOURCE_DISPLACEMENT
OUTCOME: OPEN_CONE_AXIS_ANGLE
REQUEST_ID: REQ-2026-09-26-CONE-AXIS-GROUND-ANGLE
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CONE_AXIS_ANGLE
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: ee77c97849ae0267e6e364c8d6cff572a71cfad8
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-GROUND-CENTERED-ABEL-DISCRIMINANT
REQUEST_SHA256_VERIFIED: 85db1f1a51f9094c4ad3138a11cd937dc68b18d38a927837470e3cd6168499ac
PREDECESSOR_SHA256_VERIFIED: 1b4dff27d3bff6808a541db78ae1f205b2e8714f62c5123ff70f46cf8a2d56cb
PREDECESSOR_GIT_BLOB_VERIFIED: cfa3c9fbefea9281ea5acbb5963ab69a37c4cd65
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
AXIS_TEST_ORDER: PLANE_1_THEN_0
PLANE_AXIS_EVENTUAL_STRICT_GAP: NOT_ESTABLISHED
PLANE_AXIS_UNBOUNDED_OBSTRUCTION: NOT_ESTABLISHED
AXIS_0_EVENTUAL_STRICT_GAP: NOT_ESTABLISHED
AXIS_0_UNBOUNDED_OBSTRUCTION: NOT_ESTABLISHED
PLANE_AXIS_TWO_LOWER_MOMENT_RELATION: PROVED_FROM_EXACT_PLANE_EVENNESS
FULL_FORCING_TWO_LOWER_MOMENTS_IDENTIFIED: false
SOURCE_DISPLACEMENT_DERIVATIVE_COLUMN_REDUCTION: PROVED_BELOW
WHOLE_CONE_CERTIFICATE: UNPROVED_NOT_REFUTED
ACTUAL_FIXED_MIXTURE_DISCRIMINANT: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CLOSED_REQUESTED_AXIS_SIGN_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: REPRESENTATION_SHIFT
DISCRIMINATOR: TEST_SOURCE_PLANE_PROJECTIVE_DIRECTION_BY_DISPLACEMENT
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_CONE_AXIS_ANGLE.** I have not obtained an eventual strict gap or an unbounded source obstruction for either axis. In particular, **the proposed whole-cone certificate is not killed** by this review.

There is a source-specific simplification on the first axis: its two coherent lower moments satisfy an exact relation because the plane consists of even Fourier rows. This does **not** determine the angle. The further PAPER calculation below uses the **full CCM displacement identity**—a low-rank commutator identity—to reduce the action on the derivative column of the plane to two explicit source matrix actions, with the diagonal and the Q6 boundary term retained. It gives a distinct mechanism for determining the actual plane direction, not another cone-positivity derivation.

## 1. Source lock and scope

**[COFINAL_FAMILY | PAPER]** All 3,904 bytes of the authoritative TXT and all 26,315 bytes of the attached predecessor Markdown were read. The locally computed predecessor SHA-256 matches the request. Its locally computed Git blob matches the blob returned at the pinned commit. The bootstrap was fetched from `rh_clean` and read in full. The request selects the plane axis first and explicitly separates an axis obstruction from the fate of the actual fixed mixture. fileciteturn29file0L20-L34 fileciteturn29file0L42-L65 fileciteturn32file0L3-L5

Keep the fixed P, the selected indices
\[
m=J_P+j+2,\qquad N=6m-1,
\]
the original 5m splice, the Fourier carrier \(-m\le n\le m\), and the entire fixed x. The symbols M, \(\beta=S_N-1\), V, a, d and \(\vartheta_m=d/(a^2+d)\) keep their requested meanings. No recurrence moment is replaced by a limit.

The source-plane description used below is the inherited one on the admitted tail where its two columns are independent. It is not a new choice of U. The cited source identifies its columns as the finite projections of G and G'', including their physical boundary correction. fileciteturn34file0L2-L2

No Abel formula, Wronskian formula, Cauchy enclosure, weight partition, or generic copositivity criterion is rederived here.

## 2. Plane axis first: what its exact source structure does establish

### 2.1. Keep the actual plane, including Q6

**[FINITE_CELL | PAPER]** Put \(L=\log m\), \(b=L/2\), \(\omega_n=2\pi n/L\), and write the two plane columns as
\[
\begin{aligned}
B_{n,G}=\mathbf b_n
&=\frac{(-1)^n}{\sqrt L}\int_{-b}^{b}G(t)e^{-i\omega_nt}\,dt,\\
B_{n,G''}=\mathbf e_n
&=-\omega_n^2\mathbf b_n+\epsilon_m,
\qquad \epsilon_m=\frac{2G'(b)}{\sqrt L}.
\end{aligned}
\tag{1}
\]
Thus \(B=[\mathbf b,\mathbf e]\). The second line is the exact source identity Q5, with both physical endpoints already combined using the evenness of G; it is not an edge-free differentiation rule. These are the established G and G'', not substituted Gaussian trial modes. fileciteturn34file0L2-L2

For example, the retained Q6 template vector is exactly
\[
\mathbf d
=\left(1-\frac{15}{64\pi m}\right)\mathbf b
-\frac{1}{16\pi m}\mathbf e.
\tag{2}
\]
Substitution of (1) reproduces its constant boundary row
\(-G'(b)/(8\pi m\sqrt L)\). This does not replace x by \(\mathbf d\).

Let
\[
R=B^*B,\qquad A=B^*K_jB,\qquad y=B^*x,
\qquad t=R^{-1}y,\qquad r=R^{-1}At.
\]
Here **R is the plane Gram matrix**, not the scalar recurrence moment M. The frozen projection and first axis are
\[
\boxed{\Pi=BR^{-1}B^*,\qquad u^{(1)}=Br.}
\tag{3}
\]
These identities retain \(\Pi x\), not the coordinates of an independently chosen plane vector. In particular, the smallness of A does not determine the direction of r.

### 2.2. An axis-specific relation between the two lower moments

**[FINITE_CELL | PAPER]** Both columns in (1) are real and even in n. Therefore every vector in the complex plane U is even in n, and
\[
u^{(1)}_{-n}=u^{(1)}_n.
\]
In the inherited real source convention, \(x_{-n}=\overline{x_n}\); hence \(B^*x\), t, r and \(u^{(1)}\) are real as well. This reflection relation also follows directly from the incomplete-Mellin kernel and the real selected Ferrers coefficients. The selected coefficient construction and the incomplete-Mellin convention preserve those conjugations. fileciteturn33file0L2-L2 fileciteturn37file0L2-L2

For each source channel define, without identifying the channels,
\[
\Sigma_0^{(\alpha)}=\sum_{n=-m}^{m}u_n^{(\alpha)},\qquad
\Sigma_1^{(\alpha)}=\sum_{n=-m}^{m}
(\overline{s_n}-1)u_n^{(\alpha)},
\quad s_n=\tfrac12-i\omega_n.
\]
Evenness of the plane axis gives the exact finite cancellation
\[
\sum_{n=-m}^{m}\omega_nu_n^{(1)}=0,
\qquad
\boxed{\Sigma_1^{(1)}=-\tfrac12\Sigma_0^{(1)}.}
\tag{4}
\]
This is valid even before using reality. It is a result about the **plane axis**, not a relation imposed on a general forcing vector.

The relation does not say that either moment vanishes. Indeed,
\[
\Sigma_0^{(1)}
=r_G\sum_n\mathbf b_n
+r_{G''}\left[-\sum_n\omega_n^2\mathbf b_n+(2m+1)\epsilon_m\right].
\tag{5}
\]
Its actual value still depends on the source direction r.

### 2.3. Both coherent lower moments remain in the paired functional

**[FINITE_CELL | PAPER]** To exhibit what (4) changes, retain the predecessor's exact definitions
\[
A_p(t)=\sum_{k=1}^{N}
\frac{(-1)^kp_k}{2k(2k+1)}\mathsf P_{2k}(t),
\qquad \mathcal L_L=-\partial_t((1-t^2)\partial_t),
\]
\[
\mathscr H_{\alpha,r}(t)=\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}u_n^{(\alpha)}t^{\overline{s_n}-1}
\sum_{v=1}^{r}v^{-\overline{s_n}},
\quad r/m<t<(r+1)/m.
\]
For \(1\le r<m\), the two jumps are
\[
[\mathscr H_\alpha]_{r/m}
=\frac{m^{3/4}}{r\sqrt L}\Sigma_0^{(\alpha)},\qquad
[\mathscr H_\alpha']_{r/m}
=\frac{m^{7/4}}{r^2\sqrt L}\Sigma_1^{(\alpha)}.
\]
The inherited joint formula is
\[
\begin{aligned}
c_\alpha=\operatorname{Re}\Bigg\{
&\sum_{r=1}^{m-1}\int_{r/m}^{(r+1)/m}
 A_p(t)\mathcal L_L\mathscr H_{\alpha,r}(t)\,dt\\
&+\frac{m^{7/4}}{\sqrt L}
\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[\Sigma_0^{(\alpha)}\frac r m A_p'(r/m)
-\Sigma_1^{(\alpha)}A_p(r/m)\right]\Bigg\}.
\end{aligned}
\tag{6}
\]
For axis 1 only, the bracket becomes
\[
\Sigma_0^{(1)}\left[\frac r m A_p'(r/m)+\frac12A_p(r/m)\right].
\tag{7}
\]
Neither the bracket nor its sum with the smooth integral has acquired a sign. In particular, (7) is not permission to discard the boundary contribution or estimate it independently of its cancellation with the smooth part.

For clarity, the complete smooth factor in (6) is still
\[
\begin{aligned}
\mathcal L_L\mathscr H_{\alpha,r}(t)
=\frac{m^{1/4}}{\sqrt L}\sum_{n=-m}^{m}u_n^{(\alpha)}
\left(\sum_{v=1}^{r}v^{-\overline{s_n}}\right)(\overline{s_n}-1)
\left[\overline{s_n}t^{\overline{s_n}-1}
-(\overline{s_n}-2)t^{\overline{s_n}-3}\right].
\end{aligned}
\]
These are specializations of the accepted lower-moment formulas, not a new Green derivation. The endpoint r=1 remains. The zero Legendre flux at t=1 does not remove either physical endpoint in (1). fileciteturn38file0L2-L2

## 3. The first unpaid source inequality, with every index retained

**[COFINAL_FAMILY | PAPER]** Use the predecessor's exact kernel
\[
\mathcal I_{kn}=\frac{m^{1/4}}{\sqrt L}
\sum_{r=1}^{m}r^{-\overline{s_n}}
\int_{r/m}^{1}\mathsf P_{2k}(t)t^{\overline{s_n}-1}\,dt.
\tag{8}
\]
Define the following two fully source-bound rows:
\[
\begin{aligned}
J_{1,k}
&=\sum_{n,n',a,b=-m}^{m}\sum_{k'=1}^{N}
\mathcal I_{kn}\Pi_{na}K_{j,ab}\Pi_{bn'}F_{n'k'}c_{k'},\\
J_{0,k}
&=\sum_{n,n'=-m}^{m}\sum_{k'=1}^{N}
\mathcal I_{kn}(K_{j,nn'}-\theta\delta_{nn'})F_{n'k'}c_{k'}
+J_{1,k}.
\end{aligned}
\tag{9}
\]
Here \(c_{k'}\) denotes the already fixed selected coefficient row in \(x=Fc\), not a newly selected axis. In particular, all of x and its mixed source contributions remain inside each axis. Equations (8)–(9) are exactly the predecessor's source formulas (9)–(12), specialized to the requested axes. fileciteturn37file0L2-L2

The exact unpaid scalar for axis \(\alpha\) is
\[
\boxed{
\mathfrak F_\alpha(m)=
\vartheta_m M\sum_{k=1}^{N}(4k+1)\overline{J_{\alpha,k}}J_{\alpha,k}
-\left[\operatorname{Re}\sum_{k=1}^{N}(-1)^kp_kJ_{\alpha,k}\right]^2.
}
\tag{10}
\]
The conjugation has not been replaced by a transpose. The phase cancels in the first term but not in the second.

**The first unresolved comparison is (10) with \(\alpha=1\).** On cells where \(G_{11}>0\), the requested gap requires a source-derived
\[
\mathfrak F_1(m)\ge\eta_1(m)M G_{11},\qquad \eta_1(m)>0,
\]
on an entire selected tail. The requested obstruction instead requires
\(\mathfrak F_1(m)\le0\), with \(G_{11}>0\), on a proved unbounded selected-index set. Neither inequality with those quantifiers has been derived.

All ranges in (8)–(10) are literal:
\[
\begin{gathered}
m=J_P+j+2,\quad N=6m-1,\quad1\le k,k'\le N,\\
-m\le n,n',a,b\le m,\quad1\le r\le m.
\end{gathered}
\]
The two factors in \(\overline{J}J\) retain independent copies of all summation and integration indices. No fixed-frequency limit or monomial absolute-value replacement is used.

### Axis 0 was not silently skipped

**[FINITE_CELL | PAPER]** Since the first axis did not settle whole-cone viability, the second source row in (9) was also examined. Its frequency-weighted lower moment retains
\[
\boxed{
\Sigma_1^{(0)}=-\tfrac12\Sigma_0^{(0)}
+i\sum_{n=-m}^{m}\omega_n[(K_j-\theta I)x]_n.
}
\tag{11}
\]
Only the plane term cancels from the last sum. No source identity making that remaining term zero is established here. Thus the simplification (4) cannot be promoted to axis 0 or the full forcing.

For the actual mixture, the moments remain the corresponding combinations with the fixed coefficients \(Y^2\) and \(X^2-Y^2\). Likewise the full mixed Gram entry remains untouched. Neither (10) for axis 0 nor its additional moment (11) yields an eventual gap or an unbounded obstruction in this review.

**[FINITE_CELL | PAPER]** If either \(G_{\alpha\alpha}=0\), every \(J_{\alpha,k}=0\), so \(c_\alpha=0\) and that axis is vacuous. No quotient is assigned to such a cell. I have not asserted nonvanishing of an axis from an upper bound on its norm.

### Why the existing bounds do not decide (10)

**[COFINAL_FAMILY | PAPER]** The recurrence results fix M, \(\beta\), V and \(\vartheta_m\); they do not compare the two source terms in (10). The Ferrers budget B(m) concerns the designated omitted source tail, not this retained-prefix angle. The global radical identity for G and G'' does not assert \(K_j\Pi=0\): the source explicitly distinguishes global radical lifts from their finite projections. fileciteturn34file0L2-L2

Small \(\Pi K_j\Pi\) or small \(u^{(1)}\) alone cannot determine the answer. Under a nonzero real rescaling of a nonzero axis, its squared moment and its Gram norm scale by the same factor, so q is unchanged. This is an information-loss check, not an arbitrary-forcing counterexample against the selected source. Positivity of the Gram norm supplies only the denominator's sign, not the sign of (10).

## 4. A distinct source mechanism: the CCM displacement and the derivative column

This section gives an exact source calculation that can be used to determine the **direction** left unpaid in (3). It does not assume positivity of K or rerun the cone algebra.

### 4.1. The off-diagonal generator comes from the complete source

**[FINITE_CELL | PAPER]** Let \(D_F=\operatorname{diag}(n)_{n=-m}^{m}\), \(\mathbf 1_n=1\), and introduce a new vector
\[
\mathfrak b_n=nK_{j,n0},\qquad \mathfrak b_0=0.
\]
This is the **CCM displacement vector**. It is not the recurrence moment \(\beta=S_N-1\), the plane column \(\mathbf b\), or a constant-beta wrapper.

The inspected entry constructor gives, for every integer n in the carrier,
\[
\boxed{
\begin{aligned}
\mathfrak b_n={}&
32L\sinh^2(L/4)\frac{n}{L^2+16\pi^2n^2}\\
&+\frac1\pi\int_0^L
\frac{e^{t/2}\sin(\omega_nt)}{e^t-e^{-t}}\,dt\\
&+\frac1\pi\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\sin(\omega_n\log\nu).
\end{aligned}
}
\tag{12}
\]
Every prime power in the finite source sum is retained. The plus signs on the last two lines follow from the minus signs in **W02–WR–Prime** and the off-diagonal sine convention. The source formulas and its separate diagonal branch were inspected at the requested pin. fileciteturn36file0L2-L2

Direct subtraction now gives
\[
\boxed{
K_{j,nn'}=\frac{\mathfrak b_n-\mathfrak b_{n'}}{n-n'}
\quad(n\ne n'),\qquad
[D_F,K_j]=\mathfrak b\mathbf1^T-\mathbf1\mathfrak b^T.
}
\tag{13}
\]
For the pole term this follows from
\[
\frac{n}{L^2+16\pi^2n^2}-\frac{n'}{L^2+16\pi^2n'^2}
=\frac{(n-n')(L^2-16\pi^2nn')}
{(L^2+16\pi^2n^2)(L^2+16\pi^2n'^2)}.
\]
For the other two terms it is the literal difference of the two sine functions. At n'=0, (13) returns \(nK_{j,n0}=\mathfrak b_n\), checking its orientation.

**The diagonal is not obtained by filling in a divided-difference limit.** Its exact value is
\[
\begin{aligned}
\mathfrak d_n:=K_{j,nn}={}&
32L\sinh^2(L/4)\frac{L^2-16\pi^2n^2}{(L^2+16\pi^2n^2)^2}\\
&-\gamma-\log\!\left(4\pi\frac{m-1}{m+1}\right)\\
&-\int_0^L
\frac{2e^{t/2}(1-t/L)\cos(\omega_nt)-2}{e^t-e^{-t}}\,dt\\
&-2\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
\left(1-\frac{\log\nu}{L}\right)\cos(\omega_n\log\nu).
\end{aligned}
\tag{14}
\]
Here \(\gamma\) is the Euler–Mascheroni constant. The source's removable-endpoint convention is retained in the integral. Thus (12) and (14) encode the full matrix, not just its off-diagonal part. fileciteturn36file0L2-L2

### 4.2. Apply that identity to the actual derivative column

**[FINITE_CELL | PAPER]** The vector \(\mathfrak b\) is odd. Put
\[
\chi=D_F\mathfrak b,\qquad \gamma_L=(2\pi/L)^2,
\qquad v^{\rm act}=K_j\mathbf b,\qquad w=K_j\mathbf1.
\]
The superscript on \(v^{\rm act}\) distinguishes this Fourier-space action from the recurrence row \(v_k=P_k(E_4,m)\). Its source components are explicitly
\[
\begin{aligned}
v_n^{\rm act}&=\mathfrak d_n\mathbf b_n+
\sum_{n'\ne n}\frac{\mathfrak b_n-\mathfrak b_{n'}}{n-n'}\mathbf b_{n'},\\
w_n&=\mathfrak d_n+
\sum_{n'\ne n}\frac{\mathfrak b_n-\mathfrak b_{n'}}{n-n'}.
\end{aligned}
\tag{15}
\]
All sums in (15) run over the entire source carrier.

For any even vector h on that carrier, expanding
\([D_F^2,K_j]=D_F[D_F,K_j]+[D_F,K_j]D_F\) gives
\[
[D_F^2,K_j]h
=\chi(\mathbf1^Th)-\mathbf1(\chi^Th).
\]
The other two terms vanish by odd-even pairing, not by a source sign assumption. Applying this to \(\mathbf b\) and then using (1) yields
\[
\boxed{
K_j\mathbf e
=-\gamma_LD_F^2v^{\rm act}
+\gamma_L\chi(\mathbf1^T\mathbf b)
-\gamma_L\mathbf1(\chi^T\mathbf b)
+\epsilon_m w.
}
\tag{16}
\]
The last term is mandatory. It comes from **both physical edges** in Q5 and carries the same edge data as Q6.

Consequently the actual plane compression can be reconstructed as
\[
\boxed{
A_{GG}=\mathbf b^Tv^{\rm act},\qquad
A_{G''G}=\mathbf e^Tv^{\rm act},\qquad
A_{G''G''}=\mathbf e^T\bigl[\text{right-hand side of (16)}\bigr],
}
\tag{17}
\]
with the other entry supplied by symmetry. This reduces the derivative-column action to the two explicit actions (15) and low-rank source terms. It does **not** assign a sign to these contractions.

For axis 0, the same displacement identity also makes the extra moment in (11) concrete:
\[
\sum_n\omega_n[(K_j-\theta I)x]_n
=\frac{2\pi}{L}
\left[w^TD_Fx-(2m+1)\mathfrak b^Tx-\theta\mathbf1^TD_Fx\right].
\tag{18}
\]
The plane component contributes zero to this frequency-weighted sum. None of the remaining full-source terms in (18) is dropped.

## 5. One next PAPER test, and its exact success boundary

### TEST_SOURCE_PLANE_PROJECTIVE_DIRECTION_BY_DISPLACEMENT

**[FINITE_CELL | PAPER]** Separate the geometry of the transformed source plane from the actual direction selected by K and x. Define, with plane-column labels \(a\in\{G,G''\}\),
\[
Z_{ka}=(-1)^k\sum_{n=-m}^{m}\mathcal I_{kn}B_{na},
\qquad
\ell_a=\operatorname{Re}\sum_{k=1}^{N}p_kZ_{ka},
\]
\[
S_{ab}=\operatorname{Re}\sum_{k=1}^{N}
\frac{\overline{Z_{ka}}Z_{kb}}{\mu_k},
\qquad P_m=\vartheta_m M S-\ell\ell^T.
\tag{19}
\]
These are plane-column quantities, **not** the preceding two-channel cone matrix. Their kernels retain all the incomplete integrals in (8).

For the actual real source r in (3),
\[
G_{11}=r^TSr,\qquad c_1=\ell^Tr,\qquad
\mathfrak F_1=r^TP_mr.
\tag{20}
\]
This identifies the remaining orientation problem. Merely forming P_m is not the proposed test.

**The distinct mechanism is to determine the source direction r through (12)–(17), including (14) and the edge term, before taking any norm bound.** One can avoid a small amplitude denominator altogether by using the homogeneous vector
\[
\widehat r=\operatorname{adj}(R)\,A\,\operatorname{adj}(R)y
=(\det R)^2r.
\tag{21}
\]
Its direction is the actual one; no other plane direction is selected in its place.

The bounded PAPER task is to obtain **source-derived directional bounds for the two components of (21)** from the divided-difference sums (15) and their diagonal contributions, then compare that directional sector with the quadratic form in (19). In a chart with a proved nonzero \(\widehat r_G\), this means enclosing the actual ratio \(\widehat r_{G''}/\widehat r_G\) and checking the explicit quadratic
\[
(P_m)_{GG}+2t(P_m)_{GG''}+t^2(P_m)_{G''G''}
\]
on that enclosure. Its endpoints and any interior vertex must all be covered. If that chart vanishes, use the other chart or homogeneous coordinates; do not divide by it. The zero transformed-axis case remains separate.

This tests **the source compression's direction**, not the full signed Abel margin, and it does not enlarge the actual direction to the whole plane or to the entire comparison cone. The kernel data S and \(\ell\) depend on F, the exact plane and p; the source direction additionally depends on K and the full x. This separation makes it possible to preserve cancellations in the signed source matrix actions instead of destroying them with \(\|K\|\) bounds.

**[COFINAL_FAMILY | CONDITIONAL]** For example, an independently proved directional certificate with
\[
r^TP_mr\ge h(m)\|r\|_2^2,\qquad
r^TSr\le s(m)\|r\|_2^2,
\qquad h(m)>0,\ s(m)>0,
\]
would give the paid axis gap \(\eta_1(m)=h(m)/(M s(m))\) on its certified tail. An upper certificate \(r^TP_mr\le0\), together with \(r^TSr>0\), on a proved unbounded selected-index set would give the requested axis obstruction. These are **validation contracts, not bounds supplied by this review**. No h, s, eta, or delta is defined by an unknown minimum.

The main failure risk is now specific: the diagonal contribution and the off-diagonal divided differences in (15) may cancel at the same scale that determines the direction. The commutator alone cannot resolve that cancellation. A failed directional estimate remains open; it is not a whole-cone kill.

### Two representations, only the preceding test commissioned

| Representation | Discriminating power | PAPER cost and risk |
|---|---|---|
| **Chosen: actual source-plane direction from displacement, (12)–(21).** | Can establish either an actual plane-axis gap or an actual unbounded plane-axis obstruction without paying the mixed cone condition. | Two explicit matrix actions, three plane contractions, and the transformed-plane geometry. Uniform signed estimates are still required; the diagonal is load-bearing. |
| **Alternative: the physical incomplete-Mellin projection kernel, with the exact even plane functions.** | Can bound the plane-axis numerator and norm jointly in physical coordinates, preserving their cancellation and (4). | Coupled integrals on the m−1 intervals, with both edge moments and the finite Legendre kernel. Avoids divided differences but may be less economical. No second campaign is authorized. |

## 6. Strongest attack, calibration, and closeout

**[ABSTRACT | PAPER]** The strongest objection is that (13) is blind to the diagonal. It is correct. Replacing a test matrix K by K+tI leaves its displacement commutator unchanged but changes the plane axis by \(t\Pi x\). Therefore a sign conclusion based on the commutator alone would be invalid. This is an abstract detector calibration, not an admissible modification or a counterexample for the selected family. Equations (14)–(17) explicitly retain the missing information.

**[FINITE_CELL | PAPER]** A second check is the central coefficient in (1): \(\mathbf e_0=\epsilon_m\), not zero. Dropping the edge term would already change the actual source derivative column there. The inherited source identifies this term explicitly. fileciteturn34file0L2-L2

The announced source-plane investigation produced (3)–(7), but did not fix the angular side of the actual axis. The pre-check displacement expectation—reduce the derivative-column action while keeping the diagonal explicit—is confirmed by (12)–(17). No prediction of a family gap or an unbounded obstruction was registered; neither is retrospectively scored as achieved.

**What changed:** the plane-axis lower moments have an exact source relation, and its K-dependence has an explicit displacement/derivative-column representation. **What did not change:** the sign of the actual quantity (10), first for axis 1 and then for axis 0. There is no requested axis-sign quantifier closed, and no selected-source cone theorem refuted. This is **representation progress**, not a successful axis certificate.

The three structural checks are distinct: the bridge is the full CCM displacement identity combined with Q5; the tested vanishing mechanism is plane parity, which kills only the frequency-weighted lower moment, not c_1; the family-deciding object is the actual direction (21) located relative to (19). Gram positivity and global radical membership do not substitute for that object.

```yaml
DOWNSTREAM_CONSUMER: whole_source_cone_angular_obstruction_for_the_ground_centered_moment_certificate
ACTUAL_CONSUMER_REQUIREMENT: both_axis_conditions_and_the_mixed_condition_with_a_paid_positive_delta_on_a_selected_tail
ORIGINAL_REQUESTED_OBJECT: strict_selected_axis_gaps_required_by_the_proposed_whole_cone_certificate
ORIGINAL_OBJECT_IS: PROVED_NECESSARY
ORIGINAL_OBJECT_QUALIFICATION: axis_gaps_are_necessary_only_for_the_proposed_strict_whole_cone_certificate_not_for_D_or_the_full_Abel_sign
KNOWN_WEAKER_INTERFACES:
  - an_upper_alignment_bound_only_at_the_actual_fixed_mixture_can_exclude_D_without_whole_cone_control
  - a_direct_full_source_quartic_margin_can_supply_first_tau_sign_without_the_moment_certificate
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_ESTIMATE: source_directional_control_of_the_actual_plane_compression_sufficient_to_sign_equation_10_for_axis_1
FIRST_UNPAID_SOURCE_INEQUALITY: equation_10_alpha_1_with_equations_8_and_9_and_the_requested_family_quantifiers
DISCRIMINATOR: TEST_SOURCE_PLANE_PROJECTIVE_DIRECTION_BY_DISPLACEMENT
REOPEN_TRIGGER: source_direction_enclosure_from_12_to_21_that_yields_a_paid_eventual_axis_gap_or_an_unbounded_axis_obstruction
KILLED_REQUESTED_THEOREM_SHAPE: NONE
WHOLE_CONE_CERTIFICATE_DEAD: false
ACTUAL_D_KILLED: false
NOVELTY_AXIS: source_plane_parity_plus_full_CCM_displacement_with_diagonal_and_Q6_derivative_edge_retained
MEMORY_ENTRY:
  target: selected_source_cone_axis_ground_angle
  status: OPEN
  invariant_learned: plane_axis_has_one_independent_lower_moment_but_its_angle_depends_on_the_actual_compressed_source_direction
  forbidden_future_move: infer_an_axis_angle_from_small_plane_norm_or_from_a_diagonal_blind_commutator
  next_decisive_test: TEST_SOURCE_PLANE_PROJECTIVE_DIRECTION_BY_DISPLACEMENT
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_PLANE_PROJECTIVE_DIRECTION_BY_DISPLACEMENT`, on paper, for the unchanged selected plane axis.** Use the full source generator (12), the separate diagonal (14), the exact actions (15)–(17), and the actual homogeneous direction (21). Seek a source-uniform directional enclosure, not another cone identity or a bare norm bound. Validate it against the exact transformed-plane geometry (19), treating zero axes and vanishing coordinate charts separately. Report an axis gap only with a paid positive lower function on the selected tail, or an obstruction only with a proved unbounded selected-index set and nonzero transformed axis. An axis obstruction refutes only the strict whole-cone witness. Preserve all terms in (6), (8), (9), (12), (14), and (16), including both physical edges, MIX, Q6, complex conjugation and every finite-source prime power. No Lean, mathematical runtime, numerical diagnostics, repository write, source replacement, constant-beta wrapper, route promotion, first-tau-sign claim, or RH claim is authorized.
