# STATUS: TRY_GOAL058_SOURCE_BULK_PLANE_CONE_DISCRIMINANT

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_BULK_PLANE_CONE_DISCRIMINANT
OUTCOME: OPEN_SOURCE_DISCRIMINANT
REQUEST_ID: REQ-2026-09-26-GROUND-CENTERED-ABEL-DISCRIMINANT
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_GROUND_CENTERED_ABEL_DISCRIMINANT
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 760b641e6de390417c35298a7248eee74142a583
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-ABEL-CUMULATIVE-FORCING
PREDECESSOR_VERDICT_SHA256_REPORTED: 116170b67660e98fbf72c1f391f5d46dcbe530df0572137bb309ed810313700c
PREDECESSOR_VERDICT_SHA256_INDEPENDENTLY_RECOMPUTED: false
PREDECESSOR_GIT_BLOB_READ: 4ef982fc4ab59f6457b53e330f7e8e80e87fc7d6
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
NORMALIZATION_D: VERIFIED_WITH_UNSQUARED_SIGN
DEGENERATE_KAPPA_OR_H_CASES: CANNOT_SUPPLY_STRICT_MARGIN
SOURCE_DELTA_V_STRICT_POSITIVITY: PROVED_FROM_DISTINCT_RECURRENCE_ENERGIES
SOURCE_SIGNED_C_BOUND: NOT_ESTABLISHED
SOURCE_CENTERED_VARIANCE_BOUND_SUFFICIENT_FOR_D: NOT_ESTABLISHED
SOURCE_DISCRIMINANT_PASS: NOT_ESTABLISHED
SOURCE_DISCRIMINANT_KILL: NOT_ESTABLISHED
SOURCE_CONE_OBSTRUCTION: CONDITIONAL_CERTIFICATE_NOT_VERIFIED_ON_FAMILY
SIGN_OF_TAU: OPEN
SCHUR_FLOOR: OPEN
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CLOSED_SELECTED_SIGN_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: DUALIZE
DISCRIMINATOR: TEST_SOURCE_BULK_PLANE_CONE_ANGLE_OBSTRUCTION
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_ARTIFACT_IO_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SOURCE_DISCRIMINANT.** The normalization **(D)** is correct, including its unsquared sign condition and its degenerate cases. **No source-derived one-sided bound for the actual ground moment, together with a sufficient bound for its centered variance, has been obtained.** Consequently neither requested family verdict follows.

The new reduction is source-specific: the once-fixed forcing belongs to a **two-direction cone**, with nonnegative coefficients forced by the actual orthogonal projection. Its ground moment and centered variance are exactly a linear form and a two-by-two Gram form. This exposes a different possible discriminator: **a uniform upper bound on alignment for that source-generated cone would exclude both orientations of (D), without first determining the sign of C and even before spending B(m).** The cone bound itself remains unproved; it is not a selected-source kill.

## 1. Source lock and inherited boundary

**[COFINAL_FAMILY | PAPER]** The predecessor was read completely at the requested commit. GitHub returns blob `4ef982fc4ab59f6457b53e330f7e8e80e87fc7d6`. The commit's audit records the supplied SHA-256 and accepts only the predecessor's identities and enclosure—not condition (24). That SHA-256 is reported here as committed audit evidence, not as a fresh local byte-hash calculation. The bootstrap was fetched from `rh_clean` and read through its response-format section. fileciteturn21file0L2-L5 fileciteturn22file0L2-L5 fileciteturn23file0L2-L5 fileciteturn24file0L3-L7 fileciteturn19file0L2-L5

Fix the same P and retain
\[
m=J_P+j+2,\qquad N=6m-1,\qquad -m\le n\le m,
\]
the original splice at 5m, the exact source x, F, K_j, Π, κ_m and B(m), and the exact moments
\[
M=\sum_{k=1}^N\mu_kp_k^2,\quad
\beta=S_N-1,\quad
V=\sum_{k=1}^N\mu_kv_k^2,
\quad a=1-\beta/M,\quad d=(V-\beta^2/M)/M.
\]
The earlier TXT fixes this same carrier and once-global forcing. No Abel identity, Wronskian identity, weight partition, or abstract Cauchy enclosure is rederived below. fileciteturn17file0L27-L36

The auxiliary μ-weighted coefficient geometry does **not** replace the Euclidean CCM norms X and Y. Below, two channel labels 0 and 1 label forcing components; they are not spectral-mode labels and are not Abel prefix indices.

## 2. Direct verification of (D)

### 2.1. Division by the positive normalization

**[ABSTRACT | PAPER]** For κ_m≠0 and H>0, put
\[
Z=|\kappa_m|\sqrt{MH}>0.
\]
Using the predecessor's accepted center and radius, not deriving their enclosure again,
\[
\frac{\varepsilon a\kappa_m C-Y^2B(m)}{Z}
=a c_\varepsilon-b,
\qquad
\frac{|\kappa_m|\sqrt{\Delta_v(H-C^2/M)}}{Z}
=\sqrt{d(1-c_\varepsilon^2)}.
\tag{1}
\]
The radius is nonnegative. Thus the predecessor's **positive-side requirement together with its squared comparison** is equivalent to
\[
\boxed{a c_\varepsilon-b>\sqrt{d(1-c_\varepsilon^2)}.}
\tag{D}
\]
This uses \(|c_\varepsilon|\le1\) and retains the positive-side requirement. In particular, D demands c_ε>0 and b<a. The predecessor explicitly required both inequalities in (24). fileciteturn23file0L2-L2

A paper negative control catches the forbidden squaring shortcut: at c_ε=−1 and b=0, the squared left side is a²>0 and the squared radius is zero, but the unsquared left side is −a<0. This is a calibration of the logical test, **not a selected-source example**.

If κ_m=0, the defining quartic is zero. If H=0, positivity of every μ_k gives h_k♯=0 for every k, hence C=𝓠=0. Neither case supplies either strict margin when B(m)≥0. Also Y=0 implies Πx=0 and therefore g♯=0; this case is already covered by H=0.

### 2.2. The source does not have a hidden d=0 exception

**[COFINAL_FAMILY | PAPER]** In fact Δ_v>0 on the stated selected domain. If Δ_v=0, then v_k=t p_k for all 1≤k≤N. Since N≥3, subtracting t times the ground recurrence from the fourth-mode recurrence at k=2 gives
\[
\Delta E\,t p_2=0.
\]
Here ΔE>0 and p_2>0, so t=0. Then v_1=v_2=0; the recurrence at k=1 gives ℓ_1v_0=0, contradicting v_0=1 and ℓ_1≠0. The inspected source crosswalk supplies these nonzero off-diagonal coefficients and the energy convention E=Λ+G. No numerical gap enters. fileciteturn28file0L2-L2

Accordingly d>0. For 0≤b<a, the scalar condition can also be located exactly:
\[
D\iff c_\varepsilon>c_*(a,b,d),\qquad
c_*=
\frac{ab+\sqrt{d(a^2+d-b^2)}}{a^2+d}.
\tag{2}
\]
To select the correct root without losing the sign: on 0≤c≤1, the function ac−b−√{d(1−c²)} is strictly increasing, is negative at c=b/a, and is positive at c=1. Formula (2) is its unique root in that interval. If b≥a, no c in [−1,1] works.

A useful **necessary, sign-independent filter** follows:
\[
\boxed{
D\ \Longrightarrow\ \frac{C^2}{MH}>\vartheta_m,
\qquad
\vartheta_m:=\frac{d}{a^2+d}
=\frac{MV-\beta^2}{M(M+V-2\beta)}\in(0,1).
}
\tag{3}
\]
This is not a source alignment estimate. It identifies the alignment that an independently constructed source obstruction would have to exclude. All appearances of β in (2)–(3) remain **β=S_N−1**, not −1 or zero.

## 3. Exact reduction of the actual forcing to two source channels

### 3.1. Use the projection constraint, not arbitrary forcing

**[FINITE_CELL | PAPER]** Freeze the actual x, K_j, Π and θ from the selected cell. Define
\[
\begin{aligned}
u^{(0)}&=(K_j-\theta I)x+\Pi K_j\Pi x,\\
u^{(1)}&=\Pi K_j\Pi x,\\
\lambda_0&=Y^2,\qquad \lambda_1=X^2-Y^2.
\end{aligned}
\tag{4}
\]
Since Π is the same Euclidean orthogonal projection,
\[
\lambda_0\ge0,\qquad\lambda_1\ge0,
\qquad
\boxed{g^\sharp=\lambda_0u^{(0)}+\lambda_1u^{(1)}.}
\tag{5}
\]
This uses the actual constraint Y≤X. Using the larger, unrestricted cone generated by (K_j−θI)x and ΠK_jΠx would unnecessarily discard that constraint.

Nothing in (4) recomputes x or g♯ on a weight block. Both u^(α) use the **whole same x**. When considering a comparison cone later, these two directions stay frozen: x, X, Y, Π and θ are not recomputed as the comparison coefficients vary.

Define the two pulled-back source channels
\[
z_{\alpha k}=(-1)^k(F^*u^{(\alpha)})_k,
\quad \alpha\in\{0,1\},\quad1\le k\le N.
\]
These channel symbols are unrelated to the original cell vector z_j. Set
\[
\mathfrak c_\alpha=\operatorname{Re}\sum_{k=1}^Np_kz_{\alpha k},
\qquad
\mathsf G_{\alpha\beta}
=\operatorname{Re}\sum_{k=1}^N\frac{\overline{z_{\alpha k}}z_{\beta k}}{\mu_k}.
\tag{6}
\]
The real part retains the complex source convention; it does not replace F* by Fᵀ. The actual C is real by the inherited source reflection relation. Direct finite expansion now gives
\[
\boxed{
C=\lambda^T\mathfrak c,
\qquad H=\lambda^T\mathsf G\lambda,
\qquad
H-C^2/M=\lambda^T\mathsf R\lambda,
\quad
\mathsf R:=\mathsf G-\mathfrak c\mathfrak c^T/M.
}
\tag{7}
\]
For example,
\[
H-C^2/M=
\lambda_0^2\mathsf R_{00}
+2\lambda_0\lambda_1\mathsf R_{01}
+\lambda_1^2\mathsf R_{11}.
\tag{8}
\]
The mixed entry has not been dropped or assigned a sign. The predecessor's MIX also remains inside the whole x used in both channels.

This is a **source-dependent Gram representation**, not a source estimate. In particular, nonnegativity of a Gram form cannot determine the sign of the separate linear form λᵀ𝔠.

### 3.2. Fully indexed formulas for these entries

**[FINITE_CELL | PAPER]** Let L=log m and s_n=1/2−2πin/L. Write
\[
\mathcal I_{kn}:=
\frac{m^{1/4}}{\sqrt L}
\sum_{r=1}^m r^{-\overline{s_n}}
\int_{r/m}^{1}\mathsf P_{2k}(t)t^{\overline{s_n}-1}\,dt,
\tag{9}
\]
so that, in the predecessor's source convention,
\[
z_{\alpha k}=(-1)^k\sum_{n=-m}^{m}\mathcal I_{kn}u_n^{(\alpha)}.
\]
Here
\[
\begin{aligned}
\mathsf L^{(1)}_{nn'}&=
\sum_{a,b=-m}^{m}\Pi_{na}K_{j,ab}\Pi_{bn'},\\
\mathsf L^{(0)}_{nn'}&=
K_{j,nn'}-\theta\delta_{nn'}+\mathsf L^{(1)}_{nn'},\\
u_n^{(\alpha)}&=
\sum_{n'=-m}^{m}\sum_{k'=1}^{N}
\mathsf L^{(\alpha)}_{nn'}F_{n'k'}c_{k'}.
\end{aligned}
\tag{10}
\]
Thus the signed channel moments are explicitly
\[
\boxed{
\mathfrak c_\alpha=
\operatorname{Re}
\sum_{k=1}^{N}\sum_{n,n'=-m}^{m}\sum_{k'=1}^{N}
(-1)^kp_k\mathcal I_{kn}
\mathsf L^{(\alpha)}_{nn'}F_{n'k'}c_{k'}.
}
\tag{11}
\]
Their compatible Gram entries are
\[
\boxed{
\mathsf G_{\alpha\beta}=
\operatorname{Re}\sum_{k=1}^{N}(4k+1)
\sum_{n,n'=-m}^{m}
\overline{u_n^{(\alpha)}}u_{n'}^{(\beta)}
\overline{\mathcal I_{kn}}\mathcal I_{kn'}.
}
\tag{12}
\]
The two factors 𝓘 in (12) each retain their own complete r-sum and incomplete integral. The phase (−1)^k cancels in (12) but **does not cancel in (11)**. These formulas are obtained from the pinned predecessor's incomplete-Mellin formula with no asymptotic substitution. fileciteturn22file0L2-L2

The scope is exactly
\[
m=J_P+j+2,\quad N=6m-1,\quad
1\le k,k'\le N,\quad -m\le n,n',a,b\le m,
\quad1\le r\le m.
\]
There is no fixed-Fourier-index restriction and no truncation inside these ranges.

## 4. First unpaid source inequality and the preserved boundary terms

### 4.1. The signed source inequality is unpaid already before its magnitude

**[COFINAL_FAMILY | PAPER]** For either allowed orientation, even the preliminary necessary inequality
\[
\boxed{
\varepsilon\operatorname{sgn}(\kappa_m)
\left[Y^2\mathfrak c_0+(X^2-Y^2)\mathfrak c_1\right]>0
}
\tag{13}
\]
has not been established with the requested family quantifiers. Its entries are the full indexed source sums (9)–(11), not arbitrary forcing variables. A pass would additionally need quantitative domination of the compatible source variance (7)–(12) and B(m). No such bounds A(m)>R(m) are supplied here.

The exact lower-edge content of (13) is worth making explicit. With the **once-fixed full g♯**, put
\[
\Sigma_0^\sharp=\sum_{n=-m}^{m}g_n^\sharp,
\qquad
\Sigma_1^\sharp=\sum_{n=-m}^{m}(\overline{s_n}-1)g_n^\sharp,
\]
\[
A_p(t)=\sum_{k=1}^{N}
\frac{(-1)^kp_k}{2k(2k+1)}\mathsf P_{2k}(t),
\]
and on r/m<t<(r+1)/m,
\[
\mathscr H_r^\sharp(t)=
\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n^\sharp t^{\overline{s_n}-1}
\sum_{b=1}^{r}b^{-\overline{s_n}}.
\]
The predecessor's accepted identity specializes to
\[
\boxed{
C=\mathcal V_p^\sharp+
\frac{m^{7/4}}{\sqrt L}
\sum_{r=1}^{m-1}\frac{1-r^2/m^2}{r^2}
\left[
\Sigma_0^\sharp\frac r m A_p'(r/m)
-\Sigma_1^\sharp A_p(r/m)
\right],
}
\tag{14}
\]
where
\[
\mathcal V_p^\sharp=
\sum_{r=1}^{m-1}
\int_{r/m}^{(r+1)/m}A_p(t)\mathcal L_L\mathscr H_r^\sharp(t)\,dt,
\quad \mathcal L_L=-\partial_t((1-t^2)\partial_t),
\]
and the complete smooth integrand is
\[
\mathcal L_L\mathscr H_r^\sharp(t)=
\frac{m^{1/4}}{\sqrt L}
\sum_{n=-m}^{m}g_n^\sharp
\left(\sum_{b=1}^{r}b^{-\overline{s_n}}\right)
(\overline{s_n}-1)
\left[
\overline{s_n}t^{\overline{s_n}-1}
-(\overline{s_n}-2)t^{\overline{s_n}-3}
\right].
\tag{15}
\]
Thus the first unpaid source inequality is precisely the signed positivity in (13), equivalently the signed positivity of the **joint bulk-plus-two-moment expression (14)**. There is no established positive reference term with a paid one-sided remainder for this expression. Both lower moments, including r=1, survive. No relation Σ₁♯=−Σ₀♯/2 is inserted. These are specializations of inherited formulas (14)–(20), not a new Green derivation. fileciteturn22file0L2-L2 fileciteturn23file0L2-L2

### 4.2. What has not been simplified away

**[FINITE_CELL | PAPER]** In (10), every K entry remains
\[
K_{j,nn'}=W02_{nn'}-WR_{nn'}
-\sum_{\nu=2}^{m}\frac{\Lambda(\nu)}{\sqrt\nu}
Q_{nn'}(\log\nu).
\tag{16}
\]
The inspected entry constructor keeps
\[
Q_{nn'}(t)=
\begin{cases}
2(L-t)L^{-1}\cos(2\pi nt/L),&n=n',\\[2pt]
\bigl[\sin(2\pi n't/L)-\sin(2\pi nt/L)\bigr]/[\pi(n-n')],&n\ne n',
\end{cases}
\]
and
\[
WR_{nn'}=
\frac{Q_{nn'}(0)}2
\left[\gamma+\log\!\left(4\pi\frac{m-1}{m+1}\right)\right]
+\int_0^L\frac{e^{t/2}Q_{nn'}(t)-Q_{nn'}(0)}{e^t-e^{-t}}\,dt.
\tag{17}
\]
W02 is the same literal closed entry, not deleted or bounded separately with an assumed sign. The general finite wrapper and complex source constructor preserve these entries on the full carrier. Every prime power represented by Λ(ν), 2≤ν≤m, remains. No global-radical rewriting, and hence no unaccounted global prime-tail cancellation, is used. fileciteturn25file0L2-L2 fileciteturn26file0L2-L2 fileciteturn27file0L2-L2

The source plane continues to use its Q6 vector, here written in bold to distinguish it from the scalar d=Δ_v/M:
\[
\mathbf d_n=
\left(1+\frac{\omega_n^2-15/4}{16\pi m}\right)b_n^G
-\frac{G'(L/2)}{8\pi m\sqrt L},
\qquad \omega_n=2\pi n/L.
\tag{18}
\]
Neither physical logarithmic-window boundary is discarded. The vanishing Legendre flux at t=1 in (14) is a different boundary statement and cannot erase Q6 or either physical edge. The predecessor explicitly retains those distinctions. fileciteturn23file0L2-L2

### 4.3. Why the supplied bounds do not pay this inequality

**[COFINAL_FAMILY | PAPER]** The accepted recurrence results constrain M, β, V, a and d. They do not determine the sign of the source sums (11) or the joint cancellation in (14). The positive Robin secant likewise does not give a sign for those full forcing pairings. B(m) pays the designated omitted Ferrers tail, not the retained-prefix bulk-plus-edge functional or its Gram entries.

The pinned audit accepts the predecessor only at that limited level and leaves the full source comparison open. This is a statement about the supplied estimates, not a claim that an exhaustive search of all mathematics has ruled out a supplier. fileciteturn23file0L2-L2 fileciteturn24file0L7-L7

Replacing (12) by a bare operator-norm bound would leave (13) unsigned. Separating the smooth part of (14) from its two coherent edge moments without paying their cancellation has the same defect. Neither maneuver establishes D or its negation.

## 5. One genuinely different PAPER discriminator

### TEST_SOURCE_BULK_PLANE_CONE_ANGLE_OBSTRUCTION

**[FINITE_CELL | CONDITIONAL]** Use the two actual source directions in (4), their exact five real moments—two entries of 𝔠 and three independent entries of 𝔊—and the exact threshold ϑ_m in (3). Seek an explicitly source-derived function
\[
0<\delta(m)<\vartheta_m
\]
for which the real symmetric matrix
\[
\boxed{
\mathsf A_m(\delta)=
(\vartheta_m-\delta(m))M\,\mathsf G
-\mathfrak c\mathfrak c^T
}
\tag{19}
\]
is **copositive**: its quadratic form is nonnegative on nonnegative two-component vectors. This is the usual meaning of copositivity; no algorithm or outside positivity theorem about the selected source is being imported. citeturn586120academia4

For a two-by-two matrix, the complete test is just
\[
\boxed{
\mathsf A_{00}\ge0,\qquad
\mathsf A_{11}\ge0,\qquad
\mathsf A_{01}+\sqrt{\mathsf A_{00}\mathsf A_{11}}\ge0.
}
\tag{20}
\]
The sufficient direction follows directly, for s,t≥0, from
\[
(s,t)\mathsf A(s,t)^T=
(\sqrt{\mathsf A_{00}}s-\sqrt{\mathsf A_{11}}t)^2
+2st\left(\mathsf A_{01}+\sqrt{\mathsf A_{00}\mathsf A_{11}}\right).
\]
The necessary direction follows by testing the axes and, when both diagonal entries are positive, the vector (√A₁₁,√A₀₀); a zero diagonal with a negative off-diagonal fails by taking the other coordinate arbitrarily small. Thus zero diagonal entries are covered. Requiring positive semidefiniteness on all real vectors would be unnecessarily stronger than (20).

Because the **actual** λ in (5) is nonnegative, a proof of (20) yields
\[
C^2\le(\vartheta_m-\delta(m))MH.
\tag{21}
\]
Consequently, for both ε=+1 and ε=−1,
\[
\begin{aligned}
a c_\varepsilon-b-\sqrt{d(1-c_\varepsilon^2)}
&\le a\sqrt{\vartheta_m-\delta(m)}-b
-\sqrt{d(1-\vartheta_m+\delta(m))}\\
&=-\gamma(m)-b<0,
\end{aligned}
\tag{22}
\]
where the explicit positive separation is
\[
\boxed{
\gamma(m)=
\sqrt{d(1-\vartheta_m+\delta(m))}
-a\sqrt{\vartheta_m-\delta(m)}>0.
}
\]
Its positivity is algebraic: the difference between the squares of the two nonnegative terms is (a²+d)δ(m)>0. This is the required **strict upper envelope**, not a failed sufficient lower bound mislabeled as a kill.

**[COFINAL_FAMILY | CONDITIONAL]** A source proof of (20) with such δ(m) for every selected j≥j₀ would therefore exclude D in both orientations on that whole tail. It would rule out a positive-orientation pass on any unbounded selected-index set and a negative-orientation pass on any entire selected tail. Degenerate cells are already excluded in §2. It would kill **only this moment certificate**, not the full Abel sign, Schur-floor, or the route.

### Why this is not condition (24) under a new name

This test seeks an **upper**, sign-independent restriction on attainable ground alignment in a source-generated cone. It omits the nonnegative budget deliberately: exclusion even at zero budget is stronger than needed. It uses the actual projection relation Y≤X and the actual full x in both source directions. Its sought witness is three inequalities for a two-by-two source matrix, not a lower bound for the original signed margin.

The comparison cone includes the actual forcing, but it may also include coefficient choices not realized by the selected construction. A **uniform upper bound over that cone** is a valid implication for the actual forcing. In contrast, finding one arbitrary cone vector for which D fails would prove nothing about the actual forcing. That invalid counterexample argument is not used here.

**Present status of this test: unproved on the selected family.** No δ(m) and no source proof of the three inequalities (20) have been obtained. In particular, δ must not be defined by an unproved minimum eigenvalue, an unknown alignment deficit, or the desired conclusion.

The main risk is precisely stated: one comparison-cone direction may be sufficiently ground-aligned even though the actual fixed mixture is not. Failure of (20), including an exact family failure, would then refute this stronger cone witness only. It would not prove D, refute D for the actual mixture, or justify SOURCE_DISCRIMINANT_KILL.

## 6. Alternatives, adversarial checks, and closeout

### Two representations; only one selected next test

| Representation | Decisive power | Analytic cost and risk |
|---|---|---|
| **Chosen: source two-channel cone, (19)–(20).** | One eventual copositivity certificate with a paid positive angular separation excludes both orientations for the actual forcing, and for the whole comparison cone. | Five source moments and three scalar comparisons, uniform in m. The source integral estimates are still real work; a small matrix is not automatically an easy proof. Enlarging from the actual coefficient pair to the cone can lose decisiveness. |
| **Alternative representation: the finite Legendre projection kernel for the actual forcing.** | Preserves only the actual forcing and all its cancellations; can support direct source analysis of the centered variance without a cone enlargement. | The signed bulk/edge moment is still needed, and the two-variable kernel retains all intervals and Fourier indices. More analytic bookkeeping; no new test is commissioned here. |

**[FINITE_CELL | PAPER]** For specificity, the alternative kernel is
\[
\mathscr K_N^\perp(t,u)=
\sum_{k=1}^N(4k+1)\mathsf P_{2k}(t)\mathsf P_{2k}(u)
-\frac{\Phi_p(t)\Phi_p(u)}M,
\quad
\Phi_p(t)=\sum_{k=1}^N(-1)^kp_k\mathsf P_{2k}(t).
\]
Extend the actual piecewise 𝓗♯ by zero on 0≤t<1/m. Finite expansion of its moments (9), with no exchange of infinite sums, gives
\[
H-C^2/M=
\int_0^1\!\int_0^1
\overline{\mathscr H^\sharp(t)}\,
\mathscr K_N^\perp(t,u)\,
\mathscr H^\sharp(u)\,dt\,du.
\]
This is a second representation of the same source variance, not an additional estimate or source positivity claim.

### Strongest attacks and calibration

**[ABSTRACT | PAPER]** The strongest objection to the cone proposal is that it is stronger than necessary. That objection is correct and limits its use: success transfers to the actual source; failure need not. The source forcing has not been replaced by a selectable vector, and the physical family is unchanged.

The two-by-two detector must also reject a planted cross-term failure. A matrix with diagonal entries 1 and off-diagonal −2 passes both diagonal checks but has quadratic value −2 at (1,1); the third check in (20) rejects it. This is an abstract calibration, not a selected-source counterexample. No Gram-matrix or Robin positivity is used as positivity of K_j.

The three structural approaches are separated: the **one-way transfer** is source-cone copositivity → actual alignment exclusion; an **exact vanishing identity** 𝔠=0 would also exclude D, but none has been found for the actual channels; the **family-collapsing witness** sought is (19)–(20) with explicit separation. None is silently promoted from a candidate to source evidence.

### Prediction record and actual progress

The pre-test normalization prediction is **confirmed** by (1), with the wrong-sign squared control rejected. The registered source-range investigation produced the exact two-channel representation (4)–(12), but **did not establish a source-range obstruction**. No source sign or family kill was predicted and then retrospectively claimed.

What became smaller is the comparison object for a possible obstruction: two actual source directions and five real moments, rather than unrestricted forcing coordinates. What did **not** become smaller is the unpaid selected-source sign/variance estimate itself. Therefore the progress class is **REPRESENTATION_PROGRESS**, not a claimed source-sign proof. No selected-source theorem shape has been killed.

```yaml
DOWNSTREAM_CONSUMER: first_tau_sign_gate_on_unchanged_selected_cellwise_complement
ACTUAL_CONSUMER_REQUIREMENT: full_source_quartic_margin_against_Y2_B_with_the_requested_family_quantifiers
ORIGINAL_REQUESTED_OBJECT: actual_ground_centered_moment_discriminant_D
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_certificate_not_proved_necessary_for_the_full_Abel_sign
KNOWN_WEAKER_INTERFACES:
  - direct_one_sided_full_quartic_bound_implies_first_tau_sign_via_the_inherited_tail_budget
  - source_signed_centered_correlation_bound_can_replace_the_Cauchy_radius_without_changing_the_quartic
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_IDENTITY: source_control_of_joint_bulk_plus_two_edge_moment_C_and_compatible_variance_7_to_15
FIRST_UNPAID_SOURCE_INEQUALITY: equation_13_equivalently_signed_joint_expression_14
DISCRIMINATOR: TEST_SOURCE_BULK_PLANE_CONE_ANGLE_OBSTRUCTION
DISCRIMINATOR_SCOPE: stronger_source_cone_obstruction_not_a_necessary_interface
REOPEN_TRIGGER: explicit_eventual_source_copositivity_bounds_20_with_positive_delta_or_an_actual_source_D_certificate
NOVELTY_AXIS: exact_two_channel_source_cone_using_Y_le_X_and_sign_free_alignment_exclusion
KILLED_REQUESTED_THEOREM_SHAPE: NONE
SOURCE_DISCRIMINANT_DEAD: false
MEMORY_ENTRY:
  target: selected_ground_centered_Abel_discriminant
  status: OPEN
  invariant_learned: actual_forcing_lies_in_the_frozen_bulk_plus_plane_projection_cone
  forbidden_future_move: use_an_arbitrary_failing_forcing_or_failed_cone_bound_as_an_actual_source_kill
  next_decisive_test: TEST_SOURCE_BULK_PLANE_CONE_ANGLE_OBSTRUCTION
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_BULK_PLANE_CONE_ANGLE_OBSTRUCTION`, on paper, at this source boundary.** Construct the two frozen source channels (4), the five exact moments (6), and matrix (19), keeping (9)–(18) intact. Attempt a source-derived eventual certificate for all three copositivity inequalities (20) with an explicitly justified δ(m)>0; do not obtain δ by defining it to be the desired unknown deficit. The validation gate is the strict upper envelope (22), for both ε, on the same selected tail. A genuine source proof of that gate permits only a moment-certificate kill. Failure of the cone witness must remain separate from the fate of the actual fixed mixture and of D. No new Abel derivation, common-prefix-sign condition, Gaussian substitution, omitted mixed term, numerical escalation, Lean work, repository write, route promotion, or RH claim is authorized.
