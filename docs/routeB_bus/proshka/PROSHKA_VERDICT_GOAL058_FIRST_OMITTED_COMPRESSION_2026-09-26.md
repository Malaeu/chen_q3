# STATUS: TRY_GOAL058_SOURCE_COMPRESSION_SPECTRAL_SPREAD

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_COMPRESSION_SPECTRAL_SPREAD
OUTCOME: OPEN_FIRST_OMITTED_COMPRESSION
REQUEST_ID: REQ-2026-09-26-FIRST-OMITTED-COMPRESSION
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_FIRST_OMITTED_ERROR_COMPRESSION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: f597cd6afb69304951f9dd0f9fad3f3ed7000cde
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
HONESTY_STATE: CHALLENGER_NOT_RH
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-PLANE-PROJECTIVE-DISPLACEMENT
REQUEST_SHA256_VERIFIED: 31beef80c5b7250b33904c0f4ff74cb83d624bfd4e28a98a691db25566381f72
PREDECESSOR_VERDICT_SHA256_VERIFIED: 78750ef46a881243dc68a15d61417cb480286cf50a886e13451f052531792737
PREDECESSOR_GIT_BLOB_VERIFIED: 6fea9b1d0719d9dfc9843c8f5e9d783faf8aa318
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
ALPHA_EVENTUALLY_NONZERO: NOT_ESTABLISHED
RELATIVE_BETA_AND_GAMMA_BOUNDS: NOT_ESTABLISHED
ACTUAL_SOURCE_ACTIVITY_BOUND: NOT_ESTABLISHED
STRICT_DOMINANCE_COMPARISON: NOT_ESTABLISHED
UNBOUNDED_SOURCE_FAILURE_OF_PACKAGE: NOT_ESTABLISHED
PAID_PROJECTIVE_NEIGHBORHOOD: NONE
FULL_FORM_CONTINUITY_IN_WEIGHTED_TRANSLATION_NORM: PROVED_BELOW
SOURCE_OMITTED_FOURIER_EXPANSION_IN_FORM: ABSOLUTELY_CONVERGENT_WITH_EXPLICIT_ABSOLUTE_TAIL_ENVELOPES
SPECTRAL_SPREAD_OBSTRUCTION: NECESSARY_CONDITION_PROVED_SOURCE_SIGN_NOT_ESTABLISHED
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: FORM_CONVERGENCE_AND_ABSOLUTE_ERROR_ENVELOPES_ONLY_NOT_COMPRESSION_DOMINANCE
CLOSED_REQUESTED_DOMINANCE_QUANTIFIER: NONE
ROUTE_SCORE: 3
COGNITIVE_OPERATOR_USED: COUNTEREXAMPLE_HUNT
DISCRIMINATOR: TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
LEAN_EXECUTED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_DIAGNOSTICS_EXECUTED: false
LOCAL_FILE_IO_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
PLANE_AXIS_GAP: NOT_ESTABLISHED
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_FIRST_OMITTED_COMPRESSION.** The earliest unpaid signed source contraction is still the **full**
\[
\alpha=\mathcal W(E_\parallel,E_\parallel).
\]
I have not proved it nonzero on the selected tail. Nor have I proved the relative transverse bounds, the required activity of the actual selected vector, or a source obstruction on unbounded selected indices. **The dominance certificate is unproved, not refuted.**

There is one analytic result beyond another change of coordinates: the complete form is continuous in an explicit weighted translation norm. For the actual errors built from G and G'', this proves absolute convergence of their omitted-Fourier expansions inside the form, with explicit absolute truncation bounds. Thus the prohibited passage from an L² series to a Weil-form series is now justified for these particular source functions—not assumed for arbitrary L² functions. These bounds do not provide a nonzero lower bound for |alpha|.

The next test is a **seed-independent spectral obstruction**. The requested package necessarily forces the smaller singular value of the actual compression A to be less than the larger one divided by twice the condition number of R. A source violation would exclude every rank-one seed satisfying this package, without estimating the first omitted coefficient or replacing the actual x. The implication is proved below; no such source violation is claimed.

## 1. Source lock and the first unpaid quantities

**[COFINAL_FAMILY | PAPER]** Read all **4,426 bytes** of the authoritative TXT and all **30,683 bytes** of the local predecessor. The computed predecessor SHA-256 matches the request; its computed Git blob matches the blob fetched at the requested commit. The bootstrap was fetched from `rh_clean` and read through its response-format section. The request admits the predecessor's representation but explicitly leaves its dominance estimates unproved. fileciteturn48file0L20-L26 fileciteturn52file0L3-L5

The additional pinned reads were the inherited null-plane source formulas Q2–Q8 and the literal CCM entry definitions. They supply the unchanged smooth even G, its derivative column including the edge, and the complete finite W02–WR–Prime entries. No external theorem about positivity of the Weil form is imported. fileciteturn53file0L2-L2 fileciteturn54file0L2-L2

Keep the fixed P and
\[
m=J_P+j+2,\qquad N=6m-1,\qquad L=\log m,\qquad b_L=L/2,
\]
the original 5m splice, the entire selected x, and the original Fourier carrier −m,…,m. Work on the admitted rank-two tail of B. The vectors nu and nu-perp and their first-omitted coefficient properties are inherited; their rotation is not rederived. The symbols alpha, beta, gamma in this verdict are the three error-form entries requested here, not the earlier recurrence moment beta. fileciteturn48file0L28-L54

### 1.1. Exact full-form expression for alpha

**[FINITE_CELL | PAPER]** Put G_0=G, G_1=G'', I=[−b_L,b_L], and
\[
\psi_{n,L}(u)=L^{-1/2}e^{2\pi i n(u+b_L)/L}\mathbf1_I(u).
\]
For sigma in {parallel,perp}, write w_parallel=nu and w_perp=nu-perp. Define
\[
f_\sigma=w_{\sigma,0}G+w_{\sigma,1}G'',\qquad
z_{\sigma,n}=w_{\sigma,0}b_n+w_{\sigma,1}e_n,
\]
\[
q_\sigma(u)=L^{-1/2}\sum_{n=-m}^{m}z_{\sigma,n}e^{2\pi i n(u+b_L)/L}
\quad(u\in I).
\]
The exact errors, with no infinite-series substitution, are
\[
E_\sigma(u)=
\begin{cases}
q_\sigma(u)-f_\sigma(u),&u\in I,\\
-f_\sigma(u),&u\notin I.
\end{cases}
\tag{1}
\]
Both exterior half-lines remain. The coefficient e_n is the literal
\[
e_n=-\omega_n^2b_n+\epsilon_m,\qquad
\omega_n=2\pi n/L,\qquad \epsilon_m=2G'(b_L)/\sqrt L.
\]
Thus (1) retains the edge data of Q5/Q6. In particular, the source template
\[
\mathbf d=\left(1-\frac{15}{64\pi m}\right)b-\frac{e}{16\pi m}
\]
is not an edge-free template and is not substituted for x. fileciteturn53file0L2-L2

For two such errors, set
\[
\Gamma_{\sigma\tau}(t)=
\operatorname{Re}\sum_{\varepsilon\in\{-1,1\}}
\int_{\mathbb R}\overline{E_\sigma(u)}E_\tau(u+\varepsilon t)\,du.
\tag{2}
\]
To make the physical support bookkeeping explicit, the integral in each term is the sum over a,c in {in,out} of integrals on
\[
D_a\cap(D_c-\varepsilon t),\qquad D_{\rm in}=I,\quad D_{\rm out}=I^c,
\]
using the corresponding branch of (1) in each slot. Hence (2) includes the interior–interior, both interior–exterior, and exterior–exterior correlations. In an interior–interior product the two finite frequency indices run independently over −m,…,m.

The complete signed functional is
\[
\begin{aligned}
\mathscr W[\Gamma]={}&
\int_0^\infty2\cosh(t/2)\Gamma(t)\,dt
-\frac{\gamma_{\rm EM}+\log(4\pi)}2\Gamma(0)\\
&-\int_0^\infty
\frac{e^{t/2}\Gamma(t)-\Gamma(0)}{e^t-e^{-t}}\,dt
-\sum_{v=2}^{\infty}\frac{\Lambda(v)}{\sqrt v}\Gamma(\log v).
\end{aligned}
\tag{3}
\]
Consequently the exact source contractions are
\[
\boxed{\alpha=\mathscr W[\Gamma_{\parallel\parallel}],\qquad
\beta=\mathscr W[\Gamma_{\parallel\perp}],\qquad
\gamma=\mathscr W[\Gamma_{\perp\perp}].}
\tag{4}
\]
Equation (3) is the predecessor's complete polarized form, not a positivity assertion. The archimedean subtraction, the diagonal contribution through Gamma(0), and **all** prime powers v≥2 are retained. In particular, v>m cannot be discarded in this representation. fileciteturn52file0L2-L2

**[FINITE_CELL | PAPER]** The inherited first-pair coefficients imply
\[
\Gamma_{\parallel\parallel}(0)=2\|E_\parallel\|_2^2
\ge4\rho_*^2>0.
\tag{5}
\]
This is a genuine source lower bound for the L² mass. It does **not** prove alpha nonzero: the other signed contributions in (3) can compensate its mass term. No Cauchy inequality or positivity for W is inferred from (5).

**[COFINAL_FAMILY | PAPER]** The earliest unpaid step is nonvanishing of the complete value (4), not nonvanishing of the first omitted coefficient. In particular, no source-derived positive function a_*(m) with
\[
\left|\mathscr W[\Gamma_{\parallel\parallel}]\right|\ge a_*(m)>0
\tag{6}
\]
has been obtained on the selected tail. Formula (6) names a possible quantitative enclosure interface; a sign for alpha is not imposed as an additional requirement of the original package. Neither a nonvanishing argument without (6) nor the requested relative estimates have been obtained.

### 1.2. Actual-source activity is also unpaid

**[FINITE_CELL | PAPER]** Let J_R=adj(R), Delta_R=det(R)>0, and write zeta_*=(zeta_0,zeta_1). The requested activity has the exact numerator
\[
\nu^Tt_{\rm sel}
=\frac{\zeta_*^TJ_Ry}{\rho_*\Delta_R},
\]
\[
\boxed{
\zeta_*^TJ_Ry
=(\zeta_0R_{11}-\zeta_1R_{01})y_0
+(\zeta_1R_{00}-\zeta_0R_{01})y_1,
}
\tag{7}
\]
where
\[
y_a=\sum_{n=-m}^{m}\overline{B_{na}}x_n
=\sum_{n=-m}^{m}\sum_{k=1}^{6m-1}
\overline{B_{na}}F_{nk}c_k,\qquad a=0,1.
\tag{8}
\]
These are the **entire selected** source coefficients. No source part, MIX term, or phase is recomputed after choosing nu. The inherited reality of the plane coordinates allows the real two-dimensional notation; the conjugation in (8) is retained.

The activity condition is equivalently
\[
|\zeta_*^TJ_Ry|\ge g_*(m)\rho_*\|J_Ry\|_2>0.
\tag{9}
\]
Rank two of B and rho_*>0 prove neither y≠0 nor (9). Neither assertion is established here. Exact vanishing of alpha or failure of activity on a proved unbounded selected-index set would refute this package; no such selected set or structural vanishing has been proved.

## 2. A paid analytic supplier: continuity of the complete form

This section is a new PAPER derivation. It does not change the source functions or invoke a theorem about the signs of W.

### 2.1. A norm that tolerates the physical jumps

**[ABSTRACT | PAPER]** For a function f on the full real line define
\[
A(f)=\|e^{|u|}f(u)\|_2,
\qquad
D(f)=\sup_{0<h\le1}h^{-1/4}\|f(\cdot+h)-f\|_2,
\]
\[
\|f\|_{\mathfrak X}=A(f)+D(f).
\tag{10}
\]
D is a **translation seminorm**: it measures the L² change under a small shift. The exponent 1/4 permits endpoint jumps. The exponentially weighted part controls the pole integral and the infinite prime-power sum.

On functions with finite (10), the complete real bilinear functional (3) is absolutely defined and satisfies
\[
\boxed{
|\operatorname{Re}\mathcal W(f,g)|
\le C_W\|f\|_{\mathfrak X}\|g\|_{\mathfrak X},
}
\tag{11}
\]
where one explicit, deliberately nonsharp universal constant is
\[
\boxed{
\begin{aligned}
C_W={}&16+4\log2+|\gamma_{\rm EM}+\log(4\pi)|
+\frac32e^{1/2}\\
&+\frac{2}{1-e^{-2}}
\left(e^{-1}+\frac23e^{-3/2}\right).
\end{aligned}}
\tag{12}
\]
Here (11) concerns the complete right-hand side of (3), agreeing with the admitted W on the source functions being used. It is not an assertion that every function of finite norm (10) has any additional spectral or radical property.

### 2.2. Proof, including the subtraction at zero and every prime power

**[ABSTRACT | PAPER]** Weighted Cauchy–Schwarz for ordinary integrals gives
\[
|\Gamma_{fg}(t)|\le2e^{-t}A(f)A(g),\qquad t\ge0.
\tag{13}
\]
The pointwise inequality behind this is |u|+|u±t|≥t. It implies a bound 8A(f)A(g) for the absolute pole integral, and
\[
\left|\frac{\gamma_{\rm EM}+\log(4\pi)}2\Gamma_{fg}(0)\right|
\le|\gamma_{\rm EM}+\log(4\pi)|A(f)A(g)
\]
for the constant term.

Let tau_h f=f(·+h). The exact identity
\[
\boxed{
\Gamma_{fg}(0)-\Gamma_{fg}(h)
=\operatorname{Re}\langle\tau_hf-f,\tau_hg-g\rangle_{L^2}
}
\tag{14}
\]
therefore gives
\[
|\Gamma_{fg}(h)-\Gamma_{fg}(0)|
\le h^{1/2}D(f)D(g),\qquad0<h\le1.
\]
Split the numerator of the archimedean integrand as
\[
e^{t/2}[\Gamma(t)-\Gamma(0)]+(e^{t/2}-1)\Gamma(0).
\]
Using e^t−e^(−t)≥2t, its integral on (0,1] is bounded by
\[
e^{1/2}D(f)D(g)+\frac12e^{1/2}A(f)A(g).
\]
On [1,∞), use (13) and e^t−e^(−t)≥(1−e^(−2))e^t. The bound is
\[
\frac{2}{1-e^{-2}}\left(e^{-1}+\frac23e^{-3/2}\right)A(f)A(g).
\]
Thus the renormalized integral is absolutely convergent. This argument does not separate its two individually singular terms at zero.

Finally, since 0≤Lambda(v)≤log v,
\[
\sum_{v=2}^{\infty}\frac{\Lambda(v)}{\sqrt v}|\Gamma_{fg}(\log v)|
\le2A(f)A(g)\sum_{v=2}^{\infty}\frac{\log v}{v^{3/2}}
\le(8+4\log2)A(f)A(g).
\tag{15}
\]
For the last inequality, bound each summand by the integral of
log(x+1)x^(−3/2) on [v−1,v], and then use log(x+1)≤log x+log2 for x≥1. Its integral from 1 to infinity is 4+2log2. Combining these estimates proves (11)–(12).

Only positive L² estimates were used. **No positivity or Cauchy inequality for the indefinite form W was used.**

## 3. Application to the actual omitted Fourier series

### 3.1. Coefficient estimates must include the edge cancellation

**[COFINAL_FAMILY | PAPER]** For a=0,1 let f_a=G_a and let tilde f_(a,n) be its exact window coefficient for any integer n. For n≠0, two integrations by parts in the defining integral give the bound
\[
|\widetilde f_{a,n}|\le\frac{d_a(m)}{n^2},
\]
\[
\boxed{
d_a(m)=\frac{L^{3/2}}{4\pi^2}
\left(2|f_a'(b_L)|+\int_{-b_L}^{b_L}|f_a''(u)|\,du\right).
}
\tag{16}
\]
The endpoint values of an even f_a agree; the first-derivative endpoint contribution is included in (16). For a=1 the derivatives in this formula are G''' and G''''. The exact source G and these derivatives are smooth and rapidly decreasing, as follows from the inherited explicit kernel; all displayed source integrals are finite. They are defined independently of alpha, beta, gamma and their unknown ratios. fileciteturn53file0L2-L2

Crucially, (16) estimates the actual coefficient of G'' from its defining integral. It does **not** estimate −omega_n² tilde b_n and epsilon_m separately and then sum their bounds over all omitted indices. That invalid separation would lose their cancellation. The predecessor's grouped transverse coefficient remains grouped. fileciteturn48file0L32-L44

### 3.2. Absolute form convergence, with a quantitative tail

**[FINITE_CELL | PAPER]** Directly from the windowed exponential,
\[
\|\tau_h\psi_{n,L}-\psi_{n,L}\|_2
\le\min(2,|\omega_n|h)+\sqrt{2h/L},\qquad0<h\le1.
\]
The square-root term accounts for the two edges; it is not set to zero. Also
\[
A(\psi_{n,L})=\sqrt{(m-1)/L}.
\]
Consequently
\[
\|\psi_{n,L}\|_{\mathfrak X}
\le a_m^{\rm tr}+b_m^{\rm tr}|n|^{1/4},
\]
\[
a_m^{\rm tr}=\sqrt{(m-1)/L}+\sqrt{2/L},\qquad
b_m^{\rm tr}=2^{3/4}(2\pi/L)^{1/4}.
\tag{17}
\]
These constants are unrelated to the Ferrers budget B(m) and to the earlier ground-centering coefficient a.

For any integer D≥m, (16)–(17) imply
\[
\boxed{
\left\|\sum_{|n|>D}\widetilde f_{a,n}\psi_{n,L}\right\|_{\mathfrak X}
\le T_a(m,D):=
2d_a(m)\left(\frac{a_m^{\rm tr}}D+
\frac{4b_m^{\rm tr}}{3D^{3/4}}\right).
}
\tag{18}
\]
Indeed, sum n^(−2) and n^(−7/4) by their decreasing integral bounds. The series is absolutely summable in the norm (10); its L² limit is the inherited Fourier tail. Completeness can be checked directly: weighted L² convergence identifies the limit, and the translation bounds pass to that limit for every h and then to their supremum.

**[COFINAL_FAMILY | PAPER]** Hence, for every selected m on the admitted tail, both source error expansions converge in a norm for which the **complete** form is continuous. Products of their coefficient-norm sums are finite, so their double expansions in (3) are absolutely convergent. This establishes the previously missing stronger convergence statement for these errors, with the explicit all-m, all-D estimate (18). It does not assert that L² convergence alone would have sufficed.

### 3.3. The exterior functions are part of the estimate

**[FINITE_CELL | PAPER]** For O_a=−f_a 1_(I^c), an explicit bound is
\[
\|O_a\|_{\mathfrak X}\le o_a(m):=
\|e^{|u|}f_a\mathbf1_{I^c}\|_2
+\|f_a'\mathbf1_{I^c}\|_2+2|f_a(b_L)|.
\tag{19}
\]
For the translation term, integrate the ordinary derivative over a shift of length h and retain the two boundary jumps. The L² bound is at most
h||f_a'1_(I^c)||_2+2|f_a(b_L)|sqrt(h); dividing by h^(1/4) and taking h≤1 proves (19). Both exterior half-lines occur in every norm in (19).

The exact error satisfies
\[
\|\Delta_a\|_{\mathfrak X}\le U_a(m):=o_a(m)+T_a(m,m).
\tag{20}
\]
For sigma in {parallel,perp}, set
\[
U_\sigma=\sum_{a=0}^1|w_{\sigma,a}|U_a,
\qquad T_\sigma(D)=\sum_{a=0}^1|w_{\sigma,a}|T_a(m,D).
\]
These are explicit absolute bounds, not normalized errors divided by the unknown alpha.

Define a finite-tail approximation, with the original window and physical parameter m held fixed,
\[
\Delta_a^{[D]}=
-\sum_{m<|n|\le D}\widetilde f_{a,n}\psi_{n,L}
-f_a\mathbf1_{I^c},\qquad
E_\sigma^{[D]}=\sum_a w_{\sigma,a}\Delta_a^{[D]}.
\tag{21}
\]
D is an auxiliary analytic truncation only: **the selected carrier, x, K_j, and splice do not change.** The exterior functions in (21) are exact, not truncated. We have
\[
\|E_\sigma-E_\sigma^{[D]}\|_{\mathfrak X}\le T_\sigma(D).
\]

Let alpha_D, beta_D, gamma_D be the complete form values of these finite-tail approximants. Continuity now supplies genuine two-sided absolute error enclosures:
\[
\boxed{
\begin{aligned}
|\alpha-\alpha_D|&\le C_W T_\parallel(D)[2U_\parallel+T_\parallel(D)],\\
|\beta-\beta_D|&\le C_W\{T_\parallel(D)U_\perp+T_\perp(D)U_\parallel
+T_\parallel(D)T_\perp(D)\},\\
|\gamma-\gamma_D|&\le C_W T_\perp(D)[2U_\perp+T_\perp(D)].
\end{aligned}}
\tag{22}
\]
For example, subtract the two bilinear expressions, retaining one error in each difference, and apply (11). No sign for an entry is used.

The returned prime-power range has its own explicit absolute tail bound. For any integer J≥2,
\[
\boxed{
\sum_{v>J}\frac{\Lambda(v)}{\sqrt v}|\Gamma_{fg}(\log v)|
\le\frac{2A(f)A(g)}{\sqrt J}
\left(2\log J+4+2\log2\right).
}
\tag{23}
\]
This is the same integral comparison as (15), starting at J. It bounds a tail; it does not authorize deleting it without its error. In particular, setting J=m leaves the explicitly bounded, generally nonzero range v>m.

## 4. Why these estimates do not pay the requested dominance

**[COFINAL_FAMILY | PAPER]** The distinction is now precise. Equations (18), (19), (22), and (23) control absolute contributions of all omitted Fourier indices, both physical exterior tails, and all returned prime powers. They do not establish any source-derived nonzero lower bound for the full alpha, or any bound for the ratios beta/alpha and gamma/alpha small enough to survive the activity and condition-number losses.

In particular, the directly supplied estimate
\[
|\alpha|\le C_WU_\parallel^2
\]
contains zero. The stronger enclosures (22) could separate zero only after a signed source estimate for alpha_D with a sufficient margin; no such estimate is supplied here. Increasing D in an absolute bound is not a proof that the required relative comparison holds on the selected family, and no numerical or truncation-depth campaign is authorized.

There are three distinct boundaries:

* The coefficient cancellation concerns only the pair ±(m+1). It does not cancel |n|≥m+2, and (16)–(18) do not assert relative suppression of that surviving tail.
* The physical exterior functions in (1) and (19) do not vanish. Their couplings with the interior errors remain in (2)–(4).
* The finite K uses prime powers up to m, while the radical-error expression uses every v≥2. These representations agree only through the complete admitted form identity, not by discarding the returned tail termwise.

The prior Ferrers-tail B(m) concerns a different coefficient cutoff, N=6m−1. It cannot serve as the missing relative bound here. The selected t_sel in (7)–(9) remains an additional, source-dependent activity question; an upper bound on its norm does not answer it. These are failures to derive the requested estimates, not proofs that those estimates are impossible. fileciteturn48file0L28-L56

Thus no explicit projective neighborhood can be issued under the current result. The conditional neighborhood formula of the predecessor remains conditional. fileciteturn52file0L2-L2

## 5. One distinct next PAPER falsifier: two singular values

### TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION

This test targets a necessary consequence of the entire proposed rank-one package. Unlike the previous tests, it does not choose a Fourier seed, estimate an activity angle, or ask for the same alpha-relative inequalities again.

### 5.1. A seed-independent necessary condition

**[ABSTRACT | PAPER]** Keep the same source coordinate basis (G,G'') and put
\[
\kappa_R=\|R\|_2\|R^{-1}\|_2\ge1.
\]
Let s_1(A)≥s_2(A)≥0 denote the **singular values**, which measure the magnitudes of the action of A and do not assume A positive. If the requested dominance package holds, then
\[
\boxed{A\ne0,\qquad \frac{s_2(A)}{s_1(A)}<\frac1{2\kappa_R}.}
\tag{24}
\]

To prove this implication, put E=A−alpha nu nu^T. The admitted two-coordinate decomposition and the requested relative estimates give
\[
\|E\|_2\le(2\delta_1+\delta_2)|\alpha|.
\]
For the unit vector nu, s_1(A)≥|nu^TA nu|=|alpha|. For a unit vector perpendicular to nu, its A-image equals its E-image, so the smallest singular value satisfies s_2(A)≤||E||_2. Finally, actual nonzero activity implies g_*≤1. The strict requested comparison gives
\[
\frac{s_2(A)}{s_1(A)}
\le2\delta_1+\delta_2
<\frac{g_*}{2\kappa_R}\le\frac1{2\kappa_R}.
\]
This proves (24). No modification of x is made; the universal bound g_*≤1 is merely a necessary consequence of its requested activity inequality.

For a real symmetric 2×2 matrix define
\[
T_A=\operatorname{tr}(A^2)=A_{00}^2+2A_{01}^2+A_{11}^2,
\qquad D_A=\det A=A_{00}A_{11}-A_{01}^2.
\]
Since T_A=s_1²+s_2² and |D_A|=s_1s_2, and z/(1+z²) increases for 0≤z≤1, (24) implies
\[
\boxed{
\mathfrak J_m:=2\kappa_R T_A-(4\kappa_R^2+1)|D_A|>0.
}
\tag{25}
\]
The formula uses the same fixed source units as the requested Euclidean coefficient norms. It is not declared invariant under an arbitrary rescaling of G against G''.

### 5.2. The concrete source test

**[COFINAL_FAMILY | CONDITIONAL]** Seek an explicitly proved unbounded set of selected indices and a source-derived function h(m)>0 such that
\[
\boxed{\mathfrak J_m\le-h(m)<0.}
\tag{26}
\]
A proof of (26) would refute the requested dominance package on every eventual tail. More strongly, in the same source coordinates and with the same condition-number requirement, it would refute every unit rank-one seed satisfying that package, regardless of its proposed activity direction. This is why the test has greater class-wide falsifying power than another first-pair rotation.

**No source bound (26) is established in this verdict.** Nor is a sign claimed for J_m. A positive J_m would only survive this necessary test; it would not pay alpha-nonvanishing, relative suppression, activity, or the strict original comparison. A finite failed cell would not be an eventual-family kill. Exact boundary equality would require its own exact, correctly scoped incompatibility argument; it must not be inferred from a zero-straddling enclosure.

### 5.3. Fully source-bound evaluation; no positivity substitution

**[FINITE_CELL | PAPER]** The entries used in (25) are exactly
\[
\boxed{
A_{ab}=\operatorname{Re}\sum_{n,n'=-m}^{m}
\overline{B_{na}}K_{j,nn'}B_{n'b},\qquad a,b\in\{0,1\}.
}
\tag{27}
\]
Equivalently they are the full error-form values of the inherited radical identity. This finite representation retains the literal diagonal, the archimedean subtraction, and the complete finite W02–WR–Prime constructor. The pinned constructor explicitly distinguishes its diagonal branch. fileciteturn54file0L2-L2

One exact source mechanism for a signed determinant estimate is the finite minor expansion. For index pairs I=(n_1<n_2), J=(n'_1<n'_2) in −m,…,m, write B_I for the two selected rows of B. Then
\[
\boxed{
D_A=\sum_{I,J}\det(B_I)\det(K_{j,I,J})\det(B_J).
}
\tag{28}
\]
This follows by applying the finite determinant multiplication formula twice to B^T K_j B. It retains all ordered choices of the two row-pairs I,J; diagonal and off-diagonal minors of K are both present. The reality of the source plane is used here; (27) keeps the conjugate convention explicit.

No term of (28) is declared positive. In particular, (26) is **not** whole-plane positivity substituted for the actual direction. It is an obstruction based on two singular magnitudes, valid also when A has eigenvalues of opposite signs. If one instead evaluates (27) through the error functions, (3) must remain complete; (22)–(23) now provide legitimate absolute remainder bounds for that representation.

### Two representations, one commissioned test

| Representation | Discriminating power | PAPER cost and principal risk |
|---|---|---|
| **Chosen: source spectral spread, (25)–(28).** | One unbounded negative upper certificate rules out all rank-one seeds satisfying the proposed package, without determining the actual x-activity. | Three actual source contractions and their signed determinant. Large cancellations in full K remain; a necessary-condition pass proves no dominance. |
| **Alternative: the now justified omitted-tail expansion with the absolute enclosures (18)–(23).** | Can rigorously transfer a future signed finite-tail source estimate to alpha, beta and gamma without an illegal L²/form interchange. | Still needs a nonzero source scale and activity. Absolute bounds may be far too coarse relative to the small signed entries. No cutoff escalation is commissioned. |

## 6. Adversarial checks and closeout

**[ABSTRACT | PAPER]** The strongest attack on the new analytic supplier is that endpoint jumps may make the archimedean integral divergent. The translation proof includes the square-root boundary term in (17), and (14) gives an integrable t^(−1/2) bound after subtraction. It never replaces the renormalized numerator by two separate divergent integrals. At infinity, (13) and (15) control the pole term and the complete prime sum. Thus the convergence result survives that attack.

**[ABSTRACT | PAPER]** The singular-value detector has two exact calibration cases, not selected-source counterexamples. For A=I, (25) gives J=−(2kappa_R−1)²<0, correctly excluding rank-one dominance. For A=diag(1,0), it gives J=2kappa_R>0, correctly not excluding a rank-one compression; it still does not certify activity of the actual selected vector. These checks distinguish a necessary obstruction from a sufficient dominance proof.

**[COFINAL_FAMILY | PAPER]** Prediction scoring: before the form-domain check, the registered expectation was that a weighted translation bound could justify the omitted-mode expansion, without predicting the sign of alpha. That expectation is confirmed by (11)–(23). The inherited first-pair cancellation was accepted as an input, not rescored as a new result. No selected sign or dominance prediction was registered and no such result is credited. The seed-independent implication (24)–(25) is proved; its actual-source test (26) is proposed, not reported as performed successfully.

What became smaller is the convergence debt: these source series may now be used in the complete form with explicit absolute error ledgers. What did not become smaller is the unpaid nonzero/relative scale of the signed compression, starting with alpha, and the actual activity (9). No requested dominance quantifier is closed, no selected certificate is killed, and no P_m-sector comparison is paid.

The three structural checks are explicit. The bridge is weighted translation regularity to the full renormalized form. The inherited vanishing mechanism cancels one Fourier pair, not the error energy. The new class-wide falsifier is a signed source upper bound (26), excluding every admissible rank-one seed at once. The next action is therefore a counterexample hunt against the package, not a third redefinition of its leading vector.

```yaml
DOWNSTREAM_CONSUMER: actual_plane_axis_direction_then_separate_P_m_sector_test
ACTUAL_CONSUMER_REQUIREMENT: paid_directional_information_for_the_unchanged_r_not_necessarily_rank_one_dominance
ORIGINAL_REQUESTED_OBJECT: first_omitted_pair_relative_compression_and_actual_source_activity_package
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_package_not_proved_necessary_for_the_actual_axis_or_full_Abel_sign
KNOWN_WEAKER_INTERFACES:
  - direct_source_homogeneous_bounds_for_rT_P_m_r_without_any_rank_one_reference
  - a_paid_projective_sector_from_full_compression_without_first_pair_dominance
  - actual_fixed_mixture_control_without_the_whole_cone_certificate
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
MINIMAL_MISSING_ESTIMATE: nonzero_full_source_alpha_and_compatible_relative_couplings_with_actual_activity
FIRST_UNPAID_SOURCE_CONTRACTION: equation_4_alpha_with_complete_equations_1_to_3
ACTIVITY_DEBT: equation_9_with_actual_finite_indices_in_8
NEW_CLOSED_ANALYTIC_QUANTIFIER: every_selected_m_and_every_D_ge_m_have_the_absolute_form_tail_enclosures_18_to_23
DISCRIMINATOR: TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION
REOPEN_TRIGGER: source_negative_upper_bound_26_on_an_explicit_unbounded_selected_index_set_or_paid_original_package
KILLED_REQUESTED_THEOREM_SHAPE: NONE
COMPRESSION_CERTIFICATE_DEAD: false
WHOLE_CONE_CERTIFICATE_DEAD: false
ACTUAL_D_KILLED: false
NOVELTY_AXIS: full_form_translation_continuity_and_source_absolute_Fourier_tail_enclosures_plus_seed_independent_rank_one_obstruction
MEMORY_ENTRY:
  target: selected_first_omitted_error_compression
  status: OPEN
  cognitive_operator_used: COUNTEREXAMPLE_HUNT
  invariant_learned: first_pair_nonzero_mass_and_absolute_form_convergence_do_not_supply_a_nonzero_signed_energy_scale
  forbidden_future_move: promote_absolute_tail_control_to_relative_dominance_or_a_necessary_spectral_test_to_sufficiency
  next_decisive_test: TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION
```

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_COMPRESSION_TWO_SINGULAR_VALUE_OBSTRUCTION`, on paper, for the unchanged source A=B* K_j B and R=B*B.** Seek the upper certificate (26) on an explicitly unbounded selected-index set, using the full indexed contractions (27) and signed minor expansion (28), or the complete error-form representation with the now proved absolute convergence bounds. Keep the literal diagonal, both physical edges, Q5/Q6, all finite-source prime powers, and every returned prime power whenever using the global error representation. Do not replace A by a positive matrix, change its coordinate units, substitute an arbitrary x, or evaluate only an off-diagonal commutator. A successful negative upper certificate refutes only the rank-one dominance package; a positive necessary-test result is not a dominance pass and must not trigger another seed rotation or an automatic cutoff escalation. No numerical diagnostics, mathematical runtime, Lean, repository write, first-tau-sign claim, Schur-floor claim, route promotion, or RH claim is authorized.
