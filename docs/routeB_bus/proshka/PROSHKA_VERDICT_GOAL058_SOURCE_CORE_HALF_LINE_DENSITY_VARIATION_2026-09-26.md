# STATUS: TRY_GOAL058_SOURCE_CORE_LATTICE_VARIATION_WITNESS

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SOURCE_CORE_LATTICE_VARIATION_WITNESS
OUTCOME: OPEN_SOURCE_VARIATION
REQUEST_ID: REQ-2026-09-26-SOURCE-CORE-HALF-LINE-DENSITY-VARIATION
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION
CALL_CLASS: DELEGATED_STRATEGIC_REVIEW
SOURCE_COMMIT: 9111fada99b2f5ba024335ac396545c6eea73034
PHASE_ID: PHASE_GOAL058_SELECTED_FERRERS_GROUND_TRACKING_20260923
ROUTE_ID: RouteB_TwoLevelSpectralLadder
FRONT_ID: GOAL058_SELECTED_FERRERS_GROUND_TRACKING
SOURCE_OBJECT_FAMILY_ID: SELECTED_FERRERS_MODE0_MODE4_COFINAL_CCM
TERMINAL_CONSUMER_ID: Q3.RouteB.rh_of_real_zero_family_tendsto_centeredXi
CONVENTION_LOCK_ID: GOAL058_SELECTED_FERRERS_C_2PI_M_SOURCE_ORDER_MINUS_Z
PREDECESSOR: REQ-2026-09-26-SOURCE-CORE-CONTINUOUS-LAG-DECAY
REQUEST_SHA256_LOCALLY_VERIFIED: 1dc1c0bbcbba3f20b8c8a4ece8ee7aaf000750cdeb68d26818666b03ef143ff8
REQUEST_BYTES: 5550
REQUEST_LF: 112
PREDECESSOR_VERDICT_SHA256_LOCALLY_VERIFIED: 32d338448f4305a4bdd2b627dd977aa86388268dfcd802acff1f947aaf4d6fce
PREDECESSOR_BYTES: 32542
PREDECESSOR_LF: 653
PREDECESSOR_GIT_BLOB_LOCALLY_AND_REMOTELY_MATCHED: f7ab602d8f641c92e6d99234565da525d31eb123
BOOTSTRAP_GIT_BLOB_READ: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
AUDIT_READ: docs/Codex/PAPER_CHAIN.md_source_core_continuous_lag_decay_test_at_SOURCE_COMMIT
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
SV_ON_ALL_SELECTED_log_m_GT_120: NOT_ESTABLISHED
SOURCE_NEGATIVE_VARIATION_MARGIN: NOT_ESTABLISHED
FULL_FIXED_LAG_CANDIDATE: NOT_ESTABLISHED
REQUESTED_THEOREM_SHAPE_KILLED: NONE
NEW_PAID_CONTRIBUTION: CENTRAL_HALF_LINE_DENSITY_VARIATION
NEW_CENTRAL_FREQUENCY_REGION: ABS_xi_LE_m_OVER_log_m_SQUARED
NEW_CENTRAL_VARIATION_BOUND: E11_OVER_SQRT_6
NEW_CENTRAL_MASS_BOUND: 2_E11_OVER_3_log_m
NEW_EXACT_REPRESENTATION: SOURCE_LATTICE_DENSITY_WITH_PARITY_RESTRICTED_CAUCHY_PAIRING
NEXT_TEST: TEST_SOURCE_CORE_LATTICE_VARIATION_WITNESS
NEXT_TEST_STATUS: CONDITIONAL_NOT_PROVED
NEXT_TEST_SUCCESS_SCOPE: REFUTES_ONLY_SV
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_QUALIFICATION: COFINAL_PROPER_SPECTRAL_REGION_PAID_NOT_FULL_VARIATION_BUDGET
COGNITIVE_OPERATOR_USED: DUALIZE
ROUTE_SCORE: 3
DISCRIMINATOR: Delta_var_EQUALS_16_E11_MINUS_M_MINUS_TOTAL_VARIATION
NEXT_TEST_DISCRIMINATOR: U_lattice_EQUALS_16_E11_MINUS_M_MINUS_LATTICE_VARIATION_LOWER_BOUND
C0_128: CONDITIONAL_NOT_ACTIVATED
C_INT_134: CONDITIONAL_NOT_ACTIVATED
C2_146: CONDITIONAL_NOT_ACTIVATED
NEW_PAPER_DERIVATIONS_INDEPENDENTLY_AUDITED: false
MATHEMATICAL_RUNTIME_EXECUTED: false
NUMERICAL_CUTOFF_SEARCH_EXECUTED: false
LEAN_EXECUTED: false
LOCAL_FILE_IO_TEXT_VALIDATION_AND_HASHING_ONLY: true
REPOSITORY_WRITTEN: false
SOURCE_FAMILY_CHANGED: false
CARRIER_CUTOFF_CHANGED: false
DILATION_BOUNDARY_Q_CHANGED: false
DENOMINATOR_CHANGED: false
NEW_SEED_SELECTED: false
HONESTY_STATE: CHALLENGER_NOT_RH
EXPONENT_ONE_PRIME_BLOCK: OPEN_SEPARATE
PRIME_SQUARE_COMPENSATION: OPEN_SEPARATE
OPPOSITE_SIDE_CORRELATION: OPEN_SEPARATE
INTEGRATED_SYMBOL_DEVIATION: OPEN_SEPARATE
TRANSFER_T: OPEN
ACTUAL_J_SIGN: OPEN
FIRST_TAU_SIGN: OPEN
SCHUR_FLOOR: OPEN
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

Ы. **OPEN_SOURCE_VARIATION.** I have neither a nonnegative lower envelope for the requested variation margin on the entire selected tail nor a negative upper envelope at an admitted source cell. The constant-16 lag statement and the square constants **128, 134, 146 remain unproved/conditional at their stated scopes**.

There is a new, source-paid proper-contribution bound. For every admitted selected cell with \(L=\log m>120\),
\[
\boxed{
\int_{|\xi|\le m/L^2}|\rho_m'(\xi)|\,d\xi
\le \frac{E}{\sqrt6}<\frac E2,
\qquad
\int_{|\xi|\le m/L^2}\rho_m(\xi)\,d\xi
\le\frac{2E}{3L}.
}
\tag{A}
\]
This is not the generic full-variation bound \(\mathcal V_m\le bM_m\). It uses projection orthogonality for the high coefficients and a separate, oscillatory estimate for the **actual nonzero endpoint block**, whose amplitude is paid by the source exterior. The original denominator remains \(E=E_{11}\).

The first unpaid comparison is the remaining source-moment pairing outside this central interval against the exact residual budget. To avoid simply commissioning another stronger upper-bound interface, the one next test below is a **finite-lattice lower witness for total variation**. Its exact formula retains the source coefficients, their parity-restricted Cauchy sums, and their interference. Such a witness would reject only **SV**. No such witness is claimed in this verdict.

## 1. Source lock and accepted boundary

**[FINITE_CELL | PAPER — source record]** The attached authoritative TXT was read in full and locally hashed: **5,550 bytes, 112 LF**, with the SHA-256 in the header. Its request, boundary, pin and predecessor binding agree with the canonical instruction. The full mounted predecessor was read: **32,542 bytes, 653 LF**. Its locally computed SHA-256 equals the stipulated hash, and its locally computed Git blob equals the blob returned at the pinned repository commit. The complete local text, not a truncated connector preview, is the predecessor used here. fileciteturn10file0L1-L20 fileciteturn14file0L3-L5

The bootstrap was fetched from `rh_clean` through the GitHub connector and read through its response-format section. I also opened the requested `docs/Codex/PAPER_CHAIN.md` at `9111fada99b2f5ba024335ac396545c6eea73034`, specifically the section headed **“source core continuous lag decay test.”** Its limited audit accepts the earlier mass identity, endpoint estimate, bounded-index lag margin, additional lag regions, and half-line moment identities. It does not prove SV or the full lag statement. The new derivations below are not covered by that audit. fileciteturn13file0L2-L2

**[COFINAL_FAMILY | PAPER — fixed source contract]** Fix the same \(P\) and
\[
m=J_P+j+2,\quad L=\log m>120,\quad b=L/2,\quad Q=\sqrt m,
\quad \omega_n=2\pi n/L.
\]
Keep the original \(5m\) splice, carrier \(|n|\le m\), and source
\[
\begin{aligned}
h_*(x)&=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2},\\
G(u)&=e^{u/2}\sum_{r\ge1}h_*(re^u),\qquad g=G'',\\
h&=T_mg,\quad f=h-g,\quad E=\|f\|_{L^2(\mathbb R)}^2>0,\\
\varepsilon_m&=2G'(b)/\sqrt L,\quad
 d=\varepsilon_m\sum_{|n|\le m}\psi_{n,L},\quad k=f-d,\\
\psi_{n,L}(u)&=L^{-1/2}e^{i\omega_n(u+b)}\mathbf1_{[-b,b]}(u).
\end{aligned}
\tag{1}
\]
These are the real, even source and projection in the request. Write
\[
E_O=2\int_b^\infty|g(u)|^2du,\qquad
D_d=\|d\|_2^2,\qquad v=\mathbf1_{[0,b]}k,
\]
so that the admitted exact identity is
\[
\boxed{M=\|v\|_2^2=\frac{E-E_O+D_d}{2},\qquad D_d<\frac{3E}{L}.}
\tag{2}
\]
In this verdict \(\mathcal V\) denotes the request's \(V_m=\int|\rho_m'|\); this merely distinguishes it from the earlier arithmetic core. The target is exactly
\[
\boxed{
\Delta^{\rm var}=16E-M-\mathcal V\ge0,
\qquad \mathcal V\le\frac{31}{2}E+\frac12E_O-\frac12D_d.
}
\tag{SV}
\]
Neither \(M\) nor \(\|k\|_2^2\) replaces \(E\). fileciteturn10file0L30-L71

## 2. The literal pairing and its source coefficients

**[COFINAL_FAMILY | PAPER]** Keep, for every integer \(n\),
\[
e_n=\int_{-b}^b g(u)\overline{\psi_{n,L}(u)}\,du,
\qquad
c_n=\begin{cases}\varepsilon_m,&|n|\le m,\\e_n,&|n|>m.\end{cases}
\tag{3}
\]
The dependence on \(m\) in \(c_n\) is suppressed only in notation. The coefficients are real and satisfy \(c_{-n}=c_n\). On the original window,
\[
f=-\sum_{|n|>m}e_n\psi_{n,L},\qquad
k=-\sum_{n\in\mathbb Z}c_n\psi_{n,L}
\quad\text{in }L^2,
\]
and orthogonality gives
\[
\boxed{E=E_O+\sum_{|n|>m}|e_n|^2.}
\tag{4}
\]
The low block of \(k\) is therefore \(-\varepsilon_m\), not zero. These expansions and the half-line definitions are fixed by the request. fileciteturn10file0L36-L60

For an explicit source formula, differentiation of (1) gives
\[
\begin{aligned}
\mathcal P(x)&=-64x^4+448x^3-660x^2+150x,\\
e_n&=\frac{2(-1)^n}{\sqrt L}\sum_{r\ge1}\int_0^b
 e^{u/2}\mathcal P(\pi r^2e^{2u})e^{-\pi r^2e^{2u}}
 \cos(\omega_nu)\,du.
\end{aligned}
\tag{5}
\]
All \(r\ge1\) remain. On each fixed window, the polynomial-Gaussian majorant justifies this source interchange. No separate relative estimate for an individual source block is inferred from it.

Use the unitary Fourier transform and the same center \(a=b/2\):
\[
\Psi(\xi)=\widehat v(\xi),\qquad
Z(\xi)=\widehat{(u-a)v}(\xi),\qquad
\rho=|\Psi|^2.
\]
The admitted derivative identity can be written
\[
\boxed{\rho'=2\operatorname{Im}(Z\overline\Psi).}
\tag{6}
\]
Indeed, \(\Psi'=-i\widehat{uv}\); subtracting the real multiple \(a|\Psi|^2\) from the pairing changes no imaginary part.

For finite \(N\ge m\), define the request's \(S_{0,N},S_{1,N}\) using
\[
J_0(\lambda,b)=\int_0^b e^{i\lambda u}du,
\quad J_1(\lambda,b)=\int_0^b u e^{i\lambda u}du,
\quad J_0(0,b)=b,\quad J_1(0,b)=b^2/2.
\]
Then the exact finite product is
\[
S_{1,N}\overline{S_{0,N}}
=\sum_{|n|,|q|\le N}
 c_nc_q(-1)^{n-q}
 [J_1(\omega_n-\xi,b)-aJ_0(\omega_n-\xi,b)]
 \overline{J_0(\omega_q-\xi,b)}.
\tag{7}
\]
The \(n=q\) terms are present. The centered moment vanishes at its own argument \(\lambda=0\), but this does not annihilate the product's other diagonal or mixed terms.

The stipulated \(L^2\)-to-\(L^1\) convergence gives
\[
\boxed{
\mathcal V=\lim_{N\to\infty}\frac1{\pi L}
\int_{\mathbb R}\left|\operatorname{Im}
 (S_{1,N}\overline{S_{0,N}})\right|d\xi.
}
\tag{8}
\]
Restriction of the integral to any fixed measurable frequency set preserves this convergence. The absolute value stays **after the full pairing**. No absolute infinite-double-sum interchange is needed. fileciteturn10file0L73-L87

## 3. New paid contribution: central spectral variation

### 3.1. The endpoint amplitude is paid by the exterior, not by interior decay

**[COFINAL_FAMILY | PAPER]** Put \(B=G'(b)\). The predecessor's admitted source estimate is
\[
F(u)=-g(u)>0,\qquad F(u+s)\le e^{-\pi ms}F(u),
\quad u\ge b,\ s\ge0.
\tag{9}
\]
It is used only on its exterior domain. The same source has \(G'(\infty)=0\), so
\[
B=\int_b^\infty F(u)du>0,
\]
and therefore
\[
\begin{aligned}
B^2
&=2\int_b^\infty F(u)\int_u^\infty F(y)\,dy\,du\\
&\le\frac2{\pi m}\int_b^\infty F(u)^2du
=\frac{E_O}{\pi m}
\le\frac E{\pi m}.
\end{aligned}
\tag{10}
\]
This is the audited exterior-amplitude step used in the predecessor, not an extension of (9) into the window. fileciteturn12file0L2-L2 fileciteturn13file0L2-L2

### 3.2. Bounds for the high-coefficient half-window moments

**[COFINAL_FAMILY | PAPER — new bounds]** Let
\[
F_0=\widehat{\mathbf1_{[0,b]}f},\qquad
F_1=\widehat{(u-a)\mathbf1_{[0,b]}f}.
\]
For the whole auxiliary region
\[
|\xi|\le\frac{\pi m}{L},\qquad |n|>m,
\]
put \(\lambda_n=\omega_n-\xi\). Then
\[
|\lambda_n|\ge\frac{\pi(2|n|-m)}L
\ge\frac{\pi|n|}L.
\tag{11}
\]
Since \(|J_0(\lambda,b)|\le2/|\lambda|\) for \(\lambda\ne0\), (4) and Cauchy–Schwarz in the **high coefficient index** give
\[
\begin{aligned}
|F_0(\xi)|^2
&\le\frac{E}{2\pi L}
 \sum_{|n|>m}|J_0(\lambda_n,b)|^2\\
&\le\frac{E}{2\pi L}\frac{8L^2}{\pi^2m}
=\frac{4LE}{\pi^3m}.
\end{aligned}
\tag{12}
\]
Here \(\sum_{n>m}n^{-2}\le\int_m^\infty x^{-2}dx=1/m\). The coefficient energy is bounded by the original \(E\), not identified with it.

Integration by parts inside the moment gives
\[
|J_1(\lambda,b)-aJ_0(\lambda,b)|
\le\frac b{|\lambda|}+\frac2{|\lambda|^2}.
\]
On (11), and already for \(m\ge16\),
\[
b+\frac2{|\lambda_n|}
\le L\left(\frac12+\frac2{\pi(m+1)}\right)
\le\frac{3L}{5}.
\]
Consequently,
\[
\begin{aligned}
|F_1(\xi)|^2
&\le\frac E{2\pi L}
 \sum_{|n|>m}\frac{9L^4}{25\pi^2n^2}\\
&\le\frac{9L^3E}{25\pi^3m}.
\end{aligned}
\tag{13}
\]
Both moments are legitimate limits of the high-coefficient sums: their coefficient kernels are square-summable, and integration against a bounded function on the finite window is continuous on \(L^2\). This is not a relative estimate inferred from \(e_n=O_m(n^{-2})\).

### 3.3. The nonzero low block requires an oscillatory estimate of its own

**[COFINAL_FAMILY | PAPER — new source-paid bounds]** Set
\[
D_0=\widehat{\mathbf1_{[0,b]}d},\qquad
D_1=\widehat{(u-a)\mathbf1_{[0,b]}d}.
\]
The exact endpoint synthesis has the reflected expression
\[
d(b-z)=\frac{2B}{L}
 \frac{\sin(Az)}{\sin(\pi z/L)},
\quad A=\frac{(2m+1)\pi}{L},\quad 0\le z\le b,
\tag{14}
\]
with its continuous value at \(z=0\). This follows directly from the original finite sum of \(\psi_{n,L}\); no endpoint coefficient is removed.

I claim, on the same entire region \(|\xi|\le\pi m/L\),
\[
\left|\int_0^b d(u)e^{-i\xi u}du\right|<5B.
\tag{15}
\]
Here is a boundary-complete proof. Let \(z_0=1/A\), so \(0<z_0<b\). On \([0,z_0]\), the Dirichlet sum has modulus at most \(2m+1\), giving
\[
\left|\int_0^{z_0}
 \frac{\sin(Az)}{\sin(\pi z/L)}e^{i\xi z}dz\right|
\le\frac L\pi.
\]
On \([z_0,b]\), the function
\[
w(z)=\frac1{\sin(\pi z/L)}
\]
is positive and decreasing. For any nonzero real \(\beta\), integration by parts gives
\[
\left|\int_{z_0}^b w(z)e^{i\beta z}dz\right|
\le\frac{w(z_0)+w(b)+\int_{z_0}^b|w'(z)|dz}{|\beta|}
=\frac{2w(z_0)}{|\beta|}.
\]
Use \(\sin(\pi z/L)\ge2z/L\) on \([0,b]\), and split the numerator sine into its two exponentials. Their frequencies obey
\[
|A\pm\xi|\ge\frac{\pi(m+1)}L,
\qquad
\frac{2w(z_0)}{|A\pm\xi|}
\le\frac{LA}{|A\pm\xi|}<2L.
\]
Thus the second integral has modulus less than \(2L\). Multiplication by \(2B/L\), with the harmless phase \(e^{-ib\xi}\), proves
\[
\left|\int_0^b d(u)e^{-i\xi u}du\right|
<\left(4+\frac2\pi\right)B<5B.
\]
This uses cancellation in the endpoint synthesis; replacing its entire integral by an absolute Dirichlet-kernel integral would incur an unnecessary logarithm.

Also, directly from (14),
\[
|d(b-z)|\le\frac Bz\quad(0<z\le b),
\qquad \int_0^b z|d(b-z)|dz\le Bb.
\]
Since \(u-a=a-z\) after reflection, (15) gives
\[
\left|\int_0^b(u-a)d(u)e^{-i\xi u}du\right|
\le(5a+b)B=\frac{7L}{4}B.
\]
With (10) and the unitary Fourier factors, the two resulting bounds are
\[
\boxed{
|D_0(\xi)|^2\le\frac{25E}{2\pi^2m},
\qquad
|D_1(\xi)|^2\le\frac{49L^2E}{32\pi^2m},
\quad |\xi|\le\pi m/L.
}
\tag{16}
\]
The apparent \(1/z\) estimate is used only after multiplication by \(z\); no nonintegrable majorant at \(z=0\) is integrated.

### 3.4. Combine the moments before bounding the density derivative

**[COFINAL_FAMILY | PAPER]** Exactly
\[
\Psi=F_0-D_0,\qquad Z=F_1-D_1.
\]
Using \(|x-y|^2\le2|x|^2+2|y|^2\), (12)–(13), and (16),
\[
\begin{aligned}
|\Psi(\xi)|^2
&\le\left(\frac8{\pi^3}+\frac{25}{\pi^2L}\right)\frac{LE}{m}
\le\frac{LE}{3m},\\
|Z(\xi)|^2
&\le\left(\frac{18}{25\pi^3}+\frac{49}{16\pi^2L}\right)
       \frac{L^3E}{m}
\le\frac{L^3E}{32m}.
\end{aligned}
\tag{17}
\]
These constants hold throughout \(L>120\). For a rational check using only \(\pi>3\), the first coefficient is less than
\[
\frac8{27}+\frac{25}{1080}=\frac{23}{72}<\frac13.
\]
The second is less than
\[
\frac2{75}+\frac{49}{17280}
<\frac2{75}+\frac1{300}=\frac3{100}<\frac1{32}.
\]
There is no fitted threshold or numerical parameter search.

Define only an **internal integration boundary**,
\[
\Xi_m=\frac m{L^2}.
\tag{18}
\]
It lies strictly inside \(|\xi|\le\pi m/L\). It changes neither the carrier, the source, \(Q\), nor the original variation integral. From (6) and (17),
\[
|\rho'(\xi)|
\le2|Z(\xi)||\Psi(\xi)|
\le\frac{L^2E}{2\sqrt6\,m}
\quad (|\xi|\le\pi m/L).
\tag{19}
\]
Integrating only over \([-\Xi_m,\Xi_m]\) proves the new contribution bounds
\[
\boxed{
\mathcal V_c:=\int_{|\xi|\le\Xi_m}|\rho'(\xi)|d\xi
\le\frac E{\sqrt6},\qquad
\int_{|\xi|\le\Xi_m}\rho(\xi)d\xi\le\frac{2E}{3L}.
}
\tag{20}
\]
Both are uniform over the full stated selected family \(L>120\). They do not bound the complementary frequencies.

## 4. First unpaid comparison and exact budget after the new bound

**[COFINAL_FAMILY | PAPER]** Set
\[
\mathcal V_h=\int_{|\xi|>\Xi_m}|\rho'(\xi)|d\xi.
\]
The split is exact, and (8) identifies its unpaid part as
\[
\boxed{
\mathcal V_h=
\lim_{N\to\infty}\frac1{\pi L}
\int_{|\xi|>m/L^2}
\left|\operatorname{Im}\sum_{|n|,|q|\le N}
 c_nc_q(-1)^{n-q}
 [J_1(\omega_n-\xi,b)-aJ_0(\omega_n-\xi,b)]
 \overline{J_0(\omega_q-\xi,b)}\right|d\xi.
}
\tag{21}
\]
All coefficients are still exactly (3) and (5). The precise comparison that would settle SV is
\[
\boxed{
\mathcal V_h\le
\frac{31}{2}E+\frac12E_O-\frac12D_d-\mathcal V_c.
}
\tag{22}
\]
The paid estimate does not set \(\mathcal V_c\) to zero. It gives only
\[
\boxed{
16E-M-\mathcal V_h-\frac E{\sqrt6}
\le\Delta^{\rm var}
\le16E-M-\mathcal V_h.
}
\tag{23}
\]
The remaining \(\mathcal V_h\) is not estimated at the requisite scale, so neither side of (23) is a certified sign for the full target.

For comparison, an upper proof of
\[
\mathcal V_h\le\frac{31}{2}E-M
=15E+\frac12E_O-\frac12D_d
\tag{24}
\]
would suffice and would leave the explicit margin
\[
\Delta^{\rm var}\ge\left(\frac12-\frac1{\sqrt6}\right)E>0.
\tag{25}
\]
Equation (24) is **not proved and not separately commissioned**. It records exactly how an upper estimate could spend (20). Its failure would not by itself refute SV.

The concrete limitation of the new proof is (11). It is valid in the displayed central region, but not at the remaining carrier frequencies. At \(\xi=\omega_j\), \(j>m\), the term \(n=j\) has \(\lambda_n=0\), with literal value \(J_0=b\); no separated-denominator estimate from (11) applies there. The centered moment's value zero at that one diagonal does not remove the other source pairs. Nothing in the source contract supplies their required cancellation.

Likewise, an upper bound on \(E\) cannot be used as a lower bound for the normalization. The high-coefficient energy in (4), fixed-cell convergence, or the old separate-source-block obstruction yields neither the upper comparison (22) nor a negative upper envelope for \(\Delta^{\rm var}\).

## 5. An exact source-lattice lower witness for variation

### 5.1. Half-line density at a carrier-grid frequency

**[FINITE_CELL | PAPER — new exact representation]** For every integer \(j\), define
\[
H_{m,j}=\sum_{\substack{n\in\mathbb Z\\n-j\ {m odd}}}
                  \frac{c_n}{n-j}.
\tag{26}
\]
This is an absolutely convergent single sum: \(c\in\ell^2\) and
\(\sum_{n-j\text{ odd}}|n-j|^{-2}<\infty\), so Cauchy–Schwarz applies to its absolute terms. It is not an assumption of absolute convergence of the original double pairing.

At the grid point \(\xi=\omega_j\), the exact half-window moments satisfy
\[
J_0(\omega_n-\omega_j,b)=
\begin{cases}
b,&n=j,\\
0,&n-j\ne0\text{ even},\\
iL/[\pi(n-j)],&n-j\text{ odd}.
\end{cases}
\tag{27}
\]
Substitution in the original half-line transform, with its phase \((-1)^n\), gives
\[
\Psi(\omega_j)=
-\frac{(-1)^j}{\sqrt{2\pi L}}
\left[b c_j-i\frac L\pi H_{m,j}\right].
\]
Therefore
\[
\boxed{
R_{m,j}:=\rho(\omega_j)
=\frac L{8\pi}c_j^2+\frac L{2\pi^3}H_{m,j}^2.
}
\tag{28}
\]
This is an exact value, not a fitted density or a termwise density bound. The first term is the literal grid diagonal. The square of \(H_{m,j}\) retains independent source indices and their cross terms.

In particular, for the grid points above the carrier, the low block remains explicitly
\[
H_{m,j}
=\varepsilon_m\sum_{\substack{|n|\le m\\n-j\ {m odd}}}\frac1{n-j}
+\sum_{\substack{|n|>m\\n-j\ {m odd}}}\frac{e_n}{n-j},
\qquad j>m.
\tag{29}
\]
Every high coefficient in this formula is the complete source integral (5). Neither the finite low sum nor the infinite high sum is deleted.

### 5.2. Exact normalization check at zero

**[COFINAL_FAMILY | PAPER]** Symmetry gives \(H_{m,0}=0\), while \(c_0=\varepsilon_m\). Hence
\[
\boxed{R_{m,0}=\rho(0)=\frac{B^2}{2\pi}.}
\tag{30}
\]
An independent direct check gives the same result: projection orthogonality and evenness imply \(\int_0^b f=0\), whereas \(\int_0^b d=B\). Thus \(\int_0^b k=-B\), and \(\Psi(0)=-B/\sqrt{2\pi}\).

Consequently the unavoidable zero-frequency variation baseline is small but nonzero:
\[
2\rho(0)=\frac{B^2}{\pi}\le\frac{E}{\pi^2m}.
\tag{31}
\]
For example, evenness of \(\rho\) and its zero limits at infinity give the exact positive-variation identity
\[
\mathcal V=2\rho(0)+4\int_0^\infty(\rho'(\xi))_+d\xi.
\tag{32}
\]
Here \(x_+=\max(x,0)\). Thus a zero signed integral of the derivative does not make its total variation zero. Equations (30)–(32) are source checks, not a counterexample to SV.

### 5.3. Fix one panel, without a frequency search

**[COFINAL_FAMILY | PAPER — explicit lower envelope for variation]** Let
\[
N_m=\lceil L\rceil,
\qquad j_0=0,\quad j_s=m+s\quad(1\le s\le N_m).
\tag{33}
\]
This is a fixed analytical rule. It is not a chosen set of observed extrema or a numerical grid search. The positive-frequency nodes \(\omega_{m+s}\) all lie outside the central interval paid in (20).

Define the finite density-excursion functional
\[
\boxed{
\mathcal W_m=
2\left[
 |R_{m,m+1}-R_{m,0}|
 +\sum_{s=1}^{N_m-1}|R_{m,m+s+1}-R_{m,m+s}|
 +R_{m,m+N_m}
\right].
}
\tag{34}
\]
Every \(R\) in (34) is given by the exact source formula (28)–(29). The final positive term pays the descent from the last node to zero at infinity; it is not an omitted frequency tail.

Because \(\rho\in W^{1,1}(\mathbb R)\) is even and tends to zero at both infinities, absolute continuity on each interval between these nodes yields
\[
\boxed{\mathcal V\ge\mathcal W_m.}
\tag{35}
\]
Indeed, each density difference is bounded by the integral of \(|\rho'|\) on its interval. The remaining positive-frequency tail has variation at least the last value. Doubling covers the negative half-axis exactly. The first interval starts at zero, so there is no missing lower boundary.

This produces a finite-sampling **upper envelope for the requested margin**:
\[
\boxed{
\Delta^{\rm var}\le
U_m^{\rm lattice}:=16E-M-\mathcal W_m.
}
\tag{36}
\]
No sign for \(U_m^{\rm lattice}\) is proved here. In particular, \(U_m^{\rm lattice}\ge0\) would not prove SV: a finite partition may miss variation between its nodes.

## 6. Exactly one narrower falsifiable PAPER lemma

### TEST_SOURCE_CORE_LATTICE_VARIATION_WITNESS

**[COFINAL_FAMILY | CONDITIONAL — proposed witness lemma, not proved]** On the unchanged selected family, seek an explicitly identified admitted cell with \(\log m>120\), or an explicitly proved unbounded selected sequence, for which the source formula (28)–(34) proves
\[
\boxed{
\mathcal W_m>16E-M,
\quad\text{equivalently}\quad U_m^{\rm lattice}<0.
}
\tag{LW}
\]
The cell must be tied to the same fixed \(P\) and \(m=J_P+j+2\); an arbitrarily chosen non-source coefficient sequence is not a witness. The panel (33), original \(E\), coefficient sequence (3), and threshold are fixed before this proposed test.

The **consumer** is the universal sufficient variation interface SV. The **discriminator** is the explicit scalar \(U_m^{\rm lattice}\) in (36). A rigorous upper bound
\[
U_m^{\rm lattice}\le-\gamma E,\qquad \gamma>0,
\]
at an admitted cell would immediately give
\[
\Delta^{\rm var}\le-\gamma E<0,
\]
and hence `SOURCE_VARIATION_INTERFACE_REFUTED`, with kill scope **THEOREM_SHAPE: SV ONLY**. Strict negativity proved directly, without a prefixed \(\gamma\), is also sufficient; an explicit positive margin must then be extracted from that proof.

This lemma is a smaller determining object for a **refutation**: finitely many exact density values, rather than the entire absolute derivative integral. It is deliberately incomplete as a detector. A failed witness search, a nonnegative panel margin, or an upper estimate too weak to decide its sign leaves SV open. None of those outcomes proves SV, refutes the original lag test, or establishes a square-core estimate.

Only (LW) is the next commissioned test. The high-pairing upper possibility (24) is retained as an alternative representation, not a second task. No arithmetic, frequency, or selected-index numerical search is authorized.

## 7. Route map, adversarial checks, and exact downstream scope

### Two representations, with different powers

| Representation | Discriminating power | PAPER cost and main risk |
|---|---|---|
| **Chosen: finite source-lattice variation witness**, (28)–(36). **[FINITE_CELL / COFINAL_FAMILY; CONDITIONAL]** | One certified negative upper margin rejects the universal SV interface. It does not reject the lag statement. | \(\lceil L\rceil\) carrier-adjacent density values plus zero, each with a complete source Cauchy sum. The remaining difficulty is a lower source comparison against actual \(E\); no source witness is presently supplied. |
| **Alternative: complementary-frequency paired variation**, (21)–(25). **[COFINAL_FAMILY; CONDITIONAL]** | A uniform upper estimate of the displayed strength proves SV with a positive margin, hence closes the original lag test after adjoining the audited bounded-index region. | One nonnegative paired integral outside a genuinely paid central interval. Near-carrier resonances and source interference remain; the central separated-denominator argument cannot cover them. |

**[COFINAL_FAMILY | PAPER — strongest attack]** The largest risk in the new upper estimate is silently deleting \(d\), or using its small norm with an unbounded window-length loss. Equations (14)–(16) instead keep the actual Dirichlet synthesis and prove its two central-frequency moments by cancellation. The result remains only a central-frequency result. The explicit resonance in Section 4 prevents its promotion to the full variation.

The largest risk in the lattice route is reversing (35). It is a **lower** bound on variation and therefore an **upper** bound on \(\Delta^{\rm var}\). It can certify a negative margin, not a positive one. The formula keeps both squares in (28), including the low block inside (29); dropping the Cauchy-square term or removing its source cross terms changes the density.

**[FINITE_CELL | PAPER — boundary inventory]** The split points \(z_0\) and \(b\) in (15) are included with their boundary terms. At \(z=0\), the original Dirichlet sum supplies the continuous value. Low-frequency carrier coincidences do not cause a singularity because the low block is estimated through its exact integral. For high coefficients in (11), the denominator is genuinely separated on the stated region. The central/complementary frequency split covers all of \(\mathbb R\) with no gap; its two endpoints have zero measure. In the lattice formula, \(n=j\) uses \(J_0=b\), nonzero even differences use zero, and odd differences use the exact value (27). The last density value in (34) explicitly accounts for the tail to infinity. The original half-line boundary at zero and original physical exterior in \(E\) are both retained.

No complex strip or contour deformation is used in this verdict. The exterior decay acts only at \(u\ge b\). All Fourier transforms concern the stated half-window functions, not the full-line density of \(k\). Homogeneity, source phase convention, evenness, carrier, selected indices, normalization and \(Q\) remain unchanged.

**[COFINAL_FAMILY | PAPER — downstream accounting]** The earlier fixed lag statement would follow from a proved SV on \(L>120\), together with the audited \(L\le120\) lag result. That implication is valid but its new antecedent is not proved. The arithmetic constants therefore remain conditional. The exact prior transfer retains
\[
U_m^{(2)}=V_m^{[0]}+R_{\varepsilon,m}
+U_{m,\mathrm{small}}^{(2)}+X_{m,\mathrm{large}}
-L_{m,\mathrm{large}}^{(2)}.
\tag{37}
\]
The low-frequency subtraction has its **minus sign**. Neither (20) nor a future refutation of SV changes this identity or activates \(C_0=128\), \(C_{\rm int}=134\), \(C_2=146\). A refutation of the original lag test still requires a permitted source pair \((m,t)\) with \(16E-(1+t)|A_m(t)|<0\). fileciteturn10file0L64-L71 fileciteturn10file0L89-L111 fileciteturn10file1L96-L106

## 8. Closeout and dependency epistemics

**[COFINAL_FAMILY | PAPER] What became smaller.** A uniform variation and mass budget now covers the actual source density on the entire proper spectral region \(|\xi|\le m/L^2\) for every selected \(L>120\). The unbounded cell quantifier in this proper-contribution estimate is closed. The remaining full-target comparison is explicitly (21)–(22), not a generic norm estimate.

**What did not close.** No source upper estimate closes that remaining comparison, and no negative source margin for (36) has been established. SV, the full fixed lag candidate, and the full square saving remain open. No requested theorem shape is killed.

**Prediction accounting.** The announced pre-check expectation was that a source-paid central spectral contribution could be bounded while leaving the high-frequency variation unresolved. The derivation (10)–(20) confirms precisely that limited expectation; it does not confirm SV. The subsequent lattice check was announced as a possible refutation detector. Equations (27)–(36), including the independent zero-frequency check, establish the detector's exact normalization and direction. They do not establish that it triggers on the source. No prediction that the source actually violates SV is scored as confirmed. The predecessor's SV candidate remains unresolved, and the earlier audited estimates are inputs, not newly scored discoveries.

The three structural connections used here are: Fourier–Plancherel converts projection orthogonality into moment bounds; the explicit endpoint Dirichlet kernel admits a nonstationary-phase estimate away from its carrier; and the dual characterization of variation gives finite density-excursion witnesses. The attempted vanishing check yields the nonzero source value (30), not zero variation. The potential family-deciding object is a negative lattice upper margin (36), or an upper bound on the complementary pairing, with their distinct directions preserved.

```yaml
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
DOWNSTREAM_CONSUMER: fixed_constant_16_source_core_continuous_lag_TEST_then_square_transfer
ACTUAL_CONSUMER_REQUIREMENT: source_lag_bound_on_all_original_selected_m_and_requested_lags
ORIGINAL_REQUESTED_OBJECT: SV_total_half_line_density_variation_budget_on_log_m_GT_120
ORIGINAL_OBJECT_IS: UNKNOWN
ORIGINAL_OBJECT_QUALIFICATION: sufficient_only_and_not_proved_necessary_for_the_fixed_source_lag_consumer
KNOWN_WEAKER_INTERFACES:
  - direct_lag_margin_on_predecessor_unpaid_domain_plus_audited_domain_proves_lag_TEST
  - bounds_at_prime_square_lags_can_suffice_for_arithmetic_core_without_all_real_lags
  - direct_signed_arithmetic_core_control_can_bypass_SV_and_the_lag_TEST
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
FIRST_UNPAID_SOURCE_COMPARISON: equation_21_against_exact_budget_22
MINIMAL_MISSING_ESTIMATE: source_upper_complementary_pairing_or_source_negative_lattice_upper_margin
NEW_CLOSED_QUANTIFIERS:
  - all_selected_log_m_GT_120_satisfy_central_variation_bound_E_OVER_SQRT6
  - all_selected_log_m_GT_120_satisfy_central_mass_bound_2E_OVER_3L
NEW_EXACT_REPRESENTATION: rho_at_every_Fourier_lattice_node_is_equation_28_with_full_source_Cauchy_sum
NEXT_TEST: TEST_SOURCE_CORE_LATTICE_VARIATION_WITNESS
NEXT_TEST_DOMAIN: same_P_and_selected_m_with_log_m_GT_120_and_fixed_panel_33
NEXT_TEST_DISCRIMINATOR: U_lattice_EQUALS_16E_MINUS_M_MINUS_W
NEXT_TEST_SUCCESS_IMPLICATION: negative_U_lattice_refutes_SV_only
NEXT_TEST_FAILURE_IMPLICATION: no_source_conclusion_from_a_nonnegative_or_unresolved_panel_margin
REOPEN_TRIGGER: source_proof_of_comparison_22_or_certified_negative_margin_36_or_direct_permitted_lag_violation
KILLED_REQUESTED_THEOREM_SHAPE: NONE
NOVELTY_AXIS: source_paid_central_moment_region_and_exact_finite_lattice_dual_variation_witness
MEMORY_ENTRY:
  target: source_core_half_line_density_variation
  status: OPEN
  cognitive_operator_used: DUALIZE
  invariant_learned: endpoint_low_block_requires_its_own_oscillatory_bound_and_lattice_pairing
  forbidden_future_move: extend_central_denominator_separation_through_carrier_resonances_or_reverse_lattice_lower_bound
  next_decisive_test: TEST_SOURCE_CORE_LATTICE_VARIATION_WITNESS
```

The exponent-one prime block, prime/square compensation, opposite-side correlation, integrated symbol deviation, transfer, actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor and RH remain open. The new derivations have not received independent review. No mathematical runtime, numerical search, Lean execution or repository write was performed. fileciteturn10file0L104-L112

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_CORE_LATTICE_VARIATION_WITNESS`, on PAPER, for the unchanged selected source with \(\log m>120\).** Use the fixed panel (33), the exact lattice density (28)–(29), and the original \(E\) and \(M=(E-E_O+D_d)/2\). Seek an explicitly identified admitted cell or a rigorously proved selected sequence with a negative upper envelope for \(U_m^{\rm lattice}=16E-M-\mathcal W_m\); retain all source coefficients, the finite low \(\varepsilon_m\) block, every \(r\ge1\), both squares in (28), independent source cross terms, the literal diagonal and the final tail-to-zero term in (34). Validate the sign and factors by (27), the independent zero-frequency identity (30), and the direction \(\Delta^{\rm var}\le U_m^{\rm lattice}\). A certified negative envelope rejects **SV only**. A nonnegative or unpaid lattice margin returns `OPEN_SOURCE_VARIATION` and does not certify SV; failure of this witness is not failure of the original lag test. Keep the central contribution (20) at its proper-region scope, the physical exterior in \(E\), and the negative low-frequency term in (37). No mathematical runtime, numerical cutoff or index search, Lean, repository write, new seed, source/carrier/\(Q\)/denominator replacement, route promotion, square-constant activation or RH claim.
