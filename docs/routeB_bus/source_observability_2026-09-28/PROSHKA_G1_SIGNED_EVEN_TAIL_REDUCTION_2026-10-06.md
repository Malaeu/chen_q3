# STATUS: TRY_GOAL058_SIGNED_EVEN_TAIL_PRIME_COMPARISON

```yaml
OPERATIVE_CLASS: TRY_GOAL058_SIGNED_EVEN_TAIL_PRIME_COMPARISON
REQUEST_ID: REQ-2026-10-06-ODD-SECULAR-SOURCE-SIGN
WORKING_BOUNDARY: CONTINUATION_ON_UNCHANGED_TWO_COLUMN_U
SOURCE_PIN: fc0b25a887feea95a4c7ee2191661184be0a53c7
ENTRY_BLOB: 960f1de9d00e9ca4b309a99fe98be48db40cdb31
PRESERVED: [FULL_CCM_K, N_EQUALS_m, L_EQUALS_LOG_m, ORIGINAL_SELECTED_SCHEDULE, G_AND_G_SECOND_DERIVATIVE_PLANE, COMPLEX_GRAM_METRIC, ALL_PRIME_POWERS]
OUTCOME: ORIGINAL_EVENTUAL_SIGN_UNRESOLVED
NEW_RESULTS:
  - EVEN_ARCHIMEDEAN_PERIODIZATION_WITH_NONNEGATIVE_IMAGE_TERMS
  - UNIFORM_TWO_COLUMN_OMITTED_MASS_LOWER_BOUND
  - FULL_SIGNED_FORM_EXTERIOR_REPLACEMENT_WITH_PAID_ERROR
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
EVIDENCE_STATUS: AUTHOR_DERIVATION_WITH_EXACT_CONTROLS_NOT_INDEPENDENTLY_REVIEWED
G1_CLOSED: false
G3_PROMOTION: false
RH_CLAIM: false
REPOSITORY_WRITES: false
LEAN_EXECUTED: false
SOURCE_NUMERICAL_SWEEP: false
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: AUXILIARY_SOURCE_ESTIMATES_ONLY
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
PREREGISTRATION_SCOPE: SYMBOLIC_CONTROLS_ONLY_NOT_ANALYTIC_DISCOVERY
PREREGISTRATION_SHA256: 6632e5ff3e717c6312a5ce0df39486db42189b1693dfef0d06e66ba814472458
```

## 0. Result and exact unchanged target

The eventual sign has not been proved or refuted in this pass. The new results pay two previously separate issues: the archimedean lower bound despite the physical window, and a lower bound for the omitted Fourier mass uniform in both coefficients. They do not assign a sign to the remaining prime correlations.

Fix the originally matched port P and retain

\[
m=m_j=\operatorname{preAnchorTailStart}(P)+j+2,\qquad N=m,\qquad
L=\log m,\quad a=L/2,\quad h=2\pi/L,\quad \Omega=hm.
\]

The literal orthonormal modes are
\[
\psi_{n,L}(t)=\frac{(-1)^n}{\sqrt L}e^{ihnt}\mathbf1_{[-a,a]}(t).
\]
For \(z=(z_0,z_2)\in\mathbb C^2\), put
\[
g_z=z_0G+z_2G'',\quad f_{m,z}=\sum_{|n|\le m}c_n(g_z)\psi_{n,L},
\quad c_n(g)=\frac{(-1)^n}{\sqrt L}\int_{-a}^a g(t)e^{-ihnt}\,dt.
\]
The exact retained Gram matrix is \(\mathsf G_m=V_m^*V_m\), where \(V_m=[c_m(G),c_m(G'')]\). The exact energy matrix is \(\mathsf H_m=V_m^*K_mV_m\), and
\[
U_m=\inf_{z\ne0}\frac{z^*\mathsf H_mz}{z^*\mathsf G_mz}
\]
on the eventual rank-two family. No Euclidean coefficient norm is substituted for this quotient.

Define the interior discarded part and physical exterior separately:
\[
r_{m,z}=\mathbf1_{[-a,a]}g_z-f_{m,z},\qquad
o_{m,z}=\mathbf1_{\mathbb R\setminus[-a,a]}g_z.
\]
Thus \(f_{m,z}-g_z=-(r_{m,z}+o_{m,z})\). The periodic representative of r has exactly the Fourier coefficients \(c_n(g_z)\), \(|n|>m\), and no retained coefficients. Its zero extension is NOT claimed to be a whole-line high-pass function.

Let
\[
E_m(z)=\|r_{m,z}\|_2^2=z^*\mathsf E_mz.
\]
The existing odd envelope \(\mathcal B_m\) and comparison \(\Gamma_m\) are used unchanged as inputs. The conclusion sought remains \(U_m>\mathcal B_m\), or the stated sufficient comparison \(\widetilde U_m>\mathcal B_m+\Gamma_m\), on an unbounded original sequence.

## 1. Exact positive image correction for the archimedean kernel

[ABSTRACT | PAPER]

Write
\[
J(s)=\frac{e^{-s/2}}{1-e^{-2s}}=\sum_{k=0}^{\infty}e^{-\beta_ks},
\qquad \beta_k=2k+\tfrac12,\quad s>0,
\]
and
\[
\mathfrak D(v)=\int_0^\infty J(s)\|v-\tau_sv\|_2^2\,ds.
\]
For an even complex-valued \(q\in H^1(\mathbb R/L\mathbb Z)\), let \(v=\mathbf1_{[-L/2,L/2]}q\) be its zero extension and \(d_n\) its orthonormal Fourier coefficients. Then
\[
\boxed{
\mathfrak D(v)=\sum_{n\in\mathbb Z}\mathfrak a(\omega_n)|d_n|^2
+\mathfrak I_L(v),\qquad \omega_n=2\pi n/L,
}\tag{1.1}
\]
where
\[
\mathfrak a(\omega)=2\sum_{k=0}^{\infty}
\frac{\omega^2}{\beta_k(\beta_k^2+\omega^2)},
\tag{1.2}
\]
\[
\boxed{
\mathfrak I_L(v)=2\sum_{k=0}^{\infty}
\frac{\left|\int_{-L/2}^{L/2}v(t)\cosh(\beta_kt)\,dt\right|^2}
{e^{\beta_kL}-1}\ge0.
}\tag{1.3}
\]

### Proof

First use a single exponential kernel \(e^{-\beta|s|}\). The periodized kernel is
\[
J_{\beta,L}(u)=\sum_{q\in\mathbb Z}e^{-\beta|u+qL|}.
\]
For \(|u|\le L\), its image terms are exactly
\[
J_{\beta,L}(u)-e^{-\beta|u|}
=\frac{2\cosh(\beta u)}{e^{\beta L}-1}.
\tag{1.4}
\]
Both zero-extension and periodic difference energies have the same norm term \(2\|v\|_2^2/\beta\). Their difference is the quadratic form of the image kernel. Expanding
\(\cosh(\beta(t-u))=\cosh(\beta t)\cosh(\beta u)-\sinh(\beta t)\sinh(\beta u)\)
gives, for general q,
\[
\mathfrak D_\beta(v)-\mathfrak D_{\beta,\mathrm{per}}(q)
=\frac{2}{e^{\beta L}-1}
\left(\left|\int v\cosh(\beta t)\right|^2-
\left|\int v\sinh(\beta t)\right|^2\right).
\tag{1.5}
\]
Evenness kills the second moment exactly, including for complex coefficients. Periodic Parseval gives
\[
\mathfrak D_{\beta,\mathrm{per}}(q)
=\sum_n\frac{2\omega_n^2}{\beta(\beta^2+\omega_n^2)}|d_n|^2.
\]
Sum over \(\beta=\beta_k\). The difference energies and, in the even case, the image terms are nonnegative. The image series converges: if \(B=\|q\|_\infty\), its k-th term is at most \(2B^2/\beta_k^2\). The periodic series converges for q in H1. Monotone convergence now proves (1.1). No whole-line Fourier support is asserted.

Each summand in (1.2) increases with \(|\omega|\). Also its defining summand, viewed as a function of beta, decreases. Comparing the beta-lattice of step 2 with an integral gives
\[
\boxed{
\mathfrak a(\omega)\ge\frac12\log(1+4\omega^2).
}\tag{1.6}
\]
Indeed one half of the integral of \(2\omega^2/[\beta(\beta^2+\omega^2)]\) from \(1/2\) to infinity equals the right side.

[COFINAL_FAMILY | PAPER]
For the actual even tail r, (1.1) therefore gives
\[
\boxed{
\mathfrak D(r_{m,z})\ge\mathfrak a(\Omega)E_m(z)+\mathfrak I_L(r_{m,z}).
}\tag{1.7}
\]
This is the legitimate replacement for the invalid claim that the whole-line error is high-pass.

For evaluation without large hyperbolic factors, (1.3) can equivalently be written
\[
\mathfrak I_L(r)=\frac2L\sum_{k\ge0}(1-e^{-\beta_kL})
\left|\sum_{|n|>m}\frac{c_n(g_z)}{\beta_k+i\omega_n}\right|^2.
\tag{1.8}
\]
It follows from the exact mode integral and evenness; the phase \((-1)^n\) has not been discarded.

## 2. Uniform source lower bound for the discarded mass

[COFINAL_FAMILY | PAPER]

There are constants \(c_E>0\) and \(m_E\), independent of z, such that for every integer \(m\ge m_E\),
\[
\boxed{
E_m(z)\ge c_E T_m^{9/2}\log T_m\,e^{-\pi T_m}
\left(|z_0|^2+T_m^4|z_2|^2\right),
\qquad T_m=\frac{2\pi(m+1)}L.
}\tag{2.1}
\]
Thus this lower bound is uniform in the mixed direction, including combinations chosen to cancel near the first omitted frequency. It is still an L2 lower bound, NOT Weil positivity.

### 2.1 Verified analytic input

Let Z be Hardy's real function. Bui--Hall, arXiv:2304.05178v1, equation (1), p.1, gives (specializing k=ell=0 and k=ell=1)
\[
\int_0^Y Z(t)^2dt=Y\log Y+O(Y),
\qquad
\int_0^Y Z'(t)^2dt=\frac1{12}Y\log^3Y+O(Y\log^2Y).
\tag{2.2}
\]
Only these unconditional leading terms are used. The displayed error in their formula is smaller than the errors written here. Values of Z on the critical line do not assert that all zeta zeros lie there.

The exact source Fourier identity gives
\[
|\widehat G(t)|=A_G(t)|Z(t)|,
\quad A_G(t)=2(t^2+1/4)\pi^{-1/4}|\Gamma(1/4+it/2)|.
\tag{2.3}
\]
Stirling's modulus asymptotic (DLMF 5.11.9) implies, for a fixed \(c_\gamma>0\),
\[
A_G(t)\ge c_\gamma t^{7/4}e^{-\pi t/4}\quad(t\ge t_0).
\tag{2.4}
\]
No derivative of an unspecified gamma remainder is taken.

### 2.2 Weighted moments, uniformly in the two coefficients

Put \(p(t)=z_0-z_2t^2\), \(T=T_m\), and
\[
J_T(z)=\int_1^2|z_0-z_2T^2x^2|^2dx.
\]
The elementary Gram matrix is
\[
\begin{pmatrix}1&-7/3\\-7/3&31/5\end{pmatrix},\quad
\det=34/45,\quad\operatorname{tr}=36/5.
\]
Consequently
\[
J_T(z)\ge\frac{17}{162}(|z_0|^2+T^4|z_2|^2).
\tag{2.5}
\]
Stieltjes integration by parts in (2.2), for the three weights 1, x2, x4, gives uniformly in z
\[
\|pZ\|_{L^2(T,2T)}^2
=T\log T\left(J_T(z)+O\left(\frac{|z_0|^2+T^4|z_2|^2}{\log T}\right)\right),
\tag{2.6}
\]
\[
\|pZ'\|_{L^2(T,2T)}^2
=\frac1{12}T\log^3T\left(J_T(z)+O\left(\frac{|z_0|^2+T^4|z_2|^2}{\log T}\right)\right).
\tag{2.7}
\]
Also \(\|p'Z\|_2/\|pZ\|_2=O(T^{-1})\), uniformly by (2.5). Hence
\[
\frac h\pi\frac{\|(pZ)'\|_2}{\|pZ\|_2}
\le \frac{2\log T}{L}\left(\frac1{\sqrt{12}}+o(1)\right)+O((LT)^{-1})
\longrightarrow\frac1{\sqrt3}<\frac23.
\tag{2.8}
\]
The coefficient-dependent zero of p does not invalidate the ratio: (2.5) bounds its integral norm uniformly from below.

### 2.3 Sampling is proved, not assumed

For F in H1 on an interval partitioned into cells of length h, let P be its piecewise-linear interpolant through all grid nodes, including both endpoints. On each cell F-P has zero endpoint values, and P' is the cell average of F'. Poincare and orthogonality of that average give
\[
\|F-P\|_2\le(h/\pi)\|F'\|_2.
\]
The integral of the square of a linear interpolant is at most h/2 times the sum of its endpoint squares. Therefore
\[
\sqrt{h\sum|F(t_n)|^2}\ge\|F\|_2-(h/\pi)\|F'\|_2.
\tag{2.9}
\]
The interval [T,2T] has the exact nodes \(hn\), \(m+1\le n\le2m+2\). Apply (2.8)--(2.9) and (2.6): eventually
\[
h\sum_{n=m+1}^{2m+2}|p(hn)Z(hn)|^2\ge\frac1{18}T\log T\,J_T(z).
\tag{2.10}
\]
All nodes are omitted coefficients of the original projection; the CCM matrix carrier is not enlarged.

From (2.3)--(2.4), on [T,2T],
\[
A_G(t)^2\ge c_\gamma^2T^{7/2}e^{-\pi T}.
\]
Because hL=2pi,
\[
\sum_{n=m+1}^{2m+2}\frac{|\widehat {g_z}(hn)|^2}{L}
\ge\frac{c_\gamma^2}{36\pi}T^{9/2}\log T\,e^{-\pi T}J_T(z).
\tag{2.11}
\]

### 2.4 Restore the actual window coefficients

Use the fixed derivative constants from the accepted source envelope,
\[
|G^{(k)}(t)|\le D_k^G e^{-(\pi/2)e^{2|t|}},\qquad 0\le k\le3,
\]
and put \(A_0=(D_0^G)^2+(D_2^G)^2\). Exterior integration gives
\[
\int_{|t|>a}|g_z(t)|dt\le\frac{2\sqrt{A_0}}{\pi m}e^{-\pi m/2}\|z\|_2.
\]
For the positive nodes in (2.11), the squared norm of the difference between actual and full-transform coefficients is at most
\[
\frac{8A_0}{\pi^2mL}e^{-\pi m}\|z\|_2^2.
\tag{2.12}
\]
Its ratio to (2.11)'s lower bound tends to zero uniformly because T=o(m). Eventually the error norm is at most half the full-sample norm. Combining (2.5), (2.11), and the triangle inequality proves (2.1), for example with
\[
c_E=\frac{17c_\gamma^2}{23328\pi}.
\tag{2.13}
\]
The threshold is eventual; it is not claimed to include the finite diagnostic cells.

## 3. Full exterior replacement: all prime powers and both poles are paid

[COFINAL_FAMILY | PAPER]

Use the exact full form in the question. Grouping its archimedean subtraction gives
\[
\mathcal W(v,v)=\mathfrak D(v)-c_{ar}\|v\|_2^2
+\mathcal P_{pole}(v,v)-\mathcal P_{pr}(v,v),
\tag{3.1}
\]
\[
c_{ar}=\gamma+\log(8\pi)+\pi/2,
\quad
\mathcal P_{pr}(v,v)=2\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}\operatorname{Re}C_v(\log q).
\]
The value of the constant follows by integrating the retained subtraction:
\(2\int_0^\infty(e^{s/2}-1)/(e^s-e^{-s})\,ds=\log2+\pi/2\).

For even complex v,
\[
\mathcal P_{pole}(v,v)=2\left|\int v(t)\cosh(t/2)dt\right|^2\ge0.
\tag{3.2}
\]
The source radical identity, including conjugation in the first slot, gives
\[
\mathcal W(f_{m,z},f_{m,z})=\mathcal W(r_{m,z}+o_{m,z},r_{m,z}+o_{m,z}).
\tag{3.3}
\]
For complex z this follows by sesquilinearity from the same identities for G,G''. It does not assume positivity of W.

Here is a completely explicit error budget for replacing r+o by r. Write
\[
C_0=\|G\|_2^2+\|G''\|_2^2,\quad C_1=\|G'\|_2^2+\|G'''\|_2^2,
\quad C_\infty=\|G\|_\infty^2+\|G''\|_\infty^2,
\]
\[
A_1=(D_1^G)^2+(D_3^G)^2.
\]
Define nonnegative scalar budgets
\[
e_o=\frac{A_0}{\pi m}e^{-\pi m},\qquad
w_o=\frac{A_0}{\pi}e^{-\pi m},
\]
\[
d_o=\left(\frac{2A_1}{\pi m}+8A_0+\frac{16A_0}{\pi m}\right)e^{-\pi m},
\tag{3.4}
\]
\[
d_r=2C_1+8C_\infty+2C_0\Omega^2
+8C_0\frac{2m+1}{L}+64C_0.
\tag{3.5}
\]
Then \(\|o\|_2^2\le e_o\|z\|^2\),
\(\|e^{|t|}o\|_2^2\le w_o\|z\|^2\),
\(\mathfrak D(o)\le d_o\|z\|^2\), and
\(\mathfrak D(r)\le d_r\|z\|^2\).

For the last two claims use J(s)<=2/s for 0<s<=1 and J(s)<=2e^-s/2 for s>=1. For a piecewise H1 function with the two window jumps, its translation norm on short shifts is bounded by the derivative contribution plus the two boundary strips. This gives the safe bound
\(\mathfrak D(v)\le\|v'\|_{2,\mathrm{pieces}}^2+4\|v\|_\infty^2+16\|v\|_2^2\)
for a window restriction. For the exterior the larger constants in (3.4) suffice. The finite synthesis has derivative norm at most Omega times its norm and supremum at most sqrt((2m+1)/L) times its norm. Applying these estimates to r=g_I-f proves (3.5). No derivative of a discontinuous zero extension is used as an H1 derivative.

For arbitrary v,w with weighted norms W_v,W_w,
\[
|\mathcal P_{pr}(v,w)|\le
2W_vW_w\sum_{q\ge2}\frac{\log q}{q^{3/2}}<10W_vW_w,
\]
\[
|\mathcal P_{pole}(v,w)|\le\frac83W_vW_w.
\tag{3.6}
\]
This bounds the entire infinite arithmetic sum, not only q<=m. For r,
\(W_r^2\le mC_0\|z\|^2\). The ordinary L2 cross term of r,o is zero by their disjoint supports. Cauchy--Schwarz in the positive D seminorm pays its cross term. Therefore
\[
\boxed{
|\mathcal W(f_{m,z},f_{m,z})-\mathcal W(r_{m,z},r_{m,z})|
\le R_m\|z\|_2^2,
}\tag{3.7}
\]
where
\[
\boxed{
R_m=2\sqrt{d_rd_o}+d_o+c_{ar}e_o
+26\sqrt{mC_0w_o}+13w_o
=O_G(m e^{-\pi m/2}).
}\tag{3.8}
\]
The coefficients 26 and 13 dominate the combined prime/pole cross and exterior-square constants 76/3 and 38/3. This estimate preserves the sign of the retained prime contribution while paying the genuinely tiny exterior.

## 4. The resulting explicit signed two-column form

[COFINAL_FAMILY | PAPER]

For r=r_m,z let
\[
\mathcal A_m(z)=
\sum_{|n|>m}(\mathfrak a(\omega_n)-c_{ar})|c_n(g_z)|^2
+\mathfrak I_L(r)
+2\left|\int_{-a}^a r(t)\cosh(t/2)dt\right|^2,
\tag{4.1}
\]
\[
\mathcal P_m(z)=2\sum_{2\le q\le m}\frac{\Lambda(q)}{\sqrt q}C_r(\log q).
\tag{4.2}
\]
For complex even r, C_r is real and even. Both formulas are Hermitian quadratic forms in z; write their real symmetric two-by-two matrices as mathsf A_m and mathsf P_m. The term q=m is zero exactly, even if m is a prime power, because C_r(L)=0.

Combining (1.1), (3.1)--(3.8) proves
\[
\boxed{
\|\mathsf H_m-(\mathsf A_m-\mathsf P_m)\|_{op}\le R_m.
}\tag{4.3}
\]
Also
\[
\boxed{
\mathsf A_m\succeq\kappa_m\mathsf E_m,
\qquad \kappa_m=\mathfrak a(\Omega)-c_{ar}
\ge\tfrac12\log(1+4\Omega^2)-c_{ar},
}\tag{4.4}
\]
\[
\boxed{
\mathsf E_m\succeq\mu_m\operatorname{diag}(1,T_m^4),
\qquad \mu_m=c_E T_m^{9/2}\log T_m e^{-\pi T_m}.
}\tag{4.5}
\]
In particular R_m/mu_m ->0. The exterior cannot occupy the leading signed budget even in the least favorable two-column direction.

The original metric is retained exactly:
\[
\boxed{
U_m\ge\inf_{z\ne0}
\frac{z^*(\mathsf A_m-\mathsf P_m)z-R_m\|z\|^2}
{z^*\mathsf G_mz}.
}\tag{4.6}
\]
The retained Gram tends to the positive continuous Gram of G,G''. Moreover mathsf G_m <= C_0 I by projection contraction. Using this upper bound for a positive numerator is an inequality, not a change of metric.

## 5. The exact arithmetic remainder has a boundary-Hankel representation

[ABSTRACT | PAPER, instantiated to the same source tails]

Set b_m,z(u)=r_m,z(a-u), 0<=u<=L. For 0<=s<=L,
\[
\boxed{
C_r(s)=\sum_{|n|>m}|c_n(g_z)|^2\cos(\omega_ns)
-\int_0^s\overline{b_{m,z}(u)}b_{m,z}(s-u)\,du.
}\tag{5.1}
\]
Indeed the periodic correlation is C_r(s)+C_r(L-s); evenness changes the latter into the displayed reflected integral. This is a Toeplitz/periodic diagonal minus a boundary Hankel term, not a whole-line multiplier assertion.

Consequently the remaining arithmetic form is exactly
\[
\boxed{
\mathcal P_m(z)=2\sum_{2\le q\le m}\frac{\Lambda(q)}{\sqrt q}
\left[
\sum_{|n|>m}|c_n(g_z)|^2\cos(\omega_n\log q)
-\int_0^{\log q}\overline{b_{m,z}(u)}b_{m,z}(\log q-u)\,du
\right].
}\tag{5.2}
\]
At q=m the two bracketed terms are both E_m(z), so they cancel exactly. Dropping the reflected term corrupts the endpoint and changes the source.

No positivity of the reflected prime integral is asserted. As an exact control outside the theta-tail family, take L=log 4 and r(t)=cos(10pi t/L) on [-L/2,L/2]. At s=log 2 its reflected integral is -log(2)/2. This even, purely periodic-high-pass test disproves any universal positive sign for the prime Hankel term; it is not a counterexample for U_m.

A modest additional paid bound is available for any 2<=Q<=m:
\[
\left|2\sum_{q\le Q}\frac{\Lambda(q)}{\sqrt q}C_r(\log q)\right|
\le 4\sqrt Q\log Q\,E_m(z).
\tag{5.3}
\]
It uses |C_r|<=E and the elementary finite sum bound. Taking Q=floor(log Omega) pays all those growing small-prime powers by o(log Omega)E. The full comparison is not forced to discard their signs; (5.3) is optional, not a replacement for (5.2).

## 6. First still-missing inequality, and what it would imply

[COFINAL_FAMILY | CONDITIONAL]

The remaining actual sign is the signed arithmetic comparison between mathsf P_m and the now explicit mathsf A_m, with the original retained Gram. A directly sufficient, budget-complete condition on an unbounded original sequence is
\[
\boxed{
\mathsf A_m-\mathsf P_m\succeq
(\mathcal B_m+2\Gamma_m+\delta_m)\mathsf G_m+R_m I,
\qquad \delta_m>0.
}\tag{6.1}
\]
Then (4.3) gives U_m >= B_m+2Gamma_m+delta_m and the existing window comparison gives U_tilde_m > B_m+Gamma_m. The existing odd y_m is a negative witness for both shifted odd forms. This implication does not assert (6.1).

A simpler, stronger arithmetic target that would suffice is
\[
\boxed{
\mathcal P_m(z)\le(\kappa_m-1)E_m(z)
\quad\text{for every }z\in\mathbb C^2
}\tag{6.2}
\]
on an unbounded sequence. It allows a growing logarithmic prime budget; it does not demand each correlation be negative. Equations (4.4)--(4.6) would then give
\[
U_m\ge\frac{\mu_m-R_m}{C_0}\ge\frac{\mu_m}{2C_0}
\]
eventually on that sequence. This has fixed exponential scale e^(-2pi^2 m/log m) times a polynomial, so it dominates B_m and Gamma_m. A fixed 1 is not mandatory: a positive margin epsilon_m with epsilon_m mu_m dominating R_m and C_0(B_m+2Gamma_m) would work.

**Neither (6.1) nor (6.2) has been proved.** The positive image and pole terms and the additional diagonal dispersion may make (6.1) true even if the stronger (6.2) fails. Such a failure would not be a counterexample to U_m.

The first unpaid object is no longer a fictitious high-pass lower bound or a nonuniform scalar tail mass. It is precisely the two-column, source-specific, signed prime-correlation estimate (5.2) at the paid budget (6.1). The estimate 10||exp(|t|)e||^2 does not supply it; nor does the positive Laplace representation of J supply a sign for arithmetic atoms.

## 7. Literature/alias mapping and scope

The concrete alias is reflection positivity / the method of images for exponential kernels. Neeb--Olafsson, arXiv:1312.6161v2, Example 1.2(b), explicitly names exp(-lambda|t|) as a prototypical reflection-positive function; Example 1.2(c) gives the associated periodic exponential kernels. Mapping: their real-line coordinate is t; the reflection is t->-t; their positive exponential parameter is beta_k; the period is L. Formula (1.4) and the full energy identity are proved here rather than imported as an unverified source-specific theorem. Odd parity is the explicit failed control.

The second dictionary is a logarithmic Fourier multiplier with a boundary correction. It is not an assertion that the restricted logarithmic Laplacian equals the spectral periodic operator. Equation (1.1) computes their difference for this actual kernel, with its favorable even sign. Generic Gårding or eigenvalue estimates on a different domain are unnecessary for this partial step and are not imported for the primes.

The third dictionary is stable sampling from an averaged derivative bound. The constant 1/12 in (2.2), not merely a growth order, makes 2/sqrt(12)<1 on the actual grid. The entire two-dimensional weighted family is handled by the explicit Gram lower bound (2.5). No random model or RH is used.

Only formula (1) of Bui--Hall and the gamma modulus asymptotic are imported analytic estimates. Their displayed primary sources were checked through the browser; the Bui--Hall first PDF page was visually inspected. Direct PDF downloads in this runtime failed, so no byte-level PDF SHA-256 is claimed. The repository source blobs, their source definitions, and the accepted predecessor budgets were read through the GitHub connector. No general assertion of a completed local ask.sh/database search is made.

## 8. Controls, alternatives, and closeout

[ABSTRACT | PAPER plus symbolic arithmetic controls]

The preregistered symbolic controls were run, not source numerics:

* For q(t)=cos t on [-pi,pi] and a single exponent beta, the exact difference is
  2 beta^2(1-exp(-2pi beta))/(beta^2+1)^2 >0.
* For q(t)=sin t it is -2(1-exp(-2pi beta))/(beta^2+1)^2 <0. Deleting parity fails.
* The complex-even combination cos t+i cos 2t keeps conjugation in the first slot; the imaginary cross contributions of each real symmetric form cancel.
* The moment Gram determinant is exactly 34/45, and subtracting (17/162)I remains positive definite.
* The reflected prime-boundary control in Section 5 is exactly negative.

These controls support the algebraic detector, not the unknown source prime inequality. The script output was PASS. Predictions P1--P4 concern these controls only and were confirmed; no retrospective prediction credit is assigned to the new analytical derivation or to the unknown eventual sign.

Two continuation representations, with heuristic—not mathematical—cost estimates:

1. **Signed arithmetic correlations (5.2), retaining image/pole squares.** Kill-power 9/10, proof cost 7/10. The discriminator is the smallest generalized quadratic margin of (6.1), with a complete source error budget on an unbounded original sequence. Preserve the cancellation inside each bracket and between prime powers.
2. **Explicit zero sum, with off-line pairs retained.** Kill-power 9/10, proof cost 9/10. A contribution from verified real zeros is usable only with an independently bounded signed remainder from every other zero. Omitting off-line paired terms would assume the sign being sought. No such remainder bound was obtained here.

DEPENDENCY EPISTEMICS:
- DOWNSTREAM_CONSUMER: an odd witness below the unchanged U_m; only this sufficient candidate is under test.
- ACTUAL_REQUIREMENT: U_m>B_m on an unbounded original sequence, or the stated tilde comparison with Gamma paid.
- ORIGINAL_REQUESTED_OBJECT: positive full signed two-column lower comparison.
- ORIGINAL_OBJECT_IS: sufficient for the candidate's refutation, not asserted necessary for all G1 methods.
- KNOWN_WEAKER_INTERFACES: any direct odd Rayleigh witness below U_m; (6.1) is a paid sufficient form interface, (6.2) is stronger.
- FAILURE_TYPE: NO_DERIVATION of the arithmetic inequality, not a contradiction.
- EPISTEMIC_STATUS: RESEARCH_DEBT; ORIGINAL_SIGN_UNRESOLVED.
- NOVELTY_AXIS: a derived even-image correction and uniform two-column sampling lower bound; no literature-priority claim.
- KILL_SCOPE: NONE for the prescribed source candidate.
- REOPEN_TRIGGER: a checked source bound for (6.1), or a source counterargument to that comparison with its exact scope.

No new odd convolution construction, scalar Schur identity, finite matrix experiment, Lean source, or repository write was performed. No G1 or G3 promotion and no RH claim follows.

## CODEX DIRECTIVE

Check the even image identity (1.1) and the uniform weighted sampling lower bound (2.1), including the actual window coefficient error (2.12) and the full exterior budget (3.8). Then attack exactly the signed source matrix in (5.2) against the budget (6.1), keeping the positive image/pole terms if the stronger test (6.2) loses them. Do not rerun the odd construction or use a positive Fourier-mass lower bound as the full sign. Report the first failed inequality or a fully bounded signed comparison; finite tables do not occupy the unbounded-sequence quantifier.
