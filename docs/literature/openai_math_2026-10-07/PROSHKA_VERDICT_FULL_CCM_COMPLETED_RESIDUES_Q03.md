# STATUS: TRY_RH_SOURCE_ARITHMETIC
```yaml
OPERATIVE_CLASS: TRY_RH_SOURCE_ARITHMETIC
VERDICT_CODE: FULL_CCM_MOMENT_Q03_COMPLETED_ZERO_RESIDUES_SIGNED_RETURN_EXECUTED_TARGET_OPEN
REQUEST: PROSHKA_CCM_MOMENT_Q03.txt
REQUEST_BYTES: 309494
REQUEST_SHA256: 2b9fcc1bd90d0683698336e05597170b2c931b5b04fdd1ebb8bed73b8bfd0221
SOURCE_BASELINE: 9b51c09c
BOOTSTRAP_REPO: Malaeu/chen_q3
BOOTSTRAP_BRANCH: rh_clean
BOOTSTRAP_PATH: docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md
BOOTSTRAP_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
FRONT: FULL_CCM_COUPLED_MOMENT_DRIFT
SOURCE_OBJECT: CCM_LITERAL_FULL_MATRIX_N_EQUALS_M
SCHEDULE: "m integer; N=m; L=log(m); both consecutive original full matrices"
HONESTY_STATE: CHALLENGER_NOT_RH
ADJUDICATION: INCONCLUSIVE_FOR_REQUESTED_SIGNED_ARITHMETIC_GAIN
REQUESTED_SIGNED_DRIFT_ESTIMATE: NOT_PROVED
FULL_FLOOR_IMPROVEMENT: NONE
SP_STATUS: OPEN
RH_STATUS: OPEN
PX_RH_CLAIM: NOT_MADE
EXECUTED_CALCULATION: "functional-equation completion; all-zero residues; exact critical-pair/off-critical-quartet signed Gram return against the unchanged adaptive T"
NEW_QUANTITATIVE_OUTPUT: "Theorem Q03-R: full-credit residual enclosure with omitted-zero coefficient 2000*C_N*(m+1)^(-13/8)"
OUTPUT_SCOPE: COFINAL_FAMILY
OUTPUT_VERIFIER: CONDITIONAL
CONDITIONAL_INPUT: "ZF78 in the packet's reported zeta-only Comparator scope; classical zeta functional equation and zero count"
FIRST_UNPAID: "the joint old/new positive-and-negative residue energy difference in (23), with the effective full credit retained"
ZF78_STATUS: REPORTED_ZETA_COMPARATOR_ACCEPTED_NOT_RERUN_HERE
DIRICHLET_HECKE_SIEGEL_IMPORTS: NONE
REPO_EDITS: NONE
LEAN_RUN: NONE
ARB_INTERVAL_RUN: NONE
EVIDENCE_STATE: PAPER_DERIVED_PENDING_INDEPENDENT_AUDIT
PROGRESS_CLASS: REPRESENTATION_PROGRESS
CONSUMER_PROGRESS: NO_PROGRESS
ROUTE_SCORE: 2
COGNITIVE_OPERATOR: REPRESENTATION_SHIFT
FAILURE_TYPE: NO_DERIVATION
EPISTEMIC_STATUS: RESEARCH_DEBT
KILL_SCOPE: NONE_FOR_ACTUAL_CCM_OR_SP
INDEPENDENT_AUDIT_TARGET: "Theorem Q03-R, equation (20), from the literal source, including completion, every zero multiplicity, both grids, all contour returns, and the coefficient 2000*C_N"
```

## 1. Result and exact boundary

**The requested arithmetic drift gain is not obtained. There is no improved full-floor exponent and no SP conclusion.** I execute the suggested zero-residue attack, but first complete its test matrix using the functional equation. This removes the artificial Fourier-grid poles without deleting their values. The resulting residues admit an exact positive-minus-negative Gram decomposition. Every old/new coupling and the fixed-basis diagonal companion remains in its contraction with the actual adaptive weight.

The first unsupported step is a one-sided bound for the resulting **joint signed residue-energy increment**, displayed in (23). Positivity of the critical-zero contributions at each endpoint does not establish that bound: their two-grid difference need not be positive. The negative part of an off-critical quartet has a precise quadratic small-displacement bound, but no estimate of its adaptive correlation that improves the admitted power scale is obtained.

The new enclosure, **Theorem Q03-R**, is

\[
\boxed{
\left|\Xi_{p,m}-\Gamma_{p,m}
       -\mathscr D_{p,m}((m+1)^3)
       +\frac{5000}{m\log m}\operatorname{Tr}\mathsf T\right|
\le 2000C_N(m+1)^{-13/8}\operatorname{Tr}\mathsf T.
}\tag{R}
\]

Here \(\mathscr D\) is the completely specified finite signed residue sum in (19), not an unknown matrix or a replacement weight. The constant \(C_N\) is a fixed classical zero-counting constant defined in (2). The coefficient in (R) is summable on the original schedule. **This pays the omitted residues; it does not pay the retained residue sum.**

The authoritative attachment has the requested 309,494 bytes and SHA-256, and was read completely, including its nested source packet. The bootstrap was fetched anew through the GitHub connector with the blob recorded above. No repository edit, Lean run, Comparator rerun, or interval certification was performed. The attachment expressly retains Q2's accepted truncation theorem and excludes the already checked Schur/averaging identities as additional signed suppliers. Those are inputs, not new progress here. fileciteturn8file0L1-L10 fileciteturn8file0L140-L184

## 2. Inherited objects and the only analytic dependencies

**[FINITE_CELL | PAPER: source-locked definitions]** Put
\(M=m+1\), \(L=\log m\), \(L_+=\log M\), \(I_r=\{-r,\ldots,r\}\),
\(L_r=\log r\), \(d_r=2r+1\), and \(\omega_j^{(r)}=2\pi j/L_r\).
Keep precisely

\[
\begin{split}
H_t&=\widehat K_m+t(K_M-\widehat K_m),\\
\mathsf T&=\int_0^1\left[(H_t)_-^{p-1}
 +\operatorname{diag}((-H_{t,jj})_+^{p-1})\right]dt,\\
\Xi_{p,m}&=\operatorname{Tr}\mathsf T(\mathsf C_M-\widehat{\mathsf C}_m),\\
e_m&=\frac{5000}{mL},\qquad
\Gamma_{p,m}=\operatorname{Tr}\mathsf T(\Delta\mathsf B+e_mI),\\
c_{p,m}&=\frac L{64}\operatorname{Tr}(P_{\rm new}\mathsf T).
\end{split}\tag{1}
\]

The inherited credit ordering \(\Gamma_{p,m}\ge c_{p,m}\) is used only for \(\log m\ge256\), the audited Q1 domain. The definitions and the residual equalities themselves remain valid for all \(m\ge6\) in Theorem Q03-R.

A hat always means matrix zero-padding. \(\mathsf T_{oo}\) is the principal block of this **full** \(\mathsf T\), never the negative spectral functional of an isolated old matrix. Both credits in (1) have their original meanings. The new calculation does not evaluate \(\Gamma\) from an endpoint moment difference. These definitions and their scope are inherited from Q2(4)–(5). fileciteturn8file0L291-L316

**[COFINAL_FAMILY | CONDITIONAL: ZF78]** Write \(a_0=3/8\). The named zeta premise and the functional equation put every nontrivial zero \(\rho\), with multiplicity \(\mu_\rho\), in
\(|\Re\rho-1/2|\le a_0\). Retain the packet's reported zeta-only Comparator acceptance, including its stated trust boundary; no character-family assertion is imported. fileciteturn15file0L18-L39 fileciteturn15file0L54-L65

**[ABSTRACT | PAPER: classical analytic input]** Choose a fixed \(C_N\ge1\) such that

\[
N_*(Y):=\sum_{|\Im\rho|\le Y}\mu_\rho
       \le C_NY\log(Y+3)\qquad(Y\ge1).
\tag{2}
\]

The count includes both signs of the ordinate. Also use a fixed local-count constant \(C_\ell\ge1\) for
\(\sum_{|\Im\rho-u|\le1}\mu_\rho\le C_\ell\log(|u|+3)\), enlarging constants over compact ranges. These are consequences of the classical zero-counting estimate already used in the convention lock; they are not new conjectural inputs. The packet also supplies the local logarithmic-derivative argument. fileciteturn15file1L93-L97 fileciteturn15file1L122-L126

Fix \(0<\epsilon<1/8\), \(\sigma=a_0+\epsilon\), and the same \(A_\epsilon\) as Q2(9):
\(|\mathfrak a(x+iy)|\le A_\epsilon\log(|y|+3)\) for \(\sigma\le x\le3/2\). Q2's already paid error is denoted
\[
r_{\epsilon,m}=16M^{-3/2}+
 (10000L_++300A_\epsilon+20)M^{-5/2}.
\]
Its proof and the moment receiver are not repeated. fileciteturn8file0L395-L410 fileciteturn8file0L616-L643

The outside reference check is limited to the classical normalization of \(\xi\), its functional equation, and the digamma integral used below. These facts do not improve ZF78. NIST DLMF §25.4 gives
\(\xi(s)=\tfrac12s(s-1)\pi^{-s/2}\Gamma(s/2)\zeta(s)\) and
\(\xi(s)=\xi(1-s)\); §5.9 gives the needed digamma integral. citeturn440460view2turn655239view2

## 3. Complete the actual source before moving through zeros

### 3.1 The completed logarithmic derivative matches the literal background

**[ABSTRACT | PAPER]** Define
\[
\mathscr L(z)=\frac{\xi'}{\xi}(1/2+z),\qquad
 g(z)=\frac2{z+1/2}-\frac12\log\pi
                 +\frac12\psi(1/4+z/2).
\]
Logarithmic differentiation of the displayed normalization gives exactly

\[
\boxed{\mathscr L(z)=g(z)-\mathfrak a(z),
\qquad \mathscr L(-z)=-\mathscr L(z).}\tag{3}
\]

In particular the coefficient of the retained decaying resolvent in \(g\) is **2**, not 1. The poles and the signs in Q2's
\(\mathfrak a(z)=-\zeta'/\zeta(1/2+z)-1/(z-1/2)+1/(z+1/2)\)
are unchanged.

Let \(J(s)=e^{-s/2}/(1-e^{-2s})\) and
\(c_A=\gamma+\log(8\pi)+\pi/2\). The digamma difference identity gives, for \(\Re z>0\),

\[
\boxed{
 g(z)=-\frac{c_A}{2}+\frac2{z+1/2}
             +\int_0^\infty J(s)(1-e^{-zs})\,ds.
}\tag{4}
\]

For the constant, \(\psi(1/4)=-\gamma-3\log2-\pi/2\), obtained from digamma reflection and duplication (or its rational-argument formula). Thus \(\psi(1/4)-\log\pi=-c_A\). The integral follows by subtracting the two instances of DLMF(5.9.16) and changing variables by a factor 2. citeturn440460view0turn655239view2

Use the inherited transfer
\[
\mathsf S_r(z)=\frac1{L_r}\sum_{\pm} b_{r,\pm}(z)b_{r,\pm}(z)^{\mathsf T},
\qquad b_{r,\pm}(z)_j=(z\pm i\omega_j^{(r)})^{-1}.
\]
Q2's causal inverse-transform rule applied to (4) gives
\[
\frac1{2\pi i}\int_{\Re z=\sigma}e^{L_rz}g(z)\mathsf S_r(z)\,dz
=-c_AI+2\mathsf R_r+
 \int_0^\infty J(s)\bigl[2I-\mathbf1_{s\le L_r}Q_r(s)\bigr]ds
=\mathsf B_r.
\]
Consequently

\[
\boxed{
K_r=\frac1{2\pi i}\int_{\Re z=\sigma}
             e^{L_rz}\mathscr L(z)\mathsf S_r(z)\,dz.
}\tag{5}
\]

This is a normalization check needed for the new completion, not a repetition of the background lower-bound proof. The \(s>L_r\) archimedean tail, \(-c_AI\), and both retained decaying copies have all returned. A regularization of the \(s=0\) integral in (4) justifies the interchange: on a fixed right vertical line its cutoff versions are bounded by \(C(1+\log(|\Im z|+3))\), while \(\mathsf S_r(z)=O_r(|\Im z|^{-2})\). On the inverse side \(Q_r(0)-Q_r(s)=O_r(s)\). Dominated convergence then removes the regularization.

The other term in (3) is **the same** \(\mathfrak a\) with its original von Mangoldt Dirichlet coefficients, not a zero-based replacement prime process. Its already established sharp causal inverse is \(\mathsf C_r\). Every proper prime power and the exact endpoint value zero are therefore preserved in (5). No new inverse-transform truncation is being asserted here.

### 3.2 An entire, even finite-window transfer

**[FINITE_CELL | PAPER]** Introduce

\[
\boxed{
\mathsf V_r(z)=(\cosh(L_rz)-1)\mathsf S_r(z)
             =\sum_{\pm}v_{r,\pm}(z)v_{r,\pm}(z)^{\mathsf T},
\quad
v_{r,\pm}(z)_j=\sqrt{\frac2{L_r}}
                \frac{\sinh(L_rz/2)}{z\pm i\omega_j^{(r)}}.
}\tag{6}
\]

Every apparent pole is removable. With
\(\operatorname{sinhc}(w)=\sinh(w)/w\), continuously extended by 1 at zero,

\[
v_{r,\pm}(z)_j
=\sqrt{L_r/2}\,(-1)^j
  \operatorname{sinhc}(L_rz/2\pm i\pi j).
\tag{7}
\]

This form is entire and is the prescribed value at resonances. It has no small denominator convention. The matrix \(\mathsf V_r\) is even and satisfies
\(\mathsf V_r(\bar z)=\overline{\mathsf V_r(z)}\).

The independent literal-kernel check is

\[
\boxed{\mathsf V_r(z)=\int_0^{L_r}Q_r(s)\cosh(zs)\,ds.}\tag{8}
\]

For the diagonal, integration gives
\[
\frac{\cosh(L_rz)-1}{L_r}
 \left[(z+i\omega_j)^{-2}+(z-i\omega_j)^{-2}\right].
\]
For \(j\ne k\), integrating the literal sine difference first against \(e^{zs}\) gives
\((e^{L_rz}-1)\mathsf S_r(z)_{jk}\); averaging \(z\) and \(-z\) gives (8). Both calculations retain the integer identity \(e^{i\omega_j L_r}=1\). Analytic continuation gives the resonant values, including
\[
\mathsf V_r(0)=L_r e_0e_0^{\mathsf T},\qquad
\mathsf V_r(i\omega_j)=\frac{L_r}{2}
 (e_je_j^{\mathsf T}+e_{-j}e_{-j}^{\mathsf T})\quad(j\ne0).
\tag{9}
\]

**A grid pole was completed, not discarded.** If an actual zero occurs exactly at a grid ordinate, its residue is the nonzero matrix (9) times its multiplicity. There is no exceptional omitted zero or invented half-residue.

## 4. The finite contour, including its left side and both horizontal returns

### 4.1 Residue identity and orientation

**[FINITE_CELL | CONDITIONAL: ZF78 for the chosen vertical sides]** Take a height \(Y\) which is not a zero ordinate. Traverse the rectangle from \(\sigma-iY\) upward, then left, downward, and right. Put
\[
I_r(Y)=\frac1{2\pi i}\int_{\sigma-iY}^{\sigma+iY}
                    \mathscr L(z)\mathsf V_r(z)\,dz,
\]
and let \(\mathcal H_r(Y)\) be the sum of its **top and bottom** integrals, with these orientations and the same factor \(1/(2\pi i)\).

Oddness of \(\mathscr L\) and evenness of \(\mathsf V_r\) make the left *upward* integral equal to \(-I_r(Y)\). Hence the exact finite rectangle gives

\[
\boxed{
\sum_{|\Im\rho|<Y}\mu_\rho\mathsf V_r(\rho-1/2)
             =2I_r(Y)+\mathcal H_r(Y).
}\tag{10}
\]

This explicitly evaluates the left return. It is not set to zero: it supplies the second copy of the right integral. The only poles inside are the nontrivial zeros of \(\xi\), with residues \(\mu_\rho\mathsf V_r(\rho-1/2)\). The completed \(\xi\) has neither the zeta pole at 1 nor the trivial zeta zeros as zeros; those factors were accounted for in (3)–(5). The original growing-pole cancellation and the retained decaying terms have not been lost. The zero symmetries and the distinction between trivial and nontrivial zeros are the standard ones. citeturn944074search0

### 4.2 Uniform quantitative return bounds

**[COFINAL_FAMILY | CONDITIONAL: Q2(9)]** On the right vertical line, (4) gives
\(|g(\sigma+it)|\le20\log(|t|+3)\). One elementary bound uses
\(J(s)\le2/s\) on \((0,1]\), \(\int_1^\infty J(s)ds<2\), and
\(|1-e^{-zs}|\le\min(|z|s,2)\) for \(\Re z\ge0\).
Thus, with
\(D_v=A_\epsilon+20\),
\[
|\mathscr L(\sigma+it)|\le D_v\log(|t|+3).
\]

For \(|t|\ge2\max_j|\omega_j^{(r)}|\), the already checked channel bound gives
\[
\|\mathsf S_r(x+it)\|\le\frac{8d_r}{L_rt^2},\qquad
\|\mathsf V_r(x+it)\|\le\frac{16r^\sigma d_r}{L_rt^2}
                  \quad(|x|\le\sigma).
\]
It follows that the entire omitted pair of vertical tails costs at most
\[
\left\|\frac1{\pi i}\int_{\substack{\Re z=\sigma\\|\Im z|>Y}}
          \mathscr L(z)\mathsf V_r(z)\,dz\right\|
\le\frac{32D_vr^\sigma d_r}{\pi L_r}
                  \frac{\log(Y+3)+1}{Y}.
\tag{11}
\]

Here is a height selection that actually pays the horizontal sides. The local partial-fraction identity, uniformly for \(|x|\le\sigma\), is
\[
\mathscr L(x+it)=
 \sum_{|\Im\rho-t|\le1}\frac{\mu_\rho}{x+it-(\rho-1/2)}
           +O(\log(|t|+3)).
\]
It follows by subtracting the Hadamard logarithmic derivatives at a fixed right reference abscissa; the distant-zero differences are \(O((t-\Im\rho)^{-2})\), summable by the local count. Denote a fixed uniform remainder constant by \(C_R\).

For any \(X\ge343\), the number of ordinates in \([X-1,X+2]\), counted with multiplicity, is at most \(3C_\ell\log(X+5)\), after harmless enlargement of \(C_\ell\). Delete intervals of radius
\[
\eta_X=\frac1{8(1+3C_\ell\log(X+5))}
\]
around these ordinates from \([X,X+1]\). Their total length is less than \(1/4\), so a remaining \(Y\) exists. Its distance from every zero ordinate is at least \(\eta_X\). Conjugation gives the same separation at \(-Y\). The preceding local identity yields
\[
\max_{|x|\le\sigma}|\mathscr L(x\pm iY)|
 \le D_h\log^2(Y+3),\qquad
D_h=64(1+C_\ell)^2+C_R.
\]
The two horizontal lengths sum to \(4\sigma<2\), whence
\[
\boxed{
\|\mathcal H_r(Y)\|\le
 \frac{16D_hr^\sigma d_r}{\pi L_rY^2}\log^2(Y+3).
}\tag{12}
\]

There is no favorable-sign selection of residues: the height merely avoids poles, and every omitted zero is later bounded. At \(X=M^3\), both grids meet the bandwidth requirement, and (11)–(12) for the two endpoints together are bounded, for example, by
\[
600D_vM^{\sigma-2}
 +1100D_hL_+M^{\sigma-5}.
\tag{13}
\]
Both terms are summable in the original integer \(m\), since \(\sigma<1/2\). This shows explicitly that neither the left side nor a horizontal return conceals the missing central estimate.

### 4.3 Full residue return, with the normalization fixed

**[FINITE_CELL | CONDITIONAL: ZF78 for this contour proof]** On \(\Re z=\sigma\),
\[
2\mathsf V_r(z)=
 (e^{L_rz}+e^{-L_rz}-2)\mathsf S_r(z).
\]
The integrals of \(e^{-L_rz}\mathscr L(z)\mathsf S_r(z)\) and
\(\mathscr L(z)\mathsf S_r(z)\) vanish on closing to the right. There are no poles there, and on the closing arcs their norms are bounded by
\(O_r(\log R/R^2)\); the extra negative exponential is bounded by 1. Thus (5) gives
\(2I_r(\infty)=K_r\). Letting the selected heights tend to infinity in (10), using (11)–(12), proves

\[
\boxed{
K_r=\sum_{\rho}\mu_\rho\mathsf V_r(\rho-1/2).
}\tag{14}
\]

The series is absolutely convergent in finite-dimensional operator norm: for large \(|\Im\rho|\), its summand has norm at most
\(16r^{a_0}d_r/(L_r|\Im\rho|^2)\), and (2) makes this summable. Consequently finite spectral/path contraction with the actual \(\mathsf T\) needs no unproved infinite-contour interchange. This is the literal source explicit formula derived through (3)–(5), not an alternative definition of the production family.

## 5. Evaluate the signs of every residue class

### 5.1 Critical pairs and off-critical quartets

**[FINITE_CELL | PAPER]** For real \(\gamma\), the vector \(v_{r,\pm}(i\gamma)\) is real. A critical pair \(1/2\pm i\gamma\), \(\gamma>0\), therefore contributes
\[
2\mu_\rho\sum_{\pm}v_{r,\pm}(i\gamma)
                         v_{r,\pm}(i\gamma)^{\mathsf T}\succeq0.
\]

For a quartet represented by
\(w=\delta+i\gamma\), \(\delta>0\), \(\gamma>0\), write
\(u_{r,\pm}(w)=\Re v_{r,\pm}(w)\) and
\(q_{r,\pm}(w)=\Im v_{r,\pm}(w)\). All four multiplicities agree. Its exact contribution is

\[
\boxed{
4\mu_\rho\Re\mathsf V_r(w)
=4\mu_\rho\sum_{\pm}
   \left[u_{r,\pm}u_{r,\pm}^{\mathsf T}
        -q_{r,\pm}q_{r,\pm}^{\mathsf T}\right].
}\tag{15}
\]

No transpose was changed to an adjoint. The negative Gram matrix in (15) is part of the answer. There are no real nontrivial zeros to add as a separate class: for \(0<s<1\), the alternating eta series is positive (group consecutive pairs), while \(1-2^{1-s}<0\), so \(\zeta(s)<0\). The two classes above exhaust the nontrivial zeros using their functional-equation and conjugation symmetries.

### 5.2 A genuine signed, quantitative bound for a quartet

The exact physical-window formula for each channel is
\[
v_{r,\pm}(\delta+i\gamma)_j
=\frac{(-1)^j}{\sqrt{2L_r}}
 \int_{-L_r/2}^{L_r/2}
 e^{\delta x}e^{i(\gamma\pm\omega_j^{(r)})x}\,dx.
\]
Its real part is the Fourier coefficient of
\(\cosh(\delta x)e^{i\gamma x}\), and its imaginary part comes from
\(\sinh(\delta x)e^{i\gamma x}\). Those respective coefficients are real and purely imaginary by parity. Bessel's inequality, on the **full original finite mode set**, gives

\[
\begin{split}
\sum_{\pm}\|u_{r,\pm}\|^2
 &\le\frac{\sinh(\delta L_r)}{2\delta}+\frac{L_r}{2},\\
\sum_{\pm}\|q_{r,\pm}\|^2
 &\le\frac{\sinh(\delta L_r)}{2\delta}-\frac{L_r}{2}.
\end{split}\tag{16}
\]

For any of the actual positive weights \(\mathsf T_r\) used here, (15) consequently has negative contribution at most
\[
\begin{split}
4\mu_\rho\sum_{\pm}\|\mathsf T_r^{1/2}q_{r,\pm}\|^2
&\le 2\mu_\rho\left(\frac{\sinh(\delta L_r)}{\delta}-L_r\right)
                                  \operatorname{Tr}\mathsf T_r\\
&\le \frac{\mu_\rho\delta^2L_r^3}{3}
       \cosh^2(\delta L_r/2)\operatorname{Tr}\mathsf T_r.
\end{split}\tag{17}
\]
The last inequality uses
\(|\sinh(\delta x)|\le|\delta x|\cosh(\delta L_r/2)\)
and \(\int_{-L_r/2}^{L_r/2}x^2dx=L_r^3/12\).

This is a **quadratic transverse-displacement cost**: it vanishes quadratically as a zero approaches the critical line, for fixed window. It is not a claim that an off-critical zero exists. For fixed positive \(\delta\), however, its exponential scale is still \(e^{\delta L_r}=r^\delta\). It does not provide an improved full floor under \(\delta\le3/8\), and summing the near-band bound indiscriminately would lose the mode localization.

Every distant residue has the additional estimate
\[
\|\mathsf V_r(\delta+i\gamma)\|
\le\frac{16r^{|\delta|}d_r}{L_r\gamma^2}
       \quad(|\gamma|\ge2\max_j|\omega_j^{(r)}|).
\]
Thus no unestimated residue class has been silently discarded: near-band critical pairs and quartets retain their explicit signed Gram values with bounds (16)–(17), while all distant residues have this inverse-square bound. Neither estimate assigns a favorable sign to a quartet.

## 6. Contract with the full adaptive weight and restore every credit

### 6.1 Finite positive and negative residue matrices

For a common cutoff \(Y>0\), let \(\mathcal Z_0(Y)\) consist of the distinct critical zeros with positive ordinate at most \(Y\), and let \(\mathcal Z_+(Y)\) consist of the distinct zeros with \(\delta>0\), \(\gamma>0\), \(\gamma\le Y\). Include the full multiplicity of every zero. Define

\[
\begin{split}
\mathsf P_r^{Y}
={}&2\sum_{\mathcal Z_0(Y)}\mu_\rho\sum_{\pm}
 v_{r,\pm}(i\gamma)v_{r,\pm}(i\gamma)^{\mathsf T}\\
&+4\sum_{\mathcal Z_+(Y)}\mu_\rho\sum_{\pm}
 u_{r,\pm}(w)u_{r,\pm}(w)^{\mathsf T},\\
\mathsf N_r^{Y}
={}&4\sum_{\mathcal Z_+(Y)}\mu_\rho\sum_{\pm}
 q_{r,\pm}(w)q_{r,\pm}(w)^{\mathsf T}.
\end{split}\tag{18}
\]
Both matrices are positive semidefinite; their difference, not either matrix alone, is the finite residue approximation to \(K_r\).

Now execute the desired contraction as the explicit real number

\[
\boxed{
\mathscr D_{p,m}(Y)=
\operatorname{Tr}\mathsf T\left[
 \widehat{\mathsf P}_m^Y-\mathsf P_M^Y
 +\mathsf N_M^Y-\widehat{\mathsf N}_m^Y\right].
}\tag{19}
\]

For a critical pair, its summand is
\[
2\mu_\rho\sum_{\pm}\left[
 \|\mathsf T^{1/2}\widehat v_{m,\pm}(i\gamma)\|^2
 -\|\mathsf T^{1/2}v_{M,\pm}(i\gamma)\|^2\right].
\]
For a quartet, its summand is
\[
4\mu_\rho\sum_{\pm}\left[
 \|\mathsf T^{1/2}q_{M,\pm}\|^2
 -\|\mathsf T^{1/2}\widehat q_{m,\pm}\|^2
 -\|\mathsf T^{1/2}u_{M,\pm}\|^2
 +\|\mathsf T^{1/2}\widehat u_{m,\pm}\|^2\right].
\]
In particular, the old positive energy and old negative energy have not been removed. The actual new positive energy is still a credit. The signs are fixed before any estimates.

### 6.2 Theorem Q03-R: full-credit residual enclosure

**[COFINAL_FAMILY | CONDITIONAL: ZF78, with classical (2)]** For every \(m\ge6\), every fixed even \(p\ge4\), and the original adaptive \(\mathsf T\) in (1), set \(Y_m=M^3\) and \(q_m=2000C_NM^{-13/8}\). Then

\[
\boxed{
\begin{split}
\Xi_{p,m}-\Gamma_{p,m}
 &=\mathscr D_{p,m}(Y_m)-e_m\operatorname{Tr}\mathsf T+\mathcal E_{p,m},\\
|\mathcal E_{p,m}|&\le q_m\operatorname{Tr}\mathsf T,\qquad
\sum_{m\ge6}q_m<\infty.
\end{split}
}\tag{20}
\]

**Proof.** From (2), Stieltjes partial summation gives
\[
\sum_{|\Im\rho|>Y}\frac{\mu_\rho}{|\Im\rho|^2}
\le 2C_N\int_Y^\infty\frac{\log(t+3)}{t^2}dt
\le\frac{2C_N(\log(Y+3)+1)}Y.
\]
Therefore (14) and the distant-residue estimate give
\[
\left\|K_r-(\mathsf P_r^Y-\mathsf N_r^Y)\right\|
\le\frac{32C_Nr^{a_0}d_r}{L_r}
             \frac{\log(Y+3)+1}Y.
\]
For the two endpoints at \(Y=M^3\), use
\(d_m+d_M=4M\), \(L_+/L\le2\), and
\(\log(M^3+3)+1\le4L_+\), valid for \(M\ge7\). The sum of their error norms is at most
\[
1024C_NM^{a_0-2}<2000C_NM^{-13/8}=q_m.
\]
Contract the two errors with \(\mathsf T\) and \(\mathsf T_{oo}\), using
\(\operatorname{Tr}\mathsf T_{oo}\le\operatorname{Tr}\mathsf T\).
Finally insert the literal decomposition \(\Delta\mathsf C=\Delta\mathsf B-\Delta K\) and (18)–(19). Subtraction of \(\Gamma\) leaves exactly \(-e_m\operatorname{Tr}\mathsf T\), with the sign in (20). No endpoint moment difference has been inserted. For example,
\(\sum_{m\ge n}q_m\le3200C_Nn^{-5/8}\). This proves (20).

The cutoff \(M^3\) is only an **auxiliary zero-height cutoff**. It does not change \(N=m\), either physical window, the prime cutoff, or the original Q2 contour height. Formula (14) is absolutely convergent, so zeros at ordinate exactly \(Y_m\) are simply included with full multiplicity; there is no contour running through those zeros. The finite rectangles used to prove (14) had their own explicitly separated heights and returns (10)–(13).

### 6.3 Exact return to Q2's central object

Let \(\mathcal J=\mathcal J_{\sigma,M^2}(\mathsf T)\), still at Q2's original height. Its accepted truncation estimate and (20) imply the **two-sided** enclosure

\[
\boxed{
\left|\mathcal J-\Gamma_{p,m}
 -\mathscr D_{p,m}(Y_m)+e_m\operatorname{Tr}\mathsf T\right|
\le(q_m+r_{\epsilon,m})\operatorname{Tr}\mathsf T.
}\tag{21}
\]

For the smaller new-mode credit, one must retain

\[
\boxed{
\mathcal J-c_{p,m}
=\mathscr D_{p,m}(Y_m)
 +(\Gamma_{p,m}-c_{p,m})-e_m\operatorname{Tr}\mathsf T
 +\widetilde{\mathcal E}_{p,m},
\quad
|\widetilde{\mathcal E}_{p,m}|\le(q_m+r_{\epsilon,m})\operatorname{Tr}\mathsf T.
}\tag{22}
\]

On the inherited domain \(\log m\ge256\), the nonnegative \(\Gamma-c\) is not dropped in an upper bound. Equations (21)–(22) preserve the exact choice of consumer interface. Since \(q_m+r_{\epsilon,m}=o(e_m)\), the additional errors eventually consume at most half of the explicit \(e_m\) term. This observation pays errors only; it says nothing about \(\mathscr D\).

### 6.4 Both grids, every coupling, and the diagonal companion

For any one of the real channel vectors appearing in (19), write its new-endpoint value as \(x_M=(x_o,x_n)\), with two new coordinates, and its old-endpoint value as \(x_m\). Then the corresponding difference of squared weighted norms is exactly
\[
 x_o^{\mathsf T}\mathsf T_{oo}x_o-x_m^{\mathsf T}\mathsf T_{oo}x_m
 +2x_o^{\mathsf T}\mathsf T_{on}x_n+x_n^{\mathsf T}\mathsf T_{nn}x_n.
\]
Each occurrence in (19) has its displayed outer sign. This explicitly retains both new modes and both coupling columns. In particular \(x_o\ne x_m\) in general: their logarithmic windows differ.

There is a nonsingular formula for that old-grid motion. At fixed old label \(j\), use (7) with a variable \(\ell\in[L,L_+]\):
\[
\partial_\ell v_{j,\pm}(\ell,z)
=\frac{v_{j,\pm}(\ell,z)}{2\ell}
 +\sqrt{\ell/2}(-1)^j\frac z2
   \operatorname{sinhc}'(\ell z/2\pm i\pi j).
\]
Integrating this derivative gives the exact change of every old coordinate, including resonances. No old mode is frozen and no Hilbert-parameter padding identity is assumed.

Finally, for each real vector \(x\) above,
\[
\|\mathsf T^{1/2}x\|^2
=\int_0^1\left[
 \sum_\alpha(-\lambda_\alpha(t))_+^{p-1}(u_\alpha(t)^{\mathsf T}x)^2
 +\sum_j(-H_{t,jj})_+^{p-1}x_j^2\right]dt.
\]
These are the full eigenvectors of \(H_t\), with complete eigenspace projectors at degeneracies. The second sum is the **unchanged fixed-basis diagonal companion**. Its presence cannot be replaced by spectral commutation. This is an explicit evaluation of the already defined weight, not an assumption of independence between arithmetic and spectrum.

## 7. Attempted signed extraction and the first unsupported estimate

### 7.1 The exact unsupported budget

**[COFINAL_FAMILY | CONDITIONAL: OPEN, not proved]** The first missing estimate after the calculation is a bound on the actual signed sum in (19), sufficient, for arbitrarily large fixed even \(p\), to give

\[
\boxed{
\mathscr D_{p,m}(Y_m)
 -(e_m-q_m-r_{\epsilon,m})\operatorname{Tr}\mathsf T
\le\frac{Z_p(m)}{pm}+\frac{v_{p,m}}pZ_p(m),
\qquad v_{p,m}\ge0,\quad\sum_m v_{p,m}<\infty.
}\tag{23}
\]

This is a sufficient upper-envelope version of the original full-credit target. It is not asserted necessary, and a failure of this envelope would not refute the original target. The exact error version (21) is the weaker interface if its signed error is retained rather than bounded.

**No estimate of the left side of (23) at the stated scale has been derived.** Displaying it is the failure location, not a new supplier. For the smaller credit, add the unchanged \(\Gamma-c\) as in (22). The known moment receiver is not proved again or counted as an output.

### 7.2 Strongest attack: positive critical residues cannot be deleted from the drift

**[ABSTRACT | PAPER: actual grids, control weight only]** Fix \(\gamma>0\) and the real positive reflection-symmetric control weight \(e_0e_0^{\mathsf T}\). For a critical pair of multiplicity \(\mu\), its zero-mode endpoint energy is
\[
f_\gamma(\ell)=\frac{4\mu}{\gamma^2\ell}(1-\cos(\gamma\ell)),\qquad
f_\gamma'(\ell)=\frac{4\mu}{\gamma^2}
 \left[\frac{\gamma\sin(\gamma\ell)}\ell
       -\frac{1-\cos(\gamma\ell)}{\ell^2}\right].
\]
Whenever the whole interval \([L,L_+]\) lies in a phase interval on which
\(\sin(\gamma\ell)\le-1/2\),

\[
\boxed{
f_\gamma(L_+)-f_\gamma(L)
\le-\frac{2\mu}{\gamma}\log(L_+/L)<0.
}\tag{24}
\]

There are infinitely late original integer cells with this property: fixed positive-length intervals in logarithmic phase contain many consecutive integers after exponentiation. Thus even a critical pair gives a strict negative upper envelope for its endpoint matrix increment. Its contribution to (19) is then **positive**, not a disposable favorable term.

This rejects only the theorem shape “each critical-zero Gram matrix has a positive old-to-new increment.” It does not use, or produce, an actual CCM negative spectral weight. In particular it does not refute (23), its permitted \(1/m\) term, SP, or the CCM family. A single fixed critical zero can have a much smaller cost than the complete growing family. The precise repair is to keep the signed difference of its two energies in (19).

### 7.3 What (17) does and does not pay

For the off-critical class, the exact negative cost is the imaginary-channel energy in (15). Equation (17) bounds it and distinguishes \(\delta=0\) from small nonzero \(\delta\). But its \(r^\delta\) scale at fixed \(\delta>0\), the old positive return, and the correlation of all these channels with \(\mathsf T\) remain. Neither (2) nor ZF78 controls their required signed combination. No off-critical zero is assumed to exist, and no hypothetical quartet is promoted to an actual-source counterexample.

Taking absolute values in all retained residue energies would therefore not obtain (23). It would discard the very new positive and old negative credits that might be relevant. I have not used such a discarded-sign bound to claim a new floor. The original \(m^{3/8+\epsilon}\) magnitude result remains the admitted floor; the exponent \(-13/8\) in (20) is an **error coefficient**, not a lower-spectrum exponent.

## 8. Audit, discriminator, and bounded next choices

### One precise independent-audit target

**Audit Theorem Q03-R, equation (20), only as a source-residual enclosure.** The statement to accept or reject is
\[
\forall m\ge6:\quad
\left|\Xi_{p,m}-\Gamma_{p,m}-\mathscr D_{p,m}(M^3)
                   +\frac{5000}{m\log m}\operatorname{Tr}\mathsf T\right|
\le2000C_NM^{-13/8}\operatorname{Tr}\mathsf T,
\]
with \(C_N\) defined by (2), the literal full CCM source, all zero multiplicities, and the actual weight (1).

The proof check must validate the completed logarithmic-derivative normalization (3)–(5); the entire extension and grid-zero values (6)–(9); the factor 2 and the left/horizontal returns in (10)–(13); the full source return (14); the multiplicity factors 2 and 4 in (18); and the full-mode zero-tail norm leading to the coefficient 2000. In particular check the sign of \(-e_m\operatorname{Tr}\mathsf T\) and the fact that the old block is a compression of the full weight. Success accepts (20) only, not (23), a new full floor, SP, or RH. Report the first false equality, omitted term, or constant if the check fails.

### DISCRIMINATOR

**[FINITE_CELL | CONDITIONAL: proposed certification, not executed]** For a specified finite cell, use the full-credit margin
\[
F_{p,m}=\frac{Z_p(m)}{pm}
        -\mathscr D_{p,m}(Y_m)+e_m\operatorname{Tr}\mathsf T.
\]
To test the original source residual, widen an enclosure of this margin by
\(q_m\operatorname{Tr}\mathsf T\). To test Q2's finite-height integral, widen it by
\((q_m+r_{\epsilon,m})\operatorname{Tr}\mathsf T\).
For the smaller new-mode-credit test, also subtract the exact \(\Gamma-c\).
A nonnegative lower envelope certifies only the stated finite-cell, zero-extra-error inequality; a strictly negative upper envelope refutes only that inequality. A zero-straddling enclosure is inconclusive. Refinement must enclose the actual negative spectral functional and its path integral, rather than replace an apparently tiny weight by zero. No finite prefix establishes the cofinal summability required in (23).

### Two candidate re-representations, neither authorized as an escalated computation

**A. Common physical-window transport of the completed zero channels.** Use the integral below (15), rather than comparing two sinc grids coefficient by coefficient. Transport the old test function into the new physical interval and calculate the source-form defect of the exact Fourier return. A usable result would bound the combined critical and quartet old/new energy difference, not just the distance between two vectors. **Kill-power/cost:** high against unpaid endpoint leakage or an invalid unitary identification; medium analytic setup, high full source-form return cost. The first discriminator is the explicit boundary/return operator on a mode reaching the new edge. No claim that this operator is negligible is supplied.

**B. Relative signed Gram-factor inequality, not scalar spectral averaging.** Retain the actual feature maps in (18) and seek one simultaneous relative-form estimate for their positive and negative increments, contracted with the two components of the actual \(\mathsf T\). The target must retain the old positive energy and the new negative energy visible in (19); bounds on \(\mathsf N_r\) alone are stronger and may be too costly. **Kill-power/cost:** high against a purported source-aligned positive insertion that omits old spectral mass; low algebraic contract cost, high arithmetic estimate cost. The countercheck is (24), followed by the actual signed quartet channels, not an arbitrary replacement matrix.

The cross-domain checks in this calculation were explicit: functional-equation completion removes artificial poles; Fourier/Bessel analysis gives the signed quartet cost; and a positive-Gram monotonicity test fails on the exact integer schedule. None supplies a vanishing identity for (23). Another contour deformation with an unpaid retained residue sum would be another non-gain, not the next supplier.

## 9. Claim ledger and closeout

| Claim | Scope | Verifier | Disposition |
|---|---|---|---|
| Q1 background bound | COFINAL_FAMILY | PAPER | Independently accepted in the packet, \(\log m\ge256\); not re-proved |
| Q2 truncation theorem | COFINAL_FAMILY | CONDITIONAL | Independently accepted under its named zeta bound; not re-proved |
| Exact full adaptive weight and both credits | FINITE_CELL | PAPER | Unchanged source inputs |
| Completed source normalization (3)–(5) | FINITE_CELL | CONDITIONAL | Derived using the Q2 contour premise; retains the literal background and full prime history |
| Entire transfer, direct kernel identity, and resonant values (6)–(9) | FINITE_CELL | PAPER | Derived; no discarded grid pole |
| Finite rectangle and all return estimates (10)–(13) | COFINAL_FAMILY | CONDITIONAL | Derived under the named zeta strip and classical local count |
| Full residue formula (14) | FINITE_CELL | CONDITIONAL | Derived with the named zeta strip; no discarded return |
| Critical/quartet algebra (15)–(18) | FINITE_CELL | PAPER | Derived for the displayed channels; signed, not a positive-Gram replacement |
| Quadratic off-critical negative-channel cost (17) | ABSTRACT | PAPER | Derived for every displayed finite grid; no off-critical zero asserted |
| Residual enclosure (20) | COFINAL_FAMILY | CONDITIONAL | New PAPER audit target; omitted-zero coefficient is summable |
| Return to original Q2 height and smaller credit (21)–(22) | COFINAL_FAMILY | CONDITIONAL | All fees and credits retained |
| Central adaptive signed budget (23) | COFINAL_FAMILY | CONDITIONAL | OPEN; no supplier obtained |
| Critical-residue increment need not be positive (24) | ABSTRACT | PAPER | Exact theorem-shape countercheck only; not actual adaptive T |
| Improved full floor / SP / RH | COFINAL_FAMILY | CONDITIONAL | Not established; no claim made |

**What became more explicit:** the full residual is a signed sum of actual critical-pair and off-critical-quartet channel energies. Artificial grid poles, collisions, multiplicities, both grids, the diagonal account, and the omitted-zero tail have explicit returns.

**What did not become smaller:** the required adaptive arithmetic correlation. Its allowed \(1/(pm)\) rate has not been proved, and no full-floor improvement has been derived. This is representation progress, with **NO_PROGRESS for the requested signed consumer**. A sharper name for (23) is not a closed quantifier.

**What was rejected:** only monotonicity of each individual critical-zero Gram increment on the original two-grid schedule. No CCM family, alternative companion class, or route is declared impossible.

**Do not repeat:** the endpoint moment substitution; a Schur dimension argument without the old spectral term; deleting the companion through commutation; changing a transpose square into a modulus square; or deleting a positive endpoint residue from a difference of endpoints. Do not interpret the summable exponent in (20) as a negative-bottom bound.

### Registered predictions and diagnostic outcomes

Before the checks, the registered tests were that functional-equation completion would remove the artificial grid poles while retaining their resonant values, and that critical-zero positivity might fail to survive the actual two-grid increment. The first is confirmed by (6)–(10); the second is confirmed by the strict upper envelope (24). No prediction of a successful central signed estimate was registered or substituted afterward.

Small local floating-point diagnostics, **not interval certificates**, compared (8) directly with the literal diagonal/off-diagonal kernel at zero, nonreal arguments, and grid resonances. The maximum discrepancy was below \(1.28\times10^{-15}\). The quartet real/imaginary decomposition disagreed by less than \(4.45\times10^{-16}\), and the explicit two-grid block expansion by less than \(5.57\times10^{-17}\). Planted transpose-to-adjoint and deleted-coupling faults were detected, with discrepancies about \(0.003514\) and \(0.003119\), respectively. Their positive weights were detector controls, not the actual adaptive weight and not CCM counterexamples. No zeros were numerically assumed off-critical and no finite-cell CCM sign was certified.

The prior registered Q1 background and Q2 truncation predictions now have the packet's independent PASS dispositions. Their acceptance does not transfer to (23). fileciteturn8file0L151-L169 fileciteturn8file0L982-L995

```yaml
DEPENDENCY_EPISTEMICS:
  DOWNSTREAM_CONSUMER: SUBPOLYNOMIAL_NEGATIVE_BOTTOM_SP_TO_RH
  ACTUAL_CONSUMER_REQUIREMENT: "for every eta>0, lambda_min(K_m)>=-C_eta*m^eta on every sufficiently late original cell"
  ORIGINAL_REQUESTED_OBJECT: "a source-specific signed estimate for Q2(23), or its weaker full-credit variant"
  ORIGINAL_OBJECT_IS: UNKNOWN
  NECESSITY_NOTE: "Neither this moment companion nor this one-step residue interface is asserted necessary for SP."
  KNOWN_WEAKER_INTERFACES:
    - "The exact-error full-credit form of (21) can suffice even if the upper envelope in (23) is too costly."
    - "An original-family high-moment exponent independent of arbitrarily large fixed even p reaches the inherited receiver."
    - "A direct every-eta floor on the same full K_m reaches the consumer without this contour or companion."
  FAILURE_TYPE: NO_DERIVATION
  EPISTEMIC_STATUS: RESEARCH_DEBT
  NOVELTY_AXIS: "pole-free functional-equation completion; exact signed quartet channel cost; full-residual finite zero-sum enclosure"
  REOPEN_TRIGGER: "a proved estimate of the full joint residue-energy increment, including the old positive return, or a genuinely weaker same-source floor supplier"
  MATHEMATICAL_IMPOSSIBILITY_EVIDENCE: NONE
AUXILIARY_THEOREM_SHAPE_FINDING:
  CLAIM_REJECTED: "every critical-zero Gram matrix has PSD actual two-grid increment"
  KILL_SCOPE: THEOREM_SHAPE
  KILL_EVIDENCE_KIND: EXACT_SCALAR_NEGATIVE_UPPER_ENVELOPE
  PINNED_EVIDENCE: "this artifact, equation (24), with the literal v of (6)-(7)"
  SCOPE: ABSTRACT
  VERIFIER: PAPER
  ACTUAL_ADAPTIVE_WEIGHT_COUNTEREXAMPLE: false
  REPAIR: "retain the exact signed old/new critical-energy difference in (19)"
MEMORY_ENTRY:
  iteration: FULL_CCM_MOMENT_Q03
  target: FULL_ADAPTIVE_SIGNED_ARITHMETIC_DRIFT
  status: OPEN
  failed_strategy: "extracting the central sign from functional-equation symmetry and endpoint Gram positivity alone"
  cognitive_operator_used: REPRESENTATION_SHIFT
  consumer_progress: NO_PROGRESS
  paid_term: "all omitted-zero residues with coefficient 2000*C_N*(m+1)^(-13/8)"
  smallest_unpaid_input: "the actual adaptive signed residue-energy increment in (23)"
  invariant_learned: "critical residues are positive at one window but their actual two-grid differences need not be; off-critical quartets retain a negative imaginary-channel Gram term"
  forbidden_future_move: "discarding old positive residue energy or promoting completion/truncation to a signed supplier"
  next_decisive_test: "independent source-normalization and full-residual audit of Theorem Q03-R"
```

**Final proposal:** submit Theorem Q03-R to the single PAPER audit below; do not enlarge a numerical scan or count another zero-sum identity as a signed supplier. The registered prediction for that not-yet-run independent audit is that (20) survives with its stated dependency and domain. Its highest-risk checks are the factor 2 in the completed source return and the sign of the full-credit subtraction. An adverse audit reopens this enclosure, not the original CCM family. The central signed estimate remains unpaid regardless of a successful enclosure audit.

## CODEX DIRECTIVE

Independently audit **Theorem Q03-R, equation (20)** from the literal full CCM source and the unchanged adaptive weight. Validate the entire completion, its resonant values, every zero multiplicity, the functional-equation left return and both horizontal bounds, the exact background normalization, all old/new channel couplings, and the coefficient \(2000C_NM^{-13/8}\). Return either this PAPER enclosure with precisely its named zeta dependency, or the first incorrect identity/constant and a corrected enclosure. Do not treat its acceptance as a proof of (23), rerun Lean, edit the repository, or make an SP/RH claim.
