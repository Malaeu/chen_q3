# STATUS: TRY_BOUNDARY_PAIRED_SOURCE_COMPARISON
```yaml
OPERATIVE_CLASS: TRY_BOUNDARY_PAIRED_SOURCE_COMPARISON
RESULT: PARTIAL_WITH_PRECISE_REMAINDER
REQUEST_ID: REQ-2026-10-30-BOUNDARY
BOUNDARY_ID: GOAL058_FIXED_JET_NO_ESCAPE_ON_LITERAL_CCM_BOTTOMS
REQUEST_BYTES: 6891
REQUEST_LINES: 108
REQUEST_FINAL_LF: true
REQUEST_SHA256: 50bfc8c63d663bae15b916936646eadf8379c9a78dedbf3d934d58db8bc727ba
REQUEST_GIT_BLOB_COMPUTED: 9795f0c7e668b06898f02e7a0c83d2db491731ed
REQUEST_HASH_CHECK: MATCH
SOURCE_BASE_COMMIT: b659c795f445effe157fdda2fa07256f1d430163
PROTOCOL_GIT_BLOB: e0127d491799f7764e4f50e1ae4ed4cfcaf73c13
CARRIER: ORIGINAL_EVEN_CCM_N_EQUALS_M_L_EQUALS_LOG_M
MAIN_SOURCE_RESULT: NONNEGATIVE_ESCAPING_QUASIMODES_WITH_EXACTLY_FLAT_ENDPOINTS
ADDITIONAL_SOURCE_RESULT: ANY_FIXED_FINITE_LINEAR_BOUNDARY_RECORD_CAN_BE_ANNIHILATED
EXACT_BOTTOM_DISCRIMINATOR: FLATNESS_PLUS_MINIMALITY_FORCES_POLYNOMIAL_EIGENSPACE_MULTIPLICITY
SOURCE_COMPARISON: EXACT_POLE_MAIN_TERM_CANCELLATION_AND_RECIPROCAL_CUTOFF_DISCREPANCY
ESCAPE_TO_STRICT_SOURCE_SIGN: NOT_PROVED
STRICT_COMPETITOR_FOR_ACTUAL_BOTTOM: NOT_OBTAINED
FIXED_DEGREE_TEST_COMPLETENESS: REFUTED_FOR_GENERAL_DISPLACEMENT_MATRICES
REFUTATION_SCOPE: THEOREM_SHAPE_NOT_LITERAL_CCM_NOESCAPE
PROGRESS_CLASS: PROOF_PROGRESS
PROGRESS_SCOPE: SOURCE_LEVEL_LIMITATION_AND_EXACT_ALGEBRA_NOT_RH_CLOSURE
COGNITIVE_OPERATOR: COUNTEREXAMPLE_HUNT
ROUTE_SCORE: 3
VERIFIER: PAPER
EXACT_SYMBOLIC_CONTROLS: EXECUTED_PASS
NEW_LITERAL_CCM_NUMERICAL_SCAN: false
ARB_INTERVAL_EXECUTED: false
LEAN_EXECUTED: false
REPOSITORY_WRITTEN: false
INDEPENDENT_REVIEW_OF_NEW_PROOFS: NOT_PERFORMED
T_PROVED: false
RH_PROVED: false
G1_G3_CLOSED: false
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## 0. Decision

**No strict competitor for an actual escaping bottom is proved in this batch.** In particular, the boundary identity is not promoted into a sign theorem, and a stronger sufficient property is not declared equivalent to T.

There is a new limitation **on the literal source**, not just on a synthetic matrix. For every fixed integer \(D\ge1\), I construct real, nonnegative, even, unit functions \(g_m\) in the original carrier such that
\[
 \|A_mg_m\|+\|P_{J_r}g_m\|=O_{D,r,B}(m^{-B})
 \quad\text{for every fixed }r,B,
\tag{0.1}
\]
and
\[
 g_m^{(k)}(-L/2)=g_m^{(k)}(L/2)=0
 \quad(0\le k<4D).
\tag{0.2}
\]
The derivatives are interior derivatives. These functions have **exactly zero boundary-multiplier drift for every polynomial multiplier of degree at most D**, before the trial residual is restored. In particular, the request's boundary determinant is exactly zero. This strengthens the accepted translated-theta control: it removes the possibility of detecting that control merely by taking a few more endpoint derivatives.

There is also a precise distinction between these trials and a genuine minimum. If a nonzero **exact bottom** has the flatness (0.2), all the vectors \(c,Xc,\ldots,X^Dc\) belong to its eigenspace; its multiplicity is at least \(D+1\). The constructed trials have no such eigenvector assertion. **Complete fixed-jet escape does not imply exact endpoint flatness, and no cofinal multiplicity bound is supplied.** This discriminator therefore does not close T.

A source-faithful comparison is developed in §6: subtract the continuous prime main term only **inside an exact identity**, retain its complete discrepancy, and pair the reciprocal cutoffs \(e^s\) and \(m e^{-s}\). This cancels the large growing pole term before any inequality. A concrete, independently checkable one-sided remainder budget is given in §7. **The step from escape of exact low-energy stationary vectors to a negative upper envelope for that budget remains unproved.** The regrouping alone is not arithmetic progress on that sign.

### 0.1 Source lock

The complete attached TXT was read as UTF-8 and hashed directly from its mounted bytes. The byte count, LF count and SHA-256 agree with the request. The Git blob above was independently computed from `blob <byte-count>\0<bytes>`; it was not supplied as an additional owner assertion.

The protocol was fetched through the GitHub connector from `rh_clean`. Mathematical reads were pinned to the specified source commit. The local VARIATIONAL attachment has SHA-256
`79b5f4869f75d0f14b056d9543914e05a57ab8101bfe30b1db63c09d77161f71`
and Git blob
`0e6d082247f1a943d3f52922fa9791d5e6aa635d`, matching the blob returned at that pin. Relevant portions were read locally in full. No source was read from a later mathematical HEAD.

### 0.2 What is accepted and what is not

The accepted inputs are the literal source form, theta radical identity, weighted theta decay, and the bounded PAPER results of VARIATIONAL cited by the request. The new arguments below re-pay their changed cutoff/projection steps. The request's finite m4/m8/m16 diagnostics are **RELAY / DIAGNOSTIC**, not interval or cofinal premises. ENTROPY and F/X are not reopened.

All results preserve \(N=m\), the identity Gram metric, the zero mode, both physical endpoints, all supported prime powers, and the full archimedean and pole terms. A smaller intermediate Fourier radius in §3 is used only to construct a trial **inside** the original carrier. The operator and its arithmetic cutoff remain unchanged.

## 1. Conventions and the exact question

Write
\[
 L=\log m,\quad b=L/2,\quad
 \psi_n(x)=L^{-1/2}e^{2\pi i n(x+b)/L}\mathbf1_{[-b,b]}(x).
\]
The real orthonormal even basis is
\[
 e_0=\psi_0,\qquad e_i=(\psi_i+\psi_{-i})/\sqrt2,
 \qquad d_0=1,\quad d_i=\sqrt2\ (i\ge1).
\]
Thus a real coefficient vector \(c\in\mathbb R^{m+1}\) synthesizes
\[
 f_c(x)=L^{-1/2}\sum_{i=0}^{m}d_i c_i
                 \cos\frac{2\pi i(x+b)}L,
 \qquad \|f_c\|_2=\|c\|_2.
\tag{1.1}
\]
Let \(A=A_m\) be the literal even CCM matrix. Set
\[
 x_i=i^2,\quad X=\operatorname{diag}(x_i),\quad
 F_i=i\beta_i,\quad v_i=d_i,\quad u_i=d_iF_i.
\]
The full source row is
\[
\begin{aligned}
\beta_i={}&\frac{\kappa i}{L^2+16\pi^2i^2}
 +\frac1\pi\int_0^L j(s)\sin(2\pi i s/L)\,ds\\
 &+\frac1\pi\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}
                         \sin(2\pi i\log n/L),
\end{aligned}
\quad
j(s)=\frac{e^{-s/2}}{1-e^{-2s}},\quad
\kappa=32L\sinh^2(L/4).
\tag{1.2}
\]
Here \(\beta_0=F_0=0\). For distinct indices,
\[
 A_{ij}=d_id_j\frac{F_i-F_j}{x_i-x_j},\qquad
 [X,A]=uv^T-vu^T.
\tag{1.3}
\]
The diagonal of A is the original diagonal. Formula (1.3) does not replace it.

The global form on the admissible mixed tests is
\[
\begin{aligned}
\mathfrak k(f,g)={}&-c_*\langle f,g\rangle
 +\int_0^\infty j(s)\bigl(2\langle f,g\rangle-Q_{f,g}(s)\bigr)\,ds\\
 &-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{f,g}(\log n)
 +\langle f,p\rangle\langle p,g\rangle
 -\langle f,q\rangle\langle q,g\rangle,
\end{aligned}
\tag{1.4}
\]
where the first slot is antilinear,
\(c_*=\gamma+\log(8\pi)+\pi/2\),
\(p=\sqrt2\cosh(x/2)\), \(q=\sqrt2\sinh(x/2)\), and Q is the sum of the two translated correlations. The theta input satisfies
\[
 h>0,\quad h(-x)=h(x),\quad
 \widehat h(z)=4\xi(1/2-iz),\quad
 \mathfrak k(h(\cdot-a),g)=0,
\tag{1.5}
\]
with every exponentially weighted derivative norm finite. These are the inherited source identities, not an assumption about zero location. [S1, §§1–3]

T remains the existence of persistent projection of selected unit bottoms onto one fixed finite theta jet on an unbounded original set of m. Complete fixed-jet escape is its stated negation. No assertion about the converse RH ⇒ T is used.

## 2. Audit of the resistance and boundary tests

### Lemma 1. Trial correction, exact minimum, and single-edge limitations

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For a real unit c, put \(\rho=c^TAc\), \(r=(A-\rho)c\), and \(w_{ij}=-A_{ij}c_ic_j\). For \(y_i=a_ic_i\),
\[
 y^T(A-\rho)y
 =\sum_{i<j}w_{ij}(a_i-a_j)^2
   +\sum_i a_i^2c_ir_i.
\tag{2.1}
\]
If \(\max_i|a_i|\le1\), the last term has modulus at most \(\|r\|\). The unrestricted bound is \(\max|a_i|^2\|r\|\).

**Proof.** Multiply the ith residual equation by \(a_i^2c_i\), sum, and subtract it from the quadratic form in y. Each off-diagonal pair contributes \(-A_{ij}c_ic_j(a_i-a_j)^2\). Cauchy–Schwarz bounds the remaining diagonal pairing. ∎

For an exact eigenvector the correction vanishes. If a negative edge has magnitude α and its endpoints lie in one positive component, the positive-network unit-voltage minimizer has energy \(1/R\). All other negative edges reduce the energy, so \(\alpha R>1\) yields a strict competitor. This is a sufficient implication with many negative edges; no one-edge iff theorem is being extended illicitly. Disconnected positive components are handled by component indicators. [P1, Theorem IV.7; the sufficient implication also follows directly from (2.1)]

The supplied two controls are exact. The triangle passes every cut but has fractional-voltage energy \(-1/4\) and normalized gain \(-3/5\). For the four-vertex path the positive resistance matrix for the two negative edges is
\[
 R_- =\begin{pmatrix}2&1\\1&2\end{pmatrix},\qquad
 \frac25 R_- =\begin{pmatrix}4/5&2/5\\2/5&4/5\end{pmatrix}.
\tag{2.2}
\]
The single-edge loads are \(4/5\), but the joint top load is \(6/5\). The stated voltage has energy \(-1/5\). Appendix A verifies these facts exactly.

This explains why a complete multi-edge response can be stronger. It does not supply an escape-derived inequality for the actual response matrix. When all nonzero coefficient coordinates and all amplitude directions are admitted, their positivity is the shifted PSD condition on that support; it is not new source information. Zero coefficients require separate directions and are not divided out.

### Lemma 2. The boundary formula is correct, but equality has an additional minimum-only consequence

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For an exact eigenpair \(Ac=\lambda c\), set
\[
 S_0=v^Tc,\quad S_F=u^Tc,\quad
 S_x=v^TXc,\quad S_{Fx}=u^TXc.
\]
Then
\[
 (A-\lambda)Xc=vS_F-uS_0,
\qquad
 (Xc)^T(A-\lambda)Xc=S_xS_F-S_0S_{Fx}.
\tag{2.3}
\]
For a trial the extra term is \(\sum_i x_i^2c_ir_i\), of modulus at most \(m^4\|r\|\).

**Proof.** Use \([A,X]=vu^T-uv^T\), then take the inner product with Xc. The trial version keeps Xr. ∎

Substitution of the cosine derivatives in (1.1) into (1.2) gives exactly the request's identities
\[
 S_0=\sqrt L f(-b),\qquad
 S_x=-\frac{L^2\sqrt L}{4\pi^2}f''(-b),
\]
\[
 S_F=P_1-\frac{L\sqrt L}{2\pi^2}B_1,
\qquad
 S_{Fx}=P_3+\frac{L^3\sqrt L}{8\pi^4}B_3.
\tag{2.4}
\]
Consequently
\[
 S_xS_F-S_0S_{Fx}
 =S_xP_1-S_0P_3+
 \frac{L^4}{8\pi^4}\bigl(f''(-b)B_1-f(-b)B_3\bigr).
\tag{2.5}
\]
All signs and factors agree. The sine derivatives vanish at both endpoints; the near-zero archimedean integrands are integrable, and the endpoint prime power has zero contribution. These are not derivatives of the zero extension.

If c is a bottom, \(A-\lambda\succeq0\). Equality in (2.3) then implies
\((A-\lambda)Xc=0\), by diagonalizing that PSD matrix. A stationary vector without bottomness has no such implication. This is a genuine use of minimality, but it is not yet a contradictory source comparison.

## 3. A literal-source control with exactly flat endpoints

### Lemma 3. Fixed-degree endpoint flatness can coexist with all polynomial quasimode accuracy and complete jet escape

**THIS STEP IS PROVED HERE.**

**[COFINAL_FAMILY | PAPER]** Fix an integer \(D\ge1\). There is one sequence of real even unit functions \(g_m\in V_m^E\), nonnegative on the physical window, for which (0.1) and (0.2) hold. The same sequence works for every fixed error exponent B. In addition,
\[
 v^TX^kc_m=0\quad(0\le k<2D),
\tag{3.1}
\]
where \(c_m\) is its even coefficient vector.

**Proof.** Put \(a_m=L/8\) and
\[
 r_m(x)=\frac{h(x-a_m)+h(x+a_m)}{\nu_m},\qquad
 \nu_m=\|h(\cdot-a_m)+h(\cdot+a_m)\|_2.
\]
Positivity gives \(\sqrt2\|h\|_2\le\nu_m\le2\|h\|_2\). These are unit even global radical vectors. Choose the same fixed even smooth cutoff χ as in VARIATIONAL: it equals one on \([-1/2,1/2]\), vanishes outside \((-3/4,3/4)\), and lies in \([0,1]\). Set \(z_m=\chi(x/b)r_m\).

The new ingredient is the nonnegative trigonometric factor
\[
 \phi_{D,m}(x)=\cos^{4D}(\pi x/L).
\tag{3.2}
\]
It has Fourier degree \(2D\), vanishes to order \(4D\) at both endpoints, and is bounded below by a positive constant depending only on D on the support of χ. Define
\[
 w_m(x)=\frac{z_m(x)}{\phi_{D,m}(x)}
\tag{3.3}
\]
on that support and extend it by zero. It is smooth, even and nonnegative. For each fixed integer p,
\[
 C_{D,p}:=\sup_{L\ge2}\|w_m^{(p)}\|_2<\infty.
\tag{3.4}
\]
Indeed, on \(|x|\le3L/8\) the reciprocal of the cosine factor has derivatives bounded by constants times \(L^{-k}\); the translated derivatives of h have fixed L² norms. Every endpoint jet of w vanishes.

For \(m\ge4D\), let \(M=m-2D\ge m/2\), and let P_M denote the Fourier projection on the **same window** onto modes \(|n|\le M\). Define
\[
 \eta_m=P_Mw_m-w_m,
 \qquad t_m=L^{-1/2}\sum_{|n|>M}|\langle\psi_n,w_m\rangle|.
\tag{3.5}
\]
This is the entire Fourier tail, not a numerical truncation. Parseval and Cauchy–Schwarz give, for every \(p\ge2\),
\[
 \|\eta_m\|_2\le C_{D,p}\left(\frac{L}{2\pi M}\right)^p,
 \quad
 \|\eta_m'\|_2\le C_{D,p}\left(\frac{L}{2\pi M}\right)^{p-1},
\tag{3.6}
\]
\[
 t_m\le\frac{C_{D,p}}{\sqrt L}
       \left(\frac{L}{2\pi}\right)^p
       \sqrt{\frac2{2p-1}}M^{1/2-p}.
\tag{3.7}
\]
Uniform convergence gives \(|\eta_m|\le t_m\). Thus
\[
 q_m=\phi_{D,m}P_Mw_m,\qquad
 \widetilde g_m=\phi_{D,m}(P_Mw_m+t_m)
\tag{3.8}
\]
belong to the original carrier \(|n|\le m\), and \(\widetilde g_m\ge0\). They are real and even. Both have the exact endpoint vanishing (0.2). The operator remains \(A_m\), not \(A_M\); in particular its prime cutoff is still m.

It is important not to reuse projection orthogonality incorrectly. The error
\(e_m=q_m-z_m=\phi_{D,m}\eta_m\) need not be perpendicular to \(V_m\). It does, however, have zero endpoint trace. Its zero extension belongs to H¹, with
\[
 \|e_m\|_2\le\|\eta_m\|_2,\qquad
 \|e_m'\|_2\le\|\eta_m'\|_2+C_D L^{-1}\|\eta_m\|_2.
\tag{3.9}
\]
For any unit window vector v, shifting the first argument yields
\[
 |2\langle e_m,v\rangle-Q_{e_m,v}(s)|
 \le2s\|e_m'\|_2.
\]
Since \(\int_0^\infty s j(s)ds<5\), the complete source mixed estimate is
\[
 |\mathfrak k(e_m,v)|\le
 [c_*+(2+4L)\sqrt m]\|e_m\|_2+10\|e_m'\|_2.
\tag{3.10}
\]
The extra \(c_*\|e_m\|\) is retained precisely because orthogonality is no longer available. The poles cost \(2\sqrt m\|e_m\|\), the supported primes at most \(4\sqrt m L\|e_m\|\), and the archimedean tail is included in its translation integral.

The exterior error \(t_m^{\rm out}=r_m-z_m\) starts at \(|x|\ge L/4\), hence at distance at least \(L/8\) from each translated center. Weighted theta decay gives, for any fixed \(q,t\ge0\),
\[
 \|e^{q|x|}\mathbf1_{|x|\ge L/4}h^{(j)}(x\pm a_m)\|_2
 \le m^{(q-t)/8}\|e^{(q+t)|y|}h^{(j)}(y)\|_2.
\tag{3.11}
\]
Use the explicit global tail envelope
\[
\begin{aligned}
 |\mathfrak k(t_m^{\rm out},v)|\le{}&c_*\|t_m^{\rm out}\|_2
 +10\|(t_m^{\rm out})'\|_2
 +2m^{1/4}\int e^{|x|/2}|t_m^{\rm out}(x)|dx\\
 &+2\sqrt m\left(\sum_{n\ge2}\frac{\log n}{n^{3/2}}\right)
                      \|e^{|x|}t_m^{\rm out}\|_2.
\end{aligned}
\tag{3.12}
\]
The last series is infinite and convergent. It includes every exterior prime power. Weighted L¹ follows from weighted L² with one additional weight. Equations (3.11)–(3.12) are smaller than any prescribed inverse power of m. Radicality then gives
\(\mathfrak k(q_m,v)=\mathfrak k(e_m-t_m^{\rm out},v)\).

For the positivity correction in (3.8), use the source bound
\[
 \|A_m\|\le M_m:=c_*+8+\tfrac34(2\pi m/L)^2+
                 3(2m+1)/L+(2+4L)\sqrt m.
\tag{3.13}
\]
It follows directly by bounding translation squares, both endpoint strips, the prime sum and both pole norms, as in the accepted VARIATIONAL Lemma 3. Therefore
\[
 \|A_m(t_m\phi_{D,m})\|_2\le M_m t_m\sqrt L,
\]
which is again superpolynomially small. All these conclusions hold for the same definition (3.5), with p chosen only in its proof of each error order.

Finally \(\|\widetilde g_m-r_m\|_2=O_B(m^{-B})\), so its norm tends to one. Normalize to obtain g_m. Translation of h makes every fixed theta-jet pairing superpolynomially small: for any fixed j and t,
\[
 |\langle h(\cdot\pm a_m),h^{(j)}\rangle|
 \le C_{j,t}e^{-ta_m}=C_{j,t}m^{-t/8}.
\]
The fixed jet Gram matrix is nonsingular, so these pairing bounds imply the projection bound. Endpoint flatness survives normalization. From (1.1),
\[
 f_c^{(2k)}(-b)=\frac{(-1)^k}{\sqrt L}
                (2\pi/L)^{2k}v^TX^kc,
\]
which proves (3.1). ∎

**Limits of this theorem.** It constructs source trials, not selected bottoms. It gives no sign for their Rayleigh value relative to the unknown minimum. It does not bound a shrinking spectral gap. Its constants depend on fixed D; no growing-order conclusion is smuggled in.

### Lemma 4. Every fixed-degree polynomial boundary test is exactly blind before the trial correction

**THIS STEP IS PROVED HERE.**

**[ABSTRACT | PAPER]** If \(v^TX^kc=0\) for \(0\le k<2D\), then for every real polynomial p of degree at most D,
\[
 -\sum_{i<j}A_{ij}c_ic_j\bigl(p(x_i)-p(x_j)\bigr)^2=0.
\tag{3.14}
\]
Thus the g_m of Lemma 3 make all these source drifts zero, including
\(S_xS_F-S_0S_{Fx}=0\). For their trial residual r,
\[
 (p(X)c)^T(A-\rho)p(X)c=\sum_i p(x_i)^2c_ir_i.
\tag{3.15}
\]
For polynomials bounded by one on the nodes, the absolute right side is at most \(\|r\|=O_B(m^{-B})\).

**Proof.** For monomials of degrees a,b at most D,
\[
 c^TX^a[A,X^b]c=
 \sum_{j=0}^{b-1}\Bigl[
 (v^TX^{a+j}c)(u^TX^{b-1-j}c)
 -(u^TX^{a+j}c)(v^TX^{b-1-j}c)\Bigr].
\]
Every v-moment has degree at most \(a+b-1\le2D-1\), so every summand vanishes. Bilinearity gives \(c^Tp(X)[A,p(X)]c=0\). Expanding this expression by symmetric pairs gives (3.14); Lemma 1 gives (3.15). ∎

A negative upper envelope for a promised positive drift margin η would have to overcome this exact zero: on these trials, the claimed quantity `gain - eta` is exactly `-eta<0`. This refutes only a supplier claimed for **all such escaping quasimodes**. A bottom-specific assertion may use the exact residual equation and is not refuted.

### Lemma 5. Exact minimality would force multiplicity, not merely a small boundary determinant

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** Suppose c is a nonzero exact bottom and has the v-moment flatness of Lemma 4. Then
\[
 \operatorname{span}\{c,Xc,\ldots,X^Dc\}
 \subseteq\ker(A-\lambda),
 \qquad\dim\ker(A-\lambda)\ge D+1.
\tag{3.16}
\]

**Proof.** Exact stationarity removes r in (3.15); PSD of \(A-\lambda\) turns each zero quadratic value into a zero vector equation. The moment conditions force c to have at least \(2D+1\) nonzero coordinates: otherwise the first as-many-as-support moment equations are an invertible Vandermonde system, forcing c=0. On at least D+1 distinct active nodes, the vectors \(X^kc\), \(0\le k\le D\), are linearly independent by polynomial interpolation. ∎

This is a genuine exact-bottom feature not supplied by the accepted quasimodes. It is **not** an RH proof: escape does not give the exact flatness hypothesis, and a cofinal multiplicity restriction has not been proved here. Replacing exact zeros by merely superpolynomially small numbers needs an independently paid spectral/conditioning estimate; the known accumulation of low levels makes that step nonautomatic.

## 4. The limitation is not specific to choosing endpoint derivatives

### Lemma 6. Any fixed finite linear boundary/shift record can be annihilated by source quasimodes

**THIS STEP IS PROVED HERE.**

**[COFINAL_FAMILY | PAPER]** Fix D and an integer r. For each m, let
\(\ell_{m,1},\ldots,\ell_{m,r}\) be any real linear functionals on the original even carrier, including functionals depending on the exact source. There exist real even unit \(z_m\in V_m^E\) with
\[
 \ell_{m,j}(z_m)=0\ (1\le j\le r),\qquad
 \|A_m z_m\|+\|P_{J_k}z_m\|=O_{D,r,k,B}(m^{-B})
\tag{4.1}
\]
for every fixed k,B. They may also be required to have (0.2). They are not asserted nonnegative or eigenvectors.

**Proof.** Choose r+1 distinct fixed numbers \(\gamma_j\in(1/16,1/8)\). Repeat Lemma 3 with centers \(a_{m,j}=\gamma_jL\). Every tail estimate remains uniform over this finite set. The resulting flat, nonnegative, unit packets \(g_{m,j}\) have Gram matrix
\(G_m=I+O_B(m^{-B})\): their positive and negative centers separate by a fixed positive multiple of L, and all cross correlations have every exponential decay bound. In particular \(G_m\succeq I/2\) eventually.

The r by r+1 matrix \((\ell_{m,i}(g_{m,j}))\) has a nonzero kernel. Choose a Euclidean unit vector \(a_m\) in that kernel and set
\[
 z_m=\frac{\sum_j a_{m,j}g_{m,j}}
             {\sqrt{a_m^TG_ma_m}}.
\]
The denominator is at least \(1/\sqrt2\). Exact nulling follows by linearity; the residual, flatness and fixed-jet estimates follow from the finite sum and that lower bound. No bound on the norms or conditioning of the functionals is required. ∎

For example one may set every entry of the request's record
\(f(-b),f''(-b),P_1,P_3,B_1,B_3\) to zero **exactly**, or any fixed extension of it. The B-functionals are well-defined because odd trigonometric derivatives vanish at the endpoints and remove the j-singularity.

This is the exact scope of the limitation: **no argument using only a fixed finite record, escape, and superpolynomial quasimode accuracy can force a nonzero margin from that record.** It does not show that exact selected bottoms realize the nulled record. It does not prohibit a growing-rank argument, a quantitative use of all eigen-equations, or a different same-carrier competitor.

## 5. An exact stationary negative control for every fixed polynomial degree

### Lemma 7. Displacement structure and exact stationarity do not make a finite polynomial hierarchy complete

**THIS STEP IS PROVED HERE.**

**[ABSTRACT | PAPER]** Fix \(D\ge1\). Take \(m=D+2\), nodes \(x_i=i^2\), the same even-basis weights \(d_0=1,d_i=\sqrt2\), and define
\[
 v=(d_i),\quad a=Xv,\quad u=X^2v,\qquad
 A=av^T+va^T.
\tag{5.1}
\]
This is a symmetric Loewner-displacement matrix with
\[
 F_i=x_i^2,\quad
 A_{ij}=d_id_j\frac{F_i-F_j}{x_i-x_j}\ (i\ne j),
 \qquad [X,A]=uv^T-vu^T.
\]
Let \(P(t)=\prod_{i=0}^{m}(t-x_i)\) and
\[
 c_i=\frac1{d_i P'(x_i)}.
\tag{5.2}
\]
Then
\[
 Ac=0,\qquad A p(X)c=0\quad(\deg p\le D),
\tag{5.3}
\]
but A has the explicit negative Rayleigh vector
\[
 y=(2\sqrt2,-1,0,\ldots,0)^T,
 \qquad \frac{y^TAy}{\|y\|^2}=-\frac49<0.
\tag{5.4}
\]
For \(D\ge2\), all four boundary moments \(S_0,S_x,S_F,S_{Fx}\) are zero as well.

**Proof.** Lagrange interpolation, by comparing the leading coefficient, gives
\[
 \sum_{i=0}^{m}\frac{x_i^k}{P'(x_i)}=0\quad(0\le k\le m-1=D+1).
\]
Thus both \(v^TX^kc\) and \(v^TX^{k+1}c\) vanish for \(k\le D\), which proves (5.3) from (5.1). The leading two-by-two block is
\(\left(\begin{smallmatrix}0&\sqrt2\\\sqrt2&4\end{smallmatrix}\right)\).
It gives \(y^TAy=-4\) and \(\|y\|^2=9\). The displacement identity follows by direct multiplication. The four moments are interpolation moments of orders 0,1,2,3. ∎

Normalize c if a unit stationary vector is desired. Every degree-at-most-D multiplier has exactly zero shifted energy, although a strict competitor exists. This is a **synthetic structured matrix, not the CCM arithmetic matrix**. It refutes completeness of that structural detector, not the desired source theorem. The source theorem of §3 and the exact-stationary plant here have different scopes and are not combined into a false literal counterexample.

The finite m16 excited-state diagnostics in the request are consistent with this warning, but they are not needed for the proof.

## 6. An actual source regrouping: pair the reciprocal prime cutoffs before estimating

The limitation above does not justify stopping at a new name for shifted PSD. The following calculation retains the arithmetic and changes the specific comparison one would have to prove. It does **not** prove its sign.

### Lemma 8. Exact pole/main-term cancellation for every same-carrier amplitude direction

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** For real c and a real amplitude vector a, define the sine polynomial
\[
 \mathcal W_{c,a}(s)=
 -\sum_{i<j}d_id_jc_ic_j\frac{(a_i-a_j)^2}{x_i-x_j}
       \bigl(i\sin(\omega_i s)-j\sin(\omega_j s)\bigr),
 \qquad \omega_i=2\pi i/L.
\tag{6.1}
\]
It satisfies
\(\mathcal W(L-s)=-\mathcal W(s)\),
\(\mathcal W'(L-s)=\mathcal W'(s)\), and
\(\mathcal W(0)=\mathcal W(b)=\mathcal W(L)=0\).

Define the exact, weighted prime discrepancy
\[
 \mathcal D_m(s)=
   \sum_{2\le n\le e^s}\frac{\Lambda(n)}{\sqrt n}
       -2(e^{s/2}-1),\qquad 0\le s\le L,
\tag{6.2}
\]
and its reciprocal-cutoff pairing
\[
 \mathcal R_m(s)=\mathcal D_m(s)+\mathcal D_m(L-s),
 \qquad 0\le s\le b.
\tag{6.3}
\]
Finally put
\[
 j_+(s)=j(s)-e^{-s/2}
       =\frac{e^{-5s/2}}{1-e^{-2s}}>0,
 \qquad k_L(s)=j_+(s)-j_+(L-s)>0\quad(0<s<b).
\tag{6.4}
\]
For the exact multiplier source form
\(\mathcal Q_m(c,a)=-\sum_{i<j}A_{ij}c_ic_j(a_i-a_j)^2\),
\[
 \boxed{
 \mathcal Q_m(c,a)=\frac1\pi\left[
    \int_0^b k_L(s)\mathcal W_{c,a}(s)\,ds
   -\int_0^b\mathcal R_m(s)\mathcal W_{c,a}'(s)\,ds\right].}
\tag{6.5}
\]
For an exact eigenpair, this equals \(y^T(A-\lambda)y\), \(y_i=a_ic_i\). For a trial, add exactly the residual correction (2.1).

**Proof.** First, periodicity at the integer frequencies gives
\[
 -\frac1\pi\int_0^L2\cosh(s/2)\sin(\omega_i s)\,ds
   =\frac{\kappa i}{L^2+16\pi^2i^2}.
\tag{6.6}
\]
For \(i=0\) both sides are zero. For \(i>0\), integrate the exponential-sine functions; \(\sin(\omega_iL)=0\), \(\cos(\omega_iL)=1\), and \(\cosh(L/2)-1=2\sinh^2(L/4)\) give (6.6).

Consequently the full β-row can be integrated against the source functional
\[
 (j(s)-2\cosh(s/2))\,ds+
    \sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}.
\]
Its j-singularity is interpreted against the sine polynomial, which is O(s). Substitution of (6.1) into (1.3) therefore gives
\[
 \pi\mathcal Q_m=
  \int_0^L(j(s)-2\cosh(s/2))\mathcal W(s)ds
  +\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\mathcal W(\log n).
\tag{6.7}
\]
Now **add and subtract**, rather than approximate, \(e^{s/2}ds\) in the prime measure. The growing pole density cancels identically, leaving
\[
 \pi\mathcal Q_m=\int_0^L j_+(s)\mathcal W(s)ds
                    +\int_{[0,L]}\mathcal W(s)\,d\mathcal D_m(s).
\]
Stieltjes integration by parts has no endpoint term because \(\mathcal W(0)=\mathcal W(L)=0\). Pair s and L−s using their stated symmetries. This gives (6.5). ∎

**What has and has not been discarded.** The diagonal and its archimedean constant disappear from the exact multiplier form only by the eigenrelation, or remain in the trial correction. All prime powers are retained in (6.2); no PNT estimate is inserted. The atom at n=m is present, with zero contribution. The positive even pole is fully accounted for by (6.6); the odd pole vanishes only by the actual parity. The new continuous reference is an exact algebraic splitting, not a new operator.

For \(a_i=x_i\), the coefficient identity is
\[
 \mathcal W_{c,X}(s)=
 S_x\sum_i d_i i c_i\sin(\omega_i s)
 -S_0\sum_i d_i i^3c_i\sin(\omega_i s).
\tag{6.8}
\]
Writing
\(W_f(s)=f''(-b)f'(s-b)-f(-b)f'''(s-b)\),
\[
 \mathcal W_{c,X}(s)=\frac{L^4}{8\pi^3}W_f(s).
\tag{6.9}
\]
Thus (6.5) exactly reproduces the request's boundary balance, with its large pole contribution already canceled against the continuous prime main term. It is also valid for **nonpolynomial, adaptive amplitude vectors**; this route is not required to remain with \(i^2\).

### Lemma 9. The arithmetic remainder has a finite, source-explicit one-sided enclosure

**THIS STEP IS PROVED HERE.**

**[FINITE_CELL | PAPER]** Partition \([0,b]\) at the source knots
\[
 \log n\in[0,b],\qquad L-\log n\in[0,b],\qquad
 2\le n\le m,\quad\Lambda(n)\ne0,
\tag{6.10}
\]
and optionally refine further. On each open interval between knots the two step sums are constant and
\[
 \mathcal R_m'(s)=e^{(L-s)/2}-e^{s/2}\ge0.
\tag{6.11}
\]
Therefore its infimum and supremum on that open interval are its one-sided endpoint limits. There are no missing interior extrema. Coincident knots are combined; the endpoints 0 and b and any square-root cutoff are included.

Let \(\underline R_I\le\mathcal R_m\le\overline R_I\) be independently validated bounds for each interval I. Put
\[
 V_I^+=\int_I(\mathcal W')_+ds,\qquad
 V_I^-=\int_I(\mathcal W')_-ds.
\]
Then
\[
 \int_0^b\mathcal R_m\mathcal W'\,ds
 \ge \mathcal B_m^{\rm low}(c,a):=
   \sum_I(\underline R_I V_I^+-\overline R_I V_I^-).
\tag{6.12}
\]
In particular,
\[
 \boxed{\mathcal Q_m(c,a)\le
  \frac{\mathcal A_m(c,a)-\mathcal B_m^{\rm low}(c,a)}\pi,\qquad
  \mathcal A_m(c,a)=\int_0^b k_L(s)\mathcal W_{c,a}(s)ds.}
\tag{6.13}
\]

**Proof.** Between knots differentiate the explicit exponentials in (6.2). For (6.12), multiply the lower endpoint bound by the positive part of \(\mathcal W'\), and the upper bound by its negative part. Sum the resulting integrals. ∎

This is a proper one-sided source estimate, not an equality renamed as a margin. A simple, weaker version is
\[
 \mathcal Q_m(c,a)\le\frac1\pi\left[
 \mathcal A_m(c,a)+\sum_I D_I\int_I|\mathcal W'|ds\right],
 \quad D_I=\max(|\underline R_I|,|\overline R_I|).
\tag{6.14}
\]
It may be too lossy. It is **not** made mandatory.

For completeness the reference term has an explicit convergent series. If
\(\mathcal W(s)=\sum_{i=1}^m t_i\sin(\omega_i s)\), then
\[
 \mathcal A_m=
 \sum_{i=1}^m t_i\sum_{\ell\ge0}
  \frac{\omega_i(1-e^{-(2\ell+5/2)L})}
       {(2\ell+5/2)^2+\omega_i^2}.
\tag{6.15}
\]
After terms \(0\le\ell<R\), \(R\ge1\), a valid absolute tail budget is
\[
 \frac{\sum_i|t_i|\omega_i}{4R+1}.
\tag{6.16}
\]
Indeed the decreasing tail sum of \((2\ell+5/2)^{-2}\) is bounded by its integral from R−1 to infinity. The exchange with the finite sine polynomial is justified by \(|\mathcal W(s)|=O(s)\) at zero. The variation integrals in (6.12) concern a finite cosine polynomial. They can be enclosed by splitting at certified zeros of that polynomial, or more coarsely by its coefficient bound. None of these computations has been claimed executed on the actual eigenprofiles in this batch.

## 7. The proof attempt, its first unpaid comparison, and the exact limitation

### 7.1 Attempted chain

Assume a sequence of exact selected bottoms completely escapes the fixed theta jets. Use the actual low-energy eigen-equation and choose a same-carrier amplitude direction a. Equations (6.5) and (6.13) now identify a potential source mechanism:

* the deterministic pole-canceled reference integral \(\mathcal A_m\) supplies a negative contribution;
* the reciprocal-cutoff arithmetic discrepancy is paid one-sidedly by \(\mathcal B_m^{\rm low}\);
* their separation gives a strict upper envelope for the competitor's shifted energy.

**The first unproved source step is**
\[
 \boxed{
 \text{On an escaping exact-bottom sequence, construct a nonzero amplitude rule }a_m
 \text{ for which independently justified bounds give }
 \mathcal A_m^{\rm upper}(c_m,a_m)-
       \mathcal B_m^{\rm low}(c_m,a_m)<0
 \text{ on at least one sufficiently late original cell.}}
\tag{7.1}
\]
The reference upper bound must include (6.16) if that series is truncated, and the arithmetic lower bound must include input-vector, node and variation errors if intervals are used. No uniform positive constant is requested.

**I have not proved (7.1).** In particular, positivity of \(k_L\) does not fix the sign of \(\mathcal W\); complete fixed-jet escape does not fix that sign or the sign of its pairing with \(\mathcal R_m\). The source controls of §§3–4 make \(\mathcal W\) identically zero for every fixed-degree polynomial direction. On that class neither a main-term margin nor a relative remainder margin is available. Merely making an absolute tail bound smaller would not repair the missing sign.

There is no logical passage in this verdict from “the boundary data are small” to “the signed prime correlation is unfavorable.” Such a passage is precisely what must be proved using the exact stationary equation beyond the quasimode class. The request's warning about antiphase penalties is respected: all these quadratic quantities are invariant under \(f\mapsto-f\).

### 7.2 Why (7.1) is not claimed equivalent to T or to shifted PSD

T concerns a fixed compact observable of actual bottoms. It says nothing about a choice of amplitude, a reference main-term sign, or a particular interval majorant. Equations (6.12)–(6.16) are sufficient budgets that may lose cancellations. Failure of (7.1) proves neither failure of T nor nonexistence of a better competitor.

For a concrete strictness check, on \([0,1]\) take
\[
 W(s)=-\sin(2\pi s),\qquad R(s)=100\cos(4\pi s),\qquad k(s)=1-s.
\]
Then exactly
\[
 \int_0^1RW'\,ds=0,\qquad
 \int_0^1kW\,ds=-\frac1{2\pi}<0.
\tag{7.2}
\]
Nevertheless the absolute discrepancy budget is large: on \([0,1/24]\), both cosines in \(|RW'|\) exceed 1/2 in magnitude, hence
\(\int_0^1|RW'|ds\ge100\pi/48>1/(2\pi)\).
So the signed expression is negative while the sufficient absolute envelope (6.14) does not prove it. This is an exact control for the **majorization**, not another prime system or CCM matrix.

If a source theorem is sought on a larger independently specified class, a legitimate example is
\[
 \|c\|=1,\quad Ac=\theta c,\quad\theta\le t_m^0,
\tag{7.3}
\]
where \(t_m^0\) is the Rayleigh value of the explicit centered cutoff-theta trial. Bottoms belong to this class, but excited stationary vectors may belong too. Proving an escape-sensitive (7.1) on this class would be a stronger, transformation-specific supplier. It is optional, not a mandatory replacement for T. It would have to survive the exact-stationary negative controls rather than simply read out their eigenvalue order.

### Lemma 10. A strict one-sided source envelope would give the requested competitor

**THIS STEP IS PROVED HERE — conditional implication only.**

**[FINITE_CELL | CONDITIONAL]** If independently proved source bounds give
\(\mathcal A_m^{\rm upper}-\mathcal B_m^{\rm low}\le-\eta_m<0\)
for an exact unit eigenvector c, then y=diag(a)c is nonzero and
\[
 \mathfrak k\!\left[\frac{f_y}{\|y\|}\right]
 \le\lambda-\frac{\eta_m}{\pi\|y\|^2}<\lambda.
\tag{7.4}
\]

**Proof.** Equations (2.1) and (6.13) give the negative numerator. A zero y could not have negative quadratic value, so normalization is legitimate. ∎

**THIS COMPLETION WOULD IMPLY RH.** If (7.1) were proved from complete escape for actual bottoms, (7.4) would contradict their minimum property. This would establish T, and the accepted NOESCAPE implication would establish RH. Neither implication is used as a premise proving (7.1). Its sign is still missing.

The nontrivial new result of this batch is therefore the **source-level limitation**, not a disguised claim that the above conditional completion has been achieved.

## 8. Consumer audit, routes, and decision

### 8.1 Dependency contract

| Field | Finding |
|---|---|
| DOWNSTREAM_CONSUMER | Fixed-jet NOESCAPE T, then the inherited T ⇒ RH bridge |
| ACTUAL_CONSUMER_REQUIREMENT | One fixed finite jet with a persistent positive projection on an unbounded original set, or another valid direct RH closure |
| ORIGINAL_REQUESTED_OBJECT | A strict same-carrier source competitor forced by complete escape of exact selected bottoms |
| ORIGINAL_OBJECT_IS | UNKNOWN as a necessary interface; no particular multiplier family is made mandatory |
| KNOWN_WEAKER_INTERFACES | Any independently obtained vanishing cofinal lower floor suffices for the known RH entrance; this is not assumed here |
| FAILURE_TYPE | NO_DERIVATION of the escape-sensitive source sign; COUNTEREXAMPLE only to the explicitly scoped stronger detector claims |
| EPISTEMIC_STATUS | RESEARCH_DEBT for the actual source comparison; no route-family death |
| NOVELTY_AXIS | Exact endpoint-flat source quasimodes, finite-record nulling, and paired reciprocal-cutoff arithmetic |
| REOPEN_TRIGGER | An independently proved relative signed source estimate surviving both the flat source trials and the stationary displacement plant, with the exact-eigenvector gate explicit |

### 8.2 Two candidate re-representations

The estimates below are planning judgments, not measured theorem probabilities.

| Candidate | Consumer-spendable output | Kill-power / cost estimate | Main failure mode |
|---|---|---|---|
| **Adaptive amplitude kernel and paired prime discrepancy**, §6 | A negative upper envelope (7.4) with exact pole cancellation and paid input/variation errors | High / high analytic cost | Escape fails to control the oscillatory test against reciprocal prime cutoffs; fixed-degree rules are blind on the source controls |
| **Coherent multi-edge electrical response**, not individual edge loads | A joint negative amplitude direction from off-diagonal transfer resistances | Medium-high / moderate finite diagnostic, high cofinal cost | Reconstructing the entire shifted PSD test without any independent escape-to-response estimate |

The fixed-degree boundary hierarchy is retained as a diagnostic but not selected as a cofinal supplier by itself. A growing hierarchy needs order, conditioning and residual budgets; none are silently inferred from the fixed-D proofs.

Three structural bridges were checked at the level needed here. Electrical-network theory supplies a correct restricted variational mechanism but no arithmetic escape estimate. Displacement/Loewner algebra supplies the boundary identities, while Lemma 7 blocks completeness of its fixed-degree tests. Exact prime-main-term subtraction supplies the paired discrepancy (6.5), not its sign. No purported bridge eliminates the missing source comparison.

### 8.3 Strongest attack against this verdict

The source trials are not proved exact bottoms. Therefore §§3–4 cannot refute the owner's contradiction strategy. Conversely, if the argument ignores that exactness distinction, the trials invalidate its inference even on the literal source. Lemma 5 shows one genuine minimum-only consequence, but applying it to escape would require an unproved rate-to-exactness or spectral statement.

The new primitive formula can also become another reformulation if used only to restate a negative quadratic value. This verdict does not count it as a proved sign: the interval bounds in §6 are an explicit supplier interface, and (7.1) is still the missing comparison. No numerical value has been manufactured for it.

### 8.4 Claim ledger and scoped refutations

| Claim | Scope | Verifier | Established content |
|---|---|---|---|
| B1 | FINITE_CELL | PAPER | Trial corrections, resistance controls, and the exact boundary balance |
| B2 | COFINAL_FAMILY | PAPER | Nonnegative escaping literal-source quasimodes with exact finite-order endpoint flatness |
| B3 | ABSTRACT | PAPER | Flatness makes every fixed-degree polynomial source drift vanish |
| B4 | FINITE_CELL | PAPER | Exact minimum plus flatness forces eigenspace multiplicity |
| B5 | COFINAL_FAMILY | PAPER | Any fixed finite linear source/boundary record can be annihilated by signed escaping quasimodes |
| B6 | ABSTRACT | PAPER | A structured stationary nonminimum passes every prescribed fixed-degree polynomial test |
| B7 | FINITE_CELL | PAPER | Exact pole-canceled reciprocal-prime comparison and one-sided source envelopes |
| B8 | FINITE_CELL | CONDITIONAL | A strict negative upper envelope yields the original-carrier competitor |
| B9 | COFINAL_FAMILY | CONDITIONAL | Establishing B8 from escape for actual bottoms would establish T and then RH |

The refuted theorem shapes are:

1. **Escape + arbitrary polynomial residual accuracy forces strict drift in a fixed-degree boundary test.** Counterfamily: Lemmas 3–4, the literal source. For any proposed positive margin η, the supposed gain-minus-margin has upper bound \(-\eta<0\). This is a quasimode-class refutation only.
2. **Exact stationarity + rank-two displacement makes fixed-degree tests a complete detector of nonminimum states.** Counterexample: Lemma 7, with a strict negative Rayleigh value \(-4/9\) and zero detector output. This is a structural, non-CCM refutation.

For both: `KILL_SCOPE: THEOREM_SHAPE`; `KILL_EVIDENCE_KIND: EXACT_COUNTEREXAMPLE`; pinned evidence is the theorem and reproducible Appendix A in this artifact. Neither the literal family nor variational NOESCAPE is declared mathematically dead.

## 9. Validation, registered controls, and closeout

Before exact symbolic execution, five controls were registered in the working log: the triangle and four-path energies; fixed-degree invisibility of the stationary displacement plant; consistency of the displacement/boundary/sine-coefficient identities; and the degree and endpoint jets of the cosine factor. Their fates are **CONFIRMED by exact algebra**. The additional majorant control (7.2) was checked exactly as well. These registrations concern the validation code, not a retroactive prediction of a cofinal CCM result.

The actual literal m4/m8/m16 eigenvalue and network numbers in the request were not recomputed. Their reported source quadrature is not treated as certified. No new raw CCM eigensolve, broad scan, Lean run, or repository write occurred.

**What became smaller?** A finite boundary-record route is now separated from its genuinely missing exact-eigenprofile input, with a cofinal source construction that defeats all fixed finite linear versions on the quasimode class. The arithmetic comparison can be written after the growing pole/main-prime cancellation, rather than paying those terms separately.

**What was killed?** Only the two detector theorem shapes in §8.4. T, RH and the possibility of a different strict competitor remain open.

**What must not be repeated?** Inferring strict gain from absolute smallness of boundary data or residuals; identifying all amplitude stability with a new source theorem; treating an all-zero boundary determinant as sufficient evidence of stationarity or minimality; discarding a prime endpoint or an exterior comparison tail.

**Current first unpaid source estimate:** (7.1), including the missing escape-sensitive choice and sign of its moving test polynomial. Its source enclosures are explicit; its negative sign has not been supplied.

**DISCRIMINATOR for every zero-consistent boundary output:** retain the full residual equation and, for a minimum claim, test the polynomial eigenspace consequence (3.16), not merely scalar equalities. A nonzero residual can be superpolynomially small and still exceed a proposed descent margin. For the source comparison, the discriminator is a rigorously negative upper envelope in (6.13), with complete error budget, not a rounded sign.

**Memory entry:** `BOUNDARY: fixed finite endpoint/source records can vanish exactly on escaping literal-source quasimodes. Exact minima would additionally force polynomial eigenspace invariance. Pole/main-prime cancellation gives a reciprocal-cutoff discrepancy test; escape-to-sign still unproved.`

## 10. Proshka's own line

The useful distinction is exact eigen-equations versus an arbitrarily accurate quasimode.
A tiny residual is not the same as zero when the relevant margin is still smaller.
The new endpoint factor preserves the actual carrier and makes that distinction unavoidable.
It also shows why repeatedly adding a few boundary derivatives need not change the problem.
The signed finite-record extension is stronger than a claim about one derivative trial.
It still does not manufacture an escaping exact bottom.
I would not turn the requested contradiction into a demand for a particular multiplier.
The fixed-degree multiplier has now served its diagnostic purpose.
The nearest alternative is a coherent multi-edge voltage, not another single edge.
The other alternative is an amplitude rule whose arithmetic sine kernel is controlled directly.
Both alternatives must use more than the scalar boundary equalities.
For the arithmetic route, the pole must be canceled against the prime main term before estimating.
The discrepancy that remains is at two reciprocal cutoffs, not at one isolated prime.
That paired object is source-specific and preserves every prime power.
Its sign is not a consequence of weak convergence.
A source theorem controlling its pairing with a moving eigenprofile would change the plan.
A new name for the same quadratic minimum inequality would not.
The first future check is whether a proposed amplitude rule survives the flat source packets.
The second is whether it rejects the exact stationary plant with a lower-energy direction.
Passing either control alone is insufficient.
I would ask for the explicit rule producing amplitudes, not another table of minimum values.
I would also require its signed remainder budget before authorizing a larger computation.
The strongest part of the current shelf is the exact preservation of source and carrier.
The most dangerous inference remains turning absolute decay into a relative sign.
The RH objective remains intact; no part of its missing comparison has been declared unnecessary.

## 11. Research log

### Sources actually consulted

- **[S0] READ, complete:** attached `PROSHKA_REQUEST_BOUNDARY_2026-10-30.txt`, 108 LF lines, SHA-256 recorded in the header. Governing request; resistance attempt, finite diagnostic limits, and boundary balance.
- **[S1] READ, pinned:** `docs/routeB_bus/proshka/PROSHKA_VERDICT_VARIATIONAL_2026-10-30.md` at `b659c795f445effe157fdda2fa07256f1d430163`, blob `0e6d082247f1a943d3f52922fa9791d5e6aa635d`. Local bytes matched that blob. Sections 1–7 were read for the source form, polynomial matrix bound, moving-packet return, and exact even displacement row. New endpoint multiplication required the separate nonorthogonal-error estimate (3.10).
- **[S2] READ, pinned:** `docs/routeB_bus/fokas_k_sign_2026-09-25/full_center_probe.py`, same source commit, blob `5cbd156db9be84caa938cdbabd4e9ec0b5a6d2f3`, source constructor lines 1–42. Literal `W02-WR-Prime`, endpoint and normalization check. The diagnostic code was not executed as a certificate.
- **[S3] READ:** current `docs/routeB_bus/proshka/PROSHKA_SYSTEM_PROMPT_v2.md` through the GitHub connector, blob `e0127d491799f7764e4f50e1ae4ed4cfcaf73c13`. Intake and verdict protocol; not a mathematical premise.
- **[P1] READ, bounded:** Zelazo–Bürger, *On the Robustness of Uncertain Consensus Networks*, arXiv:1408.4471, retrieved text displaying v2, Theorem IV.7, PDF page 8. Checked the connected-positive-graph, one-negative-edge scope. The direct many-edge sufficient argument is proved here. Web screenshot attempts failed with a cache error; no visual inspection or independent match to the request's saved PDF hash is claimed.
- **RELAY / DIAGNOSTIC:** the finite literal network/eigenvector values in S0. Used to respect the supplied limitations, never as a theorem premise.
- **INHERITED ACCEPTED PAPER INPUT:** the theta radical and weighted decay statements supplied through S1 and the request's audit boundary. No new independent audit of all earlier explicit-formula machinery is claimed.

### Branches rejected or restricted, with the mathematical reason

- Single-edge completeness: the exact four-path example has single loads below one and a negative combined voltage.
- Degree-only boundary escalation: Lemma 3 supplies arbitrary fixed endpoint flatness while preserving source escape and superpolynomial residual.
- Treating finite linear observations as a uniform source obstruction: Lemma 6 nulls any fixed number of them.
- Reusing old projection orthogonality after multiplying by the endpoint factor: false in general; repaired by retaining the diagonal constant and using H¹ zero-trace control in (3.10).
- Treating a zero boundary determinant as an exact eigenrelation: the trial correction survives; exact stationarity and PSD are separate hypotheses.
- Inferring oscillation or an antiphase cost from moment escape: no sign implication; the source controls are nonnegative before finite-record nulling.
- Replacing the prime comb by its continuous density: not performed. The complete discrepancy is kept in (6.2)–(6.5).
- Claiming the primitive enclosure already proves descent: rejected at the unproved sign (7.1).

### Reusable intermediate results

The cosine-factor construction enforces high-order endpoint conditions without enlarging the original Fourier carrier. The finite-packet nulling argument needs no conditioning estimate for the prescribed linear observations. The polynomial displacement plant has an exact negative witness for every fixed test degree. The reciprocal discrepancy is monotone between explicitly listed source knots; its one-sided bounds require no unlocated interior extremum. These results may be reused at precisely their stated scopes.

## 12. One next directive

**CODEX DIRECTIVE — source comparison, not another stability identity.**

At the pinned literal source, seek an explicit amplitude-selection rule outside a merely fixed-degree polynomial hierarchy and prove a one-sided estimate for the paired prime-discrepancy functional in (6.5) on the low-energy stationary class (7.3), using complete fixed-jet escape. The deliverable is either independent bounds yielding (7.1), with all projection/input/arithmetic errors paid, or an exact counterexample to the proposed rule on its stated class. The source packets of Lemma 3 and the stationary plant of Lemma 7 are mandatory negative controls at their respective scopes; neither is a substitute for checking exact literal eigen-equations. Do not promote a finite diagnostic, a computed shifted PSD matrix, or the identity (6.5) itself into the required source estimate. No repository write, Lean run or broad numerical scan is authorized by this directive.

**Success condition:** a strictly negative upper envelope for one same-carrier competitor on a cell forced by the escape argument. **Failure report:** the first actual source estimate that cannot be proved, with its quantified class and residual-relative budget. Report `SOURCE_COMPARISON_PROVED` or `SOURCE_COMPARISON_FIRST_UNPAID`; neither label alone establishes RH.

**Final boundary:** RH is the objective. No strict competitor for an actual escaping bottom, no proof of T, and no completed RH chain is claimed here. New results are PAPER proofs plus the exact algebra controls below; independent review and formal verification of this verdict have not been performed.

## Appendix A. Reproducible exact algebra controls

The script uses Python and SymPy. It performs no raw CCM numerical scan. `degree` is the prescribed fixed polynomial degree in the structured counterexample; `x` contains the distinct squared mode labels; `d` contains the orthonormal even-basis weights. The request hash check is performed only when the supplied TXT exists at the displayed local path. All negative Rayleigh values, graph controls and displacement identities are exact.

```python
#!/usr/bin/env python3
"""Exact algebra controls for BOUNDARY; no literal CCM numerical scan."""
from pathlib import Path
from itertools import product
import hashlib
import sympy as s


def laplacian(n, edges):
    M = s.zeros(n)
    for i, j, w in edges:
        b = s.zeros(n, 1)
        b[i], b[j] = 1, -1
        M += w * b * b.T
    return M


def quad(M, v):
    return s.simplify((v.T * M * v)[0])


def main():
    request = Path('/mnt/data/PROSHKA_REQUEST_BOUNDARY_2026-10-30.txt')
    if request.exists():
        raw = request.read_bytes()
        assert len(raw) == 6891 and raw.count(b'\n') == 108
        assert hashlib.sha256(raw).hexdigest() == '50bfc8c63d663bae15b916936646eadf8379c9a78dedbf3d934d58db8bc727ba'
        print('request: exact byte/hash check PASS')

    L3 = laplacian(3, [(0, 1, s.S.One), (1, 2, s.S.One),
                         (0, 2, -s.Rational(3, 4))])
    for bits in product([0, 1], repeat=3):
        assert quad(L3, s.Matrix(bits)) >= 0
    a3 = s.Matrix([1, s.Rational(1, 2), 0])
    assert quad(L3, a3) == -s.Rational(1, 4)
    assert s.simplify(3 * quad(L3, a3) / (a3.dot(a3))) == -s.Rational(3, 5)
    print('triangle: all cuts PASS; voltage=-1/4; normalized gain=-3/5')

    Lp = laplacian(4, [(0, 1, s.S.One), (1, 2, s.S.One), (2, 3, s.S.One)])
    B = s.Matrix([[1, 0], [0, 1], [-1, 0], [0, -1]])
    R = s.simplify(B.T * Lp.pinv() * B)
    assert R == s.Matrix([[2, 1], [1, 2]])
    load = s.Rational(2, 5) * R
    assert set(load.eigenvals()) == {s.Rational(6, 5), s.Rational(2, 5)}
    L4 = Lp - s.Rational(2, 5) * B * B.T
    assert quad(L4, s.Matrix([3, 2, 1, 0])) == -s.Rational(1, 5)
    print('four-path: single loads=4/5; joint top load=6/5; voltage=-1/5')

    # For a fixed degree d, the plant has m=d+2 (m+1 nodes).
    # d_i match the orthonormal even-basis weights; the matrix is NOT CCM.
    for degree in [1, 2, 3, 4]:
        n = degree + 3
        x = [s.Integer(i * i) for i in range(n)]
        d = [s.S.One] + [s.sqrt(2)] * (n - 1)
        v = s.Matrix(d)
        X = s.diag(*x)
        u = X**2 * v
        A = (X*v)*v.T + v*(X*v).T
        assert X*A - A*X == u*v.T - v*u.T
        c = s.Matrix([1/(d[i]*s.prod(x[i]-x[j] for j in range(n) if j != i))
                      for i in range(n)])
        for k in range(degree + 2):
            assert s.simplify((v.T*X**k*c)[0]) == 0
        for k in range(degree + 1):
            assert s.simplify(A*X**k*c) == s.zeros(n, 1)
        y = s.zeros(n, 1)
        y[0], y[1] = 2*s.sqrt(2), -1
        assert quad(A, y) == -4 and y.dot(y) == 9
        if degree >= 2:
            S0 = (v.T*c)[0]
            Sx = (v.T*X*c)[0]
            SF = (u.T*c)[0]
            SFx = (u.T*X*c)[0]
            assert all(s.simplify(z) == 0 for z in (S0, Sx, SF, SFx))
        print(f'polynomial plant d={degree}: exact stationary invisibility PASS; Rayleigh(y)=-4/9')

    n = 4
    x = [s.Integer(i*i) for i in range(n)]
    d = [s.S.One] + [s.sqrt(2)]*(n-1)
    F = list(map(s.Rational, [0, 3, -2, 5]))
    c = s.Matrix([s.Rational(z)/d[i] for i, z in enumerate([1, -2, 3, -4])])
    A = s.zeros(n)
    for i in range(n):
        for j in range(n):
            if i != j:
                A[i, j] = d[i]*d[j]*(F[i]-F[j])/(x[i]-x[j])
    lam = s.Rational(2, 7)
    for i in range(n):
        A[i, i] = lam-sum(A[i,j]*c[j] for j in range(n) if j != i)/c[i]
    X = s.diag(*x)
    v = s.Matrix(d)
    u = s.Matrix([d[i]*F[i] for i in range(n)])
    assert s.simplify(A*c-lam*c) == s.zeros(n, 1)
    assert s.simplify(X*A-A*X-u*v.T+v*u.T) == s.zeros(n)
    S0, SF = (v.T*c)[0], (u.T*c)[0]
    Sx, SFx = (v.T*X*c)[0], (u.T*X*c)[0]
    assert s.simplify(quad(A-lam*s.eye(n), X*c)-(Sx*SF-S0*SFx)) == 0
    a = s.Matrix([1, s.Rational(-1, 2), s.Rational(2, 3), 0])
    D = s.diag(*a)
    wenergy = -sum(A[i,j]*c[i]*c[j]*(a[i]-a[j])**2
                   for i in range(n) for j in range(i+1,n))
    assert s.simplify(quad(A-lam*s.eye(n), D*c)-wenergy) == 0
    z = s.symbols('z0:'+str(n))
    Wpair = -sum(d[i]*d[j]*c[i]*c[j]*(x[i]-x[j])*(i*z[i]-j*z[j])
                 for i in range(n) for j in range(i+1,n))
    Wmoment = Sx*sum(d[i]*c[i]*i*z[i] for i in range(n)) \
              -S0*sum(d[i]*c[i]*i**3*z[i] for i in range(n))
    assert s.simplify(Wpair-Wmoment) == 0
    print('displacement, eigenrelation, multiplier energy, sine coefficients: PASS')

    t = s.symbols('t', real=True)
    for degree in [1, 2]:
        edge = s.cos(s.pi*t)**(4*degree)
        for k in range(4*degree):
            assert s.simplify(s.diff(edge,t,k).subs(t,s.Rational(1,2))) == 0
            assert s.simplify(s.diff(edge,t,k).subs(t,-s.Rational(1,2))) == 0
        zvar = s.symbols('z')
        laurent = s.expand(((zvar+2+zvar**-1)/4)**(2*degree))
        assert s.Poly(s.expand(zvar**(2*degree)*laurent),zvar).degree() == 4*degree
    print('flat endpoint factor: exact endpoint jets and degree: PASS')

    # Strict prime-discrepancy majorization is not necessary for negative signed energy.
    W = -s.sin(2*s.pi*t)
    Rtoy = 100*s.cos(4*s.pi*t)
    assert s.integrate(Rtoy*s.diff(W,t),(t,0,1)) == 0
    assert s.integrate((1-t)*W,(t,0,1)) == -1/(2*s.pi)
    print('majorant countercontrol: signed error=0, negative reference=-1/(2*pi): PASS')
    print('ALL EXACT CONTROLS PASS; no literal CCM eigenvalue claim.')

if __name__ == '__main__':
    main()
```

Executed output:

```text
request: exact byte/hash check PASS
triangle: all cuts PASS; voltage=-1/4; normalized gain=-3/5
four-path: single loads=4/5; joint top load=6/5; voltage=-1/5
polynomial plant d=1: exact stationary invisibility PASS; Rayleigh(y)=-4/9
polynomial plant d=2: exact stationary invisibility PASS; Rayleigh(y)=-4/9
polynomial plant d=3: exact stationary invisibility PASS; Rayleigh(y)=-4/9
polynomial plant d=4: exact stationary invisibility PASS; Rayleigh(y)=-4/9
displacement, eigenrelation, multiplier energy, sine coefficients: PASS
flat endpoint factor: exact endpoint jets and degree: PASS
majorant countercontrol: signed error=0, negative reference=-1/(2*pi): PASS
ALL EXACT CONTROLS PASS; no literal CCM eigenvalue claim.
```

The output validates the algebraic controls only. The analytic proofs of the original-carrier source construction and the scope of the unproved comparison are in the main text.
