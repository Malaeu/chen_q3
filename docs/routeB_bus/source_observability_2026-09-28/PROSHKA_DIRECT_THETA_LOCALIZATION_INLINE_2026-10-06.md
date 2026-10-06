# Proshka answer 9/10 — complete inline source

Date: 2026-10-06. Chat: Missing T7 Lemma (6aba5f5a-f804-83ed-a667-68147ee00f59).
Question: 9fa73047-9963-4c76-82b1-4e20ce1d5b85. Answer: d3e3f774-1ce0-44fe-b8ac-c341aded0fcc.
Captured through read_thread after chat became idle. Linked supplement not retrieved; citation placeholders retained verbatim and not independently resolved.

## Exact question

Continuation 9/10. Answer8 is processed. Continue the SAME source-transfer goal; no new matrix, ground family or schedule.

Independent audits accepted the exact adjoint Mellin forcing and both jump moments, the reference-center tau construction, and the inertia obstruction. Notation repair: J_raw is the mu-self-adjoint recurrence matrix; B_i is its RAW deleted block in B_i p_i=-ell_1 e1; H_i=S B_i S^-1 is Euclidean symmetric. Treating B_i as already symmetric would lose the weights. R_green is indefinite on the full Jacobi carrier, but this says nothing about its first row or actual bottom forcing.

The source comparison (10)-(14) and flux (16)-(17) also checked out under the SAME matched HMODE/chi, source scaling and T1-T6 inputs. In particular h*=-16 h_CCM; a73=4a72; the window Fourier basis is (-1)^n L^-1/2 exp(2pi i n t/L). Both endpoint phases cancel. The second integration-by-parts boundary term was kept. We accepted ||Pi_span{eta,beta} qhat||=O(m^-1/4) as a FULL-CARRIER obstruction only; it proves no bottom-space angle.

The useful paid simplification is your (12). Let
g_m=c_m(G)/||c_m(G)||,
using the actual WINDOW Fourier coefficients on -m..m, not full-line samples. On the same port/schedule,
||qhat_m-xi_m g_m||<=delta_m=16 C_src/g_* m^-1/4+2E_m/Z_m=O_P(m^-1/4).
Therefore a bound for ALL bottom vectors
||(I-g_m g_m*)v|| <= C m^-1/4(log m)^A |g_m*v|
would imply the original OS at the same rate: first source injectivity gives simplicity, alpha_g<=epsilon; then alpha_q<=alpha_g+delta and its OS ratio is at most 2(epsilon+delta) eventually. Exact g_m is real even, so source-null exclusion also rules out an odd ground line. This is a paid auxiliary reference change, not a replacement of the original selected ground family. Do not spend the answer reproving this conditional bridge.

Our direct attempt:
The already audited global radical identity W(G,f)=0 holds without RH for every finite-window synthesis f, retaining the full pole, archimedean and prime-power terms.
Let f_g synthesize the unit row g_m, and r_m=G/||c_m(G)||-f_g on the whole line.
For ANY bottom v of the literal K_m, with synthesis f_v,
W(r_m,f_v)=-W(f_g,f_v)=-lambda0,m <g_m,v>.
No division by lambda0 is legitimate as a source bound. If g_m*v=0, this only gives W(r_m,f_v)=0, with no contradiction. An absolute residual bound cannot select the ground against the existing G,G'',... radical tower.

Please now attack the bottom-restricted overlap with the EXPLICIT THETA SOURCE G directly, using this paid simplification to avoid the unbounded-sign Robin Green inversion. The actual target is the displayed all-bottom inequality, or a genuinely proved component excluding source-null bottom vectors. Use the literal full signed Weil form and ground minimality together to obtain new source-specific information; preserve N=m and the original eventual quantifiers. A proven source-specific obstruction to this precise target would also change the plan.

Do not replace W by an archimedean-only or positive surrogate. G has a fixed sign on the real line, but the old signed ground-state-transform/finite-stencil attempts already showed that this does not supply positivity of W. Do not import a global complement floor, inverse-gap bound, PF argument with unproved entry signs, or an RH-equivalent all-profile positivity premise. Do not replay the Robin kernel sign partition: the September25 paper already retained full oscillatory forcing and lacked its signed pairing.

We need a new actual-source lower overlap or a rigorous actual-source obstruction, not more sufficient wrappers, generic projection identities, residual smallness, or algebra-control counts. If your concrete direct-theta attempt stalls, identify exactly what it tried and the first signed quantity it cannot bound. OS, source-null exclusion, prescribed U, G1/G3/RH remain OPEN. No Lean or repository writes.

## Exact inline answer

Ы. **I have not obtained a bottom-restricted overlap bound or excluded a source-null bottom vector.** The concrete direct-theta attempt below stalls at an explicit signed variational quantity. I am **not** recording an advance on OS.

The attempted variation was
\[
f_v\longmapsto P_m(Gf_v),
\]
using the complete \(G\) and returning to the **same original Fourier carrier**. It has an exact connection to the source coordinate, so it avoids the Robin inversion. But ground minimality does not supply the sign needed for the variation to lower energy.

There is a rigorous obstruction to one proposed repair: **uniformly small multiplication/projection error is false even on explicit, real-even, source-null carrier vectors**. Those vectors are not proved to be bottom vectors. That distinction remains essential.

## 1. A source-linked admissible variation

Retain
\[
m=m_j=N_j,\qquad L=\log m,\qquad I=[-L/2,L/2],
\]
and the full basis
\[
\psi_{n,L}(t)=\frac{(-1)^n}{\sqrt L}e^{2\pi int/L}\mathbf1_I(t),
\qquad |n|\le m.
\]
Let \(P_m\) be the orthogonal projection onto this carrier, not a ground projector. The full \(K_m\), original schedule, and complex Euclidean metric are unchanged. :chatgpt-content-reference{index="0"}

Write
\[
c_n=c_m(G)_n,\qquad
\sigma_m=\left(\sum_{|n|\le m}|c_n|^2\right)^{1/2},
\qquad
g_m=(c_n)_{|n|\le m}/\sigma_m.
\]

Suppose
\[
K_mv=\lambda v,\qquad
\lambda=\lambda_{\min}(K_m),
\]
with **no simplicity or parity assumption**, and let \(f=f_v\) be its synthesis.

Set
\[
y=P_m(Gf).
\]

The central coefficient is exactly
\[
\boxed{
y_0=\frac1{\sqrt L}\int_I G(t)f(t)\,dt
=\frac{\sigma_m}{\sqrt L}\langle g_m,v\rangle.
}
\tag{1}
\]
Thus a **source-null** bottom vector—one with \(\langle g_m,v\rangle=0\)—produces a central-zero admissible variation.

The variation is nonzero whenever \(v\ne0\):
\[
\boxed{
\langle f,y\rangle_2
=\int_I G(t)|f(t)|^2\,dt<0.
}
\tag{2}
\]
Here \(G<0\) follows from its complete theta series on \(t\ge0\), together with exact evenness. This is a sign of the **multiplication weight**, not a sign of the Weil form. The source and its symmetry are those of the audited radical calculation. 

For clarity, the coefficient matrix of this multiplication followed by projection is
\[
(T_G)_{n\ell}=\frac{c_{n-\ell}}{\sqrt L},
\qquad
g_m=\frac{\sqrt L}{\sigma_m}T_Ge_0.
\]
Both Fourier phases are included. This auxiliary operator does **not** replace \(K_m\) or define another ground family.

The proposed contradiction was to prove that source-nullity forces
\[
\mathcal W(y,y)-\lambda\|y\|_2^2<0.
\]
Ground minimality forbids such a decrease. **The required strict inequality is not established.** Its full source expression follows.

## 2. The complete signed quantity—not an archimedean surrogate

Define
\[
J(s)=\frac{e^{-s/2}}{1-e^{-2s}}
\]
and
\[
B_{G,f}(s)=
\int_{-L/2}^{L/2-s}
\bigl(G(t+s)-G(t)\bigr)^2
\operatorname{Re}\!\left(\overline{f(t)}f(t+s)\right)\,dt.
\]

The exact **localization defect**, meaning the energy change produced by multiplication before restoring the carrier, is
\[
\boxed{
\begin{aligned}
\mathcal S_{G,m}(f)
&:=\mathcal W(Gf,Gf)
-\operatorname{Re}\mathcal W(G^2f,f)\\
&=
\int_0^L\bigl[J(s)-2\cosh(s/2)\bigr]B_{G,f}(s)\,ds\\
&\quad+
\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
B_{G,f}(\log q).
\end{aligned}
}
\tag{3}
\]

This uses the literal \(W_{0,2}-W_{\mathbb R}-\mathrm{Prime}\) signs. The full pole term and every prime power remain. 

To check the formula, write
\[
C_{u,w}(s)=\int\overline{u(t)}w(t+s)\,dt,
\qquad
Q_{u,w}(s)=C_{u,w}(s)+C_{u,w}(-s).
\]
Then
\[
\begin{aligned}
&Q_{Gf,Gf}(s)-\operatorname{Re}Q_{G^2f,f}(s)\\
&\quad=
\int
\bigl[2G(t)G(t+s)-G(t)^2-G(t+s)^2\bigr]
\operatorname{Re}(\overline{f(t)}f(t+s))\,dt\\
&\quad=-B_{G,f}(s).
\end{aligned}
\]
The difference is zero at \(s=0\). Therefore the value-at-zero constant and archimedean subtraction cancel **exactly in this difference**. They were not removed from \(K_m\). The full mixed-form normalization is the audited one. 

The endpoint checks are straightforward:
\[
|B_{G,f}(s)|
\le s^2\|G'\|_\infty^2\|f\|_2^2,
\]
so the \(J(s)\sim1/(2s)\) singularity is integrable. At \(s=L\), the overlap interval has length zero. Thus the atom \(q=m\) is retained and vanishes for the correct support reason.

**The square involving \(G\) does not make (3) nonnegative or nonpositive.** The factor
\(\operatorname{Re}(\overline{f(t)}f(t+s))\) remains signed, and the continuous coefficient is \(J-2\cosh\), not \(J\).

## 3. Ground minimality requires the projection corrections too

Put
\[
h=Gf,\qquad y=P_mh,\qquad e=(I-P_m)h,
\]
\[
k=G^2f,\qquad z=P_mk,\qquad d=(I-P_m)k.
\]

Because \(z\) belongs to the original carrier and \(f\) is a bottom eigenfunction,
\[
\mathcal W(z,f)
=\lambda\langle z,f\rangle_2
=\lambda\int_I G^2|f|^2
=\lambda(\|y\|_2^2+\|e\|_2^2).
\]
Expanding the two energies gives
\[
\boxed{
\mathcal W(y,y)-\lambda\|y\|_2^2
=
\mathcal S_{G,m}(f)+\mathcal C_{G,m,\lambda}(f),
}
\tag{4}
\]
where
\[
\boxed{
\begin{aligned}
\mathcal C_{G,m,\lambda}(f)
={}&-2\operatorname{Re}\mathcal W(e,y)-\mathcal W(e,e)\\
&+\lambda\|e\|_2^2+\operatorname{Re}\mathcal W(d,f).
\end{aligned}
}
\tag{5}
\]

Every \(\mathcal W\) in (5) is the **full signed form**. The term \(\lambda\|e\|^2\) is retained without assuming the sign of \(\lambda\). There is no division by \(\lambda\), so the calculation also applies when \(\lambda=0\).

The products and remainders are smooth inside \(I\), with possible zero-extension jumps at its endpoints. Those jumps remain in their full-form pairings; they are not declared whole-line \(H^1\) functions.

For every bottom vector, ground minimality gives
\[
\mathcal S_{G,m}(f)+\mathcal C_{G,m,\lambda}(f)\ge0.
\]
The attempted exclusion needs the additional condition \(\int_I Gf=0\) to force the **opposite strict inequality**. I have not obtained such a source estimate.

The radical identity does not remove the difficulty:
\[
\mathcal W(G,F)=0
\]
does not permit replacing its first argument by \(Gf\) or \(G^2f\). This variation avoids the already-known zero pairing, but leaves the signed expression (3)–(5) unpaid.

## 4. A rigorous obstruction to the uniform norm repair

**[COFINAL_FAMILY | PAPER; carrier statement, not bottom statement]**

There are explicit real-even unit vectors \(x_m\) in the original carrier such that
\[
\langle g_m,x_m\rangle=0
\]
and
\[
\boxed{
L\|(I-P_m)(Gf_{x_m})\|_2^2
\longrightarrow\frac{\|G\|_2^2}{2},
}
\tag{6}
\]
while
\[
\boxed{
\frac{\|(I-P_m)(Gf_{x_m})\|_2^2}
{\|Gf_{x_m}\|_2^2}
\longrightarrow\frac12.
}
\tag{7}
\]

Thus multiplying a source-null carrier vector by the exact smooth \(G\) can lose asymptotically half its product norm across the Fourier cutoff.

### Actual-source calculation

Let
\[
A_G=\frac{\|G''\|_1+2\|G'\|_\infty}{4\pi^2}.
\]
The actual window coefficients satisfy
\[
|c_n|\le A_GL^{3/2}n^{-2}\qquad(n\ne0).
\tag{8}
\]
The first integration-by-parts boundary term cancels by evenness and the endpoint phases; the second is retained in \(2\|G'\|_\infty\). These are the same checked coefficient conventions and boundary calculation. 

Begin with the top cosine vector
\[
u_m=\frac{e_m+e_{-m}}{\sqrt2}.
\]
The \(n\)-th coefficient of \(Gf_{u_m}\) is exactly
\[
\frac{c_{n-m}+c_{n+m}}{\sqrt{2L}}.
\]
Therefore
\[
\boxed{
L\|(I-P_m)(Gf_{u_m})\|_2^2
=\sum_{r\ge1}|c_r+c_{2m+r}|^2.
}
\tag{9}
\]

Write
\[
S_m=\int_I G^2,\qquad I_m=\int_I G,
\qquad T_{2m}=\sum_{r>2m}c_r^2.
\]
Parseval gives
\[
\sum_{r\ge1}c_r^2
=\frac12\left(S_m-\frac{I_m^2}{L}\right),
\]
and (8) gives
\[
T_{2m}\le\frac{A_G^2L^3}{24m^3}\longrightarrow0.
\]
The mixed term in (9) has absolute value at most
\[
2\sqrt{
\frac12\left(S_m-\frac{I_m^2}{L}\right)T_{2m}
}.
\]
Since \(S_m\to\|G\|_2^2\) and \(|I_m|\le\|G\|_1\), equation (9) tends to \(\|G\|_2^2/2\).

Also,
\[
L\|Gf_{u_m}\|_2^2
=S_m+\int_I G(t)^2\cos(2\omega_mt)\,dt
\longrightarrow\|G\|_2^2.
\]
Indeed, the oscillatory integral is bounded by
\[
\frac{\|(G^2)'\|_1}{2\omega_m};
\]
the boundary sine is \(\sin(2\pi m)=0\).

Now make the vector **exactly source-null**, rather than approximately so. Set
\[
a_m=\langle g_m,u_m\rangle
=\frac{\sqrt2c_m}{\sigma_m},
\qquad
\boxed{
x_m=\frac{u_m-a_mg_m}{\sqrt{1-a_m^2}}.
}
\tag{10}
\]
Here \(c_m\) means the coefficient with label \(n=m\). Eventually \(\sigma_m\ge\|G\|_2/2\), and
\[
|a_m|
\le
\frac{2\sqrt2A_GL^{3/2}}{\|G\|_2m^2}.
\]
Thus \(x_m\) is real, even, unit, source-null, and
\[
\|x_m-u_m\|\le2|a_m|.
\]
Multiplication by \(G\) has norm \(\|G\|_\infty\), so
\[
\sqrt L\,\|G(f_{x_m}-f_{u_m})\|_2
=O_G(L^2/m^2)\longrightarrow0.
\]
This proves (6)–(7).

In particular, eventually
\[
\boxed{
\|(I-P_m)(Gf_{x_m})\|_2
\ge\frac{\|G\|_2}{4\sqrt{\log m}}.
}
\tag{11}
\]
For any fixed \(C,A\), this exceeds
\[
Cm^{-1/4}(\log m)^A
\]
on the sufficiently late original sequence.

**What is ruled out:** a uniform quarter-power \(L^2\) bound for this multiplication leakage over all even, source-null unit carrier vectors.

**What is not ruled out:** a bottom-restricted bound, cancellation among the full-form corrections in (5), source-null bottom exclusion, or OS. No \(x_m\) above has been identified as a bottom vector.

The physical values \(G(\pm L/2)\) are Gaussian-small. The loss is at the **spectral carrier edge**, not evidence of a large physical endpoint value.

## 5. Where the direct-theta attempt stops

The first signed quantity I cannot control is
\[
\boxed{
\begin{aligned}
\mathcal L_m(f)
={}&
\int_0^L[J(s)-2\cosh(s/2)]B_{G,f}(s)\,ds\\
&+\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
B_{G,f}(\log q)
+\mathcal C_{G,m,\lambda}(f),
\end{aligned}
}
\tag{12}
\]
restricted by the **literal bottom equation** and \(\int_I Gf=0\).

For a bottom vector, (12) equals the nonnegative admissible energy difference in (4). A source-null exclusion argument through this variation must independently force a negative upper bound. **I have not proved it.** Writing that desired negativity as another named lemma would merely restate the missing exclusion, so I am not proposing another conditional supplier.

There is a precise distinction between the already-paid source projection estimate and the unavailable one here. For the fixed \(G\), projection decay is known. For \(Gf_v\), the second factor is a moving eigenfunction. In fact, splitting \(v\) at \(|n|=\lfloor m/2\rfloor\) gives
\[
\boxed{
\|(I-P_m)(Gf_v)\|_2
\le
\|G\|_\infty\|v_{\rm edge}\|
+\frac{6A_GL}{m}\|v\|,
}
\tag{13}
\]
where \(v_{\rm edge}\) contains the original coordinates \(|n|>\lfloor m/2\rfloor\). This follows from the exact coefficient convolution and (8).

No adequate estimate for \(v_{\rm edge}\) on the **whole bottom eigenspace** is established here. And even such an estimate would not, by itself, supply the signed comparison (12). Equation (13) is only a diagnosis of what the norm-based localization attempt lacks—not a new mandatory OS premise.

The literature localization analogy also does not fill this gap. The discrete IMS estimate in Di Gesù, Proposition 3.1, is for a standard discrete Laplacian and a smooth quadratic partition of unity. Its hypotheses and error estimate do not cover the full signed Weil kernel, growing prime translations, or the sharp production Fourier compression used here. No positivity or spectral conclusion is imported from it. :chatgpt-content-reference{index="5"}

**Disposition:** this direct-theta multiplication attack is stalled. It supplies no lower overlap, no source-null bottom exclusion, and no counterexample to OS. The auxiliary carrier obstruction prevents one unjustified repair, but it is not progress through the bottom-space problem. The prescribed \(U_m\), G1, G3 and RH remain open.

No source spectral experiment, Lean work, repository write, or independent audit of this new derivation was performed.

:chatgpt-content-reference{index="7"}[Complete PAPER note: full signed variational calculation, explicit source-null carrier obstruction, constants, and exact stall boundary](sandbox:/mnt/data/PROSHKA_G1_DIRECT_THETA_LOCALIZATION_STALL_2026-10-06.md)

