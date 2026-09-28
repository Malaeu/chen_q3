# PAPER verdict: **(C) — source-specific cofinal resolvent-rate supplier remains unproved**

**Request:** `REQ-2026-09-28-ROUTEB-ALPHA-T7-RATE`  
**Source snapshot:** `09fa2a702063a07f67949d4c77e292a9fbf9fac2`

I do not obtain either a sufficient cofinal upper envelope for the actual \(\alpha_j\), or a source-identified cofinal lower bound refuting T7. The precise missing supplier is a **joint independent-cut and inverse-residual estimate for the original reference row against the literal full \(K_j\)**. The current front correctly distinguishes this obligation from the source-transfer error already paid by matched T5 inputs. 

There is a useful sharpening: the independent ground-upper-bound requirement can be expressed as a signed Schur inequality using the same \(K_j,\widehat q_j,\mu_j,B_{\mu,j}\), without putting the unknown ground eigenvalue into the construction. The remaining rate requirement is then an explicit relative-residual inequality. Neither follows from the existing transfer bounds.

## 1. What is already paid, with the original quantifiers

Fix the matched port \(P\). Throughout,
\[
m_j=N_j=\operatorname{preAnchorTailStart}(P)+j+2,
\qquad K_j=K_{m_j},
\]
and
\[
\widehat z_j=z(c_{0,j},c_{4,j}),\qquad
Z_j=\|\widehat z_j\|,\qquad
\widehat q_j=\widehat z_j/Z_j.
\]
Here \(K_j\) is the **full** CCM matrix, and the reference energies are the centers of the same Robin intervals used by the source transfer. The reference-prefix cutoff \(6m_j-1\) is not a replacement for the original Fourier radius \(N_j=m_j\). 

Write
\[
\varepsilon_j=\frac{E_j}{Z_j},
\qquad
W_H(m)=m^{H/2}\sqrt{\log m}.
\]
Under precisely the matched hypotheses and eventual thresholds of T5,
\[
\begin{aligned}
\varepsilon_j\le {}&
\frac{2400C_A}{c_G}\,
m_j^{11/4}(8/25)^{m_j}\\
&+\frac{16C_P}{c_G}\,
m_j\sqrt{\log m_j}\,210^{-m_j}\\
&+\frac{320C_A}{c_G}\,
m_j^{5/4}\sqrt{\log m_j}\,(2/225)^{m_j}.
\end{aligned}
\tag{1}
\]
This is the division by the positive \(Z_j\)-lower bound recorded in the observability README; it does not extend those eventual estimates to the subthreshold numerical cells. 

Consequently,
\[
\forall H\ge0,\qquad W_H(m_j)\varepsilon_j\longrightarrow0.
\tag{2}
\]
With the matched center floor, T3–T6 therefore give
\[
\operatorname{tracking\_error}_{j,H}
\le
\frac{|\Xi(0)|}{\sqrt{c_{\rm Center}}}\,
W_H(m_j)\bigl(\alpha_j+4\varepsilon_j\bigr)
\tag{3}
\]
eventually. The unresolved term is exactly the reference angle term. 

In fact, the angle transfer itself admits a two-sided estimate. Choose the common phase supplied by the source crosswalk and put \(q_j^{\rm sel}=b_j/\|b_j\|\). For \(E_j<Z_j\),
\[
\begin{aligned}
\|q_j^{\rm sel}-\widehat q_j\|
&\le
\left\|\frac{b_j}{\|b_j\|}-\frac{b_j}{Z_j}\right\|
+\left\|\frac{b_j-\widehat z_j}{Z_j}\right\|\\
&=
\frac{|Z_j-\|b_j\||}{Z_j}+\frac{E_j}{Z_j}
\le2\varepsilon_j.
\end{aligned}
\]
For the **same** ground projector,
\[
\left|
\|(I-P_{0,j})q_j^{\rm sel}\|-\alpha_j
\right|
\le2\varepsilon_j.
\tag{4}
\]

Thus, under (2), the all-\(H\) weighted angle-decay condition for the selected row is equivalent to that for the reference row. This strengthens the gap-free transfer, but supplies no estimate for either angle.

The target remains
\[
\boxed{
\forall H\ge0\ \forall \epsilon>0\
\exists J(P,H,\epsilon)\
\forall j\ge J:\quad
W_H(m_j)\alpha_j<\epsilon .
}
\tag{T7}
\]
An upper-rate proof must cover every sufficiently late index of this schedule, not a newly chosen subsequence.

## 2. The precise first missing lemma

Define the **reference** Rayleigh energy and residual:
\[
a_j=\widehat q_j^*K_j\widehat q_j,\qquad
Q_j=I-\widehat q_j\widehat q_j^*,\qquad
r_j=(K_j-a_jI)\widehat q_j=Q_jK_j\widehat q_j.
\tag{5}
\]
In particular, \(r_j\in\widehat q_j^\perp\). For real \(\mu_j\), set
\[
B_{\mu,j}
=
\left.Q_j(K_j-\mu_jI)Q_j\right|_{\widehat q_j^\perp}.
\tag{6}
\]

### Missing lemma: cofinal source-reference independent-cut/resolvent certificate

For the fixed matched \(P\), construct from the original source data a sequence of real cuts \(\mu_j\), positive numbers \(d_j\), and an index \(J_0\), such that the following hold.

For **every \(j\ge J_0\)**,
\[
\boxed{
\langle y,B_{\mu,j}y\rangle
\ge d_j\|y\|^2
\quad
\text{for every }y\in\widehat q_j^\perp
\subset\mathbb C^{\,2m_j+1},
\qquad d_j>0,
}
\tag{M1}
\]
and
\[
\boxed{
\sigma_j:=
a_j-\mu_j-r_j^*B_{\mu,j}^{-1}r_j
\le0.
}
\tag{M2}
\]

For this **same cut sequence**, establish
\[
\boxed{
\begin{gathered}
\forall n\in\mathbb N\
\exists C_n^{\rm res}<\infty\
\exists J_n\ge J_0\
\forall j\ge J_n:\\[2mm]
r_j^*B_{\mu,j}^{-2}r_j
\le (C_n^{\rm res})^2m_j^{-2n}.
\end{gathered}
}
\tag{M3}
\]

The constants and thresholds may depend on \(P\) and \(n\). There is no demand for uniformity over ports, no fixed positive floor, and no demand for a polynomial lower bound on \(d_j\).

**The first undischarged prerequisite is the cofinal construction satisfying M1–M2. Even granting that prerequisite, M3 is the missing rate estimate.** The independent-energy paper explicitly leaves both family admissibility and weighted inverse-residual decay outstanding. 

The construction must supply a source-based rule or certificate for \(\mu_j\); defining it to be the unknown \(\lambda_{0,j}\) does not discharge the obligation.

An equivalent, entirely original-operator formulation of M3 is
\[
\boxed{
r_jr_j^*
\preceq
(C_n^{\rm res})^2m_j^{-2n}B_{\mu,j}^{\,2}
\quad\text{on }\widehat q_j^\perp,
}
\tag{7}
\]
with the same quantifiers. Indeed, congruence by \(B_{\mu,j}^{-1}\) turns (7) into
\[
(B_{\mu,j}^{-1}r_j)(B_{\mu,j}^{-1}r_j)^*
\preceq
(C_n^{\rm res})^2m_j^{-2n}I.
\]

This identifies the missing estimate more precisely than “make the residual small”: the residual must be small **relative to the corresponding complement spectral scales**.

## 3. Why this certificate supplies exactly the required rate

### The ground upper bound has a noncircular Schur certificate

In the decomposition
\(\mathbb C\widehat q_j\oplus\widehat q_j^\perp\),
\[
K_j-\mu_jI
=
\begin{pmatrix}
a_j-\mu_j&r_j^*\\
r_j&B_{\mu,j}
\end{pmatrix}.
\tag{8}
\]
When M1 holds, completing the square gives a congruence to
\[
\operatorname{diag}(\sigma_j,B_{\mu,j}).
\]
Therefore,
\[
B_{\mu,j}>0
\quad\Longrightarrow\quad
\bigl[\lambda_{0,j}\le\mu_j\bigr]
\iff
\bigl[\sigma_j\le0\bigr].
\tag{9}
\]

There is also an explicit witness. Put
\[
x_j=B_{\mu,j}^{-1}r_j,\qquad
v_j=\widehat q_j-x_j.
\]
Then
\[
\|v_j\|^2=1+\|x_j\|^2,
\qquad
v_j^*(K_j-\mu_jI)v_j=\sigma_j.
\]
Hence M2 certifies
\[
\lambda_{0,j}
\le
\frac{v_j^*K_jv_j}{\|v_j\|^2}
=
\mu_j+\frac{\sigma_j}{1+\|x_j\|^2}
\le\mu_j.
\tag{10}
\]
No ground vector is used to construct this witness.

Furthermore, M1 and interlacing imply
\[
\lambda_{1,j}\ge\mu_j+d_j>\mu_j\ge\lambda_{0,j}.
\tag{11}
\]
Thus **a proved cofinal M1–M2 certificate would itself prove eventual simplicity of the full-\(K_j\) ground state**. This is the same finite simplicity mechanism used in `INDEPENDENT_ENERGY_SHIFT.md`; extending its hypotheses to the selected tail remains unproved. 

### The exact angle identity exposes the rate requirement

Choose a unit full-ground eigenvector and write
\[
u_j=c_j\widehat q_j+w_j,\qquad
w_j\perp\widehat q_j.
\]
Under M1–M2, \(c_j\ne0\). Set
\[
\Delta\mu_j=\mu_j-\lambda_{0,j}\ge0.
\]
The projected eigen-equation gives
\[
w_j=-c_j(B_{\mu,j}+\Delta\mu_j I)^{-1}r_j.
\tag{12}
\]
Consequently, with
\[
\eta_j=\|(B_{\mu,j}+\Delta\mu_j I)^{-1}r_j\|,
\]
unit normalization yields the **exact** identity
\[
\alpha_j=\frac{\eta_j}{\sqrt{1+\eta_j^2}}.
\tag{13}
\]
Since \(B_{\mu,j}>0\),
\[
\eta_j\le R_j:=\|B_{\mu,j}^{-1}r_j\|,
\qquad
\alpha_j\le\frac{R_j}{\sqrt{1+R_j^2}}\le R_j.
\tag{14}
\]
This is the finite independent-energy estimate, not a decay statement by itself. 

Now M3 gives \(R_j\le C_n^{\rm res}m_j^{-n}\) eventually for every integer \(n\). For any fixed \(H\ge0\), choose an integer \(n>H/2\). Then
\[
0\le W_H(m_j)\alpha_j
\le
C_n^{\rm res}m_j^{H/2-n}\sqrt{\log m_j}
\longrightarrow0.
\tag{15}
\]
That proves T7 and, with the already-paid source error, discharges this norm-route tracking estimate.

**This is a proof of the certificate’s sufficiency, not a proof that the original CCM source satisfies M1–M3.**

## 4. Demonstrated nonimplication of the existing estimates

T5 bounds
\[
z(E_0,E_4)-z(c_0,c_4)
\quad\text{and the selected infinite tail}.
\]
The residual requiring control is instead
\[
r_j=
\frac{1}{Z_j}(K_j-a_jI)z(c_{0,j},c_{4,j}).
\tag{16}
\]
The reviewed transfer estimates do not bound this vector after applying \(B_{\mu,j}^{-1}\). Setting the row error to zero makes T1 exact, but does not improve the reference angle at all. 

The following exact calculation shows why the existing results, **used as black-box inequalities**, cannot supply the missing rate. It is an abstract logical countermodel, **not a CCM source counterexample and not outcome B**.

For \(m_j\ge2\), put
\[
\beta_j=m_j^{-1},\qquad
c_j=\sqrt{1-\beta_j^2},\qquad
s_j=e^{-m_j}.
\]
On a two-dimensional block define
\[
\widetilde q_j=e_1,\qquad
\widetilde K_j
=
s_j^2I+s_j
\begin{pmatrix}
\beta_j^2&\beta_jc_j\\
\beta_jc_j&c_j^2
\end{pmatrix}.
\tag{17}
\]
Its exact, simple ground pair is
\[
\widetilde\lambda_{0,j}=s_j^2>0,
\qquad
\widetilde u_j=(c_j,-\beta_j)^T.
\]
The other eigenvalue is \(s_j^2+s_j\). Additional diagonal eigenvalues \(s_j^2+s_j\) can be adjoined to obtain dimension \(2m_j+1\) without changing the ground or the calculation.

Choose the explicit independent cut
\[
\widetilde\mu_j=s_j^2+s_j/4.
\]
Then
\[
\widetilde B_{\mu,j}
=s_j(3/4-\beta_j^2)
\ge s_j/2>0
\]
on the nontrivial complementary block, while the adjoined directions have complement eigenvalue \(3s_j/4\). Thus the independent spectral hypotheses hold on the entire tail.

Nevertheless,
\[
\widetilde r_j=s_j\beta_jc_j e_2,
\qquad
\|\widetilde r_j\|\le e^{-m_j}/m_j,
\tag{18}
\]
so the **unpreconditioned residual already decays exponentially**, whereas
\[
\widetilde R_j
=
\frac{\beta_jc_j}{3/4-\beta_j^2}
\sim\frac{4}{3m_j}\longrightarrow0,
\tag{19}
\]
and the exact angle is
\[
\widetilde\alpha_j
=
\|(I-\widetilde u_j\widetilde u_j^*)e_1\|
=\beta_j=\frac1{m_j}.
\tag{20}
\]
For the fixed exponent \(H=2\),
\[
W_2(m_j)\widetilde\alpha_j
=\sqrt{\log m_j}\longrightarrow\infty.
\tag{21}
\]

Finally, take the selected and reference rows equal, and scale their common norm to satisfy the T5 lower bound. Then \(E_j/Z_j=0\), so all the source-error upper bounds are satisfied exactly. The center coefficient of the normalized row is \(1\), so a fixed positive center floor is also available eventually.

Thus even the combination
\[
\begin{gathered}
E_j/Z_j=0,\qquad
\text{cofinal independent spectral cuts},\\
\|r_j\|\text{ exponentially small},\qquad
R_j\to0
\end{gathered}
\]
does **not**, as a collection of inequalities, imply T7.

The calculation does not decide what the additional literal CCM structure enforces. It demonstrates exactly why a new **source-specific relative-residual estimate such as M3** is required rather than another use of T1/T5.

## 5. Why this is neither a lower-bound verdict nor a G1 closure

The four reference-row computations use the full matrix for the reported angles, but remain finite numerical diagnostics. They supply neither an unbounded admitted sequence with a proved weighted lower bound nor cofinal simplicity/ground identification. The README explicitly records those limitations. 

Also, slow decay of a chosen \(R_j\) is not automatically slow decay of \(\alpha_j\). Diagonalizing \(B_{\mu,j}\) in (12) gives
\[
\frac{R_j}{1+\Delta\mu_j/d_j}
\le\eta_j\le R_j,
\]
and therefore
\[
\frac{R_j}{
\sqrt{(1+\Delta\mu_j/d_j)^2+R_j^2}}
\le\alpha_j
\le
\frac{R_j}{\sqrt{1+R_j^2}}.
\tag{22}
\]
A lower-bound argument through \(R_j\) would consequently need suitable control of the energy overshift relative to the complement floor, in addition to an actual lower bound. The existing upper estimate cannot be reversed by assertion.

For G1, the distinction is precise: **if** M1–M2 were proved cofinally, they would discharge eventual full-ground simplicity. They have not been proved cofinally here. Evenness, the odd-sector requirements, and their compatibility with the zero-set consumer are separate obligations; no parity conclusion is supplied by the rate calculation.

**Final adjudication:** **C.** The first missing source-specific supplier is the cofinal certificate M1–M3 on the original \(K_j\) and \(\widehat q_j=z(c_0,c_4)/Z_j\): independently certified cuts, full-complement positivity, and an all-power bound on
\[
\boxed{
R_j^2
=
r_j^*B_{\mu,j}^{-2}r_j.
}
\]
The source-transfer error is conditionally paid. The actual reference-angle tail rate is neither proved nor refuted. No failure of Route B, no G1/G3 closure, and no RH claim follows from this verdict.