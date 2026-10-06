# Proshka answer4: exact inline source

Chat Proof of CCM Growth, 6ac54396-d878-83eb-ae29-35d2bdd2262b.
Question4: JOINT_HILBERT_AUDIT_2026-10-06.md.
Assistant item 6b303390-c409-40be-9236-a105335dc7bf. Complete source retrieved 2026-10-06 around 20:53 UTC.
Supplement not retrieved; citation placeholders require primary-source checks.

Ы — **the signed-kernel attempt gives a common-cell bulk theorem, but does not yet control the bottom eigenvalue.**

**[COFINAL_FAMILY | PAPER]** On every sufficiently late original cell, a source-defined subspace of dimension at least
\[
2m+1-C\frac{m}{(\log m)^5}
\]
satisfies the lower bound
\[
W(f)\ge -C(\log m)^{10}\log\log m\,\|f\|^2.
\]
The same subspace works for every terminal exponent \(\eta>0\).

More importantly, the complementary directions and **all their coupling to that subspace** are retained in an exact **Schur complement**—the matrix left after eliminating a proved positive block. Its dimension is \(O(m/(\log m)^5)\). Its sign remains unsupplied.

**This is not a new bound for \(\lambda_{\min}(K_m)\), and no good subsequence for the full matrix is claimed.**

:chatgpt-content-reference{index="5"}[Complete PAPER verdict, including the machine-readable header, estimates, and dependency ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q04.md)

## 1. The actual source supplies a signed Gram kernel

**[FINITE_CELL | PAPER]**

Write
\[
\mathsf H_m(r)=\mathsf S(r)-\mathsf T.
\]
The accepted matrix identities give
\[
K_m=\mathsf H_m(0)+\mathcal E_m,
\qquad
\|\mathcal E_m\|\le C_0:=c_A+28.
\tag{1}
\]
Here
\[
\mathcal E_m=
\bigl(D_{\rm arch}-\operatorname{diag}a(\omega_j)\bigr)
-c_AI+2P_m(R+R^*)P_m.
\]
Thus the **actual** \(h_j\) and \(d_j\), including their cross terms, remain coupled through the original \(K_m\). This uses the full CCM source, with \(\lambda=\sqrt m\), \(N=m\), not its fixed-window lower-bound proposition. :chatgpt-content-reference{index="0"}

For the original centered carrier,
\[
f(t)=\sum_{j=-m}^{m}c_j\psi_j(t),
\qquad
\|f\|_2=\|c\|_2,
\]
the transform is exactly
\[
M_{\psi_j}(w)
=\frac{2\sinh(wL/2)}{\sqrt L\,(w+i\omega_j)},
\qquad \omega_j=\frac{2\pi j}{L}.
\tag{2}
\]
At a coincident critical zero and mode frequency, this means the removable limit, equivalently the defining integral.

Use the accepted full signed zero formula
\[
W(f)=\sum_w r_w M_f(w)\overline{M_f(w^\dagger)},
\qquad w^\dagger=-\overline w.
\tag{3}
\]
For each distinct \(w=\delta+i\gamma\) with \(\delta>0\), set
\[
p_w(f)=\frac{M_f(w)+M_f(w^\dagger)}{\sqrt2},
\qquad
b_w(f)=\frac{M_f(w)-M_f(w^\dagger)}{\sqrt2}.
\]
Then
\[
2\Re\!\left(M_f(w)\overline{M_f(w^\dagger)}\right)
=|p_w(f)|^2-|b_w(f)|^2.
\tag{4}
\]

Define the positive **Gram matrix**—a matrix formed from squared linear functionals—by
\[
\langle c,\mathcal G_mc\rangle
=
\sum_{\Re w=0}r_w|M_f(w)|^2
+
\sum_{\Re w>0}r_w|p_w(f)|^2.
\]
Both signs of \(\gamma\) are included. Consequently,
\[
\boxed{
W(f)=\langle c,\mathcal G_mc\rangle
-\sum_{\Re w>0}r_w|b_w(f)|^2,
\qquad \mathcal G_m\succeq0.
}
\tag{5}
\]

This kernel is produced from the signed source formula, **not from assumed positivity of the Pick matrix**. The important coupling is that only the **difference row** \(b_w\) is negative; the sum row stays positive. I do not replace the pair by two unrelated absolute-value estimates.

The sign control is immediate: transform values \(1,-1\) give a vanishing positive square and contribution \(-2\). That is an algebraic control, not an assertion that such a source zero exists.

### The endpoint-jumping carrier is admissible

For each fixed carrier vector, integration by parts inside the interval gives
\[
M_f(\delta+i\gamma)=O_f((1+|\gamma|)^{-1})
\]
uniformly for \(|\delta|\le1/2\) at large ordinate. Zero counting therefore makes the square series in (5) absolutely convergent.

To extend the smooth explicit formula, mollify the zero extension. Its Fourier transform is \(O_f((1+|\xi|)^{-1})\), while the archimedean multiplier is \(O(\log(2+|\xi|))\). Dominated convergence gives convergence in the supplied \(E\)-norm. On the zero strip,
\[
M_{f*\rho_\epsilon}=M_fM_{\rho_\epsilon},
\qquad |M_{\rho_\epsilon}(w)|\le e^{\epsilon/2},
\]
so the zero side converges as well. **No claim that a general zero-extended carrier vector belongs to \(H^1(\mathbb R)\) is used.**

## 2. Near-line negative rows have a simultaneous norm bound

**[COFINAL_FAMILY | PAPER]**

First retain a parameter \(0<\alpha\le1/16\), and put
\[
\theta=\frac{\alpha}{4},\qquad
T=m^{1+\theta},\qquad
J=\left\lceil\frac1\theta\right\rceil.
\tag{6}
\]
Here \(J\) is an integer derivative order; \(R\) remains the original causal operator.

Fix an absolute \(C_Z\) large enough that
\[
\sum_{|\gamma-u|\le1}r_w\le C_Z\log(|u|+4),
\tag{7}
\]
and
\[
\sum_{\substack{\Re w>0\\|\gamma|>T}}
r_w|\gamma|^{-p}
\le C_ZT^{1-p}\log(T+4),
\qquad T\ge3,\ p\ge2.
\tag{8}
\]
The first follows by differencing HSW Corollary 1.2. Partial summation gives the second, uniformly in \(p\ge2\). Neither zero spacing nor simplicity is assumed. :chatgpt-content-reference{index="1"}

Take disks of radius \(s=1/L\) around zeros with
\[
|\Re w|\le\alpha,\qquad |\Im w|\le T.
\]
Subharmonicity gives
\[
|M_f(w)|^2\le
\frac1{\pi s^2}\int_{|z-w|<s}|M_f(z)|^2\,dA(z).
\]
The multiplicity-weighted overlap of these disks is \(O(\log(T+4))\), by (7). Also, Plancherel gives
\[
\begin{aligned}
\int_{\mathbb R}|M_f(\sigma+it)|^2\,dt
&=2\pi\int_{-L/2}^{L/2}e^{2\sigma x}|f(x)|^2\,dx\\
&\le2\pi e^{\alpha L+1}\|f\|^2,
\qquad |\sigma|\le\alpha+1/L.
\end{aligned}
\]
Therefore
\[
\boxed{
\sum_{\substack{|\Re w|\le\alpha\\|\Im w|\le T}}
r_w|M_f(w)|^2
\le B_{\rm near}\|f\|^2,
}
\tag{9}
\]
where, after fixing the absolute counting constant,
\[
B_{\rm near}
=4eC_Z(\alpha L^2+L)\log(T+4)m^\alpha.
\tag{10}
\]

Since
\[
|b_w(f)|^2
\le |M_f(w)|^2+|M_f(w^\dagger)|^2,
\]
this pays all negative rows with
\[
0<\Re w\le\alpha,\qquad |\Im w|\le T.
\]

This is a **single operator-form estimate for every complex \(f\)** on that cell. It is not a family of scalar good-cell statements. Zeros outside this narrow strip have not been assumed absent; they remain below.

## 3. Every higher-zero contribution is paid by endpoint rows plus a small remainder

**[COFINAL_FAMILY | PAPER]**

The original phases give
\[
\eta_k(f):=f^{(k)}(L/2)=f^{(k)}(-L/2)
=\frac1{\sqrt L}\sum_{j=-m}^{m}c_j(i\omega_j)^k.
\tag{11}
\]
These are the **actual boundary traces**, not zero boundary conditions.

Repeated integration by parts inside the interval gives
\[
M_f(w)=
2\sinh(wL/2)
\sum_{k=0}^{J-1}\frac{(-1)^k\eta_k(f)}{w^{k+1}}
+\frac{(-1)^J}{w^J}M_{f^{(J)}}(w).
\tag{12}
\]
Let \(\Omega=2\pi m/L\). Orthogonality gives the exact carrier estimate
\[
\|f^{(J)}\|_2\le\Omega^J\|f\|_2.
\]
Thus the remainder \(E_w(f)\) in (12) satisfies
\[
|E_w(f)|^2
\le L\sqrt m\,\Omega^{2J}|\gamma|^{-2J}\|f\|^2.
\tag{13}
\]

For the finite endpoint sum \(A_w(f)\),
\[
|A_w(f)|^2
\le4\sqrt m\,J
\sum_{k<J}|\eta_k(f)|^2|\gamma|^{-2k-2}.
\]
Apply this to both members of the pair, and retain their difference using
\[
|b_w|^2
\le
2(|A_w|^2+|A_{w^\dagger}|^2)
+2(|E_w|^2+|E_{w^\dagger}|^2).
\]
Together with the unconditional tail-moment bound (8), this proves
\[
\boxed{
\sum_{\substack{\Re w>0\\|\gamma|>T}}
r_w|b_w(f)|^2
\le \mathcal J_{\alpha,m}(f)+B_{\rm tail}\|f\|^2,
}
\tag{14}
\]
where
\[
\mathcal J_{\alpha,m}(f)
=
16C_ZJ\sqrt m\,\frac{\log(T+4)}T
\sum_{k<J}\frac{|\eta_k(f)|^2}{T^{2k}}
\tag{15}
\]
is a positive form of rank at most \(J\), and
\[
B_{\rm tail}
=
4C_ZL\sqrt m\,\Omega^{2J}T^{1-2J}\log(T+4).
\tag{16}
\]

The endpoint contribution has **not** disappeared: it is retained as the explicit finite-rank form (15). All zeros above \(T\), including every multiplicity, have been covered.

The boundaries of the split are also fixed: \(|\gamma|=T\) belongs to the low part; \(\Re w=\alpha\) belongs to the near-line part.

## 4. The remaining rows have an unconditional sublinear rank

**[COFINAL_FAMILY | PAPER]**

Define \(\mathcal L_{\alpha,m}\) by stacking
\[
\sqrt{r_w}\,b_w
\quad
(\Re w>\alpha,\ |\Im w|\le T)
\]
and the \(J\) explicitly weighted endpoint rows in (15). Then
\[
\|\mathcal L_{\alpha,m}c\|^2
=
\sum_{\substack{\Re w>\alpha\\|\Im w|\le T}}
r_w|b_w(f)|^2+\mathcal J_{\alpha,m}(f).
\tag{17}
\]
Its rows are given by (2), (4), and (11). **Its definition does not use a negative eigenvector or the desired PSD conclusion.**

Put
\[
\beta_{\alpha,m}=B_{\rm near}+B_{\rm tail},
\qquad
\varepsilon_{\alpha,m}=\beta_{\alpha,m}+C_0.
\]
Equations (5), (9), and (14) now give the full-space inequality
\[
\boxed{
K_m\succeq
\mathcal G_m-\mathcal L_{\alpha,m}^*\mathcal L_{\alpha,m}
-\beta_{\alpha,m}I.
}
\tag{18}
\]
Consequently, directly against the requested \(q_j\),
\[
\boxed{
\mathsf S(r)-\mathsf T
\succeq
\mathcal G_m+(r-\varepsilon_{\alpha,m})I
-\mathcal L_{\alpha,m}^*\mathcal L_{\alpha,m}.
}
\tag{19}
\]

### The primary density theorem and its hypotheses

Chourasiya–Simonič, Corollary 1, gives
\[
\begin{aligned}
N(\sigma,T)\le{}&
8.185T^{3(1-\sigma)/(2-\sigma)}
(\log T)^{(7-5\sigma)/(2-\sigma)}\\
&+9.461(\log T)^2+167.8\log T
\end{aligned}
\tag{20}
\]
for
\[
\tfrac12\le\sigma\le\tfrac58,
\qquad T\ge3\cdot10^{12},
\]
with multiplicities. This is an unconditional density estimate; the fixed height threshold is not an RH premise. :chatgpt-content-reference{index="2"}

Use \(\sigma=1/2+\alpha\). Both signs of the ordinate give at most \(2N(1/2+\alpha,T)\) negative source rows. Thus
\[
\begin{aligned}
\operatorname{rank}\mathcal L_{\alpha,m}
\le{}&
J+16.37T^{p_\alpha}(\log T)^3\\
&+18.922(\log T)^2+335.6\log T,
\qquad
p_\alpha=\frac{3/2-3\alpha}{3/2-\alpha}.
\end{aligned}
\tag{21}
\]
The exponent calculation is
\[
(1-\alpha)-(1+\alpha/4)p_\alpha
=
\frac{\alpha(1+14\alpha)}
{8(3/2-\alpha)}>0.
\tag{22}
\]
For fixed \(\alpha\), this gives rank
\[
O_\alpha(m^{1-\alpha}L^3)+J.
\]

### Uniformity permits a stronger tuning

Now use the **uniform explicit estimates**, not substitution into an \(O_\alpha\) statement. Set
\[
\boxed{
\alpha_m=\frac{8\log L}{L},
\qquad
T=mL^2,
\qquad
J=\left\lceil\frac{L}{2\log L}\right\rceil.
}
\tag{23}
\]
For sufficiently large \(L\), \(\alpha_m\le1/16\).

Since \(m^{\alpha_m}=L^8\), (10) gives
\[
B_{\rm near}\le C L^{10}\log L.
\tag{24}
\]
For \(L\ge2\pi\),
\[
\frac{\Omega}{T}=\frac{2\pi}{L^3}\le L^{-2},
\qquad
2J\ge\frac{L}{\log L},
\]
so
\[
(\Omega/T)^{2J}\le m^{-2}.
\]
Equation (16) therefore gives
\[
B_{\rm tail}\le C m^{-1/2}L^4=o(1).
\tag{25}
\]

There is **no uncontrolled constant from the increasing derivative order**: these are derivatives of the original trigonometric polynomial, with the exact \(\Omega^J\) estimate, not derivatives of an introduced cutoff.

Finally, (22) gives
\[
T^{p_{\alpha_m}}\le m^{1-\alpha_m}=\frac m{L^8}.
\]
Using the uniform density bound (21),
\[
\boxed{
d_m:=\operatorname{rank}\mathcal L_m
\le C\frac m{L^5}
}
\tag{26}
\]
eventually, with the \(O(L^2)+J\) terms absorbed. This consequence uses precisely the uniformity in \(\sigma\) of the imported density theorem. :chatgpt-content-reference{index="3"}

Combining the estimates,
\[
\boxed{
\mathsf S(r)-\mathsf T
\succeq
\mathcal G_m+(r-\varepsilon_m)I-\mathcal L_m^*\mathcal L_m,
\qquad
\varepsilon_m\le C L^{10}\log L.
}
\tag{27}
\]

In particular,
\[
\#\{k:\lambda_k(K_m)<-C L^{10}\log L\}
\le C\frac m{L^5}.
\tag{28}
\]
This is a **spectral-count bound**, not a bound on the most negative eigenvalue.

For the requested unsmoothed operator, the same calculation yields, for every original \(f\),
\[
\boxed{
\begin{aligned}
\langle f,D_Ff\rangle
\le{}&D_{\rm arch}(f)
+(\beta_m+8+2L-c_A)\|f\|^2\\
&+\|\mathcal L_mc\|^2-\langle c,\mathcal G_mc\rangle.
\end{aligned}
}
\tag{29}
\]
No inverse estimate for \(F\), stripping of \(I-R\), or even-vector restriction appears.

## 5. Neighboring bands are glued without dropping their cross terms

**[FINITE_CELL | PAPER]**

Partition the original index interval into any contiguous bands \(I_b\), including the unresolved middle. Write
\[
c=\sum_b\iota_bc_b,
\]
where \(\iota_b\) is the coordinate embedding.

Let \(\mathcal A_m\) be the source row operator defining
\(\mathcal G_m=\mathcal A_m^*\mathcal A_m\). Equation (27) gives
\[
\boxed{
\begin{aligned}
\sum_{b,b'}
\langle c_b,\mathsf H_m(r)_{I_bI_{b'}}c_{b'}\rangle
\ge{}&(r-\varepsilon_m)\sum_b\|c_b\|^2\\
&+\left\|\sum_b\mathcal A_m\iota_bc_b\right\|^2
-\left\|\sum_b\mathcal L_m\iota_bc_b\right\|^2.
\end{aligned}
}
\tag{30}
\]

**Neither square is replaced by a sum of blockwise squares.** All neighboring-band and separated-band cross terms remain. There is no factor depending on the number of bands or on \(2m+1\).

The single common regular condition is
\[
\sum_b\mathcal L_m\iota_bc_b=0.
\tag{31}
\]
It does not require the individual block contributions to vanish separately.

Consequently, for any contiguous block \(I\), the bound holds on a subspace of dimension at least \(|I|-d_m\). For example, it controls all jointly admissible directions in the macroscopic middle block
\[
I=\{\lfloor m/4\rfloor,\ldots,\lfloor3m/4\rfloor\},
\]
apart from at most \(d_m\) linear constraints. The same map controls combinations across neighboring blocks.

**It does not prove that every direction in that contiguous block is good.** The new estimate concerns an explicitly source-defined large subspace and its coherently glued combinations.

## 6. The remaining sign is an exact smaller Schur problem

**[COFINAL_FAMILY | PAPER]**

Set
\[
\mathcal R_m=\ker\mathcal L_m,
\qquad
\mathcal E_m^{\rm src}=\operatorname{ran}\mathcal L_m^*
=\mathcal R_m^\perp.
\]
For \(r\ge2\varepsilon_m\), write the **actual**
\(\mathsf H_m(r)\) in this orthogonal decomposition:
\[
\mathsf H_m(r)=
\begin{pmatrix}
A_m(r)&B_m(r)\\
B_m(r)^*&C_m(r)
\end{pmatrix}.
\]
Equation (27) proves
\[
A_m(r)\succeq(r-\varepsilon_m)I,
\qquad
\|A_m(r)^{-1}\|\le\frac1{r-\varepsilon_m}.
\tag{32}
\]

This inverse belongs to a **proved positive regular block**, not to \(F\). No \(q_j\) is divided by. Zero or negative original diagonal slacks are not silently passed.

Completion of the square now gives
\[
\boxed{
\mathsf H_m(r)\succeq0
\iff
\mathfrak S_m(r):=
C_m(r)-B_m(r)^*A_m(r)^{-1}B_m(r)\succeq0.
}
\tag{33}
\]
The remaining matrix has dimension at most \(Cm/L^5\).

Negative eigenvectors are **not** asserted to lie in \(\mathcal E_m^{\rm src}\). Their components in the regular space are exactly why the correction \(B_m^*A_m^{-1}B_m\) must remain.

The first unsupplied inequality is now
\[
\boxed{
\forall\eta>0\ \exists C_\eta\
\exists\text{ arbitrarily large original }m:
\qquad
\mathfrak S_m(C_\eta m^\eta)\succeq0.
}
\tag{34}
\]
Since \(\varepsilon_m\) is polylogarithmic, the shift exceeds \(2\varepsilon_m\) eventually.

The regular-block estimate, its inverse bound, its dimension, and its endpoint budget are proved. **The sign in (34) is not.** Zero density bounds the number of exceptional rows; it does not bound their signed effect after coupling.

### A discriminator that uses a full-carrier correction

For \(v\in\mathcal E_m^{\rm src}\) and \(y\in\mathcal R_m\), define
\[
J_r(v,y)=
\langle v,C_mv\rangle
+2\Re\langle y,B_mv\rangle
+\langle y,A_my\rangle,
\qquad e=A_my+B_mv.
\]
The exact identity
\[
J_r(v,y)
=
\langle v,\mathfrak S_m(r)v\rangle
+\langle e,A_m(r)^{-1}e\rangle
\]
gives
\[
\boxed{
J_r(v,y)-\frac{\|e\|^2}{r-\varepsilon_m}
\le
\langle v,\mathfrak S_m(r)v\rangle
\le J_r(v,y).
}
\tag{35}
\]

A certified negative upper envelope for \(J_r(v,y)\) is a genuine **full-carrier** violation on that cell. A zero-consistent result must refine the residual \(e\) and its budget in (35). This is not a two-mode test, and passing one trial does not certify the matrix.

The registered prediction is confirmed: the source supplies a simultaneous better-scale regular block, but not full positivity. The earlier whole-matrix floor, SP, and RH retain their previous status.

**Next mathematical step:** estimate the actual exceptional Schur form (34), keeping the coupling between its off-line-zero rows and endpoint-jet rows. Use the full-carrier residual envelope (35) as the first discriminator; the regular block and the complete tail budget no longer need to be conjectured.
