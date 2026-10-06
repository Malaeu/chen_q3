# Proshka signed even tail — received answer 3/10

Source: ChatGPT connector read_thread; chat 6aba5f5a-f804-83ed-a667-68147ee00f59.
Observed turn status: completed. Message ID: cc141240-784f-4b4d-9f64-be6c3d476f42.
Received 2026-10-06. Verbatim inline answer follows. The supplemental Markdown was subsequently downloaded through its browser preview and saved unchanged as PROSHKA_G1_SIGNED_EVEN_TAIL_REDUCTION_2026-10-06.md; SHA-256 e4f7b1542f11a75136597e20fba8e5ab97d38ccaa4d060120ce2da1ba2b91177. Inline opaque references remain quoted author markup. Mathematical claims are candidates pending independent verification.

Ы. **The window obstruction can be paid for the archimedean term.** There is an exact positive boundary correction in the even sector; we do not need to pretend that the whole-line error is high-pass.

I also obtained a **uniform lower bound for the discarded Fourier mass of the entire two-column plane**, including combinations that cancel near the first omitted frequency. Together, these give a quantitative signed reduction in which the exterior error is negligible at the required scale.

**The remaining prime-correlation comparison is not proved. Therefore this is not yet a cofinal counterexample to the prescribed \(U_m\), nor a proof of its positive secular sign.** Below are the new estimates and the precise arithmetic inequality that remains.

## 1. Keep the original plane and split its error correctly

Throughout,
\[
m=m_j,\qquad N=m,\qquad L=\log m,\qquad
a=L/2,\qquad h=\frac{2\pi}{L},\qquad \Omega=hm.
\]

For \(z=(z_0,z_2)\in\mathbb C^2\), put
\[
g_z=z_0G+z_2G'',\qquad
f_{m,z}=\Pi_m(g_z|_{[-a,a]}),
\]
with the original zero-extended Fourier synthesis. The prescribed quantity remains
\[
U_m=\inf_{z\ne0}
\frac{z^*\mathsf H_mz}{z^*\mathsf G_mz},
\qquad
\mathsf H_m=V_m^*K_mV_m,\quad
\mathsf G_m=V_m^*V_m.
\]
No actual ground vector, different trial plane, or changed normalization enters. :chatgpt-content-reference{index="0"}

Separate the error into
\[
r_{m,z}=\mathbf1_{[-a,a]}g_z-f_{m,z},
\qquad
o_{m,z}=\mathbf1_{\mathbb R\setminus[-a,a]}g_z.
\]
Thus
\[
f_{m,z}-g_z=-(r_{m,z}+o_{m,z}).
\]

The periodic representative of \(r_{m,z}\) has precisely the omitted coefficients
\[
c_n(g_z),\qquad |n|>m.
\]
Its zero extension is **not** asserted to be whole-line high-pass.

Write
\[
E_m(z)=\|r_{m,z}\|_2^2=z^*\mathsf E_mz.
\]

The accepted odd envelope \(\mathcal B_m\) and window comparison \(\Gamma_m\) are retained unchanged. Their derivation is not repeated. 

## 2. Exact archimedean lower bound, including the window

Define the actual archimedean difference kernel
\[
J(s)=\frac{e^{-s/2}}{1-e^{-2s}}
=\sum_{k=0}^{\infty}e^{-\beta_ks},
\qquad
\beta_k=2k+\frac12,
\]
and
\[
\mathfrak D(v)=
\int_0^\infty J(s)\|v-\tau_sv\|_2^2\,ds.
\]

### Even periodization identity

**[ABSTRACT | PAPER]** Let \(q\) be an even, possibly complex-valued, periodic \(H^1\) function of period \(L\), and let \(v=\mathbf1_{[-L/2,L/2]}q\). If \(d_n\) are its orthonormal Fourier coefficients, then
\[
\boxed{
\mathfrak D(v)
=
\sum_{n\in\mathbb Z}\mathfrak a(\omega_n)|d_n|^2
+\mathfrak I_L(v),
}
\tag{1}
\]
where
\[
\mathfrak a(\omega)
=
2\sum_{k=0}^{\infty}
\frac{\omega^2}{\beta_k(\beta_k^2+\omega^2)}
\tag{2}
\]
and
\[
\boxed{
\mathfrak I_L(v)
=
2\sum_{k=0}^{\infty}
\frac{\left|\displaystyle\int_{-L/2}^{L/2}
v(t)\cosh(\beta_kt)\,dt\right|^2}
{e^{\beta_kL}-1}
\ge0.
}
\tag{3}
\]

Here **periodization** means repeating the function with period \(L\); the correction \(\mathfrak I_L\) is the exact difference between periodic and zero-extended geometry.

**Proof.** First use a single exponential kernel. For \(|u|\le L\),
\[
\sum_{\ell\ne0}e^{-\beta|u+\ell L|}
=
\frac{2\cosh(\beta u)}{e^{\beta L}-1}.
\tag{4}
\]
Both difference energies have the same norm term \(2\|v\|_2^2/\beta\). Their difference is the quadratic form of these image terms. The addition formula for \(\cosh\) gives
\[
\begin{aligned}
\mathfrak D_\beta(v)-\mathfrak D_{\beta,\mathrm{per}}(q)
={}&
\frac{2}{e^{\beta L}-1}
\left(
\left|\int v(t)\cosh(\beta t)\,dt\right|^2
-
\left|\int v(t)\sinh(\beta t)\,dt\right|^2
\right).
\end{aligned}
\]
The second moment is exactly zero by evenness. Periodic Parseval gives
\[
\mathfrak D_{\beta,\mathrm{per}}(q)
=
\sum_n
\frac{2\omega_n^2}{\beta(\beta^2+\omega_n^2)}
|d_n|^2.
\]
Summing over \(\beta_k\) proves (1). The image series converges: its \(k\)-th term is at most \(2\|q\|_\infty^2/\beta_k^2\). Thus the boundary correction is neither omitted nor assigned a sign by analogy.

The relevant literature alias is **reflection positivity**—positivity after reflecting one argument of a kernel. Exponential kernels and their periodic versions are explicit examples in Neeb–Ólafsson, Example 1.2(b)–(c). The particular window identity above is derived here, rather than imported as a theorem about CCM. :chatgpt-content-reference{index="2"}

Each summand in (2) increases with \(|\omega|\). Comparison of the \(\beta\)-lattice with an integral also gives
\[
\boxed{
\mathfrak a(\omega)
\ge\frac12\log(1+4\omega^2).
}
\tag{5}
\]

Apply (1) to the actual even periodic tail. Its coefficients vanish for \(|n|\le m\), so
\[
\boxed{
\mathfrak D(r_{m,z})
\ge
\mathfrak a(\Omega)E_m(z)
+\mathfrak I_L(r_{m,z}).
}
\tag{6}
\]

**This resolves the high-pass objection for this archimedean estimate.** It does not resolve the arithmetic term.

Evenness is essential. For an odd function, the image contribution in the proof has the opposite sign. An exact sine control below detects that distinction.

## 3. A lower mass bound uniform in both columns

The next result supplies a nonzero scale uniformly in \(z\).

**[COFINAL_FAMILY | PAPER]** There are constants \(c_E>0\) and \(m_E\), independent of \(z\), such that for every integer \(m\ge m_E\),
\[
\boxed{
E_m(z)\ge
c_E T_m^{9/2}\log T_m\,e^{-\pi T_m}
\left(|z_0|^2+T_m^4|z_2|^2\right),
\qquad
T_m=\frac{2\pi(m+1)}L.
}
\tag{7}
\]

This includes an \(m\)-dependent combination chosen to make \(z_0-z_2\omega^2\) small near the cutoff. It is stronger than two separate lower estimates for the individual columns.

### Weighted Hardy moments

The analytic input is the unconditional pair
\[
\int_0^T Z(t)^2\,dt=T\log T+O(T),
\]
\[
\int_0^T Z'(t)^2\,dt
=\frac1{12}T\log^3T+O(T\log^2T).
\tag{8}
\]
These are the specializations \(k=\ell=0\) and \(k=\ell=1\) of Bui–Hall, equation (1), page 1. No hypothesis about the location of all zeta zeros is used. :chatgpt-content-reference{index="3"}

Put \(T=T_m\) and
\[
p(t)=z_0-z_2t^2,\qquad
J_T(z)=\int_1^2|z_0-z_2T^2x^2|^2\,dx.
\]
The corresponding **Gram matrix**, which records the mixed as well as diagonal terms, is
\[
\begin{pmatrix}
1&-7/3\\
-7/3&31/5
\end{pmatrix}.
\]
Its determinant is \(34/45\), and its trace is \(36/5\). Hence
\[
\boxed{
J_T(z)\ge\frac{17}{162}
\left(|z_0|^2+T^4|z_2|^2\right).
}
\tag{9}
\]

Stieltjes integration by parts in (8), for the three weights \(1,x^2,x^4\), now gives uniformly in \(z\)
\[
\|pZ\|_{L^2(T,2T)}^2
=
T\log T
\left[
J_T(z)+
O\!\left(
\frac{|z_0|^2+T^4|z_2|^2}{\log T}
\right)
\right],
\tag{10}
\]
\[
\|pZ'\|_{L^2(T,2T)}^2
=
\frac1{12}T\log^3T
\left[
J_T(z)+
O\!\left(
\frac{|z_0|^2+T^4|z_2|^2}{\log T}
\right)
\right].
\tag{11}
\]
Moreover,
\[
\frac{\|p'Z\|_2}{\|pZ\|_2}=O(T^{-1})
\]
uniformly by (9). Since \(h=2\pi/L\) and \(\log T/L\to1\),
\[
\frac h\pi
\frac{\|(pZ)'\|_2}{\|pZ\|_2}
\le
\frac{2\log T}{L}
\left(\frac1{\sqrt{12}}+o(1)\right)
+O((LT)^{-1})
\le\frac23
\tag{12}
\]
eventually, for every nonzero \(z\).

### The sampling step

For \(F\in H^1\) on an interval divided into cells of length \(h\), let \(P\) be its piecewise-linear interpolant. Poincaré on each cell and the fact that \(P'\) is the cell average of \(F'\) give
\[
\|F-P\|_2\le\frac h\pi\|F'\|_2.
\]
The norm of the interpolant is at most the square root of \(h\) times the sum of squared nodal values. Therefore
\[
\boxed{
\sqrt{h\sum_n|F(t_n)|^2}
\ge
\|F\|_2-\frac h\pi\|F'\|_2.
}
\tag{13}
\]
Both endpoints are included.

The interval \([T,2T]\) has exactly the nodes
\[
hn,\qquad m+1\le n\le2m+2.
\]
All are **omitted coefficients of the original projection**; no matrix carrier has been enlarged.

Applying (12)–(13) yields
\[
h\sum_{n=m+1}^{2m+2}
|p(hn)Z(hn)|^2
\ge
\frac1{18}T\log T\,J_T(z).
\tag{14}
\]

### Return to the full \(G\) and the actual window

The exact source Fourier identity gives
\[
|\widehat G(t)|=A_G(t)|Z(t)|,
\]
\[
A_G(t)=
2(t^2+1/4)\pi^{-1/4}
|\Gamma(1/4+it/2)|.
\]
Stirling’s modulus asymptotic provides a fixed \(c_\gamma>0\) such that
\[
A_G(t)\ge c_\gamma t^{7/4}e^{-\pi t/4}
\]
for sufficiently large \(t\). No asymptotic remainder is differentiated. :chatgpt-content-reference{index="4"}

On \([T,2T]\),
\[
A_G(t)^2\ge c_\gamma^2T^{7/2}e^{-\pi T}.
\]
Using \(hL=2\pi\), equation (14) gives
\[
\sum_{n=m+1}^{2m+2}
\frac{|\widehat{g_z}(hn)|^2}{L}
\ge
\frac{c_\gamma^2}{36\pi}
T^{9/2}\log T\,e^{-\pi T}J_T(z).
\tag{15}
\]

The source derivative bounds already checked in the preceding work imply
\[
\sum_{n=m+1}^{2m+2}
\left|
c_n(g_z)-\frac{(-1)^n}{\sqrt L}\widehat{g_z}(hn)
\right|^2
\le
\frac{C_G}{mL}e^{-\pi m}\|z\|^2.
\tag{16}
\]
This is the actual exterior integral, not a replacement of the window coefficients. The complete derivative-envelope constants are available in the accepted budget record. 

Since \(T=o(m)\), the error norm in (16) is eventually at most half the lower norm in (15), uniformly in \(z\). Equations (9), (15), and the triangle inequality prove (7), for example with
\[
c_E=\frac{17c_\gamma^2}{23328\pi}.
\]

**This is still an \(L^2\) result. Its role is to make subsequent signed error budgets genuinely relative and uniform—not to supply the Weil sign by itself.**

## 4. The full exterior error is negligible relative to that mass

The source’s grouped form is
\[
\mathcal W(v,v)
=
\mathfrak D(v)-c_{\rm ar}\|v\|_2^2
+\mathcal P_{\rm pole}(v,v)
-\mathcal P_{\rm pr}(v,v),
\tag{17}
\]
where
\[
c_{\rm ar}=\gamma+\log(8\pi)+\frac\pi2,
\]
\[
\mathcal P_{\rm pr}(v,v)
=
2\sum_{q\ge2}\frac{\Lambda(q)}{\sqrt q}
\operatorname{Re}C_v(\log q).
\]
The full matrix retains exactly the source sign \(W_{0,2}-W_{\mathbb R}-\mathrm{Prime}\), including the separate diagonal formula. 

For an even complex function,
\[
\mathcal P_{\rm pole}(v,v)
=
2\left|\int v(t)\cosh(t/2)\,dt\right|^2\ge0.
\tag{18}
\]

The accepted radical cancellation, with the conjugate first slot retained, gives
\[
\mathcal W(f_{m,z},f_{m,z})
=
\mathcal W(r_{m,z}+o_{m,z},r_{m,z}+o_{m,z}).
\tag{19}
\]
This is an identity of the full signed form, not positivity. The conjugation correction in the integrated audit is retained. 

A useful new bound is
\[
\boxed{
\left|
\mathcal W(f_{m,z},f_{m,z})
-
\mathcal W(r_{m,z},r_{m,z})
\right|
\le
R_m\|z\|^2,
\qquad
R_m=O_G(me^{-\pi m/2}).
}
\tag{20}
\]

Here is an explicit budget, so the small error is independently checkable. Let
\[
C_0=\|G\|_2^2+\|G''\|_2^2,\quad
C_1=\|G'\|_2^2+\|G'''\|_2^2,
\]
\[
C_\infty=\|G\|_\infty^2+\|G''\|_\infty^2.
\]
Choose the existing fixed source constants
\[
|G^{(k)}(t)|\le D_k^G e^{-(\pi/2)e^{2|t|}},
\]
and set
\[
A_0=(D_0^G)^2+(D_2^G)^2,\qquad
A_1=(D_1^G)^2+(D_3^G)^2.
\]
Define
\[
e_o=\frac{A_0}{\pi m}e^{-\pi m},\qquad
w_o=\frac{A_0}{\pi}e^{-\pi m},
\]
\[
d_o=
\left(
\frac{2A_1}{\pi m}+8A_0+\frac{16A_0}{\pi m}
\right)e^{-\pi m},
\]
\[
d_r=
2C_1+8C_\infty+2C_0\Omega^2
+8C_0\frac{2m+1}{L}+64C_0.
\]
Then a valid choice is
\[
\boxed{
R_m=
2\sqrt{d_rd_o}+d_o+c_{\rm ar}e_o
+26\sqrt{mC_0w_o}+13w_o.
}
\tag{21}
\]

**Why it works.** The exterior estimates give
\[
\|o\|_2^2\le e_o\|z\|^2,\quad
\|e^{|t|}o\|_2^2\le w_o\|z\|^2,\quad
\mathfrak D(o)\le d_o\|z\|^2.
\]
The bounds \(J(s)\le2/s\) for \(s\le1\) and \(J(s)\le2e^{-s/2}\) for \(s\ge1\), with both window jumps retained, give
\[
\mathfrak D(r)\le d_r\|z\|^2.
\]
For the finite synthesis, use
\[
\|f'\|_2\le\Omega\|f\|_2,\qquad
\|f\|_\infty\le\sqrt{\frac{2m+1}{L}}\|f\|_2.
\]

Cauchy–Schwarz in the positive \(\mathfrak D\)-seminorm pays its cross term. The ordinary norm cross term vanishes by disjoint support. Finally,
\[
|\mathcal P_{\rm pr}(v,w)|
<
10\|e^{|t|}v\|_2\|e^{|t|}w\|_2,
\]
\[
|\mathcal P_{\rm pole}(v,w)|
\le\frac83
\|e^{|t|}v\|_2\|e^{|t|}w\|_2.
\]
The first bound sums **every prime power, including those beyond \(m\)**. Applied only to the exterior correction, it is now small enough.

Combining (7) and (20),
\[
\frac{R_m}{c_ET_m^{9/2}\log T_m\,e^{-\pi T_m}}
\longrightarrow0.
\tag{22}
\]
Thus the physical exterior is paid uniformly even in the least favorable two-column direction.

## 5. What remains: an explicit signed arithmetic form

Define the following two Hermitian quadratic forms in \(z\):
\[
\begin{aligned}
\mathcal A_m(z)={}&
\sum_{|n|>m}
\bigl(\mathfrak a(\omega_n)-c_{\rm ar}\bigr)
|c_n(g_z)|^2\\
&+\mathfrak I_L(r_{m,z})
+2\left|\int_{-a}^a
r_{m,z}(t)\cosh(t/2)\,dt\right|^2,
\end{aligned}
\tag{23}
\]
\[
\mathcal P_m(z)=
2\sum_{2\le q\le m}
\frac{\Lambda(q)}{\sqrt q}
C_{r_{m,z}}(\log q).
\tag{24}
\]
Write their matrices as \(\mathsf A_m,\mathsf P_m\).

Equations (1), (17), and (20) prove the **signed matrix estimate**
\[
\boxed{
\left\|
\mathsf H_m-(\mathsf A_m-\mathsf P_m)
\right\|_{\rm op}
\le R_m.
}
\tag{25}
\]

Moreover,
\[
\boxed{
\mathsf A_m\succeq\kappa_m\mathsf E_m,
\qquad
\kappa_m=\mathfrak a(\Omega)-c_{\rm ar},
}
\tag{26}
\]
\[
\boxed{
\mathsf E_m\succeq
\mu_m\operatorname{diag}(1,T_m^4),
\qquad
\mu_m=c_ET_m^{9/2}\log T_m\,e^{-\pi T_m}.
}
\tag{27}
\]
In particular, \(\kappa_m\to+\infty\) and \(R_m/\mu_m\to0\).

The original generalized metric is still present:
\[
\boxed{
U_m\ge
\inf_{z\ne0}
\frac{
z^*(\mathsf A_m-\mathsf P_m)z-R_m\|z\|^2
}{
z^*\mathsf G_mz
}.
}
\tag{28}
\]
The positive image and pole terms in (23) have not been discarded from this comparison.

### A boundary representation for the prime term

There is also an exact representation that separates periodic oscillation from the window boundary.

Put
\[
b_{m,z}(u)=r_{m,z}(a-u),\qquad 0\le u\le L.
\]
For \(0\le s\le L\),
\[
\boxed{
C_r(s)=
\sum_{|n|>m}|c_n(g_z)|^2\cos(\omega_ns)
-
\int_0^s\overline{b_{m,z}(u)}\,b_{m,z}(s-u)\,du.
}
\tag{29}
\]

Indeed, the periodic correlation is \(C_r(s)+C_r(L-s)\); evenness identifies the second summand with the displayed reflected integral. Thus
\[
\boxed{
\begin{aligned}
\mathcal P_m(z)
=2\sum_{2\le q\le m}\frac{\Lambda(q)}{\sqrt q}
\Bigg[
&\sum_{|n|>m}|c_n(g_z)|^2
\cos(\omega_n\log q)\\
&-\int_0^{\log q}
\overline{b_{m,z}(u)}b_{m,z}(\log q-u)\,du
\Bigg].
\end{aligned}
}
\tag{30}
\]

This is a **periodic diagonal minus a boundary Hankel term**: the latter couples \(u\) to \(s-u\), rather than to a translate.

At \(q=m\), both bracketed expressions equal \(E_m(z)\), so the endpoint contribution cancels exactly. This remains true when \(m\) is a prime power. Dropping the reflected term would destroy that cancellation.

The reflected prime integral is **not automatically positive**. For example, outside the source family, take
\[
L=\log4,\qquad r(t)=\cos(10\pi t/L).
\]
At \(s=\log2\), the reflected integral in (29) is exactly
\[
-\frac12\log2.
\]
Thus reflection positivity of the smooth archimedean kernel cannot be transferred to the arithmetic atoms.

A limited part of the prime sum can already be paid:
\[
\left|
2\sum_{q\le Q}\frac{\Lambda(q)}{\sqrt q}C_r(\log q)
\right|
\le4\sqrt Q\log Q\,E_m(z).
\tag{31}
\]
For \(Q=\lfloor\log\Omega\rfloor\), this is \(o(\log\Omega)E_m(z)\). This optional estimate removes a growing initial range of prime powers, but does not settle the remaining signed sum.

## 6. The first missing inequality—and its exact consequence

A budget-complete sufficient inequality on an unbounded original sequence is
\[
\boxed{
\mathsf A_m-\mathsf P_m
\succeq
\bigl(\mathcal B_m+2\Gamma_m+\delta_m\bigr)\mathsf G_m
+R_mI,
\qquad \delta_m>0.
}
\tag{32}
\]

It would give
\[
U_m\ge\mathcal B_m+2\Gamma_m+\delta_m,
\]
and therefore
\[
\widetilde U_m>\mathcal B_m+\Gamma_m.
\]
The already constructed odd vector would then be a genuine negative witness for the prescribed shifted candidate.

A simpler, stronger arithmetic estimate that would suffice is
\[
\boxed{
\mathcal P_m(z)\le
(\kappa_m-1)E_m(z)
\quad\text{for every }z\in\mathbb C^2
}
\tag{33}
\]
on an unbounded sequence. It does not require individual correlations to be negative.

Under (33), equations (25)–(27) imply
\[
\mathsf H_m\succeq(\mu_m-R_m)I.
\]
Projection contraction gives \(\mathsf G_m\preceq C_0I\). Once the numerator is positive,
\[
U_m\ge\frac{\mu_m-R_m}{C_0}
\ge\frac{\mu_m}{2C_0}.
\tag{34}
\]
That lower bound has scale
\[
\text{a polynomial factor}\times
\exp\!\left[-\frac{2\pi^2(m+1)}{\log m}\right].
\]
It dominates both \(\mathcal B_m\) and \(\Gamma_m\), by their accepted rates.

**Neither (32) nor (33) is established here.** The constant margin \(1\) in (33) is not mandatory. Nor is (33) necessary: the positive image and pole terms retained in (32) may compensate a failure of the stronger estimate.

The exact outstanding work is therefore the **signed source-specific prime-correlation estimate (30), at the independently paid budget (32)**. The new derivation does not conceal it in a positive model.

### What the checks establish

The exact symbolic controls passed:

The even cosine gives a positive exponential-image correction; the odd sine gives a negative one. Complex-even coefficients preserve the first-slot conjugation. The two-column moment Gram determinant is exactly \(34/45\), with the stated lower bound. The reflected-prime control is strictly negative.

These tests were registered before execution. They validate the algebraic mechanisms, not the missing arithmetic sign. No new source-matrix numerical sweep, Lean work, or repository write was performed.

**The new result is a valid window-sensitive archimedean lower bound plus a uniform two-column mass scale. The full signed lower comparison remains open.** The next useful computation is (30) as a complete \(2\times2\) quadratic form, retaining its reflected term and the positive terms in (23)—not another scalar Schur identity or another reconstruction of the odd envelope.

:chatgpt-content-reference{index="9"}[Complete PAPER derivation, explicit error constants, source locks, controls, and exact remaining inequality](sandbox:/mnt/data/PROSHKA_G1_SIGNED_EVEN_TAIL_REDUCTION_2026-10-06.md)

