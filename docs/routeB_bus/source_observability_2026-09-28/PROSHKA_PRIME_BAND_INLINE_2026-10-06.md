Ы. **I have not established \(\limsup d_m>0\), nor a source counterargument to it. The new result is a bounded estimate for the complete signed arithmetic form:** its contribution from the remaining infinite discarded-frequency expansion can be removed with an **exponentially small error in the exact two-column tail metric**.

More precisely, I construct explicit \(2\times2\) matrices \(\widehat{\mathsf E}_m,\widehat{\mathsf P}_m\), using only source frequencies
\[
m<n\le3m
\]
and **every original prime power \(q\le m\)**, for which
\[
\boxed{
\left|
\lambda_m-
\lambda_{\max}\!\left(
\widehat{\mathsf E}_m^{-1/2}
\widehat{\mathsf P}_m
\widehat{\mathsf E}_m^{-1/2}
\right)
\right|
\le\tau_m,
}
\tag{1}
\]
with an explicit \(\tau_m\) satisfying
\[
\boxed{
\forall c\in(0,\pi^2/2):\qquad
e^{cm/\log m}\tau_m\longrightarrow0.
}
\tag{2}
\]

The **reflected-Hankel contribution**—the boundary term coupling \(u\) with \(s-u\)—is incorporated algebraically before any estimate. I also give a version retaining the positive image and pole terms.

**This does not prove cancellation inside the remaining arithmetic block.** The \(\sqrt m\) absolute prime bound becomes harmless for the discarded remainder; it has not become a logarithmic bound for the main prime form.

## 1. Unchanged objects and the inputs consumed

Keep
\[
m=m_j,\qquad N=m,\qquad L=\log m,\qquad
a=L/2,\qquad h=2\pi/L,\qquad \omega_n=hn.
\]

For \(z=(z_0,z_2)\in\mathbb C^2\), write
\[
g_z=z_0G+z_2G'',\qquad
f_z=\Pi_m(g_z|_{[-a,a]}),\qquad
r_z=\mathbf1_{[-a,a]}g_z-f_z.
\]
The retained quotient remains exactly
\[
U_m=\inf_{z\ne0}
\frac{z^*\mathsf H_mz}{z^*\mathsf G_mz},
\qquad
\mathsf H_m=V_m^*K_mV_m,\quad
\mathsf G_m=V_m^*V_m.
\]
The original family, complex Euclidean metric, coefficient phase and two-column definition are unchanged. :chatgpt-content-reference{index="0"}

The tail quantities are
\[
E_m(z)=\|r_z\|_2^2=z^*\mathsf E_mz,
\]
\[
P_m(z)=2\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
C_{r_z}(\log q)=z^*\mathsf P_mz,
\]
where
\[
C_v(s)=\int_{\mathbb R}\overline{v(t)}v(t+s)\,dt.
\]
For even \(v\), this self-correlation is real, including for complex-even \(v\).

I use the already checked estimates
\[
\mathsf E_m\succeq
\mu_m\operatorname{diag}(1,T_m^4),
\qquad
\mu_m=c_E T_m^{9/2}\log T_m\,e^{-\pi T_m},
\qquad T_m=h(m+1),
\tag{3}
\]
and
\[
|\widehat G(\omega)|
\le C_F|\omega|^{5/2}e^{-\pi|\omega|/4},
\qquad C_F=48e(\pi/4)^{5/2},
\tag{4}
\]
together with the fixed source derivative bounds
\[
|G^{(k)}(t)|\le D_k e^{-(\pi/2)e^{2|t|}},
\qquad 0\le k\le4.
\tag{5}
\]
Their proofs are not repeated here. The constants are those of the checked mass and source-envelope arguments.  

**The auxiliary cutoff \(3m\) concerns discarded coefficients only.** It does not enlarge the retained carrier, change \(U_m\), or replace \(K_m\).

## 2. Combine each prime atom before estimating it

Introduce the even orthonormal modes
\[
\phi_n(t)=
\sqrt{\frac2L}(-1)^n\cos(\omega_nt)\,
\mathbf1_{[-a,a]}(t),\qquad n\ge1.
\]

Their symmetrized overlap is
\[
\mathcal J_{nk}(s)=
\int_{-a}^{a-s}
\bigl[
\phi_n(t)\phi_k(t+s)+
\phi_k(t)\phi_n(t+s)
\bigr]\,dt,
\qquad 0\le s\le L.
\]

Direct integration gives
\[
\boxed{
\mathcal J_{nk}(s)=
\begin{cases}
2(1-s/L)\cos(\omega_ns)
-\dfrac{\sin(\omega_ns)}{\pi n},
&n=k,\\[2mm]
\dfrac{2[k\sin(\omega_ks)-n\sin(\omega_ns)]}
{\pi(n^2-k^2)},
&n\ne k.
\end{cases}
}
\tag{6}
\]

This is also exactly \(q_{nk}+q_{n,-k}\) from the literal source kernel. The diagonal is retained separately, not supplied by a divided-difference limit. 

For any finite coefficient vector \(b\),
\[
2C_{\sum b_n\phi_n}(s)
=\sum_{n,k}\overline{b_n}\mathcal J_{nk}(s)b_k.
\tag{7}
\]

Thus (6) is the **joint periodic-diagonal minus reflected-Hankel atom**. In particular,
\[
\boxed{\mathcal J_{nk}(L)=0}
\]
for every \(n,k\). The atom at \(q=m\) cancels exactly, even when \(m\) is a prime power.

Define the actual arithmetic sums
\[
S_{m,n}=
\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
\sin(\omega_n\log q),
\]
\[
C_{m,n}=
\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
\left(1-\frac{\log q}{L}\right)
\cos(\omega_n\log q).
\]

On a finite band, the complete prime matrix is therefore
\[
\boxed{
(\mathcal P_m^{\mathrm{band}})_{nk}
=
\begin{cases}
2C_{m,n}-S_{m,n}/(\pi n),&n=k,\\[1mm]
\dfrac{2[kS_{m,k}-nS_{m,n}]}
{\pi(n^2-k^2)},&n\ne k.
\end{cases}
}
\tag{8}
\]

There is a useful way to retain the off-diagonal cancellation during contraction. Define the finite **Hilbert-type transform**
\[
(\mathcal H b)_n=
\sum_{k\ne n}\frac{b_k}{n^2-k^2}.
\]
Then
\[
\boxed{
b^*\mathcal P_m^{\mathrm{band}}b
=
\sum_n\left(2C_{m,n}-\frac{S_{m,n}}{\pi n}\right)|b_n|^2
-\frac4\pi\operatorname{Re}
\sum_n nS_{m,n}\overline{b_n}(\mathcal H b)_n.
}
\tag{9}
\]

To verify the sign, exchange \(n,k\) in the term containing \(kS_{m,k}\). It becomes minus the conjugate of the term containing \(nS_{m,n}\).

**Neither \(S_{m,n}\), nor the Hilbert contraction, is assigned a favorable sign.**

## 3. An explicit source band with a paid relative error

Let \(R>m\) temporarily be an auxiliary integer. Put \(W=hR\), \(F=\widehat G\), and define
\[
(\mathsf S_{m,R})_{n,:}
=
\sqrt{\frac2L}(-1)^nF(\omega_n)
(1,-\omega_n^2),
\qquad m<n\le R.
\tag{10}
\]
The corresponding approximation to the discarded part is
\[
\rho_{m,R,z}(t)=
\sum_{n=m+1}^{R}(\mathsf S_{m,R}z)_n\phi_n(t).
\]

Both coefficient and synthesis phases are present. Its exact norm and prime form are
\[
\widehat{\mathsf E}_{m,R}
=\mathsf S_{m,R}^*\mathsf S_{m,R},
\qquad
\widehat{\mathsf P}_{m,R}
=\mathsf S_{m,R}^*
\mathcal P_m^{\mathrm{band}}\mathsf S_{m,R}.
\tag{11}
\]

These are auxiliary **tail** matrices, not the original retained \(\mathsf G_m\) and \(\mathsf H_m\).

### The actual-window correction on all omitted modes

Set
\[
A_m=
\left(D_1+\frac{D_2}{\pi m}\right)^2+
\left(D_3+\frac{D_4}{\pi m}\right)^2.
\]
Equation (5) gives
\[
|g_z'(a)|+\int_a^\infty|g_z''(t)|\,dt
\le\sqrt{A_m}\,e^{-\pi m/2}\|z\|.
\]

For even \(g_z\), the two exterior Fourier integrals combine into a cosine integral. Its first integration-by-parts boundary term vanishes because
\[
\sin(\omega_na)=\sin(\pi n)=0.
\]
The second gives
\[
\boxed{
\left|
c_n(g_z)-
\frac{(-1)^n}{\sqrt L}F(\omega_n)
(z_0-z_2\omega_n^2)
\right|
\le
\frac{2\sqrt{A_m}\,e^{-\pi m/2}}
{\sqrt L\,\omega_n^2}\|z\|.
}
\tag{12}
\]

Denote this difference by \(\delta_n\). Summation over both signs yields
\[
\sum_{|n|>m}|\delta_n|^2
\le b_{0,m}\|z\|^2,
\qquad
b_{0,m}=
\frac{A_mL^3}{6\pi^4m^3}e^{-\pi m},
\tag{13}
\]
\[
\sum_{|n|>m}\omega_n^2|\delta_n|^2
\le b_{1,m}\|z\|^2,
\qquad
b_{1,m}=
\frac{2A_mL}{\pi^2m}e^{-\pi m}.
\tag{14}
\]

These are coefficient estimates with both endpoints retained.

### The remaining full-source frequencies

For
\[
J_p=\int_0^\infty(2+t)^p e^{-\pi t/2}\,dt,
\]
define
\[
f_{k,m,R}=
\frac{2C_F^2}{\pi}J_{9+2k}
W^{9+2k}e^{-\pi W/2},
\qquad k=0,1.
\tag{15}
\]
Then
\[
\boxed{
\sum_{|n|>R}\omega_n^{2k}
\left|
\frac{(-1)^n}{\sqrt L}F(\omega_n)
(z_0-z_2\omega_n^2)
\right|^2
\le f_{k,m,R}\|z\|^2.
}
\tag{16}
\]

Indeed,
\[
|z_0-z_2\omega^2|^2
\le2\omega^4\|z\|^2
\]
for \(\omega\ge1\). Combine this with (4). For \(h\le1\), compare each frequency with its preceding cell:
\[
h\omega_n^p e^{-\pi\omega_n/2}
\le
\int_{\omega_n-h}^{\omega_n}
(u+1)^p e^{-\pi u/2}\,du.
\]
Summing, using \(Lh=2\pi\), and writing \(u=W+t\) proves (16).

No unproved sampling approximation occurs here.

### Normalize in the actual tail metric

Put
\[
q_{k,m,R}=\sqrt{b_{k,m}}+\sqrt{f_{k,m,R}},
\qquad
\epsilon_{m,R}=\frac{q_{0,m,R}}{\sqrt{\mu_m}}.
\tag{17}
\]
The coefficient difference \(r_z-\rho_z\) consists of the window corrections \(\delta_n\), plus the full-source samples beyond \(R\). Minkowski and (3) give
\[
\boxed{
\|r_z-\rho_z\|_2
\le\epsilon_{m,R}\sqrt{E_m(z)}
\quad\text{for every }z\in\mathbb C^2.
}
\tag{18}
\]

Consequently, when \(\epsilon<1\),
\[
\boxed{
(1-\epsilon)^2E_m(z)
\le z^*\widehat{\mathsf E}_{m,R}z
\le(1+\epsilon)^2E_m(z).
}
\tag{19}
\]

In particular, the bounded source band has rank two eventually. Its Gram inverse is justified by (19), not by numerical invertibility.

## 4. The bounded estimate for the entire arithmetic form

The complete prime operator on the original window is
\[
\mathcal T_m=
\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
\mathbf1_I(\tau_{\log q}+\tau_{-\log q})\mathbf1_I.
\]
It is Hermitian, not necessarily positive, and
\[
\|\mathcal T_m\|
\le C_{\mathrm{pr}}(m):=
2\sum_{q=2}^{m}\frac{\Lambda(q)}{\sqrt q}
\le4\sqrt m\log m.
\tag{20}
\]

For \(\alpha=\epsilon(2+\epsilon)\), equation (18) gives
\[
\begin{aligned}
|P_m(z)-z^*\widehat{\mathsf P}_{m,R}z|
&\le
C_{\mathrm{pr}}\|r_z-\rho_z\|
(\|r_z\|+\|\rho_z\|)\\
&\le
C_{\mathrm{pr}}\alpha E_m(z).
\end{aligned}
\]
Thus
\[
\boxed{
\left\|
\mathsf E_m^{-1/2}
(\mathsf P_m-\widehat{\mathsf P}_{m,R})
\mathsf E_m^{-1/2}
\right\|
\le C_{\mathrm{pr}}\epsilon(2+\epsilon).
}
\tag{21}
\]

This bounds **all prime powers and both mixed entries together**.

To compare the generalized eigenvalues, use the same nonzero \(z\) in both quotients:
\[
\begin{aligned}
\left|\frac{P}{E}-\frac{\widehat P}{\widehat E}\right|
&\le
\frac{|P-\widehat P|}{E}
+
\frac{|\widehat P|}{\widehat E}
\left|\frac{\widehat E}{E}-1\right|\\
&\le2C_{\mathrm{pr}}\epsilon(2+\epsilon).
\end{aligned}
\]
Here \(|\widehat P|/\widehat E\le C_{\mathrm{pr}}\), regardless of its sign. Taking suprema proves (1), with
\[
\boxed{
\tau_{m,R}
=
2C_{\mathrm{pr}}(m)\epsilon_{m,R}(2+\epsilon_{m,R}).
}
\tag{22}
\]

### Why \(R=3m\) pays the normalization

Now fix \(R=3m\), independently of every observed sign. The exponential factor in \(f_{k,m,R}/\mu_m\) is
\[
e^{-\pi W/2+\pi T_m}
=
\exp\!\left[-\frac{\pi^2(m-2)}L\right].
\]
After taking square roots, every additional factor in \(\tau_m\) is polynomial in \(m,L\). The \(b_{k,m}/\mu_m\) terms decay faster. This proves (2).

There is a concrete reason not to truncate immediately above \(m\): the available mass lower bound has exponent \(e^{-2\pi^2(m+1)/L}\), while the far-sample upper bound has exponent \(e^{-\pi^2R/L}\). **Those inputs alone do not pay a cutoff \(m+O(L\log m)\).** The factor-three cutoff supplies a proved buffer.

## 5. Retaining positive image and pole compensation

The prime-only discriminator can lose useful positive terms. They can also be retained in this finite source-band representation.

Let \(\beta_k=2k+\tfrac12\). In band coefficient coordinates define
\[
(\mathcal I_{m,R})_{nk}
=
\frac4L\sum_{j\ge0}
\frac{\beta_j^2(1-e^{-\beta_jL})}
{(\beta_j^2+\omega_n^2)(\beta_j^2+\omega_k^2)},
\tag{23}
\]
\[
(\mathcal O_{m,R})_{nk}
=
\frac{4\sinh^2(L/4)}{L}
\frac1{(1/4+\omega_n^2)(1/4+\omega_k^2)}.
\tag{24}
\]
These are precisely the positive **image correction** and even **two-pole form**, by the checked periodization identity and exact hyperbolic mode integrals. 

The complete signed band matrix is
\[
\boxed{
\widehat{\mathsf Q}_{m,R}
=
\mathsf S_{m,R}^*
\left[
\operatorname{diag}\bigl(\mathfrak a(\omega_n)-c_{\mathrm{ar}}\bigr)
+\mathcal I_{m,R}+\mathcal O_{m,R}
-\mathcal P_m^{\mathrm{band}}
\right]
\mathsf S_{m,R}.
}
\tag{25}
\]
It equals \(\mathcal W(\rho_z,\rho_z)\). The bracketed matrix is **not** asserted positive.

Here is a paid error for this full signed comparison. Set
\[
\nu_{m,R}
=
\sqrt{18+\frac{5L}{\pi^2m}}\,
\frac{q_{1,m,R}}{\sqrt{\mu_m}},
\]
\[
D_{m,R}=\mathfrak a(W)+\frac{20(R-m)}L,
\qquad
C_{\mathrm{pole}}(m)=L+2\sinh(L/2),
\]
and
\[
\boxed{
\Delta_{m,R}
=
2(1+\epsilon)\sqrt{D_{m,R}}\,\nu+\nu^2
+
(c_{\mathrm{ar}}+C_{\mathrm{pole}}+C_{\mathrm{pr}})
\epsilon(2+\epsilon).
}
\tag{26}
\]

Then
\[
\boxed{
|\mathcal W(r_z,r_z)-z^*\widehat{\mathsf Q}_{m,R}z|
\le\Delta_{m,R}E_m(z).
}
\tag{27}
\]

The proof uses
\[
\mathfrak a(\omega)\le18\omega^2,
\qquad
\mathfrak I_L(v)\le10\|v\|_\infty^2,
\]
and, for a periodic tail with coefficients \(d_n\),
\[
\|v\|_\infty^2
\le\frac{L}{2\pi^2m}
\sum_{|n|>m}\omega_n^2|d_n|^2.
\]
These pay the difference-energy norm of \(r-\rho\). Cauchy–Schwarz in that positive seminorm pays its cross term. The pole, ordinary norm and prime terms use their bounded operators.

**The derivative here is the derivative of the periodic representative.** The zero-extended difference is not declared \(H^1(\mathbb R)\); its boundary jumps are handled by the image identity.

With \(R=3m\),
\[
\forall c\in(0,\pi^2/2):
\qquad e^{cm/L}\Delta_{m,3m}\longrightarrow0.
\tag{28}
\]

Combining (27) with the accepted exterior estimate gives
\[
\boxed{
\mathsf H_m
\succeq
\widehat{\mathsf Q}_{m,3m}
-\Delta_m\mathsf E_m-R_mI.
}
\tag{29}
\]
The previously checked exterior estimate includes the conjugate first slot, both jumps and all exterior prime contributions. 

For a lower certificate, a finite initial part of the positive sum (23) may be retained and its positive remainder discarded. That is a valid one-sided deletion, not an unpaid approximation.

## 6. The exact remaining inequalities

Define
\[
\widehat\lambda_m=
\lambda_{\max}\!\left(
\widehat{\mathsf E}_m^{-1/2}
\widehat{\mathsf P}_m
\widehat{\mathsf E}_m^{-1/2}
\right),
\qquad
\widehat d_m=\kappa_m-\widehat\lambda_m.
\]
Equation (22) proves
\[
\boxed{|d_m-\widehat d_m|\le\tau_m\to0.}
\tag{30}
\]

Thus the first requested route now has the following explicit arithmetic target: for one fixed \(\delta>0\), on an unbounded original index set,
\[
\boxed{
\begin{aligned}
&\sum_{n=m+1}^{3m}
\left(2C_{m,n}-\frac{S_{m,n}}{\pi n}\right)|b_n|^2\\
&\quad-\frac4\pi\operatorname{Re}
\sum_{n=m+1}^{3m}
nS_{m,n}\overline{b_n}
\sum_{\substack{m<k\le3m\\k\ne n}}
\frac{b_k}{n^2-k^2}\\
&\hspace{15mm}\le
(\kappa_m-\delta)\sum_{n=m+1}^{3m}|b_n|^2,
\qquad b=\mathsf S_{m,3m}z,\quad z\in\mathbb C^2.
\end{aligned}
}
\tag{31}
\]

Only the two source-generated directions are required—not all band coefficients.

**I have not proved (31).** It is the retained arithmetic cancellation still missing after the newly paid approximation error.

For the less wasteful route, set
\[
q_m=
\lambda_{\min}\!\left(
\widehat{\mathsf E}_m^{-1/2}
\widehat{\mathsf Q}_m
\widehat{\mathsf E}_m^{-1/2}
\right).
\]
When \(q_m>0\), equations (19) and (29) give
\[
\mathsf H_m
\succeq
\bigl[q_m(1-\epsilon_m)^2-\Delta_m\bigr]\mathsf E_m-R_mI.
\]
Therefore the budget-complete sufficient inequality is
\[
\boxed{
q_m(1-\epsilon_m)^2-\Delta_m
>
\frac{C_0\mathcal B_m+R_m}{\mu_m}.
}
\tag{32}
\]
It gives \(U_m>\mathcal B_m\) in the **original retained Gram metric**. Replacing \(\mathcal B_m\) by \(\mathcal B_m+2\Gamma_m\) gives the predecessor’s stronger \(\widetilde U_m\) comparison.

A positive limsup of \(q_m\) would suffice because every displayed error and normalized consumer budget tends to zero. **That positive limsup is also unproved here.**

## 7. Same-cell and literature checks

All estimates above hold uniformly in \(z\) **at each single sufficiently large original \(m\)**. No positive matrix average has been used.

For a future averaging argument, a legitimate sufficient criterion would require more than the average matrix. If \(X_m\) is the normalized Hermitian \(2\times2\) test, write
\[
a_m=\tfrac12\operatorname{tr}X_m,\qquad
b_m=\sqrt{\tfrac12\operatorname{tr}(X_m-a_mI)^2}.
\]
Then \(\lambda_{\min}(X_m)=a_m-b_m\). Consequently,
\[
\sum_m w_ma_m>
\sqrt{\sum_mw_mb_m^2}+\delta
\]
would force one common cell with minimum eigenvalue greater than \(\delta\). Your alternating matrices have \(a_m=\tfrac12\), \(b_m=\tfrac32\), and correctly fail this criterion. No such source trace/dispersion estimate has been proved.

I checked the **twisted second-moment** alternative against Bettin–Chandee–Radziwiłł, Theorem 1. It concerns a fixed smooth average with a Dirichlet polynomial of length \(T^\theta\), \(\theta<17/33\). Our directly visible prime polynomial has length \(m\) while the relevant frequency is of order \(m/\log m\); the moving Gram normalization and reflected coupling also have not been mapped into their theorem. It is not an available sign supplier without further work. This does not rule out a shorter, source-specific reformulation. :chatgpt-content-reference{index="6"}

Twenty preregistered exact algebra controls passed: direct overlap checks including the separate diagonal and terminal atom, the complex Hilbert contraction, the generalized-quotient perturbation check, and the alternating-average control. They do not certify the source sign. No source numerical sweep, independent review of this new derivation, Lean work, or repository write was performed.

**Bottom line:** the newly paid estimate removes the infinite discarded-frequency remainder from the full arithmetic comparison, uniformly in the exact two-column metric. It leaves the finite signed sum (31), or the complete compensated budget (32), to be proved. I have not obtained the required cancellation inside that sum and do not claim a sign change in G1.

:chatgpt-content-reference{index="8"}[Complete PAPER derivation, explicit constants, full signed budget, and executable exact controls](sandbox:/mnt/data/PROSHKA_G1_PRIME_BAND_ARITHMETIC_ESTIMATE_2026-10-06.md)
