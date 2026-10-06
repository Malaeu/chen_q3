# Proshka attachment: extracted source budgets

Source: displayed preview of `PROSHKA_ODD_SOURCE_LEAKAGE_DISCRIMINATOR_2026-10-06.md`
in chat `6aba5f5a-f804-83ed-a667-68147ee00f59`, answer completed 2026-10-06,
turn `90a8c340-648a-4f57-a3f5-e6dbaf9429c7`. The exact inline answer is
`PROSHKA_ODD_LEAKAGE_INLINE_2026-10-06.md`, obtained through `read_thread`.
This file is a transcription of the attachment's additional formulas and
arguments, not a byte-exact copy of the attachment. Browser download events
timed out; the rendered preview including its TeX annotations was read.
Original attachment outcome: ORIGINAL_EVENTUAL_SIGN_UNRESOLVED.
Author's estimates below are subject to the check recorded in ODD_TRIAL_SIGN.

## Fixed derivative constants (attachment 2.3--2.5)

\[
P_0(v)=24v-16v^2,\qquad
P_{k+1}(v)=(1/2-2v)P_k(v)+2vP_k'(v).
\]
For a polynomial \(R(v)=\sum a_\ell v^\ell\), set
\[
D[R]=2\pi^{-1/4}\sum_\ell |a_\ell|
       \left(\frac{2(\ell+1/4)}e\right)^{\ell+1/4}.
\]
Using the maximum of \(v^{\ell+1/4}e^{-v/2}\) and
\(\sum_{q\ge1}q^{-1/2}e^{-\pi(q^2-1)/2}<2\), the full theta series satisfies
\[
|G^{(k)}(t)|\le D[P_k]e^{-(\pi/2)e^{2|t|}}.
\]
For \(H=G'''-G'/4\), write \(D_k=D[P_{k+3}-P_{k+1}/4]\), \(0\le k\le3\).

## Window comparison (attachment 3.1--3.3)

\[
C_V=\frac{2\sqrt{3(D[P_0]^2+D[P_2]^2)}}\pi,\qquad
\|V_m-\widetilde V_m\|\le\frac{C_V}{\sqrt{mL}}e^{-\pi m/2}.
\]
The attachment bounds source entries by \(|q_{nk}|\le2\),
\(|q'_{nk}|\le(2+4\pi m)/L\); the grouped archimedean entry by \(15m\),
the pole entry by \(8\sqrt m/L\), and the prime-power entry by
\(4\sqrt m L\). Row sums give \(\|K_m\|\le100m^2L\), \(m\ge3\).
If \(\sigma_\infty=\sqrt{\lambda_{\min}(\mathsf G_\infty)}>0\), where
\(\mathsf G_\infty\) is the continuous Gram matrix of \(G,G''\), then eventually
\[
|U_m-\widetilde U_m|\le\Gamma_m,
\qquad \Gamma_m=\frac{800C_V}{\sigma_\infty}m^{3/2}\sqrt L\,e^{-\pi m/2}.
\]
This is a comparison using the unchanged full matrix, not a redefinition of U.

## Explicit odd error budget (attachment 4.3--6.7)

Set \(L=\log m\), \(a=L/2\), \(\Omega=2\pi m/L\),
\(\delta=\tfrac14\log L\), \(r=\lfloor\delta\Omega/e\rfloor\ge1\).
Let \(b_m=\frac r{2\delta}1_{[-\delta/r,\delta/r]}\),
\(\eta_m=b_m^{*r}\), \(h_m=H*\eta_m\), and
\(X=e^{2(a-\delta)}=m/\sqrt L\). Define
\[
R_0=\left(D_0+\frac{D_1}{\pi X}\right)e^{-\pi X/2},\qquad
R_2=\left(D_2+\frac{D_3}{\pi X}\right)e^{-\pi X/2},\qquad
P_w=\frac{D_0^2e^{2\delta}}\pi e^{-\pi X}.
\]
Here R_0 bounds \(|h_m(a)|+\int_a^\infty|h_m'|\), and R_2 bounds
\(|h_m''(a)|+\int_a^\infty|h_m'''|\).
With \(C_F=48e(\pi/4)^{5/2}\), put
\[
J_p=\int_0^\infty(2+t)^p e^{-\pi t/2}dt
=\sum_{q=0}^p\binom pq2^{p-q}\frac{q!}{(\pi/2)^{q+1}},
\]
\[
\overline S_k=\frac{4C_F^2}{\pi}J_{11+2k}\,
\Omega^{11+2k}e^{-\pi\Omega/2-2r},\qquad k=0,1.
\]
For \(L\ge2\pi\), these bound
\(L^{-1}\sum_{|n|>m}|\omega_n^k\widehat h_m(\omega_n)|^2\).
Use a preceding frequency cell of width \(2\pi/L\le1\) for each summand.
The constants do not depend on growing r.

Let f_m be the original finite projection of h_m, extended by zero, and
\(e_m=f_m-h_m\) on the whole real line. Oddness implies f_m(±a)=0, so
\(e_m\in H^1(\mathbb R)\). Exterior integration by parts gives
\[
|c_n(h_m)-(-1)^nL^{-1/2}\widehat h_m(\omega_n)|
\le\frac{2R_0}{\sqrt L|\omega_n|},
\]
\[
|c_n(h_m')-(-1)^nL^{-1/2}\widehat {h_m'}(\omega_n)|
\le\frac{2R_2}{\sqrt L\omega_n^2}.
\]
The second uses evenness of h_m' and \(\sin(\omega_na)=0\). Summing yields
\[
P_0=2\overline S_0+\frac{4L}{\pi^2m}R_0^2
                         +\frac{D_0^2}{\pi X}e^{-\pi X},
\]
\[
P_1=2\overline S_1+\frac{L^3}{3\pi^4m^3}R_2^2
 +\frac{4(2m+1)}L D_0^2e^{-\pi X}
 +\frac{D_1^2}{\pi X}e^{-\pi X}.
\]
Then \(\|e_m\|_2^2\le P_0\), \(\|e_m'\|_2^2\le P_1\), and
\(\|e^{|t|}e_m\|_2^2\le mP_0+P_w\). The derivative term includes the exact
retained-mode boundary correction \(4(2m+1)|h_m(a)|^2/L\).

With \(c_{ar}=\gamma+\log(8\pi)+\pi/2\), \(C_W=c_{ar}+13\), the full and
pole-removed quadratic forms have the absolute bound
\[
\max(|\mathcal W(e,e)|,|\mathcal A(e,e)|)
\le\mathfrak D(e)+C_W\|e^{|t|}e\|_2^2,
\]
\[
\mathfrak D(e)\le\Omega^{-2}\|e'\|_2^2+(8\log\Omega+16)\|e\|_2^2.
\]
All prime powers contribute at most
\(2\sum_{n\ge2}\log(n)n^{-3/2}\|e^{|t|}e\|_2^2<10\|e^{|t|}e\|_2^2\),
and the two poles at most \(8\|e^{|t|}e\|_2^2/3\).
Root review clarification (not a modification of the quoted author text):
for real h and z_rho=i(rho-1/2),
\(\overline{\widehat h(z_\rho)}=\widehat h(-\overline{z_\rho})
=\widehat h(z_{\bar\rho})=0\). The conjugate zero is also a zeta zero,
and both pole values vanish. This pays the first sesquilinear slot.
Exact radical cancellation gives \(\mathcal W(f_m,f_m)=\mathcal W(e_m,e_m)\)
and the same identity for \(\mathcal A\).

Define
\[
d_m=\|H\|_2-\|H'\|_2\frac\delta{\sqrt{3r}}-\sqrt{P_0}.
\]
Since \(d_m\to\|H\|_2>0\), eventually normalize
\(y_m=E_-^*c_m(h_m)/\|c_m(h_m)\|_2\). The explicit envelope is
\[
\mathcal B_m=\frac{\Omega^{-2}P_1+
 (8\log\Omega+16+C_Wm)P_0+C_WP_w}{d_m^2}.
\]
It bounds both \(|y_m^*K_m^-y_m|\) and \(|y_m^*A_m^-y_m|\).
The attachment derives
\[
\mathcal B_m\le C_H\left[m\Omega^{11}e^{-\pi\Omega/2-2r}
                              +L e^{-\pi m/\sqrt L}\right],
\quad e^{Cm/L}\mathcal B_m\to0\quad\text{for every fixed }C>0.
\]

## Exact remaining comparison (attachment 8.2--8.6)

The sufficient negative-witness inequality is \(U_m>\mathcal B_m\) on an
unbounded original sequence, or \(\widetilde U_m>\mathcal B_m+\Gamma_m\).
A positive lower bound \(U_m\ge c e^{-C_0m/L}\) would imply it. None is proved.
Conversely the requested eventual strict odd comparison would force
\((U_m)_+\le\mathcal B_m\) eventually. This does not assume U_m positive.
The two-column lower bound must retain both mixed and diagonal full-source
terms. A lower bound on omitted Fourier L2 mass is not that energy bound.
