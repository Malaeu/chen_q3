# Proshka causal dressing — exact answer1

Chat: Proof of CCM Growth, 6ac54396-d878-83eb-ae29-35d2bdd2262b.
Assistant item: 234c26fe-42be-4b9e-9724-1b0407b1b90d. Complete answer read 2026-10-06 19:11 UTC.
Question: PROSHKA_NEGATIVE_GROWTH_PHASE_2026-10-06.md.
Opaque inline citation tokens preserved; source claims require their own verification.

## Exact answer

## Result: a uniform joint estimate, and a proved obstruction to undressing it

**SP remains open.** I obtained an exact pole–prime cancellation with constants independent of \(m\), but also proved that a natural way of converting it into SP—uniform norm equivalence after a causal smoothing—fails polynomially on the **actual original carrier**. The failure persists when the archimedean energy is added to the comparison norm.

The cancellation below uses the all-integer dilation sum and the divisor identity for \(\Lambda\), not the Chebyshev-primitive integration by parts. No zero-location hypothesis is used.

### 1. Source and coordinates

Translate \(I\) to \([0,L]\) by \(x=t+L/2\). The supplied phases then give exactly
\[
e_n(x)=L^{-1/2}e^{2\pi inx/L},\qquad |n|\le m.
\]
Thus this is a unitary coordinate change of the stated carrier, not a replacement matrix. It agrees with CCM’s Proposition 3.2 and its full complex form (3.19), with \(\lambda=\sqrt m\), \(N=m\). CCM’s fixed-\(\lambda\) lower-boundedness does not supply a uniform estimate here. :chatgpt-content-reference{index="0"}

There is also a relevant literature boundary: the positive factorization in §7.7 of Suzuki’s September 2026 revision is explicitly under RH; §7 begins with that assumption. I do not import that factorization. :chatgpt-content-reference{index="1"}

Write
\[
\mathcal V_m=\operatorname{span}\{e_n:|n|\le m\},
\qquad \mathcal H_L=L^2(0,L).
\]
All functions below are zero-extended when evaluated in \(W\).

## 2. Exact causal algebra retaining all prime powers

For \(s\ge0\), define
\[
(S_s f)(x)=\mathbf1_{\{x\ge s\}}f(x-s),\qquad Xf(x)=xf(x).
\]
These operators satisfy
\[
S_sS_t=S_{s+t},\qquad [X,S_s]=sS_s,\qquad S_L=0
\tag{1}
\]
as \(L^2\)-operators. In particular, the endpoint atom at \(n=m\) is handled by \(S_{\log m}=0\), consistently with \(Q_f(L)=0\); it is not deleted by convention.

Set
\[
R_\pm=\int_0^L e^{\pm s/2}S_s\,ds,\qquad R=R_-,
\]
and
\[
\mathcal P_L=\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}S_{\log n}.
\]
The **joint** pole–prime operator is
\[
\mathcal B_L
=R_++R+R_+^*+R^*-\mathcal P_L-\mathcal P_L^*,
\tag{2}
\]
so that, on the original carrier,
\[
W(f)=D_{\rm arch}(f)-c_A\|f\|_2^2+\langle f,\mathcal B_Lf\rangle.
\tag{3}
\]

Introduce the all-integer operator
\[
Z_L=\sum_{1\le n\le m}\frac1{\sqrt n}S_{\log n}.
\]
The truncated causal algebra gives an **exact inverse**
\[
Z_L^{-1}
=\sum_{1\le n\le m}\frac{\mu(n)}{\sqrt n}S_{\log n}.
\tag{4}
\]
Indeed, multiplying these finite sums uses ordinary divisor convolution; terms whose product exceeds \(m\) act as zero.

Moreover,
\[
\boxed{\quad
Z_L^{-1}[X,Z_L]=\mathcal P_L.
\quad}
\tag{5}
\]
The coefficient at \(S_{\log n}/\sqrt n\) is
\[
\sum_{d\mid n}\mu(d)\log(n/d)=\Lambda(n).
\]
This identity recovers **every prime power**, not just the primes.

## 3. A positive-kernel dressing with uniform constants

Define
\[
A_L=R(I-R)Z_L.
\tag{6}
\]
This is a causal integral operator
\[
(A_Lf)(x)=\int_0^x a(s)f(x-s)\,ds
\]
with an explicit kernel independent of \(L\).

To compute it, first observe that the convolution kernel of \(RZ_L\) is
\[
e^{-s/2}\lfloor e^s\rfloor.
\]
Consequently,
\[
\begin{aligned}
a(s)
&=e^{-s/2}\left(\lfloor e^s\rfloor
                  -\int_0^s\lfloor e^u\rfloor\,du\right)\\
&=e^{-s/2}\left(
1-\{e^s\}+\int_0^s\{e^u\}\,du
\right).
\end{aligned}
\tag{7}
\]
Therefore
\[
0\le a(s)\le (1+s)e^{-s/2}.
\tag{8}
\]

The kernel is nonnegative. **This does not mean that \(A_L\), which is causal and not self-adjoint, is a positive operator.**

Let
\[
C_L=[X,A_L].
\]
Its kernel is \(s\,a(s)\). Young’s inequality now gives the uniform bounds
\[
\boxed{
\|A_L\|\le6,\qquad \|C_L\|\le20,
}
\tag{9}
\]
because
\[
\int_0^\infty(1+s)e^{-s/2}\,ds=6,\qquad
\int_0^\infty s(1+s)e^{-s/2}\,ds=20.
\]

### The joint operator is an exact inverse commutator

The resolvent identities give
\[
[X,R]=R^2,\qquad (I-R)^{-1}=I+R_+.
\]
Using these and (5) in the commutator of (6) yields
\[
C_L=A_L\bigl(\mathcal P_L-R_++2R\bigr).
\tag{10}
\]
The operator \(A_L\) is injective: \(R\) is injective, while \(I-R\) and \(Z_L\) are invertible. Thus
\[
T_L:=A_L^{-1}C_L=\mathcal P_L-R_++2R
\tag{11}
\]
is a well-defined bounded operator for each fixed \(L\). In particular, no unrestricted bounded inverse for \(A_L\) is being assumed.

Equations (2) and (11) give
\[
\boxed{
\mathcal B_L=3(R+R^*)-(T_L+T_L^*).
}
\tag{12}
\]
This is an exact identity for the joint pole–prime operator **before taking norms**.

The operator
\[
H_L:=R+R^*
\]
has kernel \(e^{-|x-y|/2}\), hence is positive: its full-line Fourier multiplier is
\[
\frac1{1/4+\omega^2}.
\tag{13}
\]

Since causal convolution operators commute, \(T_LA_L=C_L\). Therefore, for \(g=A_Lu\),
\[
\begin{aligned}
\langle g,\mathcal B_Lg\rangle
&=3\langle g,H_Lg\rangle
  -2\operatorname{Re}\langle A_Lu,C_Lu\rangle\\
&\ge-240\|u\|_2^2.
\end{aligned}
\]
We obtain the actual uniform estimate
\[
\boxed{
W(A_Lu)\ge
D_{\rm arch}(A_Lu)
-c_A\|A_Lu\|_2^2
-240\|u\|_2^2.
}
\tag{14}
\]
In particular,
\[
W(A_Lu)\ge-(240+36c_A)\|u\|_2^2.
\tag{15}
\]

This estimate retains the full poles and all prime powers. Its constant does not grow with \(m\). **Its norm is the preimage norm, however, not the \(L^2\)-norm required by SP.**

### Domain and endpoints in (14)

For each finite \(L\), \(a\) has bounded variation on \([0,L]\), with \(a(0)=1\). Hence \(A_Lu\in H^1(0,L)\), and
\[
(A_Lu)(0)=0.
\]
The zero extension may jump at \(L\). For any \(g\in H^1(0,L)\), direct splitting into the overlap and the two boundary intervals gives, for \(0<s\le L\),
\[
\|\tau_sg-g\|_2^2
\le
3s^2\|g'\|_2^2+
2s\bigl(|g(0)|^2+|g(L)|^2\bigr).
\tag{16}
\]
Thus the endpoint contribution is integrable against \(J(s)=O(s^{-1})\). Equation (14) applies to these zero-extended functions without imposing an unproved zero boundary condition at \(L\).

## 4. A polynomial obstruction on the original top Fourier mode

The natural attempted completion of (14) would be a subpolynomial comparison between the preimage norm and the dressed norm. That mechanism fails.

Let
\[
v_m=e_m,\qquad \|v_m\|_2=1,\qquad
\Omega=\frac{2\pi m}{L},
\]
and put \(g_m=A_Lv_m\). The exact formula is
\[
g_m(x)=\frac{e^{i\Omega x}}{\sqrt L}
       \int_0^x a(s)e^{-i\Omega s}\,ds.
\tag{17}
\]
I will prove
\[
\boxed{
\|g_m\|_2^2\le\frac{256}{\Omega}
=\frac{128}{\pi}\frac{L}{m}.
}
\tag{18}
\]

### A uniform partial-Fourier bound for the actual kernel

Write
\[
r(s)=e^{-s/2}\{e^s\},\qquad
p(s)=e^{-s/2}+(e^{-\,\cdot/2}*r)(s).
\]
Then \(a=p-r\).

We have
\[
0\le r(s)\le e^{-s/2}.
\]
Between its jumps,
\[
r'(s)=e^{s/2}-\tfrac12r(s),
\]
and its downward jump at \(s=\log n\) has size \(n^{-1/2}\). Therefore
\[
\operatorname{Var}_{[0,S]}r
\le4(e^{S/2}-1).
\tag{19}
\]

For \(\omega\ge1\), split at \(S=\log\omega\). Integration by parts up to \(S\), followed by the absolute tail bound beyond \(S\), gives, uniformly for every \(x\ge0\),
\[
\left|\int_0^x r(s)e^{-i\omega s}\,ds\right|
\le\frac7{\sqrt\omega}.
\tag{20}
\]
For completeness, the first portion is at most
\[
\frac{|r(S)|+\operatorname{Var}_{[0,S]}r}{\omega}
\le\frac5{\sqrt\omega},
\]
and the remaining \(L^1\)-tail is at most \(2/\sqrt\omega\).

Also,
\[
p(0)=1,\qquad \|p\|_\infty\le3,\qquad \|p'\|_1\le5,
\]
so
\[
\left|\int_0^x p(s)e^{-i\omega s}\,ds\right|
\le\frac9\omega.
\]
Combining these estimates,
\[
\boxed{
\sup_{x\ge0}
\left|\int_0^x a(s)e^{-i\omega s}\,ds\right|
\le\frac{16}{\sqrt\omega}.
}
\tag{21}
\]
Equations (17)–(21) prove (18), as well as
\[
g_m(0)=0,\qquad
|g_m(L)|^2\le\frac{256}{L\Omega}.
\tag{22}
\]

This already proves
\[
\inf_{\substack{v\in\mathcal V_m\\\|v\|_2=1}}
\|A_Lv\|_2
\le16\sqrt{\frac{L}{2\pi m}}.
\tag{23}
\]
Thus any carrier-wide inverse comparison must lose at least
\[
\frac1{16}\sqrt{\frac{2\pi m}{L}}
\]
in norm, or order \(m/L\) in a squared-norm comparison.

### The archimedean graph norm does not repair it

Here the endpoint costs can also be made explicit.

From (19) and the bound for \(p'\),
\[
\operatorname{Var}_{[0,L]}a\le5+4\sqrt m.
\]
Differentiating the causal convolution **inside the interval** gives
\[
\|g_m'\|_2\le6+4\sqrt m\le10\sqrt m.
\tag{24}
\]
The zero-extension jump is still accounted for separately by (16).

For \(L\ge1\), use
\[
J(s)\le\frac2s\quad(0<s\le1),
\qquad
J(s)\le2e^{-s/2}\quad(s\ge1).
\]
On \(0<s\le1/m\), equations (16), (22), and (24) give
\[
\|\tau_sg_m-g_m\|_2^2
\le300ms^2+\frac{512s}{L\Omega}.
\]
For larger shifts, use
\[
\|\tau_sg_m-g_m\|_2^2\le4\|g_m\|_2^2.
\]
Splitting the archimedean integral at \(1/m\) and \(1\) therefore yields
\[
D_{\rm arch}(g_m)
\le
\frac{300}{m}
+\frac{1024}{mL\Omega}
+\frac{2048L+4096}{\Omega}.
\tag{25}
\]
In particular, for \(m\ge3\),
\[
\boxed{
\|A_Lv_m\|_2^2+D_{\rm arch}(A_Lv_m)
\le
10000\,\frac{L}{\Omega}
=
\frac{5000}{\pi}\frac{L^2}{m}.
}
\tag{26}
\]

Consequently, the proposed uniform comparison
\[
\|v\|_2^2
\le C_\eta m^\eta
\left(\|A_Lv\|_2^2+D_{\rm arch}(A_Lv)\right),
\qquad v\in\mathcal V_m,
\tag{27}
\]
is **false for every fixed \(\eta<1\)**. Substituting \(v=v_m\) forces
\[
C_\eta\ge
\frac{2\pi}{10000}
\frac{m^{1-\eta}}{(\log m)^2}\longrightarrow\infty.
\]

This is a proved obstruction to a concrete mechanism:

> Uniform dressed semiboundedness cannot be converted to SP through subpolynomial carrier-wide norm equivalence for \(A_L\), even after adding the archimedean energy.

It is **not** a negative-bottom construction. The vector \(v_m\) is not asserted to be a bottom vector, and nothing here rules out a good estimate for the signed product \(A_L^{-1}[X,A_L]\).

There is a second domain caution: \(A_L\) does not preserve \(\mathcal V_m\). Indeed its range is \(H^1(0,L)\) with zero left trace, whereas a general carrier vector has nonzero left trace. Thus its compression cannot silently be substituted into (14) as an exact factorization of \(K_m\).

## 5. Remove the forced smoothing loss before the next estimate

The derivative loss just proved is not intrinsic to the pole cancellation. It comes from the extra factor \(R\) in \(A_L\).

Define the bounded, invertible, **unsmoothed** operator
\[
F_L=(I-R)Z_L.
\tag{28}
\]
Its inverse is explicit:
\[
F_L^{-1}=Z_L^{-1}(I+R_+).
\]
Equivalently, with
\[
M_1(x)=\sum_{n\le x}\frac{\mu(n)}n,
\]
\[
\boxed{
F_L^{-1}
=
\sum_{n\le m}\frac{\mu(n)}{\sqrt n}S_{\log n}
+
\int_0^L e^{s/2}M_1(e^s)S_s\,ds.
}
\tag{29}
\]
This is an identity, not a cancellation estimate for \(M_1\).

A direct commutator calculation gives
\[
F_L^{-1}[X,F_L]=\mathcal P_L-R_++R.
\tag{30}
\]
Hence the original joint operator also has the exact representation
\[
\boxed{
\mathcal B_L
=
2H_L-
\left(F_L^{-1}[X,F_L]
      +[X,F_L]^*F_L^{-*}\right).
}
\tag{31}
\]
No inverse of the smoothing \(R\) remains.

### What can already be paid in the unsmoothed expression

Take the polar decomposition
\[
F_L=V_LM_L,\qquad
M_L=(F_L^*F_L)^{1/2}>0,
\]
and set
\[
Y_L=V_L^*XV_L.
\]
Since \(F_L\) is invertible, \(V_L\) is unitary, and
\[
0\le X,Y_L\le LI.
\tag{32}
\]

Define the self-adjoint double commutator
\[
\mathfrak D_L
=
M_L^{-1}[M_L,[M_L,Y_L]]M_L^{-1}.
\tag{33}
\]
Elementary multiplication gives
\[
\begin{aligned}
&F_L^{-1}[X,F_L]+[X,F_L]^*F_L^{-*}\\
&\hspace{2em}=2(Y_L-X)+\mathfrak D_L.
\end{aligned}
\tag{34}
\]
The unitary-change-of-position term is therefore paid with the explicit cost
\[
2(Y_L-X)\le2LI.
\]
Combining (3), (31), and \(H_L\ge0\), we obtain, for **every vector of the actual complex carrier**,
\[
\boxed{
W(f)\ge
D_{\rm arch}(f)
-\bigl(c_A+2\log m\bigr)\|f\|_2^2
-\langle f,\mathfrak D_Lf\rangle,
\qquad f\in\mathcal V_m.
}
\tag{35}
\]

Thus the first unsupplied inequality in this version of the mechanism is
\[
\boxed{
\langle f,\mathfrak D_Lf\rangle
\le
D_{\rm arch}(f)+C_\eta m^\eta\|f\|_2^2,
\qquad f\in\mathcal V_m,
}
\tag{36}
\]
for every \(\eta>0\), eventually. Equation (36) is **not proved here**. Nor is any sign asserted for \(\mathfrak D_L\). The polar calculation isolates the remaining difficulty; it does not estimate it.

What has been established is more limited and definite: the full joint term admits the uniform dressed estimate (14); a carrier-wide undressing argument is ruled out by (26); and, after removing that forced smoothing loss, the unitary part of the remaining commutator costs only \(2\log m\).

**Next mathematical step:** estimate the upper quadratic part of the source-defined double commutator (33) on \(\mathcal V_m\), using the explicit \(F_L\) and inverse (28)–(29), with target (36). The calculation identifies the required cancellation as a signed commutator estimate—not a bound on a standalone inverse or its condition number.

