# Proshka answer3: exact inline source

Chat Proof of CCM Growth, 6ac54396-d878-83eb-ae29-35d2bdd2262b.
Question3: ENDPOINT_FACTOR_AUDIT_2026-10-06.md.
Assistant item 34935966-4fcc-4d67-bd1b-8ac4789c5315. Complete answer retrieved 2026-10-06 around 20:14 UTC.
Linked supplement download timed out; no attachment contents claimed.
Inline citation placeholders require independent primary-source verification.

Ы — I obtained a **uniform full-carrier improvement**, but not SP. The improvement holds on **every sufficiently late original cell**, simultaneously for **all complex vectors in \(\mathcal V_m\)**.

**[COFINAL_FAMILY | PAPER]** With \(L=\log m\), there are absolute constants \(C,m_0\) such that
\[
\boxed{
\lambda_{\min}(K_m)\ge
-c_A-C\sqrt m\,L^3
\exp\!\left[-c\left(\frac{L}{\log L}\right)^{1/3}\right],
\qquad m\ge m_0,
}
\tag{1}
\]
where \(c=10^{-3}\) is admissible after enlarging \(m_0\).

Consequently, for every fixed \(B>0\),
\[
\lambda_{\min}(K_m)\ge
-c_A-C_B\frac{\sqrt m}{(\log m)^B}
\]
eventually. This improves the previous \(O(\sqrt m\log m)\) floor while paying the **entire growing matrix**, including its high modes and cross terms.

A second calculation gives a genuine block estimate: the coupling between a **polylogarithmic low-frequency block** and the **top half of the carrier** tends to zero in operator norm. The intervening and neighboring bands remain unresolved.

**The exponent in (1) still tends to \(1/2\). No common-cell subpolynomial subsequence is supplied.**

:chatgpt-content-reference{index="6"}[Complete PAPER verdict with machine-readable header and claim ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q03.md)

## 1. The exact joint matrix has a dimension-free cross-term estimate

**[FINITE_CELL | PAPER]**

Use the supplied coordinate change to \([0,L]\):
\[
e_j(x)=L^{-1/2}e^{i\omega_jx},
\qquad
\omega_j=\frac{2\pi j}{L},
\qquad -m\le j\le m.
\]
This is the CCM source identification in Proposition 3.2 and equation (3.19), with \(\lambda=\sqrt m\), \(N=m\). :chatgpt-content-reference{index="0"}

Keep the **joint signed measure**
\[
d\nu_m(s)=
\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\,
\delta_{\log n}(ds)
-\bigl(e^{s/2}-e^{-s/2}\bigr)\,ds,
\qquad 0\le s\le L.
\tag{2}
\]
Its causal operator is exactly
\[
T_\nu=\int S_s\,d\nu_m(s)
=\mathcal P-R_++R
=F^{-1}[X,F],
\qquad F=(I-R)Z.
\]
In particular, **\(I-R\) remains present**.

Define
\[
\begin{aligned}
\Phi_m(\omega;y)
={}&
\sum_{n\le y}\frac{\Lambda(n)}{n^{1/2+i\omega}}
-\frac{y^{1/2-i\omega}-1}{1/2-i\omega}
+\frac{1-y^{-1/2-i\omega}}{1/2+i\omega},\\
\mathcal R_m
={}&
\sup_{\substack{|\omega|\le2\pi m/L\\1\le y\le m}}
|\Phi_m(\omega;y)|.
\end{aligned}
\tag{3}
\]
Thus \(\Phi_m\) retains pole–prime cancellation **before** taking absolute values.

Let \(\mathsf C_m\) be the compression of \(T_\nu+T_\nu^*\). Direct finite-window integration gives
\[
\langle e_j,S_se_k\rangle=
\begin{cases}
(1-s/L)e^{-i\omega_js},&j=k,\\[2mm]
\displaystyle
\frac{e^{-i\omega_ks}-e^{-i\omega_js}}
{2\pi i(k-j)},&j\ne k.
\end{cases}
\tag{4}
\]
These are the same finite-window correlation factors appearing in CCM Lemma 2.3; in particular, the off-diagonal entries contain a **difference**, not two unrelated terms. :chatgpt-content-reference{index="1"}

Set
\[
h_j=\Im\Phi_m(\omega_j;m),
\qquad
d_j=\frac2L\Re\int_0^L\Phi_m(\omega_j;e^u)\,du.
\tag{5}
\]
Then
\[
(\mathsf C_m)_{jj}=d_j,
\qquad
(\mathsf C_m)_{jk}
=\frac{h_j-h_k}{\pi(j-k)}
\quad(j\ne k).
\tag{6}
\]

Now introduce the **discrete Hilbert matrix**
\[
(\mathsf H_m^{\mathrm d})_{jk}
=
\begin{cases}
(j-k)^{-1},&j\ne k,\\
0,&j=k.
\end{cases}
\]
It is a compression of the convolution operator on \(\ell^2(\mathbb Z)\) whose Fourier multiplier is, up to sign convention, \(i(\pi-\theta)\). Hence
\[
\|\mathsf H_m^{\mathrm d}\|\le\pi
\]
independently of \(2m+1\).

Therefore
\[
\boxed{
\mathsf C_m
=\operatorname{diag}(d_j)
+\frac1\pi
[\operatorname{diag}(h_j),\mathsf H_m^{\mathrm d}],
\qquad
\|\mathsf C_m\|\le4\mathcal R_m.
}
\tag{7}
\]
Indeed,
\[
\max_j|d_j|\le2\mathcal R_m,
\qquad
\left\|\frac1\pi[\operatorname{diag}(h_j),\mathsf H_m^{\mathrm d}]\right\|
\le2\mathcal R_m.
\]

**This pays every cross term at once.** There is no multiplication by the carrier dimension and no row-sum logarithm.

The endpoint \(n=m\) is also exact: at \(s=L\), both expressions in (4) vanish. Its contribution to \(\Phi_m(\omega_j;m)\) is real and independent of \(j\), so it changes neither \(h_j\) nor \(d_j\). It has not been deleted.

## 2. Uniform arithmetic cancellation through the top frequency

**[COFINAL_FAMILY | PAPER]**

I prove
\[
\boxed{
\mathcal R_m
\le C\sqrt m\,L^3
\exp\!\left[-c\left(\frac L{\log L}\right)^{1/3}\right].
}
\tag{8}
\]

The arithmetic input is the **unconditional shrinking zero-free region** of Mossinghoff–Trudgian–Yang, Theorem 1.1:
\[
\zeta(\sigma+it)\ne0
\quad\text{if}\quad
|t|\ge3,\qquad
\sigma\ge
1-\frac1{55.241(\log|t|)^{2/3}(\log\log|t|)^{1/3}}.
\tag{9}
\]
This is not an assumed fixed zero-free half strip or RH. :chatgpt-content-reference{index="2"}

We also use the unconditional zero-counting remainder
\[
N(T)=\frac{T}{2\pi}\log\frac{T}{2\pi e}+O(\log T),
\]
which gives \(O(\log(|t|+2))\) zeros, counted with multiplicity, in a unit-height interval. Hasanalizade–Shen–Wong give an explicit version of this estimate. :chatgpt-content-reference{index="3"}

Put
\[
T=m^2,\qquad U=4m^2,
\qquad
\delta_m=
\frac1{4\cdot55.241(\log U)^{2/3}(\log\log U)^{1/3}}.
\tag{10}
\]
For sufficiently large \(m\), all zeros with \(|\Im\rho|\le U\) satisfy
\[
\Re\rho\le1-4\delta_m.
\]
For ordinates at least \(3\), this follows from (9). The remaining bounded-height zeros form a finite set strictly left of \(1\), so their fixed positive distance is absorbed into the eventual threshold.

### The contour bound

On the left and horizontal sides of the contour below,
\[
\left|\frac{\zeta'}{\zeta}(\sigma+it)\right|
\ll\frac{\log U}{\delta_m}.
\tag{11}
\]

Here is a direct justification. Subtract the Hadamard logarithmic derivatives at \(\sigma+it\) and \(2+it\). Zeros with \(|\gamma-t|\le1\) have \(O(\log U)\) total multiplicity and denominators at least \(3\delta_m\). For the other zeros, subtraction gives terms
\[
O\!\left(\frac1{|\gamma-t|^2}\right),
\]
whose sum is \(O(\log U)\). The pole at \(1\) costs at most \(\delta_m^{-1}\); the gamma-factor difference is bounded. Finally, \(\zeta'/\zeta(2+it)\) is bounded by its absolutely convergent series.

### Sharp cutoff and its endpoint cost

Fix any
\[
1\le y\le m,\qquad |\omega|\le\frac{2\pi m}{L}.
\]
Choose
\[
x=\lfloor y\rfloor+\frac12,
\qquad
c_0=\frac12+\frac1{\log(2m)}.
\]
The prime-power sum up to \(y\) equals the sum up to \(x\) exactly.

**Truncated Perron inversion** applied to
\[
-\frac{\zeta'}{\zeta}\left(s+\frac12+i\omega\right)
=
\sum_{n\ge1}\frac{\Lambda(n)}{n^{s+1/2+i\omega}},
\qquad \Re s>\frac12,
\]
gives
\[
\sum_{n\le y}\frac{\Lambda(n)}{n^{1/2+i\omega}}
=
\frac1{2\pi i}
\int_{c_0-iT}^{c_0+iT}
-\frac{\zeta'}{\zeta}\left(s+\frac12+i\omega\right)
\frac{x^s}{s}\,ds
+
O\!\left(\frac{\sqrt m\,L^2}{T}\right).
\tag{12}
\]

The error is uniform in \(\omega\), since \(|n^{-i\omega}|=1\). More explicitly, the truncated-kernel error is bounded by
\[
\sum_{n\ge1}
\frac{\Lambda(n)}{\sqrt n}(x/n)^{c_0}
\min\!\left(1,\frac1{T|\log(x/n)|}\right).
\]
Outside \([x/2,2x]\), use the convergent \(n^{-1-1/\log(2m)}\) sum. Inside this interval, the half-integer choice gives \(|x-n|\ge1/2\), and the cost is
\[
\ll
\frac{\sqrt x\log(2x)}T
\sum_{x/2\le n\le2x}\frac1{|x-n|}
\ll\frac{\sqrt m\,L^2}{T}.
\]

Shift the contour to \(\Re s=1/2-\delta_m\). The shifted zeta arguments have imaginary parts bounded by
\[
T+|\omega|<U-1.
\]
The only pole crossed is \(s=1/2-i\omega\), with residue
\[
\frac{x^{1/2-i\omega}}{1/2-i\omega}.
\]
No zeros are crossed.

By (11), the new vertical integral costs
\[
O\!\left(x^{1/2-\delta_m}\frac{L^2}{\delta_m}\right),
\]
and the horizontal integrals cost
\[
O\!\left(\frac{\sqrt m\,L}{\delta_m T}\right).
\]

Now subtract the continuous growing-pole term in (3). The cutoff adjustment costs only
\[
\left|\int_y^x u^{-1/2-i\omega}\,du\right|\le1,
\]
**not** \(O(|\omega|)\). The lower integration endpoint costs at most \(2\), and the decaying-pole integral costs at most \(2\). Thus
\[
\boxed{
\mathcal R_m
\le
5+C\frac{L^2}{\delta_m}
\left[
\left(m+\frac12\right)^{1/2-\delta_m}
+\frac{\sqrt m}{T}
\right].
}
\tag{13}
\]

This is uniform over **every cutoff and every frequency required by the same full matrix**.

For sufficiently large \(L\),
\[
\delta_m^{-1}\le CL,
\qquad
\delta_mL\ge
\frac1{600}\left(\frac L{\log L}\right)^{1/3}.
\]
Equation (13) proves (8), conservatively with \(c=10^{-3}\).

The distinction from the old Chebyshev-primitive estimate is substantive: **the oscillation enters the Dirichlet-series coefficients before contour displacement**. Neither the pole matching nor the sharp-cutoff error incurs the high-frequency factor \(m/L\).

## 3. Return to \(D_F\) and the original full form

**[COFINAL_FAMILY | PAPER]**

Write \(H_0=R+R^*\). Its kernel is \(e^{-|x-y|/2}\), so
\[
H_0\ge0,\qquad \|H_0\|\le4.
\]
The exact source identity is
\[
W(f)=D_{\rm arch}(f)-c_A\|f\|^2
+2\langle f,H_0f\rangle
-\langle f,\mathsf C_mf\rangle.
\]
Hence (7) gives
\[
\boxed{
W(f)\ge
D_{\rm arch}(f)-(c_A+4\mathcal R_m)\|f\|^2.
}
\tag{14}
\]

Likewise,
\[
D_F=(T_\nu+T_\nu^*)-2(Y-X),
\qquad 0\le X,Y\le LI,
\]
so
\[
\boxed{
\langle f,D_Ff\rangle
\le(4\mathcal R_m+2L)\|f\|^2,
\qquad f\in\mathcal V_m.
}
\tag{15}
\]

These inequalities are simultaneous over the original complex carrier. No inverse conditioning or scalar-good-cell intersection is involved.

All zero-extension jumps remain inside the exact \(D_{\rm arch}\). No endpoint trace has been set to zero.

## 4. The full archimedean matrix has a bounded off-diagonal/boundary budget

**[COFINAL_FAMILY | PAPER]**

Let \(\mathsf A_m\) be the exact \(D_{\rm arch}\) matrix, and define
\[
\begin{aligned}
a(\omega)
&=2\int_0^\infty J(s)(1-\cos\omega s)\,ds\\
&=
2\sum_{r\ge0}
\frac{\omega^2}
{(2r+\frac12)((2r+\frac12)^2+\omega^2)}
\ge0.
\end{aligned}
\tag{16}
\]
Then
\[
\boxed{
\left\|\mathsf A_m-
\operatorname{diag}\bigl(a(\omega_j)\bigr)\right\|
\le20,
\qquad L\ge1.
}
\tag{17}
\]

The diagonal error is exactly
\[
\frac2L\int_0^L sJ(s)\cos(\omega_js)\,ds
+
2\int_L^\infty J(s)\cos(\omega_js)\,ds.
\]
Set
\[
b_L=\int_L^\infty J(s)\,ds
\le\frac{2e^{-L/2}}{1-e^{-2L}}.
\]
Since
\[
\int_0^\infty sJ(s)\,ds
=\sum_{r\ge0}(2r+\tfrac12)^{-2}\le5,
\]
the diagonal error is at most \(10/L+2b_L\).

The off-diagonal matrix is minus a discrete Hilbert commutator with parameter
\[
h_j^J=-\int_0^LJ(s)\sin(\omega_js)\,ds.
\]
The full sine transform satisfies
\[
\left|
\int_0^\infty J(s)\sin(\omega s)\,ds
\right|
=
\left|
\sum_{r\ge0}
\frac{\omega}{(2r+\frac12)^2+\omega^2}
\right|
\le1+\frac\pi4.
\]
The first summand is at most \(1\), and the remaining sum is bounded by its decreasing-function integral.

Thus the off-diagonal norm is at most \(2+\pi/2+2b_L\). Altogether,
\[
2+\frac\pi2+\frac{10}L+4b_L<20
\quad(L\ge1).
\]

This pays the finite-window triangle factor and the entire \(s>L\) tail. It is not a graph-norm repair of the previously killed dressing.

## 5. A controlled block containing a growing number of directions

**[COFINAL_FAMILY | PAPER]**

Let
\[
I_q=\{j:|j|\le q\},
\qquad
J_Q=\{k:Q\le|k|\le m\},
\qquad Q\ge q+2.
\]
From the exact divided differences,
\[
\|P_{I_q}\mathsf C_mP_{J_Q}\|
\le
\frac{2\mathcal R_m}{\pi}
\sqrt{\frac{2(2q+1)}{Q-q-1}}.
\tag{18}
\]
Indeed,
\[
\sum_{j\in I_q}\sum_{k\in J_Q}\frac1{(j-k)^2}
\le
2(2q+1)\sum_{k=Q}^\infty\frac1{(k-q)^2}
\le
\frac{2(2q+1)}{Q-q-1}.
\]

For the **full \(K_m\)**, its off-diagonal parameter is
\[
v_j=-h_j^J+2h_j^R-h_j,
\qquad
h_j^R=-\int_0^Le^{-s/2}\sin(\omega_js)\,ds.
\]
For \(L\ge1\),
\[
|h_j^J|<3.2,\qquad |h_j^R|\le2,
\qquad |v_j|\le\mathcal R_m+8.
\]
Therefore
\[
\boxed{
\|P_{I_q}K_mP_{J_Q}\|
\le
\frac{2(\mathcal R_m+8)}{\pi}
\sqrt{\frac{2(2q+1)}{Q-q-1}}.
}
\tag{19}
\]

Taking
\[
q=\lfloor L^A\rfloor,\qquad Q=\lceil m/2\rceil
\]
gives, for every fixed \(A>0\),
\[
\boxed{
\|P_{I_q}K_mP_{J_Q}\|
\le
C L^{3+A/2}
e^{-c(L/\log L)^{1/3}}
=o(1).
}
\tag{20}
\]

The growing dimensions are explicitly paid. For an arbitrary decomposition \(f=u+w+v\) into low, middle, and top components,
\[
2|\langle u,K_mv\rangle|
\le
\|P_{I_q}K_mP_{J_Q}\|
(\|u\|^2+\|v\|^2)
\le
\|P_{I_q}K_mP_{J_Q}\|\,\|f\|^2.
\]

**The middle component is not discarded.** Its other cross terms are covered by the global bound (14), but not yet at subpolynomial scale.

## 6. Where the mechanism stops

The unconditional region used above has width
\[
\delta_m\asymp
L^{-2/3}(\log L)^{-1/3};
\]
it therefore supplies \(m^{1/2-o(1)}\), not \(m^{o(1)}\). Improving its numerical constant does not change that exponent boundary. :chatgpt-content-reference{index="4"}

The present proof loses the needed sign information specifically at
\[
\left\|
\frac1\pi[\operatorname{diag}(h_j),\mathsf H_m^{\mathrm d}]
\right\|
\le2\max_j|h_j|.
\]
The explicit upper envelope in (8), divided by \(m^\eta\), diverges for every \(\eta<1/2\). That says this **estimate** cannot supply SP; it does not say the actual signed form fails.

The remaining source inequality can now be stated without an unknown polar factor. Define
\[
\mathsf T_m
=\frac1\pi[\operatorname{diag}(h_j),\mathsf H_m^{\mathrm d}],
\qquad
\mathsf S_m(r)
=\operatorname{diag}\bigl(a(\omega_j)-d_j+r\bigr).
\]
The first unsupplied bound is
\[
\boxed{
\forall\eta>0\ \exists C_\eta\
\exists\text{ unbounded original }\mathcal G_\eta:
\quad
\mathsf S_m(C_\eta m^\eta)-\mathsf T_m\succeq0
\quad(m\in\mathcal G_\eta).
}
\tag{21}
\]
It would imply
\[
K_m\succeq-(C_\eta m^\eta+c_A+20)I.
\]

Conversely, the difference between \(K_m\) and
\[
\operatorname{diag}(a(\omega_j)-d_j)-\mathsf T_m
\]
has norm at most \(c_A+28\). Thus (21) is equivalent to the consumer at subpolynomial scale. **That equivalence is not claimed as progress.** The progress is the proved full-carrier bound (8), the constant-\(20\) archimedean budget, and the separated-block estimate (19).

### Cheapest source-specific discriminator

For a proposed same-cell \(r\), put
\[
q_j=a(\omega_j)-d_j+r.
\]
Every certificate for (21) must satisfy, on that same cell,
\[
q_j\ge0,\qquad q_k\ge0,\qquad
\boxed{
q_jq_k\ge
\frac{(h_j-h_k)^2}{\pi^2(j-k)^2}.
}
\tag{22}
\]
This is the exact **two-mode principal determinant**, with lower eigenvalue
\[
\frac{
q_j+q_k-
\sqrt{(q_j-q_k)^2+
4(h_j-h_k)^2/[\pi^2(j-k)^2]}
}{2}.
\]
A certified negative upper envelope refutes the proposed certificate. Passing all such pairs does not certify the full matrix or produce a common good subsequence.

**Closeout:** the registered prediction of a dimension-free, every-logarithmic-power improvement is confirmed. SP, the common-cell subpolynomial subsequence, and RH remain open. No additional theorem-shape kill is claimed.

**Next mathematical step:** estimate the **signed divided-difference commutator against the actual same-cell diagonal slack in (21)** on contiguous and neighboring frequency bands, with their cross terms retained. Equation (19) already pays the polylogarithmic head–top interaction; equation (22) is the first falsifier for a proposed weighted block estimate.
