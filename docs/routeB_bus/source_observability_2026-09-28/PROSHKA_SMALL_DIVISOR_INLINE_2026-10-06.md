# Growth answer8 — exact inline capture

Chat `6ac54396-d878-83eb-ae29-35d2bdd2262b`; question `e6511959-8e16-478b-86ea-0788efd52251`.
Answer `f63e6100-9d91-4e30-b5c5-fca1153e22fa`; untruncated read_thread capture. Claims pending audit.

---

Ы — **I obtained a signed small-divisor cancellation estimate on the original carrier. The remaining large-factor Hankel term is still unbounded at the required scale.**

On the specified strip \(X=\lfloor m/L^8\rfloor\), the part estimated below costs at most
\[
\boxed{40000L^{11/2}\log(2L)}
\]
in the **original operator norm**, simultaneously for all complex carrier vectors. In particular, it applies to the **actual** \(J_rv\), without replacing its endpoint restrictions by independent functions.

Accounting for all arithmetic ranges also gives an explicit
\[
O\!\left(m^{1/4}L^{3/2}\log(2L)\right)
\]
remainder after an exact divisor decomposition of the full matrix. **This quarter power is a remainder bound—not a negative-bottom bound.** Its unestimated complement remains signed and potentially large.

The regular equation then leaves one explicit large-factor endpoint pairing, with the full Schur correction intact. I identify below why the particular oscillatory estimate that pays the small-divisor part does not estimate that remaining pairing.

:chatgpt-content-reference{index="3"}[Complete PAPER verdict and machine-readable ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q08.md)

## 1. Split the actual signed measure, not its prime and pole norms

**[FINITE_CELL | PAPER]**

Write the supplied measure in the integer variable as
\[
d\boldsymbol\mu(x)=
\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_n(dx)
-\left(x^{-1/2}-x^{-3/2}\right)dx.
\]
For a real signed measure \(\sigma\), define its original-carrier compression
\[
\mathcal C[\sigma]
=
P_m\left[\int(S_{\log x}+S_{\log x}^{*})\,d\sigma(x)\right]P_m.
\]
Thus
\[
\mathcal C[d\boldsymbol\mu]
=\operatorname{compression}(\mathcal P-R_++R+\text{adjoint}),
\]
and the requested matrix is exactly
\[
\mathsf H_m(r):=\mathsf S(r)-\mathsf T
=\operatorname{diag}(a(\omega_j))+rI-\mathcal C[d\boldsymbol\mu].
\]

Put
\[
U=\lceil L\rceil,\qquad \Omega=\frac{2\pi m}{L},
\]
and distinguish the **Möbius function** \(\mu_{\mathrm M}\) from the signed measure. Define
\[
\alpha_U(a)=\sum_{\substack{d\mid a\\d>U}}\mu_{\mathrm M}(d).
\]
It vanishes for \(a\le U\), while for \(a>U\),
\[
\alpha_U(a)=-\sum_{\substack{d\mid a\\d\le U}}\mu_{\mathrm M}(d).
\]

For every \(n>U\), the exact truncated convolution identity is
\[
\begin{aligned}
\Lambda(n)&=\lambda_{\mathrm I}(n)+\lambda_{\mathrm{II}}(n),\\
\lambda_{\mathrm I}(n)
&=
\sum_{\substack{d\le U\\d\mid n}}\mu_{\mathrm M}(d)\log(n/d)
-
\sum_{\substack{d,\ell\le U\\d\ell\mid n}}
\mu_{\mathrm M}(d)\Lambda(\ell),\\
\lambda_{\mathrm{II}}(n)
&=
\sum_{\substack{ab=n\\a>U,\ b>U}}
\alpha_U(a)\Lambda(b).
\end{aligned}
\tag{1}
\]
This is **Vaughan’s identity**, in the form recorded as equation (18.2.1) in Kedlaya’s notes. Here it follows directly by splitting \(\mu_{\mathrm M}\) and \(\Lambda\) at \(U\), and using \(\log=1*\Lambda\) and \(\mu_{\mathrm M}*1=\varepsilon\). No distribution theorem is needed for the identity. :chatgpt-content-reference{index="0"}

The prime-power check matters: for a prime \(p>U\),
\[
\lambda_{\mathrm I}(p^2)=2\log p,\qquad
\lambda_{\mathrm{II}}(p^2)=-\log p,
\]
so their sum is the required \(\Lambda(p^2)=\log p\). For distinct primes \(p,q>U\), the two contributions at \(pq\) cancel. Neither composites nor higher powers may be dropped from this decomposition.

Define the finite coefficients
\[
A_U=\sum_{d\le U}\frac{\mu_{\mathrm M}(d)}d,\qquad
B_U=\sum_{d\le U}\frac{\mu_{\mathrm M}(d)\log d}d,\qquad
C_U=\sum_{\ell\le U}\frac{\Lambda(\ell)}\ell,
\]
and
\[
\kappa_U(x)=A_U\log x-B_U-A_UC_U.
\]

On any interval contained in \((U,m]\), make the **exact signed split**
\[
\begin{aligned}
d\boldsymbol\mu_{\mathrm I}(x)
&=
\sum_n\frac{\lambda_{\mathrm I}(n)}{\sqrt n}\delta_n(dx)
-\kappa_U(x)x^{-1/2}\,dx,\\
d\boldsymbol\mu_{\mathrm{II}}(x)
&=
\sum_n\frac{\lambda_{\mathrm{II}}(n)}{\sqrt n}\delta_n(dx)
-(1-\kappa_U(x))x^{-1/2}\,dx+x^{-3/2}\,dx.
\end{aligned}
\tag{2}
\]
Their sum is the original measure.

**No smallness of \(A_U\), \(B_U\), or \(1-\kappa_U\) is assumed.** In particular, the continuous compensator in the second line remains part of the unestimated signed interaction.

## 2. The small-divisor quadrature has a uniform original-frequency bound

**[FINITE_CELL | PAPER]**

The concrete source lemma is the following. Suppose
\[
Y\ge4U^2,\qquad Y\le Z\le\min(2Y,m),\qquad |t|\le\Omega,\qquad q\le U^2.
\]
Then
\[
\begin{aligned}
&\left|
\sum_{Y\le qk<Z}(qk)^{-1/2-it}
-\frac1q\int_Y^Zx^{-1/2-it}\,dx
\right|
\le \frac{100(1+\sqrt\Omega)}{\sqrt Y},\\
&\left|
\sum_{Y\le qk<Z}(qk)^{-1/2-it}\log k
-\frac1q\int_Y^Zx^{-1/2-it}\log(x/q)\,dx
\right|
\le \frac{300L(1+\sqrt\Omega)}{\sqrt Y}.
\end{aligned}
\tag{3}
\]
These estimates include every intermediate cutoff. Changing inclusion of an endpoint changes at most two summands, already covered by the constants.

### Small frequencies: subtract the integral before estimating

Put \(N=Y/q\ge4\). On every subinterval of \([N,2N]\), for \(|t|\le N\),
\[
\left|\sum k^{-it}-\int u^{-it}\,du\right|\le10.
\tag{4}
\]

For completeness, Euler summation leaves bounded endpoint terms and
\[
\int \bigl(\{u\}-\tfrac12\bigr)(-it/u)e^{-it\log u}\,du.
\]
In the Abel-regularized Fourier expansion of the sawtooth, the nonzero mode \(h\) has phase
\[
\phi_h(u)=2\pi hu-t\log u,\qquad
|\phi_h'(u)|\ge5|h|.
\]
Integration by parts bounds that mode, before its sawtooth coefficient, by
\[
\frac{3}{5|h|}+\frac1{50h^2}.
\]
Multiplication by the Fourier coefficient \((2\pi h)^{-1}\) makes the bounds summable. The endpoint terms and this sum are less than \(10\). The case \(t=0\) is the ordinary counting discrepancy; negative \(t\) follows by conjugation.

This step would be false at the stated scale for the uncentered sum. It is the **sum-minus-integral** estimate that is being proved.

### Higher frequencies: integer aliases are paid

For \(t>N\), take
\[
g(u)=-\frac{t}{2\pi}\log u.
\]
On \([N,2N]\),
\[
\frac{t}{8\pi N^2}\le g''(u)\le\frac{t}{2\pi N^2}.
\]
Arias de Reyna’s Lemma 5 gives, for a real \(C^2\) phase with \(0<\lambda\le g''\le\Lambda\), on an interval of length \(H\ge1\),
\[
\left|\sum e(g(k))\right|
\le\frac{A}{\sqrt\lambda}(\Lambda H+2),
\qquad A<3.
\]
These hypotheses apply exactly here, with \(H\le N\); intervals shorter than one are handled directly. :chatgpt-content-reference{index="1"}

Consequently, the sum costs at most
\[
4+3\sqrt t+\frac{31N}{\sqrt t},
\]
while its integral costs at most \(4N/t\). Since \(t>N\), their discrepancy is at most \(50\sqrt t\).

Finally, **partial summation** against \((qu)^{-1/2}\) costs \(Y^{-1/2}\). Against \((qu)^{-1/2}\log u\), the endpoint size plus variation is at most \(3L/\sqrt Y\). This proves (3).

There is no assumption that the original top frequency lies below the sampling frequency. The second case explicitly covers that failure.

## 3. Spend the estimate on the coherent \(d,h\) matrix

**[COFINAL_FAMILY | PAPER]**

Set
\[
M_{U,L}=3UL+U^2\log(2U).
\]
Summing (3) over the two small-divisor terms in (1), **with their corresponding continuous terms**, gives
\[
\sup_{\substack{|t|\le\Omega\\Y\le Z\le\min(2Y,m)}}
\left|\int_{[Y,Z)}x^{-it}\,d\boldsymbol\mu_{\mathrm I}(x)\right|
\le
\frac{100M_{U,L}(1+\sqrt\Omega)}{\sqrt Y}.
\tag{5}
\]
For the second term, only
\[
\sum_{\ell\le U}\Lambda(\ell)\le U\log U
\]
is used.

Apply the accepted matrix identity to this **single signed primitive**. If its cumulative transform is bounded by \(M\), its diagonal costs at most \(2M\), and its discrete-Hilbert commutator costs at most \(2M\). Therefore
\[
\boxed{
\|C_{\mathrm I,[Y,Z)}\|
\le
\frac{400M_{U,L}(1+\sqrt\Omega)}{\sqrt Y}.
}
\tag{6}
\]

The diagonal and divided differences are still generated from the same measure. The new input is the independently proved quadrature cancellation (3), **not another application of the old \(\mathcal R_m\) bound to the full prime source**.

For \(X=\lfloor m/L^8\rfloor\), eventually
\[
M_{U,L}\le20L^2\log(2L),\qquad
X\ge\frac{m}{2L^8},\qquad
\frac{1+\sqrt\Omega}{\sqrt X}\le5L^{7/2}.
\]
Thus
\[
\boxed{
\|C_{\mathrm I,X}\|
\le40000L^{11/2}\log(2L).
}
\tag{7}
\]

In particular, for the **actual corrected vector**,
\[
\boxed{
\begin{aligned}
&\left|
\langle v,C_XJ_rv\rangle
-\langle v,C_{\mathrm{II},X}J_rv\rangle
\right|\\
&\qquad\le
40000L^{11/2}\log(2L)\,
\|v\|\,\|J_rv\|.
\end{aligned}
}
\tag{8}
\]
The same estimate holds with both arguments equal to \(J_rv\).

This is a direct bilinear-form estimate. All finite-carrier projections remain in the operators; there is no squaring step that discards the negative projection-loss term.

## 4. Account for the rest of the source

**[COFINAL_FAMILY | PAPER]**

Choose
\[
Y_0=\lceil\sqrt m\rceil.
\]
For sufficiently large \(m\), \(Y_0\ge4U^2\).

Keep the original source on \([1,Y_0)\) intact. Its norm is bounded by
\[
\|C_{<Y_0}\|
\le8\sqrt{Y_0}(1+\log Y_0),
\tag{9}
\]
using \(\Lambda(n)\le\log n\), the elementary sum of \(n^{-1/2}\), and the continuous mass.

For the Type-I part on \([Y_0,m]\), sum (6) over dyadic intervals. The inverse square roots of their left endpoints sum to less than \(4/\sqrt{Y_0}\), so
\[
\|C_{\mathrm I,[Y_0,m]}\|
\le
\frac{1600M_{U,L}(1+\sqrt\Omega)}{\sqrt{Y_0}}.
\tag{10}
\]
The final interval may be shorter. Its cutoffs were included in (3). The atom at \(m\) is retained and has zero compressed action because \(S_L=0\).

Since \(0\le a(\omega_j)\le L+8\) eventually, define
\[
\boxed{
\Delta_m=
L+8+
8\sqrt{Y_0}(1+\log Y_0)
+\frac{1600M_{U,L}(1+\sqrt\Omega)}{\sqrt{Y_0}}.
}
\tag{11}
\]
Then
\[
\boxed{
\mathsf H_m(r)
=rI-C_{\mathrm{II},[Y_0,m]}+F_m,
\qquad
\|F_m\|\le\Delta_m,
}
\tag{12}
\]
where the remainder is explicitly
\[
F_m=\operatorname{diag}a-C_{<Y_0}-C_{\mathrm I,[Y_0,m]}.
\]
In particular,
\[
\Delta_m\le10^6m^{1/4}L^{3/2}\log(2L)
\]
eventually.

For the **original full Weil form**, retaining the archimedean form gives the stronger one-sided statement
\[
\boxed{
\begin{aligned}
W(f)\ge{}&
D_{\rm arch}(f)
-\bigl(c_A+\delta_m\bigr)\|f\|^2
+2\langle f,(R+R^*)f\rangle\\
&-\langle f,C_{\mathrm{II},[Y_0,m]}f\rangle,
\qquad
\delta_m=\Delta_m-(L+8).
\end{aligned}
}
\tag{13}
\]
This holds simultaneously for all original complex \(f\).

**It is not a quarter-power floor.** The last signed form is unestimated, and its continuous compensator has not been declared small. The result pays specified source components at that scale; it does not pay their remaining complement.

## 5. Use the actual regular equation

**[FINITE_CELL | PAPER]**

Retain the repaired source spaces
\[
\mathcal R=\ker B,\qquad \mathcal E=\mathcal R^\perp.
\]
Let \(A_r\) and \(B_r\) be the **actual** regular and regular–exceptional blocks of \(\mathsf H_m(r)\). For \(r>\epsilon_m\),
\[
A_r\succeq(r-\epsilon_m)I,
\qquad
f=J_rv=v+y,
\qquad
y=-A_r^{-1}B_rv.
\]

Insert (12) into the regular equation. It gives
\[
\boxed{
P_{\mathcal R}C_{\mathrm{II},[Y_0,m]}f
=ry+P_{\mathcal R}F_mf,
}
\]
hence
\[
\boxed{
\left\|
P_{\mathcal R}C_{\mathrm{II},[Y_0,m]}f-ry
\right\|
\le\Delta_m\|f\|.
}
\tag{14}
\]

This is the regular component of the remaining arithmetic interaction, constrained with an explicit original-norm error.

Now
\[
\langle y,\mathsf H_m(r)f\rangle=0.
\]
Therefore
\[
\langle v,\mathfrak S_m(r)v\rangle
=\langle f,\mathsf H_m(r)f\rangle
=\langle v,\mathsf H_m(r)f\rangle.
\]
Using (12) again,
\[
\boxed{
\begin{aligned}
&r\|v\|^2
-\Re\langle v,C_{\mathrm{II},[Y_0,m]}J_rv\rangle
-\Delta_m\|v\|\,\|J_rv\|\\
&\qquad\le
\langle v,\mathfrak S_m(r)v\rangle\\
&\qquad\le
r\|v\|^2
-\Re\langle v,C_{\mathrm{II},[Y_0,m]}J_rv\rangle
+\Delta_m\|v\|\,\|J_rv\|.
\end{aligned}
}
\tag{15}
\]

The correction \(B_r^*A_r^{-1}B_r\) remains fully present through \(J_r\). **There is no replacement of \(\|J_rv\|\) by \(\|v\|\).** Nor has the regular block been recomputed for the altered arithmetic decomposition.

## 6. The surviving term is an explicit endpoint Hankel pairing

**[FINITE_CELL | PAPER]**

Put
\[
b_0=L-\log Y_0\le L/2.
\]
All remaining shifts run from \([0,b_0]\) to \([L-b_0,L]\).

For actual carrier vectors \(v,f\), define
\[
\mathcal K_{v,f}(h)
=
\int_0^h
\left[
\overline{v(L-u)}f(h-u)
+\overline{v(h-u)}f(L-u)
\right]du.
\tag{16}
\]
Because the head and tail are disjoint,
\[
|\mathcal K_{v,f}(h)|\le\|v\|\,\|f\|.
\]
Differentiating while retaining the two endpoint terms also gives
\[
|\mathcal K'_{v,f}(h)|
\le4\Omega\|v\|\,\|f\|.
\tag{17}
\]
Here the actual bounds
\[
|f(t)|\le\sqrt{\frac{2m+1}{L}}\|f\|,
\qquad
\|f'\|\le\Omega\|f\|
\]
pay the endpoint and derivative costs. No vanishing trace is assumed.

Push the residual measure forward by \(h=L-\log x\):
\[
\begin{aligned}
d\nu_{\mathrm{II}}(h)
={}&
\sum_{\substack{a,b>U\\Y_0\le ab\le m}}
\frac{\alpha_U(a)\Lambda(b)}{\sqrt{ab}}\,
\delta_{L-\log(ab)}(dh)\\
&-\left[
(1-\kappa_U(me^{-h}))\sqrt m\,e^{-h/2}
-m^{-1/2}e^{h/2}
\right]dh,
\quad 0\le h\le b_0.
\end{aligned}
\tag{18}
\]
Then the unestimated scalar in (15) is exactly
\[
\boxed{
\mathcal B_{U,m}(v,J_rv)
=
\int_0^{b_0}\mathcal K_{v,J_rv}(h)\,d\nu_{\mathrm{II}}(h).
}
\tag{19}
\]

This retains the **prime-power variable \(b\)**, the signed finite-divisor coefficient \(\alpha_U(a)\), the hyperbolic constraint on \(ab\), and the continuous compensator.

At \(ab=m\), \(h=0\) and \(\mathcal K_{v,f}(0)=0\). At the other cutoffs, atoms follow the original half-open convention. The original short strip is simply a subinterval of (18); its discrepancy is paid by (8), while (9)–(15) account for the other ranges.

For \(v=f\), the kernel in (16) is the direct signed endpoint form. For the Schur calculation, it is evaluated on **\(v,J_rv\)**, not on independently chosen endpoint profiles.

## 7. Where this construction stops

There is a further **exact source lemma** for the coefficient \(\alpha_U\). For every real \(u\ge U\),
\[
\boxed{
\begin{aligned}
\sum_{U<a\le u}\alpha_U(a)
&=-A_U(u-U)+\rho_U(u),\\
\rho_U(u)
&=
\sum_{d\le U}\mu_{\mathrm M}(d)
\left(\{u/d\}-\{U/d\}\right),\\
|\rho_U(u)|&\le U.
\end{aligned}
}
\tag{20}
\]
Indeed,
\[
\sum_{a\le u}\alpha_U(a)
=
1-\sum_{d\le U}\mu_{\mathrm M}(d)\lfloor u/d\rfloor,
\]
and the sum vanishes at \(u=U\).

For fixed prime power \(b>U\), summation by parts against
\[
W_b(u)
=
u^{-1/2}\mathcal K_{v,J_rv}(L-\log(bu))
\]
leaves the signed flux
\[
\boxed{
[\rho_U(u)W_b(u)]_{\mathrm{lower}}^{\mathrm{upper}}
-
\int \rho_U(u)W_b'(u)\,du,
}
\tag{21}
\]
multiplied by \(\Lambda(b)/\sqrt b\), with the exact restrictions
\[
u>U,\qquad Y_0\le bu\le m.
\]
The upper product endpoint vanishes when \(bu=m\). The lower endpoint generally does not.

The main integrals from this summation by parts combine with the continuous compensator in (18). Writing
\[
\psi_1(x)=\sum_{n\le x}\frac{\Lambda(n)}n,
\]
their combined density in the integer variable is
\[
\boxed{
\left[
A_U\bigl(\log x-\psi_1(x/U)\bigr)-B_U-1
\right]x^{-1/2}
+x^{-3/2}.
}
\tag{22}
\]

**The prime-weighted flux (21) and density (22) must remain together.** The bound \(|\rho_U|\le U\) is proved, but using it with the free derivative estimate (17) incurs the full factor \(\Omega\). That does not close an improved signed form bound. Equation (14) controls the regular projection of the complete operator, not this derivative or the signs of the \(b\)-sum.

There is also a precise obstruction to continuing the successful small-divisor calculation by the same oscillatory argument. For a same-frequency term,
\[
e^{-i\omega\log(ab)}
e^{i\omega\log(ab')}
=
e^{-i\omega\log(b/b')}.
\tag{23}
\]
After bilinear Cauchy differencing, this phase has **zero curvature in \(a\)**. The positive-curvature hypothesis used in Section 2 is false there.

This is not a counterexample to every Type-II estimate: cross-frequency terms can retain oscillation, and arithmetic cancellation in \(\alpha_U\) remains available. It identifies exactly why the tested integer quadrature lemma does not pay the surviving cross-factor interaction.

## Verdict and next step

The registered small-divisor prediction is confirmed. The proved estimates remove that explicit portion of the source at a **polylogarithmic cost on the requested strip**, and give an **all-range quarter-power remainder budget**. They apply to the original carrier and to the actual Schur-corrected vectors.

The remaining sign is not supplied. In particular, if
\[
M_r(v)=r\|v\|^2-\Re\mathcal B_{U,m}(v,J_rv),
\]
then the available discriminator is precisely
\[
M_r(v)-\Delta_m\|v\|\,\|J_rv\|
\le
\langle v,\mathfrak S_m(r)v\rangle
\le
M_r(v)+\Delta_m\|v\|\,\|J_rv\|.
\]
A negative upper endpoint certifies a violation on that cell. A nonnegative lower envelope valid for every exceptional \(v\) would certify the cell. A straddling interval supplies neither conclusion.

**No new whole-matrix bottom floor, common-cell SP subsequence, or RH claim follows.** The earlier regular-subspace theorem and repaired high-zero budget are unchanged.

**Next mathematical step:** estimate the prime-weighted signed flux (21) together with its compensator (22) on \((v,J_rv)\), using the regular constraint (14) rather than the free endpoint derivative bound. The small-divisor sums now have a proved budget; the unresolved part is the cross-factor arithmetic sign.
