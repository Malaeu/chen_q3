Ы. **I have not proved the requested bound \(\widehat d_m\ge-1/(128m)\). I did obtain an arithmetic cancellation estimate with an error smaller than \(1/m\), but for a specific component of the complete prime sum.**

The new result is:

\[
\boxed{
\widehat{\mathsf P}_m
=
\mathsf P_m^{<Q}
+\mathsf V_m
+\mathsf{End}_m
+\mathsf{Err}_m^{\rm I},
\qquad
-\varepsilon_m^{\rm I}\widehat{\mathsf E}_m
\preceq\mathsf{Err}_m^{\rm I}
\preceq\varepsilon_m^{\rm I}\widehat{\mathsf E}_m,
\qquad
\varepsilon_m^{\rm I}=o(1/m).
}
\tag{1}
\]

Here \(\mathsf{End}_m\) is an **explicit boundary expression**, not an unknown error. The remaining \(\mathsf V_m\) is a **Möbius-weighted bilinear correlation**, written out below. The lower arithmetic range \(\mathsf P_m^{<Q}\) is retained exactly.

This estimates the **diagonal and Hilbert cross term together**. It does not truncate another Fourier tail, change \(U_m\), or infer cancellation from a positive average.

## 1. The arithmetic object remains unchanged

Keep
\[
m=m_j,\qquad N=m,\qquad L=\log m,\qquad
\Omega=\frac{2\pi m}{L},\qquad
\omega_n=\frac{2\pi n}{L}.
\]

The prescribed \(U_m\) is still the minimum Rayleigh quotient on the actual window-coefficient span of \(G,G''\), with its original complex Gram matrix. :chatgpt-content-reference{index="0"}

Use the already-paid band
\[
\mathcal N_m=\{m+1,\ldots,3m\},
\]
and exactly
\[
(\mathsf S_m)_{n,:}
=
\sqrt{\frac2L}(-1)^n\widehat G(\omega_n)
(1,-\omega_n^2),
\qquad
b=\mathsf S_mz,
\qquad
\|b\|^2=z^*\widehat{\mathsf E}_mz.
\tag{2}
\]

For the even band synthesis
\[
\rho_b(t)=
\sqrt{\frac2L}
\sum_{n\in\mathcal N_m}b_n(-1)^n
\cos(\omega_nt)\mathbf1_{[-L/2,L/2]}(t),
\]
write
\[
\mathcal J_b(s)=2C_{\rho_b}(s),
\qquad
C_v(s)=\int_{\mathbb R}\overline{v(t)}v(t+s)\,dt.
\]

The exact joint atom is
\[
\mathcal J_{n\ell}(s)=
\begin{cases}
2(1-s/L)\cos(\omega_ns)
-\dfrac{\sin(\omega_ns)}{\pi n},&n=\ell,\\[2mm]
\dfrac{2[\ell\sin(\omega_\ell s)-n\sin(\omega_ns)]}
{\pi(n^2-\ell^2)},&n\ne\ell.
\end{cases}
\tag{3}
\]

Thus \(\mathcal J_b(s)=b^*\mathcal J(s)b\). In particular,
\[
\boxed{\mathcal J(L)=0.}
\]

The **reflected boundary term** and separate diagonal are already combined in (3). This is the accepted source atom, including both phases. 

For real arrays \(s_n,c_n\), define the joint quadratic expression
\[
\begin{aligned}
\mathfrak Q_b(s,c)
={}&
\sum_n\left(2c_n-\frac{s_n}{\pi n}\right)|b_n|^2\\
&-\frac4\pi\operatorname{Re}
\sum_n ns_n\overline{b_n}(\mathcal Hb)_n,
\qquad
(\mathcal Hb)_n=
\sum_{\ell\ne n}\frac{b_\ell}{n^2-\ell^2}.
\end{aligned}
\tag{4}
\]

The complete band prime form uses
\[
s_n=\sum_{q=2}^m\frac{\Lambda(q)}{\sqrt q}
\sin(\omega_n\log q),
\]
\[
c_n=\sum_{q=2}^m\frac{\Lambda(q)}{\sqrt q}
\left(1-\frac{\log q}{L}\right)\cos(\omega_n\log q).
\tag{5}
\]

All prime powers and mixed coefficients remain.

## 2. Apply an exact divisor identity before estimating oscillation

The applicable literature alias is **Vaughan’s identity**: it splits the von Mangoldt weight into two short-divisor sums, called **Type I**, and a remaining bilinear sum, called **Type II**. I checked the identity in Kedlaya, equation (18.2.1), and Tao, Lemma 18. No distribution theorem or mean-square conclusion from those sources is imported. :chatgpt-content-reference{index="2"}

Let \(\nu(d)\) denote the **Möbius function**, avoiding a collision with the existing mass envelope \(\mu_m\). Choose deterministically
\[
k=\lfloor L^{1/8}\rfloor,
\qquad
Q=\left\lceil\frac{12\pi k^2m}{L}\right\rceil.
\tag{6}
\]
Eventually,
\[
k\ge1,\qquad k<Q<m,\qquad Q=o(m).
\]

Define
\[
\alpha_k(d)=
\sum_{\substack{uv=d\\u,v\le k}}\nu(u)\Lambda(v),
\]
\[
\beta_k(r)=
\sum_{\substack{c\mid r\\c>k}}\Lambda(c)
=
\log r-\sum_{\substack{c\mid r\\c\le k}}\Lambda(c).
\tag{7}
\]

For every \(q>k\),
\[
\boxed{
\Lambda(q)=
\sum_{\substack{d\mid q\\d\le k}}\nu(d)\log(q/d)
-\sum_{\substack{d\mid q\\d\le k^2}}\alpha_k(d)
+\sum_{\substack{dr=q\\d>k,\ r>k}}\nu(d)\beta_k(r).
}
\tag{8}
\]

For completeness, this follows by splitting \(\nu\) and \(\Lambda\) at \(k\) in the convolution identities
\[
\nu*1=\epsilon,\qquad 1*\Lambda=\log.
\]
They give
\[
\Lambda=\Lambda_{\le k}
+\nu_{\le k}*\log
-\nu_{\le k}*\Lambda_{\le k}*1
+\nu_{>k}*\Lambda_{>k}*1.
\]
At \(q>k\), the first term vanishes.

Apply (8) to the **whole joint atom** \(\mathcal J_b(\log q)/\sqrt q\). Then
\[
b^*\mathcal P_m^{\rm band}b
=
\mathscr L_m(b)+\mathscr I_m(b)+\mathscr V_m(b),
\tag{9}
\]
where
\[
\mathscr L_m(b)=
\sum_{2\le q<Q}\frac{\Lambda(q)}{\sqrt q}\mathcal J_b(\log q),
\tag{10}
\]
\[
\begin{aligned}
\mathscr I_m(b)={}&
\sum_{d\le k}\nu(d)
\sum_{Q\le dr\le m}
\frac{\log r}{\sqrt{dr}}\mathcal J_b(\log(dr))\\
&-
\sum_{d\le k^2}\alpha_k(d)
\sum_{Q\le dr\le m}
\frac1{\sqrt{dr}}\mathcal J_b(\log(dr)),
\end{aligned}
\tag{11}
\]
and
\[
\boxed{
\mathscr V_m(b)=
\sum_{d>k}\frac{\nu(d)}{\sqrt d}
\sum_{\substack{r>k\\Q\le dr\le m}}
\frac{\beta_k(r)}{\sqrt r}
\mathcal J_b(\log d+\log r).
}
\tag{12}
\]

These are exact finite sums. Composite arguments introduced by the divisor decomposition cancel according to (8); they do not replace the original prime-power weighting.

## 3. New cancellation lemma: Type I becomes explicit endpoints

Fix
\[
d\le k^2,\qquad t\in[\Omega,3\Omega],
\]
and write
\[
A_d=\lceil Q/d\rceil,\qquad B_d=\lfloor m/d\rfloor.
\]

The four amplitudes needed for the sine and weighted cosine fields are
\[
a_{d,j,\ell}(x)=
\frac{(\log x)^j}{\sqrt{dx}}\,
\vartheta_\ell(\log(dx)),
\qquad j,\ell\in\{0,1\},
\]
where
\[
\vartheta_0(s)=1,\qquad \vartheta_1(s)=1-s/L.
\tag{13}
\]

Introduce
\[
\delta_t(x)=t\log(1+1/x),
\qquad
F_{d,j,\ell,t}(x)=
\frac{a_{d,j,\ell}(x)}{e^{i\delta_t(x)}-1}.
\tag{14}
\]

The arithmetic cut in (6) ensures, throughout the summation interval,
\[
\boxed{
0<\delta_t(x)\le\frac{t}{x}
\le\frac{3\Omega d}{Q}\le\frac12.
}
\tag{15}
\]

This is **nonresonance**: the discrete phase increment stays away from every nonzero multiple of \(2\pi\). Its lower endpoint may be small, but its exact dependence is retained.

Define the explicit boundary expression
\[
\boxed{
\mathcal E_{d,j,\ell}(t)
=
d^{it}
\left[
F_{d,j,\ell,t}(B_d)(B_d+1)^{it}
-
F_{d,j,\ell,t}(A_d)A_d^{it}
\right].
}
\tag{16}
\]

Then
\[
\boxed{
\left|
\sum_{r=A_d}^{B_d}
a_{d,j,\ell}(r)(dr)^{it}
-
\mathcal E_{d,j,\ell}(t)
\right|
\le
\frac{1000L^3}{d\,m\sqrt Q}.
}
\tag{17}
\]

Also,
\[
\boxed{
|\mathcal E_{d,j,\ell}(t)|
\le\frac{2L^2}{d\sqrt m}.
}
\tag{18}
\]

Both statements hold uniformly in the four weights and the entire existing frequency band. Empty ranges contribute zero.

### Proof of the cancellation bound

Set \(\xi_r=r^{it}\) and abbreviate \(F_r=F_{d,j,\ell,t}(r)\). By construction,
\[
a(r)\xi_r=F_r(\xi_{r+1}-\xi_r).
\]
Finite summation gives the exact identity
\[
\boxed{
\sum_{r=A}^{B}a(r)(dr)^{it}
=
\mathcal E_{d,j,\ell}(t)
-
d^{it}\sum_{r=A+1}^{B}(F_r-F_{r-1})r^{it}.
}
\tag{19}
\]

The phase at the upper endpoint is \(B+1\), not \(B\). The remainder has a minus sign.

To bound that remainder, first note that
\[
q_r=(e^{i\delta_t(r)}-1)^{-1}
=
-\frac12-\frac i2\cot\frac{\delta_t(r)}2.
\]
The increments decrease in \((0,1/2]\), so the imaginary parts of \(q_r\) are monotone. Applying (19) with amplitude \(1\) gives, for every subinterval,
\[
\boxed{
\left|\sum_{r=u}^{v}r^{it}\right|
\le\frac{4\pi(B+1)}t.
}
\tag{20}
\]

This is a discrete first-derivative estimate proved with the actual phase convention.

Direct differentiation of the four amplitudes gives
\[
|a(x)|\le\frac{2L}{\sqrt d\sqrt x},\qquad
|a'(x)|\le\frac{5L}{\sqrt d\,x^{3/2}},\qquad
|a''(x)|\le\frac{10L}{\sqrt d\,x^{5/2}}.
\tag{21}
\]

Using
\[
\delta_t(x)\ge\frac{t}{2x},\qquad
|\delta_t'(x)|\le\frac{t}{x^2},\qquad
|\delta_t''(x)|\le\frac{3t}{x^3},
\]
and differentiating the denominator in (14), one obtains
\[
\boxed{
|F'(x)|\le\frac{36L}{t\sqrt d\sqrt x},
\qquad
|F''(x)|\le\frac{400L}{t\sqrt d\,x^{3/2}}.
}
\tag{22}
\]

For \(g_r=F_r-F_{r-1}\), this implies
\[
|g_B|+\sum_{r=A+1}^{B-1}|g_{r+1}-g_r|
\le
\frac{836L}{t\sqrt d\sqrt A}.
\]

Apply **Abel summation**—finite integration by parts—to the remainder in (19), using (20):
\[
|\text{remainder}|
\le
\frac{3344\pi L(B+1)}
{t^2\sqrt d\sqrt A}.
\]
Since
\[
B+1\le\frac{2m}{d},\qquad
\sqrt{dA}\ge\sqrt Q,\qquad
t\ge\frac{2\pi m}{L},
\]
this is at most
\[
\frac{1672}{\pi}\frac{L^3}{dm\sqrt Q},
\]
which proves (17). Bounding \(F\) at the two endpoints proves (18).

**The gain comes from oscillation twice:** first in the exact discrete antiderivative, then in the remainder. Summing absolute values of the original summands would not give (17).

## 4. Transfer this saving to the contracted Hilbert expression

For \(\ell=0,1\), define
\[
\mathcal E_\ell(t)=
\sum_{d\le k}\nu(d)\mathcal E_{d,1,\ell}(t)
-
\sum_{d\le k^2}\alpha_k(d)\mathcal E_{d,0,\ell}(t).
\tag{23}
\]
Use the real arrays
\[
s_n^{\rm bd}=\Im\mathcal E_0(\omega_n),
\qquad
c_n^{\rm bd}=\Re\mathcal E_1(\omega_n),
\]
and retain the full endpoint form
\[
\boxed{
\mathscr{End}_m(b)=\mathfrak Q_b(s^{\rm bd},c^{\rm bd}).
}
\tag{24}
\]

Let
\[
H_k=\sum_{d=1}^k\frac1d,\qquad
W_k=H_k+(\log k)H_k^2.
\]
Then
\[
\sum_{d\le k}\frac{|\nu(d)|}{d}
+
\sum_{d\le k^2}\frac{|\alpha_k(d)|}{d}
\le W_k.
\tag{25}
\]
Indeed,
\[
\sum_{d\le k^2}\frac{|\alpha_k(d)|}{d}
\le H_k\sum_{c\le k}\frac{\Lambda(c)}c
\le(\log k)H_k^2.
\]

Therefore (17) bounds the error in **each** Type I sine or weighted cosine field by
\[
\rho_m=\frac{1000L^3W_k}{m\sqrt Q}.
\tag{26}
\]

Now estimate their joint form, not its prime atoms separately. The finite Hilbert matrix satisfies
\[
\|\mathcal H\|
\le\frac{H_{2m}}{m+1}.
\]
Consequently, if both real error arrays are bounded by \(\rho_m\), equation (4) gives
\[
|\mathfrak Q_b(\text{errors})|
\le
\mathfrak C_m\rho_m\|b\|^2,
\]
where
\[
\mathfrak C_m=
2+\frac1{\pi(m+1)}+\frac{12}{\pi}H_{2m}.
\]

Thus
\[
\boxed{
|\mathscr I_m(b)-\mathscr{End}_m(b)|
\le
\varepsilon_m^{\rm I}\|b\|^2,
\qquad
\varepsilon_m^{\rm I}
=
\frac{1000\mathfrak C_mL^3W_k}{m\sqrt Q}
=o(1/m).
}
\tag{27}
\]

This holds for **every complex band vector \(b\)**. Applying it to \(b=\mathsf S_mz\) gives exactly the two-column metric error in (1), without a condition number or replacement of \(z^*\widehat{\mathsf E}_mz\) by \(\|z\|^2\).

The asymptotic follows directly from
\[
Q\ge\frac{12\pi k^2m}{L},\qquad
\mathfrak C_m=O(L),\qquad
W_k=O((1+\log L)^3).
\]
For example,
\[
\varepsilon_m^{\rm I}
=
O\!\left(
\frac{L^{9/2}(1+\log L)^3}{k\,m^{3/2}}
\right).
\]

There is also an actual norm saving for the component itself:
\[
|\mathscr{End}_m(b)|
\le
\frac{2\mathfrak C_mL^2W_k}{\sqrt m}\|b\|^2
=o(1)\|b\|^2.
\tag{28}
\]

**But \(o(1)\) is not \(o(1/m)\).** The endpoint main term cannot be dropped at your new tolerance. It remains explicit in the test.

## 5. The first unpaid source correlation

Define the Hermitian two-column form
\[
\mathcal R_m(z)=
\mathscr L_m(\mathsf S_mz)
+\mathscr V_m(\mathsf S_mz)
+\mathscr{End}_m(\mathsf S_mz).
\]

The proved result is
\[
\boxed{
\left|
z^*\widehat{\mathsf P}_mz-\mathcal R_m(z)
\right|
\le
\varepsilon_m^{\rm I}\,
z^*\widehat{\mathsf E}_mz.
}
\tag{29}
\]

The still-unpaid arithmetic correlation, before adding the explicit endpoint form, is precisely
\[
\boxed{
\begin{aligned}
&\sum_{2\le q<Q}
\frac{\Lambda(q)}{\sqrt q}
\mathcal J_{\mathsf S_mz}(\log q)\\
&\quad+
\sum_{d>k}\frac{\nu(d)}{\sqrt d}
\sum_{\substack{r>k\\Q\le dr\le m}}
\frac{\beta_k(r)}{\sqrt r}
\mathcal J_{\mathsf S_mz}(\log d+\log r).
\end{aligned}
}
\tag{30}
\]

This retains the **source-weighted Hilbert contraction**, its diagonal, both complex slots and the exact product cutoff. It has not been bounded at the necessary logarithmic scale.

There are two specific reasons the preceding proof does not settle (30). In the lower arithmetic range, the logarithmic phase increments can leave the nonresonant interval used in (15). In the bilinear term, the long-divisor coefficients are not the smooth amplitudes used in (21); their Möbius signs cannot be treated as independent cancellation.

The fact that \(Q=o(m)\) does not make the lower range negligible. Its absolute bound still grows. Nor does \(\beta_k(r)\ge0\) assign a sign to the bilinear correlation.

## 6. The exact remaining inequality at your tolerance

By (29), it is sufficient to prove, on an unbounded original sequence,
\[
\boxed{
\mathcal R_m(z)
\le
\left(
\kappa_m+\frac1{128m}-\varepsilon_m^{\rm I}
\right)
z^*\widehat{\mathsf E}_mz
\quad\text{for every }z\in\mathbb C^2.
}
\tag{31}
\]

A convenient allowance is
\[
\boxed{
\mathcal R_m(z)
\le
\left(\kappa_m+\frac1{256m}\right)
z^*\widehat{\mathsf E}_mz,
}
\tag{32}
\]
because eventually \(\varepsilon_m^{\rm I}\le1/(256m)\).

Then
\[
\widehat d_m\ge-\frac1{128m}.
\]
The accepted \(\tau_m=o(1/m)\) and cutoff increment would give
\[
d_m^\sharp\ge\frac1{64m}
\]
on the sufficiently late part of that **same** sequence, refuting eventual \(M_m>0\) for this \(U_m\). The implication and cutoff constants are those in the checked continuation. 

**Neither (31) nor (32) is proved here.** No averaged matrix is used to claim a common cell.

The positive **image and pole terms** also remain available: replace \(\widehat{\mathsf P}_m\) by the matrix of \(\mathcal R_m\) in the existing complete \(\widehat{\mathsf Q}_m\). Its normalized least eigenvalue changes by at most \(\varepsilon_m^{\rm I}\). Thus the same arithmetic reduction can be inserted into the less wasteful complete-form budget without deleting either positive term.

## 7. What this attempt establishes

The new theorem is an **upper-arithmetic-range Type I cancellation estimate**: its full joint quadratic form is explicit boundary data plus a proved \(o(1/m)\) remainder. That is a polynomial saving in an actual arithmetic component, not another control of the already-paid Fourier tail.

It does **not** establish that the remaining bilinear correlation is small, that the boundary term has a favorable sign, or that the prescribed candidate fails cofinally.

The preregistered controls passed: 900 exact formal-prime-log checks of the divisor identity; exact complex telescoping tests including the reversed-sign plant; the complex diagonal-plus-Hilbert identity; and the terminal-atom cancellation. Four logarithmic-phase evaluations checked the local bound diagnostically. They are not source-sign certificates. The proof above has not yet received an independent audit.

**The outstanding source estimate is now (30), combined with the explicit endpoints (24), at the same-cell matrix threshold (31). I did not obtain that signed estimate. G1, G3 and RH remain open.**

:chatgpt-content-reference{index="5"}[Complete PAPER derivation: explicit constants, source mapping, remaining correlation, and executable controls](sandbox:/mnt/data/PROSHKA_G1_TYPE_I_ENDPOINT_CANCELLATION_2026-10-06.md)
