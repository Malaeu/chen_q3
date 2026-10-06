# Growth answer9 — exact inline capture

Chat `6ac54396-d878-83eb-ae29-35d2bdd2262b`; question `4ee66e97-0dfd-43ff-afd1-323b686284c3`.
Answer `9268fe73-068a-4b61-98c4-e25f0f2a0ce5`; untruncated read_thread capture 2026-10-06 23:16 UTC. Pending audit.

---

Ы — **additive differencing does pay a genuine part of the signed Type-II interaction at a fixed exponent below \(1/2\).**

**[COFINAL_FAMILY | PAPER]** The entire **centered long-\(\alpha_U\) component**, defined below with its continuous mean retained, satisfies
\[
\boxed{
\|C_{\mathrm{long}}\|
\le 40000\,m^{5/12}L^{3/2}\log(2L)
}
\]
on **every sufficiently late original cell**, simultaneously for all complex carrier vectors.

This is not merely a high-frequency result: its low-frequency primitive has the stronger bound \(128UL\). The transfer includes every off-diagonal carrier interaction and applies directly to the actual \(J_rv\).

**It is not a \(5/12\) negative-bottom floor.** The remaining **short-\(\alpha_U\), long-prime-variable flux and its exact compensator** are still unestimated in sign. The original Schur correction remains intact.

:chatgpt-content-reference{index="2"}[Complete PAPER verdict and machine-readable ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q09.md)

## 1. Center the divisor flux without losing the compensator

**[FINITE_CELL | PAPER]**

Keep
\[
U=\lceil L\rceil,\qquad A_0=Y_0=\lceil\sqrt m\rceil,
\qquad \Omega=\frac{2\pi m}{L},
\qquad
\mathfrak h=\sum_{d\le U}\frac1d.
\]
Here \(A_0\) cuts the **factor \(a\)**, not the carrier or its frequency range.

Retain the accepted source coefficients
\[
\alpha_U(n)=-\sum_{\substack{d\le U\\d\mid n}}\mu_{\mathrm M}(d)
\quad(n>U),
\]
\[
A_U=\sum_{d\le U}\frac{\mu_{\mathrm M}(d)}d,\qquad
B_U=\sum_{d\le U}\frac{\mu_{\mathrm M}(d)\log d}d.
\]
The right-continuous primitive
\[
\rho_U(u)=
\sum_{d\le U}\mu_{\mathrm M}(d)
\left(\{u/d\}-\{U/d\}\right)
\]
has the exact **signed Stieltjes measure**
\[
\boxed{
d\rho_U(a)
=\sum_{n>U}\alpha_U(n)\delta_n(da)+A_U\,da,
\qquad a>U.
}
\tag{1}
\]
Thus the continuous term has a **plus sign**. It centers the divisor flux; it is not assumed small.

Define the long-factor measure by its action on a test function \(G\):
\[
\boxed{
\int G(x)\,d\sigma_{\mathrm{long}}(x)
=
\sum_{b>U}\frac{\Lambda(b)}{\sqrt b}
\int_{\substack{a\ge A_0\\ab\le m}}
a^{-1/2}G(ab)\,d\rho_U(a).
}
\tag{2}
\]
All prime powers in \(b\) remain. Its continuous density is
\[
A_Ux^{-1/2}
\sum_{U<b\le x/A_0}\frac{\Lambda(b)}b.
\]

Write the accepted density (22) as
\[
D_U(x)=
\left[A_U\bigl(\log x-\psi_1(x/U)\bigr)-B_U-1\right]x^{-1/2}
+x^{-3/2},
\quad
\psi_1(z)=\sum_{n\le z}\frac{\Lambda(n)}n.
\tag{3}
\]
Its domain remains \(x\ge Y_0\ge4U^2\).

The complementary measure is exactly
\[
\boxed{
\begin{aligned}
\int G\,d\sigma_{\mathrm{rem}}
={}&
\sum_{b>U}\frac{\Lambda(b)}{\sqrt b}
\int_{\substack{U<a<A_0\\Y_0\le ab\le m}}
a^{-1/2}G(ab)\,d\rho_U(a)\\
&+\int_{Y_0}^mD_U(x)G(x)\,dx.
\end{aligned}
}
\tag{4}
\]
Then
\[
d\sigma_{\mathrm{II}}
=d\sigma_{\mathrm{long}}+d\sigma_{\mathrm{rem}}.
\]

To check the compensator, the full centered flux contributes
\[
A_Ux^{-1/2}\bigl(\psi_1(x/U)-C_U\bigr),
\qquad C_U=\sum_{b\le U}\frac{\Lambda(b)}b.
\]
Adding (3) gives precisely
\[
-(1-\kappa_U(x))x^{-1/2}+x^{-3/2}.
\]
**The original flux and compensator have been repartitioned exactly, not separately bounded.**

For any such measure, \(C[\sigma]\) continues to mean
\[
P_m\int(S_{\log x}+S_{\log x}^{*})\,d\sigma(x)\,P_m.
\]
In particular, \(C_{\mathrm{long}}\) is an operator on the unchanged original carrier.

## 2. Estimate the actual CRT progression sums first

**[FINITE_CELL | PAPER]**

Let \(A\ge A_0\) be an integer, let \(I\subset[A,2A)\) be any interval arising from a product cutoff, and set
\[
S_I(t)=\sum_{n\in I}\alpha_U(n)n^{-it},\qquad \tau=|t|>0.
\]
The additive correlation is
\[
R_k(t)=
\sum_{n,n+k\in I}
\alpha_U(n+k)\alpha_U(n)
e^{-it\log((n+k)/n)}.
\]

Your CRT expansion gives this **exactly** as a sum over the compatible classes
\[
n\equiv r_{d,e,k}\pmod{q},\qquad
q=[d,e],\qquad (d,e)\mid k.
\]
I do not replace those progression sums by a main term plus a variation error.

After conjugation when needed, use
\[
\theta(a)=\tau\log\frac{a+k}{a},
\qquad
\theta''(a)=2\tau\int_a^{a+k}u^{-3}\,du.
\]
Both arguments lie in \([A,2A]\), hence
\[
\frac{\tau k}{4A^3}
\le\theta''(a)\le
\frac{2\tau k}{A^3}.
\]

On \(a=r+qu\), the phase \(\theta/(2\pi)\) therefore satisfies
\[
\lambda=\frac{q^2\tau k}{8\pi A^3},
\qquad
\Lambda=\frac{q^2\tau k}{\pi A^3},
\qquad
\text{interval length}\le A/q.
\]
These are exactly the hypotheses of Arias de Reyna’s Lemma 5 for a real \(C^2\) phase with positive second derivative. Its constant is \(2.79368380731\ldots<3\). Progressions of length below one are counted directly. :chatgpt-content-reference{index="0"}

Including endpoint changes, this gives
\[
\boxed{
\left|
\sum_{n\equiv r\ (q)}
e^{-it\log((n+k)/n)}
\right|
\le
2+5\sqrt{\frac{\tau k}{A}}
+31\frac{A^{3/2}}{q\sqrt{\tau k}}.
}
\tag{5}
\]

The modulus sum is paid by
\[
\sum_{d,e\le U}\frac1{[d,e]}
\le
\sum_{g\le U}\frac1g
\left(\sum_{a\le U/g}\frac1a\right)^2
\le\mathfrak h^3.
\]
Consequently,
\[
\boxed{
|R_k(t)|
\le
2U^2+5U^2\sqrt{\frac{\tau k}{A}}
+31\mathfrak h^3\frac{A^{3/2}}{\sqrt{\tau k}}.
}
\tag{6}
\]
At zero shift, CRT counting separately gives
\[
\boxed{R_0\le A\mathfrak h^3+U^2.}
\tag{7}
\]

No sign or smallness of the user’s \(R_U(k)\) is asserted. Its compatible progression sums have instead been estimated with their oscillation intact.

## 3. Optimize the shift range with every error included

**[FINITE_CELL | PAPER]**

Extend the sequence by zero outside \(I\). The finite-shift Cauchy identity gives, for \(1\le K\le A\),
\[
|S_I(t)|^2
\le
\frac{A+K-1}{K}
\left[
R_0+
2\sum_{k=1}^{K-1}(1-k/K)\Re R_k(t)
\right].
\]
This identity applies to the actual coefficients \(\alpha_U\); no unit-coefficient theorem is being misapplied.

Using (6)–(7) yields the complete envelope
\[
\boxed{
|S_I(t)|^2
\le
\frac{2A^2\mathfrak h^3}{K}
+10AU^2
+20U^2\sqrt{A\tau K}
+248\mathfrak h^3\frac{A^{5/2}}{\sqrt{\tau K}}.
}
\tag{8}
\]
The \(10AU^2\) term includes the CRT endpoint errors.

For \(\tau>A/U\), choose
\[
K_1=\frac{A\mathfrak h^2}{U^{4/3}\tau^{1/3}},
\qquad
K_2=\frac{A^2\mathfrak h^3}{U^2\tau},
\qquad
\boxed{K=\lfloor\max(K_1,K_2)\rfloor.}
\tag{9}
\]

This is a two-term optimization, not just a choice favoring one error. \(K_1\) balances the \(K^{-1}\) term against the growing \(K^{1/2}\) term; \(K_2\) balances the \(K^{-1/2}\) term against it.

Uniformly for
\[
A\ge A_0,\qquad A/U<\tau\le\Omega,
\]
eventually \(2\le K\le A/2\). Explicit sufficient conditions are
\[
\frac{\mathfrak h^3}{U}\le\frac14,\qquad
\frac{\mathfrak h^2}{UA_0^{1/3}}\le\frac14,\qquad
\frac{A_0\mathfrak h^2}{U^{4/3}\Omega^{1/3}}\ge4.
\]
All hold on every sufficiently late original cell.

Thus \(K\ge K_i/2\) and \(K\le K_1+K_2\). Substitution into (8) gives
\[
|S_I(t)|^2
\le
24AU^{4/3}\mathfrak h\,\tau^{1/3}
+372U\mathfrak h^{3/2}A^{3/2}
+10AU^2,
\]
and therefore
\[
\boxed{
|S_I(t)|
\le20\left[
U^{2/3}\mathfrak h^{1/2}\sqrt A\,\tau^{1/6}
+U^{1/2}\mathfrak h^{3/4}A^{3/4}
+U\sqrt A
\right].
}
\tag{10}
\]

All clipped product intervals are covered. A short clipped interval does not invalidate the argument: the sequence is zero-extended within the fixed box \([A,2A)\).

## 4. Restore the continuous mean—and cover zero frequency

**[COFINAL_FAMILY | PAPER]**

Partial summation against \(a^{-1/2}\), using the uniform subinterval estimate (10), costs at most \(2/\sqrt A\).

The continuous contribution in (1) obeys
\[
\left|A_U\int_Ia^{-1/2-it}\,da\right|
\le\frac{3\mathfrak h\sqrt A}{\tau}.
\]
When \(\tau>A/U\), this is at most \(3U\) eventually. Hence
\[
\left|\int_Ia^{-1/2-it}\,d\rho_U(a)\right|
\le64\left[
U^{2/3}\mathfrak h^{1/2}\tau^{1/6}
+U^{1/2}\mathfrak h^{3/4}A^{1/4}
+U
\right].
\tag{11}
\]

For \(\tau\le A/U\), **including \(t=0\)**, I use no curvature assertion. Expand \(\alpha_U\) exactly. For each \(d\le U\), the integer variable \(a/d\) has scale \(A/d\), and
\[
|t|\le A/U\le A/d.
\]
The accepted low-frequency sum-minus-integral estimate from Answer8, followed by partial summation, gives
\[
\boxed{
\left|\int_Ia^{-1/2-it}\,d\rho_U(a)\right|
\le\frac{32U}{\sqrt A},
\qquad |t|\le A/U.
}
\tag{12}
\]

The subtracted integral is precisely the \(A_U\) term in (1). No Möbius mean estimate is inserted.

Combining the two cases proves, for **every** \(|t|\le\Omega\),
\[
\boxed{
\left|\int_Ia^{-1/2-it}\,d\rho_U(a)\right|
\le64\left[
U^{2/3}\mathfrak h^{1/2}\Omega^{1/6}
+U^{1/2}\mathfrak h^{3/4}A^{1/4}
+U
\right].
}
\tag{13}
\]

Thus the result does not leave a low-frequency part of the long-\(\alpha_U\) operator uncontrolled.

## 5. Sum the prime-weighted flux and reconstruct the whole carrier matrix

**[COFINAL_FAMILY | PAPER]**

Define the signed cumulative transform
\[
\Phi_{\mathrm{long}}(t;y)
=
\int_{[Y_0,y]}x^{-it}\,d\sigma_{\mathrm{long}}(x).
\]
Split \(a\ge A_0\) into \([A,2A)\), \(A=2^jA_0\). For fixed \(b\), the product condition clips the upper endpoint at \(y/b\), already covered by (13).

Retain all prime powers and use only
\[
\sum_{U<b\le m/A}\frac{\Lambda(b)}{\sqrt b}
\le2L\sqrt{m/A}.
\]
The geometric sums satisfy
\[
\sum_AA^{-1/2}\le4m^{-1/4},
\qquad
\sum_AA^{-1/4}\le7m^{-1/8}.
\]
It follows that
\[
\boxed{
\begin{aligned}
\sup_{\substack{|t|\le\Omega\\y\le m}}
|\Phi_{\mathrm{long}}(t;y)|
\le\mathcal M_m:={}&
512Lm^{1/4}
\left(U^{2/3}\mathfrak h^{1/2}\Omega^{1/6}+U\right)\\
&+896LU^{1/2}\mathfrak h^{3/4}m^{3/8}.
\end{aligned}
}
\tag{14}
\]
In particular,
\[
\mathcal M_m
\le10000m^{5/12}L^{3/2}\log(2L)
\]
eventually.

For \(|t|\le A_0/U\), using (12) throughout gives the sharper
\[
\boxed{
\sup_{y\le m}|\Phi_{\mathrm{long}}(t;y)|
\le128UL.
}
\tag{15}
\]

### All cross-frequency terms are paid

Use the actual finite-window synthesis:
\[
h_j^{\mathrm{long}}
=\Im\Phi_{\mathrm{long}}(\omega_j;m),
\]
\[
d_j^{\mathrm{long}}
=\frac2L\Re\int_0^L
\Phi_{\mathrm{long}}(\omega_j;e^u)\,du.
\]
Then
\[
C_{\mathrm{long}}
=
\operatorname{diag}(d^{\mathrm{long}})
+\frac1\pi
[\operatorname{diag}(h^{\mathrm{long}}),H_{\mathrm{discrete}}].
\]
Since \(\|H_{\mathrm{discrete}}\|\le\pi\),
\[
\boxed{
\|C_{\mathrm{long}}\|
\le4\mathcal M_m.
}
\tag{16}
\]

This is the **complete coherent matrix**, not its diagonal or a selected frequency block. Adjacent-frequency, opposite-frequency and low/high cross terms all occur in the exact divided difference. There is no hidden \(2m+1\) factor.

The proof avoids a problematic mixed-phase step: it does not difference a general Fourier superposition and assume positive curvature for all its cross terms. Instead, it proves the signed primitive estimate uniformly and then reconstructs the full original matrix by the accepted exact bounded map.

The product atom \(ab=m\) is counted in the sum estimates. Its compressed action is zero because \(S_L=0\). Dyadic endpoints are half-open; included lower endpoints use \(\rho_U(\ell^-)\), excluded ones use \(\rho_U(\ell)\), and upper cumulative values are right-continuous. No trace term is discarded.

## 6. Spend the bound through the actual regular equation

**[FINITE_CELL | PAPER]**

Retain the accepted all-range identity
\[
\mathsf H_m(r)=rI-C_{\mathrm{II}}+F_8,
\qquad
\|F_8\|\le\Delta_8.
\]
The raw small-product range, Type-I terms and archimedean diagonal already paid in \(\Delta_8\) are unchanged.

Because
\[
C_{\mathrm{II}}=C_{\mathrm{long}}+C_{\mathrm{rem}},
\]
set
\[
F_9=F_8-C_{\mathrm{long}},
\qquad
\Delta_9=\Delta_8+4\mathcal M_m.
\]
Then
\[
\boxed{
\mathsf H_m(r)=rI-C_{\mathrm{rem}}+F_9,
\qquad
\|F_9\|\le\Delta_9.
}
\tag{17}
\]

Now keep the **actual** repaired regular space and its blocks:
\[
\mathcal R=\ker B,\qquad \mathcal E=\mathcal R^\perp,
\]
\[
f=J_rv=v+y,\qquad
y=-A_r^{-1}B_rv,\qquad r>\epsilon_m.
\]
Nothing has been recomputed for the split measure.

The regular equation gives
\[
\boxed{
\left\|
P_{\mathcal R}C_{\mathrm{rem}}J_rv-r y
\right\|
\le\Delta_9\|J_rv\|.
}
\tag{18}
\]

Moreover,
\[
\langle y,\mathsf H_m(r)f\rangle=0,\qquad v\perp y.
\]
Therefore
\[
\boxed{
\begin{aligned}
&r\|v\|^2-\Re\langle v,C_{\mathrm{rem}}J_rv\rangle
-\Delta_9\|v\|\,\|J_rv\|\\
&\quad\le
\langle v,\mathfrak S_m(r)v\rangle\\
&\quad\le
r\|v\|^2-\Re\langle v,C_{\mathrm{rem}}J_rv\rangle
+\Delta_9\|v\|\,\|J_rv\|.
\end{aligned}
}
\tag{19}
\]

The full \(B_r^*A_r^{-1}B_r\) correction remains through \(J_r\). **No bound for \(\|J_r\|\), and no replacement of \(\|J_rv\|\) by \(\|v\|\), is asserted.**

For the original Weil form, retaining its positive terms gives
\[
\boxed{
\begin{aligned}
W(f)\ge{}&
D_{\mathrm{arch}}(f)
-\bigl(c_A+\delta_8+4\mathcal M_m\bigr)\|f\|^2
+2\langle f,(R+R^*)f\rangle\\
&-\langle f,C_{\mathrm{rem}}f\rangle,
\end{aligned}
}
\tag{20}
\]
where \(\delta_8\) is the previously paid raw-small-range and Type-I error.

This is a new one-sided source estimate with a controlled component. **The unestimated final term prevents it from being a new whole-matrix floor.**

## 7. The exact remaining arithmetic correlation

**[FINITE_CELL | PAPER]**

For the two actual carrier vectors, retain
\[
\mathcal K_{v,f}(h)
=
\int_0^h
\left[
\overline{v(L-u)}f(h-u)
+\overline{v(h-u)}f(L-u)
\right]du.
\]
The scalar still needed in (19) is exactly
\[
\boxed{
\begin{aligned}
\mathcal R_{U,m}(v,J_rv)
={}&
\sum_{b>U}\frac{\Lambda(b)}{\sqrt b}
\int_{\substack{U<a<A_0\\Y_0\le ab\le m}}
a^{-1/2}
\mathcal K_{v,J_rv}(L-\log(ab))\,d\rho_U(a)\\
&+\int_{Y_0}^m
D_U(x)\mathcal K_{v,J_rv}(L-\log x)\,dx.
\end{aligned}
}
\tag{21}
\]

The second integral is the **same compensator (22) from Answer8**. Expanding the first Stieltjes integral restores the prime-weighted flux and all lower trace terms. At \(ab=m\), \(\mathcal K(0)=0\).

The two endpoint profiles still come from \(v,J_rv\). They have not become independent variables. The signed measure is still the full Type-II measure minus a component now proved small.

### Why this optimized additive estimate does not finish the short-factor part

For a short box \(A\asymp U\) at top frequencies \(\tau\asymp m/L\), both \(K_1\) and \(K_2\) in (9) tend to zero. The admissible choice \(K=1\) has no nonzero shifted correlation and reduces to the unsaved Cauchy estimate. For \(K\ge2\), the second-derivative envelope (5) is larger than the progression length in this regime.

**Positive curvature is present; the resulting estimate is outside its useful scale.** This is a limitation of the proved envelope, not a lower bound for the actual sum and not a theorem-shape kill.

The residual has nevertheless become more specific. On the original strip
\[
x\in[X,2X),\qquad X=\lfloor m/L^8\rfloor,
\]
the remaining terms satisfy
\[
U<a<A_0,\qquad
b=x/a>X/A_0\gg\frac{\sqrt m}{L^8}.
\]
Thus the long factor there is now specifically the **prime-power variable \(b\)**. The CRT lemma for \(\alpha_U(a)\alpha_U(a+k)\) does not estimate the shifted \(\Lambda(b)\Lambda(b+k)\) correlations produced by differencing that variable.

## Closeout

The additive-shift test succeeds on a genuine portion of the formerly unestimated Type-II operator: **all centered terms with \(a\ge\sqrt m\), including low frequencies, are paid at exponent \(5/12\)**. The progression endpoints, product cutoffs, prime powers, continuous mean and full-carrier synthesis have explicit budgets.

The remaining scalar is (21), subject to the actual regular constraint (18). Its Schur discriminator is
\[
M_r(v)-\Delta_9\|v\|\,\|J_rv\|
\le
\langle v,\mathfrak S_m(r)v\rangle
\le
M_r(v)+\Delta_9\|v\|\,\|J_rv\|,
\]
where
\[
M_r(v)=r\|v\|^2-\Re\mathcal R_{U,m}(v,J_rv).
\]
A negative upper endpoint certifies a violation on that cell; a nonnegative lower envelope for every exceptional vector certifies the cell. A straddling interval does neither.

**SP, the actual exceptional Schur sign, G1/G3 and RH remain open. No common-cell subsequence or improved whole-matrix bottom exponent is supplied.**

**Next mathematical step:** difference the remaining long prime-power variable in (21) on the original endpoint strip, keeping the resulting \(\Lambda(b)\Lambda(b+k)\) term and both mixed continuous terms together. The proved restriction \(b\gg\sqrt m/L^8\) now justifies that switch; its signed estimate must be tested on the actual \(J_rv\) against (19), not on independent endpoint profiles.
