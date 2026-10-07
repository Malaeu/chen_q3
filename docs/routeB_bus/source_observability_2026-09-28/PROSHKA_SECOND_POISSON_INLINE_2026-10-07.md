# Proshka rollover Q4 — exact inline response

Chat: 6ac58a1c-1568-83ed-95d0-857526e2b6cb
Answer: c71b36a0-350c-46de-9800-71d34bb79108
Status: independently checked on PAPER; see SECOND_POISSON_AUDIT_2026-10-07.md; RH/SP/G1/G3 OPEN.

Ы — **the second transform is now carried through the complete first-transform expression, including its jump corrections and compensator. Its analytic tail is uniformly controlled. It does not produce a new signed Schur bound.**

The arithmetic outcome is sharper than an unsuccessful estimate: **after collecting every representation of a product ratio, an explicit cropped coefficient survives at an original carrier frequency.** Its only possible contributions are two \(g=1\) representations and their \(g=3\) Möbius correction. Their exact signed sum does not vanish.

This refutes **coefficientwise suppression after the second centering**, not cancellation in the complete integral or positivity of the actual Schur complement.

:chatgpt-content-reference{index="10"}[Complete PAPER verdict, proofs, exact controls, and return budget](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q04_2026-10-07.md)

## 1. Transform the entire first expression as one function of \(a\)

**[FINITE_CELL | PAPER]**

Keep
\[
K=m^2,\qquad V=V_0,\qquad s=\tfrac12+it,
\]
and the original intervals
\[
\begin{aligned}
J_a(y)&=(U,\infty)\cap[Y_0/a,y/a],\\
I_{a,d}(y)&=[1,\infty)\cap\{u:du\in J_a(y)\},\\
I^-_{a,d}&=I_{a,d}\cap[1,V],\qquad
I^+_{a,d}=I_{a,d}\cap(V,\infty).
\end{aligned}
\]

Write the accepted, ordinary-cutoff first approximation as
\[
\widehat E_{K,s}^j(I)
=\frac12\sum_{0<|k|\le K}(-1)^k
 \int_Iu^{-s}(\log u)^j e^{i\pi ku}\,du
+\mathcal C_t^j(I)
+[u^{-s}(\log u)^jQ_K(u)]_{\partial I}.
\]

The function to which I apply the centered-\(a\) transform is
\[
\boxed{
\begin{aligned}
G_{K,t,y}(a)=a^{-s}\bigg\{&
\frac12\sum_{\substack{d\le X\\d\ {\rm odd}}}
\mu(d)d^{-s}\int_{I_{a,d}}u^{-s}\log u\,du\\
&+\sum_{\substack{d\le X\\d\ {\rm odd}}}\mu(d)d^{-s}
\left[\widehat E_{K,s}^1(I^-_{a,d})
-\log d\,\widehat E_{K,s}^0(I^+_{a,d})\right]
-2\widehat E_{K,s}^0(J_a)
\bigg\}.
\end{aligned}}
\tag{1}
\]

The **first line is the entire \(a\)-flux inside \(\Theta_U\)**. The exact changes \(x=ab\), \(b=du\) give it, including both Jacobians. Consequently,
\[
\boxed{
\Phi_V(t;y)=
\int_{Y_0}^y x^{-it}D_U(x)\,dx
+\int G_{K,t,y}(a)\,d\rho_U(a)+e_u(t;y),
}
\tag{2}
\]
where the accepted Q3 tail satisfies
\[
|e_u(t;y)|\le\varepsilon_u(m)
\le\frac{8192h_UL}{\sqrt m}
\]
uniformly over the full band and all primitive cutoffs.

Thus **\(-2\), the first \(Q_K\) boundaries, their prescribed values, and the complete former \(\Gamma_V/\Theta_U\) contribution enter the second transform together**. The remaining direct density is precisely
\[
D_U(x)=
[A_U(\log x-\psi_1(x/U))-B_U-1]x^{-1/2}+x^{-3/2}.
\]
Neither the continuous \(A_U\,da\) part of \(d\rho_U\) nor the decaying pole has disappeared. :chatgpt-content-reference{index="0"} :chatgpt-content-reference{index="1"}

## 2. A uniform second resummation that retains every jump

**[ABSTRACT | PAPER]**

For the lattice of spacing \(h\), put
\[
\epsilon_h^{\rm mid}(a)=\frac12-\{a/h\}
\quad(a\notin h\mathbb Z),
\qquad
\epsilon_h^{\rm mid}(a)=0\quad(a\in h\mathbb Z),
\]
and define
\[
\begin{aligned}
Q_{h,H}(a)&=\epsilon_h^{\rm mid}(a)
-\sum_{\ell=1}^H\frac{\sin(2\pi\ell a/h)}{\pi\ell},\\
R_{h,H}(a)&=-\frac h2B_2(\{a/h\})
+\frac{h}{2\pi^2}
\sum_{\ell=1}^H\frac{\cos(2\pi\ell a/h)}{\ell^2},
\end{aligned}
\]
where \(B_2(v)=v^2-v+1/6\). The periodic cosine series gives
\[
R'_{h,H}=Q_{h,H}\quad\text{almost everywhere},
\qquad
\|R_{h,H}\|_\infty\le\frac{h}{2\pi^2H}.
\]
The series is valid at the endpoints for \(B_2\); sawtooth midpoint values and atom corrections are handled separately. :chatgpt-content-reference{index="2"}

Extend \(G\) by zero outside its original \(a\)-interval. For its smooth pieces \((b_i,b_{i+1})\), define
\[
\mathfrak b(G,Q)
=\sum_i\left[
G(b_{i+1}^-)Q(b_{i+1})
-G(b_i^+)Q(b_i)
\right],
\]
and
\[
\boxed{
\mathcal C_h[G]
=\sum_{\substack{c\in h\mathbb Z\\c\ {\rm a\ breakpoint}}}
\left(G(c)-\frac{G(c^-)+G(c^+)}2\right).
}
\tag{3}
\]
This includes excluded outer endpoints, internal jumps, and isolated prescribed values. **There is no \(1/h\) in (3).**

Set
\[
\mathcal P_{h,H}[G]
=\frac1h\sum_{0<|\ell|\le H}
\int G(a)e^{2\pi i\ell a/h}\,da
+\mathcal C_h[G]+\mathfrak b(G,Q_{h,H}).
\]
Then the exact finite identity is
\[
\boxed{
\begin{aligned}
\int G(a)\left(\sum_j\delta_{hj}(da)-\frac{da}{h}\right)
&=\mathcal P_{h,H}[G]+\mathcal R_{h,H}[G],\\
\mathcal R_{h,H}[G]
&=-\mathfrak b(G',R_{h,H})
+\sum_i\int_{b_i}^{b_{i+1}}G''(a)R_{h,H}(a)\,da.
\end{aligned}}
\tag{4}
\]
In particular,
\[
|\mathcal R_{h,H}[G]|
\le\frac{h}{2\pi^2H}
\left[
\sum_i\bigl(|G'(b_i^+)|+|G'(b_{i+1}^-)|\bigr)
+\sum_i\int_{b_i}^{b_{i+1}}|G''|
\right].
\tag{5}
\]

This follows by two finite integrations by parts, on the smooth pieces. It **does not require separated breakpoints, a nonzero phase derivative, or \(t\ne0\)**.

### Explicit growing-cell control

**[COFINAL_FAMILY | PAPER]**

Choose
\[
\boxed{H=m^{20}.}
\]

For the complete \(G_{K,t,y}\) in (1), uniformly in \(|t|\le\Omega\) and \(Y_0\le y\le m\),
\[
\#\{\text{smooth pieces}\}\le16m^2,
\]
\[
\max_{j=0,1,2}
\|G_{K,t,y}^{(j)}\|_{\infty,\mathrm{pieces}}
\le2^{18}m^{11}.
\]
Hence the bracket in (5) is at most \(2^{24}m^{13}\).

These deliberately conservative bounds are proved in the verdict. The relevant breakpoints are the endpoint switches and
\[
a=\frac{y}{dn},\qquad a=\frac{Y_0}{dn},
\]
where a first-transform endpoint crosses an odd integer. There are \(O(m^2)\) such nodes. Their coincidence does not create a denominator: the calculation uses actual values and one-sided derivatives, not inverse distances between nodes.

Since \(\sum_{h\le U}h\le m^2\) eventually,
\[
\boxed{
\sup_{t,y}
\left|\sum_{h\le U}\mu(h)\mathcal R_{h,H}[G_{K,t,y}]\right|
\le\varepsilon_a(m):=\frac{2^{24}}{m^5}.
}
\tag{6}
\]

Define
\[
\boxed{
\Xi_{K,H}(t;y)
=\int_{Y_0}^y x^{-it}D_U(x)\,dx
-\sum_{h\le U}\mu(h)\mathcal P_{h,H}[G_{K,t,y}].
}
\tag{7}
\]
The full uniform error is
\[
\boxed{
\sup_{|t|\le\Omega,\ y\le m}
|\Phi_V(t;y)-\Xi_{K,H}(t;y)|
\le\varepsilon_4(m)
:=\varepsilon_u(m)+\varepsilon_a(m).
}
\tag{8}
\]

The first tail was already paid through the original \(a\)-flux; it is not transformed again and amplified.

**No saddle approximation has been made.** All retained integrals are exact. Stationary transitions, corners, and hyperbolic-boundary encounters therefore have no additional approximation error. The large \(H\) is an analytic truncation choice, not a proposed numerical enumeration or an arithmetic saving.

## 3. The complete double interior and its product-ratio coefficient

**[FINITE_CELL | PAPER]**

Let
\[
\mathcal D_d(y)=
\{(a,u):U<a<A_0,\ u\ge1,\ du>U,\ Y_0\le adu\le y\},
\]
\[
w_d(u)=1_{u\le V}\log u-1_{u>V}\log d,
\qquad
W_d(u)=\mu(d)w_d(u)-2\,1_{d=1}.
\]

The double-nonzero interior in (7) is exactly
\[
\boxed{
\begin{aligned}
\mathcal I_{K,H}(t;y)
={}&-\frac12
\sum_{h\le U}\frac{\mu(h)}h
\sum_{\substack{d\le X\\d\ {\rm odd}}}d^{-s}
\sum_{0<|k|\le K}\sum_{0<|\ell|\le H}(-1)^k\\
&\quad\cdot
\iint_{\mathcal D_d(y)}
a^{-s}u^{-s}W_d(u)
e^{i\pi ku+2\pi i\ell a/h}\,da\,du.
\end{aligned}}
\tag{9}
\]

The **zero-first/nonzero-second** term, from the flux inside \(\Theta_U\), is
\[
\boxed{
\mathcal Z_{K,H}
=-\frac12
\sum_{h\le U}\frac{\mu(h)}h
\sum_{\substack{d\le X\\d\ {\rm odd}}}\mu(d)d^{-s}
\sum_{0<|\ell|\le H}
\iint_{\mathcal D_d(y)}
a^{-s}u^{-s}\log u\,e^{2\pi i\ell a/h}\,da\,du.
}
\tag{10}
\]

Write \(G_B\) for the part of (1) containing the first \(\mathcal C_t^j\) and \(Q_K\) boundary operations. The remaining **complete boundary term** is
\[
\boxed{
\begin{aligned}
\mathcal B_{K,H}
={}&-\sum_{h\le U}\frac{\mu(h)}h
\sum_{0<|\ell|\le H}
\int G_B(a)e^{2\pi i\ell a/h}\,da\\
&-\sum_{h\le U}\mu(h)
\left[\mathcal C_h[G_{K,t,y}]
+\mathfrak b(G_{K,t,y},Q_{h,H})\right].
\end{aligned}}
\tag{11}
\]
Thus
\[
\boxed{
\Xi_{K,H}
=\int_{Y_0}^y x^{-it}D_U(x)\,dx
+\mathcal Z_{K,H}+\mathcal I_{K,H}+\mathcal B_{K,H}.
}
\tag{12}
\]

### Collect equal ratios in the exact integrals

In each sign quadrant put
\[
z=\pi|k|u,\qquad w=\frac{2\pi|\ell|a}{h},
\qquad r=\frac{|k\ell|}{dh}=\frac nq,\quad(n,q)=1.
\]
Then
\[
x=adu=\frac{zw}{2\pi^2r}.
\]
Every representation of this ratio has
\[
dh=qg,\qquad |k\ell|=ng.
\]

For positive \(k,\ell\), let
\[
u=\frac z{\pi k},\qquad a=\frac{hw}{2\pi\ell},
\qquad
\chi_{h,d,k,\ell}(z,w)
=1_{\{U<a<A_0,\ u\ge1,\ du>U\}}.
\]
The full coefficient is
\[
\boxed{
\begin{aligned}
\mathcal G_{n,q}^{K,H}(z,w)
={}&
\sum_{1\le g\le m/q}\frac1{qg}
\sum_{\substack{h\mid qg,\ h\le U\\
d=qg/h\ {\rm odd},\ d\le X}}\mu(h)\\
&\quad\cdot
\sum_{\substack{k\mid ng,\ k\le K\\
\ell=ng/k\le H}}
(-1)^k\chi_{h,d,k,\ell}(z,w)
\left[\mu(d)w_d(z/(\pi k))-2\,1_{d=1}\right].
\end{aligned}}
\tag{13}
\]

Every crop and logarithm remains. The common product restriction is imposed outside this coefficient:
\[
\boxed{
\begin{aligned}
\mathcal I_{K,H}
={}&-\frac12
\sum_{\epsilon,\delta=\pm1}
\sum_{\substack{n,q\ge1\\(n,q)=1}}
(2\pi^2n/q)^{s-1}\\
&\cdot
\iint_{\substack{z,w>0\\
Y_0\le zw/(2\pi^2n/q)\le y}}
(zw)^{-s}e^{i\epsilon z+i\delta w}
\mathcal G_{n,q}^{K,H}(z,w)\,dz\,dw.
\end{aligned}}
\tag{14}
\]

The normalization follows from the exact Jacobian:
\[
\frac1h d^{-s}a^{-s}u^{-s}\,da\,du
=(2\pi^2r)^{s-1}\frac{(zw)^{-s}}{dh}\,dz\,dw.
\]

This is **collection of complete integrals**, not merely collection of their saddle-leading terms. For \(t>0\), the simultaneous stationary point in the \(++\) quadrant is \(z=w=t\); the other quadrants remain in (14).

### What the uncropped identities actually cancel

**[ABSTRACT | PAPER]**

The full \(h\)-divisor convolution is
\[
C_o(c)=\sum_{\substack{h\mid c\\c/h\ {\rm odd}}}
\mu(h)\mu(c/h).
\]
For odd \(c\), this is **\(\mu*\mu\), not \(\mu*1\)**. At an odd prime its local coefficients are \(1,-2,1,0,\ldots\).

For \(N=2^eN_o\), \(N_o\) odd, and \(D_o=\#\{d:d\mid N_o\}\),
\[
\boxed{
\begin{aligned}
\sum_{k\mid N}(-1)^k&=(e-1)D_o,\\
\sum_{k\mid N}(-1)^k\log k
&=\frac{e-1}{2}D_o\log N_o
+\frac{e(e+1)}2D_o\log2.
\end{aligned}}
\tag{15}
\]

Thus \(2\Vert N\) cancels the constant-logarithm coefficient, **but leaves \(D_o\log2\) in the logarithmic moment**. The verdict gives both the all-short and all-long formulas. They are used only when every indicated divisor is included; they do not replace the cropped coefficient (13).

## 4. A complete cropped coefficient survives

**[COFINAL_FAMILY | PAPER]**

Choose odd primes
\[
\frac U2<h_0<U,\qquad
\frac X{16}<p<\frac X8,\qquad
\frac X5<\ell_0<\frac{2X}5,\qquad
2\ell_0<k_0<4\ell_0.
\tag{16}
\]
The accepted elementary dyadic-prime existence supplies these on every sufficiently late original cell.

Set
\[
q=h_0p,\qquad n=k_0\ell_0.
\]
These primes are distinct eventually, so \((n,q)=1\).

Let \(t_0=(22\pi/5)\ell_0\), and choose the nearest **original carrier frequency**
\[
\tau=\omega_j.
\]
Since \(t_0<\frac{22}{25}\Omega\), it remains inside the original carrier. Put
\[
b=\frac{\tau}{\pi\ell_0}.
\]
Eventually
\[
\frac{439}{100}\le b\le\frac{441}{100}.
\]

At \(z=w=\tau\), the primary representation has
\[
u_0=b\ell_0/k_0,\qquad
a_0=(b/2)h_0,\qquad
x_*=\frac{b^2\ell_0}{2k_0}q.
\]
It satisfies
\[
\frac{439}{400}<u_0<\frac{441}{200},
\qquad
U<a_0<3U<A_0,
\qquad
Y_0<x_*<m,
\qquad
x_*/q<5.
\tag{17}
\]
Take \(y=m\), so the saddle is strictly inside the physical product range.

### Enumerate all representations, not one tuple

Every active representation has
\[
dh<x_*,
\]
because \(a/h>U/h\ge1\) and \(u\ge1\). Thus only \(g=1,2,3,4\) can occur.

If an allowed \(h\mid qg\) does not contain \(h_0\), then \(h\mid g\), giving
\[
d=qg/h\ge q>X,
\]
which is forbidden. If it contains \(h_0\), the condition \(h_0>U/2\) forces
\[
h=h_0,\qquad d=pg.
\]
Oddness of \(d\) removes \(g=2,4\).

For \(g=1\), the primary pair \(k=k_0,\ell=\ell_0\) is always allowed. The swapped pair is allowed exactly when
\[
\chi
=1_{\{(b\ell_0/(2k_0))h_0>U\}}
=1.
\tag{18}
\]
The other divisors of \(n\) give either \(a<U\) or \(u<1\).

For \(g=3\), the **only** possible survivor is
\[
k=3\ell_0,\qquad \ell=k_0,\qquad d=3p,
\]
with \(u=b/3\) and the same swapped \(a\). It is allowed exactly when \(\chi=1\). Here \(3p<X\), so the d-cutoff does not remove it.

Every surviving \(u\) is less than five, hence short. The long sectors have no other admissible representation. The baseline is absent because \(d=p\) or \(3p\), not one.

Using the actual signs gives
\[
\boxed{
\begin{aligned}
\mathcal G_{n,q}^{K,H}(\tau,\tau)
&=-\frac1q
\left[
\log u_0+\chi\left(\log b-\frac13\log(b/3)\right)
\right]\\
&=-\frac1q
\left[
\log u_0+\chi\left(\frac23\log b+\frac13\log3\right)
\right].
\end{aligned}}
\tag{19}
\]

The \(g=3\) contribution has been combined **signed** with the swapped \(g=1\) term. It is not separately majorized.

Therefore
\[
\boxed{
q\left|\mathcal G_{n,q}^{K,H}(\tau,\tau)\right|
\ge\log(439/400)>0.
}
\tag{20}
\]

For a proposed uniform coefficient bound \(\delta_m\to0\), its slack has the negative upper envelope
\[
\boxed{
\delta_m-q|\mathcal G_{n,q}^{K,H}(\tau,\tau)|
\le\delta_m-\log(439/400)<0
}
\tag{21}
\]
eventually.

**This kills only the possible completion “the second centering makes every normalized double-interior product coefficient \(o(1)\).”**

For **Fejér cutoffs**, each term of (19) must carry its own \(w_K(k)w_H(\ell)\). The normalized change is at most
\[
10\Omega\bigl((K+1)^{-1}+(H+1)^{-1}\bigr)=o(1),
\]
so a fixed half of (20) survives eventually. The ordinary-cutoff formula above is exact without those weights.

The zero-first-alias term, boundary operations, other ratios, and physical integration can still cancel the contribution of (19). **There is no complete-integral lower bound here, and this coefficient is not an exceptional Schur vector.**

## 5. The entire return budget

**[FINITE_CELL | PAPER]**

Synthesize the same coupled data:
\[
h_j^{(4)}=\Im\Xi_{K,H}(\omega_j;m),\qquad
d_j^{(4)}=\frac2L\Re\int_0^L\Xi_{K,H}(\omega_j;e^v)\,dv,
\]
\[
C^{(4)}
=\operatorname{diag}(d_j^{(4)})
+\frac1\pi[\operatorname{diag}(h_j^{(4)}),H^{\rm d}].
\]
The dimension-free synthesis gives
\[
\boxed{
C[\tau_V]=C^{(4)}+E^{(4)},\qquad
\|E^{(4)}\|\le4\varepsilon_4(m).
}
\tag{22}
\]
This includes every cross mode. It does not require pretending that the approximation is the primitive of a frequency-independent measure. :chatgpt-content-reference{index="3"}

Keep \(C_Q\) **signed**. Then
\[
H_m(r)=rI-(C^{(4)}+C_Q)+F_{10}-E^{(4)}.
\]
For the actual \(f=J_rv=v+y\),
\[
\boxed{
P_{\mathcal R}(C^{(4)}+C_Q)f
=ry+P_{\mathcal R}(F_{10}-E^{(4)})f.
}
\tag{23}
\]

Define
\[
s_4(v)=r\|v\|^2-
\Re\langle v,(C^{(4)}+C_Q)J_rv\rangle.
\]
The full discriminator is
\[
\boxed{
\begin{aligned}
s_4(v)-(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|
&\le\langle v,\mathfrak S_m(r)v\rangle\\
&\le s_4(v)+(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|.
\end{aligned}}
\tag{24}
\]
The original regular space and complete \(B_r^*A_r^{-1}B_r\) correction remain. No bound on \(\|J_r\|\) is assumed. :chatgpt-content-reference{index="4"}

**[COFINAL_FAMILY | PAPER]** The inherited allocation is still
\[
\begin{aligned}
\Delta_{10}={}&L+8
+8\sqrt{Y_0}(1+\log Y_0)
+\frac{1600M_{U,L}(1+\sqrt\Omega)}{\sqrt{Y_0}}
+4\mathcal M_m+4M_{\rm wheel}+\Pi_m,\\
M_{U,L}={}&3UL+U^2\log(2U),\\
\mathcal M_m={}&512Lm^{1/4}
(U^{2/3}h_U^{1/2}\Omega^{1/6}+U)
+896LU^{1/2}h_U^{3/4}m^{3/8},\\
M_{\rm wheel}={}&8192Lh_U\sqrt{A_0}(\Omega^{1/6}+1)
+57344h_Um^{1/4}A_0^{1/4},\\
\Pi_m={}&24h_U\sqrt{A_0/U}.
\end{aligned}
\tag{25}
\]
All original component assignments and all prime powers remain. :chatgpt-content-reference{index="5"} :chatgpt-content-reference{index="6"} :chatgpt-content-reference{index="7"}

Thus
\[
4\varepsilon_4=O(h_ULm^{-1/2}),
\qquad
\Delta_{10}=O(m^{5/12}L^{3/2}\log(2L)).
\]
Keeping \(C_Q\) signed removes the introduced \(E_V\) allocation; **it does not remove the inherited \(5/12\) allocation**.

The full archimedean return remains
\[
\boxed{
\begin{aligned}
W(f)\ge{}&
D_{\rm arch}(f)
-(c_A+\delta_{10}+4\varepsilon_4)\|f\|^2
+2\langle f,(R+R^*)f\rangle\\
&-\langle f,(C^{(4)}+C_Q)f\rangle,
\qquad
\delta_{10}=\Delta_{10}-(L+8).
\end{aligned}}
\tag{26}
\]
Its final signed term is unestimated. No derivative absorption has been reinstated. :chatgpt-content-reference{index="8"}

## 6. Stopping reason and the next bounded test

The precise survivor is **the cropped function \(\mathcal G_{n,q}^{K,H}(z,w)\)** in (13), integrated through (14), together with (10), (11), and \(D_U\). Equal ratios have a common oscillatory kernel, but not a constant amplitude that can be removed from the integral.

The second centering supplies neither \(\mu*1\) cancellation nor uniform smallness at the simultaneous saddles. Equation (19) evaluates that failure on the actual arithmetic after complete collection. **Stop that completion.** Cancellation across the remaining integrations is still open.

The finite controls support the algebra: direct enumeration matched **1,139** grouped rational/logarithmic coefficients. A planted deletion of the interior \(1/h\) changed **802** of them. Another **375** exact checks covered the uncropped identities. For a jump control with \(h=2\), \(G=1\) below \(6\), \(G=2\) above \(6\), and prescribed \(G(6)=5\), the missing correction is exactly \(7/2\); incorrectly multiplying it by \(1/h\) loses \(7/4\). These controls do not replace the cofinal proofs.

The next selected representation is the **exact hyperbolic aspect integral**. Set
\[
z=\sqrt{2\pi^2rx}\,e^v,\qquad
w=\sqrt{2\pi^2rx}\,e^{-v}.
\]
The Jacobian cancels the ratio normalization in (14):
\[
\boxed{
\begin{aligned}
\mathcal I_{K,H}
=-\frac12\sum_{\epsilon,\delta}\sum_r
\int_{Y_0}^y x^{-s}\int_{\mathbb R}
&\mathcal G_r^{K,H}
\bigl(\sqrt{2\pi^2rx}e^v,\sqrt{2\pi^2rx}e^{-v}\bigr)\\
&\cdot e^{i\sqrt{2\pi^2rx}(\epsilon e^v+\delta e^{-v})}
\,dv\,dx.
\end{aligned}}
\tag{27}
\]
The \(++\) phase is \(2\pi\sqrt{2rx}\cosh v\). Every finite aspect cutoff remains inside \(\mathcal G\); replacing this with a full Bessel integral would be another unjustified boundary deletion.

The bounded test is to evaluate that **finite aspect integral with its logarithmic endpoints**, then combine its boundary primitives with the zero-alias and edge operations before estimating. A different surviving option is correlation between distinct product ratios in the coupled \(d/h\) matrix, but that needs a genuine arithmetic correlation input. The conditional MSTT lead supplies no such input automatically.

**Outcome:** the second analytic tail is paid, the complete product-ratio coefficient is computed, and its coefficientwise-smallness completion is refuted in a narrow cofinal scope. **The signed Schur estimate has not improved. SP/G1/G3/RH and the actual Schur sign remain OPEN.**
