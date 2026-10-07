# Proshka rollover Q5 — inline response

Chat: 6ac58a1c-1568-83ed-95d0-857526e2b6cb
Answer: 6bc1860c-1bdb-4edc-8d44-b9f16828a6fc
Status: received; independent audit pending; RH/SP/G1/G3 OPEN.

Ы — **the complete continuous boundary return now has a uniform \(1/(1+|t|)\) bound. The signed atomic part remains, and the full Schur test is still inconclusive.**

The finite aspect calculation cancels the artificial \(u=V\) interface **when the actual \(C_Q\) and the exact resummation remainders are included**. It does not cancel the physical product faces. The attempted further radial integration encounters stationary points inside the original domain, so it supplies no automatic additional signed gain.

:chatgpt-content-reference{index="11"}[Complete PAPER verdict, endpoint calculations, controls, and full return budget](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q05_2026-10-07.md)

## 1. Evaluate the finite aspect integrals before estimating

**[FINITE_CELL | PAPER]**

Keep
\[
K=m^2,\qquad H=m^{20},\qquad V=V_0,\qquad s=\tfrac12+it.
\]
Write the product ratio as \(\varrho=k\ell/(dh)\), distinguishing it from the Schur shift \(r\), and put
\[
A=\sqrt{2\pi^2\varrho x},\qquad
u_c=\frac A{\pi k},\qquad
a_c=\frac{hA}{2\pi\ell}.
\]
The original full complex carrier and eventual schedule remain unchanged. :chatgpt-content-reference{index="0"}

Use exactly your endpoints
\[
\alpha=\max\!\left(\log(a_c/A_0),-\log u_c,\log(U/(du_c))\right),
\quad
\beta=\log(a_c/U),
\quad
\gamma=\log(V/u_c).
\]
The short interval is the exact base interval intersected with \(v\le\gamma\); the long interval uses \(v>\gamma\). All original inclusion rules remain. Empty intervals contribute zero, not a negatively oriented integral.

For
\[
F(A,v)=e^{iA(\epsilon e^v+\delta e^{-v})},
\qquad
J_j(A;a,b)=\int_a^b v^jF(A,v)\,dv,
\]
an exact finite-endpoint evaluation is
\[
\boxed{
J_j=
\sum_{N=0}^{\infty}\frac{(iA)^N}{N!}
\sum_{p=0}^{N}\binom Np\epsilon^p\delta^{N-p}
\left.\partial_\lambda^j
\frac{e^{\lambda b}-e^{\lambda a}}{\lambda}
\right|_{\lambda=2p-N}.
}
\]
At \(\lambda=0\), the two values are \(b-a\) and \((b^2-a^2)/2\). This series converges absolutely on every finite interval. Its total-degree-\(N\) remainder is bounded by
\[
\left(\int_a^b |v|^j\,dv\right)
\frac{[A(e^b+e^{-a})]^{N+1}}{(N+1)!}.
\]
I use the exact value, so **no additional aspect truncation error** enters the budget.

For each tuple the evaluated expression is
\[
\mu(d)\!\left[
\log u_c\,J_0(I^-)+J_1(I^-)-\log d\,J_0(I^+)
\right]-2\,1_{d=1}J_0(I).
\]
It is then summed over **every** \(dh=qg,\ k\ell=ng\), with weight
\[
\frac{(-1)^k\mu(h)}{qg},
\]
and the original \(h,d,k,\ell\) cutoffs. This is evaluation of the complete collected coefficient—not selection of a saddle tuple.

### An exact cancellation in the complete double-interior term

For equal signs \(\epsilon=\delta=\sigma\), put \(q(v)=v/\sinh v\), with \(q(0)=1\). For opposite signs, put \(q(v)=v/\cosh v\). Finite integration by parts gives
\[
\boxed{
J_1=
\frac1{2i\sigma A}
\left([q(v)F(A,v)]_a^b-\int_a^b q'(v)F(A,v)\,dv\right).
}
\]
Thus, uniformly in both endpoints,
\[
|J_1|\le
\begin{cases}
2/A,&\epsilon=\delta,\\
3/A,&\epsilon=-\delta.
\end{cases}
\]
The equal-sign quotient is smooth through the stationary point; no endpoint has been sent to infinity.

More importantly, sum the quadrants **before a norm**:
\[
\sum_{\epsilon,\delta}F(A,v)
=4\cos(Ae^v)\cos(Ae^{-v}).
\]
This is even in \(v\). If
\[
g_\varrho(x;v)
=\mathcal G_\varrho^{K,H}(Ae^v,Ae^{-v})
\]
is Q4’s complete coefficient with its masks, then
\[
\boxed{
\mathcal I_{K,H}(t;y)
=-2\sum_\varrho\int_{Y_0}^y x^{-s}\int_0^\infty
[g_\varrho(x;v)+g_\varrho(x;-v)]
\cos(Ae^v)\cos(Ae^{-v})\,dv\,dx.
}
\tag{A}
\]

**The entire odd part of the double-interior aspect amplitude cancels.** The asymmetric physical fringes and the \(\log u_c\,J_0\) contribution do not. Equation (A) is not positivity: the coefficient and cosine product are signed, and \(x^{-it}\) remains.

## 2. Moving endpoints produce a forced equation, including corners

**[FINITE_CELL | PAPER]**

On each branch between switches, every active aspect endpoint has
\[
\sigma_b=\frac{db}{d\log A}\in\{-1,+1\}.
\]
Let \(\theta=A\,d/dA\) be the **total derivative**, and let \(\theta_0=A\partial_A\) hold \(v\) fixed.

For
\[
I_l(A)=\int_{\alpha(A)}^{\beta(A)}l(A,v)F(A,v)\,dv,
\qquad
l=c(A)+b_0v,\qquad \theta c=\kappa,
\]
the correct branchwise equation is
\[
\boxed{
(\theta^2+4\epsilon\delta A^2)I_l
=
2\kappa\,\theta J_0
+\left[2l\{F_v+\sigma_v\theta_0F\}\right]_\alpha^\beta.
}
\tag{B}
\]

Here \(\kappa=1\) for \(\log u_c+v\), and \(\kappa=0\) for the long constant or baseline. In particular, the moving logarithmic coefficient produces the term \(2\theta J_0\).

The physical face currents are explicit. With \(z=Ae^v,\ w=Ae^{-v}\),
\[
\boxed{
4i\epsilon z\,lF\quad\text{at fixed }a,
\qquad
-4i\delta w\,lF\quad\text{at fixed }u,
}
\]
with their upper/lower orientation.

At a switch, the integral is continuous but its first \(\theta\)-derivative can jump. The distributional equation additionally contains
\[
\boxed{
\sum_{A_*}
[\theta I_l]_{A_*^-}^{A_*^+}
\,\delta(\log A-\log A_*).
}
\tag{C}
\]
For example, \(J_0(A;-\log A,\log A)\), extended by zero for \(A\le1\), has
\[
[\theta J_0]_{1^-}^{1^+}=2e^{i(\epsilon+\delta)}.
\]
A zero-length interior integral therefore does **not** authorize dropping its corner current. These currents also do not replace the separate prescribed lattice values.

## 3. Combine all boundaries, the zero alias, the compensator, and signed \(C_Q\)

**[FINITE_CELL | PAPER]**

Retain the exact Q4 remainder
\[
e_4(t;y)=\Phi_V(t;y)-\Xi_{K,H}(t;y),
\qquad |e_4|\le\varepsilon_4.
\]
The complete finite expression remains
\[
\Xi_{K,H}
=
\int_{Y_0}^y x^{-it}D_U(x)\,dx
+\mathcal Z_{K,H}
+\mathcal I_{K,H}
+\mathcal B_{K,H}.
\]

Here \(\mathcal Z\) is the transformed a-flux inside \(\Theta\). The boundary term is still
\[
\begin{aligned}
\mathcal B_{K,H}
={}&-\sum_{h\le U}\frac{\mu(h)}h
\sum_{0<|\ell|\le H}
\int G_B(a)e^{2\pi i\ell a/h}\,da\\
&-\sum_{h\le U}\mu(h)
\left\{\mathcal C_h[G]+\mathfrak b(G,Q_{h,H})\right\}.
\end{aligned}
\]
Thus the transformed first edges, first \(Q_K\) jumps, second resummation boundaries, and **actual-value-minus-midpoint corrections without \(1/h\)** all remain.

### The artificial \(V\) face really cancels

The exact quadrature primitive is
\[
\Phi_Q(t;y)=
\int a^{-s}\sum_{\substack{d\le X\\d\ \mathrm{odd}}}\mu(d)d^{-s}
\left[
E_s^1(I^+_{a,d})+\log d\,E_s^0(I^+_{a,d})
\right]\,d\rho_U(a).
\]
Consequently,
\[
\boxed{
E_s^1(I^-)-\log d\,E_s^0(I^+)
+E_s^1(I^+)+\log d\,E_s^0(I^+)
=E_s^1(I).
}
\tag{D}
\]
The long weight becomes
\[
-\log d+\log(du)=\log u.
\]

Thus the \(u=V\) logarithmic jump, its current in (B), and its associated moving-boundary derivatives cancel **at the exact-source level**. At an odd integer \(V\), included-short and excluded-long half-endpoint corrections cancel correctly. In the finite \(\Xi+\Phi_Q\), the discrepancy is precisely the already budgeted \(-e_4\); there is no new free approximation of \(C_Q\).

The zero-first-alias integral plus the unsplit \(E_s^1\) gives the exact odd logarithmic sum. The Möbius convolution gives \(\Lambda(b)\) on every required \(b\).

The retained baseline gives
\[
-2E_s^0(J_a)
=-2\sum_{\substack{b\in J_a\\b\ \mathrm{odd}}}b^{-s}
+\int_{J_a}b^{-s}\,db.
\]
Its mean returns exactly \(x^{-1/2}M_U(x)\,dx\), the original wheel correction—not a discarded term. :chatgpt-content-reference{index="1"}

### The complete physical return

Define the full atomic coefficient
\[
\boxed{
c_n=
\sum_{\substack{a\mid n,\ U<a<A_0\\
b=n/a>U,\ b\ \mathrm{odd}}}
\alpha_U(a)\bigl(\Lambda(b)-2\bigr).
}
\tag{E}
\]
All a-divisors and all odd prime powers are included.

Set
\[
b_0(x)=\max(U,x/A_0),\qquad b_1(x)=x/U,
\]
\[
H_o(z)=\sum_{\substack{b\le z\\b\ \mathrm{odd}}}\frac1b,\quad
\psi_{o,1}(z)=\sum_{\substack{b\le z\\b\ \mathrm{odd}}}\frac{\Lambda(b)}b,\quad
\psi_{2,1}(z)=\sum_{2^j\le z}\frac{\log2}{2^j}.
\]
The complete continuous coefficient becomes
\[
\boxed{
\begin{aligned}
P_U(x)={}&A_U\log x-B_U-1+M_U(x)\\
&-A_U\left\{
\psi_{o,1}(b_0(x))+\psi_{2,1}(b_1(x))
+2[H_o(b_1(x))-H_o(b_0(x))]
\right\}.
\end{aligned}}
\tag{F}
\]

The decisive cancellation here is specific: the continuous \(A_U\,da\) flux contributes its **upper odd-prime harmonic sum**, which cancels the corresponding part of \(-A_U\psi_1(x/U)\) in \(D_U\). The lower prime face, upper powers-of-two term, odd baseline, and decaying pole survive. The original positive sign of \(A_U\,da\) is essential. :chatgpt-content-reference{index="2"} :chatgpt-content-reference{index="3"}

The complete identity is therefore
\[
\boxed{
\Xi_{K,H}(t;y)+\Phi_Q(t;y)
=
\sum_{Y_0\le n\le y}c_n n^{-s}
+\mathcal C_s(y)-e_4(t;y),
}
\tag{G}
\]
where
\[
\boxed{
\mathcal C_s(y)=
\int_{Y_0}^y\left[x^{-s}P_U(x)+x^{-s-1}\right]dx.
}
\]

This is the return of **all** the boundary operations, not an assertion that they vanish individually. At an included integer product \(n\), the primitive jump is exactly \(c_n n^{-s}\). Continuous density conventions do not alter those atoms.

## 4. Evaluate and bound the whole continuous boundary package

**[FINITE_CELL | PAPER]**

Put
\[
\nu=1-s,\qquad
P_s^0(z)=\frac{z^\nu}{\nu},\qquad
P_s^1(z)=z^\nu\left(\frac{\log z}{\nu}-\frac1{\nu^2}\right),
\]
and
\[
B_s(c;y)=
\begin{cases}
P_s^0(y)-P_s^0(\max(Y_0,c)),&y>\max(Y_0,c),\\
0,&y\le\max(Y_0,c).
\end{cases}
\]
Write \([P_s^j]=P_s^j(y)-P_s^j(Y_0)\). Also let
\[
\mathcal M_s(y)=
\int_{Y_0}^y x^{-s}
\log\!\left(\frac{\min(A_0,x/U)}U\right)dx.
\]
This last integral is elementary: below \(UA_0\), use \(P_s^1-2\log U\,P_s^0\); above \(UA_0\), use \(\log(A_0/U)P_s^0\), with the exact joining value.

The full finite endpoint evaluation is
\[
\boxed{
\begin{aligned}
\mathcal C_s(y)={}&
A_U[P_s^1]-(B_U+1+A_U\psi_{o,1}(U))[P_s^0]\\
&+\sum_{U<a<A_0}\frac{\alpha_U(a)}a B_s(Ua;y)
+A_U\mathcal M_s(y)\\
&-A_U\sum_{\substack{U<b\le m/A_0\\b\ \mathrm{odd}}}
\frac{\Lambda(b)-2}{b}B_s(A_0b;y)\\
&-A_U\sum_{2^j\le X}\frac{\log2}{2^j}B_s(U2^j;y)
-2A_U\sum_{\substack{U<b\le X\\b\ \mathrm{odd}}}\frac1b B_s(Ub;y)\\
&+\frac{Y_0^{-s}-y^{-s}}s.
\end{aligned}}
\tag{H}
\]
Thus the surviving continuous package is expressed through the physical faces \(Ua\), \(A_0b\), and \(Ub\). No high prime harmonic term at \(x/U\) is left as an independent error.

### A uniform integrated estimate

**[COFINAL_FAMILY | PAPER]**

On every sufficiently late original cell,
\[
\boxed{
\sup_{Y_0\le y\le m}
|\mathcal C_{1/2+it}(y)|
\le
128h_U^2(1+L)^2\frac{\sqrt m}{1+|t|},
\qquad t\in\mathbb R.
}
\tag{I}
\]

Here is the budget behind the constant. After the signed cancellations above,
\[
\sum_{U<a<A_0}\frac{|\alpha_U(a)|}{a}\le h_U(1+L),
\]
\[
\sum_{\substack{U<b\le m/A_0\\b\ \mathrm{odd}}}
\frac{|\Lambda(b)-2|}{b}\le3(1+L)^2,
\]
and the powers-of-two harmonic mass is below \(1\). Every active \(B_s\) costs at most \(2\sqrt m/|\nu|\). Integration by parts on the continuous logarithmic part gives
\[
|\mathcal M_s(y)|\le\frac{2\sqrt m(1+L)}{|\nu|}.
\]
Substitution into (H) yields
\[
|\mathcal C_s(y)|
\le
\frac{24h_U^2(1+L)^2\sqrt m}{|\nu|}
+\frac{2h_U\sqrt m}{|\nu|^2}
+\frac{2}{\sqrt{Y_0}|s|}.
\]
Now \(|s|=|\nu|\), \(1/|\nu|\le3/(1+|t|)\), and \(1/|\nu|^2\le6/(1+|t|)\), proving (I). The estimate includes \(t=0\); it does not assert smallness there.

Let \(C_{\mathrm{ct}}\) be the original-carrier compression of this complete continuous measure. For the top-half projection
\[
P_{\mathrm{top}}:\quad \lceil m/2\rceil\le|j|\le m,
\]
the coupled diagonal/commutator synthesis gives
\[
\boxed{
\|P_{\mathrm{top}}C_{\mathrm{ct}}P_{\mathrm{top}}\|
\le
\frac{512}{\pi}h_U^2(1+L)^2\frac{L}{\sqrt m}
=o(1).
}
\tag{J}
\]
This includes positive–negative top cross modes. The synthesis has no carrier-dimension loss. :chatgpt-content-reference{index="4"}

**Scope:** (J) is not a bound for the full continuous operator, its low–top coupling, the atomic operator, or the actual Schur form. No support property of \(J_rv\) has been assumed.

## 5. Where the full integrated test stops

**[FINITE_CELL | PAPER]**

I next used the moving-endpoint equation, rather than assuming a complete Bessel kernel.

For a tuple, set
\[
\zeta=2-2s=1-2it.
\]
Since \(x=A^2/(2\pi^2\varrho)\),
\[
x^{-s}dx=2(2\pi^2\varrho)^{s-1}A^{\zeta-1}\,dA.
\]
Integrating (B) with all product endpoints and corner currents gives
\[
\boxed{
\begin{aligned}
\int A^{\zeta-1}
(\zeta^2+4\epsilon\delta A^2)I_l(A)\,dA
={}&
\int A^{\zeta-1}[2\kappa\theta J_0+B_l(A)]\,dA\\
&+\sum_{A_*}A_*^\zeta[\theta I_l]_{A_*^-}^{A_*^+}\\
&-[A^\zeta(\theta I_l-\zeta I_l)]_{\mathrm{ends}},
\end{aligned}}
\tag{K}
\]
where \(B_l\) is the oriented face current in (B).

Only the artificial \(V\) face disappears after signed \(C_Q\). The remaining currents are exactly the physical faces returned in (E)–(H).

For the same-sign quadrants,
\[
\boxed{
\zeta^2+4A^2=4(A^2-t^2)+1-4it.
}
\]
Near \(A=|t|\), its magnitude is of order \(|t|\), not \(t^2\), and its real part changes sign. More directly, the remaining radial phase is
\[
\varphi(A)=2A-2t\log A,\qquad
\varphi'(A)=2(1-t/A).
\]
For \(t>0\), it is stationary at
\[
\boxed{
A=t,\qquad x=\frac{t^2}{2\pi^2\varrho}.
}
\]
These points occur inside the actual integration domains; the accepted Q4 construction establishes that geometry with all four selected numbers odd primes. **No coefficient from that construction is used here as an integral lower bound.**

Therefore the proposed completion by **uniform radial nonstationarity** has a false hypothesis on the required domain. Equation (K) is also forced, not homogeneous, and its ratio-dependent multiplier cannot be factored out of the complete arithmetic sum.

This is an obstruction to that analytic step—not a source counterexample or a kill of the finite-aspect representation.

The exact surviving integrated expression is
\[
\begin{aligned}
&-2\sum_\varrho\int_{Y_0}^y x^{-s}\int_0^\infty
[g_\varrho(x;v)+g_\varrho(x;-v)]
\cos(Ae^v)\cos(Ae^{-v})\,dv\,dx\\
&\qquad+\mathcal Z_{K,H}+\mathcal B_{K,H}
+\int_{Y_0}^y x^{-it}D_U(x)\,dx+\Phi_Q(t;y),
\end{aligned}
\]
equivalently the right side of (G).

The continuous part has the proved estimate (I). **There is no new signed estimate for the atomic sum against that continuous part, or for the equivalent complete even-aspect kernel with its physical edges.** The aspect calculation has not supplied the missing arithmetic cancellation.

## 6. Full matrix and actual Schur budget

**[FINITE_CELL | PAPER]**

Use the same \(\Xi\) for both pieces of the matrix:
\[
h_j^{(5)}=\Im\Xi(\omega_j;m),\qquad
d_j^{(5)}=\frac2L\Re\int_0^L\Xi(\omega_j;e^u)\,du,
\]
\[
C^{(5)}
=\operatorname{diag}(d_j^{(5)})
+\pi^{-1}[\operatorname{diag}(h_j^{(5)}),H^{\mathrm d}].
\]
The finite-aspect evaluation changes neither the approximation nor its error:
\[
C[\tau_V]=C^{(5)}+E^{(5)},\qquad
\|E^{(5)}\|\le4\varepsilon_4.
\]

Keep \(C_Q\) signed. Then
\[
H_m(r)=rI-(C^{(5)}+C_Q)+F_{10}-E^{(5)}.
\]
For the actual \(f=J_rv=v+y\),
\[
\boxed{
P_{\mathcal R}(C^{(5)}+C_Q)f
=ry+P_{\mathcal R}(F_{10}-E^{(5)})f.
}
\]
The original regular space and full \(B_r^*A_r^{-1}B_r\) correction remain. :chatgpt-content-reference{index="5"}

With
\[
s_5(v)=r\|v\|^2-
\Re\langle v,(C^{(5)}+C_Q)J_rv\rangle,
\]
the complete discriminator is
\[
\boxed{
\begin{aligned}
s_5(v)-(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|
&\le\langle v,\mathfrak S_m(r)v\rangle\\
&\le s_5(v)+(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|.
\end{aligned}}
\tag{L}
\]

**[COFINAL_FAMILY | PAPER]** Every inherited term remains:
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
\]
These are the original raw-small, Type-I, long-a, wheel, and powers-of-two allocations. :chatgpt-content-reference{index="6"} :chatgpt-content-reference{index="7"} :chatgpt-content-reference{index="8"}

Also,
\[
\varepsilon_4=
\frac{256h_U(1+L)^2(1+\Omega)\sqrt m}{m^2}
+\frac{2^{24}}{m^5}.
\]
Hence
\[
4\varepsilon_4=O(h_ULm^{-1/2}),
\qquad
\Delta_{10}=O(m^{5/12}L^{3/2}\log(2L)).
\]

The new top-block component estimate does **not** eliminate any fixed-power allocation here. Nor is \(\|J_rv\|\) replaced by \(\|v\|\).

The full archimedean return remains
\[
\begin{aligned}
W(f)\ge{}&
D_{\rm arch}(f)
-(c_A+\delta_{10}+4\varepsilon_4)\|f\|^2
+2\langle f,(R+R^*)f\rangle\\
&-\langle f,(C^{(5)}+C_Q)f\rangle,
\qquad \delta_{10}=\Delta_{10}-(L+8).
\end{aligned}
\]
Its last signed term is unestimated. No derivative absorption is reinstated. :chatgpt-content-reference{index="9"}

## Closeout

**Newly proved:** the total moving-endpoint equation, its corner currents, exact cancellation of the \(V\) interface after signed return, evaluation of the complete continuous physical-face package, and its uniform bound (I) with the top-block consequence (J).

**Still unproved:** the full signed integrated estimate and actual Schur sign. No new theorem-shape kill is claimed. The concrete stopping reason is the forced physical-boundary return together with the surviving radial stationary region—not merely a large upper estimate or another coefficientwise conjecture.

The next bounded test should target the **actual Schur form**, not another scalar transform. A source-defined three-moment test is available: set
\[
g=r-\epsilon_m,\quad b=B_rv,\quad
M_0=\|b\|^2,\quad M_1=\langle b,A_rb\rangle,\quad M_2=\|A_rb\|^2,
\]
and \(q(v)=\langle v,H_{EE}v\rangle\). Optimizing residual-completed trial lifts \(y=-\alpha b\) gives, when \(M_2-gM_1>0\),
\[
\boxed{
q(v)-\frac{M_0}{g}
+\frac{(M_1-gM_0)^2}{g(M_2-gM_1)}
\le\langle v,\mathfrak S_m(r)v\rangle
\le q(v)-\frac{M_0^2}{M_1}.
}
\]
The verdict covers the zero-denominator cases. The bounded task is to estimate these **actual signed source moments with all inherited components present**. This identity is a test, not an asserted source sign.

**SP/G1/G3/RH and the actual Schur sign remain OPEN. The new PAPER derivations require independent audit.**
