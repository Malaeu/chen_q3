# Rollover answer3 — exact inline capture

Chat Execute Multilinear Source Test, 6ac58a1c-1568-83ed-95d0-857526e2b6cb.
Question 0a98badc-fec4-4f86-a288-5d88965169db; answer 182d7b89-2a49-4a8d-a29e-c6cd7f031782.
Captured 2026-10-07 after reconnect. Independent audit completed; see ODD_POISSON_AUDIT_2026-10-07.md.

---

Ы — **the infinite alias tail can be paid uniformly, including every endpoint. The complete stationary arithmetic still does not yield a new signed Schur bound.**

The decision-changing obstruction is now source-specific: **after collecting every discrete a-divisor, Möbius sector, and representation of the same rational alias frequency, some stationary coefficients remain bounded away from zero after their natural normalization.** The continuous a-flux does not cancel those Fourier atoms *as a measure*. This does **not** prevent cancellation after the full frequency sum and physical integration.

:chatgpt-content-reference{index="9"}[Complete PAPER verdict, proofs, coefficient controls, and return budget](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q03_2026-10-07.md)

## 1. Uniform tail control requires an exact boundary resummation

**[FINITE_CELL | PAPER]**

Keep
\[
L=\log m,\quad U=\lceil L\rceil,\quad X=m/U,\quad
V=V_0=X/\lceil X^{1/3}\rceil,\quad \Omega=2\pi m/L,
\]
and write \(p_L=1+L\), \(s=\tfrac12+it\).

Use the unchanged intervals
\[
\begin{aligned}
J_a(y)&=(U,\infty)\cap[Y_0/a,y/a],\\
I_{a,d}(y)&=[1,\infty)\cap\{u:du\in J_a(y)\},\\
I^-_{a,d}&=I_{a,d}\cap[1,V],\qquad
I^+_{a,d}=I_{a,d}\cap(V,\infty).
\end{aligned}
\]

For interval functionals \(T^1,T^0\), abbreviate the **complete signed operation** by
\[
\begin{aligned}
\mathfrak A_{t,y}[T^1,T^0]
=\int_{U<a<A_0}a^{-s}\bigg\{
\sum_{\substack{d\le X\\d\ {\rm odd}}}\mu(d)d^{-s}
\left[T^1(I^-_{a,d})-\log d\,T^0(I^+_{a,d})\right]
-2T^0(J_a)
\bigg\}\,d\rho_U(a).
\end{aligned}
\]
Both
\[
d\rho_U(a)=\sum_{a>U}\alpha_U(a)\delta_a+A_U\,da
\]
and the continuous compensator remain inside the calculation. The sign of \(A_U\,da\) is positive, as in the original source. :chatgpt-content-reference{index="0"}

Define
\[
F_{j,t}(u)=u^{-1/2-it}(\log u)^j,\qquad
\mathcal I_k^j(t;I)=\int_I F_{j,t}(u)e^{i\pi ku}\,du.
\]

The new step beyond the supplied Fejér representation is to retain the **boundary Fourier tail**
\[
Q_K(u)=\epsilon_o^{\rm mid}(u)
-\sum_{k=1}^{K}\frac{(-1)^k\sin(\pi ku)}{\pi k},
\]
where \(\epsilon_o^{\rm mid}(u)=\lfloor(u+1)/2\rfloor-u/2\) away from odd integers and is zero at odd integers.

For every nondegenerate \(I\) with endpoints \(\ell,h\), \(\ell\ge1\), and
\[
K\ge\max\!\left(1,\frac{2|t|}{\pi\ell}\right),
\]
the exact identity is
\[
\boxed{
\begin{aligned}
E_s^j(I)
={}&\mathcal C_t^j(I)
+\frac12\sum_{0<|k|\le K}(-1)^k\mathcal I_k^j(t;I)\\
&+[F_{j,t}(u)Q_K(u)]_\ell^h+\mathcal T_K^j(t;I),\\
|\mathcal T_K^j(t;I)|
\le{}&\frac{8p_L^j(1+|t|)}{K\ell^{3/2}}.
\end{aligned}}
\tag{7}
\]
Here \(\mathcal C_t^j\) is precisely the endpoint correction specified in your question. Included odd singletons contribute their full value separately; other singletons and empty intervals contribute zero.

### Why this estimate is uniform

For \(k>K\), the two phases satisfy
\[
|\phi_{\pm k}'(u)|\ge\pi k/2,\qquad
|\phi_{\pm k}''(u)|=|t|/u^2.
\]
Integrating against the **full phase**, the leading paired boundary contribution is exactly
\[
[F_{j,t}(u)\sin(\pi ku)/(\pi k)]_\ell^h.
\]
After removing it, a second integration by parts bounds the remaining paired term by
\[
\frac{8p_L^j(1+|t|)}{k^2\ell^{3/2}}.
\]
Its tail is absolutely summable. The \(1/k\) boundary series, by contrast, is retained in \(Q_K\), not mislabeled as a uniformly small error. This is the finite integration-by-parts remainder mechanism with its derivative hypotheses verified explicitly. :chatgpt-content-reference{index="1"}

At an odd endpoint \(Q_K=0\); the required half-atom still comes from \(\mathcal C_t^j\). Near that endpoint, \(Q_K\) retains the boundary layer that bare finite Fourier sums cannot recover uniformly.

Let \(\widehat\Phi_K\) be the complete primitive obtained from (7), keeping its first three terms and retaining
\[
\Theta_U(x)=D_U(x)+\frac{x^{-1/2}}2
\int_{\substack{U<a<A_0\\a<x/U}}
\frac{H_o(x/a)}a\,d\rho_U(a)
\]
unchanged.

Then, on every sufficiently late original cell, choose \(K=m^2\). The full a-flux gives
\[
\boxed{
\sup_{\substack{|t|\le\Omega\\Y_0\le y\le m}}
|\Phi_V(t;y)-\widehat\Phi_K(t;y)|
\le\varepsilon_K
:=\frac{256h_Up_L^2(1+\Omega)\sqrt m}{K}
\le\frac{8192h_UL}{\sqrt m}.
}
\tag{9}
\]

The summation uses the actual product restriction \(d\le y/a\) and
\[
\sum_{d\le y/a}d^{-1/2}\le2\sqrt{y/a},
\qquad
\int_{U<a<A_0}\frac{|d\rho_U(a)|}{a}\le2h_Up_L.
\]
The latter includes both the atomic divisor flux and the continuous \(A_U\,da\).

**This pays the infinite analytic tail. It does not estimate the retained stationary sum.**

## 2. Stationary aliases have a uniform clipped normal form

**[ABSTRACT | PAPER]**

Take \(t=\tau>0\); negative \(t\) follows by conjugation. For \(k>0\), put
\[
u_k=\frac{\tau}{\pi k},\qquad
I_{k,\mathrm c}=I\cap[u_k/2,2u_k].
\]

On a nonempty core, use the exact change of variable
\[
r=u/u_k,\qquad
w=\operatorname{sgn}(r-1)\sqrt{2(r-1-\log r)},\qquad
z=\sqrt\tau\,w.
\]
The core integral becomes
\[
\sqrt{u_k}\,e^{i\tau(1-\log u_k)}
\int_{w_-}^{w_+}G_j(w)e^{i\tau w^2/2}\,dw,
\]
where
\[
G_j(w)=r(w)^{-1/2}\frac{dr}{dw}
[\log u_k+\log r(w)]^j.
\]

Thus, with
\[
\mathcal F(z_-,z_+)=\int_{z_-}^{z_+}e^{iz^2/2}\,dz,
\]
we obtain
\[
\boxed{
\mathcal I_{k,\mathrm c}^j
=
\frac{e^{i\tau(1-\log u_k)}}{\sqrt{\pi k}}
(\log u_k)^j\mathcal F(z_-,z_+)
+R_{k,\mathrm c}^j,
\qquad
|R_{k,\mathrm c}^j|
\le\frac{1024p_L^j}{\sqrt{k\tau}}.
}
\tag{14}
\]

This is uniform when a saddle meets a clipped endpoint. **The Fresnel limits are not replaced by infinity.**

For an explicit remainder, set
\[
H_j(w)=\frac{G_j(w)-G_j(0)}w.
\]
Then
\[
R_{k,\mathrm c}^j=
\frac{\sqrt{u_k}\,e^{i\tau(1-\log u_k)}}{i\tau}
\left(
[H_j(w)e^{i\tau w^2/2}]_{w_-}^{w_+}
-\int_{w_-}^{w_+}H_j'(w)e^{i\tau w^2/2}\,dw
\right).
\]
The verdict proves the displayed constant directly on \(1/2\le r\le2\).

### Nonstationary complements and transition cases

On a clipped dyadic box \(I\subset[B,2B]\), only
\[
\frac{\tau}{4\pi B}\le k\le\frac{2\tau}{\pi B}
\]
can have a core meeting the box.

Outside the core, the phase derivative is separated from zero by a fixed factor. Combining its first-derivative estimate with the endpoint-resummed high tail yields
\[
\boxed{
E_s^j(I)=\mathcal S_t^j(I)+\mathcal N_t^j(I),
\qquad
|\mathcal N_t^j(I)|\le\frac{2^{16}p_L^j}{\sqrt B}.
}
\tag{18}
\]
Here \(\mathcal S\) is the finite signed sum of the clipped leading terms in (14). The signed \(\mathcal N\) contains **all** nonstationary pieces, stationary remainders, and endpoint corrections.

For \(0\le\tau<1\), no core meets \([1,X]\). More generally, \(\tau\le B/4\) gives a wholly nonstationary box and the same \(O(p_L^j/\sqrt B)\) bound. No low-frequency interval is inferred from a singular \(\tau^{-1/2}\) formula.

After applying the complete operation \(\mathfrak A\),
\[
\boxed{
\Phi_V(t;y)
=
\int_{Y_0}^y x^{-it}\Theta_U(x)\,dx
+\mathfrak A_{t,y}[\mathcal S_t^1,\mathcal S_t^0]
+\mathcal R_{\rm sad}(t;y),
\qquad
|\mathcal R_{\rm sad}|
\le2^{22}h_Up_L^2\sqrt m.
}
\tag{19}
\]

This is the exact cost of a tempting but unsuccessful completion: **discarding the full first-order transition/nonstationary remainder would introduce a square-root-scale allocation.** That bound does not prove the remainder is large. It proves only that this estimate cannot be spent as a small error.

Accordingly, the preferred return retains the **exact finite integrals** from Section 1, not merely the leading saddle approximation.

## 3. Collect the actual a/Möbius arithmetic at equal rational frequencies

**[FINITE_CELL | PAPER]**

This is the arithmetic test beyond individual aliases.

At a physical product value \(x\), define
\[
\mathcal A(x)=(U,A_0)\cap(0,x/U)
\]
and
\[
W_{a,d}(x)=
\begin{cases}
\log(x/(ad)),&1\le x/(ad)\le V,\\
-\log d,&x/(ad)>V,\\
0,&x/(ad)<1.
\end{cases}
\]

The substitution \(x=adu\) puts the finite aliases and their compensator into **one signed frequency measure**:
\[
\boxed{
\begin{aligned}
\nu_{x,K}={}&
\int_{\mathcal A(x)}\frac{d\rho_U(a)}a
\bigg[
\sum_{\substack{d\le x/a\\d\ {\rm odd}}}
\frac{\mu(d)}dW_{a,d}(x)
\sum_{k\ne0}(-1)^kw_K(k)\delta_{k/(ad)}\\
&\hspace{38mm}
-2\sum_{k\ne0}(-1)^kw_K(k)\delta_{k/a}
\bigg]
+2\sqrt x\,\Theta_U(x)\delta_0.
\end{aligned}}
\tag{21}
\]
Here \(w_K\) can be the supplied Fejér weight or the ordinary finite cutoff used above.

The complete finite interior expression is
\[
\frac12\int_{Y_0}^{y}x^{-s}
\left[\int e^{i\pi\lambda x}\,d\nu_{x,K}(\lambda)\right]dx.
\]
The endpoint corrections and the \(Q_K\) boundary operations are added exactly as in (7).

The Jacobian gives **\(1/(ad)\)** outside \(x^{-s}\). The last term in (21) contributes exactly \(x^{-it}\Theta_U(x)\), once—not an extra positive zero alias.

### All discrete a-divisors combine first

For each integer \(c\le x\), put
\[
\begin{aligned}
A_c(x)&=
\sum_{\substack{a\mid c\\a\in\mathcal A(x)\\c/a\ {\rm odd}}}
\alpha_U(a)\mu(c/a),\\
B_c(x)&=
\sum_{\substack{a\mid c\\a\in\mathcal A(x)\\c/a\ {\rm odd}}}
\alpha_U(a)\mu(c/a)\log(c/a).
\end{aligned}
\]
The complete coefficient at \(c=ad\) is
\[
\boxed{
\eta_c(x)=\frac1c\left[
1_{1\le x/c\le V}\log(x/c)A_c(x)
-1_{x/c>V}B_c(x)
-2\alpha_U(c)1_{c\in\mathcal A(x)}
\right].
}
\tag{23}
\]

Now reduce \(k/c=n/q\), with \((|n|,q)=1\). Every representation is \(c=qg,\ k=ng\). Therefore the **whole reduced-frequency coefficient** is
\[
\boxed{
\mathcal W_{n,q}^{(K)}(x)
=
\sum_{1\le g\le x/q}
(-1)^{ng}w_K(ng)\eta_{qg}(x).
}
\tag{24}
\]

This combines identical phases before taking absolute values. In particular, the parity factor is \((-1)^{ng}\); \(q\) need not be odd because the original a-flux is not odd-supported.

### What actually cancels

On the uncropped divisor range
\[
c\ {\rm odd},\qquad U<c<\min(A_0,x/U),
\]
the identities \(\alpha_U=\mu_{>U}*1\) and \(1*(\mu\log)=-\Lambda\) give
\[
\boxed{
A_c(x)=\mu(c),\qquad
B_c(x)=-(\mu_{>U}*\Lambda)(c).
}
\tag{26}
\]

This is a genuine signed cancellation: the complete divisor coefficient \(A_c\) has magnitude at most one instead of a divisor-multiplicity bound. It does **not** estimate the remaining reduced \(g\)-sum, cropped ranges, or continuous terms.

The continuous \(A_U\,da\) part remains in (21). For each \(d,k\), its change of variable
\[
\lambda=\frac{k}{ad}
\]
has
\[
\frac{|da|}{a}=\frac{|d\lambda|}{|\lambda|}.
\]
Consequently it produces an **absolutely continuous frequency density**, with the same \(\mu(d)/d\), logarithmic switch, baseline, and product restrictions. The full formula is equation (25) of the verdict. Every bounded frequency interval involves finitely many relevant indices, so this is not a formal interchange of divergent measures.

## 4. A complete stationary coefficient survives on every late original cell

**[COFINAL_FAMILY | PAPER]**

Choose odd primes
\[
U<\ell\le2U,\qquad
\frac{m}{64U}<p\le\frac{m}{32U},
\qquad q=\ell p.
\]
The accepted elementary dyadic-prime count supplies them eventually. Then
\[
p>A_0,\qquad \ell<A_0,\qquad m/64<q\le m/16.
\]

For every
\[
\frac43q\le x\le\frac53q,
\]
we have \(Y_0<x<m\), \(x/q<V\), and \(q>x/2\).

There is exactly one allowed a-divisor of \(q\): **\(a=\ell\)**. The others are below \(U\) or above \(A_0\). Moreover,
\[
\alpha_U(\ell)=-1,\qquad \mu(p)=-1,
\]
so \(A_q(x)=1\). The baseline at \(c=q\) is absent because \(q>A_0\).

In the fully reduced sum (24), **only \(g=1\) is possible**, since \(x/q<2\). Therefore
\[
\boxed{
\mathcal W_{n,q}(x)
=(-1)^n\frac{\log(x/q)}q,
\qquad
q|\mathcal W_{n,q}(x)|\ge\log(4/3)>0.
}
\tag{29}
\]

This is not an isolated \((a,d,k)\) summand: every representation of that reduced frequency has been collected.

There is also an actual top-frequency saddle. Take \(t=\Omega\), and choose \(n\), coprime to \(\ell p\), among the three consecutive integers starting at
\[
\left\lfloor\frac{2\Omega}{3\pi}\right\rfloor.
\]
Each prime divides at most one of those three integers. Hence such an \(n\) exists, and eventually
\[
\boxed{
x_*=\frac{\Omega q}{\pi n}\in[4q/3,5q/3].
}
\tag{30}
\]
The phase \(\pi(n/q)x-\Omega\log x\) is stationary at \(x_*\).

The continuous a-density has no atom at \(n/q\), and the compensator in (21) lies at frequency zero. Thus the candidate coefficientwise estimate
\[
q|\nu_x(\{n/q\})|\le\delta_m,\qquad \delta_m\to0,
\]
uniformly on this stationary domain, has the negative upper slack
\[
\boxed{
\delta_m-q|\nu_{x_*}(\{n/q\})|
\le\delta_m-\log(4/3)<0.
}
\tag{31}
\]

**Killed:** uniform normalized suppression at each reduced stationary frequency, including automatic annihilation of all stationary aliases by Möbius/a-flux collection.

**Not killed:** the full signed integral. Different rational frequencies, the continuous density, the physical \(x\)-integration, and the endpoint terms can still cancel. Equation (31) proves neither a large compressed norm nor a negative actual Schur direction.

## 5. The precise surviving phase and stopping reason

The stationary phase after restoring the a/d weights is
\[
\boxed{
\frac{\mu(d)}
{\sqrt{\pi a d k}}\,
e^{i\tau[1-\log(\tau/\pi)+\log(k/(ad))]},
}
\tag{32}
\]
multiplied by its clipped Fresnel factor, the short or long logarithm, and \((-1)^k/2\).

At a fixed carrier frequency,
\[
e^{i\tau\log(k/(ad))}
\overline{e^{i\tau\log(k'/(ad))}}
=e^{i\tau\log(k/k')}.
\]
The displayed phase has **zero curvature in \(a\) and \(d\)** after this correlation. Any useful additional oscillation would have to be proved in the retained arithmetic and clipped amplitudes; it is not supplied by a unit-amplitude curvature theorem.

There is also no automatic shortening: a free-factor range \(u\asymp B\) becomes \(k\asymp\tau/B\). The family above has \(u\in[4/3,5/3]\) and \(k\asymp\Omega\), and survives the complete reduced-frequency collection.

**Stop:** free-factor Poisson transformation followed by either coefficientwise Möbius smallness or presumed new curvature in the Möbius variable.

The surviving object is explicitly (21)–(25), together with both endpoint operations. A useful estimate must exploit **cancellation between distinct reduced fractions and their continuous/boundary contributions**, or only the actual pairing \((v,J_rv)\). The available whole-primitive fallback remains the accepted
\[
\sup_{|t|\le\Omega,\ y\le m}|\Phi_V(t;y)|
\le32h_Up_L^3\sqrt m;
\]
this test has not improved it.

## 6. Complete matrix and actual Schur budget

**[FINITE_CELL | PAPER]**

Form the same coupled data from \(\widehat\Phi_K\):
\[
\widehat h_j=\Im\widehat\Phi_K(\omega_j;m),\qquad
\widehat d_j=\frac2L\Re\int_0^L\widehat\Phi_K(\omega_j;e^u)\,du,
\]
\[
\widehat C_K=
\operatorname{diag}(\widehat d_j)
+\pi^{-1}[\operatorname{diag}(\widehat h_j),H^{\rm d}].
\]
The accepted synthesis includes all cross modes and \(\|H^{\rm d}\|\le\pi\). :chatgpt-content-reference{index="2"}

Consequently,
\[
\boxed{
C[\tau_V]=\widehat C_K+\mathcal E_K,
\qquad \|\mathcal E_K\|\le4\varepsilon_K.
}
\tag{35}
\]
This does not assume the endpoint-resummed approximation is the primitive of a common frequency-independent measure: it synthesizes a finite self-adjoint matrix and proves its distance to the actual source matrix.

Keep the actual
\[
f=J_rv=v+y,\qquad y=-A_r^{-1}B_rv,\qquad r>\epsilon_m.
\]
With \(C_Q=C[\sigma_{Q,V}]\),
\[
\widehat F_K=F_{10}-C_Q-\mathcal E_K,
\]
the actual regular equation is
\[
\boxed{
P_{\mathcal R}\widehat C_Kf
=ry+P_{\mathcal R}\widehat F_Kf.
}
\tag{37}
\]
The original spaces and full Schur correction remain unchanged. :chatgpt-content-reference{index="3"}

Paying Q1’s quadrature gives the error
\[
\Delta_{10}+E_V+4\varepsilon_K.
\]
The better choice is to keep \(C_Q\) **signed**. Define
\[
\widehat s_K(v)=r\|v\|^2-
\Re\langle v,(\widehat C_K+C_Q)J_rv\rangle.
\]
Then
\[
\boxed{
\begin{aligned}
\widehat s_K(v)-(\Delta_{10}+4\varepsilon_K)\|v\|\|J_rv\|
&\le\langle v,\mathfrak S_m(r)v\rangle\\
&\le\widehat s_K(v)+(\Delta_{10}+4\varepsilon_K)\|v\|\|J_rv\|.
\end{aligned}}
\tag{38}
\]

No bound on \(\|J_r\|\) is assumed. In particular, a vanishing **carrier-norm** error does not automatically become a vanishing exceptional-space error without its displayed \(\|J_rv\|\).

The entire inherited allocation remains
\[
\boxed{
\begin{aligned}
\Delta_{10}
={}&L+8
+8\sqrt{Y_0}(1+\log Y_0)
+\frac{1600M_{U,L}(1+\sqrt\Omega)}{\sqrt{Y_0}}\\
&+4\mathcal M_m+4M_{\rm wheel}+\Pi_m,
\qquad
M_{U,L}=3UL+U^2\log(2U).
\end{aligned}}
\]
The verdict expands every term. These are the original raw-small, Type-I, long-a, wheel, and powers-of-two costs—not new omissions. :chatgpt-content-reference{index="4"} :chatgpt-content-reference{index="5"} :chatgpt-content-reference{index="6"}

Their scales are
\[
E_V=O(h_Um^{1/3}L^{13/6}),\qquad
4\varepsilon_K=O(h_ULm^{-1/2}),\qquad
\Delta_{10}=O(m^{5/12}L^{3/2}\log(2L)).
\]
Thus signed recombination removes the introduced \(E_V\) allocation, **not the inherited \(5/12\) allocation**. Neither version supplies all-eta SP.

The full archimedean form can remain explicit:
\[
\boxed{
\begin{aligned}
W(f)\ge{}&
D_{\rm arch}(f)
-(c_A+\delta_{10}+4\varepsilon_K)\|f\|^2
+2\langle f,(R+R^*)f\rangle\\
&-\langle f,(\widehat C_K+C_Q)f\rangle,
\qquad \delta_{10}=\Delta_{10}-(L+8).
\end{aligned}}
\tag{40}
\]
Its final signed term is unestimated; no derivative absorption or full bottom floor is claimed. :chatgpt-content-reference{index="7"}

The discriminator remains literal: a nonnegative lower envelope for every actual exceptional vector certifies the cell; a negative upper envelope for an actual exceptional vector certifies a negative Schur direction. The rational-frequency coefficient witness is neither.

## Closeout and next bounded test

The exact arithmetic controls passed: **885** interior convolution checks and **4,376** rational/logarithmic coefficient comparisons. A planted sign reversal failed **439** checks. These are auxiliary controls, not substitutes for the cofinal proofs or interval certificates.

The test has established a uniform endpoint-safe analytic tail, a clipped stationary formula, the complete rational-frequency arithmetic coefficient, and a narrow cofinal obstruction to coefficientwise cancellation. **It has not improved the actual signed Schur estimate.**

The next selected test is the **second Poisson transform of the centered a-flux**, whose exact input is
\[
d\rho_U(a)=
-\sum_{h\le U}\mu(h)
\left(\sum_{j\ge1}\delta_{hj}(da)-\frac1h\,da\right),
\qquad a>U.
\]
It must be applied to the complete expression above, including its first-transform boundary terms and compensator. The two-alias phase is
\[
\pi ku+\frac{2\pi\ell a}{h}-t\log(adu),
\]
with simultaneous saddle
\[
u_*=\frac{t}{\pi k},\qquad
a_*=\frac{th}{2\pi\ell},\qquad
x_*=\frac{t^2dh}{2\pi^2k\ell}.
\]
The bounded task is to collect identical **product ratios** \(k\ell/(dh)\) with the actual signed weights before estimating—not to apply another independent positive alias envelope.

**SP, G1, G3, RH, and the actual exceptional Schur sign remain OPEN. These new PAPER derivations still require independent audit.**
