# Rollover answer1 — exact inline capture

Chat Execute Multilinear Source Test, 6ac58a1c-1568-83ed-95d0-857526e2b6cb.
Question1744596a-e79e-4e60-80f9-04cad01421ec; answer8eec1ad3-f3e8-4b5f-bd23-8e85874a1e2c.
Captured untruncated via read_thread 2026-10-07. Independent audit completed; see LINEAR_CONVOLUTION_AUDIT_2026-10-07.md.
Exact question/attachment: GROWTH_ROLLOVER_QUESTION1_2026-10-07.md.

---

Ы — **the signed long-free sectors collapse exactly, and their quadrature error is paid on the full original carrier. The actual Schur sign remains open.** The test also produces a stronger negative result than a failed estimate: **the complete remaining compensated measure has square-root-scale total variation**, uniformly over the useful cutoff family. That refutes the absolute-mass version of this supplier—not the signed Schur target.

The attachment’s **SHA-256 matches**.

:chatgpt-content-reference{index="8"}[Complete PAPER verdict, proofs, machine-readable ledger, and next directive](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q01_2026-10-07.md)

The original complex carrier, actual \(J_r\), continuous compensator, and prime-power accounting remain unchanged. The starting consumer is precisely the supplied Q10 pairing, not a recomputed Schur complement. :chatgpt-content-reference{index="0"}

## 1. The signed long-free sectors collapse before any absolute values

**[FINITE_CELL | PAPER]**

Keep
\[
L=\log m,\qquad U=\lceil L\rceil,\qquad
X=\frac mU,\qquad z=\lceil X^{1/3}\rceil.
\]
Here \(X\) is the upper bound for the factor \(b\), not the historical endpoint-strip parameter.

Introduce a **free-factor cutoff**
\[
\boxed{V_0=\frac Xz,\qquad V_0\le V\le X.}
\]
On every sufficiently late original cell,
\[
V\ge z,\qquad V^2\ge X.
\]
This cutoff does not change the accepted zero cutoff \(T=mL^2\).

On odd positive integers, define
\[
N_V(n)=1_{n\le V},\qquad \ell_V(n)=1_{n\le V}\log n.
\]
The complete **all-free-short coefficient** is
\[
\boxed{
\beta_V
=
3\mu_z*\ell_V
-3\mu_z^{*2}*N_V*\ell_V
+\mu_z^{*3}*N_V^{*2}*\ell_V.
}
\]
Thus every Möbius-weighted sector remains, with the original coefficients \(3,-3,1\). The supplied Heath–Brown identity is exact throughout \(b\le X\). :chatgpt-content-reference{index="1"}

The new signed identity is
\[
\boxed{
\Lambda(b)-\beta_V(b)
=
\log b
\sum_{\substack{d\mid b\\b/d>V}}\mu(d),
\qquad b\le X,\quad b\ \mathrm{odd}.
}
\tag{1}
\]

### Why the cancellation is exact

There can be at most one free factor \(w>V\). Its cofactor \(q=b/w\) satisfies
\[
q<X/V\le z.
\]
Consequently, every Möbius cutoff is inactive on the cofactor, and every other free factor is automatically at most \(V\).

When the logarithmic factor is long, the cofactor convolution is
\[
\mu^{*j}*1^{*(j-1)}=\mu.
\]
Summing \(3,-3,1\) gives \(\mu(q)\log w\).

When a nonlogarithmic factor is long, there are \(j-1\) choices. Its cofactor convolution is
\[
\mu^{*j}*1^{*(j-2)}*\log
=\mu*\Lambda=-\mu\log.
\]
Since
\[
-3(2-1)+1(3-1)=-1,
\]
these terms contribute **\(+\mu(q)\log q\)**. The total is therefore
\[
\mu(q)\bigl(\log w+\log q\bigr)=\mu(q)\log b.
\]

The \(\log q\) term is essential. An exact integer-coefficient control, representing logarithms by prime-valuation vectors, checked **83,500 coefficient comparisons** at \(X=1000,z=10,V=100\). All passed. Deliberately deleting \(\log q\) produced **188 failures**. These are finite controls; the convolution argument supplies the general identity.

## 2. The free integer/log-factor quadrature is paid with all product cutoffs

**[FINITE_CELL | PAPER]**

Use the unchanged \(F_{v,f}\) from Q10. Define the signed quadrature discrepancy
\[
\begin{aligned}
\mathcal Q_V(v,f)
=
\sum_{\substack{d\le X/V\\d\ \mathrm{odd}}}\mu(d)
\bigg[
&\sum_{\substack{w>V,\ w\ \mathrm{odd}\\dw\le X}}
\log(dw)F_{v,f}(dw)\\
&-\frac12\int_V^{X/d}\log(dw)F_{v,f}(dw)\,dw
\bigg].
\end{aligned}
\tag{2}
\]
The density \(1/2\) is explicit. Every original restriction inside \(F\), including the separate \(a\)- and product cutoffs, remains.

Let \(\sigma_{Q,V}\) be its real signed source measure, and put
\[
h_U=\sum_{d\le U}\frac1d,\qquad
\Omega=\frac{2\pi m}{L}.
\]
Then
\[
\boxed{
\begin{aligned}
\sup_{\substack{|t|\le\Omega\\Y_0\le y\le m}}
\left|\int_{[Y_0,y]}x^{-it}\,d\sigma_{Q,V}(x)\right|
\le{}&
4096h_U(1+L)^2\sqrt m\\
&\times
\left[
\frac{4(\Omega^{1/6}+1)}{\sqrt V}
+\frac7{V^{1/4}}
\right].
\end{aligned}}
\tag{3}
\]

The proof uses the accepted odd-lattice quadrature, including its endpoint conventions and low-frequency case. :chatgpt-content-reference{index="2"}

For fixed \(a,d\), a dyadic free-factor box \(R\le w<2R\) is clipped to
\[
[R,2R)\cap(V,\infty)
\cap[Y_0/(ad),\,y/(ad)].
\]
This is one interval. Partial summation against \(\log(dw)\) costs at most \(2L\); it does **not** differentiate \(F\) or discard a product-cutoff trace.

The remaining coefficient mass is paid by
\[
\sum_{d\le B}d^{-1/2}\le2\sqrt B,
\qquad
\int_{U<a<A_0}\frac{|d\rho_U(a)|}{a}
\le2h_U(1+L).
\]
The second inequality includes both the atomic divisor flux and the continuous \(A_U\,da\) term. Summing the dyadic boxes gives (3).

The accepted **primitive-to-matrix map**—the diagonal plus discrete-Hilbert commutator generated by the same signed primitive—then gives
\[
\boxed{
\|C[\sigma_{Q,V}]\|
\le E_V,
}
\]
where
\[
\boxed{
E_V=
16384h_U(1+L)^2\sqrt m
\left[
\frac{4(\Omega^{1/6}+1)}{\sqrt V}
+\frac7{V^{1/4}}
\right].
}
\tag{4}
\]
This pays all original carrier cross modes, not just diagonal observations. :chatgpt-content-reference{index="3"}

### Parameter choice

**[COFINAL_FAMILY | PAPER]**

Take the smallest cutoff in the exact-collapse range:
\[
\boxed{V=V_0=X/z.}
\]
It removes the largest long-free sector available to this particular collapse. Since \(V_0\asymp X^{2/3}\),
\[
\boxed{
E_{V_0}
\le 2\cdot10^6h_U\,m^{1/3}L^{13/6}
}
\tag{5}
\]
eventually.

For \(V=X^\theta\), \(2/3\le\theta<1\), the two polynomial exponents in (4) are
\[
\frac23-\frac\theta2,
\qquad
\frac12-\frac\theta4.
\]
They agree at \(\theta=2/3\). Increasing \(V\) lowers the quadrature cost but leaves more arithmetic in the residual.

**This does not improve the full error exponent:** the existing \(\Delta_{10}\) remains in the calculation. Its recorded \(m^{5/12}\)-scale component budget is not a bottom floor. :chatgpt-content-reference{index="4"}

## 3. The complete residual retains the compensator and every Möbius sector

**[FINITE_CELL | PAPER]**

Define the finite harmonic Möbius sum
\[
A_<(s)=\sum_{\substack{d<s\\d\ \mathrm{odd}}}\frac{\mu(d)}d.
\]
Only arguments at most \(z\) occur below.

The remaining pairing is exactly
\[
\boxed{
\begin{aligned}
\mathcal B_V(v,f)
={}&
\sum_{\substack{U<b\le X\\b\ \mathrm{odd}}}
(\beta_V(b)-2)F_{v,f}(b)\\
&+\frac12\int_U^X
\log b\,A_<(b/V)F_{v,f}(b)\,db
+\mathcal D(v,f).
\end{aligned}}
\tag{6}
\]
Therefore
\[
\boxed{\mathcal R_*(v,f)=\mathcal B_V(v,f)+\mathcal Q_V(v,f).}
\tag{7}
\]

The **\(-2\) odd sum remains discrete**. The old \(\mathcal D\) remains present. These are precisely the terms required by the supplied parity return. :chatgpt-content-reference{index="5"}

In the original product variable \(x\), the updated continuous density is
\[
\boxed{
\Gamma_V(x)
=
\widetilde D_U(x)
+
\frac{x^{-1/2}}2
\int_{\substack{U<a<A_0\\a<x/V}}
\frac{\log(x/a)}a
A_<\!\left(\frac{x}{aV}\right)d\rho_U(a).
}
\tag{8}
\]
This follows from \(x=ab\), including the Jacobian \(db=dx/a\). Strictness in \(A_<\) records \(w>V\). No sign or smallness of \(\Gamma_V\) is assumed.

Let \(\tau_V\) denote this complete residual measure. Thus
\[
\mathcal B_V(v,f)=\langle v,C[\tau_V]f\rangle,
\qquad
\sigma_*=\tau_V+\sigma_{Q,V}.
\]

There is also an exact **two-factor evaluation** of the all-free-short coefficient:
\[
\boxed{
\beta_V(b)
=
\sum_{\substack{du=b\\u\le V}}\mu(d)\log u
-
\sum_{\substack{du=b\\u>V}}\mu(d)\log d.
}
\tag{9}
\]
It follows by inserting \(\Lambda=\mu*\log\) into (1).

The first Möbius variable can now be as large as \(X/u\). It is **not truncated at \(z\)**. In the second sum, \(d<X/V\le z\) automatically. This is the explicit remaining Möbius-weighted sector—not an unweighted free-factor sum masquerading as one.

## 4. The all-free-short aggregate has a source-specific obstruction

**[COFINAL_FAMILY | PAPER]**

The following calculation combines **all Heath–Brown sectors and all allowed original \(a\)-divisors**. It is not the earlier individual-tuple obstruction.

Set
\[
R_0=\frac{\sqrt X}{16}
\]
and choose distinct odd primes
\[
U<\ell\le2U,\qquad
R_0<p\le2R_0,\qquad
4R_0<q\le8R_0.
\]
Put
\[
n=\ell pq.
\]

On every sufficiently late original cell,
\[
\frac m{64}<n\le\frac m8,
\qquad p,q>z,
\]
and the only divisors of \(n\) satisfying \(U<a<A_0\) are
\[
a=\ell,\ p,\ q.
\]
Indeed, the products \(\ell p,\ell q,pq\) exceed \(A_0\), while
\[
\ell p,\ell q<V_0\le V.
\]
Each permitted \(a\) is a prime greater than \(U\), so
\[
\alpha_U(\ell)=\alpha_U(p)=\alpha_U(q)=-1.
\]

Equation (1) now gives
\[
\beta_V(pq)=-\log(pq)\,1_{pq>V},
\qquad
\beta_V(\ell p)=\beta_V(\ell q)=0.
\]
Consequently,
\[
\boxed{
\tau_V(\{\ell pq\})
=
\frac{6+\log(pq)\,1_{pq>V}}{\sqrt{\ell pq}}>0.
}
\tag{10}
\]

The constant \(6\) comes from the three retained \(-2\) contributions. The continuous part of \(d\rho_U\) and the exact density \(\Gamma_V(x)\,dx\) are nonatomic in \(x\), so neither cancels this atom.

There is an additional exact return check:
\[
\sigma_{Q,V}(\{\ell pq\})
=
-\frac{\log(pq)\,1_{pq>V}}{\sqrt{\ell pq}},
\qquad
\sigma_*(\{\ell pq\})=\frac6{\sqrt{\ell pq}}.
\]
Thus the larger atom created by the split has not been confused with the previous residual—or with the complete original Weil measure, whose other components remain in \(F_{10}\).

### These atoms rule out a whole class of absolute certificates

An elementary central-binomial-coefficient argument gives
\[
\#\{p:R<p\le2R\}\ge\frac{R}{8\log R}
\]
for sufficiently large real \(R\). The complete proof is in the verdict; no RH or prime-pair estimate is used.

The three prime intervals therefore produce at least
\[
\frac{m}{32768L^2\log U}
\]
distinct products \(n=\ell pq\). Summing their positive atom masses proves
\[
\boxed{
\|\tau_V\|_{\mathrm{TV}}
\ge
2^{-16}\frac{\sqrt m}{L^2\log U},
\qquad
V_0\le V\le X.
}
\tag{11}
\]
Here **total variation** is the absolute mass of the complete signed measure, including its continuous part.

For \(V\le X/128\), including the selected \(V_0\) eventually, every chosen \(pq\) exceeds \(V\), yielding the stronger estimate
\[
\boxed{
\|\tau_V\|_{\mathrm{TV}}
\ge
2^{-16}\frac{\sqrt m}{L\log U}.
}
\tag{12}
\]

This is an actual lower bound for the residual’s total variation, not merely a large upper estimate.

For any fixed \(C>0\), \(\eta<1/2\), and any cutoff selection \(V(m)\in[V_0,X]\),
\[
\boxed{
Cm^\eta-\|\tau_{V(m)}\|_{\mathrm{TV}}
\le
Cm^\eta-
2^{-16}\frac{\sqrt m}{L^2\log U}
<0
}
\tag{13}
\]
eventually.

**Theorem-shape kill:** subpolynomial total-variation control of this complete residual is false throughout the stated cutoff family.

**Not killed:** cancellation against the actual carrier kernel, a one-sided signed pairing estimate, the Schur target, or SP. Atom indicators are not being substituted for actual exceptional vectors. A large total variation does not establish a large compressed operator norm.

That distinction is the narrow reason the absolute version of this attempted supplier stops.

## 5. The full Schur transfer remains intact

**[FINITE_CELL | PAPER]**

Define
\[
F_V=F_{10}-C[\sigma_{Q,V}],
\qquad
\Delta_V=\Delta_{10}+E_V.
\]
Then
\[
\boxed{
\mathsf H_m(r)=rI-C[\tau_V]+F_V,
\qquad
\|F_V\|\le\Delta_V.
}
\tag{14}
\]

Keep the actual spaces and blocks:
\[
\mathcal R=\ker B,\qquad
\mathcal E=\mathcal R^\perp,
\qquad
f=J_rv=v+y,\qquad
y=-A_r^{-1}B_rv.
\]
They are not recomputed for the new decomposition. These are the supplied repaired source objects. :chatgpt-content-reference{index="6"}

The actual regular equation becomes
\[
\boxed{
P_{\mathcal R}C[\tau_V]f
=
ry+P_{\mathcal R}F_Vf.
}
\tag{15}
\]

The Schur form is exactly
\[
\langle v,\mathfrak S_m(r)v\rangle
=
r\|v\|^2-\Re\mathcal B_V(v,J_rv)
+\Re\langle v,F_VJ_rv\rangle.
\]
Writing
\[
s_V(v)=r\|v\|^2-\Re\mathcal B_V(v,J_rv),
\]
the faithful **discriminator** is
\[
\boxed{
\begin{aligned}
s_V(v)-\Delta_V\|v\|\,\|J_rv\|
&\le \langle v,\mathfrak S_m(r)v\rangle\\
&\le s_V(v)+\Delta_V\|v\|\,\|J_rv\|.
\end{aligned}}
\tag{16}
\]

A nonnegative lower envelope for every exceptional vector certifies the cell. A negative upper endpoint for an actual exceptional vector certifies a negative Schur direction. A straddling interval certifies neither.

**No bound on \(\|J_r\|\) has been assumed.** The full \(B_r^*A_r^{-1}B_r\) correction is present.

For comparison, the available fully absolute estimate is
\[
\|\tau_V\|_{\mathrm{TV}}
\le32h_U(1+L)^3\sqrt m,
\]
including the discrete flux and both continuous densities. Combined with (16), it is weaker than the accepted whole-source estimate. More importantly, (11) proves that **a better total-variation argument cannot repair its exponent**.

The missing estimate is still the sign and size of the explicit aggregate (6) on \((v,J_rv)\). Equation (15) does not, by itself, estimate its exceptional pairing.

## 6. The next supplier should attack the signed two-factor product

The surviving coefficient is now computable without six independently majorized variables.

Define finite **Mellin polynomials**
\[
M_X(s)=\sum_{\substack{d\le X\\d\ \mathrm{odd}}}\mu(d)d^{-s},
\qquad
N_W(s)=\sum_{\substack{u\le W\\u\ \mathrm{odd}}}u^{-s}.
\]
Equation (9) says that the coefficients through \(b\le X\) are exactly those of
\[
\boxed{
-M_X(s)N_V'(s)
+
M_X'(s)\bigl(N_X(s)-N_V(s)\bigr).
}
\tag{17}
\]

**First candidate: retain this complete signed product through the hyperbolic cutoff.** Its algebraic cost is low, and it directly tests whether cancellation survives in the carrier’s divided differences although it fails in total variation. The original \(a\)-measure and compensator must enter before taking norms. Replacing \(M_X\) by \(1/\zeta\), assuming a zero-free strip, or turning a mean-value bound into uniform carrier control would not supply the missing estimate.

**Second candidate: an exact Poisson–Mellin transform of the free \(u\)-sum in (9).** Keep the Möbius coefficient outside the transform and retain the odd-lattice aliases and endpoints. This has greater boundary-analysis cost; its decisive risk is that the Möbius-weighted arithmetic persists unchanged in the dual ratio phase. No generic unit-amplitude estimate pays that coefficient.

The first candidate is the next selected supplier. The second is a genuinely different representation, not a license to repeat absolute sector bounds.

**Closeout:** the signed long-free cofactor cancellation and full-carrier quadrature are proved here; the triple-prime forecast is confirmed by the complete residual atom calculation. The total-variation supplier is refuted in its precise scope. **The actual signed Schur estimate, SP, G1/G3, and RH remain open.** These are **PAPER derivations**, not yet an independent audit or a Lean-checked result.
