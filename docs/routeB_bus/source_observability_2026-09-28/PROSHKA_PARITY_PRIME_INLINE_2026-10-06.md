# Growth answer10 — exact inline capture

Chat `6ac54396-d878-83eb-ae29-35d2bdd2262b`; question `2dbe9556-ff59-4978-a7f7-0481e80bf4ea`.
Answer `94600296-a768-4be8-8ec6-64e5e0ef3fd4`; untruncated read_thread capture 2026-10-06 23:43 UTC. Pending audit.
This chat has used all ten question slots; no new sends here.

---

Ы — **the parity-centered test stalls at a weighted even-shift aggregate. It does not give a new full bottom bound.** I can, however, pay the return from the two-wheel to the **original continuous compensator**, and remove the powers of two with an explicit original-norm error. After those corrections, the surviving arithmetic term and the precise limitation of the additive estimate are clear.

**[COFINAL_FAMILY | PAPER]** On every sufficiently late original cell, the wheel correction costs
\[
O\!\left(m^{5/12}L^{5/6}\log(2L)\right),
\]
and the powers-of-two correction costs
\[
24h_U\sqrt{A_0/U},
\qquad
h_U=\sum_{d\le U}\frac1d,\quad
U=\lceil L\rceil,\quad A_0=\lceil\sqrt m\rceil.
\]
These bounds hold on the **whole original complex carrier**. They apply to the actual \(J_rv\), with its norm and Schur correction retained.

The remaining even-shift expression contains the prime–prime term, **both linear subtractions**, the residue-class baseline, and the mixed continuous terms. The proved parity information gives no power saving for that expression.

:chatgpt-content-reference{index="2"}[Complete PAPER verdict and same-phase handoff](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q10.md)

## 1. An exact parity split of the surviving source

**[FINITE_CELL | PAPER]**

Retain
\[
Y_0=A_0=\lceil\sqrt m\rceil,\qquad
\Omega=\frac{2\pi m}{L},
\]
and the accepted centered divisor measure
\[
d\rho_U(a)
=
\sum_{n>U}\alpha_U(n)\delta_n(da)+A_U\,da,
\qquad
\rho_U(U)=0,\qquad |\rho_U|\le U.
\]
The surviving measure is
\[
\begin{aligned}
\int G\,d\sigma_{\rm rem}
={}&
\sum_{b>U}\frac{\Lambda(b)}{\sqrt b}
\int_{\substack{U<a<A_0\\Y_0\le ab\le m}}
a^{-1/2}G(ab)\,d\rho_U(a)\\
&+\int_{Y_0}^mD_U(x)G(x)\,dx,
\end{aligned}
\tag{1}
\]
where
\[
D_U(x)=
[A_U(\log x-\psi_1(x/U))-B_U-1]x^{-1/2}+x^{-3/2}.
\tag{2}
\]

Use the exact decomposition
\[
\boxed{
\Lambda(n)=e_o(n)+w_2(n)+p_2(n),
}
\tag{3}
\]
with
\[
e_o(n)=1_{n\ {\rm odd}}(\Lambda(n)-2),\qquad
w_2(n)=2\,1_{n\ {\rm odd}},\qquad
p_2(n)=(\log2)1_{n=2^j,\ j\ge1}.
\]

All odd prime powers remain in \(e_o\). The powers of two will be **bounded, not dropped**.

Replacing the discrete wheel by its Lebesgue mean adds the exact density
\[
x^{-1/2}M_U(x),\qquad
M_U(x)=
\int_{\substack{U<a<A_0\\a<x/U}}\frac{d\rho_U(a)}a.
\]
Thus define
\[
\boxed{
\widetilde D_U(x)=D_U(x)+x^{-1/2}M_U(x).
}
\tag{4}
\]
This is an almost-everywhere density identity; the strict endpoints retain the product restrictions. Integration by parts against \(1/a\) gives
\[
|M_U(x)|\le1.
\]
**It gives no smallness or sign for \(\widetilde D_U\).**

Let \(\sigma_*\) be (1) with \(\Lambda\) replaced by \(e_o\) and \(D_U\) replaced by \(\widetilde D_U\). Then
\[
\boxed{
\sigma_{\rm rem}
=\sigma_*+\sigma_{\rm wheel}+\sigma_2,
}
\tag{5}
\]
where \(\sigma_{\rm wheel}\) uses
\[
d\kappa_2(b)=
\sum_{n>U}w_2(n)\delta_n(db)-1_{b>U}\,db
\]
in the inner \(b\)-variable, and \(\sigma_2\) uses \(p_2\).

This is the exact return to the original continuous source. No assertion that \(\Lambda-w_2\) is small has entered.

## 2. The wheel correction is paid in the original carrier norm

**[FINITE_CELL | PAPER]**

The needed quadrature estimate is: for \(B\ge64\), every interval \(I\subset[B,2B]\), either endpoint convention, and every real \(t\),
\[
\boxed{
\left|
2\sum_{\substack{n\in I\\n\ {\rm odd}}}n^{-1/2-it}
-\int_Ix^{-1/2-it}\,dx
\right|
\le1024\bigl(|t|^{1/6}+B^{1/4}+1\bigr).
}
\tag{6}
\]
For \(|t|\le B/4\), the sharper bound \(64/\sqrt B\) holds.

Here is the estimate, including its shift choice. Write \(n=2j+1\). At low frequency, Euler summation on this shifted lattice and the accepted sawtooth argument bound the **sum-minus-integral** before partial summation. The nonzero Fourier modes have phase derivative bounded below by \(5|k|\); their integrated bounds are summable. This covers \(t=0\) and all clipped intervals.

At higher frequency, an additive shift of \(k\) in \(j\) produces the phase
\[
t\log\frac{n+2k}{n}.
\]
In the \(j\)-coordinate, its normalized second derivative lies between
\[
\lambda=\frac{|t|k}{\pi B^3},
\qquad
\Lambda=\frac{8|t|k}{\pi B^3}.
\]
The progression interval has length at most \(B/2\). Arias de Reyna’s Lemma 5 therefore bounds its exponential sum by
\[
2+8\sqrt{\frac{|t|k}{B}}
+16\frac{B^{3/2}}{\sqrt{|t|k}}.
\]
The real \(C^2\) phase, positive-curvature bounds and interval-length hypothesis are exactly those of the lemma; short intervals and endpoint changes are counted directly. :chatgpt-content-reference{index="0"}

Finite shift averaging gives
\[
|S_{\rm odd}|^2
\le
\frac{2B^2}{K}+8B
+32\sqrt{B|t|K}
+128\frac{B^{5/2}}{\sqrt{|t|K}}.
\tag{7}
\]
For \(|t|\ge16B\), choose
\[
K_*=\max\!\left(B|t|^{-1/3},\frac{B^2}{|t|}\right).
\]
When \(K_*\ge2\), take \(K=\lfloor K_*\rfloor\). Then \(K\le B/8\), \(K\ge K_*/2\), and
\[
|S_{\rm odd}|^2
\le36B|t|^{1/3}+214B^{3/2}+8B.
\]
When \(K_*<2\), the trivial bound already fits (6). In the intervening range \(B/4<|t|<16B\), the direct second-derivative estimate suffices. Partial summation and the continuous integral complete (6).

### Sum the correction over the actual short factor

Divisor expansion gives
\[
\int_{U<a<A_0}a^{-1/2}|d\rho_U(a)|
\le4h_U\sqrt{A_0},
\]
\[
\int_{U<a<A_0}a^{-3/4}|d\rho_U(a)|
\le8h_UA_0^{1/4}.
\tag{8}
\]
For each \(a\), split the \(b\)-range dyadically. There are at most \(2L\) boxes, and their fourth roots sum to at most \(7(m/a)^{1/4}\). All product cutoffs are covered by (6). Therefore
\[
\sup_{\substack{|t|\le\Omega\\y\le m}}
\left|
\int_{[Y_0,y]}x^{-it}\,d\sigma_{\rm wheel}(x)
\right|
\le M_{\rm wheel},
\tag{9}
\]
where
\[
\boxed{
M_{\rm wheel}
=
8192Lh_U\sqrt{A_0}(\Omega^{1/6}+1)
+57344h_Um^{1/4}A_0^{1/4}.
}
\tag{10}
\]

Apply the accepted exact primitive-to-\((d,h)\) matrix map:
\[
\boxed{
\|C[\sigma_{\rm wheel}]\|\le4M_{\rm wheel}.
}
\tag{11}
\]
This pays **all cross-frequency terms**, not just diagonal observations.

For the powers of two,
\[
\sum_{2^j>U}\frac{\log2}{\sqrt{2^j}}<\frac3{\sqrt U}.
\]
Together with (8), this proves
\[
\boxed{
\|C[\sigma_2]\|
\le\Pi_m:=24h_U\sqrt{A_0/U}.
}
\tag{12}
\]

The atom at \(ab=m\) remains in these estimates; its compressed action is zero because \(S_L=0\). Included and excluded dyadic endpoints are handled with the appropriate right or left traces. No derivative of a cutoff endpoint profile is used.

## 3. The actual corrected-vector weight

**[FINITE_CELL | PAPER]**

From this point onward, let
\[
f=J_rv
\]
be the unchanged actual Schur-corrected vector. Define
\[
\mathcal K_{v,f}(h)=
\int_0^h
\left[
\overline{v(L-u)}f(h-u)
+\overline{v(h-u)}f(L-u)
\right]du,
\]
and
\[
\boxed{
F_{v,f}(b)=
b^{-1/2}
\int_{\substack{U<a<A_0\\Y_0\le ab\le m}}
a^{-1/2}\mathcal K_{v,f}(L-\log(ab))\,d\rho_U(a).
}
\tag{13}
\]
Also put
\[
\mathcal D(v,f)=
\int_{Y_0}^m
\widetilde D_U(x)\mathcal K_{v,f}(L-\log x)\,dx.
\]

The remaining scalar is exactly
\[
\boxed{
\mathcal R_*(v,f)
=\langle v,C[\sigma_*]f\rangle
=\sum_{n>U}e_o(n)F_{v,f}(n)+\mathcal D(v,f).
}
\tag{14}
\]

The endpoint restrictions in \(F\) still come from \(v,J_rv\). They have not become independent variables. Since all remaining shifts have length at least \(L/2\),
\[
|\mathcal K_{v,f}(h)|\le\|v\|\,\|f\|.
\]
Consequently,
\[
\boxed{
|F_{v,f}(b)|
\le
4h_U
\sqrt{\frac{\min(A_0,m/b)}b}\,
\|v\|\,\|f\|.
}
\tag{15}
\]
This bound retains the product support. I make no smoothness assertion for \(F\) across product cutoffs.

## 4. Execute additive differencing after the mandatory centering

**[FINITE_CELL | PAPER]**

Partition the integer \(b\)-range into dyadic boxes \(I_\ell=[B_\ell,2B_\ell)\), with exact clipping at the first and last cutoffs. Write
\[
z_n=e_o(n)F_{v,f}(n),\qquad
S_\ell=\sum_{n\in I_\ell}z_n,\qquad
E_\ell=\sum_{n\in I_\ell}|z_n|^2.
\]

Every odd-shift correlation is now **exactly zero**, even with these complex weights and sharp cutoffs: one factor has even argument. The powers-of-two exceptions were paid in (12).

Index the odd integers of a box consecutively, padding missing endpoints with zeros. If its length is \(N_\ell\le B_\ell/2+1\), then for every \(1\le H\le N_\ell\),
\[
\boxed{
|S_\ell|^2
\le
\frac{N_\ell+H-1}{H}
\left[
E_\ell+
2\sum_{k=1}^{H-1}(1-k/H)\Re C_{\ell,2k}
\right].
}
\tag{16}
\]

The surviving correlation is
\[
\boxed{
\begin{aligned}
C_{\ell,2k}
={}&
\sum_{\substack{n,n+2k\in I_\ell\\n\ {\rm odd}}}
\bigl[
\Lambda(n)\Lambda(n+2k)
-2\Lambda(n)-2\Lambda(n+2k)+4
\bigr]\\
&\hspace{25mm}\cdot
F_{v,f}(n+2k)\overline{F_{v,f}(n)}.
\end{aligned}
}
\tag{17}
\]

The constant \(4\) is the exact two-wheel even-shift baseline. An upper bound for the positive \(\Lambda\Lambda\) term does **not** bound this centered signed expression.

Moreover, the weight in (17) contains the complete double integral
\[
\begin{aligned}
\frac1{\sqrt{n(n+2k)}}\iint
&\frac{
\mathcal K_{v,f}(L-\log(a(n+2k)))
\overline{\mathcal K_{v,f}(L-\log(a'n))}
}{\sqrt{aa'}}\\
&\hspace{20mm}d\rho_U(a)\,d\rho_U(a'),
\end{aligned}
\tag{18}
\]
with both separate product constraints. Thus the short-factor correlations and all carrier cross terms remain. No identification of \(a\) with \(a'\) has been made.

### Both continuous mixed terms remain

The full residual square is
\[
\boxed{
\begin{aligned}
|\mathcal R_*|^2
={}&|\mathcal D|^2
+2\Re\!\left(\overline{\mathcal D}\sum_\ell S_\ell\right)
+\sum_\ell|S_\ell|^2\\
&+2\Re\sum_{\ell<j}S_\ell\overline{S_j}.
\end{aligned}
}
\tag{19}
\]
The second term comprises **both mixed continuous terms**. The first is the continuous–continuous term. Equation (4) records their return to the original \(D_U\).

Accordingly, the exact upper aggregate produced by this attempt is
\[
\begin{aligned}
\mathcal A_{\boldsymbol H}(v,f)
={}&|\mathcal D|^2
+2\Re\!\left(\overline{\mathcal D}\sum_\ell S_\ell\right)
+2\Re\sum_{\ell<j}S_\ell\overline{S_j}\\
&+\sum_\ell
\frac{N_\ell+H_\ell-1}{H_\ell}
\left[
E_\ell+
2\sum_{k=1}^{H_\ell-1}(1-k/H_\ell)\Re C_{\ell,2k}
\right].
\end{aligned}
\tag{20}
\]
We have proved
\[
|\mathcal R_*|^2\le\mathcal A_{\boldsymbol H}(v,f).
\]
**We have not proved that this signed aggregate is small.**

The wheel and powers-of-two errors are carried linearly through (11)–(12), not silently discarded inside this square.

## 5. The optimized parity-only envelope gives no power saving

**[FINITE_CELL | PAPER]**

Using only the currently available estimate
\[
|C_{\ell,2k}|\le E_\ell
\]
in (16) gives
\[
|S_\ell|^2\le(N_\ell+H-1)E_\ell.
\]
Therefore
\[
\boxed{
\inf_{1\le H\le N_\ell}(N_\ell+H-1)E_\ell
=N_\ell E_\ell.
}
\tag{21}
\]

The optimized shift range, with these inputs, is \(H=1\): **no nonzero shift**. This is a proved limitation of the derived envelope, not a lower bound for the actual source sum.

Its original-norm scale is explicit. Put
\[
M=\|v\|\,\|J_rv\|,
\qquad
A_\ell=\min(A_0,m/B_\ell).
\]
From (15), the actual number of odd indices, and \(|\Lambda(n)-2|\le2L\),
\[
E_\ell\le64h_U^2L^2A_\ell M^2,
\]
so
\[
|S_\ell|\le8h_UL\sqrt{B_\ell A_\ell}\,M.
\]
Summing the dyadic boxes gives
\[
\boxed{
\left|\sum_\ell S_\ell\right|
\le32h_UL^2\sqrt m\,\|v\|\,\|J_rv\|.
}
\tag{22}
\]
For \(B_\ell\ge m/A_0\), the envelope has
\[
\sqrt{B_\ell A_\ell}=\sqrt m.
\]
The remaining endpoint strip contains such ranges.

For comparison, elementary absolute estimates in (4) give
\[
|\mathcal D(v,J_rv)|
\le10h_UL^2\sqrt m\,\|v\|\,\|J_rv\|.
\]
Thus the fully absolute fallback from this attempted differencing is
\[
42h_UL^2\sqrt m\,\|v\|\,\|J_rv\|,
\]
which is **weaker than the already accepted whole-source bound**.

This identifies the narrow stall. The negative odd-shift term of the uncentered coefficient \(\Lambda-1\) belongs to the periodic component \(w_2-1\). Its Fejér average vanishes at even averaging lengths. After that component has been returned correctly to the continuous source, it is unavailable as an additional negative contribution to (17).

The unestimated information is now the sign and magnitude of **weighted even-prime correlations together with their mixed terms**, not the parity identity.

## 6. Return through the actual regular equation

**[FINITE_CELL | PAPER]**

Set
\[
C_*=C[\sigma_*],\qquad
F_{10}=F_9-C[\sigma_{\rm wheel}]-C[\sigma_2],
\]
and
\[
\boxed{
\Delta_{10}
=\Delta_9+4M_{\rm wheel}+\Pi_m.
}
\tag{23}
\]
Then
\[
\boxed{
\mathsf H_m(r)=rI-C_*+F_{10},
\qquad
\|F_{10}\|\le\Delta_{10}.
}
\tag{24}
\]
Including the accepted \(\Delta_9\), this remains an
\[
O\!\left(m^{5/12}L^{3/2}\log(2L)\right)
\]
**component-error budget**, not a bottom floor.

Keep the unchanged repaired spaces and actual blocks:
\[
\mathcal R=\ker B,\qquad
\mathcal E=\mathcal R^\perp,\qquad
f=J_rv=v+y,\qquad
y=-A_r^{-1}B_rv,\qquad r>\epsilon_m.
\]
The regular equation now reads
\[
\boxed{
P_{\mathcal R}C_*f=ry+P_{\mathcal R}F_{10}f,
\qquad
\|P_{\mathcal R}C_*f-ry\|\le\Delta_{10}\|f\|.
}
\tag{25}
\]

Since \(\langle y,\mathsf H_m(r)f\rangle=0\),
\[
\boxed{
\langle v,\mathfrak S_m(r)v\rangle
=
r\|v\|^2-\Re\mathcal R_*(v,J_rv)
+\Re\langle v,F_{10}J_rv\rangle.
}
\tag{26}
\]
Hence, with
\[
M_r(v)=r\|v\|^2-\Re\mathcal R_*(v,J_rv),
\]
the available discriminator is
\[
\boxed{
\begin{aligned}
M_r(v)-\Delta_{10}\|v\|\,\|J_rv\|
&\le \langle v,\mathfrak S_m(r)v\rangle\\
&\le M_r(v)+\Delta_{10}\|v\|\,\|J_rv\|.
\end{aligned}
}
\tag{27}
\]

The complete \(B_r^*A_r^{-1}B_r\) correction is present through \(J_r\). No bound on \(\|J_r\|\) is presumed.

The regular equation constrains the **linear projection of \(C_*f\)**. It has not supplied an estimate for the quadratic, even-shift aggregate (17)–(20). That is the first unsupplied source estimate in this construction.

A negative upper endpoint in (27) certifies an actual negative Schur direction on that cell. A nonnegative lower envelope for every exceptional vector certifies the cell. A straddling interval does neither. The squared route (20) remains optional; a direct real-part estimate in (26) could be weaker and sufficient.

## Same-phase handoff and next own attempt

**Proved and retained:** the full \(m^{1/2-o(1)}\) floor; the polylogarithmic floor outside codimension \(O(m/L^5)\); the repaired small complete high-zero tail; the Type-I estimate; and the centered long-\(\alpha_U\) component estimate. This answer adds only the explicitly paid wheel correction (11) and powers-of-two correction (12). **No new full fixed exponent or common good subsequence has been obtained.**

**Killed versus stalled:** the earlier norm-transfer, jet-majorant and blind-packet certificates remain killed only in their recorded scopes. The fixed-inner exceptional transfer is RH-strength and stalled, not an unconditional source counterexample. The present parity-centered signed test is **stalled, not killed**: its optimized proved envelope is (21), and the weighted even-shift aggregate remains unestimated. SP, G1/G3 and RH remain open.

The next own attempt should avoid asking for a shifted-prime asymptotic. There is an exact **linear** alternative before squaring. Let
\[
z=\left\lceil(m/U)^{1/3}\right\rceil,\qquad
\mu_z(n)=\mu_{\rm M}(n)1_{n\le z}.
\]
For Dirichlet convolution, put
\[
D_z=\varepsilon-\mu_z*1.
\]
Because \(D_z(n)=0\) for \(n\le z\), its third convolution power vanishes for \(n\le z^3\). Multiplying
\[
\varepsilon-D_z^{*3}
=
3(\varepsilon-D_z)
-3(\varepsilon-D_z)^{*2}
+(\varepsilon-D_z)^{*3}
\]
by \(\Lambda\), and using \(1*\Lambda=\log\), proves for **every required \(b\le m/U\)**
\[
\boxed{
\Lambda(b)
=
3(\mu_z*\log)(b)
-3(\mu_z^{*2}*1*\log)(b)
+(\mu_z^{*3}*1^{*2}*\log)(b).
}
\tag{28}
\]
There is no truncation remainder in that range.

**Next own mathematical attempt:** insert (28) into the linear residual (14), before prime-variable differencing, and test the unrestricted integer/logarithmic-factor sectors with their signed Möbius coefficients retained. Keep the odd support, \(F_{v,J_rv}\), the exact compensator (4), and every sector without a usable long factor explicit. This replaces the unestimated shifted-prime-pair input by a concrete finite convolution problem; it does not assert that the resulting sectors are already controlled.
