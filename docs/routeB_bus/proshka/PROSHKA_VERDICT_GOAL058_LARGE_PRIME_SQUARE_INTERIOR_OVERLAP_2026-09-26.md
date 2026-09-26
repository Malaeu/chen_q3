# PAPER VERDICT — OPEN_INTERIOR_SQUARE

```yaml
REQUEST_ID: REQ-2026-09-26-LARGE-PRIME-SQUARE-INTERIOR-OVERLAP
BOUNDARY_ID: GOAL058_SELECTED_FERRERS_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP
SOURCE_COMMIT: 2eda2829d7c9edea40369cf494eee28ef70b9cac
OUTCOME: OPEN_INTERIOR_SQUARE
SCOPE: COFINAL_FAMILY
VERIFIER: PAPER
INTERIOR_SQUARE_SAVING: NOT_ESTABLISHED
UNBOUNDED_SELECTED_LEADING_WITNESS: NOT_ESTABLISHED
NEW_PAID_CONTRIBUTION: JOINT_Q5_Q6_ENDPOINT_DEPENDENCE
NEW_BOUND: ABS_ENDPOINT_CORRECTION_LT_6_E11_FOR_m_GE_65536
REFINED_BOUND: ENDPOINT_CORRECTION_IS_o_E11
NEW_PAPER_DERIVATION_INDEPENDENTLY_AUDITED: false
HONESTY_STATE: CHALLENGER_NOT_RH
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

**Neither requested quantifier for \(V_m\) is established.** There is, however, a further paid reduction: the **joint contribution of every term involving the exact Q5/Q6 endpoint coefficient** has an explicit bound
\[
|R_{\varepsilon,m}|\le r_\varepsilon(m)E_{11}<6E_{11},
\qquad m\ge65536,
\qquad r_\varepsilon(m)\longrightarrow0.
\]

The endpoint coefficient is retained in an exact identity, not set to zero. The first remaining comparison is the endpoint-independent coefficient of the same source-indexed four-term expression. Both mixed terms, the literal diagonal, all source indices, and the moving inverse-dilation boundary remain.

## 1. Source lock and scope

The authoritative TXT was read in full: 6,136 bytes, 116 LF, with locally computed SHA-256
```text
7d64210b75199c2f421ac06289b2d646cbd22a6a9119dc1d38ffaf665f71f064
```
I read the complete predecessor at the pinned commit, through its final directive, and the requested limited audit of answer no. 10. The connector returned predecessor Git blob
```text
5fe2c05e457a6494284c8c3ce6f995c716d0cca1
```
The pinned audit records the stipulated predecessor SHA-256
```text
e248537c6ba25cc8dd628769093ed8e3c39112b9a29571234932d50b2b35b220
```
That remote SHA-256 is audit-reported, not independently recomputed here. The audit accepts the predecessor’s exterior, shoulder, and remainder estimates at their stated scopes; its correction of the eventual inequality is a wording correction, not another estimate.  

Fix the same \(P\), with
\[
m=J_P+j+2,\qquad m\ge2^{16},
\]
on the admitted selected family. Throughout,
\[
L=\log m,\quad b=L/2,\quad Q=\sqrt m,\quad X_2=m^{1/4},
\quad \omega_n=2\pi n/L,
\]
and
\[
g=G'',\qquad h=T_mg,\qquad f=h-g,\qquad
E=E_{11}=\|f\|_2^2>0.
\]
The source, original \(5m\) splice, carrier, and coefficient identity are those fixed in the request. In particular,
\[
e_n=-\omega_n^2b_n+\varepsilon_m,
\qquad
\varepsilon_m=\frac{2G'(b)}{\sqrt L}.
\]
The functions \(f\) and \(h\) are real and even. :chatgpt-content-reference{index="2"}

Write
\[
\mathcal P_m=\{p\text{ prime}:L<p\le X_2\},\qquad
t_p=2\log p,\quad a_p=b-t_p,\quad w_p=\frac{\log p}{p}.
\]
The sole target remains
\[
V_m=4\sum_{p\in\mathcal P_m}w_p
       \int_0^{a_p}f(u)f(u+t_p)\,du.
\tag{1}
\]
The admitted transfer is
\[
U_m^{(2)}
=V_m+U_{m,\mathrm{small}}^{(2)}
  +X_{m,\mathrm{large}}-L_{m,\mathrm{large}}^{(2)},
\qquad
|U_m^{(2)}-V_m|\le12(1+\log L)E.
\tag{2}
\]
In particular, the low-frequency term has the **minus sign**. :chatgpt-content-reference{index="3"}

## 2. The complete indexed expression and its endpoint decomposition

For clarity, define
\[
s_n=\tfrac12-i\omega_n,\qquad
J(\kappa,a)=\int_0^a e^{i\kappa u}\,du,\qquad J(0,a)=a,
\]
and
\[
\mathcal H_2(s;A,B)=\int_A^B h_2(x)x^{s-1}\,dx,
\]
where
\[
h_2(x)=(-64v^4+448v^3-660v^2+150v)e^{-v},
\qquad v=\pi x^2.
\]

For either of the two coefficient vectors used below, denote the predecessor’s four terms by
\[
\begin{aligned}
\widetilde T_{0,p}[c]
={}&\frac1{Lp}\operatorname{Re}
 \sum_{n,q=-m}^{m}
 \overline{c_n}c_q(-1)^{q-n}
 e^{i\omega_qt_p}J(\omega_q-\omega_n,a_p),\\
\widetilde T_{1,p}[c]
={}&\frac1{\sqrt L}\operatorname{Re}
 \sum_{n=-m}^{m}\sum_{r\ge1}
 \overline{c_n}(-1)^n(rp^2)^{-s_n}
 \mathcal H_2(s_n;rp^2,rQ),\\
\widetilde T_{2,p}[c]
={}&\frac1{\sqrt L}\operatorname{Re}
 \sum_{n=-m}^{m}\sum_{r\ge1}
 \overline{c_n}(-1)^n(p^2)^{s_n-1}r^{-s_n}
 \mathcal H_2(s_n;r,rQ/p^2),\\
\widetilde T_{3,p}
={}&\sum_{r,s\ge1}
 \int_1^{Q/p^2}h_2(rx)h_2(sp^2x)\,dx.
\end{aligned}
\tag{3}
\]
Thus, with
\[
\mathcal W_m[c]
=4\sum_{p\in\mathcal P_m}(\log p)
 \bigl[\widetilde T_{0,p}[c]-\widetilde T_{1,p}[c]
       -\widetilde T_{2,p}[c]+\widetilde T_{3,p}\bigr],
\tag{4}
\]
the actual requested scalar is \(V_m=\mathcal W_m[e]\). These are the predecessor’s indexed terms, including both different Mellin upper boundaries. 

The self diagonal is literally
\[
\bigl(\widetilde T_{0,p}[c]\bigr)_{n=q}
=\frac{a_p}{Lp}\sum_{n=-m}^{m}|c_n|^2\cos(\omega_nt_p).
\tag{5}
\]
No off-diagonal term is discarded.

Now make the exact coefficient decomposition
\[
\alpha_n=-\omega_n^2b_n,\qquad e_n=\alpha_n+\varepsilon_m,
\]
and define the endpoint synthesis
\[
d(u)=\varepsilon_m\sum_{n=-m}^{m}\psi_{n,L}(u).
\tag{6}
\]
Inside the window, this gives the algebraic remainder \(f-d\). No projection orthogonality or changed normalization is asserted for that remainder.

Set
\[
V_m^{[0]}=\mathcal W_m[\alpha]
=4\sum_{p\in\mathcal P_m}w_p
 \int_0^{a_p}(f-d)(u)(f-d)(u+t_p)\,du.
\tag{7}
\]
Then
\[
\boxed{
\begin{aligned}
V_m&=V_m^{[0]}+R_{\varepsilon,m},\\
R_{\varepsilon,m}
&=4\sum_{p\in\mathcal P_m}w_p\int_0^{a_p}
 \bigl[d(u)f(u+t_p)+f(u)d(u+t_p)-d(u)d(u+t_p)\bigr]\,du.
\end{aligned}}
\tag{8}
\]

The minus sign on the last term is necessary: (8) is written using the actual \(f\), not \(f-d\).

At the indexed level, (8) retains the joint sum of all endpoint-dependent terms arising from
\[
\overline e_ne_q
=\overline\alpha_n\alpha_q
+\varepsilon_m\overline\alpha_n
+\varepsilon_m\alpha_q+\varepsilon_m^2,
\]
and from the \(\varepsilon_m\) term in **each** mixed sum. No claim is made that these indexed pieces are individually small.

## 3. New PAPER estimate: the entire endpoint correction is paid

### 3.1. Normalize the endpoint amplitude using only the exterior source

Put
\[
B=G'(b),\qquad F(u)=-g(u)\quad(u\ge b),\qquad
E_O=2\int_b^\infty F(u)^2\,du\le E.
\]
The admitted source input is
\[
F(u)>0,\qquad F(u+s)\le e^{-\pi ms}F(u),
\qquad u\ge b,\ s\ge0.
\tag{9}
\]
Its domain is exterior. The predecessor and audit explicitly preserve that restriction.  

The source gives \(G'(\infty)=0\), hence
\[
B=\int_b^\infty F(u)\,du>0.
\]
Consequently,
\[
\begin{aligned}
B^2
&=2\int_b^\infty F(u)\int_u^\infty F(v)\,dv\,du\\
&\le\frac2{\pi m}\int_b^\infty F(u)^2\,du
=\frac{E_O}{\pi m}.
\end{aligned}
\]
Therefore
\[
\boxed{B^2\le\frac{E}{\pi m}.}
\tag{10}
\]

This is the only use of exterior decay in the new argument. It bounds a scalar endpoint amplitude; it does not assert interior decay of \(g\) or \(f\).

By orthonormality of the original carrier,
\[
\|d\|_2^2
=(2m+1)\varepsilon_m^2
=\frac{4(2m+1)B^2}{L}
<\frac{3E}{L}.
\tag{11}
\]
Since \(d\) is even,
\[
\|d_+\|_2^2<\frac{3E}{2L}.
\tag{12}
\]

### 3.2. The endpoint synthesis has an explicit interior profile

Let
\[
D_m(\theta)=\sum_{n=-m}^{m}e^{in\theta}.
\]
For \(0\le z\le b\),
\[
d(b-z)=\frac{2B}{L}D_m(2\pi z/L).
\]
Using the finite geometric sum and
\(\sin(\pi z/L)\ge2z/L\) on this interval gives
\[
|d(b-z)|
\le \min\left\{\frac{2(2m+1)B}{L},\,\frac Bz\right\}.
\]
Define
\[
\eta_m=\frac{L}{2(2m+1)}.
\]
Then
\[
\boxed{|d(b-z)|\le\frac{B}{\max\{\eta_m,z\}},
\qquad 0\le z\le b.}
\tag{13}
\]

For the unshifted endpoint factor in (8), \(u\le a_p\) implies \(b-u\ge t_p\). Thus
\[
\int_0^{a_p}|d(u)|^2\,du
\le B^2\int_{t_p}^{b}\frac{dz}{z^2}
\le\frac{B^2}{t_p}.
\tag{14}
\]

The other orientation requires a different estimate: \(d(u+t_p)\) can be large near the moving endpoint \(u=a_p\).

### 3.3. A Gram bound for the moving, one-sided endpoint profiles

Define
\[
v_p(u)=\mathbf1_{[0,a_p]}(u)d(u+t_p),\qquad u\ge0.
\tag{15}
\]
These are **interior endpoint Dirichlet profiles**, not the predecessor’s exterior theta profiles and not translates of the full error.

Their diagonal norms satisfy
\[
\|v_p\|_2^2\le\|d_+\|_2^2
=\frac{2(2m+1)B^2}{L}.
\tag{16}
\]

For \(p<q\), put
\[
\delta=t_q-t_p=a_p-a_q>0.
\]
On the common support, use \(z=a_q-u\). Formula (13) gives
\[
|\langle v_p,v_q\rangle|
\le B^2\int_0^\infty
 \frac{dz}{\max(\eta_m,z)\max(\eta_m,z+\delta)}.
\]
Splitting at \(z=\eta_m\) proves
\[
\boxed{
|\langle v_p,v_q\rangle|
\le\frac{B^2}{\delta}
 \left[1+\log\left(1+\frac{\delta}{\eta_m}\right)\right].
}
\tag{17}
\]
Indeed, the first part is at most \(B^2/\delta\), and the second is
\[
\frac{B^2}{\delta}\log(1+\delta/\eta_m).
\]

Since \(\delta\le b\), the bracket in (17) is at most
\[
K_m=1+\log(2m+2).
\]
Enumerate the prime bases increasingly as \(p_1,\ldots,p_s\). Integer spacing gives
\[
t_{p_j}-t_{p_i}
=2\int_{p_i}^{p_j}\frac{dx}{x}
\ge\frac{2(j-i)}{X_2}.
\tag{18}
\]
Also \(s\le X_2\). Hence every absolute Gram row sum is at most \(B^2R_m\), where
\[
R_m=
\frac{2(2m+1)}{L}
+X_2K_m(1+L/4).
\tag{19}
\]
The elementary inequality \(2|c_ic_j|\le |c_i|^2+|c_j|^2\) now yields
\[
\left\|\sum_pc_pv_p\right\|_2^2
\le B^2R_m\sum_p|c_p|^2.
\tag{20}
\]

Here the constants can be made uniform on the requested tail without a numerical search. For \(m\ge2^{16}\),
\[
L\ge8,\qquad
\frac{L^3}{m^{3/4}}\le1,\qquad
K_m\le2L,\qquad
1+L/4\le3L/8.
\]
The ratio \(L^3/m^{3/4}\) decreases once \(L>4\), and its value at \(m=2^{16}\) is \((\log2)^3<1\). Therefore
\[
\frac{R_m}{m}
\le\frac{4+2/m+3/4}{L}
<\frac5L.
\]
Combining this with (10) proves the uniform estimate
\[
\boxed{
\left\|\sum_pc_pv_p\right\|_2^2
\le\frac{2E}{L}\sum_p|c_p|^2,
\qquad m\ge2^{16}.
}
\tag{21}
\]

This is the load-bearing new step. A triangle inequality over the translated endpoint profiles would lose the squared-weight summation and would not give the bound below.

### 3.4. Bound the three terms of the exact correction

The predecessor’s elementary weight bounds give
\[
W_m:=\sum_{p\in\mathcal P_m}w_p
\le L/2+2\log2\le L,
\qquad
\sum_{p\in\mathcal P_m}w_p^2<5.
\tag{22}
\]
Only these upper bounds are used; no prime-distribution or multiplier-sign assertion is imported. 

Because \(t_p>2\log L\), equations (10), (14), and
\(\|f_+\|_2^2=E/2\) give
\[
\begin{aligned}
\left|4\sum_pw_p\int_0^{a_p}d(u)f(u+t_p)\,du\right|
&\le4B\sqrt{E/2}\sum_p\frac{w_p}{\sqrt{t_p}}\\
&\le \frac{2L}{\sqrt{\pi m\log L}}E.
\end{aligned}
\tag{23}
\]

For the opposite orientation, apply (21) to \(c_p=w_p\):
\[
\begin{aligned}
\left|4\sum_pw_p\int_0^{a_p}f(u)d(u+t_p)\,du\right|
&=4\left|\left\langle f_+,\sum_pw_pv_p\right\rangle\right|\\
&\le4\sqrt{\frac5L}\,E.
\end{aligned}
\tag{24}
\]

Finally, (12) and (21) give
\[
\left|4\sum_pw_p\int_0^{a_p}d(u)d(u+t_p)\,du\right|
\le\frac{4\sqrt{15}}{L}E.
\tag{25}
\]

Thus the exact correction in (8) satisfies
\[
\boxed{
|R_{\varepsilon,m}|\le r_\varepsilon(m)E,
\qquad
r_\varepsilon(m)=
\frac{2L}{\sqrt{\pi m\log L}}
+4\sqrt{\frac5L}
+\frac{4\sqrt{15}}L.
}
\tag{26}
\]
Every term tends to zero.

For an explicit uniform constant, \(L^2/m\) decreases on this tail and is less than \(1/256\) at its start. Consequently the three terms in (26) are respectively less than
\[
\frac18,\qquad \frac72,\qquad 2.
\]
Therefore
\[
\boxed{
|V_m-V_m^{[0]}|<6E_{11}
\quad\text{for every admitted selected }m\ge65536,
\qquad
\frac{|V_m-V_m^{[0]}|}{E_{11}}\longrightarrow0.
}
\tag{27}
\]

At \(p^2=Q\), \(a_p=0\), so its contributions to (1), (7), and (8) are zero. This does **not** remove the predecessor’s exterior strips: those remain in (2).

## 4. The first unpaid source-indexed signed comparison

After (27), the unpaid scalar is explicitly
\[
\boxed{
V_m^{[0]}
=
4\sum_{p\in\mathcal P_m}(\log p)
\left[
\widetilde T_{0,p}[\alpha]+\widetilde T_{3,p}
-\widetilde T_{1,p}[\alpha]-\widetilde T_{2,p}[\alpha]
\right],
\qquad
\alpha_n=-\omega_n^2b_n.
}
\tag{28}
\]

What is missing is a source-derived comparison between
\[
4\sum_p(\log p)
  \bigl[\widetilde T_{0,p}[\alpha]+\widetilde T_{3,p}\bigr]
\quad\text{and}\quad
4\sum_p(\log p)
  \bigl[\widetilde T_{1,p}[\alpha]+\widetilde T_{2,p}[\alpha]\bigr]
\]
at the **actual \(E_{11}\) scale**, with their signs retained.

For example, the retained self diagonal is
\[
\frac{a_p}{Lp}
\sum_{n=-m}^{m}\omega_n^4|b_n|^2\cos(\omega_nt_p).
\tag{29}
\]
It has no supplied sign. The independent \(n\ne q\) terms remain equally part of (28).

The inverse-dilation restriction is also unchanged. Define
\[
H_\alpha(y)=y^{-1/2}
 \sum_{n=-m}^{m}\alpha_n\psi_{n,L}(\log y),
\qquad
F_+(x)=\sum_{r\ge1}h_2(rx).
\]
Then the reverse mixed sum retains the form
\[
\int_1^Q H_\alpha(y)
 \sum_{\substack{L<p\le X_2\\p\ {\rm prime}\\p^2\le y}}
 \frac{\log p}{p^2}F_+(y/p^2)\,dy.
\tag{30}
\]
The condition \(p^2\le y\) has not been flattened, and no restricted square-divisor weight has been replaced by \(\log k\). These are explicit source requirements. :chatgpt-content-reference{index="8"}

### Why the admitted bounds do not decide either quantifier

The direct norm bound still gives only
\[
|V_m|
\le2E\sum_{p\in\mathcal P_m}w_p
\le(L+4\log2)E.
\tag{31}
\]
Its ratio to \((1+\log L)E\) is unbounded. It therefore does not supply a finite eventual saving constant.

Projection orthogonality applies on the complete original window. It does not annihilate the restricted translated products in (28). Likewise, the predecessor’s pointwise Fourier estimate and paid shoulder do not control the remaining high-frequency source-weighted moment.

Most importantly, **(21) is not a Gram estimate for translated copies of \(f\) or \(f-d\)**. It is proved from the explicit Dirichlet profile of the one scalar endpoint synthesis. Extending it to the remaining error would be an unsupported step.

Finally, an upper bound supplies no leading lower witness. The positive arithmetic weights multiply signed correlations, and neither an eventual sign nor an explicitly proved unbounded selected-index set has been obtained.

Thus (27) pays an actual source contribution, but (28) still has neither requested upper nor lower estimate.

## 5. One strictly narrower falsifiable PAPER test

### `TEST_SOURCE_INTERIOR_SQUARE_CORE_AFTER_PAID_ENDPOINT`

Test only the signed expression (28), using all four indexed terms (3), with \(\alpha_n=-\omega_n^2b_n\), the original prime-square range and moving boundaries, and the **original**
\[
E_{11}=\|T_mg-g\|_2^2
\]
as denominator.

The required delivery is either an explicit finite \(C_0\) and selected threshold \(m_0\) proving
\[
|V_m^{[0]}|\le C_0(1+\log L)E_{11}
\quad\text{for every admitted selected }m\ge m_0,
\tag{32}
\]
or a proved \(c_0>0\) and explicitly proved unbounded selected-index set on which
\[
|V_m^{[0]}|\ge c_0\ell_mE_{11}.
\tag{33}
\]

This is narrower by a proved contribution, not merely by notation: the **joint sum of all \(\varepsilon_m\)-linear and \(\varepsilon_m^2\) terms** has already been bounded in (26). Those terms remain in the exact correction (8); they no longer require a source-signed estimate at either target scale.

The transfer is fully paid:
\[
\boxed{
U_m^{(2)}
=V_m^{[0]}+R_{\varepsilon,m}
+U_{m,\mathrm{small}}^{(2)}
+X_{m,\mathrm{large}}-L_{m,\mathrm{large}}^{(2)}.
}
\tag{34}
\]
Hence
\[
|U_m^{(2)}-V_m^{[0]}|
\le\bigl[12(1+\log L)+r_\varepsilon(m)\bigr]E.
\tag{35}
\]

A proof of (32) would give, on the common selected tail,
\[
C_{\mathrm{int}}=C_0+6,\qquad C_2=C_0+18.
\tag{36}
\]

A proof of (33) would give the exact lower transfers
\[
|V_m|\ge[c_0\ell_m-r_\varepsilon(m)]E,
\tag{37}
\]
and
\[
|U_m^{(2)}|
\ge[c_0\ell_m-r_\varepsilon(m)-12(1+\log L)]E.
\tag{38}
\]
Only after restricting to the tail where
\[
r_\varepsilon(m)+12(1+\log L)
\le \tfrac12c_0\ell_m
\tag{39}
\]
could one conclude
\[
|U_m^{(2)}|\ge\tfrac12c_0\ell_mE.
\]
The eventual inequality is **\(\le\)**. It follows conditionally because
\((1+\log L)/\ell_m\to0\); it does not manufacture the unbounded set required in (33).

## 6. Closeout

**Closed on PAPER in this review:** the entire joint Q5/Q6 endpoint-dependent contribution to the actual interior overlap has the explicit uniform bound (27), and the stronger vanishing relative bound (26).

**Not closed:** the signed cancellation (28), a saving for \(V_m\), or a leading witness on an unbounded selected set. No theorem shape has been killed.

Even a successful square result would leave the exponent-one prime block and possible prime/square cancellation at the whole-head level separate. Opposite-side correlation, integrated symbol deviation, transfer, the actual \(J_m\) sign, first \(\tau_j\) sign, Schur-floor, and RH remain open. :chatgpt-content-reference{index="9"}

## CODEX DIRECTIVE

**Perform only `TEST_SOURCE_INTERIOR_SQUARE_CORE_AFTER_PAID_ENDPOINT`, on PAPER, for (28) with the complete indexed terms (3).** First check the new endpoint estimate (10)–(27); accept it only at its proved scope, namely the joint endpoint-dependent correction (8). Then seek (32) or the genuinely unbounded selected-source witness (33), always relative to the original \(E_{11}\). Retain both mixed terms, independent \(n,q\), the literal diagonal, every \(r,s\ge1\), \(p^2\le Q\), and the moving \(p^2\le y\) boundary. Keep the endpoint correction in the exact transfer (34), with the low-frequency subtraction negative. Do not transplant the endpoint-profile Gram estimate to the remaining error. No mathematical runtime, numerical cutoff search, Lean, repository write, new seed, source/carrier/\(Q\) replacement, route promotion, or RH claim.