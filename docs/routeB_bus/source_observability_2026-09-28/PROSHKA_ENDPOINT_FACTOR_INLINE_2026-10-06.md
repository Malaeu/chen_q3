# Proshka endpoint factor — exact answer2

Chat Proof of CCM Growth, 6ac54396-d878-83eb-ae29-35d2bdd2262b.
Assistant item e36cfb18-b5a2-4c3d-b55a-7b8b3d0f1012. Complete inline answer read 2026-10-06 19:44 UTC.
Question2 is in CAUSAL_DRESSING_AUDIT_2026-10-06.md.
Linked supplement is not yet retrieved; all checked claims must use the inline text below or separately verified sources.

## Exact answer

Ы — **SP remains OPEN.** I proved a **cofinal obstruction to removing the factor \(I-R\) from the finite-window polar estimate**. Unlike the earlier \(A\)-undressing obstruction, this concerns a **signed double-commutator form**, not a norm comparison alone.

The obstruction occurs on the original two-mode vector
\[
p_m(x)=\sqrt{\frac2L}\sin\frac{2\pi x}{L}
      =\frac{e_1-e_{-1}}{i\sqrt2}.
\]
The omitted factor produces a positive signed contribution of order
\[
\frac{\sqrt m}{(\log m)^3},
\]
whereas
\[
D_{\rm arch}(p_m)\le \frac{72\pi^2}{(\log m)^2}.
\]
It fails on **every sufficiently late original cell**, so a good subsequence cannot rescue this particular mechanism.

**This is not a lower bound for \(\langle p_m,Dp_m\rangle-D_{\rm arch}(p_m)\).** The remaining arithmetic term can cancel that contribution, and estimating precisely that cancellation remains necessary.

:chatgpt-content-reference{index="2"}[Complete PAPER verdict, including the machine-readable header and claim ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q02.md)

## 1. The precise mechanism being tested

**[FINITE_CELL | PAPER]**

Keep the actual operators on \(\mathcal H_L=L^2(0,L)\):
\[
Z=\sum_{n\le m}\frac1{\sqrt n}S_{\log n},
\qquad
B=I-R,
\qquad
F=BZ.
\]

Take the **polar decompositions on the full \(\mathcal H_L\)**, before restricting forms to the original carrier:
\[
F=VM,\qquad Y_F=V^*XV,
\]
\[
Z=UN,\qquad Y_Z=U^*XU.
\]
Thus \(D=\mathfrak D_F\), where
\[
\mathfrak D_F
=MY_FM^{-1}+M^{-1}Y_FM-2Y_F,
\]
and define the comparison object
\[
\mathfrak D_Z
=NY_ZN^{-1}+N^{-1}Y_ZN-2Y_Z.
\]

Here \(\mathfrak D_Z\) is **only a diagnostic comparison**, not a replacement matrix or terminal consumer. Both polar unitaries are defined because the source operators are invertible for each finite \(L\). No uniform inverse bound is used.

The concrete temptation is that the elementary factor
\[
b(z)=\frac{z-\frac12}{z+\frac12}
\]
has modulus one on the imaginary axis. One might therefore try to remove it when estimating the integer operator and then restore it with a subpolynomial signed error.

The exact transfer shape I tested is:
\[
\boxed{
\langle f,\mathfrak D_Ff\rangle
\le
\langle f,\mathfrak D_Zf\rangle
+a_0D_{\rm arch}(f)
+Cm^\eta\|f\|_2^2
\quad\text{for all }f\in\mathcal V_m,
}
\tag{T}
\]
on arbitrarily large original cells, with fixed \(a_0,C\ge0\).

**For every \(0<\eta<\tfrac12\), (T) is false.**

The source identification remains CCM Proposition 3.2 with \(\lambda=\sqrt m\); its equation (3.19) contains the full pole term and von Mangoldt prime-power sum. No fixed-window lower-bound theorem is promoted to a growing-window estimate. :chatgpt-content-reference{index="0"}

## 2. The finite-endpoint defect is exactly rank one—and not negligible

**[FINITE_CELL | PAPER]**

Put
\[
u_L(x)=e^{(x-L)/2},
\qquad H=R+R^*.
\]
Direct integration over the **complete finite interval** gives
\[
\begin{aligned}
(R^*R)(x,y)
&=\int_{\max(x,y)}^L
 e^{-(t-x)/2}e^{-(t-y)/2}\,dt\\
&=e^{-|x-y|/2}-e^{(x+y)/2-L}.
\end{aligned}
\]
Consequently,
\[
\boxed{
B^*B=I-u_L\otimes u_L,
\qquad
\|u_L\|^2=1-m^{-1}.
}
\tag{1}
\]

For the actual source \(F=BZ\), this becomes
\[
\boxed{
F^*F=Z^*Z-v_L\otimes v_L,
\qquad v_L=Z^*u_L,
}
\tag{2}
\]
with the explicit integer-counting vector
\[
v_L(x)
=e^{(x-L)/2}\lfloor e^{L-x}\rfloor
\quad\text{a.e.}
\tag{3}
\]

Thus the boundary correction really is rank one. The mistake would be to infer that its effect on the signed polar expression is small.

A collateral check already shows substantial cancellation on the actual constant carrier mode. Let
\[
S(y)=\sum_{n\le y}n^{-1/2}.
\]
Then
\[
Ze_0(x)=L^{-1/2}S(e^x),
\]
whereas
\[
Fe_0(x)
=L^{-1/2}
\left(2e^{-x/2}\lfloor e^x\rfloor-S(e^x)\right).
\]
Elementary integral comparisons give
\[
\left|
\frac{2\lfloor y\rfloor}{\sqrt y}-S(y)
\right|\le2,
\qquad
S(y)\ge\sqrt{y/2}.
\]
Therefore
\[
\boxed{
\|Fe_0\|^2\le4,
\qquad
\|Ze_0\|^2\ge\frac{m-1}{2L},
\qquad
\frac{\|Fe_0\|^2}{\|Ze_0\|^2}
\le\frac{8L}{m-1}.
}
\tag{4}
\]

This rules out subpolynomial lower **Gram comparisons** between \(F\) and \(Z\) on the original carrier. It does **not** show polynomial growth of \(\|F^{-1}\|\): the large denominator in (4) is \(\|Ze_0\|\), not \(\|e_0\|\).

The signed obstruction below does not rely on that Gram comparison.

## 3. An exact signed envelope without any inverse-norm estimate

**[FINITE_CELL | PAPER]**

For an invertible operator \(T=U_T|T|\), direct multiplication gives
\[
T^{-1}[X,T]+\bigl(T^{-1}[X,T]\bigr)^*
=
\mathfrak D_T+2(Y_T-X).
\tag{5}
\]

For the actual integer source,
\[
Z^{-1}[X,Z]
=\mathcal P
=\sum_{2\le n\le m}
  \frac{\Lambda(n)}{\sqrt n}S_{\log n}.
\]
The coefficient identity is
\[
\sum_{d\mid n}\mu(d)\log(n/d)=\Lambda(n),
\]
so **all prime powers are retained**.

The accepted unsmoothed identity gives
\[
F^{-1}[X,F]=\mathcal P-R_++R.
\]
Writing
\[
H_+=R_++R_+^*,
\]
and subtracting the two instances of (5), we get
\[
\boxed{
\mathfrak D_F-\mathfrak D_Z
=H-H_+-2(Y_F-Y_Z).
}
\tag{6}
\]

Because both polar factors are unitary,
\[
0\le Y_F,Y_Z\le LI.
\]
Hence we have the following genuine two-sided **form envelope** on the full \(\mathcal H_L\):
\[
\boxed{
H-H_+-2LI
\ \preceq\
\mathfrak D_F-\mathfrak D_Z
\ \preceq\
H-H_++2LI.
}
\tag{7}
\]

Here \(\preceq\) means inequality of quadratic forms.

The arithmetic operators cancel **in this diagnostic difference**, not in the target. Equation (7) lets us test the finite-window factor-removal mechanism without knowing either polar unitary explicitly.

## 4. Exact response on the original two-mode sine

**[COFINAL_FAMILY | PAPER]**

Set
\[
k=\frac{2\pi}{L},\qquad
d=\frac14+k^2,
\qquad
p_m(x)=\sqrt{\frac2L}\sin(kx).
\]
This is a normalized vector of the original \(\mathcal V_m\), involving only \(n=\pm1\). Its being real and reflection-odd is a property of a witness, **not a restriction of the target carrier**.

For real \(\alpha\), define
\[
R_\alpha=\int_0^L e^{\alpha s}S_s\,ds.
\]
The finite-window integral is explicitly
\[
(R_\alpha p_m)(x)
=
\sqrt{\frac2L}\,
\frac{
-\alpha\sin(kx)-k\cos(kx)+ke^{\alpha x}
}{
\alpha^2+k^2
}.
\tag{8}
\]
The \(ke^{\alpha x}\) term is the boundary response. In particular, it cannot be discarded at the right endpoint.

Integrating (8) against \(p_m\), using \(kL=2\pi\), gives
\[
\boxed{
\langle p_m,(R_\alpha+R_\alpha^*)p_m\rangle
=
-\frac{2\alpha}{\alpha^2+k^2}
+\frac{4k^2(1-e^{\alpha L})}
 {L(\alpha^2+k^2)^2}.
}
\tag{9}
\]

Subtract the cases \(\alpha=-\tfrac12\) and \(\alpha=\tfrac12\):
\[
\boxed{
\langle p_m,(H-H_+)p_m\rangle
=
\frac2d+\frac{8k^2}{Ld^2}\sinh(L/2)
=:b_L.
}
\tag{10}
\]
Therefore (7) implies
\[
\boxed{
\langle p_m,(\mathfrak D_F-\mathfrak D_Z)p_m\rangle
\ge b_L-2L.
}
\tag{11}
\]

The leading coefficient is explicit:
\[
b_L\sim256\pi^2\frac{\sqrt m}{L^3}.
\]

For a nonasymptotic lower envelope, take \(L\ge4\pi\). Then \(d\le\tfrac12\) and
\[
\sinh(L/2)\ge\frac14e^{L/2}.
\]
Thus
\[
\boxed{
\langle p_m,(\mathfrak D_F-\mathfrak D_Z)p_m\rangle
\ge
32\pi^2\frac{\sqrt m}{L^3}-2L.
}
\tag{12}
\]

This is a **signed lower bound for the actual polar-commutator difference**, not a bound inferred from poor conditioning.

## 5. The archimedean cost is too small to repair this comparison

**[COFINAL_FAMILY | PAPER]**

Both endpoint values of \(p_m\) vanish. Its zero extension therefore belongs to \(H^1(\mathbb R)\), and
\[
\|p_m'\|_2^2=k^2.
\]
For every \(s\ge0\),
\[
\|\tau_sp_m-p_m\|_2^2\le s^2k^2.
\]
This estimate includes shifts beyond the support. No endpoint value jump has been omitted.

Since
\[
\frac1{1-e^{-2s}}
=
1+\frac1{e^{2s}-1}
\le1+\frac1{2s},
\]
we obtain
\[
\begin{aligned}
\int_0^\infty s^2J(s)\,ds
&\le
\int_0^\infty(s^2+s/2)e^{-s/2}\,ds\\
&=16+2=18.
\end{aligned}
\]
Hence
\[
\boxed{
D_{\rm arch}(p_m)
\le18k^2
=\frac{72\pi^2}{L^2}.
}
\tag{13}
\]

Now evaluate the proposed comparison margin:
\[
a_0D_{\rm arch}(p_m)+Cm^\eta
-\langle p_m,(\mathfrak D_F-\mathfrak D_Z)p_m\rangle.
\]
For \(\log m\ge4\pi\), equations (12)–(13) give the **upper envelope**
\[
\boxed{
U_m(a_0,C,\eta)
=
\frac{72a_0\pi^2}{(\log m)^2}
+Cm^\eta+2\log m
-\frac{32\pi^2\sqrt m}{(\log m)^3}.
}
\tag{14}
\]

For every fixed \(a_0,C\ge0\) and \(0<\eta<\tfrac12\),
\[
U_m(a_0,C,\eta)<0
\]
for every sufficiently large \(m\).

Thus the exact quantifier statement is
\[
\boxed{
\begin{gathered}
\forall a_0,C\ge0\;\forall\eta\in(0,\tfrac12)\;
\exists M\;\forall\text{ original }m\ge M:\\
\langle p_m,\mathfrak D_Fp_m\rangle
>
\langle p_m,\mathfrak D_Zp_m\rangle
+a_0D_{\rm arch}(p_m)+Cm^\eta.
\end{gathered}
}
\tag{15}
\]

The **negative upper envelope (14)** certifies the theorem-shape kill. It is stronger than failure along one bad subsequence: **there is no unbounded good subsequence for (T).**

The weakest immediate repair is (7): retain \(H-H_+\) exactly and then pay \(2L\). That repair is valid, but it is **not an SP supplier**.

## 6. The exact arithmetic cancellation that remains

The previous calculation does not say that \(\mathfrak D_F\) itself has a large positive form. It says that the integer contribution must cancel a large, explicitly known positive term.

For the same original witness, direct integration gives
\[
Q_{p_m}(s)
=
2\left[
\left(1-\frac{s}{L}\right)\cos(ks)
+\frac{\sin(ks)}{kL}
\right],
\qquad 0\le s\le L.
\tag{16}
\]
Define the **joint signed source residual**
\[
\boxed{
\begin{aligned}
\mathcal J_m
={}&
2\sum_{2\le n\le m}
\frac{\Lambda(n)}{\sqrt n}
\left[
\left(1-\frac{\log n}{L}\right)\cos(k\log n)
+\frac{\sin(k\log n)}{kL}
\right]\\
&+\frac2d+\frac{8k^2}{Ld^2}\sinh(L/2).
\end{aligned}
}
\tag{17}
\]

Every prime power remains in this expression. At \(n=m\), its bracket is exactly zero; that is the genuine endpoint action, not a deleted atom.

Since
\[
\langle p_m,Xp_m\rangle=L/2,
\]
the exact polar identity yields
\[
\langle p_m,\mathfrak D_Fp_m\rangle
=
\mathcal J_m+L-2\langle p_m,Y_Fp_m\rangle.
\]
Therefore
\[
\boxed{
\left|
\langle p_m,\mathfrak D_Fp_m\rangle-\mathcal J_m
\right|
\le L.
}
\tag{18}
\]

Consequently, the requested \(D\)-bound on this witness requires
\[
\boxed{
\mathcal J_m
\le
18k^2+C_\eta m^\eta+L
}
\tag{19}
\]
on any proposed good cell.

This residual also has an exact relationship to the **original full Weil form**. Namely,
\[
h_L:=\langle p_m,Hp_m\rangle
=
\frac1d+
\frac{4k^2(1-e^{-L/2})}{Ld^2},
\qquad 0\le h_L\le4,
\]
and
\[
\boxed{
W(p_m)
=
D_{\rm arch}(p_m)-c_A+2h_L-\mathcal J_m.
}
\tag{20}
\]

Thus the unsupplied estimate is genuinely arithmetic: it must control the **signed prime sum together with \(b_L\)**. Separate estimates for those two terms would lose their cancellation again.

For the full carrier, the first unsupplied inequality remains exactly
\[
\forall\eta>0\;\exists C_\eta\;
\exists\text{ unbounded original }\mathcal G_\eta:
\]
\[
\boxed{
\langle f,\mathfrak D_Ff\rangle
\le
D_{\rm arch}(f)+C_\eta m^\eta\|f\|^2
\quad
(m\in\mathcal G_\eta,\ f\in\mathcal V_m).
}
\tag{21}
\]
No common-cell good subsequence has been supplied.

**Closeout.** The registered prediction about a non-subpolynomial signed endpoint effect is confirmed. The killed object is the optional transfer (T), not (21), SP, or the route. The result excludes an actual-source finite-window factor-removal mechanism; it does not establish a bottom-vector obstruction.

**Next mathematical step:** prove or refute
\[
\forall\eta>0\;\exists C_\eta\;
\exists\text{ arbitrarily large original }m:
\qquad
\mathcal J_m\le C_\eta m^\eta
\]
for the explicit all-prime-power sum (17), **without separating it from \(b_L\)**. Equation (18) makes this a necessary low-mode source test—not permission to infer the full-carrier bound from scalar good cells.

