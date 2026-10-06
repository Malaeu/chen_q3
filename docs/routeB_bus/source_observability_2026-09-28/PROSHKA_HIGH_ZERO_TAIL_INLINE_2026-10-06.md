# Proshka growth answer 5 — exact inline capture

Chat: Proof of CCM Growth (`6ac54396-d878-83eb-ae29-35d2bdd2262b`).
User message: `3cbb23c2-0144-4ff4-8147-ee1943995419`.
Answer: `6364d8ef-221b-4d0b-8f28-7f2af0f51c6d`; completed 2026-10-06 21:14:33 UTC.
Captured via read_thread; untruncated. Claims below require audit; RH remains OPEN.

---

Ы — **the endpoint-jet majorant really does obstruct the old sufficient \(Q\)-test, and that obstruction can be removed.**

**[COFINAL_FAMILY | PAPER]** At the already selected cutoff \(T=m(\log m)^2\), the **complete signed high-zero contribution** satisfies
\[
\boxed{\|W_{>T}\|\le \frac{3\cdot10^6}{\sqrt{\log m}}.}
\]
This is an operator bound on the **entire original complex carrier**, including its endpoint action—not a bound after imposing vanishing jets.

The old jet-majorized \(Q\)-comparison nevertheless fails on every sufficiently late original cell for every fixed shift \(r=Cm^\eta\), \(0<\eta<1/2\). I give an actual carrier witness below. On that same witness, the **actual shifted target form is positive** eventually. This separates the artificial obstruction from source negativity.

The repair also proves positivity of the **endpoint-only block inside the actual previous Schur complement**, with its coupling retained. **The remaining low off-line-pair comparison, SP, and RH remain open.**

:chatgpt-content-reference{index="3"}[Complete PAPER verdict with machine-readable header and claim ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_NEGATIVE_BOTTOM_GROWTH_Q05.md)

## 1. A weighted zero count that pays magnitude, not just rank

**[COFINAL_FAMILY | PAPER]**

Write
\[
L=\log m,\qquad d=2m+1,\qquad w=\delta+i\gamma.
\]

The additional literature input is the **full Table 1** in Chourasiya–Simonič, not an extrapolation of the previously used \([.500,.625]\) display. Corollary 1 and Table 1 cover \(1/2\le\sigma\le1\), \(X\ge3\cdot10^{12}\). Taking the maxima \(46.06,9.461,167.8\), and using that the logarithmic exponent is at most \(3\), gives
\[
N(\sigma,X)
\le224X^{3(1-\sigma)/(2-\sigma)}(\log X)^3.
\tag{1}
\]
The table was checked directly. This is an unconditional density estimate, not an absence-of-zeros assumption. :chatgpt-content-reference{index="0"}

HSW Corollary 1.2 also gives, very conservatively,
\[
N(X)\le X\log X\qquad(X\ge3\cdot10^{12}).
\tag{2}
\]
Both counts include multiplicities. :chatgpt-content-reference{index="1"}

I claim that, uniformly for \(X\ge m\ge3\cdot10^{12}\),
\[
\boxed{
\mathcal N_m(X):=
\sum_{|\gamma|\le X}r_wm^{|\delta|}
\le2700X(\log X)^{5/2}.
}
\tag{3}
\]

### Proof

Put \(v=\log X\), so \(L\le v\). For \(0\le u\le1/2\),
\[
p(u):=\frac{3/2-3u}{3/2-u}\le1-\frac43u.
\]
The **layer-cake identity**—integrating the level sets of \(m^{|\delta|}\)—and the zero symmetries give
\[
\mathcal N_m(X)
\le2N(X)+4L\int_0^{1/2}e^{Lu}N(1/2+u,X)\,du.
\tag{4}
\]
Thus
\[
N(1/2+u,X)
\le
\min\!\left\{Xv,\;224Xv^3e^{-4uv/3}\right\}.
\]

Split the integral at
\[
u_0=\frac{3\log v}{2v}.
\]
The part below \(u_0\) is at most
\[
4Xv(e^{Lu_0}-1)\le4Xv^{5/2}.
\]
For the remaining part, put \(a=4v/3-L\ge v/3\). Its contribution is at most
\[
896\frac{L}{a}Xv^3e^{-au_0}
\le2688Xv^{5/2}.
\]
Adding \(2N(X)\le2Xv\) proves (3).

Partial summation now yields
\[
\boxed{
\sum_{|\gamma|>T}\frac{r_wm^{|\delta|}}{\gamma^2}
\le10800\frac{(\log T)^{5/2}}{T},
\qquad T\ge m.
}
\tag{5}
\]
Indeed, the lower boundary term has the favorable sign, and
\[
\int_T^\infty\frac{(\log u)^{5/2}}{u^2}\,du
\le2\frac{(\log T)^{5/2}}T
\]
for \(\log T\ge5\).

**The change from the previous tail estimate is the weight \(m^{|\delta|}\).** It is summed using the density theorem before being replaced by its worst value \(\sqrt m\).

## 2. The entire high-zero operator is small

**[FINITE_CELL | PAPER]**

On the original centered carrier, retain the exact rows
\[
a_{w,j}:=M_{\psi_j}(w)
=\frac{2\sinh(wL/2)}{\sqrt L\,(w+i\omega_j)},
\qquad
\omega_j=\frac{2\pi j}{L}.
\tag{6}
\]
The numerator contains **both finite endpoints**. I use the already accepted extension of the signed zero formula to this carrier; no new \(H^1\) zero-extension assumption is made.

Set
\[
\Omega=\frac{2\pi m}{L}.
\]
For \(|\gamma|>T\ge2\Omega\),
\[
|2\sinh(wL/2)|^2\le4m^{|\delta|},
\qquad
|w+i\omega_j|\ge|\gamma|/2.
\]
Therefore
\[
\boxed{
\|a_w\|_2^2
\le\frac{16d}{L}\frac{m^{|\delta|}}{\gamma^2}.
}
\tag{7}
\]

The dimension \(d=2m+1\) has not disappeared. It is paid explicitly.

Define the positive high-zero **evaluation Gram matrix**
\[
\mathcal R_{>T}:=\sum_{|\gamma|>T}r_wa_w^*a_w.
\]
Equations (5)–(7) give
\[
\boxed{
\operatorname{tr}\mathcal R_{>T}
\le172800\frac dL\frac{(\log T)^{5/2}}T
=:\tau(m,T).
}
\tag{8}
\]

For each off-line pair,
\[
\left|2\Re\!\left(M_f(w)\overline{M_f(w^\dagger)}\right)\right|
\le |M_f(w)|^2+|M_f(w^\dagger)|^2.
\]
Critical-line rows are positive. Consequently the **complete signed tail** obeys
\[
-\mathcal R_{>T}\preceq W_{>T}\preceq\mathcal R_{>T},
\qquad
\|W_{>T}\|\le\tau(m,T).
\tag{9}
\]
The high pair-sum and pair-difference Gram matrices are each dominated by \(\mathcal R_{>T}\) as well.

At the original cutoff \(T=mL^2\),
\[
\boxed{
\tau_m
\le172800\frac{2m+1}{L}
\frac{(L+2\log L)^{5/2}}{mL^2}
\le3\cdot10^6L^{-1/2}.
}
\tag{10}
\]
Here \(d\le3m\) and \(\log T\le2L\).

This holds simultaneously for all carrier vectors. Zeros at \(|\gamma|=T\) belong to the low part; every higher zero and multiplicity is included. No zero-free ordinate is selected.

**Equation (10) does not say that the old jet majorant is small. It says that the actual high-zero action is small, so that majorant can be replaced.**

## 3. The old jet-majorized \(Q\)-test has an actual source witness against it

**[COFINAL_FAMILY | PAPER]**

Take the normalized **endpoint Dirichlet vector**
\[
g_m=\frac1{\sqrt d}\sum_{j=-m}^{m}\psi_j.
\tag{11}
\]
It uses the original carrier and has
\[
\|g_m\|_2=1,\qquad
|g_m(L/2)|^2=|g_m(-L/2)|^2=\frac dL.
\tag{12}
\]

I first prove that its true source Gram and Weil form have only polylogarithmic size:
\[
\boxed{
\langle g_m,\mathcal G_mg_m\rangle\le B_g(m),
\qquad
|W(g_m)|\le B_g(m),
\qquad
B_g(m)=540000L^{11/2}.
}
\tag{13}
\]

### The true source estimate

For any \(\gamma\), choose \(j_0\) nearest to \(-\gamma L/(2\pi)\) among the carrier indices. For \(j\ne j_0\),
\[
|\gamma+\omega_j|\ge\frac{\pi}{L}|j-j_0|.
\]
For the nearest mode use its defining integral, avoiding any removable quotient in (6). Summing the remaining modes gives
\[
\begin{aligned}
|M_{g_m}(w)|
&\le
\sqrt{\frac Ld}\,m^{|\delta|/2}
\left(1+\frac4\pi H_{2m}\right)\\
&\le4\sqrt{\frac{L^3}{d}}\,m^{|\delta|/2}.
\end{aligned}
\tag{14}
\]

For \(|\gamma|\le m\), combine this with (3). The sum of squared evaluations is at most
\[
21600L^{11/2}.
\]
For \(|\gamma|>m\), use (8) with \(T=m\); here \(m\ge2\Omega\) in the stated range. This costs at most
\[
518400L^{3/2}.
\]
Their sum is bounded by (13). The positive pair-sum Gram and the absolute signed form are both bounded by this same evaluation sum.

### The artificial jet penalty

The accepted old parameters were
\[
J=\left\lceil\frac L{2\log L}\right\rceil,
\qquad T=mL^2,
\]
and the old jet majorant was
\[
\mathcal J_m(f)=
16C_ZJ\sqrt m\,\frac{\log(T+4)}T
\sum_{k<J}\frac{|\eta_k(f)|^2}{T^{2k}}.
\]
Its zeroth term alone gives
\[
\boxed{
\mathcal J_m(g_m)
\ge16C_Z\frac{\sqrt m}{L\log L}.
}
\tag{15}
\]

Let
\[
Q_{\rm old}=\mathcal G_m+(r-\epsilon_m^{\rm old})I,
\]
where \(\epsilon_m^{\rm old}=O(L^{10}\log L)\). Because the old source rows contain the entire jet majorant,
\[
\boxed{
\begin{aligned}
&\langle g_m,
(Q_{\rm old}-\mathcal L_{\rm old}^*\mathcal L_{\rm old})
g_m\rangle\\
&\quad\le
540000L^{11/2}+Cm^\eta
-16C_Z\frac{\sqrt m}{L\log L}
=:U_m(C,\eta).
\end{aligned}
}
\tag{16}
\]
For every fixed \(C>0\) and \(0<\eta<1/2\),
\[
U_m(C,\eta)<0
\]
on every sufficiently late original cell. Also \(r-\epsilon_m^{\rm old}>0\) eventually, so the \(Q\)-test is well-defined.

This is a **negative upper envelope**, not merely a failed estimate.

By contrast, write the accepted relation as
\[
K_m=\mathsf H_m(0)+\mathcal E_m,
\qquad
\mathsf H_m(r)=\mathsf S(r)-\mathsf T_m,
\qquad
\|\mathcal E_m\|\le C_0:=c_A+28.
\]
Then
\[
\boxed{
\langle g_m,\mathsf H_m(Cm^\eta)g_m\rangle
\ge Cm^\eta-B_g(m)-C_0>0
}
\tag{17}
\]
eventually.

Thus the old sufficient comparison rejects this actual source direction while the true shifted target is positive on it.

**KILL_SCOPE: THEOREM_SHAPE.** The killed shape is the original jet-majorized sufficient \(Q\)-comparison at subpolynomial shifts. Equation (17) proves positivity only on this witness—not positivity of the whole matrix. Nothing here kills the exact Schur target or SP.

## 4. Replace the artificial rows by a controlled full-operator error

**[COFINAL_FAMILY | PAPER]**

Keep exactly the earlier tuning
\[
\alpha_m=\frac{8\log L}{L},
\qquad T=mL^2.
\]

Let \(\mathcal G_{\le T}\) contain all critical-line rows and positive pair-sum rows below \(T\). Let \(\mathcal L_0\) contain precisely
\[
\sqrt{r_w}\,b_w,\qquad
\Re w>\alpha_m,\quad |\Im w|\le T,
\]
where
\[
b_w(f)=\frac{M_f(w)-M_f(w^\dagger)}{\sqrt2}.
\]
**There are no jet rows in \(\mathcal L_0\).**

Let \(N_{\rm near}\) denote the positive Gram of the negative rows with
\[
0<\Re w\le\alpha_m,\qquad |\Im w|\le T.
\]
The accepted near-line estimate supplies
\[
0\preceq N_{\rm near}\preceq\beta_mI,
\qquad
\beta_m=O(L^{10}\log L).
\]

The full source identity is now
\[
\boxed{
K_m
=\mathcal G_{\le T}
-\mathcal L_0^*\mathcal L_0
-N_{\rm near}
+W_{>T}.
}
\tag{18}
\]
Every signed zero contribution has been assigned to one part. Through the accepted full explicit formula, this retains the original poles, \(I-R\), all prime powers, and all cross terms.

Put
\[
J_m=\mathcal G_{\le T}-\mathcal L_0^*\mathcal L_0,
\qquad
\kappa_m=C_0+\tau_m,
\qquad
\epsilon_m=\beta_m+\kappa_m.
\]
Then the **actual requested matrix** has the asymmetric sandwich
\[
\boxed{
J_m+(r-\epsilon_m)I
\preceq \mathsf H_m(r)
\preceq J_m+(r+\kappa_m)I.
}
\tag{19}
\]

The lower comparison has a proved polylogarithmic loss. The upper comparison has a bounded loss. The large jet overestimate is absent from both.

This is stronger than a sufficient minorant with an uncontrolled discrepancy: it gives a quantitative connection back to the actual sign.

## 5. A positive block inside the actual previous Schur complement

**[COFINAL_FAMILY | PAPER]**

This repair can be spent directly on the Schur form you asked to estimate.

Define
\[
\mathcal R_{\rm old}=\ker\mathcal L_{\rm old},
\qquad
\mathcal R_0=\ker\mathcal L_0.
\]
The old rows were the same low off-line rows plus the jets, so
\[
\mathcal R_{\rm old}\subseteq\mathcal R_0.
\]
Write
\[
\mathcal R_0
=\mathcal R_{\rm old}\oplus\mathcal J_{\rm end},
\qquad
\dim\mathcal J_{\rm end}\le J.
\tag{20}
\]
The space \(\mathcal J_{\rm end}\) consists of directions made exceptional **only by the old endpoint constraints**.

For \(r>\epsilon_m\), (19) proves
\[
\boxed{
\mathsf H_m(r)|_{\mathcal R_0}
\succeq(r-\epsilon_m)I.
}
\tag{21}
\]

Now decompose the **actual old Schur complement** on
\[
\mathcal R_{\rm old}^{\perp}
=
\mathcal J_{\rm end}\oplus\mathcal R_0^\perp:
\]
\[
\mathfrak S_{\rm old}(r)=
\begin{pmatrix}
D_{\rm end}&C_{\rm end}\\
C_{\rm end}^*&E_0
\end{pmatrix}.
\]

For \(v\in\mathcal J_{\rm end}\), its Schur quadratic form is
\[
\inf_{y\in\mathcal R_{\rm old}}
\langle y+v,\mathsf H_m(r)(y+v)\rangle.
\]
Every \(y+v\) lies in \(\mathcal R_0\). Equation (21) therefore gives
\[
\boxed{
D_{\rm end}\succeq(r-\epsilon_m)I,
\qquad
\|D_{\rm end}^{-1}\|\le(r-\epsilon_m)^{-1}.
}
\tag{22}
\]

Thus the endpoint-only block of the **actual** previous Schur form is now proved positive. Its full coupling is retained in
\[
\boxed{
\mathfrak S_0(r)
=
E_0-C_{\rm end}^*D_{\rm end}^{-1}C_{\rm end}.
}
\tag{23}
\]
By Schur associativity, this is exactly what results from eliminating the entire \(\mathcal R_0\) directly from \(\mathsf H_m(r)\).

The previous \(B^*A^{-1}B\) correction has not been dropped; it is already inside \(\mathfrak S_{\rm old}\). The additional correction in (23) remains as well.

Dependent jet rows merely make \(\mathcal J_{\rm end}\) smaller. If it is zero-dimensional, the additional elimination is empty. No original diagonal \(q_j\) or zero jet pivot is divided by.

**This is an actual Schur-block estimate.** It does not assert that a small perturbation of the full matrix automatically produces a small entrywise perturbation of its Schur complement.

## 6. The remaining source comparison is now finite and quantitatively faithful

**[FINITE_CELL | PAPER]**

For \(s>0\), define
\[
Q_0(s)=\mathcal G_{\le T}+sI,
\qquad
Z_m(s)=\mathcal L_0Q_0(s)^{-1}\mathcal L_0^*.
\]
Only the explicit shift supplies positivity of \(Q_0(s)\). No sampling floor for \(\mathcal G_{\le T}\) is assumed.

The conjugation identity gives
\[
J_m+sI\succeq0
\quad\Longleftrightarrow\quad
Z_m(s)\preceq I.
\]
Combining this with (19),
\[
\boxed{
Z_m(r-\epsilon_m)\preceq I
\ \Longrightarrow\
\mathsf H_m(r)\succeq0
\ \Longrightarrow\
Z_m(r+\kappa_m)\preceq I,
\qquad r>\epsilon_m.
}
\tag{24}
\]

Unlike the old jet-majorized test, this comparison has a **proved discrepancy** relative to the actual target. At the same numerical shift, the left test remains sufficient and the right test necessary; they are not silently identified.

The first unsupplied family estimate is
\[
\boxed{
\forall\eta>0\ \exists C_\eta>0\
\exists\text{ unbounded original }\mathcal G_\eta:
\qquad
Z_m(C_\eta m^\eta)\preceq I
\quad(m\in\mathcal G_\eta).
}
\tag{25}
\]
The shifts in (24) are absorbable at that scale, but **this equivalence is not the claimed progress**. The progress is the full high-zero magnitude bound, the source-specific failure of the old majorant, and the positive endpoint-only block of the actual Schur.

The unresolved interaction is now solely between the finite low off-line **difference rows** and the retained finite critical-line and **pair-sum rows**. I do not have the required estimate for it.

### A source-specific discriminator with an actual carrier witness

Take a row-space vector \(z\), an original carrier coefficient vector \(y\), and \(s>0\). Put
\[
b=\mathcal L_0^*z,\qquad
e=b-Q_0(s)y,
\]
\[
F_s(z,y)
=
2\Re\langle b,y\rangle-\langle y,Q_0(s)y\rangle.
\]
Completion of the square gives
\[
\boxed{
F_s(z,y)
\le\langle z,Z_m(s)z\rangle
\le F_s(z,y)+\frac{\|e\|^2}{s}.
}
\tag{26}
\]

More importantly,
\[
\boxed{
\langle y,(J_m+sI)y\rangle
=
\|z\|^2-F_s(z,y)-\|\mathcal L_0y-z\|^2.
}
\tag{27}
\]
Therefore a certified strict inequality
\[
F_s(z,y)>\|z\|^2
\]
already produces a negative direction in the original carrier.

At \(s=r+\kappa_m\), the upper inequality in (19) turns that into an **actual violation of \(\mathsf H_m(r)\succeq0\)**, rather than mere failure of a sufficient test. For a zero-consistent result, the residual budget \(\|e\|^2/s\) in (26) is the discriminator. Passing individual trials does not certify the whole row-space matrix.

## Closeout

The announced high-zero repair test closes: the complete tail has norm \(O(L^{-1/2})\), not the polynomial endpoint penalty imposed by the old majorant. The latter yields a genuine, source-specific theorem-shape kill, but the actual route survives that kill because (10) replaces the overestimate.

The actual Schur now has an additional proved positive block. What remains is its low off-line-pair sign—not another endpoint budget, density count, or standalone inverse estimate. **No new whole-matrix bottom floor or common-cell SP subsequence is supplied.**

**Next mathematical step:** establish (25) from the finite low critical-line and pair-sum rows, using the shifted variational margin (26)–(27) as the first sign discriminator. The endpoint rows must stay removed by the proved tail bound; reinstating their old majorant would reintroduce a certificate already refuted on the original source.
