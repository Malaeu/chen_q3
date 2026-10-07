Ы — **the actual source gives a strictly positive regular gap, a mixed moment estimate, and a quantitative discriminator for the three-moment certificate’s loss. It does not give the requested all-\(\eta\) sign.**

The source calculation excludes the branch \(b\ne0,\ Tb=0\). The remaining difficulty is an explicit **projected four-source correlation**, with every term of \(F_{10}\) retained. I have not produced a source-realized failure of \(L_3\), or a negative actual Schur vector.

:chatgpt-content-reference{index="15"}[Complete PAPER verdict, source-moment expansions, error propagation, and directive](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q06_2026-10-07.md)

## 1. The full source gives more than \(T\succeq0\)

**[COFINAL_FAMILY | PAPER]**

Keep the original source projectors
\[
\Pi=P_{\mathcal R},\qquad Q=P_{\mathcal E}=I-\Pi,
\qquad \mathcal R=\ker\mathcal L_0,
\]
with the original zero cutoffs and eventual cells. Write
\[
G=\mathcal G_{\le T_{\rm z}},\qquad
Z=\mathcal L_0^*\mathcal L_0,\qquad
\mathcal E_{\rm a}=K_m-H_0.
\]

The accepted complete zero identity is
\[
H_0=G-Z-N_{\rm near}+W_{>T_{\rm z}}-\mathcal E_{\rm a},
\]
where
\[
0\preceq N_{\rm near}\preceq\beta_mI,\qquad
\|W_{>T_{\rm z}}\|\le\tau_m,\qquad
\epsilon_m=\beta_m+c_A+28+\tau_m.
\]
All positive pair-sum rows and all retained negative difference rows remain. :chatgpt-content-reference{index="0"}

The useful point is that the **archimedean comparison is asymmetric**. Let \(H_{\rm pole}\) denote the compression of the positive kernel \(e^{-|x-y|/2}\). The source identities give
\[
\mathcal E_{\rm a}
=A_{\rm arch}-\operatorname{diag}(a)-c_AI+2H_{\rm pole},
\]
\[
\|A_{\rm arch}-\operatorname{diag}(a)\|\le20,
\qquad 0\preceq H_{\rm pole}\preceq4I.
\]
Therefore
\[
\boxed{
-(20+c_A)I\preceq\mathcal E_{\rm a}\preceq(28-c_A)I.
}
\tag{1}
\]
The full endpoint and off-diagonal archimedean terms are already included in the constant \(20\). :chatgpt-content-reference{index="1"} :chatgpt-content-reference{index="2"}

Define the **actual positive completion**
\[
\mathsf P:=H_0+\epsilon_mI+Z=G+\mathsf V,
\]
where
\[
\mathsf V=\epsilon_mI-N_{\rm near}+W_{>T_{\rm z}}-\mathcal E_{\rm a}.
\]
Using precisely the fixed \(\epsilon_m\), not changing it, gives
\[
\boxed{
\sigma I\preceq\mathsf V\preceq\rho_mI,\qquad
\sigma=2c_A>0,\qquad
\rho_m=\beta_m+2\tau_m+2c_A+48.
}
\tag{2}
\]
Indeed, the lower scalar is
\[
\epsilon_m-\beta_m-\tau_m-(28-c_A)=2c_A.
\]

Now \(\Pi Z=Z\Pi=0\). Thus
\[
\boxed{
T=\Pi\mathsf P\Pi|_{\mathcal R}\succeq\sigma I_{\mathcal R},
\qquad
B=\Pi\mathsf P Q.
}
\tag{3}
\]
The negative Gram disappears from \(B,T\) **because of the actual source projector**, not because its norm was bounded or its rows omitted.

For \(v\in\mathcal E\), put
\[
p=\langle v,\mathsf Pv\rangle,\qquad
n_-(v)=\|\mathcal L_0v\|^2.
\]
Then the exceptional diagonal remains
\[
\boxed{
q_0=p-\epsilon_mN-n_-(v),\qquad
q=gN+p-n_-(v).
}
\tag{4}
\]
No comparison of \(n_-(v)\) with \(p\) has been assumed.

### A genuinely mixed source estimate

**[FINITE_CELL | PAPER]**

Apply Cauchy–Schwarz to the positive form \(\mathsf P-\sigma I\), on the actual vectors \(v\) and \(b=Bv\). Since
\[
\langle b,(\mathsf P-\sigma I)v\rangle=M,
\]
we obtain
\[
\boxed{
M^2\le(p-\sigma N)(c-\sigma M).
}
\tag{5}
\]

Consequently, for \(b\ne0\),
\[
\boxed{
p>\sigma N,\qquad c>\sigma M>0,\qquad e\ge\sigma c>0.
}
\tag{6}
\]

This settles one source question completely: **\(b\ne0,\ Tb=0\) is impossible on these eventual cells.** The branch \(b=0\) remains \(S_r(v)=q\), and its sign must still be checked separately.

## 2. The actual moments contain all signed source words

**[FINITE_CELL | PAPER]**

Use seven already signed operators:
\[
(S_0,\ldots,S_6)
=
\bigl(
\operatorname{diag}a,\,
-C_{<Y_0},\,
-C_I,\,
-C_{\rm long},\,
-C_{\rm wheel},\,
-C_2,\,
-C_*
\bigr).
\]
Then
\[
\boxed{
H_0=\sum_{i=0}^6S_i=F_{10}-C_*.
}
\tag{7}
\]
This is the exact source decomposition; the wheel and powers of two remain inside the moments. :chatgpt-content-reference{index="3"} :chatgpt-content-reference{index="4"} :chatgpt-content-reference{index="5"}

Set
\[
b_i=\Pi S_iv,\qquad
w_{ki}=\Pi S_k\Pi S_iv,
\qquad
b=\sum_i b_i,\qquad
w=\sum_{k,i}w_{ki}=\Pi H_0b.
\]
The complete evaluation is
\[
\begin{aligned}
q_0&=\sum_i\langle v,S_iv\rangle,\\
M&=\sum_{i,j}\langle b_i,b_j\rangle,\\
d_3&:=\langle b,w\rangle
=\sum_{i,k,j}\langle b_i,S_kb_j\rangle\in\mathbb R,\\
d_4&:=\|w\|^2
=\sum_{k,i,\ell,j}\langle w_{ki},w_{\ell j}\rangle,
\end{aligned}
\]
and hence
\[
\boxed{
c=d_3+\epsilon_mM,\qquad
e=d_4+2\epsilon_md_3+\epsilon_m^2M.
}
\tag{8}
\]

The **source covariance** controlling the certificate’s loss is therefore
\[
\boxed{
\Gamma(v):=Me-c^2
=Md_4-d_3^2
=\sum_{j<k}|b_jw_k-b_kw_j|^2.
}
\tag{9}
\]
It is independent of the scalar shift in \(T\). Equation (8) retains every mixed term—including terms involving different \(F_{10}\) components and \(C_*\).

### Explicit projection corrections on the actual exceptional space

The source matrix being multiplied is not an unspecified Hermitian matrix:
\[
(H_0)_{jj}=a(\omega_j)-d_j,\qquad
(H_0)_{jk}=-\frac{h_j-h_k}{\pi(j-k)}\quad(j\ne k),
\]
where \(d_j,h_j\) come from the same full signed primitive
\[
\Phi_m(t;y)
=
\sum_{2\le n\le y}\Lambda(n)n^{-1/2-it}
-\frac{y^{1/2-it}-1}{1/2-it}
+\frac{1-y^{-1/2-it}}{1/2+it}.
\]
All original cross modes and both pole pieces remain. :chatgpt-content-reference{index="6"}

Write \(\mathcal L=\mathcal L_0\), and define
\[
\mathcal A_j=\mathcal L H_0^j\mathcal L^*,
\qquad j=0,\ldots,4,
\qquad
\mathcal I=\mathcal A_0^\dagger.
\]
The **Moore–Penrose inverse** here only implements the already fixed projector:
\[
Q=\mathcal L^*\mathcal I\mathcal L.
\]
No conditioning bound is assumed, and dependent source rows are allowed.

For every actual vector \(v=\mathcal L^*z\),
\[
N=z^*\mathcal A_0z,\qquad q_0=z^*\mathcal A_1z,
\]
\[
M=z^*\mathcal D_2z,\qquad
d_3=z^*\mathcal D_3z,\qquad
d_4=z^*\mathcal D_4z,
\]
where
\[
\begin{aligned}
\mathcal D_2={}&\mathcal A_2-\mathcal A_1\mathcal I\mathcal A_1,\\
\mathcal D_3={}&\mathcal A_3-\mathcal A_2\mathcal I\mathcal A_1
-\mathcal A_1\mathcal I\mathcal A_2
+\mathcal A_1\mathcal I\mathcal A_1\mathcal I\mathcal A_1,
\end{aligned}
\]
and
\[
\boxed{
\begin{aligned}
\mathcal D_4={}&
\mathcal A_4
-\mathcal A_3\mathcal I\mathcal A_1
-\mathcal A_2\mathcal I\mathcal A_2
-\mathcal A_1\mathcal I\mathcal A_3\\
&+\mathcal A_2\mathcal I\mathcal A_1\mathcal I\mathcal A_1
+\mathcal A_1\mathcal I\mathcal A_2\mathcal I\mathcal A_1
+\mathcal A_1\mathcal I\mathcal A_1\mathcal I\mathcal A_2\\
&-\mathcal A_1\mathcal I\mathcal A_1
  \mathcal I\mathcal A_1\mathcal I\mathcal A_1.
\end{aligned}}
\tag{10}
\]

Thus the exact remaining covariance is
\[
\boxed{
\Gamma(\mathcal L^*z)
=(z^*\mathcal D_2z)(z^*\mathcal D_4z)
-(z^*\mathcal D_3z)^2.
}
\tag{11}
\]

Taking only \(\mathcal A_4\), or replacing any intermediate \(\Pi\) by the identity, does **not** calculate this correlation.

## 3. Quantify the certificate’s loss on the actual source

**[FINITE_CELL | PAPER]**

For an independent source upper bound, set
\[
\mathcal R_m=\sup_{\substack{|t|\le\Omega\\1\le y\le m}}|\Phi_m(t;y)|,
\qquad
\mathfrak B_m=L+8+4\mathcal R_m,
\qquad
a_m=\epsilon_m+\mathfrak B_m.
\]
The accepted full-matrix estimate gives
\[
\|H_0\|\le\mathfrak B_m,\qquad
\boxed{\sigma I\preceq T\preceq a_mI.}
\tag{12}
\]
Its known scale remains \(m^{1/2-o(1)}\), not subpolynomial. :chatgpt-content-reference{index="7"} :chatgpt-content-reference{index="8"}

For \(b\ne0\), abbreviate
\[
D_g=gc+e,\qquad A_g=gM+c.
\]
The optimized residuals in your supplied identities are the actual vectors
\[
r_L=\frac{eb-cTb}{D_g},
\qquad
r_U=\frac{cb-MTb}{A_g}.
\]
Their norms evaluate exactly:
\[
\boxed{
\|r_L\|^2=\frac{e\Gamma}{D_g^2},
\qquad
\|r_U\|^2=\frac{M\Gamma}{A_g^2}.
}
\tag{13}
\]

Inserting the **proved source spectral interval** (12) into the accepted residual identities yields
\[
\boxed{
\frac{\sigma e\Gamma}{g(g+\sigma)D_g^2}
\le S_r(v)-L_3(v)
\le
\frac{a_me\Gamma}{g(g+a_m)D_g^2},
}
\tag{14}
\]
and
\[
\boxed{
\frac{M\Gamma}{(g+a_m)A_g^2}
\le U_1(v)-S_r(v)
\le
\frac{M\Gamma}{(g+\sigma)A_g^2}.
}
\tag{15}
\]

These give a same-moment discriminator stronger than merely reporting that \(L_3<0\):
\[
\begin{aligned}
S_r(v)\ge\max\bigg\{&
L_3+\frac{\sigma e\Gamma}{g(g+\sigma)D_g^2},\
U_1-\frac{M\Gamma}{(g+\sigma)A_g^2}
\bigg\},\\
S_r(v)\le\min\bigg\{&
L_3+\frac{a_me\Gamma}{g(g+a_m)D_g^2},\
U_1-\frac{M\Gamma}{(g+a_m)A_g^2}
\bigg\}.
\end{aligned}
\tag{16}
\]

Every quantity is evaluated on the same actual vector and cell. A negative upper bound certifies that cell’s negative Schur direction. A negative \(L_3\) alone does not.

If \(\Gamma=0\), then \(Tb\) is collinear with \(b\), both optimized residuals vanish, and
\[
L_3=U_1=S_r(v).
\]
The zero discriminator is the source residual \(eb-cTb\), or the squared-minor sum (9), with certified arithmetic and projector errors—not floating-point subtraction of nearly equal \(Me\) and \(c^2\).

### A source-valid improvement using the same moments

The new source gap also permits
\[
g_\sigma=g+\sigma,\qquad
c_\sigma=c-\sigma M,\qquad
e_\sigma=e-2\sigma c+\sigma^2M.
\]
Applying the same three-moment construction to \(T-\sigma I\) gives
\[
L_{3,\sigma}
=q-\frac{M}{g+\sigma}
+\frac{(c-\sigma M)^2}
{(g+\sigma)[D_g-\sigma A_g]}.
\]
The denominator is positive by (5)–(6), and
\[
\boxed{
L_{3,\sigma}-L_3
=
\frac{\sigma\Gamma(e-\sigma c)}
{g(g+\sigma)D_g[D_g-\sigma A_g]}
\ge0.
}
\tag{17}
\]

This is **not a higher-moment hierarchy**: it spends the newly proved source bound \(T\succeq2c_AI\). It still supplies no estimate of \(\Gamma\) at the required scale.

The original overestimate can be seen directly:
\[
\boxed{
L_3
=gN+(q_0+\epsilon_mN)
-\frac{\Gamma/e}{g}
-\frac{c^2/e}{g+e/c}.
}
\tag{18}
\]
The certificate places mass \(\Gamma/e\) at the zero endpoint although the actual \(T\) is bounded below by \(\sigma\). These weights come from the actual source moments. **Their size on actual exceptional vectors remains unestimated**; this is not a fabricated spectral counterexample.

## 4. Execute the available uniform estimate

**[COFINAL_FAMILY | PAPER]**

The complete source bounds do prove \(F_r(v)\ge0\), simultaneously for every actual exceptional vector, at
\[
\boxed{
r_{\rm norm}(m)=\epsilon_m+2\mathfrak B_m.
}
\tag{19}
\]
Indeed,
\[
g=2\mathfrak B_m,\qquad
q\ge(\epsilon_m+\mathfrak B_m)N,\qquad
M\le\mathfrak B_m^2N,
\]
so
\[
gq-M
\ge(2\epsilon_m\mathfrak B_m+\mathfrak B_m^2)N\ge0.
\]
Therefore
\[
F_r=(gq-M)(gc+e)+c^2\ge0.
\]
The \(b=0\) branch has \(q\ge0\) separately; the nonzero degenerate branch was excluded in Section 1.

But substituting the accepted source envelope gives only
\[
\boxed{
r_{\rm norm}
=
O\!\left(
\epsilon_m+
\sqrt m\,L^3
e^{-10^{-3}(L/\log L)^{1/3}}
\right).
}
\tag{20}
\]
This reproduces the previous exponent tending to \(1/2\). It does not establish the all-\(\eta\) target. The fact that this **upper envelope** is too large says nothing about the actual necessary shift. :chatgpt-content-reference{index="9"}

### The precise unestimated comparison

For \(b\ne0\), the numerator is
\[
\boxed{
F_r
=
g\bigl\{(q_0+rN)(gc+e)-Mc\bigr\}
-\Gamma(v).
}
\tag{21}
\]
The remaining source estimate is therefore
\[
\boxed{
\Gamma(\mathcal L^*z)
\le
g\bigl\{(q_0+rN)(gc+e)-Mc\bigr\}
}
\tag{22}
\]
for every actual \(z\), at \(r=C_\eta m^\eta\), on an unbounded original family.

Here the left side is explicitly (10)–(11), and the right side uses the same full signed moments. The separate condition
\[
q_0+rN\ge0\qquad\text{on }\ker B\cap\mathcal E
\]
also remains: \(F_r=0\) identically when \(b=0\), regardless of that diagonal sign.

**Why this attempt stops:** the positive completion controls the regular spectrum and gives the mixed estimate (5). It does not compare the retained negative-row energy \(n_-(v)\) with the positive energy after the regular response, and it does not estimate the projected four-source covariance (11) against the signed margin in (22).

The Q5 top-block continuous bound cannot be inserted into this missing step: neither \(\Pi\) nor the actual columns of \(\mathcal L^*\) are proved supported in that block. Zero-count magnitude bounds likewise do not estimate these row orientations and cross correlations.

No source-realized obstruction to (22) has been established. **The certificate is not refuted.**

## 5. Entire return budget and nonlinear moment errors

**[FINITE_CELL | PAPER]**

In Sections 1–4, \(H_0\) is the **exact full source**. Thus there is no additive \(\Delta_{10}\) approximation error in those moments: its previously allocated operators were all reinserted, signed, in (7)–(8). This is recombination, not a proof that the components are small.

The inherited allocation itself remains
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
\tag{23}
\]
All corresponding source operators remain in the products defining \(B,T,c,e\). :chatgpt-content-reference{index="10"} :chatgpt-content-reference{index="11"} :chatgpt-content-reference{index="12"}

The actual return is unchanged:
\[
A_r=gI+T,\qquad
f=J_rv=v-A_r^{-1}b,\qquad
\Pi H_m(r)f=0,
\]
\[
S_r(v)=q-\langle b,(g+T)^{-1}b\rangle.
\]
One may deduce the honest per-vector bound
\[
\|J_rv\|^2\le N+\frac{M}{(g+\sigma)^2},
\]
but \(M\) has not been controlled at an all-\(\eta\) scale. This does not make \(\|J_r\|\) uniformly bounded.

### A small analytic tail must be propagated through the moments

If the Q5 approximation is used,
\[
\widetilde H_0=F_{10}-(C^{(5)}+C_Q),\qquad
\|\widetilde H_0-H_0\|\le\delta=4\varepsilon_4,
\]
with \(C_Q\) signed and
\[
\varepsilon_4=
\frac{256h_U(1+L)^2(1+\Omega)\sqrt m}{m^2}
+\frac{2^{24}}{m^5},
\]
define, using the **same actual projectors**,
\[
\widetilde b=\Pi\widetilde H_0v,\quad
\widetilde T=\Pi(\widetilde H_0+\epsilon_mI)\Pi|_{\mathcal R},
\quad
\widetilde w=\widetilde T\widetilde b.
\]
Put
\[
\rho_b=\delta\sqrt N,\qquad
\rho_w=\delta\|\widetilde b\|
+(\|\widetilde T\|+\delta)\rho_b.
\]
Then
\[
\boxed{
\begin{aligned}
|q_0-\widetilde q_0|&\le\delta N,\\
|M-\widetilde M|&\le2\|\widetilde b\|\rho_b+\rho_b^2,\\
|c-\widetilde c|&\le
\|\widetilde b\|\rho_w+\|\widetilde w\|\rho_b+\rho_b\rho_w,\\
|e-\widetilde e|&\le2\|\widetilde w\|\rho_w+\rho_w^2.
\end{aligned}}
\tag{24}
\]
The file gives the resulting division-free error bound for \(F_r\).

These amplification factors cannot be omitted. A vanishing carrier-norm tail is **not automatically a vanishing fourth-moment error**. Errors in an approximately constructed source projector would require their own certificate.

If \(F_{10}\) is paid rather than retained signed, the original complete bracket remains
\[
\boxed{
\begin{aligned}
s_5(v)-(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|
&\le S_r(v)\\
&\le s_5(v)+(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|,
\end{aligned}}
\]
where
\[
s_5(v)=rN-\Re\langle v,(C^{(5)}+C_Q)J_rv\rangle.
\]
No fixed-power allocation has been sharpened in this calculation. The actual full Schur correction remains present. :chatgpt-content-reference{index="13"}

## What genuinely changed

The new source results are the regular gap \(T\succeq2c_AI\), exclusion of the nonzero degenerate branch, the mixed estimate (5), and the explicit certificate-loss bounds (14)–(17). The full projected moment correlation is evaluated algebraically in (8)–(11).

**The main signed family has not improved:** the only uniform sign estimate obtained is (19), at the old scale. No nonzero numerical exceptional witness was constructed, and no arbitrary matrix or invented off-line zero is being offered as one.

The next bounded calculation should address that correlation directly. The actual matrix has the **rank-two displacement identity**
\[
[D_{\rm ind},H_0]
=\pi^{-1}(u\mathbf h^*-\mathbf h u^*),
\quad
D_{\rm ind}=\operatorname{diag}(j),\quad u=(1,\ldots,1)^T.
\]
For \(R_z=(zI-D_{\rm ind})^{-1}\),
\[
\boxed{
H_0R_zu
=
R_zH_0u
+\frac{u^*R_zu}{\pi}R_z\mathbf h
-\frac{\mathbf h^*R_zu}{\pi}R_zu.
}
\]
The actual negative-row columns are paired Cauchy vectors of this form, with their finite endpoint numerators. The bounded task is to use this identity on those columns to test the **joint second-, third-, and fourth-source correlation already in (10)**—not introduce higher moments. It must stop if it only replaces the same unknown by unestimated correlations involving \(H_0u\) and \(\mathbf h\).

**SP/G1/G3/RH and the actual Schur sign remain OPEN. These are new PAPER derivations, not an independent audit or a certified source computation.**
