Ы — **the displacement test stalls without a new signed Schur estimate.** There is a concrete cancellation in \(Hu\), with a vanishing entrywise remainder on the middle half of the carrier. But after combining both \(H\)-actions, an explicit **signed two-source kernel** remains. The actual paired-zero relation cancels a same-pair overlap only up to its exact finite-carrier defect; it does not estimate the complete projected correlation.

**No source-realized failure of \(L_3\), negative actual Schur vector, or improved bottom exponent is established.**

:chatgpt-content-reference{index="18"}[Complete PAPER verdict, proofs, controls, and nonlinear error ledger](sandbox:/mnt/data/PROSHKA_VERDICT_FULL_CCM_GROWTH_ROLLOVER_Q07_2026-10-07.md)

## 1. A cancellation in the complete prime–pole first anchor

**[FINITE_CELL | PAPER]**

Keep \(H=H_0\), \(A=Hu\), \(\kappa=2\pi/L\), and the single signed source
\[
d\nu(s)=
\sum_{2\le n\le m}\frac{\Lambda(n)}{\sqrt n}\delta_{\log n}(ds)
-(e^{s/2}-e^{-s/2})\,ds.
\]
All prime powers and both pole pieces remain. The matrix is the original
\[
H=\operatorname{diag}(a)-P_m\int_0^L(S_s+S_s^*)\,d\nu(s)P_m.
\]
No source entries are varied independently. :chatgpt-content-reference{index="0"} :chatgpt-content-reference{index="1"}

Write
\[
p_j=\Re\Phi_m(\kappa j;m),\qquad
h_j=\Im\Phi_m(\kappa j;m),\qquad
\lambda_j=H_{m+j}-H_{m-j},
\]
where \(H_n=\sum_{k=1}^n1/k\) and \(H_0=0\).

The exact symmetric-shift action on \(u\) is
\[
K_j(s)=
2(1-s/L)\cos(j\theta)
+\frac1\pi\sum_{k\ne j}
\frac{\sin(k\theta)-\sin(j\theta)}{j-k},
\qquad \theta=\kappa s.
\]
This retains the original diagonal triangle and every cross mode. :chatgpt-content-reference{index="2"}

For \(0<s<L\), define
\[
\rho_j(s)=\frac1\pi\left[
\sum_{n>m-j}\frac{\sin((n+j)\theta)}n
+\sum_{n>m+j}\frac{\sin((n-j)\theta)}n
\right].
\]
Collecting the finite sine and cosine sums gives
\[
\boxed{
K_j(s)=
\cos(j\theta)-\frac{\lambda_j}{\pi}\sin(j\theta)+\rho_j(s).
}
\tag{1}
\]
The identity used here is
\[
2\sum_{n\ge1}\frac{\sin(n\theta)}n=\pi-\theta,
\qquad 0<\theta<2\pi.
\]
Its hypotheses match \(s/L\in(0,1)\); it is not applied at the endpoints. :chatgpt-content-reference{index="3"}

At those endpoints, the exact values are
\[
\rho_j(0)=1,\qquad \rho_j(L)=-1.
\]
Thus \(K_j(0)=2\) and \(K_j(L)=0\). In particular, the atom at \(n=m\) cancels between the cosine term and \(\rho_j(L)\), rather than being deleted. :chatgpt-content-reference{index="4"}

Integrating the **combined** identity (1) against the source gives
\[
\boxed{
A_j=a(\kappa j)-p_j-\frac{\lambda_j}{\pi}h_j+\eta_j,
\qquad
\eta_j=-\int_{[0,L]}\rho_j(s)\,d\nu(s).
}
\tag{2}
\]

### The remainder can be bounded uniformly—but only on its stated band

**[COFINAL_FAMILY | PAPER]**

For every integer \(m\ge16\),
\[
\boxed{
\max_{|j|\le m/2}|\eta_j|
\le128\,\frac{(1+L)^3}{\sqrt m}.
}
\tag{3}
\]

For this bound, Abel summation of the two tails gives
\[
|\rho_j(s)|
\le\frac4{\pi m\sin(\pi s/L)}
\le
\frac{L}{m\min(\log x,\log(m/x))},
\qquad x=e^s\in(1,m).
\]
The finite formula independently gives
\[
|\rho_j(s)|\le8(1+L)
\]
up to the endpoints.

Integrate these bounds against the actual atomic and continuous absolute masses **after** the cancellation (1). On \([1,\sqrt m]\), use
\[
\frac{\Lambda(n)}{\log n}\le1,\qquad
\frac{1-1/x}{\log x}\le1.
\]
On \([\sqrt m,m/2]\), use \(2L/m\); on \([m/2,m-1]\), use \(L/(m-x)\). The final continuous unit interval uses the finite bound, and the atom at \(m\) uses its exact value \(-1\). Their sum is bounded by (3).

**What this pays:** redundancy between the diagonal triangle and Hilbert terms in the first anchor.

**What it does not pay:** the retained \(p_j,h_j\), the outer carrier band, or the action on \(\mathcal E\). The exact \(\eta_j\) is retained at every index below. Neither the projector nor an actual paired row is assumed supported in the middle band.

## 2. Combine both \(H\)-actions: the remaining correlation is explicit

**[FINITE_CELL | PAPER]**

The source entries imply
\[
(Hx)_j
=
A_jx_j+\frac1\pi\sum_{k\ne j}
\frac{(h_j-h_k)(x_j-x_k)}{j-k}.
\tag{4}
\]
Consequently,
\[
\boxed{
(Hh)_j=h_jA_j+
\frac1\pi\sum_{k\ne j}\frac{(h_j-h_k)^2}{j-k},
}
\]
\[
\boxed{
(H^2u)_j=A_j^2+
\frac1\pi\sum_{k\ne j}
\frac{(h_j-h_k)(A_j-A_k)}{j-k}.
}
\tag{5}
\]
Direct diagonal multiplication cancels in these differences. The archimedean contribution remains inside \(A_j-A_k\); the signed denominators do not create a positive form.

Put
\[
r_j(z)=\frac1{z-j},\qquad
s_z=\frac1\pi\sum_kr_k(z),\qquad
\tau_z=\frac1\pi\sum_kh_kr_k(z),
\]
\[
Z_j(z)=A_j+s_zh_j-\tau_z.
\]
Here \(\tau_z\) denotes the displacement scalar, not the high-zero tail budget.

Substituting (5) into the two supplied actions and **collecting their mixed terms** yields
\[
\boxed{
X_{z,j}=r_j(z)Z_j(z),\qquad
Y_{z,j}=r_j(z)Z_j(z)^2+\mathcal Q_{z,j},
}
\tag{6}
\]
where
\[
\boxed{
\mathcal Q_{z,j}=
\frac1\pi\sum_{k\ne j}
\frac{(h_j-h_k)\bigl[A_j-A_k+s_z(h_j-h_k)\bigr]}
{(j-k)(z-k)}.
}
\tag{7}
\]

The extra term is not optional. In applying (4) to \(x_j=r_jZ_j\),
\[
x_j-x_k
=(j-k)r_jr_kZ_j
+r_k\bigl[A_j-A_k+s_z(h_j-h_k)\bigr].
\]
The first term produces the displayed square in (6); the second produces (7).

### Expand the surviving kernel through the full source

Define
\[
f_{jk}(s)=\sin(\kappa ks)-\sin(\kappa js),
\quad
\Delta K_{jk}(s)=K_j(s)-K_k(s),
\quad
\Delta a_{jk}=a(\kappa j)-a(\kappa k).
\]
Then
\[
\boxed{
\mathcal Q_{z,j}
=
\int\mathcal L_{z,j}(s)\,d\nu(s)
+\iint\mathcal T_{z,j}(s,t)\,d\nu(s)d\nu(t),
}
\tag{8}
\]
with
\[
\mathcal L_{z,j}(s)
=
\frac1\pi\sum_{k\ne j}
\frac{\Delta a_{jk}f_{jk}(s)}{(j-k)(z-k)},
\]
\[
\boxed{
\mathcal T_{z,j}(s,t)=
\frac1\pi\sum_{k\ne j}
\frac{f_{jk}(s)\bigl[-\Delta K_{jk}(t)+s_zf_{jk}(t)\bigr]}
{(j-k)(z-k)}.
}
\tag{9}
\]

This is a concrete kernel, not an uncomputed \(Hu,Hh,H^2u\) placeholder. If
\[
q_{\mathrm p}(s)=e^{s/2}-e^{-s/2},
\]
its double-source part is exactly
\[
\begin{aligned}
&\sum_{n,n'\le m}
\frac{\Lambda(n)\Lambda(n')}{\sqrt{nn'}}
\mathcal T_{z,j}(\log n,\log n')\\
&-\sum_{n\le m}\frac{\Lambda(n)}{\sqrt n}
\int_0^L\mathcal T_{z,j}(\log n,t)q_{\mathrm p}(t)\,dt\\
&-\sum_{n'\le m}\frac{\Lambda(n')}{\sqrt{n'}}
\int_0^L\mathcal T_{z,j}(s,\log n')q_{\mathrm p}(s)\,ds\\
&+\int_0^L\int_0^L
\mathcal T_{z,j}(s,t)q_{\mathrm p}(s)q_{\mathrm p}(t)\,ds\,dt.
\end{aligned}
\tag{10}
\]
**Both mixed terms remain separately**, since this kernel need not be symmetric.

At \(s=L\) or \(t=L\), the corresponding kernel vanishes: \(f_{jk}(L)=0\) and \(K_j(L)=0\). Thus endpoint prime-power occurrences cancel correctly even inside the second action.

The first-anchor remainder estimate (3) does not estimate (8)–(10). The unsaved full primitive remains in \(p,h\), and its quadratic correlation remains signed.

## 3. Evaluate the actual paired-zero relation

**[FINITE_CELL | PAPER]**

For every actual retained zero \(w=\delta+i\gamma\),
\[
z_w=\frac{\bar w}{i\kappa},\qquad
z_{w^\dagger}=\bar z_w,
\]
and its endpoint numerator has the exact normalization
\[
\boxed{
t_w=\frac{2\sinh(\bar wL/2)}{i\kappa\sqrt L}
=\frac{\sqrt L}{\pi}\sin(\pi z_w),
\qquad
t_{w^\dagger}=\bar t_w.
}
\tag{11}
\]
These are the source rows, with both finite endpoints and their original zero cutoffs. :chatgpt-content-reference{index="5"} :chatgpt-content-reference{index="6"}

Hence the actual columns are evaluated by
\[
(HC)_{jw}
=
\sqrt{r_w/2}
\left[t_wX_{z_w,j}-\bar t_wX_{\bar z_w,j}\right],
\]
\[
(H^2C)_{jw}
=
\sqrt{r_w/2}
\left[t_wY_{z_w,j}-\bar t_wY_{\bar z_w,j}\right],
\tag{12}
\]
using (2), (6), and (8) exactly. No endpoint coefficient is made independent of its zero parameter.

### Spend the complete signed zero identity

Let \(\mathcal P\) contain all retained positive critical and pair-sum rows. Keep
\[
\mathsf E_0=-N_{\rm near}+W_{>T_z}-(K_m-H_0)
\]
signed. Then
\[
\boxed{
H=\mathcal P^*\mathcal P-CC^*+\mathsf E_0.
}
\tag{13}
\]
This is the complete source equality; it has not dropped prime powers, poles, or archimedean corrections. :chatgpt-content-reference{index="7"}

Set \(\Omega_{+-}=\mathcal PC\). Every entry is computed by the finite kernel
\[
\mathscr K_m(p,w)
=
\sum_{j=-m}^m
\frac{4\sinh(pL/2)\sinh(\bar wL/2)}
{L(p+i\kappa j)(\bar w-i\kappa j)}.
\]
Writing
\[
\mathscr J_L(z)=\frac{2\sinh(zL/2)}z,\qquad \mathscr J_L(0)=L,
\]
Parseval gives the exact evaluation
\[
\boxed{
\mathscr K_m(p,w)
=\mathscr J_L(p+\bar w)-\mathscr T_m(p,w),
}
\tag{14}
\]
where \(\mathscr T_m\) is the absolutely convergent sum of the **same summand** over \(|j|>m\). It stays in the formula, including for zero parameters outside the carrier band.

For a positive pair-sum row,
\[
\boxed{
\begin{aligned}
(\Omega_{+-})_{p,w}
=\frac{\sqrt{r_pr_w}}2\bigl[
&\mathscr K_m(p,w)-\mathscr K_m(p,w^\dagger)\\
&+\mathscr K_m(p^\dagger,w)
-\mathscr K_m(p^\dagger,w^\dagger)
\bigr].
\end{aligned}}
\tag{15}
\]

### The same-pair term cancels—but the carrier defect does not

For \(p=w\), the four whole-interval terms in (15) are
\[
\mathscr J_L(2\delta)-L+L-\mathscr J_L(-2\delta)=0.
\]
Consequently,
\[
\boxed{
(\Omega_{+-})_{w,w}
=
-i r_w\Im\left[
t_w^2\sum_{|j|>m}\frac1{(z_w-j)^2}
\right].
}
\tag{16}
\]

**[COFINAL_FAMILY | PAPER]** For every actual retained row also satisfying \(|\gamma|\le\Omega/2\),
\[
\boxed{
|(\Omega_{+-})_{w,w}|
\le
\frac{4r_wL}{\pi^2}m^{\delta-1}
\le
\frac{4r_wL}{\pi^2\sqrt m}.
}
\tag{17}
\]
Indeed, \(|\Re z_w|\le m/2\),
\[
|t_w|^2\le Lm^\delta/\pi^2,
\qquad
\sum_{|j|>m}|z_w-j|^{-2}\le4/m,
\]
and \(0<\delta<1/2\).

This is a **same-pair overlap bound**, not a bound for \(\Omega_{+-}\), \(\mathcal P^*\Omega_{+-}\), or the actual Schur operator. The original retained set extends to \(mL^2\), not merely \(\Omega/2\).

### The remaining zero correlation is explicit

**[FINITE_CELL | PAPER]**

For two actual off-line parameters \(p,w\), the whole-interval part of (15) is
\[
\boxed{
4i\sqrt{r_pr_w}
\int_0^{L/2}
\cosh(\delta_p t)\sinh(\delta_w t)
\sin((\gamma_p-\gamma_w)t)\,dt.
}
\tag{18}
\]
The finite-carrier value subtracts the four exact tails from (14). Critical positive rows have the corresponding \(\delta_p=0\) expression and their original normalization.

Equation (18) cancels at equal ordinates before the carrier defect. **No estimate obtained here controls the complete distinct-ordinate kernel with its tails and projectors.** Zero membership enters through the actual row set and the full explicit formula (13); it does not make the finite prime–pole kernel (9) vanish.

This is the limit of this calculation, not a claim that further arithmetic cancellation is impossible.

## 4. Return to the actual projected moments

**[FINITE_CELL | PAPER]**

Put \(G_C=C^*C\) and retain
\[
\Pi=I-CG_C^\dagger C^*.
\]
The evaluated source inputs are
\[
\begin{aligned}
HC&=\mathcal P^*\Omega_{+-}-CG_C+\mathsf E_0C,\\
\mathscr B&=\Pi(\mathcal P^*\Omega_{+-}+\mathsf E_0C),\\
\mathscr W&=\Pi(\mathcal P^*\mathcal P+\mathsf E_0)\mathscr B.
\end{aligned}
\tag{19}
\]

For every actual \(v=Cz\),
\[
\begin{aligned}
N&=z^*G_Cz,\\
q_0&=z^*
\left[\Omega_{+-}^*\Omega_{+-}-G_C^2+C^*\mathsf E_0C\right]z,\\
b&=\mathscr Bz,\qquad w=\mathscr Wz,\\
M&=\|b\|^2,\qquad d_3=\langle b,w\rangle,\qquad d_4=\|w\|^2,\\
c&=d_3+\epsilon_mM,\qquad
e=d_4+2\epsilon_md_3+\epsilon_m^2M.
\end{aligned}
\tag{20}
\]
Here \(w=\Pi Hb\), not \(Tb\).

The feedback is still exactly
\[
w=\Pi\left[H^2C-HC\,G_C^\dagger C^*HC\right]z.
\]
No bound on \(G_C^\dagger\) is assumed, and dependent source rows are allowed.

Thus
\[
\boxed{
\Gamma(Cz)=
\|\mathscr Bz\|^2\|\mathscr Wz\|^2
-|\langle\mathscr Bz,\mathscr Wz\rangle|^2.
}
\tag{21}
\]
The needed comparison remains
\[
\boxed{
\Gamma(Cz)
\le
g\left\{(q_0+rN)(gc+e)-Mc\right\}
}
\tag{22}
\]
for every actual \(z\), at \(r=C_\eta m^\eta\), on an unbounded original family.

**This calculation has not proved (22).** The local cancellation (17) does not control \(\Omega_{+-}^*\Omega_{+-}\) against \(G_C^2\), nor its interaction with the regular projection and \(\mathsf E_0\).

The separate condition
\[
q_0+rN\ge0\qquad\text{on }\ker B\cap\mathcal E
\]
also remains. The nonzero degenerate branch stays excluded by the accepted \(T\succeq2c_AI\).

Using separate norms still supplies only
\[
r=\epsilon_m+2\mathfrak B_m,\qquad
\mathfrak B_m=L+8+4\mathcal R_m,
\]
at the previously accepted \(m^{1/2-o(1)}\) envelope. No exponent improvement has been obtained. That is a limitation of the proved upper estimate, not a lower bound on the necessary shift. :chatgpt-content-reference{index="8"} :chatgpt-content-reference{index="9"}

## 5. Full budget: no component was removed inside a moment

**[FINITE_CELL | PAPER]**

Throughout,
\[
\boxed{
H=
\operatorname{diag}a-C_{<Y_0}-C_I-C_{\rm long}
-C_{\rm wheel}-C_2-C_*.
}
\]
Every signed \(F_{10}\) component and its cross terms are present in (8)–(10) and (20). The new bounds (3) and (17) were **not substituted** for source entries or columns. The exact calculations therefore introduce no approximation error—but do not supply the missing estimate. :chatgpt-content-reference{index="10"} :chatgpt-content-reference{index="11"} :chatgpt-content-reference{index="12"}

The actual return remains
\[
f=J_rv=v-(g+T)^{-1}b,\qquad
\Pi(H+rI)f=0,
\]
\[
S_r(v)=q_0+rN-\langle b,(g+T)^{-1}b\rangle.
\]
In particular,
\[
\|J_rv\|^2
=N+\|(g+T)^{-1}b\|^2
\le N+\frac{M}{(g+2c_A)^2}.
\]
Since \(M\) is unestimated at the required scale, this is not a uniform bound on \(\|J_r\|\).

If \(F_{10}\) is instead paid through the previous approximation, its allocation is unchanged:
\[
\begin{aligned}
\Delta_{10}={}&L+8+8\sqrt{Y_0}(1+\log Y_0)
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
These remain component budgets, not a bottom floor. :chatgpt-content-reference{index="13"} :chatgpt-content-reference{index="14"} :chatgpt-content-reference{index="15"}

With \(C_Q\) retained signed,
\[
\boxed{
s_5(v)-(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|
\le S_r(v)\le
s_5(v)+(\Delta_{10}+4\varepsilon_4)\|v\|\|J_rv\|,
}
\]
where
\[
s_5(v)=rN-\Re\langle v,(C^{(5)}+C_Q)J_rv\rangle,
\]
\[
\varepsilon_4=
\frac{256h_U(1+L)^2(1+\Omega)\sqrt m}{m^2}
+\frac{2^{24}}{m^5}.
\]
No fixed-power allocation is sharpened here. The full Schur correction is retained. :chatgpt-content-reference{index="16"}

The artifact also retains Q6’s complete nonlinear propagation and its division-free discriminator:
\[
|F_r-\widetilde F_r|
\le
|\widetilde A|E_D+|\widetilde D|E_A+E_AE_D
+2|\widetilde c|E_c+E_c^2.
\]
No approximate source or projector was used to certify a sign in this answer. The new scalar remainder bounds cannot be substituted for a source-operator error.

## Stopping result

**What genuinely changed:** the first anchor has the explicit source cancellation (2)–(3); both \(H\)-actions have the combined kernel (8)–(10); and the actual same-pair zero overlap has the exact carrier-defect evaluation (16).

**What did not change:** the projected fourth-source correlation (21) has no new signed bound against (22). Neither the all-\(\eta\) certificate nor its failure on an actual exceptional vector has been proved.

The finite controls checked the source formulas and endpoint normalization, not the asymptotic claim. Generic complex parameters used for those controls were **not declared zeta zeros**, and no nonzero actual exceptional numerical witness was constructed.

**Stop this displacement mechanism at the surviving kernel and its projector feedback.** Continuing to rewrite \(Hu,Hh,H^2u\) would repackage the same unestimated correlation. No higher-moment node or replacement representation is selected without a new source estimate.

**SP, G1, G3, RH, and the actual Schur sign remain OPEN. These new PAPER derivations still require independent audit.**
