# Proshka answer 10/10 — complete inline source

Date: 2026-10-06. Chat: Missing T7 Lemma (6aba5f5a-f804-83ed-a667-68147ee00f59).
Question: 0d8931db-b520-431e-9af5-920c13a0dbe9. Answer: 3bc13552-7f56-4c68-9b3c-7394da299fad.
Captured through read_thread after chat became idle at18:36 UTC. Linked supplement not retrieved; citation placeholders retained verbatim, not independently resolved.
This chat is exhausted for new questions; do not send question11.

## Exact question

Continuation 10/10. Answer9 is fully processed. This is the final bounded exploration of the SAME actual CCM source family after the recorded direct-theta localization stall; do not silently switch matrices, drop prime powers, or claim the old G1/G3 chain closed.

Independent checks accepted your exact variation, all signs in (3)-(5),(12), and the half-leakage counterexample (6)-(11). The latter kills ONLY uniform carrier-wide projection repair: x_m is not a bottom vector. The constant6 edge split is valid. Direct P_m(Gf) localization is STALLED at its full signed defect.

Our own additional attempt pays only one term: from |G(t)|<=D0 exp[-(pi/2)e^(2|t|)], sup_t |G(t)G(t+log n)|<=D0^2 e^(-pi n). Thus for the full prime shift operator P_I=sum Lambda(n)/sqrt(n)(T_log n+T_log n*), ||M_G P_I M_G||<=2D0^2 sum Lambda(n)n^-1/2 e^-pi n, uniformly in m. This controls the cross term in (G(t+s)-G(t))^2 only, not its endpoint-G^2 terms or projection correction. It gives no sign.

A possibly much cheaper terminal obligation emerged. Please test and ATTACK IT rather than continue the failed multiplication variation or the almost-unit overlap OS. Keep the literal full Hermitian K_m on |n|<=m, L=log m, N=m, original m_j=preAnchorTailStart(P)+j+2, and the exact normalized WINDOW row g_m=c_m(G)/sigma_m. Let P0,m be the orthogonal projector onto the ENTIRE bottom eigenspace (no simplicity/parity assumption), epsilon_m=||K_m g_m|| and rho_m=||P0,m g_m||.

Exact algebra, needing no gap:
  |lambda_min(K_m)| rho_m=||P0,m K_m g_m||<=epsilon_m.
Therefore a lower bound on rho may suffice even if it tends to zero. The minimal proposed target is:
  whenever lambda_min(K_m)<0, rho_m>0 and epsilon_m/rho_m ->0
on the original eventual family. A fixed-polynomial lower bound rho_m>=c m^-A, c>0 and fixed finite A, only on those negative-bottom cells, would suffice using the residual below. This requires neither rho->1 nor simplicity nor exclusion of every source-null vector within a degenerate bottom space. It cannot assume away a purely odd negative bottom, since then rho=0 exactly.

Available actual-source residual proof, already on our shelf (not a spectral assumption):
For each fixed derivative order, G is smooth, even and has Gaussian log tails; its endpoint derivative jumps are polynomial(m)e^-pi m. Repeated integration by parts retaining these jumps gives for the WINDOW projection p_m of G:
  ||p_m-G||_L2(I)+||(p_m-G)'||_L2(I)+sum_edge |p_m-G|=O_R(m^-R)
for each fixed R, with derivative order chosen large enough, no uniformity in growing R. The full mixed-form estimate against ANY unit finite synthesis f is
 |W(e-t,f)| <= (2+4L)sqrt(m)||e||2 +26||e'||2
    +26 D_e sqrt(3m/L)+tau_G(m),
 e=p_m-G|I, t=G 1_(I^c),
 tau_G=2m^(1/4)A_G+2sqrt(m)S_Lambda T_G
       +26||G'1_(I^c)||2+26(|G(-L/2)|+|G(L/2)|)sqrt(3m/L),
 A_G=int_(I^c)e^(|t|/2)|G(t)|dt,
 T_G=||e^|t| G 1_(I^c)||2,
 S_Lambda=sum_(n>=2)log(n)n^-3/2.
All terms of tau_G are polynomial(m)e^-c m. The global radical W(G,f)=0 and sigma_m->||G||2>0 thus give epsilon_m=O_R(m^-R). Our Sept25 independently checked proof already gives epsilon->0; this fixed-order strengthening is explicitly derived in ODD_TRIAL_SIGN on our shelf and is being checked separately, not assumed from small Rayleigh values.

Own proposed consumer check:
For arbitrary fixed complex f in C_c^infinity(R), eventually support(f) lies inside I. Its projection f_m on these same modes, zero-extended, satisfies for Omega=2pi m/L
 ||f-f_m||2=O_q(Omega^(1/2-q)),
 ||(f-f_m)'||_L2(I)=O_q(Omega^(3/2-q)),
 ||f-f_m||_infinity,I=O_q(Omega^(1-q)).
Weighted A(e)=||e^|t|e||2<=sqrt(m)||e||2, and the zero-extension jump estimate ||e(.+h)-e||2<=h||e'||2+C sqrt(h)||e||infinity imply convergence in X with norm A(e)+sup_(0<h<=1)h^-1/4||e(.+h)-e||2. Our already checked full-Weil continuity on X retains both poles and ALL prime powers. Consequently W(f_m,f_m)->W(f,f), with W(f_m,f_m)=coeff(f_m)* K_m coeff(f_m). If lambda_min>=-o(1), every compact smooth complex test has nonnegative full Weil form, and Weil's criterion would give RH. This short full-carrier extension is under independent check; identify any real normalization/domain error, but do not spend the whole answer merely repackaging this conditional algebra. We have NOT declared a new proved terminal consumer or changed the source family.

MAIN TASK: find an actual-source proof of the weaker lower-overlap condition (polynomial lower norming weight would be enough) on negative-bottom cells, or a rigorous obstruction to it. Use our exact theta source, full matrix equations, spectral measure/norming-constant aliases or another concrete source-specific mechanism, with literature checked where relevant. Small residual alone does not lower-bound rho; abstract cyclicity without a quantitative bound does not suffice; real-space sign of G does not authorize PF for a signed Weil matrix; a global inverse-gap/complement floor or all-profile positivity PREMISE would be circular. A proof of the lower overlap would be a new substantive theorem, not bookkeeping.

The bounded current literature check found CCM §8 still leaves G1/tracking open; Andrade's scalar Herglotz criterion retains its uniform scalar inequality; Groskin v4 2605.20224 has finite-matrix identification and numerical cross-cutoff overlaps, not this theorem. They are not suppliers.

If the weaker attack stalls, state the precise actual-source signed/norming quantity left uncontrolled and whether this weaker consumer is genuinely usable; distinguish a proved obstruction from lack of proof. Do not invent a new sufficient wrapper as a result. No Lean or repository edits; RH remains OPEN.

## Exact inline answer

Ы. **The weaker consumer is valid. I have not proved its lower-overlap input.**

The concrete source calculation gives a **quantified adverse alternative on the unchanged \(N=m\) family**:

> **If** there is an off-critical-line zero \(\tfrac12+\delta+i\gamma\), with \(\delta>0\), then, for a fixed \(c_*>0\),
> \[
> \boxed{\lambda_{\min}(K_m)\le-c_*m^{\delta/4}}
> \]
> on **every sufficiently late original cell**. Consequently,
> \[
> \boxed{\rho_m\le c_*^{-1}m^{-\delta/4}\epsilon_m.}
> \]
> Thus \(\rho_m\) would decay faster than every inverse power; wherever \(\rho_m>0\), the ratio \(\epsilon_m/\rho_m\) would diverge rather than tend to zero.

**This does not assert that an off-line zero exists. It is not a counterexample to your target.** It shows, using the actual source rather than an abstract matrix control, exactly how the unexcluded negative spectrum would defeat the proposed norming bound.

The source-pair construction already appears in the September 9 work. The additional calculation here is its **uniform projection onto the original diagonal carrier \(N=m,\ L=\log m\)** and the resulting statement about the actual bottom norming weight. I do not count the older construction as new. 

## 1. The full-form topology pays the proposed consumer

Keep
\[
I_m=[-L/2,L/2],\qquad L=\log m,
\]
\[
\psi_{n,L}(t)=\frac{(-1)^n}{\sqrt L}e^{2\pi int/L}\mathbf1_{I_m}(t),
\qquad |n|\le m.
\]
Let \(P_m\) denote this Fourier projection, distinct from the entire-bottom projector \(P_{0,m}\).

The literal matrix is the restriction of the **full signed Weil form**:
\[
\mathcal W(P_mf,P_mh)=c_m(f)^*K_mc_m(h).
\]
The general finite wrapper uses exactly the modes \(-m,\ldots,m\); it does not supply positivity. 

Use the already established positive **control norm**
\[
\|f\|_{\mathcal E}^2
=
\|e^{|t|}f\|_2^2+\mathcal D(f,f),
\]
\[
\mathcal D(f,f)=
\int_0^\infty
\frac{e^{-s/2}}{1-e^{-2s}}
\|\tau_sf-f\|_2^2\,ds.
\]
This is not \(\mathcal W(f,f)\). The full form satisfies
\[
\boxed{
|\mathcal W(f,h)|\le22\|f\|_{\mathcal E}\|h\|_{\mathcal E}.
}
\tag{1}
\]
Its proof retains both pole functionals and bounds the complete prime-power sum using
\[
|\langle f,\tau_sh\rangle|
\le e^{-|s|}
\|e^{|t|}f\|_2\|e^{|t|}h\|_2.
\]
These continuity and domain facts are on the checked source shelf. 

For a fixed \(f\in C_c^\infty(\mathbb R;\mathbb C)\), eventually its support lies strictly inside \(I_m\). Write
\[
e_m=f-P_mf,\qquad \Omega=\frac{2\pi m}{L},\qquad C_q=\|f^{(q)}\|_1.
\]
Summing the actual Fourier coefficients gives, for each fixed integer \(q\ge2\),
\[
\begin{aligned}
a_0:=\|e_m\|_2
&\le\frac{C_q}{\sqrt{\pi(2q-1)}}\Omega^{1/2-q},\\
a_1:=\|e_m'\|_{L^2(I_m)}
&\le\frac{C_q}{\sqrt{\pi(2q-3)}}\Omega^{3/2-q},\\
a_\infty:=\|e_m\|_{\infty,I_m}
&\le\frac{C_q}{\pi(q-1)}\Omega^{1-q}.
\end{aligned}
\tag{2}
\]

The zero extension can jump at both endpoints. Splitting a translation into the common interior and the two boundary strips gives
\[
\|\tau_se_m-e_m\|_2
\le s\,a_1+\sqrt{2s}\,a_\infty
\qquad(0<s\le1).
\]
Using \(J(s)\le2/s\) for \(s\le1\) and \(J(s)\le2e^{-s/2}\) for \(s\ge1\),
\[
\boxed{
\|e_m\|_{\mathcal E}^2
\le(m+16)a_0^2+2a_1^2+8a_\infty^2
\longrightarrow0.
}
\tag{3}
\]

This also verifies your proposed translation-seminorm argument. No whole-line high-pass assertion or global \(H^1\) claim is needed.

Therefore
\[
\mathcal W(P_mf,P_mf)\to\mathcal W(f,f),
\qquad
\|P_mf\|_2\to\|f\|_2.
\]
If \((-\lambda_{\min}(K_m))_+\to0\), the variational inequality implies
\[
\mathcal W(f,f)\ge0
\quad\text{for every }f\in C_c^\infty(\mathbb R;\mathbb C).
\]

That is the full complex-test Weil criterion, not an even-only or pole-removed condition. Its equivalence with RH is stated explicitly before equation (1.2) in Suzuki’s paper. The RH-dependent Hilbert-space constructions later in that paper are not being used as unconditional inputs. :chatgpt-content-reference{index="3"}

**So the proposed consumer has no remaining normalization or jump-domain defect in this calculation.** A proof of its overlap premise would be a new terminal argument, not retroactive verification of the old G1/G3 constructors.

## 2. The residual strengthening remains an upper estimate

For the actual even window coefficients of \(G\), repeated integration by parts gives, for \(n\ne0\) and every fixed \(p\ge1\),
\[
\boxed{
c_m(G)_n
=
\frac2{\sqrt L}\sum_{j=1}^{p}
\frac{(-1)^{j-1}G^{(2j-1)}(L/2)}{\omega_n^{2j}}
+
\frac{(-1)^p}{\omega_n^{2p}}c_m(G^{(2p)})_n.
}
\tag{4}
\]
In particular, the first boundary contribution is
\[
+\frac{2G'(L/2)}{\sqrt L\,\omega_n^2},
\]
not zero. This agrees with the exact source derivative recurrence in the current record. 

For fixed derivative order, the endpoint terms are polynomial multiples of \(e^{-\pi m}\). The last term in (4) gives the three omitted-tail orders
\[
O_p(\Omega^{1/2-2p}),\qquad
O_p(\Omega^{3/2-2p}),\qquad
O_p(\Omega^{1-2p})
\]
in interior \(L^2\), interior derivative \(L^2\), and pointwise norm.

Substitution in the **full mixed-form estimate supplied in the question**, including its exterior \(\tau_G\), yields
\[
\boxed{
\forall R>0:\qquad
\epsilon_m=\|K_mg_m\|=O_R(m^{-R}).
}
\tag{5}
\]
The derivative order is chosen after fixing \(R\), then held fixed as \(m\to\infty\). The normalization is legitimate because \(\sigma_m\to\|G\|_2>0\).

This confirms the stated fixed-order strengthening from the supplied mixed-form bound. It remains a residual estimate, not a lower bound on any spectral weight. The existing audit expressly distinguishes the full residual from a small Rayleigh quotient. 

## 3. Concrete source attack: isolate one hypothetical off-line pair

**[COFINAL_FAMILY | PAPER, conditional on the specified off-line zero]**

Use the exact Laplace transform of the same complete source:
\[
\mathcal G(z)=\int_{\mathbb R}G(t)e^{zt}\,dt
=-4\xi(1/2+z).
\tag{6}
\]
The factor \(-4\), evenness and weighted decay are those of the source audit. 

Suppose
\[
w=\delta+i\gamma,\qquad \delta>0,
\]
is a zero of multiplicity \(r\). Its partner
\[
w^\dagger=-\overline w=-\delta+i\gamma
\]
has the same multiplicity.

For a rapidly decreasing function \(v\) with \(\mathcal M_v(w)=0\), define
\[
(\mathcal J_wv)(t)
=
e^{-wt}\int_{-\infty}^{t}e^{wu}v(u)\,du
=
-e^{-wt}\int_t^\infty e^{wu}v(u)\,du.
\tag{7}
\]
The equality uses the zero moment. The two representations separately control the negative and positive tails. They give
\[
(\partial_t+w)\mathcal J_wv=v,
\qquad
\mathcal M_{\mathcal J_wv}(z)
=
\frac{\mathcal M_v(z)}{w-z}.
\]

Set
\[
d_w=\frac{(-1)^r}{r!}\mathcal G^{(r)}(w)\ne0,
\qquad
H_w=\frac{\mathcal J_w^rG}{d_w},
\tag{8}
\]
and define \(H_{w^\dagger}\) similarly.

Their transforms are exactly one at their respective selected zero and zero at every other distinct zeta zero. **All other zeros, including all other possible off-line zeros, are annihilated by the source factor—not omitted from an estimate.**

In these coordinates the signed zero formula is
\[
\mathcal W(f,h)
=
\sum_{z\in Z}m_z\,
\overline{\mathcal M_f(-\overline z)}
\,\mathcal M_h(z).
\tag{9}
\]
For the fixed functions in (8), smooth cutoff and weighted integration by parts justify the formula and its absolute limiting sum. This is the same full explicit formula underlying the literal matrix, with its conjugate first slot. :chatgpt-content-reference{index="7"}

Thus
\[
\mathcal W(H_w,H_w)
=
\mathcal W(H_{w^\dagger},H_{w^\dagger})=0,
\qquad
\mathcal W(H_w,H_{w^\dagger})=r.
\]

For \(b\ge0\), put
\[
u_b=e^{-ib\gamma}\tau_bH_w
-e^{ib\gamma}\tau_{-b}H_{w^\dagger}.
\tag{10}
\]
Its two nonzero evaluations in (9) are
\[
\mathcal M_{u_b}(w)=e^{\delta b},
\qquad
\mathcal M_{u_b}(w^\dagger)=-e^{\delta b}.
\]
Consequently,
\[
\boxed{
\mathcal W(u_b,u_b)=-2r e^{2\delta b},
\qquad
\|u_b\|_2^2\le
D:=2\bigl(\|H_w\|_2^2+\|H_{w^\dagger}\|_2^2\bigr).
}
\tag{11}
\]

The norm bound is independent of \(b\). The two-pole term and the prime powers are still contained in \(\mathcal W\); no favorable sign has been assigned to them separately.

This is the existing source-pair separator, rechecked in the current normalization. The next step is what ties it to the actual production family.

## 4. Project it onto \(N=m\), with a uniform error

Define the fixed finite source constant
\[
B=
\int_{\mathbb R}e^{4|t|}
\left(
|H_w|^2+|H_w'|^2+
|H_{w^\dagger}|^2+|H_{w^\dagger}'|^2
\right)\,dt.
\tag{12}
\]
It depends on the selected zero, its multiplicity and the nonzero derivative in (8). It may be large; no uniform root-conditioning bound is asserted.

Choose smooth cutoffs \(\chi_a\), supported strictly inside \((-a,a)\), equal to one on \([-a+1,a-1]\), with
\[
0\le\chi_a\le1,\qquad
\|\chi_a'\|_\infty\le2,
\]
and all fixed-order derivative bounds independent of \(a\). Such a family is obtained from one fixed smooth step at the two endpoints.

Now make the **original parameter choice**
\[
a=\frac L2,\qquad s=a-1,\qquad b=\frac s4,
\qquad f_a=\chi_a u_b.
\tag{13}
\]

### Compactification

For \(v\in H^1(\mathbb R)\),
\[
\mathcal D(v,v)\le\|v'\|_2^2+16\|v\|_2^2.
\]
If
\[
B(v)=\int e^{4|t|}(|v|^2+|v'|^2),
\]
retaining both transition strips gives
\[
\|(1-\chi_a)v\|_{\mathcal E}^2
\le
(e^{-2s}+24e^{-4s})B(v)
\le25e^{-2s}B(v).
\]

For (10),
\[
B(u_b)\le2e^{4b}B,\qquad
\|u_b\|_{\mathcal E}\le\sqrt{34B}\,e^b.
\]
Applying (1),
\[
\begin{aligned}
|\mathcal W(f_a,f_a)-\mathcal W(u_b,u_b)|
&\le
220\sqrt{68}\,B e^{-s+3b}
+1100B e^{-2s+4b}\\
&\le3000B e^{-s/4}.
\end{aligned}
\tag{14}
\]
This reproduces the shelf’s complete compactification budget, including the cutoff derivative. 

Hence, eventually,
\[
\mathcal W(f_a,f_a)\le-r e^{\delta(a-1)/2},
\qquad
\|f_a\|_2^2\le D.
\tag{15}
\]

### The moving test has uniformly bounded fixed-order derivatives

This is the crucial extra check. Let \(M_j\) bound \(\|\chi_a^{(j)}\|_\infty\), independently of \(a\), with \(M_0=1\). Then
\[
C_3=
\sum_{j=0}^{3}\binom3jM_j
\left(
\|H_w^{(3-j)}\|_1+
\|H_{w^\dagger}^{(3-j)}\|_1
\right)<\infty
\tag{16}
\]
satisfies
\[
\|f_a'''\|_1\le C_3
\]
for every sufficiently large \(a\).

Translation does not change these unweighted norms, and the factors \(e^{\pm ib\gamma}\) have modulus one. There is **no derivative order increasing with \(m\)**.

Apply the Fourier and jump estimates (2)–(3) with this same \(C_3\). They yield
\[
\boxed{
\|f_a-P_mf_a\|_{\mathcal E}
\le E_3(m):=
C_3
\left[
\frac{m+16}{5\pi}\Omega^{-5}
+\frac2{3\pi}\Omega^{-3}
+\frac2{\pi^2}\Omega^{-4}
\right]^{1/2}.
}
\tag{17}
\]
The projection is onto exactly \(|n|\le m\). Its two zero-extension jumps are paid by (3).

Also
\[
\|f_a\|_{\mathcal E}
\le C_Bm^{1/8},
\qquad
C_B=(\sqrt{34}+5\sqrt2)\sqrt B.
\]
Therefore
\[
\boxed{
\begin{aligned}
|\mathcal W(P_mf_a,P_mf_a)-\mathcal W(f_a,f_a)|
&\le22E_3(m)\bigl(2C_Bm^{1/8}+E_3(m)\bigr)\\
&=O_{w,r}\!\left(m^{-11/8}(\log m)^{3/2}\right).
\end{aligned}
}
\tag{18}
\]

The error tends to zero while the magnitude of the negative quantity in (15) grows. Eventually,
\[
\mathcal W(P_mf_a,P_mf_a)
\le-\frac r2e^{-\delta/2}m^{\delta/4}<0.
\]
This proves \(P_mf_a\ne0\). Since orthogonal projection gives
\[
\|P_mf_a\|_2^2\le D,
\]
the variational principle for the **literal full matrix** gives
\[
\boxed{
\lambda_{\min}(K_m)
\le
-\frac{r e^{-\delta/2}}{2D}\,m^{\delta/4}.
}
\tag{19}
\]

All constants are fixed after selecting the hypothetical zero. The inequalities hold for every sufficiently large integer \(m\), hence for every sufficiently late original \(m_j\).

**No nestedness of the changing Fourier spaces is assumed.** The auxiliary test is only a variational witness. It does not redefine \(g_m\), \(U_m\), the selected ground family, or the mode schedule.

## 5. Consequence for the exact bottom norming weight

Let \(P_{0,m}\) project onto the **entire** bottom eigenspace. Regardless of multiplicity,
\[
P_{0,m}K_mg_m
=
\lambda_{\min}(K_m)P_{0,m}g_m.
\]

Under the conditional estimate (19), with
\[
c_*=\frac{r e^{-\delta/2}}{2D},
\]
we obtain
\[
\boxed{
\rho_m\le c_*^{-1}m^{-\delta/4}\epsilon_m.
}
\tag{20}
\]

Together with (5), this gives
\[
\forall A>0:\qquad m^A\rho_m\longrightarrow0.
\]
At any cell where \(\rho_m>0\),
\[
\boxed{
\frac{\epsilon_m}{\rho_m}
\ge c_*m^{\delta/4}.
}
\tag{21}
\]
At \(\rho_m=0\), there is no division: the proposed nonvanishing requirement fails there.

Thus the hypothetical adverse alternative defeats **every fixed-polynomial lower norming bound**, on the whole late original family, not merely on selected numerical cells.

Again, this is conditional on an off-line zero. **It neither proves such a zero exists nor refutes the lower-overlap condition.**

## 6. Why the norming-constant approach still stalls

The exact missing quantity is the spectral mass
\[
\boxed{
\nu_m(\{\lambda_{\min}(K_m)\})
=
\langle g_m,P_{0,m}g_m\rangle
=
\rho_m^2.
}
\tag{22}
\]

For any orthonormal basis \(u_1,\ldots,u_d\) of the whole bottom space,
\[
\boxed{
\rho_m^2
=
\frac1{\sigma_m^2}
\sum_{\ell=1}^{d}
\left|
\int_{I_m}G(t)f_{u_\ell}(t)\,dt
\right|^2.
}
\tag{23}
\]
This is not an infimum over bottom vectors. Degenerate bottom spaces may contain source-null vectors while still having \(\rho_m>0\). A purely odd bottom space makes (23) zero and has not been assumed away.

The scalar spectral measure \(\nu_m\) is positive because \(K_m\) is Hermitian, but positivity of a measure does not lower-bound its smallest atom. The source residual supplies only
\[
\int t^2\,d\nu_m(t)=\epsilon_m^2.
\]
The construction above shows how an adverse spectrum would satisfy that small-moment constraint: its bottom moves negatively while the source weight shrinks faster than any inverse power.

The **cyclicity** alias—density of translates—does not supply the missing lower bound either. The project already proves that translates of \(G\) span a dense subspace of \(L^2\), since \(\widehat G\) is nonzero almost everywhere. But those translates are simultaneously full-Weil radicals. This is \(L^2\)-density, not density in the form-control topology, and not cyclicity of \(g_m\) for each \(K_m\). The distinction is explicit in the shelf proof. 

There is a useful qualitative cross-check. If a compact smooth \(f\) had \(\mathcal W(f,f)=-d<0\), approximate it in \(L^2\) by a finite combination \(r\) of translates of \(G\). Then
\[
\mathcal W(f-r,f-r)=-d
\]
while \(\|f-r\|_2\) can be arbitrarily small. For each fixed such choice, compactification in \(\mathcal E\), followed by the original Fourier projection, yields arbitrarily negative normalized Rayleigh quotients. Thus any negative compact witness would force
\[
\lambda_{\min}(K_m)\to-\infty
\]
on the same sequence. Equation (19) provides a quantitative version when an off-line zero is specified.

This cross-check does **not** establish a negative witness. It confirms why the qualitative translate theorem cannot select the favorable norming alternative.

## 7. Final disposition

**The lower norming estimate remains unproved.** I have neither established \(\rho_m>0\) on negative-bottom cells nor bounded \(\epsilon_m/\rho_m\) there.

What is established in this attempt is the conditional, original-carrier estimate (19), with its full projection budget, and the norming consequence (20)–(21). It rules out treating “small negative spectrum with polynomial source visibility” as an automatic remaining regime: any off-line zero would instead produce increasingly negative bottoms with superalgebraically small visibility.

The proposed weaker consumer is genuinely usable. In fact, after the domain check, its truth—and the truth of the polynomial sufficient version—is equivalent to RH: it implies full Weil nonnegativity, while RH leaves no negative finite cells on which the overlap condition must be imposed. **That equivalence does not invalidate the proof strategy. It means the missing lower norming theorem is substantive, not already supplied by the residual or qualitative cyclicity.**

The next independent check should concern the new passage from the existing source-pair separator to (19): the fixed third-derivative bound, both jump strips, the \(-4\xi\) normalization, and the negative numerator/denominator direction. No new sufficient wrapper or Lean receiver is proposed.

No numerical source experiment, Lean run, repository edit, or independent audit of this new derivation was performed. **The prescribed \(U_m\), OS, G1, G3 and RH remain open.**

:chatgpt-content-reference{index="11"}[Complete PAPER derivation: original-carrier projection budget, conditional norming obstruction, consumer check and exact remaining quantity](sandbox:/mnt/data/PROSHKA_G1_NEGATIVE_BOTTOM_NORMING_ALTERNATIVE_2026-10-06.md)

