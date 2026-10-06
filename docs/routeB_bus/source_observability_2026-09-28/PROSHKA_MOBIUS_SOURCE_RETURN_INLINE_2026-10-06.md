# Proshka answer 6/10: Mobius source return

Status: AUXILIARY_PAPER_CHECKED; see MOBIUS_PROJECTION_AUDIT_2026-10-06.md. No G1/G3/RH closure.
Source chat: 6aba5f5a-f804-83ed-a667-68147ee00f59
User message: 9243705b-51f8-4e48-91be-e8dc7bda961d
Assistant message: a5c16301-1a2b-4609-9001-d1bbf7b87082
Captured from read_thread on 2026-10-06. Inline response is complete; linked supplement not retrieved. Reported checks below are Proshka claims until independently verified.

## Exact question

Continuation 6/10, same G1 prescribed-U source-sign discriminator. Answer5 has now passed independent analytic and algebra/metric checks: constants 1000 and 2 safe, epsI=o(1/m), complex pullback exact. Finite empty ranges need End=0 convention; eventually all ranges are nonempty. Its result is accepted only as auxiliary PAPER mathematics; no sign or G1 promotion.

Please work on the remaining signed source correlation, not another Fourier truncation or divisor decomposition. Keep the exact original U, m=N, L=log m, source S, complex Ehat and all prime powers. The sufficient target remains R_m(z)<= (kappa_m+1/(256m))*z*Ehat_m*z for all complex z on one unbounded original subsequence, where R=P_low+V+End from your answer5. A proved positive lower bound in the full compensated Qhat is also usable if it pays every error. This would decide whether this U can work; it would not itself prove RH.

Our bounded own attempt after answer5: fixed-frequency Type II logarithmic phase is separable, exp(it log(dr))=d^it r^it. On rectangles the sum factors. Cauchy in d cancels the d phase; the expanded term has phase (r1/r2)^it independent of d, and d ranges from ceil(Q/min(r1,r2)) to floor(m/max(r1,r2)), with d>k. Thus ordinary mixed-phase differencing alone gives no inner d oscillation. This is a limitation of that argument only. Arbitrary phase-matched coefficients yield the negative control; the actual Mobius/divisor weights are not arbitrary.

We retained the exact source contraction. With w_dr=nu(d)beta_k(r)/sqrt(dr), d,r>k, Q<=dr<=m, let W(t)=sum w_dr exp(it log(dr)), W1(t)=sum w_dr log(dr)exp(itlog(dr))=W'(t)/i. For b=S*z, define A_n=|b_n|^2/(pi n)+(4n/pi)Re(conj(b_n)(H b)_n). Then V(b)=2 sum_n |b_n|^2 Re(W(omega_n)+i W'(omega_n)/L)-sum_n A_n Im W(omega_n). Root and independent native checker verified this identity. No sign follows yet.

Can the actual S_n=sqrt(2/L)(-1)^n Ghat(omega_n)(1,-omega_n^2), together with the linked W/W' and Hilbert coefficients, furnish a signed cancellation that is lost by taking fixed-frequency absolute bounds? Work out one concrete source-specific mechanism. Preserve the low arithmetic range and explicit endpoints jointly, and any image/pole compensation. If a short-window twisted-moment theorem or an explicit-zero formula is used, prove the mapping, original-sequence quantifier, two-column minimum and off-critical-line terms; no RH or favorable zero signs may be assumed. BCR continuous theta<17/33 and Montgomery RH-conditional pair correlation do not directly apply (already audited).

The desired outcome is the displayed signed bound or a rigorous source counterargument that changes the plan. If unresolved, identify the first genuinely new source correlation needed after this separable-phase obstruction, and establish an estimate for it with an explicitly retained remainder; a renamed version of the same unbounded TypeII form is not progress. No repository writes or Lean. G1, G3 and RH remain OPEN.

## Exact inline answer

Ы. **I obtained a source-specific cancellation estimate and a source-specific obstruction to extending it across the whole line. I did not obtain the required signed upper bound.**

The mechanism is **Möbius inversion applied to the complete theta source before taking frequencywise absolute values**. It yields an explicit approximation to the mixed Type II response with error \(o(1/m)\) in the exact \(\widehat{\mathsf E}_m\) metric.

However, the same calculation shows that its **whole-line source-inversion remainder cannot be discarded**: two fixed critical-line zero evaluations detect a remainder whose \(L^1\)-mass grows outside the left window endpoint. This is an actual-source obstruction to that shortcut—not a counterexample to \(U_m\), and not an estimate of the remaining projected correlation.

## 1. Exact source cancellation, rather than separable-phase differencing

Keep all original objects and the prescribed two-column \(U_m\). In particular,
\[
m=m_j,\qquad N=m,\qquad L=\log m,\qquad I=[-L/2,L/2],
\]
with the full \(G,G''\) source and original complex metric. :chatgpt-content-reference{index="0"} :chatgpt-content-reference{index="1"}

Introduce the elementary source
\[
\psi(t)=e^{t/2}h_*(e^t),
\qquad
h_*(x)=(24\pi x^2-16\pi^2x^4)e^{-\pi x^2}.
\]
Then, exactly,
\[
G(t)=\sum_{n\ge1}n^{-1/2}\psi(t+\log n).
\]

For \(z=(z_0,z_2)\in\mathbb C^2\), write
\[
g_z=z_0G+z_2G'',\qquad
\psi_z=z_0\psi+z_2\psi''.
\]

Let \(\nu(d)\) denote the Möbius function. The full source satisfies
\[
\boxed{
\sum_{d\ge1}\frac{\nu(d)}{\sqrt d}\,
g_z(t+\log d)=\psi_z(t).
}
\tag{1}
\]

**Proof.** On every compact interval of real \(t\), the double Gaussian series and its two fixed derivatives converge absolutely and uniformly. Grouping by the product \(\ell=dn\), its coefficient is
\[
\sum_{d\mid\ell}\nu(d)=\mathbf1_{\{\ell=1\}}.
\]
This is the usual Möbius divisor identity, with the needed source convergence proved directly by the Gaussian decay. :chatgpt-content-reference{index="2"}

Unlike an arbitrary phase-matched sequence, our complete source possesses this cancellation. But (1) is initially a **local physical-coordinate identity**. It does not justify interchanging the infinite Möbius sum with a whole-line Fourier integral on the critical line.

## 2. Apply it to the existing Type II operator

Retain Answer5’s exact cutoffs
\[
k=\lfloor L^{1/8}\rfloor,\qquad
Q=\left\lceil\frac{12\pi k^2m}{L}\right\rceil,
\]
and
\[
\beta_k(r)=
\log r-\sum_{\substack{c\mid r\\c\le k}}\Lambda(c).
\]
Thus \(0\le\beta_k(r)\le\log r\), and \(\beta_k(r)=0\) for \(r\le k\).

Define the finite positive-shift operator
\[
(\mathcal T_m^+v)(t)=
\sum_{\substack{d,r>k\\Q\le dr\le m}}
\frac{\nu(d)\beta_k(r)}{\sqrt{dr}}\,
v(t+\log(dr)),
\]
\[
\mathcal T_{m,I}^+=\mathbf1_I\mathcal T_m^+\mathbf1_I.
\]

For the unchanged band synthesis \(\rho_z=\rho_{S_mz}\),
\[
\boxed{
\mathscr V_m(S_mz)
=
2\operatorname{Re}
\langle\rho_z,\mathcal T_{m,I}^+\rho_z\rangle.
}
\tag{2}
\]

This is the **complete linked \(W,W'\)–Hilbert expression** from the question, in physical translation coordinates. Neither its diagonal nor its reflected-Hankel contribution has been removed. The accepted Type I endpoint form and lower arithmetic range remain separate, unchanged inputs. 

Set
\[
J_m=\left\lfloor\frac m{k+1}\right\rfloor,\qquad
\ell_r=\max\{k,\lceil Q/r\rceil-1\},\qquad
u_r=\lfloor m/r\rfloor.
\]
Let \(\mathcal R_m^{\rm div}\) contain the integers \(k<r\le J_m\) with \(\ell_r<u_r\). Empty ranges contribute zero.

Define the explicit finite forcing
\[
\boxed{
F^\mu_{m,z}(t)=
\sum_{r\in\mathcal R_m^{\rm div}}\frac{\beta_k(r)}{\sqrt r}
\left[
\psi_z(t+\log r)
-
\sum_{d\le\ell_r}\frac{\nu(d)}{\sqrt d}
g_z(t+\log(dr))
\right].
}
\tag{3}
\]

Applying (1) gives the exact source-inversion remainder
\[
\boxed{
Q^\mu_{m,z}:=
F^\mu_{m,z}-\mathcal T_m^+g_z
=
\sum_{r\in\mathcal R_m^{\rm div}}\frac{\beta_k(r)}{\sqrt r}
\sum_{d>u_r}\frac{\nu(d)}{\sqrt d}
g_z(t+\log(dr)).
}
\tag{4}
\]

No new decomposition of \(\Lambda\) has occurred: (1) acts on the Möbius coefficients already present in the fixed Type II term.

## 3. A paid local estimate: all source indices through \(m\) cancel

This is the first new quantitative result.

The two fixed derivative polynomials are
\[
P_0(v)=24v-16v^2,\qquad
P_2(v)=150v-660v^2+448v^3-64v^4.
\]
Put \(P_z=z_0P_0+z_2P_2\). Expanding the complete source in (4) on compact physical sets gives
\[
Q^\mu_{m,z}(t)
=
e^{t/2}\sum_{\ell>m}
\mathfrak c_m(\ell)
P_z(\pi\ell^2e^{2t})e^{-\pi\ell^2e^{2t}},
\tag{5}
\]
where
\[
\mathfrak c_m(\ell)=
\sum_{\substack{r\in\mathcal R_m^{\rm div}\\r\mid\ell}}
\beta_k(r)
\sum_{\substack{d\mid\ell/r\\d>u_r}}\nu(d).
\]

The condition \(d>\lfloor m/r\rfloor\) forces \(rd>m\). Therefore every source index \(\ell\le m\) is absent **by exact arithmetic cancellation**, not by an envelope.

Moreover,
\[
|\mathfrak c_m(\ell)|
\le L\,d_3(\ell)\le L\ell^2,
\qquad
|P_z(v)|\le1362\,\|z\|v^4\quad(v\ge1).
\]

Define fixed finite source constants
\[
C_T=1362\pi^4
\sum_{h\ge1}(1+h)^{10}e^{-2\pi h},
\]
\[
C_G=1362\pi^4
\sum_{n\ge1}n^8e^{-\pi(n^2-1)}.
\tag{6}
\]

Writing \(t=-L/2+v\), \(v\ge0\), and \(\ell=m+h\), equation (5) yields
\[
\boxed{
|Q^\mu_{m,z}(-L/2+v)|
\le
C_TLm^{23/4}
e^{17v/2}e^{-\pi m e^{2v}}\|z\|.
}
\tag{7}
\]

Indeed,
\[
\ell^{10}\le m^{10}(1+h)^{10},
\qquad
\ell^2e^{2t}\ge me^{2v}+2h,
\]
and \(e^{17t/2}=m^{-17/4}e^{17v/2}\).

For \(m\ge3\),
\[
e^{17v/2}e^{-\pi m e^{2v}}
\le e^{-\pi m}e^{-\pi mv}.
\]
Consequently,
\[
\boxed{
\|\mathbf1_IQ^\mu_{m,z}\|_2
\le C_TL^{3/2}m^{23/4}e^{-\pi m}\|z\|,
}
\tag{8}
\]
and
\[
\boxed{
\int_{-L/2}^{\infty}|Q^\mu_{m,z}(t)|\,dt
\le\frac{C_T}{\pi}Lm^{19/4}e^{-\pi m}\|z\|.
}
\tag{9}
\]

These are bounds for the actual Möbius/divisor-weighted source remainder.

### Restore the physical window

For \(u\ge L/2\), the same complete Gaussian calculation gives
\[
|g_z(u)|\le C_Gm^{17/4}e^{-\pi m}\|z\|.
\]
Also,
\[
\sum_{\substack{d,r>k\\Q\le dr\le m}}
\frac{|\nu(d)|\beta_k(r)}{\sqrt{dr}}
\le2\sqrt m\,L(1+L).
\tag{10}
\]

This absolute estimate is used **only on the Gaussian-small physical exterior**, not on the main signed correlation.

Positive translations of \(t\in I\) can exit only through the right endpoint. Combining (8)–(10), set
\[
\mathfrak J_m=
L^{3/2}e^{-\pi m}
\left[
C_Tm^{23/4}
+2C_G(1+L)m^{19/4}
\right].
\]
Then
\[
\boxed{
\left\|
\mathcal T_{m,I}^+(\mathbf1_Ig_z)
-\mathbf1_IF^\mu_{m,z}
\right\|_2
\le\mathfrak J_m\|z\|.
}
\tag{11}
\]

Both window endpoints and the original product cut are accounted for.

## 4. The resulting mixed correlation estimate

Define two Hermitian quadratic forms:
\[
\mathcal F_m(z)=
2\operatorname{Re}\int_I
\overline{\rho_z(t)}F^\mu_{m,z}(t)\,dt,
\tag{12}
\]
\[
\mathcal C_m(z)=
2\operatorname{Re}
\left\langle
\rho_z,
\mathcal T_{m,I}^+
(\mathbf1_Ig_z-\rho_z)
\right\rangle.
\tag{13}
\]

The second is the **complementary-projection correlation**. It is not being set to zero.

Use the accepted exact-metric lower bound
\[
\widehat E_m(z)=\|\rho_z\|_2^2
\ge\frac14\mu_m\|z\|^2,
\qquad
\mu_m=c_ET_m^{9/2}\log T_m\,e^{-\pi T_m},
\quad
T_m=\frac{2\pi(m+1)}L.
\tag{14}
\]
This is the previously checked two-column mass estimate followed by its paid band comparison, not a new mass argument.  

Equations (2), (11)–(14) prove
\[
\boxed{
\left|
\mathscr V_m(S_mz)
-
\bigl[\mathcal F_m(z)-\mathcal C_m(z)\bigr]
\right|
\le
\eta_m\,z^*\widehat{\mathsf E}_mz,
\qquad
\eta_m=\frac{4\mathfrak J_m}{\sqrt{\mu_m}}.
}
\tag{15}
\]

Since \(T_m=o(m)\),
\[
\boxed{
\forall c\in(0,\pi):
\quad e^{cm}\eta_m\longrightarrow0.
}
\tag{16}
\]
In particular, \(\eta_m=o(1/m)\).

This is uniform in **all complex coefficient directions at the same cell**. The complementary function \(\mathbf1_Ig_z-\rho_z\) is not assumed orthogonal to the band: the full-sample construction and actual window coefficients differ. Its exact value is retained in (13).

**What has been estimated is the whole-source mixed forcing. The difference between that forcing and the complementary-projection correlation still carries the requested sign.**

## 5. A genuine source obstruction to dropping the whole-line return

There is a stronger conclusion than “we lack a domination hypothesis.” For the same \(Q^\mu_{m,z}\) in (4),
\[
\boxed{
\int_{-\infty}^{-L/2}|Q^\mu_{m,z}(t)|\,dt
\ge c_*\sqrt{J_m}\log J_m\,\|z\|
}
\tag{17}
\]
for every complex \(z\) and every sufficiently large original \(m\), with a fixed \(c_*>0\).

Thus its remainder is exponentially small on the original window, yet cannot be discarded in a whole-line Fourier/Mellin argument.

### An actual divisor-weighted moment, with explicit error

For fixed \(s=\tfrac12-i\gamma\), let
\[
B_{k,J}(s)=
\sum_{k<r\le J}\frac{\beta_k(r)}{r^s},
\qquad
A_k=\sum_{c\le k}\frac{\Lambda(c)}c.
\]

Elementary sum–integral comparison gives
\[
\boxed{
B_{k,J}(s)=
\frac{J^{1-s}}{1-s}
\left(
\log J-A_k-\frac1{1-s}
\right)
+\mathcal E_{k,J}(s),
}
\tag{18}
\]
where
\[
\boxed{
|\mathcal E_{k,J}(s)|
\le D_s+2C_s\sqrt k\log k,
}
\]
\[
C_s=3+2|s|+|1-s|^{-1},
\qquad
D_s=5+4|s|+|1-s|^{-2}.
\tag{19}
\]

**Proof.** Including the fractional final interval,
\[
\sum_{n\le X}n^{-s}
=\frac{X^{1-s}}{1-s}+O(C_s),
\]
\[
\sum_{n\le X}n^{-s}\log n
=
X^{1-s}\left(
\frac{\log X}{1-s}-\frac1{(1-s)^2}
\right)+O(D_s).
\]
The derivative integrals used to bound the errors are
\[
\int_1^\infty |s|x^{-3/2}\,dx=2|s|,
\]
\[
\int_1^\infty x^{-3/2}(1+|s|\log x)\,dx=2+4|s|.
\]
The endpoint terms are included in the displayed constants.

Because \(\beta_k(r)=0\) for \(r\le k\),
\[
B_{k,J}(s)=
\sum_{r\le J}r^{-s}\log r
-
\sum_{c\le k}\Lambda(c)c^{-s}
\sum_{n\le J/c}n^{-s}.
\]
Substitution proves (18), with error bounded by
\[
D_s+C_s\sum_{c\le k}\frac{\Lambda(c)}{\sqrt c}
\le D_s+2C_s\sqrt k\log k.
\]

Since
\[
A_k\le\log k(1+\log k)=o(\log J_m),
\]
we obtain
\[
\boxed{
B_{k,J_m}(s)=
\frac{J_m^{1-s}\log J_m}{1-s}(1+o_s(1)).
}
\tag{20}
\]

This estimate is at **fixed frequencies**. It is not a claim about \(W(\omega_n)\) at the moving frequencies in the sign problem.

### Two zero evaluations control both source columns

Choose two distinct positive critical-line zero ordinates \(\gamma_1,\gamma_2\). Their existence is unconditional; this does not assume that all other zeros lie on the critical line. :chatgpt-content-reference{index="6"}

Put \(s_\ell=\tfrac12-i\gamma_\ell\). Direct Gaussian Mellin integration gives
\[
\widehat\psi(\gamma)
=
B(\gamma):=
2s(1-s)\pi^{-s/2}\Gamma(s/2).
\tag{21}
\]
This is nonzero at the selected ordinates, while
\[
\widehat G(\gamma_\ell)=0.
\]

Eventually \(Q<m/2\). Every \(k<r\le J_m\) then has a nonempty original \(d\)-range, since
\[
r\lfloor m/r\rfloor\ge m-r\ge m/2.
\]

Now Fourier-transform the **finite expression**
\[
Q^\mu_{m,z}=F^\mu_{m,z}-\mathcal T_m^+g_z.
\]
Every translate of \(g_z\) vanishes at \(\gamma_\ell\). Only the elementary-source terms in \(F^\mu\) remain:
\[
\boxed{
\widehat Q^\mu_{m,z}(\gamma_\ell)
=
(z_0-z_2\gamma_\ell^2)
B(\gamma_\ell)B_{k,J_m}(s_\ell).
}
\tag{22}
\]

There is no interchange with an infinite Möbius Fourier series here.

The fixed matrix
\[
\mathsf B_*=
\operatorname{diag}
\left(
\frac{B(\gamma_1)}{1-s_1},
\frac{B(\gamma_2)}{1-s_2}
\right)
\begin{pmatrix}
1&-\gamma_1^2\\
1&-\gamma_2^2
\end{pmatrix}
\]
is invertible. Let \(\sigma_*=\sigma_{\min}(\mathsf B_*)>0\).

The factors \(J_m^{i\gamma_\ell}\) are unit-modulus row phases. Therefore (20)–(22) imply
\[
\left\|
\begin{pmatrix}
\widehat Q^\mu_{m,z}(\gamma_1)\\
\widehat Q^\mu_{m,z}(\gamma_2)
\end{pmatrix}
\right\|
\ge
\frac{\sigma_*}{2}\sqrt{J_m}\log J_m\,\|z\|
\]
eventually.

By (9), the part of either moment on \([-L/2,\infty)\) is exponentially small. Hence
\[
\left\|
\begin{pmatrix}
\displaystyle\int_{t<-L/2}Q^\mu_{m,z}(t)e^{-i\gamma_1t}\,dt\\[1mm]
\displaystyle\int_{t<-L/2}Q^\mu_{m,z}(t)e^{-i\gamma_2t}\,dt
\end{pmatrix}
\right\|
\ge
\frac{\sigma_*}{4}\sqrt{J_m}\log J_m\,\|z\|.
\]
Each component is bounded by the left-exterior \(L^1\)-norm. This proves (17), with
\[
c_*=\frac{\sigma_*}{4\sqrt2}.
\]

**This is simultaneous control of both coefficient directions**, not a scalar average selecting different cells for different vectors.

### Exact scope of this obstruction

Equation (17) refutes the proposed shortcut

> “Apply Möbius inversion to the full source, then discard the inverse remainder in a whole-line transform.”

It does **not** refute the required signed bound. In particular:

- \(Q^\mu_{m,z}\), whose left-exterior mass grows, is the **arithmetic source-inversion remainder**.
- \(\mathcal C_m(z)\) in (13) is the **finite-window complementary-projection correlation**.

They are different objects. Equation (17) supplies no lower bound or unfavorable sign for \(\mathcal C_m\), \(U_m\), or the Weil form.

No off-critical-line zero term was assigned a sign or omitted from a positivity argument. The two chosen zeros are only detecting linear Fourier moments.

## 6. The remaining signed comparison

Retain the original low arithmetic form and explicit Type I endpoints. Equation (15) gives
\[
\boxed{
\mathscr R_m(z)=
\mathscr P_m^{\rm low}(z)+\mathrm{End}_m(z)
+\mathcal F_m(z)-\mathcal C_m(z)+e_m(z),
\qquad
|e_m(z)|\le\eta_m\widehat E_m(z).
}
\tag{23}
\]

Thus a sufficient estimate in these coordinates is
\[
\boxed{
\begin{aligned}
\mathcal C_m(z)-\mathcal F_m(z)\ge{}&
\mathscr P_m^{\rm low}(z)+\mathrm{End}_m(z)\\
&-
\left(
\kappa_m+\frac1{256m}-\eta_m
\right)\widehat E_m(z)
\end{aligned}
}
\tag{24}
\]
for every complex \(z\), on **one unbounded original subsequence**.

For example, a bound with \(\kappa_m+1/(512m)\) before paying \(\eta_m\) would suffice eventually.

**I have not proved (24).** Writing it is not itself progress on the sign. The substantive estimates obtained here are the local full-source cancellation (11), its relative mixed-form bound (15), and the source-specific obstruction (17) to discarding its whole-line remainder.

The positive image and pole compensation can remain in the complete \(\widehat{\mathsf Q}_m\) test. Replacing its prime part by
\[
\mathscr P_m^{\rm low}+\mathrm{End}_m+\mathcal F_m-\mathcal C_m
\]
changes the normalized quadratic form by at most
\[
\varepsilon_m^{I}+\eta_m.
\]
Neither positive term needs to be deleted. The existing full-form budget can be used with that error, provided positivity is established before applying the lower metric bound.

## 7. Checks and conclusion

The preregistered controls produced **735 exact symbolic checks**, covering Möbius source cancellation, the fixed derivative polynomial, product-cut endpoints and empty ranges, complex mixed-form subtraction, and the two-evaluation rank test. Twelve finite numerical checks tested the elementary power-sum constants; these are diagnostics, not interval or source-sign certificates.

No new source-matrix spectral computation, Lean run, repository write, or independent audit of this new derivation was performed.

**The source does provide an exact cancellation unavailable to arbitrary phase-matched coefficients. But its passage through the finite projection still requires the signed correlation (24). That estimate remains unproved; the original \(U_m\) discriminator, G1, G3 and RH remain open.**

:chatgpt-content-reference{index="8"}[Complete PAPER derivation, explicit constants, source-return obstruction, and executable checks](sandbox:/mnt/data/PROSHKA_G1_MOBIUS_SOURCE_RETURN_2026-10-06.md)
