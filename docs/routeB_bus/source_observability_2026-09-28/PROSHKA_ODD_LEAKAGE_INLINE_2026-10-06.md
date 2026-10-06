Ы. **I can now prove a cofinal source estimate for an explicit odd test. I have not yet proved the comparison with the prescribed \(U_m\), so the eventual sign remains unresolved.**

The new estimate is substantially stronger than merely producing an odd Rayleigh quotient tending to zero. There is an explicitly defined sequence of unit odd vectors \(y_m\), in the **original carrier \(N=m\)**, such that

\[
\boxed{
\max\!\left\{
|y_m^*K_m^-y_m|,
|y_m^*A_m^-y_m|
\right\}
\le \mathcal B_m,
\qquad
\forall C>0:\quad
e^{Cm/\log m}\mathcal B_m\longrightarrow0.
}
\tag{1}
\]

Here **\(A_m^-\)** is exactly the pole-removed odd block from the request. Its positivity is **not** assumed.

Consequently, **any** source-proved lower bound

\[
\boxed{
U_m\ge c\,e^{-C_0m/\log m}
}
\tag{2}
\]

with fixed \(c,C_0>0\), on an unbounded admitted sequence, would refute this particular two-column candidate. The explicit \(y_m\) would eventually have energy below \(U_m\), including for \(A_m^-\). What is missing is precisely that signed lower comparison—not the construction of an odd competitor.

I retain your exact definition of \(U_m\), its actual Gram matrix, and the original schedule. No true ground energy is substituted. :chatgpt-content-reference{index="0"}

## 1. The odd construction

Write

\[
L=\log m,\qquad a=L/2,\qquad \Omega=\frac{2\pi m}{L}.
\]

Keep the complete source

\[
G(t)=e^{t/2}\sum_{q\ge1}
\left(24\pi q^2e^{2t}-16\pi^2q^4e^{4t}\right)
e^{-\pi q^2e^{2t}},
\]

and start from Codex’s odd profile

\[
H=G'''-\frac14G',
\qquad
\widehat H(z)=-iz(z^2+1/4)\widehat G(z).
\tag{3}
\]

The two zero factors have different jobs: \(\widehat G\) vanishes at the zeta-zero points, while \(z^2+1/4\) kills both pole evaluations. This is the source profile identified in the attached attempt. :chatgpt-content-reference{index="1"}

Rather than assume that the fixed plane \(\{G',G'''\}\) wins, define a **compact convolution**—a repeated local average—of \(H\):

\[
\delta_m=\frac14\log L,
\qquad
r_m=\left\lfloor\frac{\delta_m\Omega}{e}\right\rfloor ,
\]

\[
b_m(t)=\frac{r_m}{2\delta_m}
\mathbf1_{[-\delta_m/r_m,\delta_m/r_m]}(t),
\qquad
\eta_m=b_m^{*r_m},
\qquad
h_m=H*\eta_m.
\tag{4}
\]

These definitions are used for sufficiently large \(m\), so \(r_m\ge1\).

The kernel \(\eta_m\) is even, nonnegative, has integral one and is supported in \([-\delta_m,\delta_m]\). Its exact Fourier transform is

\[
\boxed{
\widehat\eta_m(z)
=
\operatorname{sinc}\!\left(\frac{\delta_m z}{r_m}\right)^{r_m},
\qquad
\operatorname{sinc}z=\frac{\sin z}{z},
\quad \operatorname{sinc}0=1.
}
\tag{5}
\]

Therefore \(h_m\) is odd and preserves **all** the zeros in (3).

This changes only the admissible odd test. It does **not** change \(U_m\), \(K_m\), the window \([-L/2,L/2]\), or the retained modes.

### Exact radical cancellation

Let \(\mathcal W\) denote the complete Weil form, \(\mathcal P\) its two-pole term, and

\[
\mathcal A=\mathcal W-\mathcal P=-W_{\mathbb R}-\mathrm{Prime}.
\]

The explicit formula and the rapidly decreasing cutoff argument give

\[
\boxed{
\mathcal W(h_m,f)=
\mathcal P(h_m,f)=
\mathcal A(h_m,f)=0.
}
\tag{6}
\]

This holds for each \(m\) and every finite-window test needed below. The extension is justified exactly as for \(G,G''\): weighted integration by parts controls the zero sum, while exponential weights control the complete prime-power sum. Convolution merely multiplies the entire Fourier transform by (5), so it does not remove any required zero. The underlying explicit formula is the signed formula, not Weil positivity. :chatgpt-content-reference{index="2"}

The construction also remains nontrivial. The second moment of the averaging kernel is

\[
\int t^2\eta_m(t)\,dt=\frac{\delta_m^2}{3r_m}.
\]

Hence the translation inequality gives

\[
\boxed{
\|h_m-H\|_2
\le
\|H'\|_2\frac{\delta_m}{\sqrt{3r_m}}
\longrightarrow0.
}
\tag{7}
\]

Here \(H\ne0\): otherwise \(G'''-G'/4=0\), incompatible with a nonzero, two-sided rapidly decreasing \(G\).

## 2. The Fourier estimate uses the full theta sum

The following estimate is useful independently of the convolution construction:

\[
\boxed{
|\widehat G(\omega)|
\le C_F|\omega|^{5/2}e^{-\pi|\omega|/4},
\qquad |\omega|\ge2,
\qquad C_F=48e(\pi/4)^{5/2}.
}
\tag{8}
\]

It can be proved directly from the source, without an estimate for \(\zeta\) on the critical line.

The Gaussian sum is analytic for \(|\Im t|<\pi/4\). Its real evenness, supplied by the theta identity, extends to this strip. For \(0\le b<\pi/4\), put \(c=\cos(2b)>0\). Substituting \(u=qe^t\) on \(t\ge0\), and using

\[
\sum_{q\le u}q^{-1/2}\le2\sqrt u,
\]

gives

\[
\begin{aligned}
\int_0^\infty |G(t+ib)|\,dt
&\le
48\pi\int_0^\infty u^2e^{-\pi c u^2}\,du
+
32\pi^2\int_0^\infty u^4e^{-\pi c u^2}\,du\\
&=12c^{-3/2}+12c^{-5/2}.
\end{aligned}
\]

The other half-line has the same bound. Thus

\[
\int_{\mathbb R}|G(t+ib)|\,dt\le48c^{-5/2}.
\]

For positive \(\omega\), shift the Fourier contour downward by

\[
b=\pi/4-1/\omega.
\]

The vertical sides vanish by the same Gaussian estimate. Since

\[
\cos(2b)=\sin(2/\omega)\ge\frac4{\pi\omega},
\]

we obtain (8). Negative frequencies follow by symmetry.

From (3),

\[
|\widehat H(\omega)|
\le 2C_F|\omega|^{11/2}e^{-\pi|\omega|/4}.
\tag{9}
\]

Now the averaging kernel supplies an additional factor. For \(|\omega|\ge\Omega\),

\[
\begin{aligned}
|\widehat\eta_m(\omega)|
&\le
\left(\frac{r_m}{\delta_m|\omega|}\right)^{r_m}\\
&\le
e^{-r_m}
\left(\frac{\Omega}{|\omega|}\right)^{r_m}
\le e^{-r_m}.
\end{aligned}
\tag{10}
\]

**The growing order \(r_m\) is not hidden in an uncontrolled derivative constant.** Only the fixed functions \(H,H',H'',H'''\) will be estimated physically.

For the original frequency lattice \(\omega_n=2\pi n/L\), define

\[
S_k=\frac1L\sum_{|n|>m}
|\omega_n^k\widehat h_m(\omega_n)|^2,
\qquad k=0,1.
\]

Equations (9)–(10) give

\[
\boxed{
S_k\le C_k\Omega^{11+2k}
e^{-\pi\Omega/2-2r_m},
\qquad k=0,1,
}
\tag{11}
\]

with constants independent of both \(m\) and \(r_m\).

For completeness, one explicit choice is

\[
C_k=\frac{4C_F^2}{\pi}J_{11+2k},
\qquad
J_p=\int_0^\infty(2+t)^p e^{-\pi t/2}\,dt.
\]

When \(L\ge2\pi\), the lattice spacing is at most one; comparison of each summand with the preceding unit-bounded cell proves this discrete estimate. There is no replacement of the frequency sum by an unproved sampling asymptotic.

## 3. The endpoints are controlled separately

The full-source derivatives satisfy bounds of the form

\[
|H^{(k)}(t)|
\le D_k\exp\!\left[-\frac\pi2e^{2|t|}\right],
\qquad 0\le k\le3,
\tag{12}
\]

with fixed, explicitly constructible constants.

A convenient construction starts from

\[
P_0(v)=24v-16v^2,
\qquad
P_{k+1}(v)=(1/2-2v)P_k(v)+2vP_k'(v).
\]

Then \(G^{(k)}\) is the complete Gaussian sum with polynomial \(P_k\), and \(H^{(k)}\) uses \(P_{k+3}-P_{k+1}/4\). Bounding the finitely many polynomial coefficients against the Gaussian gives (12). No theta truncation enters.

Because \(\eta_m\) has support in \([-\delta_m,\delta_m]\), for \(t\ge a\),

\[
|h_m^{(k)}(t)|
\le
D_k\exp\!\left[-\frac\pi2 e^{2(t-\delta_m)}\right].
\]

Write

\[
\boxed{
X_m=e^{2(a-\delta_m)}=\frac m{\sqrt L}.
}
\]

Consequently,

\[
|h_m^{(k)}(a)|\le D_ke^{-\pi X_m/2},
\]

\[
\int_{|t|>a}|h_m^{(k)}(t)|^2dt
\le\frac{D_k^2}{\pi X_m}e^{-\pi X_m},
\qquad k=0,1,
\tag{13}
\]

and

\[
\int_{|t|>a}e^{2|t|}|h_m(t)|^2dt
\le
\frac{D_0^2e^{2\delta_m}}{\pi}e^{-\pi X_m}.
\tag{14}
\]

### The odd endpoint term must not be dropped

Let \(f_m\) be the literal finite Fourier projection of \(h_m\), zero-extended outside the original window, and set

\[
e_m=f_m-h_m.
\]

Oddness gives \(c_{-n}=-c_n\), \(c_0=0\), and therefore

\[
f_m(-a)=f_m(a)=0.
\]

Thus \(f_m,e_m\in H^1(\mathbb R)\).

But \(h_m(a)\) need not vanish. In the original coefficient convention, integration by parts gives

\[
\boxed{
c_n(h_m')
=i\omega_nc_n(h_m)+\frac{2h_m(a)}{\sqrt L}.
}
\tag{15}
\]

Parseval therefore yields the exact identity

\[
\boxed{
\begin{aligned}
\|e_m'\|_2^2
={}&
\sum_{|n|>m}|c_n(h_m')|^2
+\frac{4(2m+1)}L|h_m(a)|^2\\
&+\int_{|t|>a}|h_m'(t)|^2dt.
\end{aligned}
}
\tag{16}
\]

The middle term is essential.

To compare the actual coefficients with full Fourier samples, exterior integration by parts gives

\[
\left|
c_n(h_m)-\frac{(-1)^n}{\sqrt L}\widehat h_m(\omega_n)
\right|
\le
\frac{2R_0}{\sqrt L|\omega_n|},
\]

where

\[
R_0=|h_m(a)|+\int_a^\infty|h_m'(t)|dt.
\]

For the even function \(h_m'\), the exact identity \(\sin(\omega_na)=0\) permits another integration by parts:

\[
\left|
c_n(h_m')-\frac{(-1)^n}{\sqrt L}\widehat h_m'(\omega_n)
\right|
\le
\frac{2R_2}{\sqrt L\omega_n^2},
\]

\[
R_2=|h_m''(a)|+\int_a^\infty|h_m'''(t)|dt.
\]

Summing these bounds, and using (11)–(16), proves

\[
\boxed{
\|e_m\|_2^2
\le C_H\left[
\Omega^{11}e^{-\pi\Omega/2-2r_m}
+\frac Lm e^{-\pi X_m}
\right],
}
\tag{17}
\]

\[
\boxed{
\|e_m'\|_2^2
\le C_H\left[
\Omega^{13}e^{-\pi\Omega/2-2r_m}
+\frac mL e^{-\pi X_m}
\right].
}
\tag{18}
\]

All constants here are fixed-source constants. The attached derivation supplies their unsimplified formulas, including the complete boundary budget.

## 4. Passing to the full matrix energy

This is where the prime and archimedean terms must remain.

For \(e\in H^1(\mathbb R)\) with \(W_e=\|e^{|t|}e\|_2<\infty\), define

\[
\mathfrak D(e)
=
\int_0^\infty
\frac{e^{-x/2}}{1-e^{-2x}}
\|e-\tau_xe\|_2^2\,dx.
\]

Grouping the original archimedean subtraction at zero gives

\[
\mathcal A(e,e)
=
\mathfrak D(e)
-c_{\rm ar}\|e\|_2^2
-\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{e,e}(\log n),
\]

\[
c_{\rm ar}=\gamma+\log(8\pi)+\pi/2.
\tag{19}
\]

This is the complete pole-removed form, with the same sign convention as the literal matrix definitions. 

Weighted Cauchy–Schwarz gives

\[
|Q_{e,e}(\log n)|\le2n^{-1}W_e^2,
\]

so **all prime powers together** satisfy

\[
\left|
\sum_{n\ge2}\frac{\Lambda(n)}{\sqrt n}Q_{e,e}(\log n)
\right|
\le
2W_e^2\sum_{n\ge2}\frac{\log n}{n^{3/2}}
<10W_e^2.
\tag{20}
\]

The two-pole term satisfies

\[
|\mathcal P(e,e)|\le\frac83W_e^2.
\]

Thus, with \(C_W=c_{\rm ar}+13\),

\[
\max\{|\mathcal W(e,e)|,|\mathcal A(e,e)|\}
\le\mathfrak D(e)+C_WW_e^2.
\tag{21}
\]

There is no assumed positivity in this estimate.

The translation bound

\[
\|e-\tau_xe\|_2
\le\min\{x\|e'\|_2,\,2\|e\|_2\}
\]

and a split at \(x=1/\Omega\) and \(x=1\) give

\[
\mathfrak D(e)
\le
\Omega^{-2}\|e'\|_2^2
+(8\log\Omega+16)\|e\|_2^2.
\tag{22}
\]

Also,

\[
W_{e_m}^2
\le
m\|e_m\|_2^2
+\frac{D_0^2e^{2\delta_m}}{\pi}e^{-\pi X_m}.
\tag{23}
\]

Now use the exact radical identity (6):

\[
\boxed{
\mathcal W(f_m,f_m)=\mathcal W(e_m,e_m),
\qquad
\mathcal A(f_m,f_m)=\mathcal A(e_m,e_m).
}
\tag{24}
\]

This does **not** declare a finite projection to be null. Its entire energy is carried by the explicitly bounded error.

The general finite wrapper identifies these two form values with the original full and pole-removed coefficient-matrix values. 

From (7), (17), and \(H\ne0\),

\[
\|f_m\|_2\longrightarrow\|H\|_2>0.
\]

Therefore the unit odd vector

\[
\boxed{
y_m=
\frac{E_-^*c_m(h_m)}{\|c_m(h_m)\|_2}
}
\tag{25}
\]

is defined eventually. Combining (17)–(24) proves

\[
\boxed{
\max\{|y_m^*K_m^-y_m|,|y_m^*A_m^-y_m|\}
\le
C_H\left[
m\Omega^{11}e^{-\pi\Omega/2-2r_m}
+
L e^{-\pi m/\sqrt L}
\right].
}
\tag{26}
\]

This is the claimed **full-source odd Rayleigh upper envelope**.

## 5. Its rate is stronger than every fixed exponential in \(m/\log m\)

Since

\[
r_m\ge\frac{\delta_m\Omega}{e}-1,
\]

the first term in (26) is bounded by a fixed constant times

\[
m\Omega^{11}
\exp\!\left[
-\left(\pi^2+\frac\pi e\log L\right)\frac mL
\right].
\tag{27}
\]

The second term is

\[
L\exp\!\left[-\frac{\pi m}{\sqrt L}\right].
\]

For every fixed \(C>0\), both expressions multiplied by \(e^{Cm/L}\) tend to zero. This proves (1).

The estimate applies to **every sufficiently large integer \(m\)**. Restricting it to the original selected schedule therefore needs no new subsequence or extrapolation.

The endpoint budget is smaller than the displayed Fourier-tail budget. This is a comparison of **proved upper envelopes**. It is not a lower bound for the actual omitted-mode energy, whose signed contributions can cancel further.

## 6. A separate estimate isolates the window correction in the original \(U_m\)

For \(g=G,G''\), introduce the comparison coefficients

\[
\widetilde c_m(g)_n
=
\frac{(-1)^n}{\sqrt L}\widehat g(\omega_n),
\qquad |n|\le m.
\]

Let \(\widetilde U_m\) be the minimum Rayleigh quotient on their two-column span, **still using the original full \(K_m\)**.

These samples are only an auxiliary comparison. The prescribed \(U_m\) remains the window-coefficient minimum.

The physical Gaussian bounds imply

\[
\|V_m-\widetilde V_m\|_{\rm op}
\le
\frac{C_G}{\sqrt{mL}}e^{-\pi m/2}.
\tag{28}
\]

The complete source entries give the coarse but sufficient estimate

\[
\|K_m\|_{\rm op}\le100m^2L.
\]

For this bound, the pole entries, full prime-power entries and grouped archimedean entries are bounded separately; their small spectral cancellation is not being used to infer a sign.

The limiting two-column Gram matrix is

\[
\begin{pmatrix}
\|G\|_2^2&-\|G'\|_2^2\\
-\|G'\|_2^2&\|G''\|_2^2
\end{pmatrix}\succ0.
\]

Its strict positivity follows from independence of \(G,G''\). Consequently normalized vectors corresponding to the same coefficient pair in \(V_m\) and \(\widetilde V_m\) differ by \(O(\|V_m-\widetilde V_m\|)\). Comparing their Rayleigh quotients and taking minima yields

\[
\boxed{
|U_m-\widetilde U_m|
\le
\Gamma_m
=
C_G' m^{3/2}\sqrt L\,e^{-\pi m/2}.
}
\tag{29}
\]

Thus **the window-coefficient correction cannot contribute a leading term of fixed scale \(e^{-Cm/L}\)**. Its bound is much smaller.

However, this does not establish that \(\widetilde U_m\), or \(U_m\), has a positive leading term on that scale.

## 7. The remaining signed inequality

For the explicitly constructed vector (25),

\[
\boxed{
\begin{aligned}
y_m^*(K_m^- -U_mI)y_m&\le\mathcal B_m-U_m,\\
y_m^*(A_m^- -U_mI)y_m&\le\mathcal B_m-U_m.
\end{aligned}
}
\tag{30}
\]

Therefore the remaining sufficient inequality for **this negative-witness construction** is

\[
\boxed{
U_m>\mathcal B_m
}
\tag{31}
\]

on an unbounded admitted sequence. Using the paid window correction, it suffices instead to prove

\[
\boxed{
\widetilde U_m>\mathcal B_m+\Gamma_m.
}
\tag{32}
\]

A particularly useful source lower bound would be

\[
z^*\widetilde V_m^*K_m\widetilde V_mz
\ge
c\,e^{-C_0m/L}\,
z^*\widetilde V_m^*\widetilde V_mz
\qquad(z\in\mathbb C^2),
\tag{33}
\]

with fixed positive \(c,C_0\), on an unbounded original sequence. The rows of the comparison matrix are explicit:

\[
\widetilde V_{m,n,:}
=
\frac{(-1)^n}{\sqrt L}
\widehat G(\omega_n)\,(1,-\omega_n^2).
\]

**Equation (33) still requires a signed estimate of the complete two-column energy, including its mixed terms.** Neither an \(L^2\) lower bound for the discarded Fourier coefficients nor the numerical fact that \(U_m\) is positive in the sampled cells proves it.

If (2) is established, (30) becomes a genuine negative upper envelope:

\[
y_m^*(K_m^- -U_mI)y_m,\quad
y_m^*(A_m^- -U_mI)y_m
\le
-\frac c2e^{-C_0m/L}<0
\]

on the sufficiently late part of that sequence. That would refute this \(U_m\), already at the positive-\(M_m\) prerequisite.

**I have not proved (31)–(33).** The finite observations remain diagnostics and are not promoted into this missing lower bound. Their stated limitations are retained. :chatgpt-content-reference{index="5"}

The resulting next calculation is now specific: **the signed two-column lower bound (32), with the full-Fourier-sample comparison (29)**. We do not need an odd eigensolver to supply the competing asymptotic upper bound; (25)–(26) already supply it.

The polynomial recurrence and the boundary identity passed exact symbolic controls. In particular, the test \(h(t)=t\) on \([-\pi,\pi]\), \(m=1\), gives derivative error \(6\pi\), entirely recovered by the endpoint term in (16); omitting it gives the false answer zero. The full analytical derivation has not yet received an independent audit.

:chatgpt-content-reference{index="7"}[Complete PAPER derivation: explicit constants, unsimplified error budgets, source locks, checks, and the exact remaining inequality](sandbox:/mnt/data/PROSHKA_ODD_SOURCE_LEAKAGE_DISCRIMINATOR_2026-10-06.md)
