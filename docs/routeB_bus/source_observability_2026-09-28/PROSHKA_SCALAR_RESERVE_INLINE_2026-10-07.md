# Q8 native answer

Chat: 6ac58a1c-1568-83ed-95d0-857526e2b6cb
Answer: 3c583de5-f233-4474-9025-965d15cc8865
Native status: completed; source reference markers retained verbatim. Root subsequently read the entire linked PAPER artifact in its rendered preview; see SCALAR_RESERVE_AUDIT_2026-10-07.md.

Ы — **the entire convexity-loss tail is paid, but the signed arithmetic reserve remains open.** For every integer \(Q\ge64\), the exact losses satisfy
\[
\boxed{
\sum_{\substack{q>Q\\q\ \mathrm{prime\ power}}}\ell_q
\le \frac{18\log Q+24}{\sqrt Q}.
}
\]
This is an unconditional bound on the **whole infinite tail**, not a numerical-prefix result.

The bounded explicit-formula attempt also gives a uniform reserve estimate
\[
E_q\ge-C_E\sqrt q\,e^{-\alpha\sqrt{\log q}}
\]
at **every sufficiently large prime power**. It does not give \(E_q\ge d_q\): the proved lower envelope is negative and grows in magnitude.

There is also a useful qualification to the proposed falsifier: **a finite failure \(E_q<d_q\) is not automatically a tail obstruction, but a certified \(E_q\le0\) would be stronger for this exact source.** The calculation below shows that it would force a negative actual Suzuki value. No such event is established here.

:chatgpt-content-reference{index="7"}[Complete PAPER verdict, proofs, source mapping, and limitations](sandbox:/mnt/data/PROSHKA_VERDICT_SCALAR_ARITHMETIC_RESERVE_Q08_2026-10-07.md)

## 1. Pay the complete convexity loss

**[COFINAL_FAMILY | PAPER]**

At an event \(q=p^k\), retain
\[
a_q=\frac{\log p}{\sqrt q},\qquad
y_{q-}=A(q^-)-c,
\]
and write the supplied loss as
\[
\ell_q
=2\left[(y_{q-}+a_q)\log(1+a_q/y_{q-})-a_q\right].
\]

The first needed estimate is a lower bound for the **actual pre-jump denominator**, not its expected asymptotic.

Let
\[
\psi_{\rm Ch}(x)=\sum_{n\le x}\Lambda(n).
\]
For every integer \(n\ge1\),
\[
\psi_{\rm Ch}(2n)\ge\log\binom{2n}{n}
\ge2n\log2-\log(2n+1).
\]
Indeed, each term
\[
\left\lfloor\frac{2n}{p^j}\right\rfloor
-2\left\lfloor\frac n{p^j}\right\rfloor
\]
in the prime factorization of the binomial coefficient is zero or one. Its exponent at \(p\) is therefore at most \(\lfloor\log_p(2n)\rfloor\), which proves the first inequality. The second follows because the central coefficient is the largest of \(2n+1\) coefficients summing to \(2^{2n}\).

Taking \(n=\lfloor q/2\rfloor\) and removing the event at \(q\) gives
\[
\psi_{\rm Ch}(q^-)
\ge(q-2)\log2-\log(q+1)-\log q
\ge q/2,\qquad q\ge64.
\]
The last inequality follows by checking its elementary lower bound at \(64\) and observing that the difference is increasing thereafter.

Since \(c<0\),
\[
\boxed{
y_{q-}\ge A(q^-)
\ge\frac{\psi_{\rm Ch}(q^-)}{\sqrt q}
\ge\frac{\sqrt q}{2}.
}
\tag{1}
\]

We also have an elementary complete-source upper count. Prime powers in \((n,2n]\) contribute to the same central binomial coefficient, so
\[
\psi_{\rm Ch}(2n)-\psi_{\rm Ch}(n)
\le\log\binom{2n}{n}\le2n\log2.
\]
Iteration on powers of two, followed by upward dyadic rounding, proves
\[
\boxed{\psi_{\rm Ch}(x)\le4(\log2)x<3x.}
\tag{2}
\]

Now use the exact integral representation
\[
\ell_q=2\int_0^{a_q}\frac{a_q-u}{y_{q-}+u}\,du.
\]
It gives
\[
0\le\ell_q\le\frac{a_q^2}{y_{q-}}
\le\frac{2\Lambda(q)^2}{q^{3/2}}
\le\frac{2\Lambda(q)\log q}{q^{3/2}}.
\]

For \(f(x)=x^{-3/2}\log x\), decreasing on \([64,\infty)\), partial summation with (2) yields
\[
\begin{aligned}
\sum_{n>Q}\frac{\Lambda(n)\log n}{n^{3/2}}
&=-\psi_{\rm Ch}(Q)f(Q)
-\int_Q^\infty\psi_{\rm Ch}(x)f'(x)\,dx\\
&\le3\int_Q^\infty x^{-3/2}
\left(\frac32\log x-1\right)\,dx\\
&=\frac{9\log Q+12}{\sqrt Q}.
\end{aligned}
\]
The lower boundary has the favorable sign; the boundary at infinity vanishes.

Therefore
\[
\boxed{
0\le\sum_{\substack{q>Q\\q\ {\rm prime\ power}}}\ell_q
\le\mathfrak L(Q):=\frac{18\log Q+24}{\sqrt Q},
\qquad Q\ge64.
}
\tag{3}
\]

All prime powers were retained. No prime-count asymptotic, RH assumption, or finite table entered this proof.

## 2. The reserve cancels the instantaneous linear error

**[FINITE_CELL | PAPER]**

Use the complete source in Suzuki’s equation (1.1). Its pole and Lerch terms combine exactly to
\[
\Psi(t)=4e^{t/2}+ct+b-R(t)
-\sum_n\frac{\Lambda(n)}{\sqrt n}(t-\log n)_+.
\tag{4}
\]
The PDF was checked to be the requested **v4**. No term from its source has been removed. :chatgpt-content-reference{index="0"}

For real \(x\ge1\), define
\[
\delta(x)=A(x)-c-2\sqrt x,\qquad
u(x)=\frac{A(x)-c}{2\sqrt x},
\]
and the nonnegative **convex remainder**
\[
\mathcal D(x)
=4\sqrt x\,[u(x)\log u(x)-u(x)+1].
\]
This \(\mathcal D\) is distinct from the supplied prime sum \(D(x)\).

Finite partial summation gives
\[
D(x)=A(x)\log x-\int_1^x\frac{A(v)}v\,dv.
\]
Substituting this into the reserve, with \(A=y+c\), first cancels the \(c\)-terms and then gives
\[
\boxed{
E_x=4+b-\int_1^x\frac{\delta(v)}v\,dv-\mathcal D(x).
}
\tag{5}
\]
At a prime-power event, equivalently,
\[
\boxed{
E_q=\Psi(\log q)+R(\log q)-\mathcal D(q).
}
\tag{6}
\]

The important cancellation is that **the instantaneous term \(\delta(q)\log q\) is gone**. What remains instantaneously is quadratic, with an unfavorable but known sign.

When \(|u(q)-1|\le1/2\), the second derivative \(1/u\) of \(u\log u-u+1\) lies between \(2/3\) and \(2\). Consequently,
\[
\boxed{
\frac{\delta(q)^2}{3\sqrt q}
\le\mathcal D(q)
\le\frac{\delta(q)^2}{\sqrt q}.
}
\tag{7}
\]
Neither (5) nor (7) assumes a sign for \(\delta\) or \(\Psi\).

## 3. Execute the unconditional explicit-formula estimate at the jumps

**[COFINAL_FAMILY | PAPER]**

The specific proved input is Suzuki’s Theorem 1.1(3):
\[
|\Psi(t)|\le C_\Psi e^{t/2-\alpha\sqrt t},
\qquad t\ge T_\Psi,
\tag{8}
\]
for some \(C_\Psi\ge1\) and \(0<\alpha\le1\). These constants exist by the theorem; no numerical values or explicit numerical threshold are asserted here. This is an unconditional estimate for the exact function (4). :chatgpt-content-reference{index="1"}

**Differentiating the big-\(O\) estimate would be invalid.** Instead, the arithmetic source supplies a one-sided derivative constraint:
\[
\boxed{
\Psi''=
\left(e^{t/2}-\frac{e^{-5t/2}}{1-e^{-2t}}\right)dt
-\sum_q a_q\delta_{\log q}
\preceq e^{t/2}dt.
}
\tag{9}
\]
Every prime-power jump is present, with its negative sign.

Fix \(t\ge\max(T_\Psi+1,2)\), and put
\[
h=e^{-\alpha\sqrt t/2},\qquad
M_t=e^{(t+1)/2}.
\]
On \([t-1,t+1]\), (8) implies
\[
|\Psi(v)|\le C_\Psi e^{3/2}e^{t/2-\alpha\sqrt t}.
\]
Integrating (9) forward and backward gives
\[
\begin{aligned}
\Psi'_+(t)&\ge
\frac{\Psi(t+h)-\Psi(t)}h-\frac{M_th}{2},\\
\Psi'_-(t)&\le
\frac{\Psi(t)-\Psi(t-h)}h+\frac{M_th}{2}.
\end{aligned}
\]
Because \(\Psi'_+(t)\le\Psi'_-(t)\), both one-sided slopes satisfy
\[
|\Psi'_\pm(t)|
\le
\left(2e^{3/2}C_\Psi+\frac{e^{1/2}}2\right)
e^{t/2-\alpha\sqrt t/2}.
\tag{10}
\]
This covers event times and intervening events; it assumes no prime-gap estimate.

The exact remainder obeys
\[
0<-R'(t)\le\frac25\frac{e^{-5t/2}}{1-e^{-2t}}.
\]
Since
\[
\delta(e^t)=-\Psi'_+(t)-R'(t)
\]
and the pre-jump value uses \(\Psi'_-(t)\), setting
\[
C_\delta=2e^{3/2}C_\Psi+2
\]
gives
\[
\boxed{
|A(e^t\pm)-c-2e^{t/2}|
\le C_\delta e^{t/2-\alpha\sqrt t/2}.
}
\tag{11}
\]

In particular, (7) holds above
\[
T_1=\max\!\left(
T_\Psi+1,\ 2,\
\frac{4(\log C_\delta)^2}{\alpha^2}
\right).
\]
Combining (6), (7), (8), and (11) proves
\[
\boxed{
\begin{aligned}
-(C_\Psi+C_\delta^2)\sqrt q\,e^{-\alpha\sqrt{\log q}}
&\le E_q\\
&\le C_\Psi\sqrt q\,e^{-\alpha\sqrt{\log q}}+d_q,
\qquad \log q\ge T_1.
\end{aligned}}
\tag{12}
\]

This is a **uniform every-event estimate**. The half-exponent loss in the slope bound is squared in (7), so it does not further degrade the exponential saving in the reserve.

But
\[
\sqrt q\,e^{-\alpha\sqrt{\log q}}\longrightarrow\infty,
\qquad
d_q\asymp q^{-5/2}.
\]
Thus (12) does not reach the required positive reserve. Its negative lower envelope is a limitation of this estimate, **not evidence that \(E_q\) actually becomes negative**.

## 4. The exact unpaid arithmetic is now only the signed drift

**[FINITE_CELL | PAPER]**

For a prime-power anchor \(Q\ge64\), define
\[
\mathcal S_Q(q)=
\sum_{\substack{Q<v\le q\\v\ {\rm prime\ power}}}
\frac{\Lambda(v)}{\sqrt v}
\log\frac{4v}{y_{v-}^{\,2}},
\qquad
\mathcal L_Q(q)=\sum_{Q<v\le q}\ell_v.
\]
The complete jump budget is
\[
\boxed{
E_q-d_q
=
E_Q+\mathcal S_Q(q)-\mathcal L_Q(q)-d_q,
\qquad
0\le\mathcal L_Q(q)\le\mathfrak L(Q).
}
\tag{13}
\]

Hence any proved lower estimate for the **actual** \(\mathcal S_Q(q)\) can now be spent with an explicit all-future loss. What remains to establish is
\[
\boxed{
\mathcal S_Q(q)
\ge -E_Q+\mathcal L_Q(q)+d_q
\quad\text{for every prime power }q\ge Q,
}
\tag{14}
\]
above one anchor \(Q\).

The bounded attempt gives only, with
\[
G(q)=\sqrt q\,e^{-\alpha\sqrt{\log q}},
\]
\[
\begin{aligned}
\mathcal S_Q(q)&\ge-E_Q-(C_\Psi+C_\delta^2)G(q),\\
\mathcal S_Q(q)&\le-E_Q+C_\Psi G(q)+d_q+\mathfrak L(Q).
\end{aligned}
\]
The first is not a uniform finite lower barrier. Its divergence does not establish that the actual infimum of \(\mathcal S_Q\) is \(-\infty\).

The exact zero formula also does not furnish the missing sign automatically. Grouping the actual zeros by their genuine symmetries gives
\[
\begin{aligned}
\Psi(t)={}&
2\sum_{\substack{\rho=1/2+i\gamma\\\gamma>0}}
r_\rho\frac{1-\cos(\gamma t)}{\gamma^2}\\
&+4\sum_{\substack{\beta>1/2\\\gamma>0}}
r_\rho\Re
\frac{\cosh((\beta-\tfrac12+i\gamma)t)-1}
{(\beta-\tfrac12+i\gamma)^2}.
\end{aligned}
\tag{15}
\]
This is the complete source identity, with no zero truncation. The first sum is nonnegative; the second has no sign supplied by this calculation. Declaring every summand nonnegative would assume the missing zero-location statement. Suzuki’s derivation retains the full zero sum and its multiplicities. :chatgpt-content-reference{index="2"}

**Stopping reason:** the convexity loss is summable, but the available verified estimate controls the magnitude—not the lower signed excursions—of the remaining prime-power drift. No new correlation input has been established that pays (14).

## 5. Keep the clipped minimum separate—and sharpen the finite discriminator

**[FINITE_CELL | PAPER]**

Let
\[
t_q^*=2\log(y_q/2).
\]
This is the unconstrained minimizer of the growing-pole part, **not the clipped minimum of the full Suzuki cell**.

On the original cell,
\[
\boxed{
\Psi(t)=E_q+
2y_q\left(
e^{(t-t_q^*)/2}-1-\frac{t-t_q^*}{2}
\right)-R(t).
}
\tag{16}
\]
The middle term is nonnegative. The full interior minimizer instead solves
\[
2e^{t/2}-R'(t)=y_q
\]
and must be clipped to \([\log q,\log q_{\rm next}]\).

Thus \(E_q<d_q\) alone does not establish a negative cell minimum. Even the conclusion \(t_q^*-\log q=o(1)\) from (11) does not place it inside the cell, whose width also shrinks.

There is, however, a stronger source-specific statement about **nonpositive \(E_q\)**. For \(t>0\), put
\[
\mathcal K_q(t)=
\begin{cases}
\displaystyle
\sum_{q<n\le e^t}\frac{\Lambda(n)}{\sqrt n}(t-\log n),
&e^t\ge q,\\[2mm]
\displaystyle
\sum_{e^t<n\le q}\frac{\Lambda(n)}{\sqrt n}(\log n-t),
&e^t<q.
\end{cases}
\]
Every summand is nonnegative. Comparing the prime sum stopped affinely at \(q\) with the actual positive-part sum in (4) gives
\[
\boxed{
E_q=\Psi(t_q^*)+R(t_q^*)+\mathcal K_q(t_q^*).
}
\tag{17}
\]

Moreover,
\[
-c=\frac{\gamma_E+\pi/2+3\log2+\log\pi}{2}>2,
\]
so \(y_q>2\) and \(t_q^*>0\). Since \(R(t)>0\),
\[
\boxed{
E_q\le0\quad\Longrightarrow\quad\Psi(t_q^*)<0.
}
\tag{18}
\]

This qualifies the finite-versus-eventual warning. A finite violation **\(E_q<d_q\)** is only a failure of the sufficient reserve unless more is shown. A certified actual **\(E_q\le0\)** would force a negative Suzuki value, contradict RH by Suzuki’s implication RH \(\Rightarrow\Psi(t)\ge0\) for all positive \(t\), and therefore also refute the eventual reserve lemma that implies RH. :chatgpt-content-reference{index="3"}

**No such event is found or claimed here.** A negative lower bound for \(E_q\), a sign-straddling interval, or the supplied floating diagnostic does not establish (18).

For a zero-consistent calculation, the precise finite discriminator is a certified upper bound for
\[
E_q-R(t_q^*)-\mathcal K_q(t_q^*).
\]
Strict negativity would certify an actual negative \(\Psi\), without confusing global and clipped minima.

## 6. Verdict and complete limitations

**What genuinely changed:** the entire infinite convexity-loss supplier now has the explicit bound (3). The source calculation cancels the instantaneous linear error in the reserve and controls its quadratic replacement at every late event. The exact identity (17) distinguishes ordinary reserve-certificate failure from an actual nonpositive reserve.

**What remains open:** the signed lower estimate (14), hence \(E_q\ge d_q\) on every sufficiently late prime-power cell. No source counterexample to that lemma is proved, and the calculation does not establish that it is too strong.

Were the requested every-late-cell reserve proved, (16) would give eventual nonnegativity of the complete \(\Psi\), and Suzuki’s Theorem 11.1 at \(\omega=0\) would supply the terminal implication. Sparse favorable cells do not satisfy that hypothesis. :chatgpt-content-reference{index="4"}

No approximation of \(K_m\), the source projectors, or \(J_r\) was made. Accordingly, **\(\Delta_{10}\) is neither spent nor improved here**: this is a different exact scalar sufficient test, not a repaired Schur budget. The previous SP target remains open as recorded in the original source pack. :chatgpt-content-reference{index="5"}

**Stop this bounded attempt at the unpaid signed drift.** Repeating the convexity-loss estimate will not address it. No replacement representation is selected without a new source lower estimate.

**RH, SP, G1/G3, and the actual Schur sign remain OPEN. These new PAPER derivations require independent audit.**
