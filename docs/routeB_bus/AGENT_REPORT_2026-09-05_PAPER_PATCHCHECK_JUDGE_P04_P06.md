# PATCHCHECK — independent verification (canonical.tex, groundstate.tex, setup.tex)

Only the three named files were read. `app:constants` ($M_0,M_1,M_2,A$) was NOT opened: everything
below is verified *conditional on* the Thm 3.2 envelope. Scripts: `p1a.py p1b.py p3.py p3sym.py p3full.py`.

## (1) Lemma 3.3 — CORRECT (all four claims)

**Envelope.** $|\Phi^{(j)}|\le AM_je^{-\frac\pi2e^{2|x|}}$, $f_0=\Phi/A\Rightarrow|f_0^{(j)}|\le M_je^{-\frac\pi2e^{2|x|}}$.
$|x-q|\ge|x|-|q|$ (valid also when $|x|<|q|$, as $|x-q|\ge0$) gives $e^{2|x-q|}\ge e^{-2|q|}e^{2|x|}$, hence
$|(U_qf_0)^{(j)}|\le M_je^{-a_qe^{2|x|}}$, $a_q=\frac\pi2e^{-2|q|}$. ✔

**Three integrals.** $y=e^{2|x|}$, $dx=dy/(2y)$, factor 2 for the two half-lines, $Y=e^{2R}\ge1$:
$I_1=\int_Y^\infty e^{-2ay}dy=\frac{e^{-2ae^{2R}}}{2a}$ (identity); $I_2=\int_Y^\infty y^{-1}e^{-2ay}dy=E_1(2aY)$;
$I_3=\int_Y^\infty y^{-3/4}e^{-ay}dy=a^{-1/4}\Gamma(\tfrac14,aY)$; $y^{-1},y^{-3/4}\le1$ give the majorants.
Checked at $(a,R)=(\frac\pi2,0),(\frac\pi2,1),(0.3,0),(0.3,0.7),(2,1.5),(0.05,2),(5,0)$:
$I_1$/claim$-1\le5\cdot10^{-12}$ (pure quadrature); $I_2$/claim $=0.7929,0.1300,0.4968,0.1861,0.0492,0.0158,0.9156$;
$I_3$/claim $=0.7431,0.2105,0.4536,0.2458,0.1035,0.0408,0.8853$. All $\le1$. ✔

**Three norms.** (i) $\le M_0^2I_1=\frac{M_0^2}{2a_q}e^{-2a_qe^{2R}}$ ✔.
(ii) $e_R'=(1-\chi_R)(U_qf_0)'-\chi_R'U_qf_0$, $|v+w|^2\le2|v|^2+2|w|^2$, then $I_2$:
$(2M_1^2+2c_\chi^2M_0^2)\frac{e^{-2a_qe^{2R}}}{2a_q}=\frac{M_1^2+c_\chi^2M_0^2}{a_q}e^{-2a_qe^{2R}}$ — the stated constant exactly ✔.
(iii) $e_R''=(1-\chi_R)(U_qf_0)''-2\chi_R'(U_qf_0)'-\chi_R''U_qf_0$, triangle inequality then $I_3$:
$\frac{M_2+2c_\chi M_1+c_\chi'M_0}{a_q}e^{-a_qe^{2R}}$ ✔.

**$H^1$ bound.** $\max_{(0,1]}t\,a(t)=0.7014634088$ (at $t=1$; $\to1/2$ at $0^+$) $\le4/3$, so $a\le4/(3t)$ ✔.
$a\le\frac43e^{-t/2}\iff\frac1{1-e^{-2t}}\le\frac43\iff t\ge\log2=0.693$, true on $[1,\infty)$ (sup $1.1565$) ✔.
$\int_0^1\frac{4}{3t}t^2dt=\frac23$; $\int_1^\infty\frac43e^{-t/2}\cdot4\,dt=\frac{32}3e^{-1/2}=6.4697\le\frac{32}3$. ✔
(Bound valid; the constant $32/3$ is loose by $e^{-1/2}$ — slack, not an error.)

**Quintic.** $p'=-30t^2(t-1)^2$, $p''=-60t(t-1)(2t-1)$; $p(0)=1,p(1)=0,p'(0)=p'(1)=p''(0)=p''(1)=0$
(constant extension is $C^2$). Exactly (sympy): $\max|p'|=15/8=1.875$ at $t=\frac12$;
$\max|p''|=\frac{10\sqrt3}{3}=\frac{10}{\sqrt3}=5.7735027$ at $t=\frac12\pm\frac{\sqrt3}6$. ✔
Width $98/100$: $|\chi'|\le1.91327\le2$, $|\chi''|\le6.01156\le8$ ✔; mollifying does not raise sup-norms;
the mollified step is $1$ on $(-\infty,0.005]$, $0$ on $[0.995,\infty)$, so $\chi_R(x)=\mathrm{step}(|x|-R)$ is
smooth at $x=0$ even for $R=0$, is $1$ on $[-R,R]$, $0$ off $[-R-1,R+1]$, and $|\chi_R'|,|\chi_R''|$ inherit
the step's bounds since $(\operatorname{sgn}x)^2=1$. ✔

## (2) Convolution paragraph (Prop 3.4) — CORRECT
$(f_0*h)^{(j)}=\int f_0^{(j)}(x-y)h(y)dy$; $|y|\le H\Rightarrow|x-y|\ge|x|-H\Rightarrow e^{2|x-y|}\ge e^{-2H}e^{2|x|}$,
so $\exp(-\frac\pi2e^{2|x-y|})\le\exp(-a_He^{2|x|})$, $a_H=\frac\pi2e^{-2H}$, giving
$|(f_0*h)^{(j)}|\le\|h\|_1M_j\exp(-a_He^{2|x|})$. The needed constant is $M_j$ (the $f_0$ envelope),
**not** $AM_j$ (which belongs to $\Phi$) — the paragraph uses $M_j$, correct as written. Re-running
Lemma 3.3 with $(a_H,\|h\|_1M_j)$ is legitimate: that proof uses only the envelope's shape.

## (3) Theorem 4.1 — CORRECT
Polarisation: $\B(g,v)=\D(g,v)-c_AH(g,v)+[\overline{A_+(g)}A_-(v)+\overline{A_-(g)}A_+(v)]-2\sum w_nC_{g,v}$
(antilinear in $g$, $\B(g,g)=\Q(g)$, using $C_{g,g}=C_g$ from setup.tex). Numerics: $f=e^{-x^2}$,
$s(x)=(1+2i)e^{-3(x-1)^2}+(0.5-1.3i)e^{-2(x+1.7)^2}$ (so $|s|^2$ is **not** even), $h=0.004$ on $[-9,9]$.

(a) $|a_2s_2-a_1s_1|^2-(a_2-a_1)(a_2|s_2|^2-a_1|s_1|^2)=a_1a_2|s_2-s_1|^2$; integrate $\Rightarrow E_s(t)$.
Numeric $|{\rm diff}|\le2.2\cdot10^{-16}$ at $t=0.05,0.3,\log2,1,2.5$. ✔

(b) $H(f_0s)=\int f_0^2|s|^2=\Re H(f_0,f_0|s|^2)$; numeric diff $0.0$ — cancel exactly. ✔

(c) $C_g(t)-\Re C_{f_0,f_0|s|^2}(t)=\int a_1a_2[\Re(\bar s_1s_2)-\tfrac12(|s_1|^2+|s_2|^2)]=-\tfrac12E_s(t)$,
so $-2w_n(\cdot)=+w_nE_s(\log n)$: coefficient $w_n$, **not** $2w_n$ — the $\tfrac12$ in $C_{g,v}$ ("two
directions") supplies it. Numeric ratio $1.000000000000$ at $t=\log2,\log3,\log4,\log5$. ✔

(d) Both pole terms, written as double integrals and symmetrised in $x\leftrightarrow x'$, carry the same
real symmetric kernel $2\cosh\frac{x-x'}2$; with $\Re(s(x)\overline{s(x')})-\tfrac12(|s(x)|^2+|s(x')|^2)=-\tfrac12|s(x)-s(x')|^2$
the difference is $-\int\!\!\int f_0(x)f_0(x')\cosh\frac{x-x'}2|s(x)-s(x')|^2=-\int_\R\cosh\frac t2E_s(t)dt
=-\int_0^\infty(e^{t/2}+e^{-t/2})E_s(t)dt$ ($E_s$ even: $|E_s(.9)-E_s(-.9)|=2.2\cdot10^{-16}$).
Only "$f_0$ real" is used — $A_+(f_0)=A_-(f_0)$ and evenness of $|s|^2$ are not needed.
*Symbolic:* on a 3-point discretisation with arbitrary complex $s_i$ and positive weights,
sympy returns $T_1-T_2-{\rm RHS}\equiv0$ exactly.
*Numeric:* $T_1=1.095098038505$, $T_2=6.636921062638$, LHS $=-5.541823024132$, RHS $=-5.541823024134$,
residual $1.85\cdot10^{-12}$ (rel. $3.3\cdot10^{-13}$). ✔

**Whole identity** (same stand-in; prime sum truncated at $n\le400$ on both sides; common grid $dt=0.004$, $T=14$):
$\Q(fs)=-0.013255923218$, $\Re\B(f,f|s|^2)=-0.013255916445$, LHS $=-6.773\cdot10^{-9}$,
RHS $=\int bE_s+\sum w_nE_s(\log n)=-6.772\cdot10^{-9}$; residual $-6.1\cdot10^{-13}$
($1.1\cdot10^{-13}$ rel. to the largest constituent $|T_1-T_2|=5.54$). Per piece:
$\D_g-\D_{f,v}=1.3916849829=\int aE_s$ (diff $4\cdot10^{-16}$); $T_1-T_2=-5.5418230241=-\int2\cosh\frac t2E_s$
(diff $6\cdot10^{-13}$); $-2(S_g-S_{f,v})=4.1501380345=\sum w_nE_s$ (exact). ✔
Also $b=a-2\cosh\frac t2=\frac{e^{-5t/2}}{1-e^{-2t}}-e^{t/2}$ (since $a-e^{-t/2}=\frac{e^{-5t/2}}{1-e^{-2t}}$) ✔,
and the second form of (4.2) (half-integral against the even $\tilde\nu$) reproduces the first, $E_s$ being even. ✔

## (4) Plane-wave display — CORRECT
$|e^{i\xi(x+t)}-e^{i\xi x}|^2=|e^{i\xi t}-1|^2=2(1-\cos\xi t)$, $x$-independent $\Rightarrow E_s(t)=2(1-\cos\xi t)C_0(t)$.
Numeric diffs $\le4.4\cdot10^{-16}$ for $(\xi,t)\in\{0.7,2.3\}\times\{0.4,1.3\}$.

## (5) Lemma 4.2, added sentence — CORRECT
$(y^3-y-1)'=3y^2-1\ge2>0$ for $y>1$ (strictly increasing), value $-1<0$ at $y=1$. Sign link, exactly:
$b(t)=e^{t/2}\frac{e^{-3t}+e^{-2t}-1}{1-e^{-2t}}=-e^{t/2}\frac{y^{-3}(y^3-y-1)}{1-e^{-2t}}$, and $1-e^{-2t}>0$ for $t>0$,
so $b$ has the sign opposite to the cubic. Numerics ($b(t)$ | $y^3-y-1$):
$t=0.1$: $+3.2451045785$ | $-0.7553121105$; $t=0.28$: $+0.0078320796$ | $-0.0067628356$;
$t=0.2811995743$: $+1\cdot10^{-10}$ | $-1\cdot10^{-10}$; $t=0.3$: $-0.1148955570$ | $+0.1097443036$;
$t=\log2$: $-1.1785113020$ | $+5$; $t=1$: $-1.5537885216$ | $+16.3672550947$.
$\rho=1.32471795724$, $t_0=\log\rho=0.281199574323$ — match the paper's $1.324717957\ldots$, $0.2811995743$. ✔

## Caveats (not errors)
- $M_0,M_1,M_2,A$ unchecked (app:constants out of scope) — UNVERIFIABLE here.
- $32/3$ in the $H^1$ bound is valid but loose by $e^{-1/2}$ (sharp from this argument: $\frac{32}3e^{-1/2}$).
- The (3) numerics use a Gaussian stand-in: they verify the **algebraic** identity (which needs only
  $f_0$ real), not $\Re\B(f_0,f_0|s|^2)=0$, which rests on Prop. 3.4.
