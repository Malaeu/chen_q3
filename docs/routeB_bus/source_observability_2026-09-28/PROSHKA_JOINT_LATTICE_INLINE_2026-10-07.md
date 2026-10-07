# Q10 native answer

Chat 6ac58a1c-1568-83ed-95d0-857526e2b6cb; user 2454f011-d320-43f1-a9e1-7d125b40568d; answer 29afc971-faa8-4da1-aa80-8923eedce5d2. Native idle with completed answer; reference markers retained verbatim.

Ы — **the proposed joint remainder is correct. After combining it with the complete continuous main term, the operation returns the original weighted prime discrepancy exactly, with coefficient one. No new one-sided estimate is obtained.**

The cancellation is complete: the harmonic Möbius terms cancel the whole main term, the two half-weight sums integrate to zero **jointly**, and the constant from the unweighted floor identity also integrates to zero. The lower endpoints are essential to these conclusions.

:chatgpt-content-reference{index="8"}[Complete PAPER verdict, derivation, source checks, and return budget](sandbox:/mnt/data/PROSHKA_VERDICT_SCALAR_JOINT_INTEGER_LATTICE_Q10_2026-10-07.md)

## 1. The submitted change of variables passes

**[FINITE_CELL | PAPER]**

Fix any real \(x\ge1\), put \(t=\log x\), and retain
\[
F(t)=\sum_{n\le x}\frac{\Lambda(n)}{\sqrt n}(t-\log n).
\]
All sums below use the ordinary Möbius function and include every prime power.

For
\[
f_s(u)=u^{-1/2}\log u\,(s-\log u),
\qquad 1\le u\le e^s,
\]
the complete continuous integral is
\[
\boxed{
H_0(s)=\int_1^{e^s}f_s(u)\,du
=4e^{s/2}(s-4)+4s+16.
}
\tag{1}
\]
The terms \(4s+16\) are lower-endpoint contributions. They cannot be omitted merely because \(f_s\) vanishes at both endpoints.

Define
\[
\mathscr M(x)=
\sum_{d\le x}\frac{\mu(d)}{\sqrt d}H_0(\log(x/d)).
\]
The starting relation is exactly
\[
F(t)=\mathscr M(x)-T_K(x).
\tag{2}
\]

The derivative in the fractional-part formula is
\[
f_s'(u)=u^{-3/2}
\left(s-2\log u-\frac{s\log u}{2}+\frac{(\log u)^2}{2}\right).
\]
Under
\[
u=v/d,\qquad s=t-\log d,
\]
its bracket becomes
\[
\boxed{
P_0(v,t)+(\log d)P_1(v,t),
}
\]
with precisely your coefficients
\[
\begin{aligned}
P_0(v,t)&=t-2\log v+\frac{(\log v)^2}{2}-\frac{t\log v}{2},\\
P_1(v,t)&=1+\frac t2-\frac{\log v}{2}.
\end{aligned}
\]
The weight and Jacobian combine as
\[
\frac{\mu(d)}{\sqrt d}u^{-3/2}\,du
=\mu(d)v^{-3/2}\,dv.
\]
The full domain is \(1\le d\le v\le x\). Finite Fubini therefore proves
\[
\boxed{
T_K(x)=-
\int_1^x v^{-3/2}
\left[P_0(v,t)U_0(v)+P_1(v,t)U_1(v)\right]\,dv.
}
\tag{3}
\]

Write, without estimating them,
\[
\mathfrak m_j(v)=
\sum_{d\le v}\frac{\mu(d)(\log d)^j}{d},
\qquad
\mathfrak M_j(v)=
\sum_{d\le v}\mu(d)(\log d)^j,
\quad j=0,1.
\]
The two exact divisor/floor identities give
\[
\boxed{
\begin{aligned}
U_0(v)&=v\mathfrak m_0(v)-1-\tfrac12\mathfrak M_0(v),\\
U_1(v)&=v\mathfrak m_1(v)+\psi_{\rm Ch}(v)-\tfrac12\mathfrak M_1(v).
\end{aligned}}
\tag{4}
\]
In particular, the sign in front of \(\psi_{\rm Ch}\) is **plus**:
\[
\sum_{d\le v}\mu(d)\log d\lfloor v/d\rfloor
=\sum_{n\le v}\sum_{d\mid n}\mu(d)\log d
=-\psi_{\rm Ch}(v).
\]

No correction to the submitted candidate is needed.

## 2. Evaluate the joint cancellation before any inequality

**[FINITE_CELL | PAPER]**

The useful primitive is
\[
\boxed{
G_d(v)=v^{-1/2}(t-\log v)\log(v/d),
\qquad d\le v\le x.
}
\tag{5}
\]
Direct differentiation gives
\[
G_d'(v)=v^{-3/2}
\left[P_0(v,t)+(\log d)P_1(v,t)\right],
\]
and, crucially,
\[
\boxed{G_d(d)=G_d(x)=0.}
\tag{6}
\]

I apply this **per divisor**, after finite Fubini. That avoids differentiating cumulative Möbius step functions as though they were smooth.

### The half-weight terms vanish together

Using (5)–(6),
\[
\begin{aligned}
&\int_1^x v^{-3/2}
\left[P_0\mathfrak M_0+P_1\mathfrak M_1\right]\,dv\\
&\qquad=
\sum_{d\le x}\mu(d)\int_d^xG_d'(v)\,dv\\
&\qquad=
\sum_{d\le x}\mu(d)\bigl[G_d(x)-G_d(d)\bigr]
=0.
\end{aligned}
\]
Thus
\[
\boxed{
\int_1^x v^{-3/2}
\left[P_0\mathfrak M_0+P_1\mathfrak M_1\right]\,dv=0.
}
\tag{7}
\]

This is not a bound for either separate sum. It is an exact cancellation of their integrated combination and uses no Mertens estimate.

### The constant floor term also vanishes

At \(d=1\),
\[
\boxed{
\int_1^x v^{-3/2}P_0(v,t)\,dv
=
\left[v^{-1/2}(t-\log v)\log v\right]_1^x
=0.
}
\tag{8}
\]
The constant \(-1\) in \(U_0\) has therefore been retained and evaluated. It supplies no extra reserve.

### The harmonic Möbius terms cancel the entire main term

Again using finite Fubini,
\[
\begin{aligned}
&\int_1^x v^{-1/2}
\left[P_0\mathfrak m_0+P_1\mathfrak m_1\right]\,dv\\
&\qquad=
\sum_{d\le x}\frac{\mu(d)}d\int_d^x vG_d'(v)\,dv\\
&\qquad=
-\sum_{d\le x}\frac{\mu(d)}d\int_d^xG_d(v)\,dv.
\end{aligned}
\]
The boundary \([vG_d(v)]_d^x\) is zero at both ends. Substituting \(v=du\) in the last integral gives
\[
\int_d^xG_d(v)\,dv
=\sqrt d\,H_0(t-\log d).
\]
Consequently,
\[
\boxed{
\int_1^x v^{-1/2}
\left[P_0\mathfrak m_0+P_1\mathfrak m_1\right]\,dv
=-\mathscr M(x).
}
\tag{9}
\]

This is the full \(H_0\) in (1), including \(4s+16\).

### What remains

Substitute (4) into (3), then combine with (2). Equations (7)–(9) remove every other contribution:
\[
\boxed{
F(t)=
\int_1^{e^t}
\frac{1+\tfrac12(t-\log v)}{v^{3/2}}
\psi_{\rm Ch}(v)\,dv.
}
\tag{10}
\]

**There is no residual Möbius term, endpoint error, or separately positive correction left over.**

An independent **Stieltjes return check** makes the source content explicit. Let
\[
g_x(v)=v^{-1/2}\log(x/v).
\]
Then
\[
-g_x'(v)=v^{-3/2}\left(1+\tfrac12\log(x/v)\right),
\quad
g_x(x)=0,
\quad
\psi_{\rm Ch}(1)=0.
\]
Hence
\[
\int_1^x
\frac{1+\tfrac12\log(x/v)}{v^{3/2}}\psi_{\rm Ch}(v)\,dv
=
\int_{[1,x]}g_x(v)\,d\psi_{\rm Ch}(v),
\]
which is exactly the original prime-power ramp.

Its right derivative is
\[
\frac{\psi_{\rm Ch}(x)}{\sqrt x}
+\frac12\int_1^x\frac{\psi_{\rm Ch}(v)}{v^{3/2}}\,dv
=\mathcal A(x).
\]
At \(x=q\), the complete derivative jump is \(\Lambda(q)/\sqrt q\). The zero ramp value at an included endpoint has not become a missing half-event.

## 3. Combine the result with the complete archimedean source

**[FINITE_CELL | PAPER]**

Keep
\[
B(t)=4e^{t/2}+ct+b-R(t),
\]
\[
c=\frac{\operatorname{digamma}(1/4)-\log\pi}{2},
\qquad
b=\frac{\pi^2}{4}+2G_{\rm Cat}-8,
\]
\[
R(t)=\frac14\sum_{k\ge1}
\frac{e^{-(2k+1/2)t}}{(k+1/4)^2}.
\]
These are the complete terms of Suzuki’s equation (1.1): the \(k=0\) Lerch contribution cancels the decaying pole term exactly; neither was discarded. The requested v4 source was checked directly. :chatgpt-content-reference{index="0"}

Define the signed quantity left by the tested cancellation:
\[
\boxed{
\mathscr W(x)=
\int_1^x
\frac{1+\tfrac12\log(x/v)}{v^{3/2}}
\bigl[\psi_{\rm Ch}(v)-v\bigr]\,dv.
}
\tag{11}
\]
The baseline integral is elementary:
\[
\begin{aligned}
\int_1^xv^{-1/2}\left(1+\tfrac12\log(x/v)\right)dv
&=\int_0^t e^{r/2}\left(1+\tfrac12(t-r)\right)dr\\
&=\left[e^{r/2}(t-r+4)\right]_0^t\\
&=4\sqrt x-t-4.
\end{aligned}
\]
Therefore the complete return is
\[
\boxed{
F(\log x)=4\sqrt x-\log x-4+\mathscr W(x),
}
\tag{12}
\]
and
\[
\boxed{
\Psi(\log x)
=(c+1)\log x+(b+4)-R(\log x)-\mathscr W(x).
}
\tag{13}
\]

The lower-endpoint terms \(-\log x-4\) are indispensable. They give **\(c+1\)** and **\(b+4\)**, not an unspecified lower-order error.

At \(x=1\),
\[
\mathscr W(1)=0,\qquad R(0)=b+4,
\]
so (13) retains the exact initial value \(\Psi(0)=0\). No derivative of the archimedean series at zero is needed.

### Why the remaining positive kernel does not supply the desired sign

The kernel in (11) is positive, but it multiplies the **signed** discrepancy \(\psi_{\rm Ch}(v)-v\).

Applying \(\psi_{\rm Ch}\ge0\) to (10) gives \(F\ge0\). That is the wrong direction for the requested upper estimate \(F\le B\). Neither floor identity used above orders the quantity in (11) against the affine and archimedean terms in (13).

The operation has thus returned the original unpaid prime discrepancy with coefficient **one**. It has not produced a contraction factor, a favorable leftover boundary, or an independent reserve.

## 4. Exact return to the existing drift and reserve

**[FINITE_CELL | PAPER]**

At a prime power \(q\), retain
\[
y_q=\mathcal A(q)-c,\qquad
u_q=\frac{y_q}{2\sqrt q},
\]
and the Q8 convex correction
\[
\mathscr D(q)
=4\sqrt q\,[u_q\log u_q-u_q+1].
\]
The accepted reserve identity is
\[
E_q=\Psi(\log q)+R(\log q)-\mathscr D(q).
\]
Substituting (13) gives
\[
\boxed{
E_q-d_q
=(c+1)\log q+(b+4)
-\mathscr W(q)-\mathscr D(q)-d_q.
}
\tag{14}
\]

Thus the exact unpaid combination is
\[
\mathscr W(q)+\mathscr D(q),
\]
with **every prime power still inside \(\mathcal A(q)\)**. The favorable source identities have not supplied the upper bound on this combination needed to sign (14).

For a prime-power anchor \(Q\), the original jump recurrence now reads
\[
\boxed{
\begin{aligned}
\mathcal S_Q(q)
={}&(c+1)\log(q/Q)
-[\mathscr W(q)-\mathscr W(Q)]\\
&-[\mathscr D(q)-\mathscr D(Q)]
+\mathcal L_Q(q).
\end{aligned}}
\tag{15}
\]
No term in (15) has acquired a new signed estimate.

This does not alter the **clipped full-cell minimum**. On the original cell,
\[
\Psi(t)=B(t)-\mathcal A(q)t+D_q,
\qquad
\log q\le t\le\log q_{\rm next},
\]
and the exact interior critical equation remains
\[
B'(t)=\mathcal A(q),
\]
subject to clipping. The calculation has not replaced it by the unconstrained growing-pole minimum, signed the previously defined \(V_q\), or inferred a cell sign from \(T_K(10)\) or \(T_K(100)\).

## 5. The terminal budget is unchanged

**[COFINAL_FAMILY | PAPER; ACCEPTED Q8/Q9 INPUTS]**

The already paid contributions remain
\[
0\le\mathcal L_Q(q)\le
\mathfrak L(Q)=\frac{18\log Q+24}{\sqrt Q},
\]
and
\[
|\mathcal S_Q^{\rm pow}(q)|\le\mathfrak P(Q),
\]
where
\[
\mathfrak P(Q)=
6C_\delta e^{-\beta\sqrt{\log Q}}
\left(
\frac{\sqrt{\log Q}}{\beta}
+\frac1{\beta^2}+1+16Q^{-1/6}
\right).
\]
Their existing thresholds and constants are unchanged. The proper-power event split still retains all proper powers in the prehistory of every prime event. :chatgpt-content-reference{index="1"} :chatgpt-content-reference{index="2"} :chatgpt-content-reference{index="3"}

Consequently, the complete lower envelope remains
\[
\boxed{
E_q-d_q\ge
E_Q+\mathcal S_Q^{\rm prime}(q)
-\mathfrak L(Q)-\mathfrak P(Q)-d_q.
}
\tag{16}
\]
The Q9 expression
\[
\mathcal S_Q^{\rm prime}
=-\mathfrak C_Q+\mathfrak J_Q
\]
retains its favorable nonlinear term; its signed bound is still open. The existing two-sided reserve bracket is likewise unchanged. :chatgpt-content-reference{index="4"}

The new calculation contributes **zero approximation error and zero newly proved terminal margin**. Exact recombination has removed bookkeeping terms, not estimated the remaining arithmetic.

A proof of the eventual full-cell sign would still satisfy Suzuki’s Theorem 11.1 at \(\omega=0\). Nothing above establishes that premise, and no unbounded-height verification or RH assumption was used. :chatgpt-content-reference{index="5"}

No \(K_m\), source projector, or \(J_r\) approximation was made. **\(\Delta_{10}\) is neither spent nor improved**, and the original SP and actual Schur obligations retain their previous quantifiers. :chatgpt-content-reference{index="6"}

## 6. Source checks and precise stopping scope

The exact controls checked the arithmetic and boundary coefficients, not a numerical prefix of \(\Psi\) or \(E\).

The two floor identities and both \(U\)-formulas passed at **2,048 rational cutoffs**, \(v=n\) and \(v=n+1/3\), \(1\le n\le1024\), using rational coefficients and formal prime-log vectors. Reversing the sign of \(\psi_{\rm Ch}\) in \(U_1\) failed at **2,046** cutoffs.

Symbolic checks independently verified the change-of-variables polynomial, \(G_d'\), the per-divisor cancellations, the complete \(H_0\) integral, and the baseline \(4\sqrt x-t-4\). Deleting the lower-endpoint constant \(16\) from \(H_0\) leaves the exact nonzero residue
\[
-16d^{-1/2}.
\]
These controls support the displayed proofs; they are not an independent PAPER audit or an asymptotic sign certificate.

**What is proved:** the submitted candidate is exact, and its complete joint evaluation is (10)–(13), with every boundary and source term retained.

**What is not proved:** a new one-sided bound for \(\mathscr W\), the prime-prefix net correlation, the reserve, or the clipped cell minimum.

**Stop this particular exact floor-pairing mechanism here.** Counting a canceled Möbius term as an additional saving after the prime sum has returned would count it twice. Re-expanding the same equalities does not advance the signed estimate.

That is an exact-return stall—not a counterexample to the target, not mathematical death of the route, and not a claim that another arithmetic estimate cannot control the surviving term. No replacement representation is selected without such an estimate.

**RH, SP, G1/G3, the scalar reserve, and the actual Schur sign remain OPEN. These new PAPER derivations require independent audit.**
