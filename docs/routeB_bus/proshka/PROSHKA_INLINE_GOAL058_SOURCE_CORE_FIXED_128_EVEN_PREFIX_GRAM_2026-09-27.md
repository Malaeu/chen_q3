Ы. **SOURCE_EVEN_PREFIX_GRAM_DIAGONAL.**

For the **complete source**, the **original common weight**, and every fixed pair \(1\le\ell,k\le128\), the new PAPER argument proves
\[
\boxed{
G_{\ell k}(M)
:=\sum_{M\le m<2M}w_mx_{\ell,m}x_{k,m}
=\delta_{\ell k}M+o(M).
}
\]
Thus the **Gram matrix**—the matrix of weighted coefficient cross products—satisfies \(G(M)/M\to I_{128}\). In particular,
\[
\boxed{
C_M=o(M),\qquad D_M=(-246+o(1))M.
}
\]
There is therefore an integer \(M_*(P)\) such that
\[
\boxed{D_M<-123M<0\qquad\text{for every integer }M\ge M_*(P).}
\]

:chatgpt-content-reference{index="4"}[Complete PAPER verdict — full proof, source checks, and one bounded CODEX DIRECTIVE](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_FIXED_128_EVEN_PREFIX_GRAM_2026-09-27.md)

### What closes the off-diagonal question

The proof does **not** infer the cross products from the accepted diagonals. It derives a **shifted continuous moment** from the verified fixed-order continuous derivative-moment family in Bui–Hall, equation (1). That external theorem uses Hardy’s \(Z\)-function and is unconditional; it is not a discrete sampling law. :chatgpt-content-reference{index="0"}

The newly derived formula is
\[
\frac{1}{|I_M|H}\int_{I_M}Z(t)Z(t+c/H)\,dt
=\operatorname{sinc}(c/2)+o(1),
\qquad H=\log M,
\]
uniformly for \(c\) in any fixed compact interval. Here \(\operatorname{sinc}(y)=\sin(y)/y\), with value \(1\) at zero, and \(I_M\) is the corresponding actual frequency interval.

The proof supplies an explicit **Taylor-remainder bound**, rather than assuming this shifted formula. It also pays the difference between the actual variable shift and \(c/H\). For the requested pair,
\[
c=4\pi(k-\ell),
\]
so the sinc value is exactly zero off the diagonal and one on it.

The separate, load-bearing step is **product quadrature**: a proved passage from the actual discrete \(m\)-mesh to the continuous product integral. Using the Euler–Maclaurin formula with its periodic-Bernoulli remainder, the normalized sampling error satisfies
\[
\limsup_{M\to\infty}
\frac{|\text{sampling error}|}{M\log M}
\le 2\zeta(r)\alpha_r,
\qquad
\alpha_r\le\frac6r.
\]
Both block endpoints are included. The quadrature identities are standard; their application to the two distinct phases is proved in the verdict. :chatgpt-content-reference{index="1"}

The order of limits is essential: **fix each auxiliary derivative order, take \(M\to\infty\), then let the auxiliary orders increase**. No derivative order grows with \(M\). Both finite-window errors, their mixed products, all theta-source-index cross terms, and the same original weight are retained.

### The consequence is limited to the second-gate block test

The Gram law gives
\[
\sum_{M\le m<2M}w_mJ_m^{\mathrm{disp}}
=(254+o(1))M,
\]
while \(\sum w_ma_m^2=M+o(M)\). Hence the coefficient in \(D_M\) is \(8-254=-246\).

Because the weights are positive, **every sufficiently late block contains an original admitted cell with**
\[
\boxed{J_m^{\mathrm{disp}}>8a_m^2.}
\]

That cell need not be one of the accepted first-gate witnesses. Nor does a negative block average prevent other cells from satisfying both gates. **Existential C128 is neither established nor excluded; PC and the later source-sign questions remain undecided.** This is the consequence boundary specified in the request. :chatgpt-content-reference{index="2"}

The authoritative TXT and signed-block source match their stipulated **SHA-256** hashes. The final two `PAPER_CHAIN.md` sections were read at the pinned commit; its full-file SHA-256 was recorded from the request but not independently rehashed.

**The new proof has not received independent review. No RH claim is made.** The file’s single **CODEX DIRECTIVE** commissions that PAPER audit, especially the compact-uniform shift remainder, critical product sampling, endpoint terms, and window corrections.

**Verdict artifact SHA-256**
```text
90b53885c8de1971817077ad057c0b360e5efdf943d787831ed527e71bf63b12
```
