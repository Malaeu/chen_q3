Ы. **SOURCE_PATH_VARIANCE_AVERAGE_PROVED.**

For the **complete source**, the original weights, and every sufficiently large integer block,
\[
\boxed{
0\le
\sum_{M\le m<2M}w_m\,4L_m^2\mathscr V_m^{\mathrm{path}}
\le C_D\frac{M}{\log M},
\qquad D=256.
}
\]
Thus **VAVG128 holds**: the normalized variance average is \(O_D((\log M)^{-2})\), hence tends to zero.

Combined with the accepted action deficit, this yields an actual-source result:
\[
\boxed{
\forall M\ge M_*(P)\quad
\exists\,m\in[M,2M)\text{ in the original admitted family}:
\quad \mathscr Q_m<-S_m<0.
}
\]
**Universal PIB128—and every eventual version on that same family—is therefore refuted.** No first numerical witness or numerical threshold is asserted.

:chatgpt-content-reference{index="4"}[Complete PAPER verdict — full proof, source checks, and one bounded CODEX DIRECTIVE](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_FIXED_128_PATH_VARIANCE_COMPENSATION_2026-09-27.md)

### What pays the variance

The proof bounds the **actual path variance**, not the action substituted for it. It verifies the proposed second-window-derivative formula, including its sign, and retains both boundary terms involving \(g'(\lambda/2)\) and \(g(\lambda/2)\). The combined finite-window correction satisfies a source-uniform, square-summable estimate
\[
|q_{k,n}(\lambda)|
\le C\lambda^{3/2}n^{-2}
   e^{-(\pi/2)e^\lambda}.
\]
Its contribution is exponentially small under the **same original weights**.

The one additional external input is the unconditional continuous second moment
\[
\int_0^T |Z''(t)|^2\,dt
=\frac{T\log^5T}{80}+O(T\log^4T),
\]
from Bui–Hall, equation (1), at derivative pair \((2,2)\). No third-derivative moment is needed. :chatgpt-content-reference{index="0"}

Crucially, the proof does **not** apply this continuous theorem directly to discrete Fourier samples. It changes variables inside the original parameter paths and proves bounded **frequency multiplicity**—the number and weight of paths contributing at a frequency—separately for the forward infinite tail and backward odd-offset block. The entire high-frequency remainder is retained and bounded.

### The strict transfer to the original receiver

The predecessor supplies, with the same positive weights,
\[
\sum w_m\mathscr R_m<-8M\log M,
\qquad
\sum w_mS_m<4M\log M.
\]
These are the accepted block inputs, not new assumptions about individual cells. :chatgpt-content-reference{index="1"}

The variance bound eventually gives \(\sum w_m4L_m^2\mathscr V_m^{\mathrm{path}}<M\log M\). Therefore the **exact compensation identity** yields
\[
\boxed{
\sum_{M\le m<2M}w_m(\mathscr Q_m+S_m)
<-3M\log M<0.
}
\]
Positive weights force an actual admitted cell with \(\mathscr Q_m<-S_m\) in every sufficiently late block.

### Scope

This closes **VAVG128** and refutes **only universal/eventual PIB128**. A negative \(\mathscr Q_m\) does not establish a negative \(T_m\), decide MG128, or prove a PC or SV violation. No MG128 disjunction arm is selected; MT128, MG128, C128, PC, SV, lag, and Schur-floor remain open. This is the consequence boundary specified in the request. :chatgpt-content-reference{index="2"}

The authoritative TXT and pinned predecessor match their stipulated **SHA-256** hashes. **The new proof has not received independent review. No RH claim is made.** The file’s single **CODEX DIRECTIVE** commissions that independent PAPER audit.

**Verdict artifact SHA-256**
```text
17cf49ca3958c270da791562fc8000c5e9a246460327f99b598cf09c4761e431
```
