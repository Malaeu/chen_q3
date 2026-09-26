Ы. **OPEN_PRIME_SQUARE_HIGH_FREQUENCY.**

:chatgpt-content-reference{index="1"}[Complete PAPER verdict — Markdown](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_PRIME_SQUARE_HIGH_FREQUENCY_2026-09-26.md)

**Neither requested family conclusion is established:** there is no proved eventual lower-order bound for the complete square block and no proved leading contribution on an unbounded selected-index set. The predecessor’s limited audit does not supply either result. 

### New source-relative bounds

The **exterior-involving contribution in the exact physical representation** is now controlled. For every admitted selected cell with **\(m\ge16\)**,
\[
\boxed{
\left|
4\sum_{\substack{p\le m^{1/4}\\p\ \mathrm{prime}}}
\frac{\log p}{p}
\int_{b-2\log p}^{\infty}
f_m(u)f_m(u+2\log p)\,du
\right|
<7E_{11}(m).
}
\]

The proof uses the actual source’s exterior decay and the separation of the shifts \(2\log p\). Their **Gram matrix**—the matrix of pairwise \(L^2\) overlaps—has a uniformly bounded row sum. This preserves information that a sum of individual norm bounds would lose.

**That physical contribution is not the high-frequency block by itself.** The verdict retains the required low-frequency subtraction explicitly.

Separately, for **\(m\ge256\)**, the exact square contribution on the larger frequency interval
\[
\boxed{\sqrt m<|\xi|\le \frac{m}{(\log m)^{4/3}}}
\]
has absolute value **less than \(E_{11}/2\)**. This follows within the admitted projection estimate’s domain; it does not change the source, carrier, or \(Q\).

### What remains unpaid

Define the actual **interior–interior overlap**
\[
\mathscr V_m=
4\sum_{\substack{\log m<p\le m^{1/4}\\p\ \mathrm{prime}}}
\frac{\log p}{p}
\int_0^{b-2\log p}
f_m(u)f_m(u+2\log p)\,du.
\]

The new estimates, the small-prime-base bound, and the retained low-frequency subtraction give
\[
\boxed{
\left|\mathscr U_m^{(2)}-\mathscr V_m\right|
\le12(1+\log\log m)\,E_{11}(m),
\qquad m\ge16.
}
\]

**The signed source cancellation in \(\mathscr V_m\) remains unproved.** The file expands all four terms, retains the \(n=q\) diagonal and **Q5/Q6 endpoint**, and identifies the removed mixed-domain strips as part of the bounded exterior contribution—not as zero.

The single next directive is **`TEST_SOURCE_LARGE_PRIME_SQUARE_INTERIOR_OVERLAP`**. A proved saving for this narrower quantity would give the requested square saving through the displayed remainder. A proved leading contribution would likewise reach the square-leading outcome after subtracting that lower-order remainder. **Neither is claimed here.**

Even a completed square result would leave the exponent-one prime block open; a leading square term could still cancel against it. The opposite-side correlation, transfer, \(J_m\), first \(\tau_j\) sign, and **Schur-floor** remain open. **No RH claim is made.** The new PAPER derivations have not yet undergone independent audit.

**SHA-256**
```text
e248537c6ba25cc8dd628769093ed8e3c39112b9a29571234932d50b2b35b220
```