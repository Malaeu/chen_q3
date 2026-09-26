Ы. **OPEN_SOURCE_CORE_LAG_DECAY.** The fixed candidate is not established on the entire selected tail, and no source-based counterexample is established.

:chatgpt-content-reference{index="2"}[Read the full PAPER verdict](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_CONTINUOUS_LAG_DECAY_2026-09-26.md)

### What is proved

For the unchanged source and original \(E=E_{11}\), the argument proves
\[
\boxed{
16E-(1+t)|A_m(t)|\ge \frac{9}{80}E>0
}
\]
for **every admitted selected**
\[
65536\le m\le e^{120},
\qquad 2\log\log m\le t\le \frac{\log m}{2}.
\]

The improvement comes from retaining the **overlap geometry**: when \(t\ge b/2\), the two intervals contributing to Cauchy–Schwarz are disjoint, giving an extra factor of two. The proof also certifies explicit lag regions for every larger selected \(m\).

This closes a bounded-index region—not the unbounded selected tail required by the request. The original constant **16** and threshold **65536** remain unchanged. :chatgpt-content-reference{index="0"}

### What remains unpaid

The verdict derives an exact **summation-by-parts representation** retaining both the carrier-edge coefficient
\[
\varepsilon_m-e_{m+1}
\]
and every subsequent difference \(e_n-e_{n+1}\). Their sum is exactly \(\varepsilon_m\): the nonzero low block has not disappeared.

The one proposed next lemma concerns the **half-line spectral density**
\[
\rho_m(\xi)=
\left|(2\pi)^{-1/2}\int_0^b k(u)e^{-i\xi u}\,du\right|^2.
\]
The derived sufficient condition is
\[
\boxed{
\int_{\mathbb R}\rho_m(\xi)\,d\xi
+\int_{\mathbb R}|\rho_m'(\xi)|\,d\xi
\le16E.
}
\]
The second integral is the density’s **total variation**. A source-derived proof on the remaining cells would settle every unpaid lag at once. **That inequality is not proved here.** It is stronger than the original lag candidate; its failure alone would not refute that candidate.

Consequently, **\(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional**. The exact transfer retains the negative low-frequency subtraction. :chatgpt-content-reference{index="1"}

The full file contains the source-lock checks, all derivations and boundary checks, the remaining source-indexed comparison, and exactly one bounded **CODEX DIRECTIVE**. The predecessor’s SHA-256 and Git blob were independently matched locally; **the new mathematical argument has not received independent review**. No mathematical runtime, Lean execution, repository write, route promotion, or RH claim was made.

**Verdict SHA-256**
```text
32d338448f4305a4bdd2b627dd977aa86388268dfcd802acff1f947aaf4d6fce
```