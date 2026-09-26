Ы. **OPEN_SOURCE_FIRST_NODE_PEAK.** Neither a negative first-node certificate for the actual source nor its nonnegativity on every admitted selected cell is established.

:chatgpt-content-reference{index="3"}[Read the full PAPER verdict](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_FIRST_NODE_PEAK_2026-09-27.md)

### What the argument proves

The complete **even-offset Cauchy sum** has an exact **logarithmic-kernel representation**:
\[
\sum_{\ell\ge1}\frac{e_{m+2\ell}}{2\ell-1}
=\frac{(-1)^m}{\sqrt L}\,\mathcal Z_m,
\]
where
\[
\mathcal Z_m=
\int_0^b g(u)
\left[
\log\cot\!\left(\frac{\pi u}{L}\right)
\cos(\omega_{m+1}u)
-\frac{\pi}{2}\sin(\omega_{m+1}u)
\right]du.
\]

Here \(g\) retains the **complete theta-source series**. The sine term is essential: removing it breaks an exact endpoint-cancellation check.

Completing the sum does **not** change the original cutoff \(K\). The file retains, in an exact correction, the entire low \(\varepsilon\) block, the negative-Fourier-index contribution, and every completed offset beyond \(K\).

For **every admitted selected \(L=\log m>120\)**, their combined effect on the original discriminator satisfies
\[
\boxed{
|\mathfrak p_m-\mathfrak p_m^{\log}|
\le\delta_m<\frac1{6L}<\frac1{720},
\qquad \delta_m\longrightarrow0,
}
\]
with
\[
\mathfrak p_m^{\log}
=
16-\frac ME+\frac{2R_0}{E}
-\frac{L e_{m+1}^{\,2}}{2\pi E}
-\frac{2\mathcal Z_m^{\,2}}{\pi^3E}
+\eta_m.
\]

This is a **uniform source-relative error bound**, not a source-sign result. The literal diagonal, zero node, physical exterior, and original denominator \(E\) remain.

### What remains unpaid

The missing comparison is the size of the **two complete source moments**
\[
\frac{L}{2\pi}e_{m+1}^{\,2}
+\frac{2}{\pi^3}\mathcal Z_m^{\,2}
\]
against the exact budget \(16E-M+2R_0\), including the displayed error allowance. Neither the generating identity nor the correction bound proves that this threshold is crossed.

The verdict’s one bounded **CODEX DIRECTIVE** is `TEST_SOURCE_CORE_LOGARITHMIC_MOMENT_PEAK`. Its concrete sufficient source inequality is
\[
\boxed{
\frac{2}{\pi^3}\mathcal Z_m^{\,2}
\ge16E-M+2R_0+\frac{E}{24}.
}
\]
A proof at an explicitly admitted selected cell would imply
\[
\mathfrak p_m<-\frac7{360},
\]
and therefore provide a negative original first-node witness. **This source inequality is not proved here.**

Failure of this narrower sufficient condition would not exclude the original first-node certificate: its retained diagonal could still contribute to a peak. Likewise, nonnegativity of the original first-node certificate would establish neither full-panel exclusion nor **SV**. Those remain the request’s stipulated decision directions. :chatgpt-content-reference{index="0"}

### Verification and scope

The authoritative TXT was read in full: **5,001 bytes, 94 LF**, valid **UTF-8**. Its computed hash is recorded in the verdict. The complete predecessor’s **SHA-256** matched the requested hash, and its **Git blob** matched the pinned repository object. The requested limited independent audit was also read; it accepts the predecessor’s geometry and sufficient implication, not a source sign.  

**The new mathematical derivations have not received independent review.** No coefficient numerics, mathematical runtime, Lean execution, repository write, route promotion, or RH claim occurred. The constants \(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional.

**Verdict SHA-256**
```text
4398b4aeb4674b7d0df9eee2efc88b44e84eb6238539d17daf1804962268e2d8
```