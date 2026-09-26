Ы. **OPEN_SOURCE_LOG_MOMENT_PEAK.** Neither the requested logarithmic peak nor exclusion of its certificate on every admitted selected cell is established.

:chatgpt-content-reference{index="3"}[Read the full PAPER verdict](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_LOGARITHMIC_MOMENT_PEAK_2026-09-27.md)

### What is proved

The **paired logarithmic moment** has an exact contour representation
\[
Z_m=Y_m+\mathcal E_m,
\]
where \(Y_m\) is the real part of the complete source integral on the horizontal line \(\operatorname{Im}z=1/(2L)\).

The vertical side at the origin contributes **exactly zero to the real moment**. The opposite side is retained and bounded, for every admitted selected \(L=\log m>120\), by
\[
\boxed{
|\mathcal E_m|
\le
\frac{256L(L+2)}{\sqrt{\pi m}}\sqrt E
<
\frac{\sqrt E}{64L^2}.
}
\]
The proof uses the complete theta-source series and the original \(E\), including its physical exterior. It does not split the logarithmic cosine from its compensating sine or discard either endpoint.

**This pays an endpoint correction—not the main source moment.** The sign comparison for \(Y_m\), and therefore for the complete \(Z_m\), remains unpaid.

### The remaining coherence is localized to finite source prefixes

Using the already fixed \(N=\lceil L\rceil\), define the **unweighted even-offset prefixes**
\[
S_{m,R}=\sum_{\ell=1}^{R}e_{m+2\ell},
\qquad 1\le R\le N.
\]
The verdict gives their exact finite-kernel source integrals and an exact summation-by-parts representation of the logarithmic moment. Every larger offset is retained in a remainder satisfying
\[
\boxed{
|Z_m^{\mathrm{far}}|
\le
\sqrt{\frac{L}{4(2N-1)}}\,\sqrt E
<
\frac{\sqrt E}{2}.
}
\]
The cross term between this remainder and the retained moment is accounted for. The original \(K=N+\lceil L^4\rceil\), panel, low block, reflected Fourier indices, and signed correction remain unchanged.

### One next PAPER lemma—not a proved source bound

The single **CODEX DIRECTIVE** is `TEST_SOURCE_CORE_EVEN_PREFIX_CANCELLATION`, testing
\[
\boxed{
L\,S_{m,R}^{\,2}\le49R E
\quad
\text{for every admitted selected }L>120
\text{ and every }1\le R\le\lceil L\rceil.
}
\]

The file proves the implication
\[
\text{this source cancellation bound}
\quad\Longrightarrow\quad
\boxed{\chi_m\ge\frac{827}{240}>0}
\]
on the entire stated family. That would establish **LOG_MOMENT_CERTIFICATE_EXCLUDED**, and nothing stronger.

**The cancellation bound itself is not proved.** A negative source discriminator
\[
49-\frac{L S_{m,R}^{\,2}}{RE}<0
\]
would refute only this proposed prefix lemma; it would not prove a logarithmic peak, because later weighted prefixes can still cancel. Conversely, an actual negative \(\chi_m\) must produce at least one such finite-prefix violation.

This preserves the original distinction: exclusion of the narrower logarithmic certificate would not exclude the first-node certificate, the full panel, or **SV**. :chatgpt-content-reference{index="0"}

### Verification and scope

The authoritative TXT was read in full: **5,824 bytes, 109 LF**, valid **UTF-8**. Its computed checksum is recorded in the verdict. The complete predecessor’s **SHA-256** matches the stipulated hash, and its **Git blob** matches the pinned repository object. The requested limited independent audit was read; it accepts the predecessor’s identities and correction bounds, not a source sign.  

**The new mathematical derivations have not received independent review.** No coefficient numerics, mathematical runtime, Lean execution, repository write, route promotion, or RH claim occurred. The constants \(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional.

**Verdict SHA-256**
```text
47bc3636eccbe16977658314dd1847816675c74e501fd55e3c5f091695d71f52
```