Ы. **OPEN_SOURCE_VARIATION.** The requested **SV** inequality is not proved on the whole selected tail, and no source-based negative variation margin is established.

:chatgpt-content-reference{index="2"}[Read the full PAPER verdict](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_HALF_LINE_DENSITY_VARIATION_2026-09-26.md)

### What is proved

For **every admitted selected** \(m\) with \(L=\log m>120\), the new argument bounds a proper part of the actual **half-line spectral density**:
\[
\boxed{
\int_{|\xi|\le m/L^2}|\rho_m'(\xi)|\,d\xi
\le \frac{E_{11}}{\sqrt6}<\frac{E_{11}}2,
}
\]
and
\[
\boxed{
\int_{|\xi|\le m/L^2}\rho_m(\xi)\,d\xi
\le \frac{2E_{11}}{3L}.
}
\]

The proof retains the nonzero **endpoint block** \(d\). Its central-frequency moments are bounded using cancellation in the exact **Dirichlet kernel**, with the amplitude paid by the admitted exterior-source estimate. The denominator remains the original \(E_{11}\), including the physical exterior.

These are **cofinal proper-contribution bounds**, not a proof of the full variation budget.

### What remains unpaid

Write
\[
\mathcal V_c=\int_{|\xi|\le m/L^2}|\rho_m'|,
\qquad
\mathcal V_h=\int_{|\xi|>m/L^2}|\rho_m'|.
\]
The remaining comparison is exactly
\[
\mathcal V_h\le16E_{11}-M_m-\mathcal V_c.
\]

The new bound does not settle this inequality. In particular, the separated-denominator argument used centrally cannot extend through the remaining **carrier frequencies**, where the literal Fourier moments become resonant.

### The next test seeks a genuine negative witness

The verdict derives exact density values at the **Fourier lattice**, including the diagonal and a parity-restricted sum of the complete source coefficients. A fixed finite panel of those values gives
\[
\mathcal V_m\ge\mathcal W_m,
\qquad
\boxed{
\Delta_m^{\mathrm{var}}
\le U_m^{\mathrm{lattice}}
:=16E_{11}-M_m-\mathcal W_m.
}
\]

A source proof that \(U_m^{\mathrm{lattice}}<0\) at an admitted selected cell would **refute SV**. No such source witness is established here. A nonnegative or unresolved panel margin would prove neither SV nor its negation.

This would reject only the sufficient variation interface—not the original lag statement. **\(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional**, and no downstream sign or RH conclusion follows.  

The predecessor’s **SHA-256** and **Git blob** were matched locally against the requested hash and pinned repository object. **The new mathematical derivations have not received independent review.**

**Verdict SHA-256**
```text
575b7b2a88916b4d245a9d030ed2abf0e87530c895f8f70cfb41baaa769ba170
```