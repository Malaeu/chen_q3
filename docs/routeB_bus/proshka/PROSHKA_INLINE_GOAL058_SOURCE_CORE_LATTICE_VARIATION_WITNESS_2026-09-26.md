Ы. **OPEN_SOURCE_LATTICE_WITNESS.** Neither a negative fixed-panel margin for the actual source nor its uniform exclusion is established.

:chatgpt-content-reference{index="2"}[Read the full PAPER verdict](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_LATTICE_VARIATION_WITNESS_2026-09-26.md)

### What the argument proves

The **frozen panel remains unchanged**:
\[
N=\lceil L\rceil,\qquad 0,m+1,\ldots,m+N.
\]

The new reduction concerns the coefficients needed to evaluate those same samples. With the explicit analytical split
\[
K=N+\lceil L^4\rceil,
\]
the argument constructs a finite-coefficient panel margin \(U_m^{[K]}\) and proves, for **every admitted selected \(L=\log m>120\)**,
\[
\boxed{
\left|U_m^{\mathrm{lattice}}-U_m^{[K]}\right|
\le \eta_mE_{11}<\frac{E_{11}}{48},
\qquad
\eta_m=\frac{1}{4\sqrt{2L}}+\frac{1}{24L^2}\longrightarrow0.
}
\]

This is a **proved error bound**, not a source-sign result. The proof retains the full low \(\varepsilon_m\) block, the positive and negative Fourier indices, the diagonal, and the interference between retained and omitted coefficients. Every retained coefficient still uses its complete source series over \(r\ge1\). The original \(E_{11}\), including the physical exterior, remains the denominator.

The verdict also derives a **lower bound for the panel margin** by completing a square in the unknown coefficient-tail energy. A nonnegative source value of that bound would exclude a negative panel margin even under the most adverse remaining tail. **Its source sign is not proved either.**

### The remaining decision

The original margin now has the certified enclosure
\[
\boxed{
U_m^{\mathrm{lattice}}
\in
\left[U_m^{[K]}-\eta_mE_{11},\;
      U_m^{[K]}+\eta_mE_{11}\right].
}
\]

A source proof that the **upper endpoint is strictly negative** at an admitted cell would provide the requested witness and refute **SV only**. A source proof that the **lower endpoint is nonnegative for every admitted cell** would exclude this fixed-panel witness—but would not prove SV, because variation between sample nodes remains uncontrolled. Those are the original decision directions. :chatgpt-content-reference{index="0"}

The one bounded **CODEX DIRECTIVE** is therefore `TEST_SOURCE_CORE_FINITE_COEFFICIENT_PANEL_MARGIN`, using the same panel and the enclosure above. No different panel, numerical search, or replacement source is proposed.

**The actual source sign remains unpaid.** The constants \(C_0=128\), \(C_{\mathrm{int}}=134\), and \(C_2=146\) remain conditional; no downstream sign or RH conclusion follows. :chatgpt-content-reference{index="1"}

The predecessor’s **SHA-256** and **Git blob** were matched locally against the requested hash and pinned repository object. **The new mathematical derivations have not received independent review.** No mathematical runtime, Lean execution, or repository write was performed.

**Verdict SHA-256**
```text
699879b62accfe76f0130e77224957bccf153510c266383cb39c65c73fd9cc13
```