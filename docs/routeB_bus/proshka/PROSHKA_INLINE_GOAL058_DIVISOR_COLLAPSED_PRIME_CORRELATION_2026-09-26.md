Ы. **OPEN_DIVISOR_CORRELATION.**

:chatgpt-content-reference{index="2"}[Complete PAPER verdict — Markdown](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_DIVISOR_COLLAPSED_PRIME_CORRELATION_2026-09-26.md)

**Neither requested family conclusion is established:** there is no proved finite \(C_{\rm div}\) for the eventual lower-order bound, and no proved leading arithmetic contribution on an unbounded selected-index set. The full three-term cancellation in **(D)** remains unpaid; its exactness alone does not provide either estimate. :chatgpt-content-reference{index="0"}

### New source-relative bound

Split the actual error correlation into contributions whose arguments lie on the **same physical half-line** and on **opposite half-lines**. For the same-side contribution, define
\[
\mathscr S_m^{>\sqrt m}
=
4\sum_{\nu>\sqrt m}\frac{\Lambda(\nu)}{\sqrt\nu}
\int_0^\infty f_m(u)f_m(u+\log\nu)\,du.
\]

The verdict proves, for every admitted selected cell with **\(m\ge16\)**,
\[
\boxed{
\left|\mathscr S_m^{>\sqrt m}\right|
\le
\mathfrak r_{\rm side}(m)E_{11}(m)
\le
\frac{2\log m}{m^{1/4}}\,E_{11}(m),
\qquad
\mathfrak r_{\rm side}(m)\to0.
}
\]

This includes **every prime power** in that range. The proof uses the actual exterior source decay once the shifted argument leaves the window.

**It is not a bound for the full arithmetic correlation.** In the opposite-side contribution, both arguments can remain inside the window when \(\sqrt m<\nu<m\). That contribution cannot inherit the same-side estimate.

### Whole-line summation is now justified

Using the exact reflection symmetry of \(g\), the verdict turns
\[
2\int_{\mathbb R}g(u)Z_g(u)\,du
\]
into an **absolutely convergent divisor-weighted reciprocal-source series**, with an explicit exponential majorant. Both physical tails remain.

It also proves
\[
\boxed{
\lim_{u\to-\infty}e^{u/2}Z_g(u)=-\tfrac12,
\qquad Z_g\notin L^2(\mathbb R).
}
\]
Thus an **unweighted \(L^2\) estimate for \(Z_g\)** is unavailable. This does not invalidate the pairings in (D): their convergence is justified separately.

### One next PAPER test

**`TEST_SOURCE_SAME_SIDE_DILATION_HEAD`**

The file isolates the remaining same-side range \(2\le\nu\le\sqrt m\), with its exact four-term source expansion. The two mixed terms retain their different integration domains; the restricted divisor weight is not silently replaced by \(\log k\).

A proved saving for this head, together with the bound above, would pay the **entire same-side component**. The opposite-side component would remain separate. Conversely, a leading same-side contribution would require a cancellation analysis—not automatically establish `DIVISOR_CORRELATION_KILLED`.

**Transfer, \(J_m\), compression dominance, selected-vector activity, axis gap, first \(\tau_j\) sign, and Schur-floor remain open. No RH claim is made.** The new PAPER derivations have not yet undergone independent audit.

**SHA-256**
```text
2a02d6bc989b4a990f81ab5eff2d277897fd28657df5fff91e3df037a63292eb
```