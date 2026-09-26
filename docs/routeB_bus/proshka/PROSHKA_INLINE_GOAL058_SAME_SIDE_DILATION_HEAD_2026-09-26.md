Ы. **OPEN_SAME_SIDE_HEAD.**

:chatgpt-content-reference{index="3"}[Complete PAPER verdict — Markdown](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SAME_SIDE_DILATION_HEAD_2026-09-26.md)

**Neither requested family conclusion is established:** there is no proved eventual lower-order bound for the whole head and no proved leading contribution on an unbounded selected-index set. The component-saving mechanism remains **unproved, not refuted**. These are distinct from bounds for individual pieces of the head. :chatgpt-content-reference{index="0"}

### Two contributions are now bounded

The verdict introduces the **one-sided Fourier transform**
\[
\Phi_m(\xi)=\frac1{\sqrt{2\pi}}\int_0^\infty f_m(u)e^{-i\xi u}\,du,
\]
which represents the same-side correlation without incorporating the opposite-side term.

For the complete head multiplier
\[
D_Q(\xi)=\sum_{2\le\nu\le Q}
\frac{\Lambda(\nu)}{\sqrt\nu}\cos(\xi\log\nu),
\]
the new PAPER derivation proves, on every admitted selected cell with **\(m\ge16\)**,
\[
\boxed{
\left|4\int_{|\xi|\le\sqrt m}
D_Q(\xi)|\Phi_m(\xi)|^2\,d\xi\right|
\le \rho_{\rm low}(m)E_{11},
\qquad
\rho_{\rm low}(m)\le
\frac{\log m}{2m^{1/4}}\longrightarrow0.
}
\]

The proof uses the **actual projection’s orthogonality** together with the admitted exterior decay. It retains the physical tails and the endpoint correction; in particular,
\[
\Phi_m(0)=\frac{G'(b)}{\sqrt{2\pi}}>0,
\]
not zero. The continuous-frequency split does **not** change the Fourier carrier or \(Q\). The exterior estimate used in this argument is confined to its source-proved domain. 

Separately, **all prime powers of exponent at least three** have the uniform bound
\[
\boxed{
|\mathscr S_m^{(\ge3)}|\le C_3E_{11},
\qquad
C_3=\frac{2(4+2\log2)}{1-2^{-1/2}}<48.
}
\]

### What remains unpaid

After these bounds, the unresolved quantity is the **joint high-frequency contribution of primes and prime squares**, evaluated against the full source density \(|\Phi_m|^2\). The verdict supplies its exact formula and the corresponding four-term source expansion. Neither mixed term, its moving boundary, nor the separate diagonal is removed.

The single next directive is **`TEST_SOURCE_PRIME_SQUARE_HIGH_FREQUENCY_CORRELATION`**. It concerns only
\[
\nu=p^2\le\sqrt m,\qquad |\xi|>\sqrt m,
\]
so it excludes exponent-one primes, higher powers, and the already bounded low-frequency region.

**A square saving would still leave the prime contribution open. A leading square contribution could still cancel against that prime contribution.** Neither result alone would decide the whole head.

The file combines the new bounds with the already paid \(>Q\) same-side tail only through an explicit remainder. The opposite-side correlation, transfer, \(J_m\), first \(\tau_j\) sign, and Schur-floor remain open. **No RH claim is made.** The new PAPER derivations have not yet undergone independent audit.

**SHA-256**
```text
39b02d5663ff7c918f8e0875375bd152d05148fc1f3a80c887529a8f93fe9ca2
```