Ы. **OPEN_SOURCE_PROJECTED_MESH_INCREMENT_BUDGET.**

The authoritative TXT and pinned predecessor match their stipulated **SHA-256** hashes. **PIB128 is neither proved nor refuted:** no universal nonnegative bound for \(\mathscr Q_m\), and no strictly negative value at an actual admitted cell, has been established.

:chatgpt-content-reference{index="0"}[Complete PAPER verdict — full argument, source checks, and one bounded CODEX DIRECTIVE](sandbox:/mnt/data/PROSHKA_VERDICT_GOAL058_SOURCE_CORE_FIXED_128_PROJECTED_MESH_INCREMENT_BUDGET_2026-09-27.md)

### A projected proof method is ruled out

The verdict proves that splitting the **forward increment** into its moving-endpoint contribution and its remaining bulk contribution produces **two sequences of infinite squared norm on the prescribed infinite tail**.

The endpoint contribution is the nonzero constant
\[
a_m^+=\int_L^{L_+}\frac{g(\lambda/2)}{\sqrt\lambda}\,d\lambda<0
\]
at every tail index. The bulk contribution tends to \(-a_m^+\). Their constants cancel, leaving the actual increment finite.

**This rules out separate endpoint/bulk norm estimates—not PIB128.** The divergence of the separated pieces supplies no lower bound for the combined \(W_m\).

### The exact action–increment distinction

The combined derivative has the **endpoint-cancelled representation**
\[
e_n'(\lambda)=
\frac{2(-1)^n}{\lambda^{3/2}}
\int_0^{\lambda/2}
\left(u g'(u)+\frac12g(u)\right)
\cos\!\left(\frac{2\pi nu}{\lambda}\right)\,du.
\]

Keeping both existing projections and their different orientations, the verdict constructs a coupled velocity \(\mathbf z_m(t)\) satisfying
\[
\mathbf v_m=\int_0^1\mathbf z_m(t)\,dt.
\]
Its **projected action**, the integrated squared velocity, obeys
\[
\mathscr A_m:=\int_0^1\|\mathbf z_m(t)\|^2\,dt
=W_m+\mathscr V_m^{\mathrm{path}}.
\]

For the **actual complete source**, the new argument proves
\[
\boxed{\mathscr V_m^{\mathrm{path}}>0}
\]
at every admitted cell. The proof uses real analyticity and decay to rule out a constant projected velocity; it does not substitute an unprojected norm.

### One narrower test remains

The proposed **coupled projected dilation-action budget** is
\[
\mathscr R_m
:=E_m+E_{m-1}-4L^2\mathscr A_m-2LO_m\ge0.
\]
The exact relation is
\[
\boxed{
\mathscr Q_m
=\mathscr R_m+4L^2\mathscr V_m^{\mathrm{path}}.
}
\]

Thus a universal proof of \(\mathscr R_m\ge0\) would prove strict PIB128. But this candidate is **genuinely stronger**: a negative \(\mathscr R_m\) would refute only the action budget, not PIB128. Its relative source estimate remains unpaid; positivity of the variance does not supply that estimate.

No predecessor disjunction arm has been selected. MT128, MG128, C128, PC, SV, lag, Schur-floor, and RH remain open. The new derivations have not received independent review.

**Verdict artifact SHA-256**
```text
b43493e3bfe6ce83a440dde89e732f09882d7940feb4c831b9c4d812d6010b4b
```