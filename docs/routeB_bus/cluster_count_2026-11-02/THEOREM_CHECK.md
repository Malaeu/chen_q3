# Exact theorem check: cluster counts versus the NOESCAPE guard

Read-only PAPER audit, 2026-11-02. No numerical scan, cofinal proof, or Git write.

Source fetched at `Malaeu/chen_q3@rh_clean`:
`docs/routeB_bus/proshka/PROSHKA_VERDICT_NOESCAPE_2026-10-30.md`.
Git blob: `453d2f7dfd14810b32ac89e24bb0f85c26ed7fcc`.
SHA256: `fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded`.
The 64077-byte local source reproduces this blob and SHA256.
All line references below are to these exact source bytes.

## What L12 actually assumes and concludes

**CONFIRMED**, L12 lines634–663, equations(5.1)–(5.3):
for a Hermitian A and a genuine r-dimensional subspace J,

`||A|_J|| ≤ δ < μ`, `μ>0`, `N_A(μ):=#{λ(A)<μ} ≤ r`

imply exactly r levels below μ, all in `[−δ,δ]`, hence `A≥−δI`.
For the entire signed low space `S=1_(−∞,μ)(A)H`,
every unit v satisfies `||P_J v||²≥1−(δ/μ)²`.
The residual is an **operator norm**, not a Rayleigh value or a columnwise
residual without Gram conditioning. The conclusion permits negative levels
down to −δ; it is not positivity when δ>0.

## Absolute and signed counts cannot be interchanged

For a positive threshold, the exact identity is

`N_A(μ)=#{|λ|<μ}+#{λ≤−μ}`.

The second term includes the negative boundary −μ. The positive boundary +μ
is excluded from both first counts. All counts include multiplicity.
Thus comparing `#{|λ|<μ}` with `dimension−N_ζ` does not check L12's guard.
The source explicitly flags this at lines691 and919–921.

Finite control: `A=diag(−1,0,2)`, `μ=1/2`, `J=span{the middle coordinate}` has r=1 and δ=0.
Its absolute count is1, but its signed count is2 and its bottom is−1.
An absolute-count replacement would accept precisely the hidden negative
direction that the theorem excludes.

## Required residual and separation budgets

The exact conditioned residual is given in L2, lines221–246, equation(2.4).
For a synthesis matrix B with full column rank and `M=B*B>0`, set

`Q=B M^(−1/2)`,
`Δ²=λmax(M^(−1/2)B*A²B M^(−1/2))`.

This pays rank, Gram conditioning, and every mixed residual direction.
For derivative jets the simpler source bound is equation(5.5), lines682–691:
`Δ² ≤ Σ_j ||A_m P_m h^(2j)||² / λmin(M)`.
Growing-rank constants and the Gram denominator must be established at that
rank; fixed-order decay cannot be substituted into a growing-rank formula.

**Direct lower-floor consumer:** L13, lines669–680, equation(5.4), allows
growing r_m and needs `Δ_m→0`, `Δ_m<μ_m`, and the signed upper count.
A uniform ratio is not needed for this lower-floor conclusion.

**Fixed-jet no-escape consumer:** L14, lines699–743, shows that merely
`Δ_m<μ_m` can give overlap tending to zero when their ratio tends to1.
Equation(5.9), lines774–782, requires a fixed finite r, fixed q<1,
an unbounded original family, `N_A_m(μ_m)≤r`, and `Δ_r,m≤q μ_m`.
The projected/global-jet angle from equation(2.5) is also paid.
For growing jets, fixed-coordinate tightness and projection/Gram control are
additional requirements for T: lines745–772, equation(5.8).
In particular, a proposed `r_m=d_m−N_ζ(T_m)` growing like `m/log m`
is not the fixed-rank hypothesis in(5.9). It may be a candidate for L13's
different growing-rank interface, provided its actual operator residual
vanishes and remains below the threshold and its signed count saturates.

## Does dimension minus a zeta-zero count supply J?

Let d be the actual parity-carrier dimension (d=m+1 in the even carrier).
Imposing `f̂(γ_j)=0` at q positive critical ordinates defines a kernel of an
evaluation matrix Z. For real even f, each positive ordinate supplies at most
one real scalar condition; its negative does not provide another independent
condition. Exact dimension is `d−rank(Z)`, not automatically `d−q`.
Multiplicity or repeated constraints must not be counted as independent rows
without the corresponding derivative conditions and a rank argument.

Those finite vanishing conditions do **not** make this subspace radical for
the full source: the other zero contributions remain, including unexcluded
off-critical zeros. They also do not give a bound on `||A|_J||`.
Even a zero quadratic restriction `J*A J=0` would not imply `A J=0`;
mixed directions are part of the required residual.

The global theta radical cancels the complete zero set through its H factor.
Its finite physical projection does not preserve all these transform zeros
exactly. L1–L2 provide a residual/Gram budget for fixed projected jets;
they do not identify them with a finite-zero evaluation kernel.

Therefore `dimension−N_ζ(T)` is a useful comparison statistic only after the
height T, parity, multiplicity convention, and strict threshold are specified.
To spend it in L12 one still needs an independently constructed genuine J,
its conditioned residual below μ, and the **signed** upper count.
Choosing J to be the computed small-absolute-eigenvalue spectral subspace
does not supply an independent cofinal residual bound or exclude deep
negative eigenvalues.

## Consequence for the requested finite scan

Report separately `#{|λ|<μ}`, `#{λ<μ}`, `#{λ≤−μ}`, dimension,
the chosen zero-count height, and equality/uncertain boundary cases.
Agreement over m=8,…,40 is a finite diagnostic, not equation(5.9).
L3, lines248–263, also proves that every fixed polynomial threshold m^(−B)
eventually contains arbitrarily many absolute-near-zero levels; a bounded-rank
upper-count extrapolation at that threshold would contradict the source lemma.

**Verdict:** the saturation theorem is valid, but the proposed absolute-count
and dimension-minus-zero-count comparison alone does not meet its hypotheses.
This rejects that inference, not the literal spectral-count route.
