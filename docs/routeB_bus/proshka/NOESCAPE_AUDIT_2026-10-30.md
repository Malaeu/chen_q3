# NOESCAPE — bounded independent PAPER audit, Mac 30.10

Source: PROSHKA_VERDICT_NOESCAPE_2026-10-30.md, SHA-256
fdfd384345b69d7565100b93ef57348eb6944bdbaf014a01c001df007129aded.
Independent reader: noescape_audit (read-only researcher; not Proshka author).
Root checked the L12 min-max/singular-value argument and replayed the L14
counterexample with exact rational arithmetic for m=2,...,6.
This is a bounded PAPER audit, not Lean verification or a source-bound proof.

## Findings

No algebraic defect found in the reviewed central implications.

- L1-L4: fixed-order quasimode estimates give arbitrarily many eigenvalues in
  every fixed polynomial band near zero. They do not select the bottom.
- L5-L6: the literal parity negative witnesses supply the lower-floor/RH
  implication and fixed-jet persistence implies RH. Persistence is not proved.
- L10-L11: the split retains window/exterior corrections and prime powers.
  Absolute exterior smallness does not pay division by tiny excited eigenvalues.
- L12: min-max for A^2 puts at least r levels in [-delta,delta]; one-sided
  count below positive mu allows no additional negative levels. Equal finite
  dimensions transfer the singular-value angle bound to the entire low space.
- L13: vanishing residual plus this count implies RH even at growing rank;
  source count remains unpaid. The package is not asserted equivalent to RH.
- L16-L18: one fixed pairing or fixed compact observable suffices. Density of
  the fixed derivative family is an inherited CONFINE premise; its earlier
  independent audit is recorded in CODEX_AUDIT_CONFINE_2026-10-30.md.

## Exact root replay of L14

epsilon=2^(-m^2), t^2=4^(-m)/sum_{j=0}^m 4^(-j),
(Delta/mu)^2=1-t^2+epsilon^2*t^2. Python fractions.Fraction verified strict
0<(Delta/mu)^2<1 and the one-sided count=1 for m=2,...,6.

| m | t^2 | (Delta/mu)^2 |
|---|---|---|
|2|1/21|1707/1792|
|3|1/85|22020097/22282240|
|4|1/341|1460288880641/1464583847936|

The symbolic formula makes t^2 tend to zero and Delta/mu tend to one. This
checks the counterexample to strict-margin-implies-uniform-overlap; it says
nothing negative about the actual theta source.

## Operational return

Same living Proshka chat located through visible conversation messages:
https://chatgpt.com/g/g-p-6aafae55d09481919c5971b73d862184-sort-rh-marz-2026/c/6ae1f6d5-8024-83ed-a7e1-cf8ebdbc9a93
Title: Generate Verdict File. It contains STIELTJES, MARKOV, CONFINE and
NOESCAPE; NOESCAPE has completed naturally. No new message sent at this point.

The m8 handoff script computes X=T-F, not an independent identity check.
Saved m16/m20 tables lack eigenvector coefficients. However existing
phase5_scripts/edge_ledger_build.py contains a reusable Arb matrix/eigenpair
primitive; this corrects a narrower initial search miss. The bounded m16
eigenpair computation completed at 120 dps in 8.586 seconds. Its second
level is 4.7334184764486e-32; all 289 source-entry midpoint comparisons
agree diagnostically within 1e-50. Files: ../thetagrade_2026-10-28/
noescape_m16_eigenpair.py and .json. A separate read-only reviewer reran the
eigenpair, checked all 52 serialized balls and all five source hashes, with
no material findings. JSON SHA256:
41b9048af2cd698c521d062dc412d94c70acaacc9fa7efd5cb4896db3bbc2f29.

Qualification: the real-coordinate balls enclose a common nonzero real
vector, because the exact matrix is real symmetric and its eigenvalue is
real/simple. The norm ball containing 1 is only a consistency check.
Downstream unit-vector use must interval-normalize by sqrt(sum X_j^2),
whose lower bound is positive, or retain the norm in a scale-invariant ratio.
The recorded lower/upper strings are endpoint balls, not exact decimals.
The builder/source identity still requires analytic mapping; the mpmath
comparison is diagnostic. Independent F/X quadrature and full relative
tail/error certification remain separate unfinished work.

Open source obligations: inverse-weighted leakage with margin below one;
or saturated one-sided source count with vanishing residual;
or one persistent fixed compact observable/pairing. None is discharged here.

## Bounded direct-space follow-up

The independently derived representation is X=k(h_out,v)−k(W,v)+<PW,A_m v>,
with same-window W and complete physical source pairings. It avoids an
algebraically decaying high-mode truncation. The bounded worker script
noescape_m16_direct_x.py completed the normalized source overlap and B,
then only the exterior pairing before timeout. B≈4.22699336601418e−33
(Arb enclosure in JSON); k(h_out,v)≈1.75169e−35 is mpmath diagnostic with
large signed component cancellation. It is NOT X. k(W,v), X, F and a full
relative quadrature certificate remain unpaid. Do not label D_ext decided.
The researcher's exterior arch tail formula assumed S>=L; its later
example S=b+0.3 violated that assumption and was not used. The worker
was directed to use S=L+0.3 instead.

## Independent finite F/X diagnostic completed

Fast W quadrature (64/96 nodes,60dps) gave k(W,v)≈1.71163502246749e−35
and direct X≈4.00560883248790e−37, X/B≈9.47626e−5. The order difference
is diagnostic only. Separate Fourier summation gives F_96≈−4.22739392689743e−33;
F+X+lambda<h,v>≈−1.85e−53. Both sides were computed independently;
none was defined by this closure test. The retained sums still need certified
errors. A new independently checked analytic tail budget beyond96 is
<4.258e−37 (NOESCAPE_FOURIER_TAIL_2026-10-30.md), not an empirical
truncation difference. Finite-F interval propagation is the next bounded step.

## Interval F and identity-derived exterior bound (independent review)

noescape_m16_fourier_arb.py/.json propagate retained real-vector boxes
through interval normalization, exact closed kernel and Acb xi samples.
The accepted Fourier tail proof and M16_ARB_SOURCE_MAP supply the analytic
parts; the retained overlap's omitted theta tail is <7.909e−224<1e−210.
An independent read-only recomputation reproduced F, B and the final bound.
The same exact unit eigenvector is enclosed in both overlap and F computations.
Xi realness comes from the functional equation/conjugation, not merely an
imaginary enclosure containing zero.

Conditional on the inherited exact NOESCAPE source identity and trusted
Arb/Acb enclosure semantics,

    |X_16,1|/B < 0.000195481 < 0.0002 < 1/4.

This is a proved finite-cell, identity-derived bound. It is NOT an independently
quadrature-enclosed X or an independent interval check of the identity. The
separate direct-X diagnostic agrees, but its quadrature budget remains unpaid.
Thus the finite smallness prediction is supported rigorously via the identity;
the stronger independent-computation requirement of NOESCAPE section11 is
not labelled complete. No cofinal inference or proof of T/RH follows.

Verified script SHA256:
7fa097648752ec0043679c72447611a44dc60d26b041e18eed10b8be60cf378c; output:
cd5092bb420f53f0300639350d3e154a6a2b30aadd5fb949003e03480ad85d5e.
The generated JSON's tail-review PENDING wording describes its creation time;
the subsequent mathematical and numerical reviews are recorded here.

## Direct-X certificate follow-up remains open

M16_DIRECT_X_CERTIFICATE_GAP_2026-10-30.md reduces the truncated W convolution
to incomplete gamma functions, with explicit distinction from the full image
and theta sums. Bounded Arb outer integrals did not yield an enclosure.
Total independent absolute error must be below approximately1.05635e-33;
the paired arch integral and all omitted source tails remain unpaid.
No change to the finite identity-derived bound or cofinal status.
