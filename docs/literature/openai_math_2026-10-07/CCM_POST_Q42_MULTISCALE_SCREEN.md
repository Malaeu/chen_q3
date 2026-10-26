# Post-Q42 multiscale supplier screen — no new attempt count

2026-10-26. Original P, complete signed C0 and consumer unchanged.
Q42 repairs the entire artificial pole hierarchy but leaves C0 coefficient1.
This screen checks the earlier dilation/renewal fork before new computation.

## Confirmed duplicate

CCM_Q20_SELBERG_PAIR_ATTEMPT.md already contains the full actual
Lambda2=Lambda log+Lambda*Lambda identity, weighted pair return, Selberg
O(x) recurrence, its information-loss discriminator and local pole check.
CCM_Q03_AFFINE_RETURN_TEST.md already rules out treating that coefficient
identity as an independent positive credit. No repeated Selberg computation
is counted as a fresh failed attempt.

## Buchstab entrance and exact signed extension

Primary: Kevin Ford, Sieve Methods Lecture Notes, Spring2023,
https://ford126.web.illinois.edu/sieve2023.pdf , printed p40 Lemma3.8,
and p41 proof of Theorem3.9, read through the web PDF text.
The least-prime partition is exact; its following scalar estimates use
monotonicity of a nonnegative sieve measure. No such monotonicity is
imported for the signed CCM weights.

For any finite Hermitian weights B_n, define S_B(z) as the sum over n<=m
having no prime factor <=z. For 2<=w<z exactly
 S_B(z)=S_B(w)-sum_{w<p<=z} sum_{n<=m, p|n, Pminus(n)=p} B_n.
The inner supports are disjoint. This applies to the complete original-P
matrix weight (with whatever source coefficient the chosen exact fork uses)
without splitting temporal or mode cross terms. Prime powers are classified
by their least prime, not deleted. The n=1 convention is Pminus(1)=infinity.
No hyperbolic or projection error arises from this finite partition.

But dropping a class or inserting scalar upper/lower sieve inequalities
requires a justified Loewner sign for its weighted contribution. Coefficient
positivity alone does not supply that sign. Q32 order-transport preflight
proves every normalized original test g_c(x)=c*h(x)c changes sign on the
continuous interval. This does NOT by itself prove a negative value at a
particular integer/prime; no such stronger conclusion is asserted here.
An actual signed sieve supplier has not been supplied by Lemma3.8.

Taking norms per atom after the disjoint partition gives exactly the same
sum_n ||B_n|| as before it, so reindexing alone saves no absolute budget.
This does not exclude cancellation within or across least-prime classes.
The full current bound remains A<=s_keep P, s_keep<=6sqrt(m)+6m^(1/4),
T_gtR<=(s_keep+b_div)P, PK_mP>=-(s_keep+50log(m)+8)P.
No additional fees or favorable sign are invented; exponent unchanged.

## Scope

A source/hypothesis screen, not a new asymptotic counterexample or full
arithmetic attempt. No numerical source evaluation, no Lean/Arb, no Q43.
Need a genuinely signed weighted supplier, not a new name for the partition.
Read-only post_q41_supplier_screen completed: two focused ask dictionaries
returned INCOMPLETE due q3_docs freshness. Q20/Q03/Q39 are verified
duplicates or missing signed inputs; no distinct worked supplier found in
this bounded screen. No global literature-absence claim.
