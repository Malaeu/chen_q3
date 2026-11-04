# Independent inherited rank–trace consumer audit

DIAGNOSTIC_NEVER_A_PROOF. The assigned inequalities in `INPUT_RANK_TRACE.md`, §§3 and5, are valid with the improved sampling cap σ=L+1/5 supplied by the independently audited gamma5 lemma. No dimension, multiplicity or off-line positive-index obstruction was found. **The same finite inputs actually imply at least15 simple critical-line upper zeros, and at least100 distinct upper zeros, below the strict cutoff T300.** The original14 is a valid weaker conclusion. This strengthening is exact integer bookkeeping, not an additional source estimate or route-state change.

## Abstract inequality

In (3.3), let Π project onto ran P and Σ onto ran R, where B=R−N is its positive/negative spectral decomposition. Since RN=0, expansion of the five squared/block terms gives

    ||P+R−N||F²−c trP−2c tr(R−N)+c²rank(P)/4+c²rank(R).

The block decomposition of N contributes ||N||F²; X=P−ΠNΠ contributes the cross term −2tr(PN); the R-square contributes −2c trR; and the final trace term restores +2c trN. Thus the identity has exactly the printed constants and signs. All terms are nonnegative: tr(PR)≥0 and 0≤tr(ΠN)≤trN. Replacing actual ranks by upper bounds proves (3.1); c=2 gives (3.2). No positivity assumption on P+B enters.

## Same physical normalization and zero blocks

The carrier has dimension m+1. Parseval in the entire even L2 basis gives

    2||e_m(γ)||²≤L+sin(Lγ)/γ.

Every nontrivial zero has |γ|>5 by the audited theta–Mellin argument, so the right side is ≤L+1/5. For each simple critical-line upper zero, its two signed-height terms give the PSD rank-one matrix2e(γ)e(γ)^T. Dividing by σ therefore gives trace≤1 and rank≤1. Summing s1 such blocks yields P1≥0, rankP1≤s1 and trP1≤s1; equality or independence of their columns is unnecessary.

A critical-line zero of multiplicityν≥2 contributes one PSD direction, regardless ofν, but costs at least two units in the multiplicity count N. An off-line upper pair with common multiplicityν≥1 has a real symmetric block

    4ν[aa^T−bb^T],  a=Re e(z), b=Im e(z).

It has positive index at most one, even if a,b are linearly dependent or zero. Its two positive-height source zeros cost at least two units in N, and count as two distinct upper zeros. Positive index is subadditive for a finite sum: intersect the nonpositive spectral subspaces of its summands to obtain a subspace of codimension at most the sum of their positive indices on which the total quadratic form is nonpositive. Hence

    n+(Bbad)≤s2+b,  N≥s1+2s2+2b,
    Nd=s1+s2+2b.

Multiplicity multiplies a block; it never creates additional independent positive directions. A finite-dimensional carrier can only lower these ranks/indices. The argument therefore needs no equality between dimension m+1 and N.

Apply (3.2) with r=s1 and b_index=s2+b. Using trP1≤s1 gives

    Phi(head/σ)≤3s1+4s2+4b.

Since the right side is ≤s1+2N, the simple-count inequality follows. It is also ≤2Nd+N, so the distinct-count inequality follows. The strict cutoff excludes all height-T blocks into the tail; their possible presence does not invalidate use of an upper bound for the inclusive zero count.

## Head–tail and finite integers

For signed tail R, ||R||F≤||R||1 gives exactly (5.3), with no PSD requirement. Substitution of a≥895.9, q≤5481, E≤12.5, σ=log300+1/5 produces

    Phi(head/σ)≥F−>383.69377706.

The independently computed Rosser bound185.3596…<186 gives integer N≤185. The printed ceiling consumer therefore yields s1≥14 and Nd≥100 without any census.

There is a slightly stronger exact consequence. Put k=s2+b, a nonnegative integer. Then

    3s1+4k>383.69377706,   s1+2k≤185.

If s1≤14, then

    3s1+4k≤3s1+4 floor((185−s1)/2)≤383.

The last maximum occurs at s1=13; at s1=14 the bound is only382. This contradicts the score lower bound. Consequently **s1≥15**. No possible high multiplicities evade this, because they only consume more of N. Nd≥100 remains sharp for these abstract constraints: s1=15,s2=85,b=0,N=185 permits score up to385 and Nd=100. This is only feasibility of the bookkeeping constraints, not construction of a zeta spectrum.

Thus, conditional on the separately replayed source/tail interval gates and imported explicit count theorem, the stronger finite statement is: at least15 simple critical-line upper zeros and at least100 distinct upper zeros with0<γ<T300, with safe fractions15/185 and100/185. These are finite lower bounds; the actual total count, zeros individually, and asymptotic results are not determined by this consumer audit.
