# Positive complement after the Gridnev–Garcia transfer obstruction

Status: own exact finite-dimensional identity with a bounded diagnostic;
no source retention estimate, descent, T or RH proof.
Previous goal turn made progress: DIAGONAL independent audit and primary
threshold mechanisms were committed/pushed in 1a4966a4. GREEN subsequently
received this calculation in its complete attached request; response arrived
in bf8612ad. See GREEN_VERDICT_AUDIT for the stronger literal anchor theorem.

## Attempt: remove the one nonpositive jump mode

Keep the literal even matrix A=J+uu*-C I. Assume for this calculation only
that mu1(J) is simple and its exact updated bottom beta=lambda+C lies strictly
between mu1 and mu2. Neither strictness nor simplicity is claimed cofinally.
Choose unit e1, J e1=mu1 e1, and decompose

    u=b e1+u_plus, f=a e1+v, v perpendicular e1,
    R=(J_plus-beta)^(-1), S=<u_plus,R u_plus>, T=||R u_plus||².

Then R is positive on the complement and the exact eigen-equation gives

    v=-a b R u_plus/(1+S),
    beta-mu1=b²/(1+S),
    |a|²=1/[1+b² T/(1+S)²].                       (PC1)

All displayed formulas use real coordinates; complex conjugates give the
corresponding Hermitian statements. Under the strict assumptions a and b
cannot vanish: otherwise positivity on the complement forces f=0, or the
uncoupled e1 would remain a lower eigenvector.
The rank-one update is exact, retaining the complete original prime, arch
and pole terms. No physical multiplication or carrier enlargement occurs.

Proof: complement equation is v=-R u_plus(ab+<u_plus,v>).
Pairing with u_plus solves ab+<u_plus,v>=ab/(1+S); the e1 equation gives
the second formula, and normalization the third.
With d=mu2-beta>0, T<=S/d. Consequently

    ||v||²/|a|² <= [(beta-mu1)/d] S/(1+S).       (PC2)

This is NOT a positive-kernel representation in physical space, nor an
independent source bound. Exact minimality supplies the interlacing location;
the block identities themselves hold for any eigenvector in this interval.
The missing information is the source-weighted inverse-square moment T,
not just positivity of R or the smallness of S.

## What a residual changes

For a unit trial q=a e1+v, rho=<q,(J+uu*)q>, residual r=(J+uu*-rho)q,
assume separately mu1<rho<mu2 and define R,S at rho. Writing r_plus for the
complement residual and t=<u_plus,q>, one gets exactly

    v=R r_plus-R u_plus t,
    t=[ab+<u_plus,R r_plus>]/(1+S).

Thus even the first correction costs ||r_plus||/(mu2-rho). There is no
reason to drop it merely because ||r|| is small absolutely. If rho is outside
the interval, positivity of R is unavailable; endpoint cases need their own
kernel-compatible block treatment. No escaping quasimode is promoted to a
bottom by this calculation.

## Literal finite diagnostic

Using the same full source matrix and exact pole coefficients as
NOESCAPE_JUMP_RANK_ONE_ATTEMPT, 90-digit floating arithmetic gives:

| m | mu2-beta | squared overlap with e1 | S | b²T/(1+S)² |
|---|---:|---:|---:|---:|
|4|1.71800934e-5|0.5173917223|0.0146177039|0.9327715481|
|8|4.12837224e-15|0.3584310211|0.0081070886|1.7899370900|
|16|3.05179305e-32|0.2564569045|0.0038314725|2.8992906112|

PC1 agrees with direct eigenvector overlap to absolute errors below
1.3e-87,1.5e-77,3.5e-61 respectively. These are floating algebra diagnostics,
not interval certificates, not bounds for arbitrarily large m.
The previously computed h-overlap is near 0.9984 at m16, so e1(J) must not
be silently identified with the theta profile. The table does not prove
decay of the e1 overlap or exclude retention through the complement.

## Exact result and remaining question

Removing the single nonpositive mode repairs spectral positivity, but does
not repair the uniform Green estimate: the positive inverse has a tiny gap,
and the squared-resolvent moment remains unbounded by current source estimates.
For fixed-jet retention, one additionally needs the physical/jet profile of
the reconstructed vector a e1+v; a bound on |a| alone would not suffice without
control of cancellation against v. This is narrower than a generic statement
that every positive-resolvent route fails.
Next question: can exact theta radicality bound the joint source-weighted
resolvent response, including its jet pairing and residual amplification,
rather than bounding the inverse norm alone? No such estimate is supplied here.

Bounded independent PAPER check reproduced PC1, PC2 and the residual blocks.
It emphasized that the e1 scalar equation also acquires r1 for trials;
no exact secular equation is claimed for them. Endpoint cases stay excluded.
