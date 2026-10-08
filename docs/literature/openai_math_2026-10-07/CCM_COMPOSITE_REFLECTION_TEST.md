# Actual composite shifts: reflection test and its band boundary

2026-10-08. Own bounded attempt after Q8. Independent read-only q05_moment_audit PASS for R1–R4 and the source-hypothesis mapping; sparse_band_receiver separately checked the concrete m=16,R=2 control. C5, full SP and RH OPEN. This is a test of importing reflection positivity, not a replacement consumer.

## Exact obstruction and source

Q8 pays A+C_comp but does not control C_comp from below. Positive scalar weights on translations do not ensure a positive operator. The target remains CCM_COMPOSITE_SIGN_TARGET.md(C5), with the improved Q8 joint return and original three-constraint P, M=floor(m^alpha), R=floor(m^beta), fixed parameters. Q8(43) is another sufficient form of the unpaid signed comparison, not an estimate.

Use L=log m, a=L/2, and the finite actual set S={log n:R<n<m, n composite, b_R(n)>0}; weights w_s=b_R(n)/sqrt(n)>0. The n=m atom has exactly zero physical form and may be retained separately. On H=L2(0,L), let K be the zero-extended symmetric translation sum, whose finite Fourier compression is the original composite matrix. No prime powers or small-factor composites are removed from S.

The negative control outside the intended finite-band class is the unrestricted smooth test proved below. UNVERIFIED search hints were a positive Hankel/Laplace representation and a parity-resolved kernel comparison; any return must preserve the Fourier band, exponential moments and endpoints.

## Exact parity forms

For g on (0,a) define U_epsilon g(t)=g(t)/sqrt(2) on the left and epsilon*g(L-t)/sqrt(2) on the right, epsilon=+1 or -1. This is an isometry into the reflection parity sector. The reflected matrix blocks give exactly

    U_epsilon* K U_epsilon = T + epsilon H,             (R1)
    T(t,u)=sum_s w_s[delta(t-u-s)+delta(t-u+s)],
    H(t,u)=sum_s w_s delta(t+u-(L-s)), 0<t,u<a.

These are bounded finite sums of partial translations/reflections, interpreted as kernels acting by integration, not pointwise values of distributions. T contains all within-half shifts; H contains all cross-half shifts. In particular H must not be restricted only to s>a. Both blocks commute with conjugation; no sign is assigned to them.

Original reflection preserves the Fourier band |j|<=M and the span of b,v_plus,v_minus, so its orthogonal projection P commutes with reflection. On each finite-band parity space R1 is a valid exact formula. The original exponential moment constraints become

    integral_0^a g(t)[exp(sigma*t/2)+epsilon*exp(sigma*L/2)*exp(-sigma*t/2)]dt=0, sigma=+1,-1.  (R2)

The endpoint condition is g(0)=0. For arbitrary smooth half-functions supported away from 0,a, both exponential moments equal to zero are sufficient for R2 and smooth endpoint matching. Such functions need not lie in the finite Fourier band.

## Atomic Hankel positivity fails even after the moment constraints

Assume S is nonempty and select s_star in S, h=L-s_star in (0,2a). Choose distinct u,v in (0,a), u+v=h, avoiding the finitely many equations

    2u,2v in {L-s:s in S}, and |u-v| in S.               (R3)

This is possible because admissible u form a nonempty open interval and each forbidden equation excludes only finitely many points. Choose a sufficiently small interval U around u, and V=h-U around v, so U,V are disjoint and compactly contained in (0,a). All sum/difference sets stay away from every atom except the selected h in U+V. Also their individual difference widths are less than min S. This is a finite-cell choice, with no uniform width promised.

Take nonzero real chi in C_c^infinity(U), and psi=(d^2/dt^2-1/4)chi. Then psi is nonzero (a compactly supported solution of chi''=chi/4 would vanish identically), and integration by parts gives integral exp(±t/2)psi(t)dt=0. Put phi(t)=psi(h-t), supported in V. It obeys the same two zero moments. Normalize both to norm1; their disjoint supports make them orthonormal.

On span{psi,phi}, the exact quadratic-form matrices are

    T = [[0,0],[0,0]],   H = [[0,w_star],[w_star,0]].     (R4)

The diagonal H entries vanish by R3; the off-diagonal integral at h is integral psi(t)^2dt=1, with all other atoms excluded by support. Therefore T+epsilon H has Rayleigh values ±w_star on (psi±phi)/sqrt(2). The corresponding U_epsilon functions satisfy both full exponential constraints and vanish near both physical endpoints. Both reflection sectors have negative and positive directions in this unrestricted smooth space.

This disproves an unrestricted smooth reflection-positivity entrance for the actual nonzero finite composite measure, even with the stated moment constraints. It does NOT produce a negative direction in the original finite-band P, a cofinal lower bound on its magnitude, a counterexample to C5, or an RH conclusion. A nonzero finite trigonometric polynomial cannot have the compact support used here; projecting these witnesses requires a quantitative error budget not supplied by this construction. This is the exact stopping boundary of the attempt.

Concrete source control: for m=16,R=2, only n=9,15 have positive weights. Both log n>a=log4, so T=0. Taking h=log(16/9),u=h/3,v=2h/3 satisfies R3; the second Hankel atom log(16/15) is smaller than h/8. This checks that the construction is nonvacuous for the actual source, without asserting a finite-band witness.

## Source-verified alias return

Search dictionaries: (1) reflection-positive Hankel versus Toeplitz compression; (2) Schoenberg conditional positivity/exponential moments; (3) completely monotone Laplace mixtures. Three ask.sh queries returned INCOMPLETE because semantic-index freshness validation failed; no absence claim. The local shelf already contains periodic/Hankel identities in MOBIUS_PROJECTION_AUDIT_2026-10-06.md and PROSHKA_SIGNED_EVEN_TAIL_INLINE_2026-10-06.md. R1 alone is not counted as a new sign estimate.

Primary source fetched: Neeb–Olafsson, Reflection positivity for the circle group, arXiv:1411.2439v1, https://arxiv.org/pdf/1411.2439v1 . Local sources/neeb_olafsson_1411.2439v1.pdf, SHA2563ab8df7283ba95b46489f7b593f12ebd3cac26fd3e9117fa219936b57bab3114. Printed p.3, Definition2.1, Example2.3 and Theorem2.4. Exact short quote: “if and only if there exists” a positive operator-valued measure; formula(3) gives phi(t)=integral_0^infinity (exp(-t lambda)+exp(-(beta-t)lambda))dmu_plus(lambda).

Mapping: the source's period beta would be L, its half-domain (0,beta/2) would be (0,a), and its positive sum kernel would have to supply H in R1 (or an explicitly bounded comparison). The source assumes a weakly continuous periodic function and its positive Hankel kernel. Our H is an atomic distribution and fails that positivity on the moment-constrained smooth tests R4. No positive mixture representation or band-restricted replacement has been constructed. Source formula verified from the actual PDF; classification INAPPLICABLE as a direct supplier, not a theorem about our arithmetic matrix. It neither proves nor disproves finite-band C5.

## Decision

Do not seek C5 by applying generic reflection positivity to the unsmoothed atomic kernel. A useful next step must retain the actual finite-band test density or pay the entire smoothing/projection return before importing a positive-kernel theorem. No further representation-only claim is a supplier. Q9 is not sent; any next question must request an actual quantitative bound on the retained compressed signed form.

AUTOPSY: dropped=THEOREM_SHAPE; note=unrestricted atomic reflection positivity fails after both exponential moments; the low-band constraint is indispensable to the remaining source estimate.
