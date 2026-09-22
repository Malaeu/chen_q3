# Goal 058 — Fokas paired-window semantic-search brief

Date: 2026-09-22. Status: SOURCE_PINNED_EXPLORATORY; production edge UNBOUND.
Owner requested incorporation, semantic-search readiness, and continued work
with Proshka toward a checked proof. The native app goal is ACTIVE; this brief
is a next-move specification within Goal 058, not a replacement proof goal.

## Obstruction in plain language

The exact analytic source has an explicit finite-window Mellin formula, but
its coefficients are not yet controlled strongly enough to transfer the
spectral floor and track the same finite ground family toward Ξ. Rewriting
its window error as two linked terms may expose a cancellation. Their sum
must be handled before separate absolute-value estimates lose that structure.

## Source pin and formula

Base: 63c028ac17995e9abb57a6c4a95cefc92ec1c63f.
Generator commit: 70da2617592c5dc5d14215f23dc487f2004f58b7.
Generator blob: 51c54f58d8d091b70b545e09094157f0384c94b9.
[Generator G4–G7](../routeB_bus/proshka/ccm_exact_source_generator_2026-09-20/VERDICT.md).
[Reviewed formula, proof, links and retrieval limits](../../q3.lean.aristotle/docs/reviewed_notes/2026_09_22_fokas_paired_window_review.md).

For integer m≥2, n∈ℤ, L=log m, s_n=1/2−2πin/L and the exact selected
Ferrers mode0/mode4 source H_m at c=2πm:

R_m(s;H_m)=ζ(s,m+1)∫_0^1 H_m(v)v^{s−1}dv
          +Σ_{k=1}^m k^{−s}∫_0^{k/m}H_m(v)v^{s−1}dv.

α_mn=m^{1/4}/√L [ζ(s_n)ℋ_m(s_n)−R_m(s_n;H_m)].
q_mN=α/Z_mN, Z²=Σ_{|n|≤N}|α|², Z>0 required.
All identities concern the original source, not a rounded cache or arbitrary
finite polynomial. Off the discrete s_n lattice retain m^{s−1/4}.

## Existing proof and negative control

PAPER: change of variable plus finite sum gives the identity in the reviewed
note. Source coefficient identity does not supply positivity or ground tracking.

Negative control outside the target pair: H=P₂, ∫H=0 but ℋ(1/2)=−2/5.
Thus a proposed mechanism using only zero mass must fail. Additional equations
of the actual modes may still provide cancellation; those must be used explicitly.

## Own search rewrites — UNVERIFIED mechanisms

1. Treat R_m as one functional of H_m, pairing a Hurwitz tail with a dilation
   window. Search Mellin convolution / Abel–Plana / incomplete Mellin identities.
2. Apply the prolate Sturm–Liouville equation under the weighted integrals and
   retain the Lagrange boundary concomitant at 0, k/m and 1. Search Green
   identity / boundary form / spectral projector defect. This is a search hint,
   not a proved cancellation or a justified endpoint integration by parts.

## Output and stopping condition

First exact shelf keys: `Ferrers Mellin`, `Hurwitz zeta`, `finite Dirichlet`,
`prolate boundary`, `paired window`.
Then three dictionaries in the reviewed note, with source/hypothesis mapping.
Return a worked identity and an explicit surviving boundary term or uniform
bound, including all m,n domains and normalization dependencies. Stop this
bounded attempt once that discriminator is resolved; preserve the obstruction
for the semantic return before selecting another mechanism.

One independent checker reviews the exact candidate. A follow-up to the same
living Proshka chat must use a byte-verified source-pinned .txt request under
the registered transport. This intake is not itself a new sent request.

Long-range consumer: FiniteGroundTransformToCCMTrialLocallyUniform, with ground
selection, cofinal schedule, residual/separation, projection tail and continuum
CCM→Ξ mapping all explicit. No claim that only one unsupplied premise remains.
CHALLENGER_NOT_RH. PX_RH_CLAIM: NOT_MADE.
