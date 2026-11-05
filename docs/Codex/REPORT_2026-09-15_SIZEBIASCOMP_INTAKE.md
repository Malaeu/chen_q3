# SIZEBIASCOMP intake: full-field convergence with the actual cutoff

STATUS: ACCEPT_FULL_FIELD_TRANSPORT_CONVERGENCE_AND_CUTOFF_RATE_OBSTRUCTION_ONLY.
Verifier: independently reviewed analytical proof; Lean verification not performed.
Review receipt SHA256: 7d47422e564ac355dc6940517b4abddd3298e0498d021b0cb61547d19519d411.
Request: REQ-2026-09-15-SIZEBIASCOMP, commit bea1abcd6baf5a171ceefa98b79548e528a2bf79.
Raw response: f6cb4ba3279e61de944b954bff524875fed97932, docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_SIZEBIASCOMP_2026-09-15.md.
Raw SHA256: 784e16445c64c1b480cfb0fdc5740182ad59253a775bfc8ab7dc0c44a654eafd (55408 bytes, 754 LF).
Honesty: CHALLENGER_NOT_RH; source_sign_progress=false; canonical_admission=false; PX_RH_CLAIM=NOT_MADE.

## What changed

The previous report bounded the scalar renewal remainder R_m. The response carries that coupling through the actual nonlinear conditional fields, using square roots of the physical densities. The conditional projection changes at every S_m. The terminal micro-minus-loss identity is exactly the original V, for every finite complex row on the original interval, with the original normalization and the cutoff t=1.

The decisive cancellation occurs before estimation:
v_x(t,s)=sqrt(mu/(2A^2))*a^(9/4)*t^(3/4)*[h(ats)/sqrt(h(ts))]*[h(at(1-s))/sqrt(h(t(1-s)))].
For a in (1/2,1), the complete small- and large-argument source estimates make these weighted fields and their t derivatives bounded on t>=1. The moving projection term Pi_t prime is retained. These are constants for each finite row; they are not a uniform positive lower bound in the coefficient norm.

## Boundary and budget

The literal cutoff has a jump. Its crossing probability is
p_m=P(S_m<1<=S_infinity)=d1*c_dagger*6^(-m)+epsilon_m,
|epsilon_m|<=20*pi^4/63*15^(-m), m>=1,
where d1=2*pi/5 and c_dagger>0 is determined by the full source.

The first innovation T1 is independent of (A_m,R_m), permitting a globally Lipschitz density estimate for both endpoints of the crossing interval. Tilting each of the first m H variables by 6h changes its mean to 2/5. Its limiting shifted series has mean 2*pi/9, which proves positivity of c_dagger on a fixed positive-density compact. This is a source argument, with no zero-location or target-sign assumption.

For each complete field, the mean-square approximation error equals
||U_c(1)||^2*d1*c_dagger*6^(-m)+O_c(15^(-m)).
The bulk and boundary error sums are finite, including mixed terms. For a single projected column the jump is nonzero, so an unchanged O(15^(-m)) rate for this literal cutoff field is false. In directions with both trace amplitudes zero, the O(15^(-m)) bound survives.

The response also proves absolute summability of the full quadratic telescopes, separately for micro, projection and loss. No unpaid infinite-norm premise remains in those specific convergence statements.

## What remains open

The terminal quadratic pairing is <U,J U>, with J swapping the two channels. J has both signs. Ordinary Hilbert-space norms, projection orthogonality and absolute summability do not prove the sign of this pairing.

The terminal identity can be written
V[c]=b_c*P(Tstar>=1)+integral_1^infinity P(Tstar>=t)*psi_c_prime(t) dt.
Nonnegativity of that entire expression is still the original unsolved sign problem. The new survival-weighted expression is not an independent sign supplier.

For a single negative shift, a positive-probability cutoff-crossing event has a strictly negative full pathwise telescope increment. This excludes nonnegative increments almost surely for this one construction. It does not exclude nonnegative expected full increments, compensation across levels, other constructions, or V>=0. No negative V witness is supplied.

## Acceptance and continuation

The independent review accepted precisely the scope above. Root has read the full raw response and checked the map, the first-innovation conditioning, tilted-tail constant, summed geometric constants, moving projection and the scope of the negative event.

This request is one bounded construction-and-repair package. It does not reset or increment the parked Barvinok fingerprint by its name, does not change canonical historical counters, and does not count reading/review/publication as further sign attempts. Its target-level outcome is NO_DERIVATION_OF_FINAL_SIGN, with substantive transport progress.

The next research decision must address the source-specific joint sign of the two channels under the complete integral. A further convergence estimate or orthogonality identity alone does not reopen a sign route. Preserve the new budget as an available theorem; do not send the same task again.

AUTOPSY: dropped=OBJECT_IDENTITY; note=The convergent complete field carries an indefinite two-channel pairing; its positive norm is not the original V.
