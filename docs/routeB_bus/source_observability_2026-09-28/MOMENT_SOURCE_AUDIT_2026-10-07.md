# Rollover Q6 — actual source moment audit

Source: PROSHKA_MOMENT_SOURCE_INLINE_2026-10-07.md and full Q06 preview.
Chat 6ac58a1c-1568-83ed-95d0-857526e2b6cb; answer
31648e32-ad26-43ca-8ab7-b5a5326109f8. Bounded independent checks below.

## Source constants and family estimate

growth_symbol_attempt checked §§1,4 against accepted Q3–Q5 source identities.
E_a=(A_arch-diag(a))-cA I+2H_pole lies between -(20+cA)I and
(28-cA)I. The fixed epsilon=beta+cA+28+tau therefore gives
2cA I<=V<= (beta+2tau+2cA+48)I, hence T>=sigma I with sigma=2cA.
Applying Cauchy–Schwarz to P-sigma I gives M²<=(p-sigma*N)(c-sigma*M).
When b!=0 both factors are strictly positive, and e>=sigma*c>0.
For r=epsilon+2Bsrc, q>=(epsilon+Bsrc)N and M<=Bsrc²N imply
F>=0 on all actual exceptional vectors, including b=0 separately.
This uses exactly the old Bsrc=L+8+4R_m estimate: exponent1/2-o(1),
no improvement toward all eta and no lower bound on the required shift.
No substantive correction was found.

## Projected arithmetic pass

causal_algebra_audit checked §2 and the final displacement identity.
The seven signed operators sum to H0; all cross words are retained.
D2,D3,D4 are exactly the products with respectively one, two and three
intermediate Pi factors. Q=L*(LL*)^dagger L handles dependent rows;
no inverse conditioning is asserted. Shift cancellation in Gamma is exact.
The squared minors use COORDINATES of b,w in an orthonormal carrier basis,
not source-word indices b_i,w_ki. Their inner product is real, justifying
d3² rather than a missing complex modulus. Ambient Fourier coordinates
also suffice since b,w lie in the regular subspace.
The displacement and resolvent signs agree with H_jk=-(h_j-h_k)/pi(j-k).
Actual negative rows are paired Cauchy rows with both finite endpoint
numerators and sqrt(r_w/2) preserved; there are no jet rows.

## Residual and perturbation pass

answer10_pair_audit checked §3 and §5's moment error formulas, assuming the
source interval. Expanding optimized residuals gives e*Gamma/Dg² and
M*Gamma/Ag². The monotone weights theta/[g(g+theta)] and1/(g+theta)
give the stated lower/upper directions. For the improved certificate,
Dg-sigma*Ag=g(c-sigma*M)+(e-sigma*c)>0 and the exact gain formula holds.
The zero-covariance case makes both residuals vanish; no approximate zero
is promoted to equality. Partial fractions agree with the own source check.
Fixed actual projectors give the two vector perturbation bounds and all
four scalar bounds. Approximate-projector errors are NOT included.

## Root full-preview return check

Root read the full Q06 preview. The additional division-free bound (31)
follows by writing F=A*D+c², A=gq-M, D=gc+e. If errors in A,D,c are
E_A,E_D,E_c, then the product difference is bounded by
|Atilde|E_D+|Dtilde|E_A+E_AE_D+2|ctilde|E_c+E_c².
Nonnegative lower endpoint certifies only the stated actual vector; a
negative upper endpoint refutes only the moment certificate there.
Neither supplies whole-space quantifiers without an additional argument.
The diagonal a(omega) series tail is bounded by the decreasing integral
of2omega²(2x+1/2)^-3 from J to infinity, giving omega²/[2(2J+1/2)²].
The full return has no Delta10 approximation when all its signed operators
are retained in H0. Paying them separately restores exactly the former
(Delta10+4epsilon4)||v||||J_rv|| bracket. Moment amplification is not free.
The per-vector ||J_rv||²<=N+M/(g+sigma)² follows from orthogonality and
the actual inverse bound; it is not a uniform operator estimate.

## Next own attempt and status

SCHUR_MOMENT_SOURCE_CHECK gives the weaker PSD completion check and exact
zero-node mass, independently checked with the nonnegative-mass wording.
DISPLACEMENT_SOURCE_OWN, independently checked by causal_algebra_audit,
computes two H actions on the conjugated actual
rows and retains the projector feedback. Its remaining anchor correlations
have no proved saving; this setup is not claimed as a new bound.
Q6's moment-envelope approach is STALLED at the old1/2-o(1) exponent,
not refuted. Select exactly one bounded displacement/source-cancellation
test on the same projected second/third/fourth moments, with no higher
moments or fabricated zero. SP/G1/G3/RH and actual Schur sign remain OPEN.

Q7 sent once in the same living chat. UI readback showed the full question,
Pro, empty composer, Stoppen and connection-recovery status. Do not resend.
