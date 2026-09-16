# Poincare comparison closed; complete signed form still open

STATUS: INDEPENDENTLY_REVIEWED_PAPER_SCOPED_RESULT.
No canonical admission, Lean proof, negative original-V witness or RH claim.

## Exact received artifact

Request REQ-2026-09-16-POINCARECOMP was sent once and has now been answered.
Response commit: `2dbd8191cfa515121c3c24c44ca61c2e5bc46acc`.
Path: `docs/routeB_bus/proshka/PROSHKA_RESPONSE_GOAL058_POINCARECOMP_2026-09-16.md`.
Git blob: `2f2b28ac8f73033e7671d6c5467fcff09bb98fc6`.
SHA256: `1920733be233ad33403c1c482b3db6c0d253db091ca646415fe84fd5b3a0bc6d`.
49478 bytes, 518 LF, no CR, final LF. Parent read all 518 lines.
The independent checker read the same immutable artifact in full; its report
and exact digest are preserved in the accompanying certificate.

## Accepted theorem and its exact limit

For every kappa>0 and every nonempty open interval J contained in (-infinity,0),
there is a finite complex row with nodes in J for which

    M[c] - kappa D_X[c] < 0.

In particular the sufficient lower envelope L_pi=M-(D_X+sqrt(D_G D_B))/(2pi^2)
has a negative finite row on the original interval I. Thus improving the
fixed positive constant in this absolute derivative comparison cannot prove
the required all-row sign. The valid conditional Poincare inequality and
L<=B_pi are unaffected. A negative lower bound is not a negative value of V.

This agrees with the independently published parent obstruction at
345dfea4365498cfdff460e78620f4d717e49147. The two parallel derivations concern
one proposed comparison, not two failed full-sign attempts.

## Parent reproduction of the proof

1. On Omega={Re z<0, |Im z|<pi/6}, a=e^(2z) satisfies Re a>0 and
   Re(1/a)>1/2. The full small-u modular series gives exponential decay for
   h(au)/sqrt(h(u)) and [a h'(au)-(h'/h)(u)h(au)]/sqrt(h(u)). The latter
   expression never divides by complex h(au). The large-u growth allowed
   when Re a<1/2 is canceled by the retained sqrt(r(t)) physical factor.
   The resulting half-density bounds are t^(7/4)e^(-pi delta t) and
   t^(11/4)e^(-pi delta t), locally uniformly in the two complex arguments.
   This establishes one joint holomorphic domain for the actual quadratic
   kernels M and D_X, not for the nonquadratic L_pi.
2. U=ats, W=at(1-s), T=U+W gives dt ds=dU dW/(aT). In M the signed
   coefficient log(t)+2x becomes exactly log(T). The complete transformed
   measure has the integrable majorant (15), so the M diagonal stays bounded
   and converges. On a fixed positive-mass rectangle with T>1, the limiting
   s-score is nonzero and X>=-x; hence D_X>=c_D(-x), c_D>0. No negative
   contribution was discarded from this nonnegative derivative energy.
3. The already accepted all-finite analytic positivity propagation lemma
   applies to K_kappa=M-kappa D_X. Were it PSD on every row in J, it would
   remain PSD along the connected negative real axis, contradicting the
   distant negative diagonal. This gives an actual finite-row existence
   result in J; it supplies neither a numerical rank nor a negative V row.

## Exact reciprocal transport also accepted

Writing w(t)=t^(3/2)r(t)^2/(2A^2), reciprocity gives

    j_t=p_(1/t)/p_t=g_(-log t),  E_t j_t=1,
    j_t g_x(1/t)=g_(x-log t)(t),
    F_x(1/t)=F_(-x)(t),  w(1/t)/t^2=w(t).

These identities have the correct -9/2 likelihood exponent and all Jacobians.
The conditional projection changes: j_t is nonconstant for t!=1, and the
rank-one projection discrepancy (27) is strictly positive. The primitive
potential changes by 2 alpha beta+beta^2-beta'; this is retained, not dropped.

Parent directly substituted t=1/tau into the truncated full expression:

    V_H(x,y)=integral_(1/H)^1 w(tau)(x+y-log tau)
                         F_(-x)(tau)F_(-y)(tau) d tau.

The finite cutoff becomes [1/H,1]. With the transformed conditional measure,
the covariance identity has factor 2 and cancels exactly the same covariance
part of M. Conditional endpoint products vanish by the exponential source
bounds; the physical t=1 trace remains w(1)(x+y)F_x(1)F_y(1). No integration
by parts in t occurred, so that trace is not an omitted additive term.
The H->infinity limit follows from the separately established absolute
integrability of the original signed pieces.

After this change of space the remaining expression is exactly

    V[c]=-2 Re integral_0^1 w(tau) conjugate(m^r)
                           [X m^r+b^r] d tau,
    m^r=sum c_i F_(-x_i), b^r=sum c_i(-x_i)F_(-x_i).

It is the original unknown sign in new coordinates. For two distinct nodes
the pointwise mean-channel determinant equals
-(x_1-x_2)^2 F_(x_1)^2 F_(x_2)^2. Thus neither positivity of a conditional
potential nor positivity at each integration point is the missing mechanism.
This determinant is not a negative integrated V witness.

## What is now excluded and what remains useful

Do not reopen a fixed positive absolute derivative budget, an unchanged
conditional projection under inversion, or positivity from an isometry alone.
The full source product was used to control the complex domain and score;
no property special to primes was used in this new proof.

The earlier reciprocal likelihood covariance diagnostic at
98d00ddda0777c4d19d4de9b83910e8477011ba5 is compatible with this response:
reciprocal means agree while their conditional fluctuations do not admit the
specified forward contraction. That diagnostic and a generic reverse Markov
contraction do not supply the mixed signed comparison.

Next action is a bounded semantic return on the mixed pair, before another
proof request. A useful candidate must supply a source-checkable sufficient
condition, distinguish the known negative control, and account for the whole
integrated mean channel. Merely restating its positivity fails this test.
The source-specific renewal block test already recorded in
PLAN_2026-09-16_FIVE_FULL_V_CANDIDATES remains untried, not a proved supplier.

The current request is complete. The native goal of the complete V sign remains
active. This is one scoped exclusion and one exact reformulation; the sign of
the original V has not been proved or disproved.
