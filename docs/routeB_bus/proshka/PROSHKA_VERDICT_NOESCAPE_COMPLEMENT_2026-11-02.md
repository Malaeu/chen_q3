# STATUS: TRY_NOESCAPE_COMPLEMENT_LOWER_ENVELOPE
```yaml
OPERATIVE_CLASS: TRY_NOESCAPE_COMPLEMENT_LOWER_ENVELOPE
DATE: 2026-11-02
SOURCE_PIN: e9d36a8245a79a6b0436d52719828024f202ec61
CARRIER: LITERAL_CCM_EVEN_N=m_L=log_m
RESULT: EXACT_BLOCK_REDUCTION_ONLY
COMPLEMENT_BOUND_PROVED: false
RH_PROVED: false
VERIFIER: PAPER
SCOPE: COFINAL_FAMILY
PROGRESS_CLASS: REPRESENTATION_PROGRESS
PREDICTION_RESIDUAL_ONLY_SUFFICIENT: REFUTED
```

## Exact block theorem

Let A_m be the literal real-even CCM matrix, u_m=P_mh/Z_m, ||u_m||=1, Q_m=I-u_mu_m*. Define a_m=<u_m,A_mu_m>, b_m=Q_mA_mu_m and C_m=Q_mA_mQ_m on u_m-perp. In the orthogonal decomposition span(u_m) plus u_m-perp,

    A_m = [[a_m,b_m*],[b_m,C_m]].

For all unit x=alpha u_m+y, y perpendicular to u_m, the exact quadratic form is

    <A_m x,x> = a_m |alpha|²+2Re(conj(alpha)<b_m,y>)+<C_m y,y>.

The off-diagonal block has operator norm ||b_m||. Thus Weyl/min-max gives

    lambda_min(A_m) >= min(a_m,lambda_min(C_m))-||b_m||.

The pinned NOESCAPE supplies delta_m=||A_mu_m||=O_B(m^-B) for every fixed B, so |a_m|,||b_m||<=delta_m. Therefore

    C_{m_k} >= -epsilon_k I, epsilon_k -> 0
    => lambda_min(A_{m_k}) >= -max(epsilon_k,delta_{m_k})-delta_{m_k} -> 0 from below.

The inherited compact negative witness under not-RH yields lambda_min(A_m)<=-nu/2 for all sufficiently large m. Contradiction. Therefore the complementary bound on an unbounded original subsequence implies RH. Conversely RH implies nonnegativity of the full Weil form and C_m>=0. This is an RH-equivalent RE-REPRESENTATION, NOT a proof of the missing arithmetic sign.

## Exact source target

For every unit real-even f in the literal V_m with <f,P_mh>=0, prove k[f]>=-epsilon_m on an unbounded subsequence with epsilon_m->0. All prime powers, archimedean integral and poles remain. This is precisely the C_m bound. No eigenvalue division, coordinatewise X/F, simple ground state or gap is required.

## Adversarial falsifier

Take A_m=diag(0,-1), u=e1, X=0. Then ||A_mu||=0 while C_m=[-1]. This kills residual-plus-exterior-smallness promotion at ABSTRACT scope, not the literal CCM bound.

## Why the source sign remains

A fixed negative compact test under not-RH can be orthogonalized against the global theta-radical h without changing its Weil energy. Thus the negative witness can reside in the h-orthogonal complement. The complementary inequality requires a genuinely signed arithmetic comparison; the block identity does not create it.

## Two candidate representations

1. Schur/inertia: construct a Householder basis of u_m-perp and certify the minimum eigenvalue of C_m on a finite cell (kill power 5/5; cost low). This is a DISCRIMINATOR for a false spectral inference, not cofinal proof.
2. Signed source-constrained Rayleigh: minimize the complete prime-power Weil form under ||f||=1 and <f,P_mh>=0, retaining pole and continuum (kill power 4/5; cost medium). The first genuine target is a cofinal lower envelope with epsilon_m->0.

## Consumer, predictions, closeout

DOWNSTREAM_CONSUMER: RH through the pinned finite negative-witness theorem.
ACTUAL_CONSUMER_REQUIREMENT: lambda_min(A_m)>=-o(1) on an unbounded subsequence.
ORIGINAL_REQUESTED_OBJECT: F-only bound plus coordinatewise X/F.
ORIGINAL_OBJECT_IS: NOT_NECESSARY for this alternative consumer.
KNOWN_WEAKER_INTERFACE: C_m>=-o(1) plus delta_m->0.
FAILURE_TYPE: NO_DERIVATION of the source lower bound.
EPISTEMIC_STATUS: RESEARCH_DEBT.
NOVELTY_AXIS: remove small eigenvalue denominators, not prove a new sign.
REOPEN_TRIGGER: source-signed estimate on the h-orthogonal complement.
REGISTERED_PREDICTION: residual and exterior smallness alone do not control C_m; CONFIRMED by exact abstract counterexample.
NEXT_DECISIVE_TEST: finite full-spectrum Householder C_m audit, then a signed arithmetic estimate or stop this representation.
RH_CLAIM: NOT_MADE.
