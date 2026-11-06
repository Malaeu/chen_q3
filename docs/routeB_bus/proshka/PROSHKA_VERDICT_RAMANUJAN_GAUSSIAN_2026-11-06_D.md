# STATUS: TRY_RAMANUJAN_GAUSSIAN_EXACT_HEAD_D

```yaml
OPERATIVE_CLASS: TRY_RAMANUJAN_GAUSSIAN_EXACT_HEAD_D
RH_PROVED: false
PX_RH_CLAIM: NOT_MADE
SPEC_FREEZE_COMMIT: 1f307ff7d9590f8096c0c0624145927a6646b156
PROVED_STEPS:
  - {id: EXACT_FINITE_RAMANUJAN_EXPANSION_FOR_TRUNCATED_LAMBDA, scope: FINITE_CELL, verifier: PAPER}
  - {id: EXACT_BALANCED_GREEN_HEAD_IN_RAMANUJAN_COORDINATES, scope: FINITE_CELL, verifier: PAPER}
  - {id: FINITE_GAUSSIAN_MELLIN_TRANSFORM, scope: FINITE_CELL, verifier: PAPER}
RH_GAP: COFINAL_SIGNED_HEAD_TAIL_CANCELLATION_IN_THE_TRUE_MOBIUS_GREEN_FORM
PROGRESS_CLASS: REPRESENTATION_PROGRESS
RH_SIGN_PROGRESS: NONE
KILLS: []
CLOSES: [FINITE_RAMANUJAN_HEAD_REPRESENTATION]
OPENS: [SOURCE_SPECIFIC_COFINAL_SIGNED_BOUND]
COGNITIVE_OPERATOR: EXACT_RAMANUJAN_DIVISOR_FOURIER_RETURN
ROUTE_SCORE: 2
```

## Verdict

[COFINAL_FAMILY | CONDITIONAL] **RH is not proved.** The original Ramanujan modular identity in the brief is explicitly labeled false. Its corrected zero series cannot be set equal to zero; no new zero-free information follows merely from the exact Gaussian factor. In particular the displayed corrected formula is stated with a simple-zero restriction. No assertion of simplicity, convergence after rearrangement, or zero-free strip is imported. The alpha/beta Gaussian scaling has not been independently audited against a primary source; the frozen prediction P1 remains **UNRESOLVED**, not a hit. The numerical 10^-5 agreement is DIAG and is not an error bound.

## Exact finite additive-multiplicative return

[FINITE_CELL | PAPER] For each integer N>=2 define the truncated divisor convolution

```
Lambda_[N](l) = -sum_(d|l, d<=N) mu(d) log d.
c_q(l) = sum_(1<=a<=q, gcd(a,q)=1) exp(2*pi*i*a*l/q).
h_N(q) = -(1/q) sum_(d<=N, q|d) mu(d) log d.
```

Then **for every positive integer l**,

```
Lambda_[N](l) = sum_(q<=N) h_N(q)c_q(l).            (1)
```

Proof: group all d in the right-hand side, using the elementary identity
`sum_(q|d)c_q(l)=d*1_(d|l)`. This identity follows by partitioning all d-th roots of unity by their exact order. Consequently the coefficient of each `-mu(d)log d` is exactly `1_(d|l)`. No limiting interchange, conjectural Ramanujan expansion, or unproved convergence is involved. For 1<=l<=N, `Lambda_[N](l)=Lambda(l)`, including every proper prime power.

[FINITE_CELL | PAPER] Let L=log N, s_N the original centered Möbius scalar, and define the actual current on 1<=l<=N as in 2cb30501:

```
d_(N,l) = (s_N - Lambda(l)/L)/l.
v_N(l) = (L*s_N - sum_(q<=N) h_N(q)c_q(l))/l.
```

Then `d_(N,l)=v_N(l)/L` exactly. Hence the **entire finite head block** of the balanced Green form of a337b335 is the explicit quadratic form

```
Z_head(N) = (1/L^2) sum_(1<=l,k<=N)
  v_N(l) v_N(k) / max(l,k)
  * (1-|log((l+1)/(k+1))|/log(2))_+.          (2)
```

This is a genuine finite Ramanujan-coordinate representation of the *original* head, with all cross terms retained. It is positive semidefinite because the balanced Green kernel is PSD. However, (2) alone supplies **no uniform upper bound**. The actual Z_N also contains the full tail l>N and the signed head-tail cross term; replacing that tail by zero would change the source. Thus neither (1) nor (2) establishes the cofinal boundedness required in a337b335 (20).

### Finite Gaussian Mellin check

[FINITE_CELL | PAPER] For x>0, N finite, and Re s>0,

```
F_N(x)=sum_(n<=N) mu(n)/n * exp(-x/n^2)
int_0^infinity x^(s-1) F_N(x) dx
 = Gamma(s) sum_(n<=N) mu(n)n^(2s-1).         (3)
```

Proof: integrate each of the finitely many terms using x=n²u. The infinite Dirichlet-series identity `sum mu(n)n^(2s-1)=1/zeta(1-2s)` is **absolutely valid only when Re s<0**, disjoint from the elementary Mellin-integral domain Re s>0. Thus directly sending N to infinity in (3) and identifying the answer with `Gamma(s)/zeta(1-2s)` requires an independent continuation/limit argument. It cannot be used as an unqualified positivity or RH proof. This is a precise domain obstruction for the naive finite-to-global shortcut, not a claim that the classical corrected Ramanujan formula is invalid.

## Strongest attack and missing bound

[ABSTRACT | PAPER] An exact finite Ramanujan basis expansion is a change of coordinates. It preserves the value of the quadratic form but does not impose a new inequality on its actual signed coefficients. A positive Gram matrix can have arbitrarily large value on a prescribed vector (e.g. the one-dimensional Gram [1] evaluated at [t]); positivity is a lower-sign statement, not the required upper estimate. The proposed Gaussian modular symmetry is *not* an exact symmetry of the unmodified Möbius sum; the zero correction is precisely what cannot be discarded.

[COFINAL_FAMILY | CONDITIONAL] The minimal unproved assertion remains

```
exists C<infinity:
 {N in S: Z_(N,N^2)<=C} is unbounded,            (4)
```

where Z is the full signed source-matched balanced form from a337b335, not just (2). If (4) were proved, the already pinned receiver `E_N<=14 Z_N+9/log²N`, pointwise zero residual, and the Mellin lower bound at a hypothetical right zero would imply RH. **No independent estimate of (4) has been obtained.**

### Predictions and next test

P1 UNRESOLVED: primary-source scaling not independently verified. P2 HIT in the limited sense that the *brief itself* says the original symmetry is false; no new falsifier derived. P3 HIT: exact (1) and (2), no upper bound. P4 HIT: RH remains open. These scores do not constitute numerical experiments.

Candidate A: exploit joint `c_q(l)c_r(k)` cancellation *with the true h_N(q)* and full head-tail boundary; kill-power high if a strict O(1) bound emerges, analytic cost very high. Candidate B: Gaussian-Mellin contour transfer with an explicit nonzero zero-residue correction and controlled infinite truncation; kill-power high, cost very high. **DISCRIMINATOR:** a one-sided bound that holds for the actual ordinary-integer source but fails after inserting an off-line quartet; near-zero numerics do not suffice.

K8A: DOWNSTREAM_CONSUMER=RH via NB capture; ACTUAL_CONSUMER_REQUIREMENT=bounded pointwise-zero subsequence; ORIGINAL_REQUESTED_OBJECT=RH proof; ORIGINAL_OBJECT_IS=UNKNOWN as a requirement for this particular Ramanujan method; KNOWN_WEAKER_INTERFACES=optimal NB capture or literal Weil floor; FAILURE_TYPE=NO_DERIVATION; EPISTEMIC_STATUS=RESEARCH_DEBT; NOVELTY_AXIS=finite exact Ramanujan head return; REOPEN_TRIGGER=source-specific signed bound for full Z or independently controlled Gaussian contour remainder.

```yaml
iteration:
  target: TRUE_SOURCE_SIGNED_BALANCED_GREEN_BOUND
  status: OPEN
  cognitive_operator_used: EXACT_RAMANUJAN_DIVISOR_FOURIER_RETURN
  new_gap_name: COFINAL_HEAD_TAIL_SIGNED_CANCELLATION
  invariant_learned: FINITE_RAMANUJAN_EXPANSION_PRESERVES_ALL_CROSS_TERMS
  forbidden_future_move: TREAT_FALSE_ORIGINAL_MODULAR_IDENTITY_AS_ZERO_DEFECT
  next_decisive_test: EXPAND_FULL_HEAD_TAIL_CROSS_TERM_IN_C_Q_WITH_EXACT_BOUNDARY
  route_score: 2
```

Verification: PAPER algebraic identities only; no Lean, Arb, or independent analytic audit. Freeze unchanged. Source pins: prime-only 115714b7 blob 9feeb057; balanced Green a337b335 blob 692b1082; literature sweep 7d23fbe9 blob 0ae6bb1a. No RH claim.
