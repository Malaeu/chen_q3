# ARSENAL_CARDS_v1 — proof-mechanism card-file (K9 materialization)
# Source corpus: "How the Ideas Came Together" (12 reasoning walkthroughs, 2026).
# Scan rule (K4): match BY SIGNATURE, not by field. Every import passes the card's
# TRANSFER invariants (K3) and K7 (unconditional input) before use.
# Card status lifecycle: UNTESTED -> USED(goal-NNN) -> KILLED(autopsy line).
# Format v1.1 (2026-08-23, verdict ebd1d70f): cards MAY carry BRIDGE_KIND
#   (cross-domain transfer cards only), INSIGHT_STATE (closed enum of
#   INSIGHT_STATE_V1), FALSIFIER (exact plant / instantiated DUAL),
#   TOY_VALIDATION (NOT_RUN|PASS|FAIL - never proof authority),
#   DEPENDENCY_FOOTPRINT (CLOSES/OPENS by catalog names). Legacy cards
#   C01-C12 stay valid; fields are added on the next USED/KILLED touch;
#   mass retrofit is forbidden (process bloat).
# Aliases only; no new frozen-glossary terms (ROUTE_B_STATE glossary untouched).

## C01 SIGN-MASS-LOCALIZATION                                    [src: Ch1 sphere packing]
MECHANISM: when a global norm/positivity inequality sticks at the wrong constant,
  stop improving constants — the global functional has forgotten WHERE the
  negative mass lives. Prove a local mass-exclusion inequality on the explicit
  region instead (Mellin/strip maximum principle in the source; any
  location-keeping transform qualifies).
SIGNATURE: LP or positivity bound stuck; the needed global inequality is provably
  unavailable; the obstruction has a spatial/spectral "where".
ROUTE_B: 𝒟_m sign on a ∈ [4/3, √m] (JUMP-TARGET A); edge-sliver negative-mass
  location; master split a₁ = HUMP + FAR is already a localization move.
TRANSFER: must carry support/cone membership of the sign; dropping location
  reverts to the failed global route (FATAL per K3).
DUAL (Прошка): "does this bound track WHERE the mass sits, or only how much?"
STATUS: UNTESTED

## C02 IDEAL-PLUS-REMOTE-COMPENSATOR                             [src: Ch1.7]
MECHANISM: the extremal/ideal profile is inadmissible (divergent, non-Schwartz).
  Truncate + taper it, then add a SMALL positive component on a remote INTERVAL
  (interval, not point — interval averaging kills resonant frequencies) that
  restores global damping while leaving the limiting constant unchanged.
SIGNATURE: optimal weight/test function fails admissibility at 0 or ∞; naive
  truncation loses the constant.
ROUTE_B: Weil-positive test functions with prescribed decay; Müntz v3
  pole-subtracted shell (pole subtraction = compensator instance already in use).
TRANSFER: compensator must vanish at the target saddle/constant; verify the
  interval-averaging inequality survives the new kernel.
DUAL: "does the repair term shift the constant it claims to preserve?"
STATUS: UNTESTED

## C03 MOVING-REPRESENTATION                                     [src: Ch2 codes]
MECHANISM: a certificate built on one fixed distinguished vector per point
  silently discards exponential multiplicity. Replace the fixed line by a
  subspace MOVING with the point; equivariance makes the final kernel scalar
  /two-point again, so the certificate class does not change — only its rank.
SIGNATURE: LP/certificate uses one canonical vector; a stabilizer group acts;
  suspicion of wasted degrees of freedom.
ROUTE_B: per-cell certificates (033 bands, fixed r-profiles) vs one object
  parametric in m; test-function family moving with λ_m instead of frozen.
TRANSFER: equivariance must be exact (group action on both factors); the
  recovered kernel must be radial/two-point for the same consumer.
DUAL: "which multiplicity does the fixed choice discard, and is it exponential?"
STATUS: UNTESTED

## C04 SAME-COORDINATES-TWO-LAWS                                 [src: Ch4 Connes]
MECHANISM: two objects "equal" after a forgetful functor can differ by a cocycle
  invisible to the coarse structure (measure) and visible to the fine one
  (dual/torsion). Name the functor explicitly; the invariant lives one
  category finer than the equivalence used.
SIGNATURE: an equivalence/reformulation looks lossless; need either to separate
  two objects or to explain why a distinction is invisible to a detector.
ROUTE_B: conservation-of-hardness audits — every RH reformulation must declare
  which structure it forgets; α-Gate vs ZEO seeing the same Ξ through
  different functors.
TRANSFER: the forgotten structure must be named as data (cocycle/torsion/order),
  not gestured at.
DUAL: "equal in WHICH category? what does the equivalence forget?"
STATUS: UNTESTED

## C05 DISJOINT-SUM-NOT-PRODUCT                                  [src: Ch5 permanent]
MECHANISM: products destroy critical/positivity structure (∇(fg)=0 on common
  zeros); sums in DISJOINT variables add codimensions and budgets. Cancellation
  schemes (root-of-unity) can embed many disjoint blocks into one object with
  all cross-terms cancelling ALGEBRAICALLY (verified, not assumed).
SIGNATURE: need to amplify a per-block property to global scale; temptation to
  multiply per-block certificates.
ROUTE_B: per-band ε_r ledgers combine by SUM (combined-ledger discipline,
  residual 7e-37 validation); spectral-ladder block decomposition.
TRANSFER: disjointness of variables/supports must be literal; every surviving
  block coefficient proven nonzero; cross-cancellation exact-arithmetic.
DUAL: "do the blocks really live in disjoint variables, or only disjoint names?"
STATUS: UNTESTED

## C06 TRANSCENDENCE-NOT-LINEAR-COUNT                            [src: Ch6]
MECHANISM: count independent parameters by transcendence degree over the
  coefficient field, never by linear independence or by superficially distinct
  expressions (z and z² are different, trdeg = 1). Survive division/cancellation
  via the projection identity K(Y) ∩ R[Y] = K[Y].
SIGNATURE: degrees-of-freedom lower bound where intermediates can cancel or
  divide; "many different coefficients" claimed as "many parameters".
ROUTE_B: P1 rank-vs-dimension audits; counting genuinely independent constraints
  among h-package constants before declaring a slot "the missing estimate".
TRANSFER: pass to the generated FIELD before counting; charges attach to the
  marked skeleton, not to sibling complexity.
DUAL: "is this a transcendence count or a list of different-looking formulas?"
STATUS: UNTESTED

## C07 PROBABILITY-WEIGHTED-ESTIMATE                             [src: Ch7 quantum]
MECHANISM: prove the estimate WITH the conditioning weight attached
  (p·D(conditional) ≤ D(global) + h(p)) so the rare branch pays for itself:
  cost log(1/p), never 1/p. Scale-resolved purification (resolvent family)
  instead of one coherent square root that accumulates all eigenvalue scales.
SIGNATURE: conditioning on a rare event destroys a bound by 1/p; smallest
  eigenvalue/scale enters a denominator.
ROUTE_B: exceptional-set budgets (teeth, measure-zero ledgers); any conditioned
  estimate inside the spectral ladder; dps>15 alarms (scale accumulation).
TRANSFER: the branch weight must cancel the exact denominator BEFORE averaging;
  check no smallest-scale constant survives in the final bound.
DUAL: "where does 1/p (or 1/λ_min) hide in this conditional estimate?"
STATUS: UNTESTED

## C08 PARITY-AS-SELECTOR                                        [src: Ch8 GapCVP]
MECHANISM: parity/char-2 turns cancellation from enemy into selection: an odd
  fiber forces a nonempty witness set; valuations synchronize local data into
  one global consistent object (ultrametric: two disagreeing local bits force
  v(1) ≥ 1, impossible).
SIGNATURE: cancellation threatens an encoding; need to force existence of ONE
  consistent global witness from local parities.
ROUTE_B: sign bookkeeping in alternating ledgers; exact-rational symbolic
  checkers (034-style) where parity arguments demand exact arithmetic.
TRANSFER: parity claims require exact arithmetic — float64 FORBIDDEN here;
  all local valuations extended in ONE common field.
DUAL: "is the parity computed exactly, and in one common valuation?"
STATUS: UNTESTED

## C09 PRECOMMIT-AND-STRENGTHEN-INVARIANT                        [src: Ch10 Ramsey]
MECHANISM: (a) fix the auxiliary object BEFORE cases are enumerated — one union
  bound then pays for ALL future pairs simultaneously; an object chosen after
  seeing the case proves a weaker theorem. (b) strengthen the induction
  invariant past what the consumer needs (χ ≤ j+1, not mere triangle-freeness)
  so the recursion closes without new resources.
SIGNATURE: recursive construction where reuse across stages fails; witness
  chosen post hoc; induction hypothesis too weak to propagate.
ROUTE_B: r=195 used ONLY as pre-committed regression profile, never intrinsic
  (034 FORBIDDEN list already honors this card); Lean induction strengthening;
  K6 OBJECT PRE-COMMIT is this card promoted to law.
TRANSFER: pre-commit recorded in the goal file (timestamped); the strengthened
  invariant must be checked to actually propagate one full stage.
DUAL: "was this object fixed before or after the cases were seen?"
STATUS: UNTESTED

## C10 FUNCTIONAL-NOT-SURROGATE                                  [src: Ch9 Ehrhart + Ch2]
MECHANISM: pointwise/ray convexity of a surrogate (A_k) does NOT transfer to the
  required scalar functional (P_k): Jensen gives P ≤ A with strict gap. Scalar
  convexity/positivity must come from a genuine positivity theorem applied to
  the RIGHT object — in the source, a rank-ONE Bergman kernel where kernel =
  inverse partition, so Berndtsson positivity applies directly. Companion law
  (Ch2): positivity is a CONSTRUCTED Gram remainder ‖Ψ*Ψ‖², never a presumed
  sign of a formal recurrence.
SIGNATURE: temptation to integrate pointwise convexity into scalar convexity;
  any PSD claim proved by "the coefficients look positive"; variance term
  uncontrolled in the second derivative.
ROUTE_B: roof H1∧H2∧H3∧H4 positivity — every PSD input built as g = h⋆h̃
  ("pair, don't multiply"); ⟨ĝ, ν̂_edge⟩ via Parseval avoiding the BCK sign
  tax; any convexity claim in the ladder must name its positivity theorem
  and its rank-one (or Gram) object.
TRANSFER: identify the exact scalar functional the consumer needs; verify the
  positivity theorem's hypotheses (joint psh / PSD by construction) on THAT
  object, not on a ray surrogate.
DUAL: "is convexity proved for P or for its Jensen-majorant A? where is the
  Gram square?"
STATUS: UNTESTED

## C11 ADMISSIBLE-QUOTIENTS                                      [src: Ch11]
MECHANISM: forbidding/forcing only the literal disjoint template fails — copies
  in the wild may overlap. Close the pattern class under all admissible
  (structure-preserving, witness-injective) quotients; then any homomorphic
  image collapses to a member of the finite closed family, and the forcing
  argument survives arbitrary incidental overlaps.
SIGNATURE: a forcing/exclusion argument silently assumes two witnesses are
  disjoint; overlap cases unhandled.
ROUTE_B: import audits (K3 counterexample hunts) where two certificate
  instances may share cells/bands; quarantined-artifact collision audits
  (post-034 sliver) — overlap taxonomy before promotion.
TRANSFER: the quotient family must stay FINITE and each member keep the load-
  bearing substructure injectively.
DUAL: "what happens when the two witnesses overlap? is the quotient family closed?"
STATUS: UNTESTED

## C12 BOUNDED-POTENTIAL-EXCLUSION                               [src: Ch12 + Ch3]
MECHANISM: exclude a hypothetical global object by a monotone potential bounded
  in [0,1]: each layer of the object provably increases it by fixed w > 0;
  enough layers → contradiction. Companion law (Ch3): never iterate an
  UNBOUNDED quantity — replace by a bounded monotone surrogate with per-
  component median normalization f = M/(M+median); telescoping + coarea then
  convert one-sided drift into concentration.
SIGNATURE: need NONexistence of an embedded/global configuration where local
  counting fails; or iteration accumulates small relative losses on an
  unbounded invariant.
ROUTE_B: HumpMassBound (node 3.2) accumulation arguments; excluding off-line
  zero configurations via a monotone functional; ledger quantities spanning
  1e-30..1e-243 — normalize to bounded ratios before iterating.
TRANSFER: potential bounds must be independent of the hypothetical object
  (K5 circularity audit); the per-layer gain w must survive all dependence
  corrections (η(L)-terms) with margin.
DUAL: "is the potential's bound independent of the object being excluded?
  is the iterated quantity bounded?"
STATUS: UNTESTED


## C13 RESTORE-SYMMETRY-BY-EXPLICIT-SHADOW                       [src: Zwegers 2002 mock-theta; owner-ratified 2026-08-23]
MECHANISM: when an object ALMOST satisfies a functional law (modular
  transform, Poisson/inversion identity, functional equation) because it was
  truncated, localized, or otherwise pushed out of the law's domain: do not
  estimate the violation. COMPLETE the object — write the EXACT identity
  "broken object = transformed object + explicit shadow terms", where every
  shadow term is a closed-form object (Zwegers: the period-integral shadow
  restoring SL2(Z) for Ramanujan's mock theta functions; here: point/boundary
  defects restoring the summation-map symmetry). Estimation happens only
  AFTER the exact completion, term by term.
SIGNATURE: a symmetry/functional law holds on an ideal class (Schwartz,
  modular, zero-mass); the production object misses the class by explicit
  finite data (truncation jumps, nonzero point values, endpoint seams); the
  gap between "near-symmetric" and "symmetric" blocks a rate or a radical
  membership.
ROUTE_B: BV Poisson defect identity of H2A_4_1B_3C_1_7 — the truncated
  prolate trial breaks Connes (18); the exact completion
  E(f)(u) = E(fhat)(1/u) + (1/2)fhat(0)u^(-1/2) - (1/2)f(0)u^(1/2)
  carries both point defects explicitly (one survives for the selected
  trial). Candidate next uses: near-radical budget for the truncated trial
  (supplier S2/T3 chain); any window/inversion covariance statement.
TRANSFER: the shadow must live in ONE declared category (L2/function, form,
  distribution, operator graph) with any category change carried by a named
  map — the 3C.1.6/3C.1.7 endpoint-atom repair is the standing counterexample.
  The completed identity must be EXACT (no O-terms); a shadow that is itself
  only estimated re-imports the original problem (K5 circularity).
DUAL (Прошка): "is the defect being ESTIMATED where it could be written
  EXACTLY — and does the completed object satisfy the exact law term by term,
  in one category?"
STATUS: USED(H2A_4_1B_3C_1_7)
BRIDGE_KIND: ONE_WAY_TRANSFER  # mechanism transfer from mock-modular
  completion; no inverse map claimed
INSIGHT_STATE: FALSIFIER_PASSED  # exact identity derived and plants run
  (3C.1.7-3C.1.9); not yet SOURCE_WRITTEN/KERNEL_GREEN
FALSIFIER: transform-label plant (a Mellin label does not create
  radicality: B(G,G)=1 for G=e_0 under the identity form) + seam plant
  (full-endpoint vs midpoint E-star differ pointwise at u=lambda/n,
  equal a.e.)
TOY_VALIDATION: NOT_RUN  # identity derived symbolically; no numeric run
DEPENDENCY_FOOTPRINT:
  CLOSES: [BV_POISSON_POINT_DEFECT_ALGEBRA]
  OPENS:  [SELECTED_ABEL_LIMIT_ACTUAL_FOURIER_CROSSWALK_AND_ROOT_ENERGY]
NOTE: the C13 slot mentioned in the 2026-08-05 unified-contour verdict
  (source-faithful transport, C13_SHAPE_TEST) was NOT_MINTED and remains a
  separate future card; per deck rule cards append sequentially and never
  renumber, so that family will take the next free number when it splits.

# END v1 — 13 cards (C13 minted 2026-08-23, owner-ratified). Update discipline: status changes ONLY with goal-NNN cite
# (USED) or one-line autopsy (KILLED), per K6/K8. New cards append as C13+,
# never renumber (CLOSED_GOAL_IMMUTABLE analogue for card identity).
