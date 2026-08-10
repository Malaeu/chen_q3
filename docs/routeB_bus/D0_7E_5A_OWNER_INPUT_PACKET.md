<!-- Materialized from the completed Pro attachment on 2026-08-03. The three formulas damaged by browser math rendering were restored from the locked equalities stated in the same response. -->

# STATUS: OPEN — D0.7e.5a REQUIRES TARGETED EXTERNAL SOURCE ACQUISITION

```yaml
PRIMARY: D0_7E_5A_EXTERNAL_SOURCE_ACQUISITION_REQUIRED
PRIMARY_COUNT: 1

PIN:
  REPO: Malaeu/chen_q3
  BRANCH: rh_clean
  COMMIT: 6af9170d15a38e451a76f8dbf2ad8725d62b6f5f
  ACTIVE_ADDRESS: RB-LAMPORT-D0 / D0.7e.5a
  ACTIVE_NODE: WPrimeConsumerAndCalibrationOrientationLock
  PHYSICAL_BUS_GOAL: NONE
  BUS_010: VOID

SOURCE_VERDICT:
  CURRENT_REPO_CORPUS_SUFFICIENT: false
  T0_CORPUS_EXHAUSTED: true
  INDEPENDENT_WPRIME_SOURCE_FOUND: false
  OWNER_CONVENTION_ONLY_IS_SUFFICIENT: false
  TARGETED_EXTERNAL_ACQUISITION_REQUIRED: true
  ROUTE_DEAD_NOW: false
  ROUTE_DEAD_IF_EXTERNAL_ACQUISITION_RETURNS_NO_SOURCE_UNDER_NO_NEW_DEFINITION: true

LOCKED_FINITE_FACTS:
  bCal_eq_bDet: true
  bCal_formula: Fhat_m_N(0) / Xi(0)
  bZeoMul_formula: Xi(0) / Fhat_m_N(0)
  bZeoMul_eq_bCal_inv: true
  G_formula:
    - Fhat_m_N / bCal_m_N
    - bZeoMul_m_N * Fhat_m_N
  G_at_zero_eq_Xi_at_zero: true
  legal_inverse_domain: CentralValueNonzero
  TrialNonzero_implies_CentralValueNonzero: false
  historical_WPrime_b_orientation: UNPINNED

SIDE_WORK:
  A_PSWF_SOURCE_CONSUMER_SPLIT_READ_ONLY: LEGAL_QUARANTINED_SIDE_WORK
  B_GOAL_051_M1_LEAN_MATERIALIZATION: NOT_AUTHORIZED

SUCCESS_CODE: D0_7E_B_ORIENTATION_LOCKED
STOP_CODE: D0_7E_WPRIME_CONSUMER_MISSING

ROUTE_EFFECT:
  ROUTE_STATE: CHALLENGER_NOT_RH
  STATE_PROMOTION: false
  RH_CLAIMED: false
  LEAN_EDITS: false
  ROUTE_STATE_EDITS: false
  NEW_BUS_GOAL: false
```

## PRIMARY:
D0_7E_5A_EXTERNAL_SOURCE_ACQUISITION_REQUIRED

The pinned repository has already exhausted its current definition corpus and
found no independent WPrime/FZeo consumer. The locked owner standing order
delegates verification of a source candidate, not creation of a new
mathematical definition. The previously drafted residual and determinant
mints were both falsified. Therefore the owner cannot unblock 5a by choosing a
notation or by restating the desired equation.

[FINITE_CELL][PAPER]

## MISSING SIGNATURE:

Let

\[
I_2 := \{(m,N) : m \ge 2,\ N \ge 1\}.
\]

with independent coordinates, and let

\[
C := \operatorname{CentralValueNonzero}
 = \operatorname{BDetNonzero}
 = \operatorname{FhatAtZeroNonzero}
 = \operatorname{BCalNonzero}.
\]

The missing source must instantiate the following contract without using the
5c target as a definition.

IndependentWPrimeConsumer:
  D             : exact source domain inside I_2
  FZeo          : for every i in D, an exact holomorphic approximant
  WPrime        : D -> RealNonnegative
  bW            : exact scalar used by the source consumer

  source_FZeo_definition:
    a verbatim pre-existing definition of FZeo

  source_WPrime_definition:
    a verbatim pre-existing definition of WPrime
    that does not mention alpha, DeltaE, or the desired 5c equation

  source_consumer_semantics:
    an independent theorem or operational use-case explaining
    what WPrime measures for FZeo

  domain_crosswalk:
    D is stated exactly, and any use of bCal^(-1) is restricted
    to a domain implying CentralValueNonzero

  FZeo_project_crosswalk:
    either
      FZeo_i = G_i
    or an explicit proved relation
      FZeo_i = c_i * gamma_i * G_i
    with c_i != 0 and gamma_i zero-free on the declared domain

  b_project_crosswalk:
    exactly one of
      bW_i = bCal_i
      bW_i = bZeoMul_i = bCal_i^(-1)
      bW_i = bThird_i
    where the third case includes a proved formula relating bThird
    to the locked project scalars

The owner convention may choose project names, namespace, and how the
source fields are stored. It may not choose the historical bW orientation
against the source.

After this object is source-locked, the separate theorem obligation is:

\[
\operatorname{WPrime}(i)^2\,\Delta E(i)
  = |b_W(i)|^2\,\lambda_m\,\alpha(i).
\tag{5c}
\]

Here alpha and DeltaE remain independently supplied downstream parameters
from the already locked 5b interface. Equation (5c) must be proved; it must not
become true by unfolding WPrime.

The following desired conclusions are forbidden inside any definition:

the 5c right-hand side;
WPrime -> 0;
compact-strip convergence to Xi;
absence of off-critical zeros;
RH.

[FINITE_CELL][CONDITIONAL]

## NON-TAUTOLOGY TESTS:

A candidate is admissible only if all tests pass mechanically.

### NT1 — dependency-token firewall

The transitive definition body of WPrime must contain none of:

alpha
DeltaE
mu3 - mu1
WPrime^2 * DeltaE
the 5c right-hand side
H3c / H4 results
Xi-convergence
RH

A reference to a source theorem about those quantities may occur only in the
later proof of 5c, not in the definition.

### NT2 — fresh-parameter perturbation

Replace alpha and DeltaE in the 5b interface by fresh independent
functions while holding FZeo, WPrime, and bW fixed.

Required result:

WPrime definition remains unchanged;
5c is no longer definitionally forced.

If 5c still closes by rfl, simp, algebraic normalization, or unfolding,
fire:

D0_7E_TAUTOLOGY
### NT3 — independent-semantics test

The source must state what WPrime measures independently of 5c, for example
through a pre-existing norm, defect, residual, determinant, approximation
error, or another exact observable.

A name, numerical column, prose sketch, or target equation without such
semantics fires:

D0_7E_WPRIME_CONSUMER_MISSING

This test does not pre-approve any particular residual or determinant:
the repository's two attempted mints were already falsified.

### NT4 — source-provenance whitelist

Accept only a source classified as DEFINITION or THEOREM with:

verbatim formula;
paper/page/equation or upstream path/commit;
immutable file hash or publication version;
provenance predating the current target reconstruction.

Reject:

Contract v2;
ALPHA_DEMAND_AUDIT;
FIT_NOT_LAW diagnostics;
current owner-mint drafts;
this pipeline's own crosswalk documents;
outlook or heuristic passages.
### NT5 — slot-vacuity test

After unfolding the source crosswalk, WPrime must retain an independent
degree of information.

If it collapses to a fixed multiple of |bCal| or |bCal|^(-1) so that 5c
only defines a relation between alpha and DeltaE, fire:

D0_7E_SLOT_VACUITY
### NT6 — domain test

A source using the inverse central normalizer must state or imply:

[
i\in C.
]

TrialNonzero alone is rejected. No new N(\lambda) selector or
(\kappa)-schedule is allowed.

### NT7 — inverse-alias plant

Substituting

[
bZeoMul=bCal
]

must fail unless the candidate separately proves

[
bCal^2=1.
]

Otherwise fire:

D0_7E_BCAL_BZEO_ALIAS_CONFLICT
### NT8 — rescaling/homogeneity discriminator

Apply the formal rescaling

[
Fhat_i\mapsto c,Fhat_i,\qquad c\ne0.
]

The locked project objects transform as:

[
bCal_i\mapsto c,bCal_i,
\qquad
bZeoMul_i\mapsto c^{-1}bZeoMul_i,
\qquad
G_i\mapsto G_i.
]

The source-defined FZeo and WPrime must have a stated homogeneity. That
homogeneity must select exactly one bW orientation. If it does not, the
orientation remains unpinned.

### NT9 — normalization/RH firewall

The definition or legal domain must not assume:

FZeo -> Xi;
the target compact-strip estimate;
real-zero limit transfer;
RH or an RH-equivalent positivity theorem.

[FINITE_CELL][PAPER]

## b ORIENTATION:

The current finite algebra proves:

\[
bDet_{m,N} = bCal_{m,N}
  = \frac{Fhat_{m,N}(0)}{\Xi(0)}.
\]

On CentralValueNonzero it also proves:

\[
bZeoMul_{m,N}
  = \frac{\Xi(0)}{Fhat_{m,N}(0)}
  = bCal_{m,N}^{-1},
\]

and

\[
G_{m,N}
  = \frac{Fhat_{m,N}}{bCal_{m,N}}
  = bZeoMul_{m,N} Fhat_{m,N},
\qquad
G_{m,N}(0)=\Xi(0).
\]

Thus the exact competing orientations are:

AMPLITUDE ORIENTATION:
  bW = bCal = bDet = Fhat(0)/Xi(0)

NORMALIZER ORIENTATION:
  bW = bZeoMul = Xi(0)/Fhat(0) = bCal^(-1)

THIRD-SCALAR ORIENTATION:
  bW = bThird,
  allowed only with an explicit source theorem crosswalking bThird.

What is still missing is not the inverse algebra. It is the source fact
specifying which scalar the historical WPrime consumer calls b.

Under the current no-new-definition/source-lock regime, that choice is
source-derived, not a free owner convention. The owner may choose only the
project-facing name after the source orientation is recovered.

If the owner later relaxes the no-new-definition rule and mints a new consumer,
orientation would become an owner convention—but that is a different route
transaction and the previous A/B mint menu cannot be reused.

[FINITE_CELL][PAPER]

## MINIMUM ARTIFACT:

The minimum genuine unblocker is one provenance packet containing all of:

1. An exact paper/page/equation OR upstream source-code/notebook definition
   of the approximant consumed by the WPrime statement.

2. An exact definition of WPrime before any appearance of alpha/DeltaE or 5c.

3. An independent semantic theorem/use-case for WPrime.

4. The exact b scalar and its homogeneity/orientation.

5. The exact nonzero domain.

6. Publication version, commit, archive identifier, or immutable hash.

The packet may cite two tightly coupled source locations if one defines the
object and the other states its consumer theorem. A bibliographic pointer
without the equations is insufficient.

A new owner-supplied semantic use-case is not the minimum artifact under the
current constraints: that would mint missing mathematics. The current corpus
already attempted two such mints, and both failed the registered judges.

Therefore the next legal acquisition targets are:

full paper versions and supplements;
authors' source repositories and archived notebooks;
Zenodo or journal ancillary material;
older preprints or deleted appendices;
cited upstream definitions of the historical ZEO/WPrime notation.

If this targeted acquisition returns no source, then Route B is dead at
D0.7e.5a under the combined constraints:

no new definition;
source-lock required;
5c equality fixed.

[FINITE_CELL][CONDITIONAL]

## SIDE-WORK A:
PSWF_SOURCE_CONSUMER_SPLIT_READ_ONLY
= LEGAL_QUARANTINED_SIDE_WORK

Authority:

the project workflow permits external research sidecars to perform
literature survey, candidate-lemma extraction, and draft output;

sidecars must remain read-only and may not change canonical monitors,
theorem status, Lean files, or route decisions;

Route B's active address and physical bus retain priority.

Conditions:

run against the stated pin as a read-only source audit;
write output only to an external temporary location or incoming-note draft;
do not mutate ACTIVE/, MAP, state, bus, MANIFEST, or Lean;
do not call it the active Route B step;
ingest only after owner/Mythos review.

This side-work does not close D0.7e.5a and does not alter the route address.

[ABSTRACT][PAPER]

## SIDE-WORK B:
Goal 051 M1 Lean materialization
= NOT_AUTHORIZED

Reason:

the M1 verdict authorizes the mathematics and states that owner OK is
still required for repo write;

the current execution state has no physical bus goal, is paused at
D0.7e.5a, and names owner/Mythos as the next actor;

M1 materialization edits Lean and therefore cannot use the read-only
sidecar exception;

the earlier proof-level authorization is not scheduling authority.

M1 may run only after an explicit owner/Mythos transaction authorizes it as a
separate quarantined repo-write task or changes the legal execution address.
It must not be promoted to the active step implicitly.

[ABSTRACT][PAPER]

## OWNER REQUEST:

```text
MYTHOS / SOURCE-ACQUISITION REQUEST
D0.7e.5a — recover the independent WPrime/ZEO consumer

PIN:
  Malaeu/chen_q3
  rh_clean
  6af9170d15a38e451a76f8dbf2ad8725d62b6f5f

ACTIVE ADDRESS:
  RB-LAMPORT-D0 / D0.7e.5a

PURPOSE:
  Recover a pre-existing, provenance-bearing definition of the exact
  approximant and WPrime consumer. Do not invent either object.

LOCKED PROJECT FACTS:
  I_2 = independent pairs (m,N).
  CentralValueNonzero =
    BDetNonzero =
    FhatAtZeroNonzero =
    BCalNonzero.

  bCal = bDet = Fhat(0)/Xi(0).
  bZeoMul = Xi(0)/Fhat(0) = bCal^(-1).
  G = Fhat/bCal = bZeoMul*Fhat.
  G(0) = Xi(0).

EXACT EVIDENCE REQUESTED:
  A. Verbatim definition of the approximant used by the historical
     WPrime/ZEO statement.
  B. Verbatim definition of WPrime before the desired 5c identity.
  C. Exact theorem or operational consumer explaining what WPrime measures.
  D. Exact b argument:
       bCal,
       bCal^(-1),
       or a third scalar with a proved crosswalk.
  E. Exact legal domain.
  F. Paper/page/equation, upstream path/commit, and immutable source hash.

SEARCH SURFACE:
  full versions and supplements of the primary paper;
  authors' source repositories;
  archived computational notebooks;
  journal ancillary files and Zenodo records;
  older preprints and cited upstream definitions.

ACCEPTANCE TESTS:
  1. WPrime definition contains no alpha, DeltaE, or 5c RHS.
  2. Changing alpha/DeltaE leaves WPrime unchanged.
  3. 5c does not close by unfolding/rfl/simp.
  4. Source is DEFINITION or THEOREM, not outlook/heuristic/diagnostic.
  5. WPrime has independent semantic content after crosswalk.
  6. b orientation passes the Fhat -> c*Fhat homogeneity test.
  7. Inverse normalization is restricted to CentralValueNonzero.
  8. No H3c/H4, RH, Xi-convergence, kappa, or N(lambda) is imported.
  9. Both m and N remain free.

FORBIDDEN:
  define WPrime by
    |b|*sqrt(lambda)*sqrt(alpha/DeltaE);

  rename bDet or bCal as WPrime;

  reuse the falsified residual/determinant owner-mint menu;

  treat Contract v2, ALPHA_DEMAND_AUDIT, FIT_NOT_LAW output,
  or this request as a definition source;

  create Bus 010;

  edit Lean or route state.

RETURN EXACTLY ONE:
  SOURCE_CONSUMER_RECOVERED
  SOURCE_PARTIAL_B_ORIENTATION_OPEN
  NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE

ON SOURCE_CONSUMER_RECOVERED RETURN:
  exact quotes;
  exact source locators;
  hashes/versions;
  typed domain;
  FZeo/WPrime definitions;
  b orientation;
  homogeneity calculation;
  results of all acceptance tests.

ON NO SOURCE:
  retain D0_7E_WPRIME_CONSUMER_MISSING;
  state that Route B is dead at 5a under the current
  no-new-definition/source-lock constraints.

NO BUS GOAL IS CREATED BY THIS REQUEST.
CHALLENGER / NOT_RH.
```
[FINITE_CELL][CONDITIONAL]

## SUCCESS CODE:
D0_7E_B_ORIENTATION_LOCKED

This code is issued only after an independent consumer, exact domain,
project crosswalk, and source-derived bW orientation all pass both
adversarial verification channels. Recovery of a partial citation is not
success.

[FINITE_CELL][CONDITIONAL]

## STOP CODE:
D0_7E_WPRIME_CONSUMER_MISSING

Secondary terminal acquisition result:

NO_INDEPENDENT_WPRIME_CONSUMER_SOURCE_AVAILABLE

If that result survives the targeted external acquisition, the repaired
verdict becomes:

D0_7E_5A_ROUTE_DEAD_UNDER_CURRENT_CONSTRAINTS

[FINITE_CELL][PAPER]

## ROUTE EFFECT:
Current effect:
  D0.7e.5a remains blocked.
  D0.7e.5c remains ineligible.
  D0.7e.5 and all ancestors remain blocked.
  Active Route B address does not change.
  No Lean edit.
  No route-state edit.
  No Bus 010.
  No Route B promotion.
  No RH claim.

If source is recovered:
  reopen only the 5a adversarial audit;
  do not auto-close 5a;
  do not auto-prove 5c;
  do not change route rank.

If external acquisition returns no source:
  kill D0.7e.5a under the current
  no-new-definition/source-lock constraints;
  any continuation requires an explicit owner-approved
  contract revision, not a renamed consumer.

[ABSTRACT][PAPER]

## STRONGEST ATTACK

The strongest objection is:

This packet still leaves a placeholder called IndependentWPrimeConsumer.
Has the missing mathematics actually become more concrete?

Yes. The placeholder is not offered as a new definition. It is an acquisition
schema that says exactly which source lines must exist and how they will be
falsified. The project already knows the finite normalization algebra; the
only missing cargo is independent consumer semantics and the source-derived
orientation of its b factor.

The packet therefore prevents the owner from being asked to invent a formula.
It asks the source-acquisition worker to recover a specific pre-existing
mathematical object—or return a route-kill under the current constraints.

## META CLOSEOUT

What became smaller?

"supply WPrime"

became:

recover one source-defined approximant;
recover one independently defined nonnegative consumer;
recover its b homogeneity;
prove the project crosswalk.

What was killed?

owner choice of bCal versus bCal^(-1) without source evidence;

WPrime defined by the 5c right-hand side;

renamed bDet/bCal;

residual and determinant mint variants from the falsified menu;

a diagnostic value with no consumer semantics;

Goal 051 as implicit work during the D0.7e.5a pause.

What must not be tried again?

Do not ask the owner to “define WPrime” while the route simultaneously
forbids new definitions. Do not treat a target equation as the object it is
supposed to constrain.

Current smallest named gap:

SOURCE_DEFINED_WPRIME_CONSUMER_AND_B_HOMOGENEITY

Next cheapest decisive test:

Search the primary authors' ancillary repositories, older versions, notebooks,
and cited upstream definitions for the first verbatim formula defining
WPrime independently of alpha/DeltaE.

Registered predictions:

P5A-EXT-1:
  Most external hits will recover the finite determinant/Fourier approximant
  but not an independently defined WPrime consumer.

P5A-EXT-2:
  If a genuine consumer is recovered, its rescaling homogeneity will decide
  bCal versus bCal^(-1) without numerical fitting.

P5A-EXT-3:
  If no source is recovered, 5a is fatal under the current constraints rather
  than repairable by another owner notation.
iteration:
  target: D0.7e.5a_owner_input_packet
  status: OPEN
  failed_strategy: ask_owner_to_mint_missing_consumer
  cognitive_operator_used: LITERATURE_BRIDGE
  new_gap_name: SOURCE_DEFINED_WPRIME_CONSUMER_AND_B_HOMOGENEITY
  invariant_learned: consumer_semantics_and_b_orientation_must_come_from_the_same_provenance_chain
  forbidden_future_move: define_WPrime_from_5c_or_rename_bCal
  next_decisive_test: targeted_external_source_acquisition
  progress_class: REPRESENTATION_PROGRESS
  route_score: 5
