# PROSHKA REQUEST — GOAL 057 B3 ASSOCIATED WEIL OPERATOR DOMAIN SOURCE AUDIT

```yaml
MODE: DELEGATED_STRATEGIC_REVIEW
TRANSACTION: GOAL057_B3_ASSOCIATED_WEIL_OPERATOR_DOMAIN_SOURCE_AUDIT
CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
PHASE_KEY: UNCHANGED
HEAD: f62584be
ORIGIN_RH_CLEAN: f62584be
PARENT_PRIMARY: TRY_GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_REPAIRED
PARENT_SUCCESS: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_PROVED
CURRENT_GAP: SELECTED_KTRIAL_ASSOCIATED_WEIL_OPERATOR_DOMAIN_AND_COMPRESSION
OWNER_GATE: PX_RH_CLAIM_ONLY
```

## Completed parent

The repaired B2 child is committed and pushed. Production now has exactly:

```lean
ccmFiniteSynthesisEquiv
    (i : PairIndex) :
    EuclideanSpace ℂ (CCMModeFinite i.N) ≃ₗᵢ[ℂ] E_m_N i

sourceCCMFiniteRieszOperator
    (i : PairIndex) :
    Module.End ℂ (E_m_N i)

sourceCCMFiniteRieszOperator_apply_sourceTrial
```

Production SHA-256:
`bf72d6f84c33f6ddd0f6e0c76563c8d6cf4416124f1b8c8e8dc988dc4ad58e59`.

Direct Lean, target/full build, `q3_check`, 80/80 orchestrator tests, strict
Spine, 7/7 proof-DB declarations, three SQLite integrity checks, and all six
plants pass. This is only `FINITE_RIESZ_CARRIER_BIND_ONLY`; the checkpoint
ledger remains `0 closed / 10 remaining`.

## Exact current target

Let the literal selected trial be

```lean
xE : E_m_N i :=
  kTrial_m_N
    i
    (prolateCombination (S.source.pair i))
    (S.source.eStar_memLp i)
    (S.source.trialNonzero i)
```

and let `x : H_m i := xE`. For the source-associated unbounded Weil operator
`A_m`, the desired paper-level facts are:

```text
x ∈ Dom(A_m)

P_m_N i (A_m x) = sourceCCMFiniteRieszOperator i xE
```

The second equality follows from the form-representation identity once the
domain membership, ambient operator, form, and projection are all genuinely
pinned. No invariance claim `A_m(E_m_N) ⊆ E_m_N` is needed merely to project
`A_m x`.

## Source audit completed locally

### 1. Current Lean bytes

There is no production Lean declaration for any of:

- `qW_m` / `BW_m`;
- `Dom(A_m)`;
- the associated unbounded operator `A_m`;
- a closed lower-semibounded form representation theorem.

Pinned Mathlib has orthogonal projections and Fréchet-Riesz duality, but the
local source scan found no closed-semibounded-form / associated-unbounded-
operator API. Therefore a direct implementation is not a wrapper around an
existing library object.

### 2. Project source locks

`D0_2_EXACT_WEIL_SESQUILINEAR_FORM.md` proves at paper level only:

```text
E_m_N ⊆ Dom(BW_m)
```

`D0_3_EXACT_OPERATOR_TYPE_REGISTRY.md` explicitly records:

```text
E_m_N ⊆ Dom(A_m)                         NOT PROVED
A_m(E_m_N) ⊆ E_m_N                       NOT PROVED
WeilOp_m_N = A_m restricted to E_m_N        NOT PROVED
WeilOp_m_N = P_m_N A_m P_m_N                NOT PROVED
```

Both artifacts are `SOURCE_LOCKED / LEAN_UNPINNED` at the relevant interface.

### 3. Primary paper facts

Pinned source:

`literature/zotero/H8ULBMAL/fulltext.md`

Connes–Consani–Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755.

- Proposition 3.3: `QW_λ` is lower bounded and lower semicontinuous.
- Proposition 3.4: the span of the modes `V_n` is a form core.
- Section 3.2 invokes the representation theorem and obtains the canonical
  lower-bounded unbounded selfadjoint `A_λ`.
- Theorem 3.6: `A_λ` has discrete lower-bounded spectrum.
- Before Corollary 3.8 the paper states that piecewise-smooth compactly
  supported functions are in the form domain because their Fourier transforms
  are `O(|t|^-1)`.

The paper passage found locally does not state that those functions lie in the
operator domain.

### 4. Candidate real domain proof, not yet source-certified

The proof of Theorem 3.6 decomposes `A_λ` into bounded non-archimedean and
pole contributions plus an archimedean Fourier multiplier with

```text
∂_t θ(t) = 1/2 log|t| + O(1).
```

For a piecewise-smooth compactly supported `f`, the paper gives
`ƒ̂(t)=O(|t|^-1)`. Hence

```text
log|t| · ƒ̂(t) ∈ L²(dt).
```

Every production `V_n_m` is smooth on the compact multiplicative window, and
the selected `kTrial_m_N` is a finite linear combination of these modes.
This suggests the genuine route:

```text
finite mode span ⊆ Dom(A_m)
  ⇒ selected kTrial_m_N ∈ Dom(A_m)
  ⇒ projected action = finite Riesz action
```

But the current repository has neither the Fourier-multiplier realization of
`A_m` nor the analytic estimates needed to make this a small Lean proof.

### 5. Existing downstream receiver

`AmbientResidualSplit.lean` already proves the generic residual decomposition.
`H4A1_AMBIENT_RESIDUAL_SPLIT_2026-07-12.md` correctly rejects a premise-only
restatement: H4a1b still needs the exact domain-safe operator, projection,
trial, and form/operator crosswalk. Do not materialize another theorem whose
only new input is the desired compression equality.

## Decision requested

Choose exactly one operative primary.

### Candidate A — source-specific operator-domain construction

```text
TRY_GOAL057_B3_SELECTED_KTRIAL_OPERATOR_DOMAIN_FROM_PIECEWISE_SMOOTH_CORE
```

Select this only if the primary source plus standard analysis genuinely
support the `O(1/t) × log(t)` operator-domain route. Give the smallest exact
sequence of mathematical and Lean children; identify whether we must first
materialize a source-specific Fourier multiplier/operator graph or a reusable
closed-form representation layer. Do not hide that infrastructure inside a
single theorem.

### Candidate B — form-dual residual replacement

```text
TRY_GOAL057_B3_FORM_DUAL_RESIDUAL_REPLACEMENT
```

Select this only if an exact form-dual defect can feed the actual H3/H4 chain
without merely assuming the missing operator-domain theorem. Name the first
existing consumer and prove that the replacement advances the current
checkpoint rather than renaming it.

### Candidate C — kill the current operator-domain route

```text
KILL_GOAL057_B3_CURRENT_OPERATOR_DOMAIN_COMPRESSION_ROUTE_SOURCE_UNAVAILABLE
```

Select this if neither A nor B is presently source-backed and executable.
Then name one dependency-aware replacement atom with the highest information
gain and no surrogate operator.

## Required ruling details

For the selected candidate, return:

1. exact mathematical theorem shape;
2. exact source pin(s), including whether the piecewise-smooth argument gives
   form-domain or operator-domain membership;
3. minimum production file(s) and public surface;
4. K6 object precommit;
5. executable plants for form-domain/operator-domain, bounded/unbounded,
   projection-codomain, and surrogate-operator errors;
6. STOP, SUCCESS, and next gap;
7. honest effect on the ten-checkpoint ledger;
8. whether this remains the same six-field phase and living chat.

## Boundaries

```yaml
FORBIDDEN:
  - treat_form_domain_as_operator_domain
  - model_A_m_as_Module_End_of_H_m
  - infer_operator_compression_from_finite_form_coordinates
  - introduce_a_bounded_surrogate_A_m
  - materialize_a_premise_only_hCompressedAction_receiver
  - claim_E_m_N_invariance_without_proof
  - call_the_finite_residual_the_continuum_numerator
  - close_H4a1b_without_the_domain_and_crosswalk
  - decrement_the_ten_checkpoint_ledger_without_a_closed_checkpoint
  - create_Bus_010
  - release_Goal_055
  - submit_Aristotle
  - promote_Route_B
  - make_PX_or_RH_claim
  - open_a_fresh_chat

ROUTE: CHALLENGER_NOT_RH
BUS_010: VOID
GOAL_055: HOLD
G2_CCM: FROZEN
ARISTOTLE_SUBMISSION: NONE
PX_RH_CLAIM: NOT_MADE
```
