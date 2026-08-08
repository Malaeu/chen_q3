# PROSHKA REQUEST — GOAL 057 B2 FINITE RIESZ OPERATOR SOURCE-BIND RELEASE

```yaml
MODE: DELEGATED_STRATEGIC_REVIEW
TRANSACTION: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_RELEASE
CONVERSATION_ID: 6a72e750-dc60-83eb-946b-61d2073c232b
PHASE_KEY: UNCHANGED
HEAD: 1ba34ff53f80071c29018860ef826f636279de10
ORIGIN_RH_CLEAN: 1ba34ff53f80071c29018860ef826f636279de10
PARENT_RESPONSE_ID: 46ec7d70-a6f9-4fad-a792-2c70ca6d0393
PARENT_PRIMARY: KILL_GOAL057_B2_DIRECT_CROSSWALK_SOURCE_UNAVAILABLE
SELECTED_CHILD: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND
OWNER_GATE: PX_RH_CLAIM_ONLY
```

## Why this is a separate release boundary

Your B2 source audit correctly killed the direct `hCompressedAction` theorem shape.
The repository does not have a domain-safe ambient associated Weil operator, selected
trial operator-domain membership, or a source theorem identifying the finite Riesz
operator with `P_m_N A_m P_m_N`. That KILL is now archived, state-pinned, committed,
and pushed at the commit above. The ten-checkpoint ledger remains `0 closed / 10
remaining`.

This request asks only whether the prerequisite child you selected may now be
materialized in production Lean. It does not reopen the killed direct target.

## Local type confirmation

Production source currently has exactly:

```lean
ccmFiniteSynthesis
    (i : PairIndex) :
    (CCMModeFinite i.N → ℂ) →ₗ[ℂ] H_m i

sourceCCMFiniteOperator
    (i : PairIndex) :
    Module.End ℂ (CCMModeFinite i.N → ℂ)

E_m_N (i : PairIndex) : Submodule ℂ (H_m i)

P_m_N (i : PairIndex) : H_m i →L[ℂ] E_m_N i
```

`ccmFiniteSynthesis_sourceCCMComplexRow` already identifies the forward synthesis of
the exact source row with the ambient coercion of the literal `kTrial_m_N` source
trial. `coe_P_m_N_apply_eq_sum_inner_V_n_m_smul` already pins the conjugate-first
coordinate orientation. The literal finite index order is
`j ↦ ccmModeFinite N j = j-N`, hence `-N,…,N`.

## Exact proposed production child

Owned file only:

`q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarCCMFiniteRieszOperator.lean`

Sole import:

```lean
import Q3.Proofs.RouteB.D0PstarCCMFiniteSourceResidual
```

Namespace: `Q3.RouteB.D0Pstar`.

Public surface exactly:

1. `ccmFiniteSynthesisEquiv`
2. `sourceCCMFiniteRieszOperator`
3. `sourceCCMFiniteRieszOperator_apply_sourceTrial`

The theorem statement is exactly the one in your B2 verdict:

```lean
theorem sourceCCMFiniteRieszOperator_apply_sourceTrial
    (S : ProlateCanonicalSourceData)
    (i : PairIndex) :
    let xE : E_m_N i :=
      kTrial_m_N
        i
        (prolateCombination (S.source.pair i))
        (S.source.eStar_memLp i)
        (S.source.trialNonzero i)
    ((sourceCCMFiniteRieszOperator i xE : E_m_N i) : H_m i) =
      ccmFiniteSynthesis i
        (sourceCCMFiniteOperator i
          (sourceCCMComplexRow S i)) := by
  ...
```

Required semantics and plants remain verbatim from the B2 verdict: exact isometric
coordinate equivalence, exact `-N,…,N` order, conjugate-linear-first coefficients,
operator on `E_m_N` rather than `H_m`, and all five `P057_B2_*` mutations firing.

## One decision required

Return exactly one operative primary:

- `RELEASE_GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND` if this exact child is
  source-backed, non-duplicative, and worth materializing now; or
- one `KILL_...` / `TRY_..._REPAIRED` primary with the smallest exact correction if
  the equivalence or theorem still hides a carrier/orientation/tautology defect.

If released, give the minimum implementation-sensitive Lean route for constructing
the `LinearIsometryEquiv` and conjugating the coefficient operator. Do not expand the
public surface.

```yaml
STOP: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_MISSING
SUCCESS: GOAL057_B2_FINITE_RIESZ_OPERATOR_SOURCE_BIND_PROVED
NEXT_GAP_AFTER_SUCCESS: SELECTED_KTRIAL_ASSOCIATED_WEIL_OPERATOR_DOMAIN_AND_COMPRESSION
FORBIDDEN:
  - edit_any_Lean_file_inside_this_review
  - name_the_finite_operator_A_m
  - assert_Dom_A_m_membership
  - assert_ambient_operator_compression
  - close_H4a1b
  - decrement_the_ten_checkpoint_ledger
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
PX_RH_CLAIM: NOT_MADE
```
