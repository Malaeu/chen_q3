# TASK 2026-08-24 — Goal 058 selected-Ferrers V/W phase closure

```yaml
schema: q3_codex_phase_goal.v1
task_id: GOAL058_SELECTED_FERRERS_V_W_FIXED_K_PHASE_CLOSE
goal_run: "058"
bus_goal: docs/routeB_bus/058_realzero_ground_diagonal_to_xi.goal.md
branch: rh_clean
base_head: 461f259e1526dfb30ce423c39d26d0cae21e49c5
owner_grant: GOAL_SCOPED_OPERATIONAL_GRANT_2026_08_24
phase_key_hash: 1c0914e2e93a49defedf2c8a8497fbdc22de993b7404e0426e4b2d6c131f9aae
mode: PHASE_THEN_BATCH_ONE_KERNEL_GREEN_AT_A_TIME
route: CHALLENGER_NOT_RH
bus_010: VOID
goal_055: HOLD
route_promotion: false
rh_claim: false
```

## Exact objective

Close the selected-Ferrers fixed-`k` V/W phase on the unchanged production
family and exact downstream shifted-archimedean form-domain consumer.

This is a phase-close goal inside the already open physical Goal 058.  It does
not mint Goal 059, does not create a second executable bus goal, and does not
claim G3, Route B promotion, W5, a cofinal rate, or RH.

The phase is closed only when:

1. every `PROSHKA_VERDICT_REQ_2026_08_22_V_*` item has a checked terminal
   ledger edge to one of `SEMANTICALLY_ADMITTED`, `KILLED`, `RETIRED`, or a
   later exact successor; a conditional preflight is never silently relabelled
   as a proved theorem;
2. the W3 Abel--Poisson `L2` lock remains bound to kernel commit `01ee6f43` and
   independent semantic-admission commit `8fa01d82`;
3. the W4 zero-endpoint repair is bound into the request lifecycle and the
   repaired production Lean node is kernel-green and independently
   semantically admitted;
4. the exact fixed-`k` shifted-form-domain assembly consuming that W4 node is
   kernel-green and independently semantically admitted;
5. the request queue for this phase has no unbound `OPEN`/`IN_REVIEW` verdict,
   semantic quarantine is empty, all registered closeout gates pass, and one
   source-addressed phase-close report records what remains open.

Success token:

```text
GOAL058_SELECTED_FERRERS_V_W_FIXED_K_PHASE_CLOSED
```

The sole successor intentionally left open by this task is:

```text
W5_COFINAL_RATE
```

## Immutable source pins

```yaml
W3_KERNEL_COMMIT: 01ee6f43822c3a7515dc56c76e0334de2a7e6b14
W3_SEMANTIC_ADMISSION_COMMIT: 8fa01d82
W4_INITIAL_AUTHORIZATION_COMMIT: 1fd5e432
W4_INITIAL_DECISION: TRY_W4_PIECEWISE_AC_DERIVATIVE_INTEGRABILITY_LEMMA
W4_LEDGER_REPAIR_VERDICT_COMMIT: 461f259e1526dfb30ce423c39d26d0cae21e49c5
W4_LEDGER_REPAIR_VERDICT_BLOB: 76d70ddef8c5770fa7c2e05ab6b9fefdf64c26a0
W4_LEDGER_REPAIR_DECISION: TRY_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR
W4_PREFLIGHT: docs/routeB_bus/H2A_4_1B_3C_1_13_W4_FIXED_K_SHIFTED_ROOT_ENERGY_PREFLIGHT_2026-08-24.md
W4_VERDICT: docs/routeB_bus/proshka/PROSHKA_VERDICT_CODEX_REQ_2026_08_24_W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_2026-08-24.md
```

## Execution DAG

### P0 — terminal V-ledger audit

Produce a deterministic ledger over all
`docs/routeB_bus/proshka/PROSHKA_VERDICT_REQ_2026_08_22_V_*` files.  For every
item record its exact Git blob, declared status, terminal successor or kill,
and the kernel/semantic-admission commit when applicable.  The audit is
evidence only; it does not reclassify conditional preflights.

Exit:

```text
V_LEDGER_COMPLETE_ZERO_UNBOUND_TERMINAL_EDGES
```

### P1 — bind the W4 repair verdict

Close the CAS lifecycle for
`REQ-2026-08-24-W4-ZERO-ENDPOINT-JUMP-LEDGER` against the exact verdict at
`461f259e`.  The answer must bind request ID, payload digest, request Git blob,
phase, blocker, verdict path/blob, decision, next node, and forbiddens.  No
manual state rewrite is allowed.

Exit:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_VERDICT_BOUND
```

### P2 — repaired W4 production Lean node

Continue the exact authorized file:

```text
q3.lean.aristotle/Q3/Proofs/RouteB/
G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

The public signature frozen by the verdict is unchanged.  The body of
`selectedFerrersAbelLogJumpBudget` uses exactly:

```lean
Finset.Icc 2 (k + 2)
```

The proof first establishes the sharp private piecewise-IBP bound with the
actual right-hand representative `g_k(0+)`, then pays the endpoint difference
by triangle inequality and identifies it with the final `n = k + 2` summand.
It must not use a midpoint surrogate or assume
`|g_k(0+)| <= |g_k(0)|`.

Mandatory gates:

```bash
cd q3.lean.aristotle
lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
lake build Q3.Proofs.RouteB.G6N1SelectedFerrersPiecewiseACDerivativeIntegrability
cd ..
scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersPiecewiseACDerivativeIntegrability.lean
```

Every public declaration and plant must have exactly
`[propext, Classical.choice, Quot.sound]`.

Kernel-green exit:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIRED_AND_FIXED_K_FOURIER_DECAY_KERNEL_GREEN
```

Semantic exit:

```text
W4_ZERO_ENDPOINT_JUMP_LEDGER_REPAIR_SEMANTICALLY_ADMITTED
```

### P3 — exact fixed-k shifted-form-domain assembly

After P2 semantic admission, close the exact consumer and no surrogate:

```lean
sourceArchimedeanShiftedFormDomain
```

The assembly must consume the production selected-Ferrers W3 limit, the W1
ordinary-Fourier-to-synthesized-isometry a.e. crosswalk, the repaired W4
fixed-`k` decay theorem, and the exact logarithmic source weight.  The theorem
head is minted only after exact-target/supplier preflight and, if its shape is
not already forced by an admitted source, one same-phase Proshka adjudication.

The result is fixed-`k` membership only.  No constant uniform in `k` and no
cofinal rate may occur in its statement or proof.

Exit:

```text
W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY_SEMANTICALLY_ADMITTED
```

### P4 — phase close

Write one source-addressed close report containing the V-ledger receipt, exact
W3/W4 kernel and semantic commits, theorem IDs, axiom profiles, validation
commands, rejected shortcuts, `CLOSES`, and the single `OPENS: W5_COFINAL_RATE`.
Run the registered goal-close transaction, strict startup, Route B status,
migration census, semantic freshness, and quarantine validation.  Update
physical route state last.  Do not close the parent Goal 058 unless its other
independent gates are actually closed.

## Commit and review loop

- One verified node, one scoped commit, then `git pull --rebase` and `git push`.
- Never stage unrelated local files, archives, SQLite sidecars, environments,
  or Aristotle exhaust.
- Proshka sees only committed GitHub bytes.  A reviewer request names the repo,
  branch, exact commit, canonical paths, and one precise requested decision.
- Use the unchanged living phase chat.  Never click `Answer now`; wait for
  natural completion.  Do not open a fresh chat for a helper, commit, build
  failure, or elapsed time.
- Ordinary child closure causes no reviewer call.  Use `PHASE_THEN_BATCH`; ask
  only at a real theorem-shape, source, semantic-admission, or fatal fork.

## Failure codes

```text
V_LEDGER_TERMINAL_EDGE_MISSING
W4_ZERO_ENDPOINT_REQUEST_BINDING_INVALID
W4_ZERO_ENDPOINT_RIGHT_REPRESENTATIVE_GAP
W4_REPAIRED_JUMP_BUDGET_GAP
W4_PIECEWISE_IBP_OR_DERIVATIVE_INTEGRABILITY_GAP
W4_ORDINARY_TO_SYNTHESIZED_FOURIER_CROSSWALK_GAP
W4_FIXED_K_SHIFTED_FORM_DOMAIN_ASSEMBLY_GAP
KERNEL_GREEN_NOT_SEMANTICALLY_ADMITTED
SEMANTIC_QUARANTINE_ACTIVE
```

## Hard boundaries

```text
NUMERICS: forbidden unless separately source-precommitted and authorized
ARISTOTLE: forbidden unless a later exact leaf is separately authorized
NEW_PAPER_AXIOM: forbidden
NEW_SORRY_ADMIT_NATIVE_DECIDE: forbidden
W5_COFINAL_RATE: open, outside this task
DOWNSTREAM_GOAL058_ASSEMBLY: outside this task
ROUTE_PROMOTION: false
PX_RH_CLAIM: NOT_MADE
```

## Physical phase state — 2026-08-24

The source-addressed closeout is:

```text
docs/routeB_bus/GOAL058_SELECTED_FERRERS_V_W_FIXED_K_PHASE_CLOSEOUT_2026-08-24.md
```

```text
STATUS: CLOSED
SUCCESS: GOAL058_SELECTED_FERRERS_V_W_FIXED_K_PHASE_CLOSED
OPENS: W5_COFINAL_RATE
PARENT_GOAL_058: OPEN
ROUTE_PROMOTION: false
RH_CLAIM: false
```
