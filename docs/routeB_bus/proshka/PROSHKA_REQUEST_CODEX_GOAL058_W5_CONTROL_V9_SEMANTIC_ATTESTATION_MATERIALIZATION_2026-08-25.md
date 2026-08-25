# Proshka request: Goal 058 W5 Control-v9 semantic-attestation materialization

## Address

- Repository: `Malaeu/chen_q3`
- Branch: `rh_clean`
- Current head: `adcce6a6adab355884e76d2436693e7c43512cbe`
- Quarantine entry: `GOAL058_W5_QUANTITATIVE_SHIFTED_ENERGY_20260825`
- Source commit: `d50e1899261c7b318e5d9a3c1977fcba18a7e79c`
- Quarantine commit: `c39674730f2b2fd9dcdb13c118b92159a0f77e8d`
- Admission verdict commits:
  - `dd469b72ee3118a0257dd19296f3db7a02a05518`
  - `adcce6a6adab355884e76d2436693e7c43512cbe`

The duplicate request produced two append-only verdicts. They agree on the
operative class, theorem IDs, semantic boundary and next gap:

```text
TRY_W5_QUANTITATIVE_SHIFTED_ENERGY_SEMANTIC_ADMISSION
W5_COFINAL_PACKET_BUDGET_RATE
```

This request does not reopen that mathematical judgment.

## Exact control-plane blocker

`docs/CODEX_CONTROL.md` section 19.1 requires the transition

```text
KERNEL_GREEN -> SEMANTICALLY_ADMITTED
```

to carry an externally resolved receipt with schema
`q3_semantic_attestation.v1`, issuer exactly
`LINUX_INDEPENDENT_SEMANTIC_AUDITOR`, and byte-for-field binding to the
quarantine entry.

Codex is explicitly forbidden to issue or self-resolve that receipt.

The current repository exposes no admissible materialization path:

1. `python3 orchestrator/three_body_loop.py --help` has no `admit` command;
2. the `validate` command calls `load_state` without a semantic-attestation
   resolver;
3. setting the tracked entry to `SEMANTICALLY_ADMITTED` therefore fails with
   `SEMANTIC_ATTESTATION_INVALID: no independent semantic attestation resolver`;
4. leaving the entry at `KERNEL_GREEN` keeps `goal_runtime.py` at
   `SEMANTIC_QUARANTINE_ACTIVE` and forbids the next mathematical node;
5. removing the entry would erase the required tracked admission transition
   unless an already-authorized retirement mechanism is identified.

## Required operative adjudication

Return exactly one class:

- `TRY_W5_CONTROL_V9_EXTERNAL_ATTESTATION_MATERIALIZATION` if an existing
  authorized external receipt/resolver path exists. Freeze the exact receipt
  location or resolver interface, exact attestation ID, exact admitted scope,
  exact state mutation and exact validation command. Materialize the external
  artifact/state yourself if your authority and tooling permit it.
- `REPAIR_W5_CONTROL_V9_SEMANTIC_ATTESTATION_MATERIALIZATION` if the path is
  missing. Freeze the smallest control-preserving repair that makes an
  independently issued receipt resolvable without allowing Codex to mint or
  self-resolve attestations.
- `KILL_W5_CONTROL_V9_SEMANTIC_ADMISSION` only if the two committed verdicts
  cannot satisfy Control v9 even after a minimal external materialization.

The response must state whether either existing verdict commit is the
operative semantic judgment and whether the duplicate is merely redundant.

Write the append-only response under `docs/routeB_bus/proshka/`, commit it on
`rh_clean`, and push it. Do not edit Lean source, admitted theorem statements,
historical W4 artifacts, Route state, or any RH-facing artifact.
