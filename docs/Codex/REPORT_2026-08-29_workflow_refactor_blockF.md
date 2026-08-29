# WORKFLOW REFACTOR — BLOCK F

> Superseded operationally by Workflow Repair G. The Block-F command named
> `run --through close-node` compiled a plan but did not execute a close-node
> transition; its empty write set and constant zero-review field were shadow
> assertions, not a closed autonomous loop.

```yaml
status: DONE
block: F
closes:
  - WORKFLOW_BLOCK_F_UNIFIED_RUNTIME
  - WORKFLOW_CLOSURE_REFACTOR
opens: []
PX_RH_CLAIM: NOT_MADE
```

`orchestrator/workflow_runtime.py` is now the single documented stateless front
door for plan, run-through-node planning, phase close, and session close. It
calls the existing physical `goal_runtime.py` selector and the existing Block B
and C/D close entries; it does not create a second selector, policy kernel, or
durable runtime state.

Every plan includes the physical goal binding, exact registered tool slice,
derived-artifact status, close gates, addressable assembly/insight debt, empty
automatic write set, preserved foreign dirty paths, and hashes of Control,
TOOLS, and the dependency DAG. Missing/unavailable tools, selector ambiguity,
stale derived artifacts, and owner-only RH authority are explicit `HOLD`s.

The manifest registers the unified front door and both close routes. Existing
front doors remain callable, while `docs/Codex/README.md` points normal workflow
use to the unified entry.

W9 preflight (`ask.sh`) found no existing operational workflow runtime to reuse;
its matches were unrelated mathematical uses of “close/phase”. Four adversarial
plants cover three lifecycle closure shapes, host-independent logical plans,
fail-closed missing tools and stale artifacts, deterministic repeated plans,
foreign-dirty preservation, zero Proshka calls on ordinary close, and the ban on
automatic delivery or RH claims.

The final phase-close acceptance run also exposed a pre-existing macOS Bash 3.2
path-conversion defect in `check_arch_floor_quarantine.sh`: its escaped slash was
preserved literally. The portable parameter expansion now maps `Q3.Axioms` to
`Q3/Axioms.lean` on both registered hosts before the gate is rerun.
