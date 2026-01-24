# ERS Summary (consolidated, legacy)

This file consolidates ERS-based analysis to avoid duplication.
It is **legacy** and not canonical for the current single-scale mainline.
Use only for historical context or when referencing old ERS graphs.

## Canonical mainline (do not confuse)

- Mainline uses single-scale `t_critical = 3/20`, `tau = 0`.
- Canonical status: `ACTIVE/chain_status.md`
- Canonical constants: `ACTIVE/SPECS_INDEX.md`

## Consolidated ERS sources (archived)

- `ACTIVE/spec_rh_q3_decomposition.md`
  - Full ERS graph, critical path, phases.
- `ACTIVE/spec_high_ers_constants.md`
  - ERS-ranked constants (t_sym, C_SB, M_0^{unif}, etc.).

## Why legacy

- ERS analysis is built on the two-scale/uniform branch (`t_sym`, `t_rkhs_cap`).
- The mainline moved to single-scale and τ=0; ERS ranking no longer tracks the
  current bottlenecks.

## When to use

- Historical audit of old uniform branch assumptions.
- If you explicitly compare old vs new critical paths.

## When NOT to use

- Do not use for current chain decisions or axiom list.
- Do not cite ERS-ranked constants as current blockers without checking
  `ACTIVE/orchestrator.md` and `ACTIVE/chain_status.md`.
