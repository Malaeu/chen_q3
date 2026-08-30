# Goal 058 R2 moving Krylov/Feshbach closeout

Date: 2026-08-30
Status: `CLOSED_KILLED`
Operative class: `KILL_R2_MOVING_KRYLOV_FESHBACH`

## Source lock

- Request commit: `02e60cc4177e9ec45b3571dfd082253d20f12f92`
- Request path: `docs/routeB_bus/proshka/PROSHKA_REQUEST_GOAL058_R2_MOVING_KRYLOV_FESHBACH_DISCRIMINATOR_2026-08-29.txt`
- Request Git blob: `067dd5f70bca53b948003702de49aca13bde0102`
- Request SHA-256: `a746da60b5a6052a0e32d6341681d4848bb9c36b4a20b88c50a0f41271031e3f`
- Verdict commit: `81da25d6ed2675800bb72d6feaf1a42a1f292a03`
- Verdict Git blob: `beeffcd1ca7dd8f038f99a8e151d22e3fec021a5`
- Binding-repair commit: `034123539bb4a13c1aa5b902bcdd9ada1efc701c`
- Binding-repair Git blob: `4b740b8faf00d5c0f1af73c29d69e41de294d396`

The append-only repair supersedes only the incorrect request manifest in the
original verdict. The mathematical `KILL` is unchanged.

## Exact finding

On `r_i != 0`, the carrier

```text
U_i = span_C {q_i, r_i / ||r_i||}
```

is an honest exact two-dimensional Krylov space. Its outgoing coupling is the
second Lanczos residual

```text
c_i = (I - P_i) K_i (r_i / ||r_i||).
```

Hermiticity, unit normalization, `q_i ⟂ r_i`, and exact rank two do not bound
`||c_i||`. The planted Hermitian Jacobi chain makes the next coupling arbitrary.
No source theorem for the literal CCM family controls this coupling, and its
Feshbach consumer reimports the same complement inverse/floor debt.

## Ledger

```text
CLOSES:
  R2_MOVING_KRYLOV_ADMISSIBILITY_DISCRIMINATOR
  R2_VERDICT_REQUEST_BYTE_BINDING_MISMATCH

OPENS: []

REMAINS_OPEN:
  GOAL058_GROUND_TO_TRIAL_SAME_FAMILY_BRIDGE
```

No Lean execution was authorized or performed. No six-field phase-key change,
Route promotion, or RH claim occurred.

## Rerank

The stopped R2 carrier is not renamed or retried. The next cheapest allowed
discriminator returns to the unfinished primary R1 branch: source-audit whether
the exact same ground-family, normalized by a fixed compact `L²(K₀)` gauge, has
a source-backed whole-strip normality and cluster-identification theorem without
using the dead tracking rate or a wrong-family adapter.

