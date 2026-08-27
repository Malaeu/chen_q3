# Arch-floor semantic quarantine v1

```yaml
document_class: SEMANTIC_QUARANTINE_RECEIPT
transaction: P4_ARCH_FLOOR_SEMANTIC_QUARANTINE_V1
date: 2026-08-27
unconditional_rh_proof: false
route_b_changed: false
definitions_changed: false
theorem_crosswalk_created: false
```

## Object boundary

The repository contains distinct objects that historical prose conflated:

| Object | Meaning | Status |
|---|---|---|
| `Q3.a_star` | raw scaled Archimedean kernel on `ℝ` | definition |
| `Q3.c_arch K` | `sInf` of the raw kernel on `[-K,K]` | definition |
| `Q3.c_star` | the number `11/10` | definition |
| `_root_.P_A` | periodized torus symbol | separate definition |
| `Q3.P_A` | alleged namespaced symbol | does not exist |

No theorem in the audited tree identifies `_root_.P_A` with `Q3.c_arch`, and
this transaction does not invent one.

## Source collision

`Q3/Axioms.lean` T1.3 proves only `Q3.a_star 0 > 0` and explicitly states
that `∀ ξ, Q3.a_star ξ > 0` is false for `|ξ| > 1`. Historical T1.6 prose then
claimed global positivity and used it to justify positivity of every compact
infimum. The later `c_star ≤ c_arch K` prose also transferred a torus-symbol
floor to the raw-kernel infimum without a theorem-level crosswalk.

The Clean surface contained the stronger explicit axiom
`Q3.Clean.a_star_pos : ∀ ξ, Q3.a_star ξ > 0`; it is therefore included in the
same quarantine rather than left as an apparently classical fact.

## Canonical conditional assumptions

```text
Q3.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption
Q3.Conditional.LegacyArchFloor.torusFloorLeRawKernelCompactInfAssumption
Q3.Clean.Conditional.LegacyArchFloor.rawKernelGlobalPosAssumption
Q3.Clean.Conditional.LegacyArchFloor.rawKernelCompactInfPosAssumption
```

The former names remain deprecated theorem aliases with the same types:

```text
Q3.c_arch_pos
Q3.c_star_le_c_arch
Q3.Clean.a_star_pos
Q3.Clean.c_arch_pos
```

The active `Q3/` consumers modified by this transaction use the explicit
conditional names. The aliases exist only for source compatibility. A term
that consumes one under `warningAsError` must fail with a deprecation error;
`#check` alone is not the deprecation plant because Lean does not emit that
warning for this command.

## Tracked consumer census

The full tracked `*.lean` scan distinguishes executable references from token
provenance embedded in historical output. No current consumer in the modified
`q3.lean.aristotle/Q3/` production slice uses a deprecated name.

| Deprecated token | Intentionally remaining tracked paths | Classification |
|---|---|---|
| `Q3.c_arch_pos` | `q3.lean.aristotle/A3_Bridge.lean`; `q3.lean.aristotle/AxiomsTheorems.lean`; `q3.lean.aristotle/CheckAxioms.lean`; `q3.lean.aristotle/Proofs/Q_nonneg_bridge.lean`; `q3.lean.aristotle/Proofs/Q_nonneg_on_atoms_integrated.lean` | pre-existing top-level compatibility copies outside the `Q3/` production slice; several have independent pre-existing build failures |
| `Q3.c_arch_pos` | `q3.lean.aristotle/archive/untracked_misc_2026-01-20/full/q3.lean.aristotle/archive/bridge_wip_2026-01-20/Q_Nonneg_Bridge.lean` | archive |
| `Q3.c_arch_pos`, `Q3.c_star_le_c_arch` | `q3.lean.aristotle/aristotle_output/Brange_Lipschitz_HeatProof_aristotle.lean`; `q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctx24.lean`; `q3.lean.aristotle/aristotle_output/prime_b_grid_pp_i19_pointwise_target_aristotle_ctxrootfix.lean` | immutable generated provenance strings, not Lean term consumers |
| `Q3.Clean.a_star_pos` | `q3.lean.aristotle/Proofs/Q_Lipschitz_bridge_v2.lean` | pre-existing lowercase compatibility copy outside the `Q3/` production slice; contains a pre-existing `sorry` |
| `Q3.Clean.a_star_pos` | `q3.lean.aristotle/archive/bridge_legacy_lowercase_2026-01-20/Q_Lipschitz_bridge.lean` | archive |
| `Q3.Clean.c_arch_pos` | none | no tracked consumer |

The qualified-name census is fail-closed in the validation script: any new path
or missing listed provenance path is drift. A second census fixes the exact
active-`Q3/` bare-name occurrences, including path, line, and source text, so
an added consumer inside a namespace or after an `open` declaration cannot
evade the qualified-token scan. Its allowlist also
contains legitimate same-spelling declarations such as the proved
`Q3.a_star_pos : Q3.a_star 0 > 0`; the set itself is checked exactly. The
top-level copies are recorded rather than silently edited because they are not
the current `Q3/` production modules and some already fail for unrelated
statement drift. P8 root-artifact classification must decide their eventual
physical disposition.

## Dependency boundary

The suspect assumptions are not in the current compiled broad-cone RH export
profile. The expected profile remains:

```text
[propext, Classical.choice, Q3.Weil_criterion,
 Q3.prime_term_le_at_t_critical_axiom, Quot.sound]
```

Quarantine therefore changes names and semantic visibility, not the truth
status of the repository and not Route B. It proves neither raw-kernel
positivity nor a torus-to-raw-kernel bridge.

## Validation contract

Run the dedicated fail-closed transaction gate from the repository root:

```bash
bash scripts/check_arch_floor_quarantine.sh
```

The gate performs all of the following:

- builds and directly checks all eight modified Lean modules;
- runs the unchanged standard `scripts/q3_check.sh` on the six non-axiom
  modules;
- treats the two axiom modules as an audited one-for-one rename transaction,
  checking exact whole-file content hashes, the four canonical assumption
  declarations, exact old/new Lean statement parity, and exact `#print axioms`
  parity; the whole-file hashes make this gate reproducible after commit and
  fail closed on any unrelated declaration or prose drift;
- checks that deprecated aliases fail through term consumption under
  `warningAsError`, while canonical names pass;
- under the explicit import `Q3.AxiomsTheorems`, checks that `_root_.P_A`
  exists and `Q3.P_A` does not;
- compares the current RH dependency profile exactly;
- verifies both the qualified tracked path census above and an exact
  active-`Q3/` bare-name occurrence census;
- requires a clean Route B proof subtree; unrelated control-plane drafts are
  outside this P4 claim and remain untouched.

The standard checker is not weakened. It correctly rejects unreviewed added
`axiom` lines; this dedicated gate adds the stronger semantic evidence needed
for the four explicit one-for-one assumption renames.

Success token:

```text
ARCH_FLOOR_SEMANTIC_QUARANTINE_VALID
```
