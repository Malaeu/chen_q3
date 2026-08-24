# Codex source record — W5 quantitative shifted-energy extraction

```yaml
schema: q3_codex_source_record.v1
date: 2026-08-25
branch: rh_clean
implementation_parent: 661a20a73dedff14031fa28b47669c59d6412f44
status: KERNEL_GREEN_AWAITING_INDEPENDENT_SEMANTIC_ADMISSION
node: W5_QUANTITATIVE_SHIFTED_ENERGY_EXTRACTION
route: CHALLENGER_NOT_RH
route_promotion: false
rh_claim: false
```

## Scoped source bytes

```yaml
q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersQuantitativeShiftedRootEnergy.lean:
  git_blob: 5205b76c962a01411dffbe6ded97bf2eaa6fd313
  sha256: 534e60bd431178d1556b10a17c3eafea344b6ad833fbb938e518a6d5c6218d52
  bytes: 11730
  lines: 267
  final_lf: true
```

## Result

The node exposes the exact W4 decay budget
`selectedFerrersAbelFourierDecayBudget k` and proves:

```text
selectedFerrersAbelLogZeroExtension_fourier_decay_quantitative
selectedFerrersAbelLimit_shiftedEnergy_le_majorant
```

The second theorem bounds the literal shifted Archimedean sesquilinear energy
of the production W3 Abel-limit vector by

```text
2 * (|log pi| + log 4 + 7)
  * selectedFerrersAbelFourierDecayBudget(k)^2
  * integral_R ((1 + log(2 + |t|))^2 / (1 + |t|)^2).
```

The last integral is proved finite and is independent of `k`.  Thus every
remaining cofinal dependence is isolated in the explicit packet `L1`,
derivative, and repaired jump ledgers.  No fixed-`k` finiteness is promoted to
a uniform estimate.

## Gates

```text
direct Lean: PASS
target build: PASS (7912 jobs)
q3_check: PASS
source scan: no sorry, admit, exact?, or native_decide
public axioms: [propext, Classical.choice, Quot.sound]
```

```text
CLOSES:
  W5_QUANTITATIVE_SHIFTED_ENERGY_EXTRACTION

OPENS:
  W5_COFINAL_PACKET_BUDGET_RATE
```

The node is kernel-green only.  Until independent semantic admission, it is
not consumed downstream.  It does not close W5, G3, G1, Route B, or RH.
