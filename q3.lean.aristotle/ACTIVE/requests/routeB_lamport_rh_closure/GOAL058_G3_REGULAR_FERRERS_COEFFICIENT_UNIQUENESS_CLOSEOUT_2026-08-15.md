# Goal 058 G3 — regular Ferrers coefficient uniqueness closeout

Date: 2026-08-15

Verdict:

```text
G3_CURRENT_REGULAR_SOLUTION_COEFFICIENT_UNIQUENESS_PROVED
G1_STATUS: OPEN
G3_STATUS: OPEN
ROUTE: CHALLENGER_NOT_RH
STOP_CODE: G3_UNIQUE_CURRENT_REGULAR_SOLUTION_TO_CLASSICAL_PSF_ZEROCOUNT_SOURCE_GAP
```

## Exact result

The new public theorem

```lean
mode4FerrersRegularEvenProlateSolution_coefficients_eq
```

proves that two
`Mode4FerrersRegularEvenProlateSolution mProject K Λ` objects have identical
coefficient rows whenever `2 ≤ mProject`.

The proof is source-free.  The exact three-term recurrence first makes the two
rows scalar multiples of one another.  Positivity of the stored zeroth
coefficients selects the positive scalar, and the common weighted unit
normalization forces its square, hence the scalar itself, to be one.

This removes ambiguity between multiple current packaged witnesses at fixed
`mProject`, `K`, and `Λ`.  It does not identify that current witness with an
external DLMF `Ps^0_{2p}`, and it does not prove an interior zero count.

## Evidence

- strict startup before the write: `P9_STRICT_PASS` at `7a4c07f0`;
- exact knowledge query: no hits;
- direct `lake env lean`: PASS;
- named target build: PASS, 7771 jobs;
- `scripts/q3_check.sh`: PASS;
- forbidden-token and `git diff --check` scans: PASS;
- public axiom surface: exactly
  `[propext, Classical.choice, Quot.sound]`;
- Lean file SHA-256:
  `236b82eb1eb86bac955ab6cc778ccab479b27e4135263a6d9ab494ba9db6d7dd`;
- scoped proof commit: `3ba54773`.

The post-commit strict startup correctly detected stale semantic and
cartographer receipts.  The canonical semantic refresh completed and strict
startup returned `P9_STRICT_PASS`; cartographer inventory was then regenerated
for the new declaration.

## External judgment boundary

The attached source-lock packet was byte-verified by Proshka at SHA-256
`377441ff72b40add5f4ee3c0ef101597b8589f6a7cd4fff2b9c5f89789d4463e`.
Proshka accepted the parameter shift `chi = Λ + G`, the degree map `n = 2p`,
and the bounded regular source class, but rejected treating the DLMF citation
as a Lean proof for the same witness.  Aristotle remained unauthorized at that
boundary.

The remaining source seam is one of the following honest kernel suppliers:

1. a singular Sturm oscillation theorem for the current regular class; or
2. an exact nonzero-scalar identity with a formal classical order-zero PSF
   carrier that already owns the `2p` zero count.

No desired zero-count binder, custom axiom, G1/G3 closure, Route promotion, or
RH claim is introduced by this closeout.
