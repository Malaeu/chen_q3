# CODEX DIRECTIVE — Route 058 P59 G2b

```yaml
DATE: 2026-08-12
ROUTE: CHALLENGER_NOT_RH
GOAL: 058
GATE: G2b
TARGET: Proposition59GroundLagrangeZeroSetBridge
BASE_HEAD: 5dcae17b467111eeb4d4b58fe63793e131fe146b
STATUS: EXECUTION_AUTHORIZED
```

Source contract: `058_realzero_ground_diagonal_to_xi.goal.md`,
`ROUTE058_GATE_CONTRACTS.md`, and §18 of
`proshka/PROSHKA_MASTER_ROUTE_REALZERO_GROUND_DIAGONAL_TO_XI_2026-08-11.md`.

## Name lock

The public CCM wrapper must consume the literal normalized supplier below. This line is
the name lock; suffix substitution is a contract failure.

```text
LAGRANGE_REAL_ZERO_SUPPLIER_NAME_LOCK: Q3.RouteB.ccmSourceLagrangePolynomial_complex_zerosRealOn_of_bottomRayleigh_simple_normalized
```

The wrapper may use local helper lemmas for the carrier equivalence, the Cauchy numerator
identity, and the zero-set split. It must nevertheless close its final G1-to-G2 call with
the exact name-locked declaration above. The adjacent `_simple` declaration, a generic
real-zero theorem, or an unqualified similarly named helper is not an admissible final
supplier.

## Execution contract

- Implement `Proposition59GroundLagrangeZeroSetBridge` in the `Q3.RouteB` namespace.
- Reuse the exact `CCMModeFinite N` row and transport it to the integer carrier
  `Finset.Icc (-(N : ℤ)) N`; do not introduce a second coefficient family.
- Preserve the coordinate `-L*z/(2*pi)`, including the minus sign and scale.
- Split included removable poles, exterior sine-lattice zeros, and off-lattice
  Lagrange zeros. Do not replace the split by scalar equality of the full transform and
  a finite polynomial.
- Keep every G1 input conditional. No finite-to-global promotion, route promotion, or
  RH claim is authorized.

## Validation

```text
lake env lean Q3/Proofs/RouteB/Proposition59GroundLagrangeZeroSetBridge.lean
lake build
#print axioms Q3.RouteB.Proposition59GroundLagrangeZeroSetBridge
```

Success code: `P59_GROUND_LAGRANGE_ZEROSET_BRIDGE_PROVED`.

Failure codes remain those in the source directive, including
`P59_CARRIER_EQUIV_GAP`, `P59_CAUCHY_NUMERATOR_IDENTITY_GAP`,
`P59_COMPLEX_SINE_ZERO_API_GAP`, `P59_LAGRANGE_SIGN_MISMATCH`,
`P59_LAGRANGE_SCALE_MISMATCH`, and `LEAN_BUILD_FAIL`.
