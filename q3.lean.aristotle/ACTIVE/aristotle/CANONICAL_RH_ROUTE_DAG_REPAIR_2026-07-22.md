# Canonical RH route DAG repair — 2026-07-22

Status: `CONDITIONAL_CANONICAL_ROOF_LEAN_LOCKED / NOT_RH`

## Result

The recovered Aristotle skeleton was not accepted as an RH proof.  Its false
universal supply shape has been replaced by the hole-free local module
`Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean`.

The corrected dependency chain is:

```text
one fixed canonical family Pstar
  + one parent cofinal path
  + one nested S2 extraction
  + H1 on Pstar
  + H2a certificates on that parent path
  + anchor and S1 on that same path
  + MontelAnchorGate
  + full Theorem510RealZeroBridge
  + S2 identification on the selected family
  -> generic Hurwitz zero transfer
  -> centeredXi zeros real
  -> Q3.RH
```

The final implication is the Lean theorem
`Q3.RouteB.CanonicalRHRoute.rh_of_canonical_slots`.  Its proof contains no
`sorry`, `admit`, or `exact?`.

## Firewall

- `H2aAt` does not imply real zeros by definition.
- The only H2a-to-H2b edge is the explicit contract
  `Theorem510RealZeroBridge`.
- The compiled plant `evenNonrealZeroPlant(z)=z^2+1` proves that evenness alone
  does not imply real zeros.
- `SoftSameCofinalSubsequence` materializes the Round-13 quantifier guard;
  S2 consumes `parent (extract k)`, not an independent diagonal.
- The file is a conditional roof.  It does not construct the exact
  `Mfin_(m,N)` certificates, prove the exact Theorem-5.10 factorization, or
  prove S1/S2.

## Validation

```text
lake env lean Q3/Proofs/RouteB/CanonicalRHRouteSkeleton.lean   PASS
lake build Q3.Proofs.RouteB.CanonicalRHRouteSkeleton          PASS
hard-hole scan                                                 CLEAN
unexpected axioms                                              NONE
```

Only standard Mathlib foundations reported by `#print axioms` remain:
`propext`, `Classical.choice`, and `Quot.sound`.

## Next Aristotle leaf

The first independent leaf is the local-domain Hurwitz zero-escape theorem in
`aristotle_input/routeb_hurwitz_zero_escape_2026_07_22.md`.  It removes the
temporary whole-plane strengthening in `SlotH1` and supports the intended
upper/lower half-strip roof.  Submission requires the owner's explicit OK on
the exact prompt.

Route B remains `CHALLENGER / NOT_RH`.  Bus 010 was not created.
