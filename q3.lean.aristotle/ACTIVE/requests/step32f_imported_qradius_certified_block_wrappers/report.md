# Step32F imported Q-radius certified-block wrappers report

## Status

Closed.

## Request

Close the receiver wiring from the imported Q-row radius payloads to the active
certified coefficient block constructors, while keeping all analytic enclosure
facts explicit as inputs.

## Declarations added

In `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`:

- `primaryK11CertifiedCoeffBlock_of_importedQRadius`
- `controlK9CertifiedCoeffBlock_of_importedQRadius`

Each wrapper consumes:

```text
base D/R matrix hboxes
+ imported Q-row hbox
+ Gram-radius dominance
+ D/R penalty-radius dominance
=> CertifiedCenteredBSplineCoeffBlock
```

## Files touched

- `Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_imported_qradius_certified_block_wrappers/report.md`

## Commands run

- `lake env lean Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean`
- `lake build Q3.Proofs.PSD_CenteredCoeffCertifiedBlockImport`
- `rg -n "sorr[y]|admi[t]" Q3/Proofs/PSD_CenteredCoeffCertifiedBlockImport.lean ACTIVE/requests/step32f_imported_qradius_certified_block_wrappers/report.md`
- `git diff --check`
- `lake build Q3.Main`
- `./scripts/check_axioms.sh`

## Compile status

Closed and verified.

- The edited active import file compiles with `lake env lean`.
- The focused module build passes.
- `Q3.Main` builds successfully.
- Focused hole scan found no proof holes.
- `git diff --check` passes.
- Axiom check passes with the expected profile:
  `3` standard Lean axioms and `2` documented project axioms.

## Remaining blocker

The remaining work is no longer this receiver wiring. It is the concrete
generated/numeric proof payload:

- base D/R matrix hboxes;
- Q-row hboxes against `primaryK11QRadius` and `controlK9QRadius`;
- Gram-radius dominance;
- final D/R penalty-radius dominance.

## Next smallest theorem

Add or import the concrete Q-row hbox facts for the active imported Q-radius
payloads, if those facts are already available from the generator.
