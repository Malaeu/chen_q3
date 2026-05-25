# Step32F penalty lower-bound parameter import report

## Status

Closed.

## Request

Continue the Step32F coefficient-payload lane after the finite penalty
lower-bound receiver.  The next step should stay honest: import the Step18
penalty parameters and expose exact lower-bound targets, without pretending
that the interval/SPD proof is already Lean-checked.

## Files touched

- `scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py`
- `Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_penalty_lower_bound_params_import/report.md`

## Theorems / definitions added

Generated Lean parameter layer:

```lean
primaryK11TauD
primaryK11TauR
primaryK11DFloor
primaryK11RFloor
primaryK11DFloor_pos
primaryK11RFloor_pos
primaryK11DLowerBound
primaryK11RLowerBound
primaryK11PenaltyLowerBoundCert_of_bounds
primaryK11FinitePenaltyCert_of_bounds

controlK9TauD
controlK9TauR
controlK9DFloor
controlK9RFloor
controlK9DFloor_pos
controlK9RFloor_pos
controlK9DLowerBound
controlK9RLowerBound
controlK9PenaltyLowerBoundCert_of_bounds
controlK9FinitePenaltyCert_of_bounds
```

## What changed

The new generator parses the accepted Step18 `best_tau` and `safe_lower`
values from the active certificate-family outputs and emits them as exact
rational Lean constants.

For each active block it exposes two remaining proof targets:

```lean
primaryK11DLowerBound
primaryK11RLowerBound
controlK9DLowerBound
controlK9RLowerBound
```

If those targets are proved, the generated adapters immediately produce:

```lean
FinitePenaltyLowerBoundCert D R Q
FinitePenaltyCert D R Q
```

## Why this is the right bridge

The previous node added the theorem-facing receiver
`FinitePenaltyLowerBoundCert`.  This node pins the active Step18 parameters to
that receiver:

```text
Step18 tau/safe_lower values
→ named Lean lower-bound propositions
→ FinitePenaltyLowerBoundCert.of_bounds adapters
→ FinitePenaltyCert
```

It still does not claim the lower bounds themselves.  The next checker must
prove the named propositions from exact rational matrix/SPD data.

## Commands run

```bash
./scripts/research_oracle.py query "FinitePenaltyLowerBoundCert interval SPD lower bound generator Lean rational LDL Cholesky" -c q3_docs
./scripts/research_oracle.py query "Step32F finite penalty lower-bound receiver checked interval SPD generator payload exact rational" -c q3_docs
./scripts/research_oracle.py query "PSD-pd active payload FinitePenaltyLowerBoundCert D penalty R penalty euclideanEnergy" -c q3_docs
./scripts/research_oracle.py query "verified finite matrix lower bound exact rational Gershgorin LDL Lean Step32" -c q3_docs
python3 scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
lake build Q3.Proofs.PSD_PenaltyCertificate
lake env lean Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean
lake build Q3.Proofs.PSD_CenteredCoeffPenaltyImport
lake build Q3.Main
rg -n "sorry|admit|exact\?" Q3/Proofs/PSD_CenteredCoeffPenaltyImport.lean Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean Q3/Proofs/PSD_PenaltyCertificate.lean scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py
./scripts/check_axioms.sh
git diff --check
```

## Compile status

`Q3.Proofs.PSD_CenteredCoeffPenaltyImport` builds successfully.

Full `Q3.Main` builds successfully.  Hole scan found no `sorry`, `admit`, or
`exact?` in the checked Step32 files and generator.  `./scripts/check_axioms.sh`
passed with the expected profile: 3 standard Lean axioms and 2 documented
project axioms.  `git diff --check` passed.

## Remaining blocker

The actual interval/SPD proof is still open.  The next smallest theorem is to
prove, for the primary block first:

```lean
primaryK11DLowerBound
primaryK11RLowerBound
```

using an exact rational checker route, likely LDL/SOS or another
kernel-checkable matrix lower-bound certificate.  A raw numerical safe lower
is not enough.
