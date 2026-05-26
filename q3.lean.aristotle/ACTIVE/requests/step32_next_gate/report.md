# Step32 Next Gate Report

Status: scalar-blocker-written
Date: 2026-05-26

## Current Gate

Generated Step21/Step22 entry hbox certificates for:

- `PrimaryK11BaseEntryHboxCert`
- `ControlK9BaseEntryHboxCert`
- `ActiveCenteredCoeffEntryHboxCert`

## Closed Prerequisites

- Matrix-identification bridge:
  `centeredBSplineCoeffWeilForm_eq_matrixSub_quadForm`
- Boundary row identification:
  `centeredBSplineBoundaryRows_identify_Q`
- Latest local Step32 bridge commit: `0cb3478c`

## Last Validation

Bootstrap created and validated against the current live gate:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Result: passed.

Prime entry bridge added and validated:

```bash
lake env lean Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
```

Result: passed.

## Execution Result

New Step32-local bridge module:

```text
Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
```

Lean-checked theorem added:

```lean
theorem primaryK11AnalyticP_entry (i j : CoeffIndex23) :
    primaryK11AnalyticP i j =
      centeredBSplineFinitePrimeKernelProfile
        11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
        (primaryK11Center j - primaryK11Center i)
```

The module also adds the control analogue and two receiver lemmas:

```lean
primaryK11AnalyticP_entry_hbox_of_profile_hbox
controlK9AnalyticP_entry_hbox_of_profile_hbox
```

These show that the active `matrixEntrywiseAbsLe` field follows immediately
once the finite prime profile has an entrywise scalar hbox.

No final hbox theorem was integrated in this run.  The current Lean file now
identifies the analytic `P` entries, but the actual scalar interval replay for
the 98-term finite prime profile is still absent.

Exact missing lemma family:

```lean
theorem primaryK11AnalyticA_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticA primaryK11A primaryK11ARadius

theorem primaryK11AnalyticP_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius

theorem primaryK11AnalyticP0_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP0 primaryK11P0 primaryK11P0Radius

theorem controlK9AnalyticA_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticA controlK9A controlK9ARadius

theorem controlK9AnalyticP_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP controlK9P controlK9PRadius

theorem controlK9AnalyticP0_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      controlK9AnalyticP0 controlK9P0 controlK9P0Radius
```

Smallest next theorem target:

```lean
primaryK11AnalyticP_entry_hbox
```

Why this one first: `PSD_CenteredCoeffPrimeDictionaryBoundsImport.lean` already
provides the dictionary-level positivity and `log p`/shift bound bridge needed
by a generated finite-prime hbox module.  The Arch `A` and continuous `P0`
hboxes require the heavier Step22 acb/tail and Step21 B-spline integral replay
layers.

Exact scalar certificate blocker:

```lean
theorem primaryK11FinitePrimeKernelProfile_entry_hbox :
    ∀ i j : CoeffIndex23,
      |centeredBSplineFinitePrimeKernelProfile
          11 primaryK11Ell primaryK11PrimeWeight primaryK11PrimeShift
          (primaryK11Center j - primaryK11Center i) -
        primaryK11P i j| ≤ primaryK11PRadius i j
```

With this exact theorem, the final hbox is one line:

```lean
theorem primaryK11AnalyticP_entry_hbox :
    Q3.Proofs.matrixEntrywiseAbsLe
      primaryK11AnalyticP primaryK11P primaryK11PRadius :=
  primaryK11AnalyticP_entry_hbox_of_profile_hbox
    primaryK11FinitePrimeKernelProfile_entry_hbox
```

Current helpers are insufficient for that scalar theorem:

- `activeL3PrimeLog_bounds_of_exp_bounds` and
  `activeL3PrimeShift_bounds_of_exp_bounds` bound `log p` and `r log p`.
- `centeredBSplineR_nonneg` only proves `0 ≤ centeredBSplineR k x`.
- There is no Lean replay yet that bounds/evaluates
  `centeredBSplineR 11 (((d) ± activeL3PrimeShift n) / primaryK11Ell)` and
  propagates those 98 weighted terms into the imported midpoint/radius
  entries.
- Therefore the missing object is the generated scalar interval replay for
  the finite prime profile, not another wrapper and not a PSD table.

Commands run:

```bash
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
rg -n "primaryK11AnalyticA|primaryK11AnalyticP|primaryK11AnalyticP0|controlK9AnalyticA|controlK9AnalyticP|controlK9AnalyticP0" q3.lean.aristotle/Q3 q3.lean.aristotle/scripts
./scripts/research_oracle.py query "Step32 EntryHbox matrixEntrywiseAbsLe A P P0" -c q3_docs
./scripts/research_oracle.py query "Step21 P0 interval Arb matrixEntrywiseAbsLe" -c q3_docs
./scripts/research_oracle.py query "Step22 Arch interval acb hbox A matrix" -c q3_docs
./scripts/research_oracle.py query "PrimeDictionaryBounds log exp hbox P matrix" -c q3_docs
lake env lean Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean
./scripts/research_oracle.py query "primaryK11AnalyticP_entry_hbox finite prime kernel scalar certificate" -c q3_docs
./scripts/research_oracle.py query "centeredBSplineFinitePrimeKernelProfile interval midpoint radius replay" -c q3_docs
./scripts/research_oracle.py query "Step21 Step22 prime side P matrix hbox Arb certificate" -c q3_docs
./scripts/research_oracle.py query "centeredBSplineR exact rational interval certificate Lean" -c q3_docs
```

Compile status:

- `Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean` passes through
  `scripts/q3_check.sh`.
- `Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean` passes direct Lean and
  `scripts/q3_check.sh`.
- No `sorry`, `exact?`, or `admit` appears in the active entry-hbox file.

Blocker status:

- Stop condition satisfied by exact scalar blocker report.
- Next action: generate
  `primaryK11FinitePrimeKernelProfile_entry_hbox`, then wrap it into
  `primaryK11AnalyticP_entry_hbox` using the compiled receiver.

## Next Update Format

- theorem added:
- files touched:
- commands run:
- compile status:
- blocker, if any:
