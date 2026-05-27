# Step32 Next Gate Report

Status: centered-bspline-r-blocker-written
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

Latest update: the same module now also exposes the primary 98-term summand
surface and a Lean-checked propagation theorem:

```lean
def primaryK11FinitePrimeProfileTerm
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real

theorem primaryK11FinitePrimeKernelProfile_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    ...
```

The final analytic hbox also has a direct term-level receiver:

```lean
theorem primaryK11AnalyticP_entry_hbox_of_term_hboxes
    (termMid termRad :
      CoeffIndex23 -> CoeffIndex23 -> PrimeShiftIndexL3 -> Real)
    ...
```

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

Exact scalar certificate blocker already reduced:

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

Exact missing `centeredBSplineR` interval replay lemma:

```lean
def primaryK11R11MinusMidRat : Nat -> Nat -> Nat -> Rat
def primaryK11R11MinusRadiusRat : Nat -> Nat -> Nat -> Rat
def primaryK11R11PlusMidRat : Nat -> Nat -> Nat -> Rat
def primaryK11R11PlusRadiusRat : Nat -> Nat -> Nat -> Rat

def primaryK11R11MinusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (primaryK11R11MinusMidRat i.val j.val n.val : Real)

def primaryK11R11MinusRadius
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (primaryK11R11MinusRadiusRat i.val j.val n.val : Real)

def primaryK11R11PlusMid
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (primaryK11R11PlusMidRat i.val j.val n.val : Real)

def primaryK11R11PlusRadius
    (i j : CoeffIndex23) (n : PrimeShiftIndexL3) : Real :=
  (primaryK11R11PlusRadiusRat i.val j.val n.val : Real)

theorem primaryK11CenteredBSplineR11PrimeShiftPair_hbox :
    ∀ i j : CoeffIndex23, ∀ n : PrimeShiftIndexL3,
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) -
            primaryK11PrimeShift n) / primaryK11Ell) -
        primaryK11R11MinusMid i j n| ≤
          primaryK11R11MinusRadius i j n ∧
      |centeredBSplineR 11
          (((primaryK11Center j - primaryK11Center i) +
            primaryK11PrimeShift n) / primaryK11Ell) -
        primaryK11R11PlusMid i j n| ≤
          primaryK11R11PlusRadius i j n
```

Why this is the exact next missing lemma: the compiled receiver
`primaryK11AnalyticP_entry_hbox_of_term_hboxes` already handles finite-sum
propagation once term midpoint/radius tables exist.  The remaining term hbox
proofs require the two `centeredBSplineR 11` enclosures above, plus the already
anticipated generated weight replay for
`primaryK11PrimeWeight n = log p * exp(-(r log p)/2)`.  The `centeredBSplineR`
tables are not present in the repo, and current Lean only has
`centeredBSplineR_nonneg`.

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
./scripts/research_oracle.py query "primaryK11FinitePrimeProfileTerm centeredBSplineR interval replay term hbox" -c q3_docs
./scripts/research_oracle.py query "centeredBSplineR 11 positivePartPower interval upper lower generated Lean" -c q3_docs
./scripts/research_oracle.py query "Step32 prime profile termMid termRad 98 prime shifts" -c q3_docs
./scripts/research_oracle.py query "B spline truncated power formula centeredCardinalBSpline certificate" -c q3_docs
```

Compile status:

- `Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean` passes through
  `scripts/q3_check.sh`.
- `Q3/Proofs/PSD_CenteredCoeffPrimeEntryHboxImport.lean` passes direct Lean and
  `scripts/q3_check.sh`.
- No `sorry`, `exact?`, or `admit` appears in the active entry-hbox file or
  the new prime-entry hbox module.

Blocker status:

- Stop condition satisfied by exact `centeredBSplineR` interval replay blocker
  report.
- Next action: generate
  `primaryK11CenteredBSplineR11PrimeShiftPair_hbox`, then use it with generated
  weight/term tables to discharge
  `primaryK11AnalyticP_entry_hbox_of_term_hboxes`.

## Next Update Format

- theorem added:
- files touched:
- commands run:
- compile status:
- blocker, if any:

## Update (2026-05-27) — Entry certificate downstream adapters

Status: downstream-entry-adapters-compiled

The active entry-hbox certificate now has named downstream adapters from the
already-existing certificate bundle to the finite certificate ledger and
directed-family handoff.

Theorem/definitions added in:

```text
Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

New finite-block adapters:

```lean
primaryK11FiniteBlock_of_entryHboxCert
controlK9FiniteBlock_of_entryHboxCert
primaryK11FiniteBlock_of_activeEntryHboxCert
controlK9FiniteBlock_of_activeEntryHboxCert
```

New directed-family adapters:

```lean
primaryK11SingletonDirectedCertFamily_of_entryHboxCert
controlK9SingletonDirectedCertFamily_of_entryHboxCert
primaryK11SingletonDirectedCertFamily_of_activeEntryHboxCert
controlK9SingletonDirectedCertFamily_of_activeEntryHboxCert
```

New finite analytic Weil nonnegativity wrappers:

```lean
primaryK11_weil_nonneg_on_analyticBoundary_of_entryHboxCert
controlK9_weil_nonneg_on_analyticBoundary_of_entryHboxCert
primaryK11_weil_nonneg_on_analyticBoundary_of_activeEntryHboxCert
controlK9_weil_nonneg_on_analyticBoundary_of_activeEntryHboxCert
```

Meaning: once the six real entry-hbox fields `hA`, `hP`, and `hP0` for
primary/control are supplied, the path to `CertifiedFiniteBlock`, singleton
`DirectedCertFamily`, and finite analytic Weil nonnegativity is now named and
Lean-checked in the active request file.

This does not close Step33A.1.  The first missing proof source remains:

```lean
primaryK11CenteredBSplineR11PrimeShiftPair_hbox
```

That lemma is still needed before the primary `P` field
`primaryK11AnalyticP_entry_hbox` can be assembled through the compiled
term/profile receivers.

Commands run:

```bash
lake env lean Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean
```

Compile status:

- direct Lean passes for `Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`;
- `scripts/q3_check.sh Q3/Proofs/PSD_CenteredCoeffEntryHboxImport.lean`
  passes;
- no `sorry`, `exact?`, or `admit` occurs in the touched Lean file.
