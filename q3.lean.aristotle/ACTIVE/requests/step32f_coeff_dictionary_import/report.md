# Step32F coefficient dictionary import report

## Request

Continue after the active primary/control LDL certificates and add the concrete
dictionary data needed by the centered coefficient analytic contract.

## Files touched

- `scripts/q3_psdpd_step32f_coeff_dictionary_lean_data.py`
- `Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean`
- `docs/INSIGHTS.md`
- `ACTIVE/requests/step32f_coeff_dictionary_import/report.md`

## Theorems and definitions added

- `PrimeShiftIndexL3`
- `activeL3Ell030Delta025CenterRatEntry`
- `activeL3Ell030Delta025Center`
- `activeL3PrimeBaseEntry`
- `activeL3PrimeExponentEntry`
- `activeL3PrimeBase`
- `activeL3PrimeExponent`
- `activeL3PrimeShift`
- `activeL3PrimeWeight`
- `CenteredCoeffDictionaryData`
- `activeL3Ell030Delta025DictionaryData`
- `primaryK11DictionaryData`
- `controlK9DictionaryData`
- `primaryK11_hk`
- `controlK9_hk`
- `primaryK11_hell`
- `controlK9_hell`
- `primaryK11CoeffAnalyticKernelContract`
- `primaryK11AnalyticC`
- `primaryK11AnalyticQ`
- `controlK9CoeffAnalyticKernelContract`
- `controlK9AnalyticC`
- `controlK9AnalyticQ`

## Commands run

```bash
./scripts/research_oracle.py query "Step22 midpoint generator center weight shift" -c q3_docs
./scripts/research_oracle.py query "centeredBSplineCoeffAnalyticKernelContract weight shift" -c q3_docs
./scripts/research_oracle.py query "CertifiedCenteredBSplineCoeffBlock center weight shift payload" -c q3_docs
python3 scripts/q3_psdpd_step32f_coeff_dictionary_lean_data.py
python3 -m py_compile scripts/q3_psdpd_step32f_coeff_dictionary_lean_data.py
lake env lean Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean
lake build Q3.Main
rg -n "sorry|admit|exact\\?" Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean scripts/q3_psdpd_step32f_coeff_dictionary_lean_data.py Q3/Proofs/PSD_CenteredCoeffPayloadImport.lean Q3/Proofs/PSD_CenteredCoeffPenaltyLDLImport.lean
git diff --check
./scripts/check_axioms.sh
```

## Compile status

`lake env lean Q3/Proofs/PSD_CenteredCoeffDictionaryImport.lean` passed.

`lake build Q3.Main` passed.

The focused hole scan found no `sorry`, `admit`, or `exact?` in the checked
files.

`git diff --check` passed.

`./scripts/check_axioms.sh` passed with the expected profile: 5 total axioms,
consisting of 3 standard Lean axioms and 2 documented project axioms.

## Result

The active coefficient payload now has a Lean-checked generator-side
dictionary:

- centers are the exact rational grid
  `u_i = -27/10 + i/4` for `i : Fin 23`;
- the finite prime dictionary has 98 entries for `r * log p <= 6`;
- shifts are represented analytically as `r * Real.log p`;
- weights are represented analytically as
  `Real.log p * Real.exp (-(r * Real.log p) / 2)`;
- concrete primary/control analytic contract aliases are available as
  `primaryK11CoeffAnalyticKernelContract` and
  `controlK9CoeffAnalyticKernelContract`.

## Does this instantiate `CertifiedCenteredBSplineCoeffBlock`?

Not yet, and this is intentional.

The current matrix payload import records exact rational midpoint matrices and
radius contracts.  Those midpoint matrices are not definitionally the same as
the analytic contract entries generated from `center/weight/shift`; for example,
the CSV boundary row stores decimal rational approximations of `exp(±u_i/2)`.

So the next bridge must be one of:

1. an interval/enclosure theorem from analytic contract entries to the imported
   midpoint/radius matrix boxes; or
2. a revised certified-block receiver that consumes the existing interval-box
   certificate instead of requiring definitional matrix equality.

## Remaining blocker

The next smallest node is the analytic-to-payload bridge:

```text
primaryK11AnalyticC/Q, controlK9AnalyticC/Q
  -> imported midpoint/radius payload boxes
  -> existing FinitePenaltyCert / certified block consumer
```

The dictionary layer is now present, so the remaining obstacle is no longer
missing `center/weight/shift` data.  It is the midpoint/radius-to-analytic
matrix bridge.
