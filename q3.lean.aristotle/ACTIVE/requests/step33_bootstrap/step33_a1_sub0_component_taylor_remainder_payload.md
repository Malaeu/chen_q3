# Step33A.1-A sub0 component Taylor remainder payload

## Status

- schema: `q3_psdpd_step33_a1_sub0_component_taylor_remainder_payload.v2`
- status: `fail_closed_component_taylor_remainder_coarse_source_budget_killed`
- firstFailure: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL`
- proofGrade: `False`
- leanPayloadWritten: `False`
- target Lean file: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorRemainderPayload.lean`
- first theorem/object: `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated`
- transport theorem/object: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure_generated`

## Target expression

```text
primaryFiniteRow0Parent0Split100Sub0RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 45 ((1 : Rat) / 20) primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeff eta
```

- cell: `Set.Icc (0 : Real) ((1 : Real) / 10)`
- center: `1/20`
- assembledDegree: `45`
- required conclusion: `|targetExpression eta| <= ComponentPropagationRemainderAbs, then transport to ResidualTaylorRemainderAbs`

## Available inputs

### Coefficient assembly

- path: `ACTIVE/requests/step33_bootstrap/step33_a1_sub0_component_taylor_exact_assembly_certificate.json`
- schema: `q3_psdpd_step33_a1_sub0_component_taylor_exact_assembly_certificate.v1`
- status: `algebraic_assembly_payload_checked_remainder_source_open`
- firstFailure: `STEP33_A1_SUB0_SHAPESQ_DERIV_EXPLICIT_CAUCHY_ROWS_2_TO_15_ORDER16_GAP`
- assembledRawDerivCoeffLength: `46`
- residualTaylorCoeffLength: `46`
- algebraicAssemblyCrosswalkPassed: `True`
- componentTaylorProofsPresent: `False`
- residualTaylorRemainderAbs: `None`
- componentPropagationRemainderAbs: `None`

### Active-actual candidate

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`
- activeActualCenterJetRowsFilePresent: `True`
- activeActualFactorIntervalReceiverPresent: `True`
- activeActualProductRowIntervalsPresent: `True`
- activeActualCenterRowIntervalFromFactorRowsPresent: `True`
- sourceNormalFormActiveActualSourceIntervalValidPresent: `True`
- sourceIntervalCertToResidualIntervalPresent: `True`
- limitation: This is a source-model center-jet interval layer, not a whole-cell degree-45 component Taylor remainder proof.

### Coarse P45 source

- path: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`
- budgetSourcePath: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightProductSource.lean`
- budgetKillPath: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill.lean`
- sourceTheorem: `primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource`
- transportTheorem: `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure`
- budgetName: `primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`
- budgetKillTheorem: `primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail`
- sourceReady: `True`
- budgetKillReady: `True`
- spendableForStep33A1A: `False`
- limitation: This is a formal coarse P45 source and a formal negative budget comparison.  It is alive as source evidence, but not a closing Step33A.1-A certificate.

## Required rows

### R0_exact_degree45_assembly_coefficients

- status: `FORMAL_PAYLOAD_LIST_EQ_ONLY`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`
- notes: Lean list equalities materialize AssembledRawDerivCoeff and ResidualTaylorCoeff, but they do not bound the analytic component remainder.

### R1_active_actual_center_row_intervals

- status: `FORMAL_INPUT_CANDIDATE`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`
- notes: Rows are only center-jet row intervals for the activeActual source-model layer in degrees 0..15 after model subtraction. They are not yet the whole-cell bound for ActualComponent - P45(AssembledRawDerivCoeff).

### R2_direct_signed_component_remainder_rows

- status: `FORMAL_COARSE_SOURCE_PRESENT_BUDGET_KILLED`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`
- notes: A formal coarse P45 source exists for RawIntegrandDerivClosedForm eta - rawOmegaATaylorPolynomial 45 (1/20) AssembledRawDerivCoeff eta on Set.Icc 0 (1/10), bounded by primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget.  The local budget-kill file proves this coarse symmetric budget is too wide, so sharper signed rows are still missing for closure.

### R3_componentPropagationRemainderAbs

- status: `FORMAL_COARSE_CANDIDATE_BUDGET_KILLED`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`
- notes: The available candidate is primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget; it is formal, but not spendable as the final component remainder budget because the exact budget comparison fails.

### R4_residualTaylorRemainderAbs

- status: `FORMAL_COARSE_CANDIDATE_BUDGET_KILLED`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`
- notes: primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure transports the coarse source into the residual derivative enclosure, but it carries the same budget-killed coarse constant.

### R5_exact_rational_budget_comparison

- status: `FORMAL_FAIL_COARSE_SOURCE`
- artifact: `Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill.lean`
- notes: primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail proves the coarse source width exceeds the target interval width, so the first failure for the current local source is STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL.

## Why existing artifacts are not enough

- Exact coefficient assembly is algebraic and proof-checked as list equality, but it gives no analytic remainder bound.
- The activeActual rows are degree-0..15 source-model center-jet intervals after residual model subtraction; the requested component remainder is a whole-cell degree-45 error against AssembledRawDerivCoeff.
- The combined/source interval certificates route residual derivative intervals, but the current component ledger still has ComponentPropagationRemainderAbs and ResidualTaylorRemainderAbs set to null.
- primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource and primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure give a formal coarse P45 source, but primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail proves the carried coarse budget is too wide for the target residual interval.
- No local file currently defines the generated sharper objects primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated or primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure_generated; those names remain reserved until sharper signed rows and their exact budget comparison pass.

## Symbol inventory

### coefficientPayload

- `primaryFiniteRow0Parent0Split100Sub0AssembledRawDerivCoeffPayload`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`, line=`25`
- `primaryFiniteRow0Parent0Split100Sub0ResidualTaylorCoeffPayload`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`, line=`74`
- `primaryFiniteRow0Parent0Split100Sub0_assembledRawDerivCoeff_payload_eq`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`, line=`123`
- `primaryFiniteRow0Parent0Split100Sub0_residualTaylorCoeff_payload_eq`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`, line=`128`

### activeActualRows

- `primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowLower`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`, line=`898`
- `primaryFiniteRow0Parent0Split100Sub0ActiveActualCenterJetRowUpper`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`, line=`903`
- `primaryFiniteRow0Parent0Split100Sub0_activeActual_centerJet_row_interval_from_factor_rows`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`, line=`927`

### sourceNormalForm

- `primaryFiniteRow0Parent0Split100Sub0_combinedCancellation_sourceIntervalValid_of_activeActual_interval`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceNormalForm.lean`, line=`545`
- `theorem to_fullTaylor_residual_deriv_interval`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationSourceIntervalCert.lean`, line=`138`

### coarseP45Bridge

- `primaryFiniteRow0Parent0Split100Sub0_rawDerivClosedForm_tightAssembledSource`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`, line=`129`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_tight_enclosure`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`, line=`144`
- `primaryFiniteRow0Parent0Split100Sub0TightProductAssemblyErrorBudget`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightProductSource.lean`, line=`55`
- `primaryFiniteRow0Parent0Split100Sub0_tightProductAssemblyErrorBudget_width_fail`: exists=`True`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorTightBudgetKill.lean`, line=`30`

### missingGeneratedTarget

- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated`: exists=`False`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorCoeffAssemblyPayload.lean`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated`: exists=`False`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaACombinedCancellationActiveActualCenterJetRowsPayload.lean`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_componentTaylor_remainder_source_generated`: exists=`False`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`, line=`None`
- `primaryFiniteRow0Parent0Split100Sub0_fullTaylor_residual_deriv_taylor_enclosure_generated`: exists=`False`, file=`Q3/Proofs/PSD_CenteredCoeffRawOmegaAComponentTaylorP45Bridge.lean`, line=`None`

## Next implementable patch

- action: `build_sharper_component_taylor_remainder_interval_generator`
- ifRowsMissing: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_SHARPER_SIGNED_ROW_SOURCE_GAP`
- ifBudgetFalse: `STEP33_A1_SUB0_COMPONENT_TAYLOR_REMAINDER_BUDGET_CONSTANT_FAIL`
- description: Generate sharper rational/interval signed rows for the exact target expression, compute a smaller ComponentPropagationRemainderAbs plus ResidualTaylorRemainderAbs, and keep Lean output disabled until all rows and the exact rational budget comparison pass.
