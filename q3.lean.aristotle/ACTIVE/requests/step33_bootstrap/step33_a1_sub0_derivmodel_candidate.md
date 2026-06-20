# Step33A.1-A Sub0 Derivative-Model Candidate

Fail-closed candidate.  This is not Lean proof data.

## Summary

- schema: `q3_psdpd_step33_a1_sub0_derivmodel_candidate.v1`
- status: `derivmodel_candidate_generated_crosswalk_unproved_not_proof_data`
- first danger point: `STEP33_A1_SUB0_DERIVMODEL_TO_RESIDUAL_DERIV_CROSSWALK_GAP`
- proof-safe closed fields: `0`
- Lean emitted: `False`

## Raw-Coefficient Equality Check

- raw equals residualfit: `True`
- raw equals derivfit: `True`
- residualfit equals derivfit: `True`
- meaning: `The existing derivfit candidate is still the raw-integrand Taylor polynomial coefficients, not the derivative-model coefficients consumed by modelDeriv.`

## Generated Model

- formula: `modelCoeff[i] = (i + 1) * rawCoeff[i + 1]`
- raw degree: `16`
- model degree: `15`
- model coeff count: `16`
- center: `5.000000000000000000E-2`
- radius: `5.000000000000000000E-2`
- modelBound formula: `sum_i abs(modelCoeff[i]) * radius^i`
- modelBound: `60128873212381686241540561835466089/327680000000000000000000000000000000`
- modelBound decimal: `0.183498758582707782719545`

## Missing Inputs

- `STEP33_A1_SUB0_DERIVMODEL_TO_RESIDUAL_DERIV_CROSSWALK_GAP`
- `STEP33_A1_SUB0_DERIVMODEL_LEAN_ARITHMETIC_EMISSION_GAP`

## Guard

- not Lean proof data
- does not use sampled derivative intervals as proof
- does not prove deriv cert.residual is modeled by this polynomial
- does not provide interpolationError
- existing derivfit raw coefficients remain diagnostic-only
