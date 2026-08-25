# SOURCE RECORD — W5 full-endpoint value rate

```yaml
schema: q3_codex_source_record.v1
record_for: W5_FULL_ENDPOINT_VALUE_RATE
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5EndpointValueRate.lean
node_git_blob: 6d909c75ffceb7e51d90b031698bef35f46da275
parent_commit_at_record: 08cc086653b990b9e88d4659ba6593f4cc68c6d8
public_surface:
  - selectedFerrersAbelLogEndpointValues_rate_of_modeAndChiRates
conclusion: >-
  eventually both full-endpoint values of the additive-log representative are
  at most (96 + C1 + C2) / sqrt(lambda_k): the starred target coincides at the
  two window edges by the committed inversion, so one right-edge Gaussian
  bound pays both; the error bound evaluates to C1/sqrt(lambda) at the lower
  edge and better at the upper, and the center shadow to C2/sqrt(lambda).
private_reconstructions:
  - w5e_target_le_half_gaussian
  - w5e_gaussian_series_le_geometric
  - w5e_E_star_norm_le_of_one_le
  - w5e_fullEStarError_window_bound
  - w5e_center_bound
  - w5e_abelLimit_decomposition
reconstruction_reason: >-
  the analytic bricks live private in the L1 node whose frozen contract is one
  public theorem; local reconstruction is the pattern the W4 node already used
  for the W2 chain.
load_bearing_committed_suppliers:
  - E_star_explicitCCMLimitH_inv
  - selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
  - selectedFerrersExplicitTargetTail_bound
  - selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
conditionality: F72_6_MODE_AND_CHI_RATE_INPUTS
closes:
  - W5_FULL_ENDPOINT_VALUE_RATE
opens: []
route: CHALLENGER_NOT_RH
rh_claim: false
```
