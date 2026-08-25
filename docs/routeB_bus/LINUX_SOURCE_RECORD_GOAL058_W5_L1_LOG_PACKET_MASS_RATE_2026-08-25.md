# SOURCE RECORD — W5 additive-log L1 packet mass rate

```yaml
schema: q3_codex_source_record.v1
record_for: W5_L1_LOG_PACKET_MASS_RATE
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersW5L1MassRate.lean
node_git_blob: 2151175e95b733c002cb56e8302ca78db143b2c5
parent_commit_at_record: ae0e33bf87a27dabf219a96a41a54679e657707c
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_W5_L1_LOG_PACKET_MASS_RATE_2026-08-25.md
public_surface:
  - selectedFerrersAbelLogZeroExtension_l1_rate_of_modeAndChiRates
conclusion: >-
  eventually, integral of the norm of the additive-log zero extension is at
  most B + A / sqrt(lambda_k) with A = 2*C1 + C2 assembled from the committed
  window error and center bounds, and
  B = 192 * exp(-pi/2) * (pi - 1/2)^(-1).
private_reconstructions:
  - explicitCCMLimitH_le_half_gaussian
  - gaussian_series_le_geometric
  - E_star_explicitCCMLimitH_norm_le_of_one_le
  - E_star_explicitCCMLimitH_norm_le_of_le_one
  - gaussian_tail_intervalIntegral_le
  - envelope_additive_bound
  - exp_decay_intervalIntegral_le
  - E_star_explicitCCMLimitH_additive_envelope
  - fullEStarError_window_bound
  - selectedPacket_center_bound
  - abelLimit_decomposition
  - exp_abs_intervalIntegral_le
  - exp_neg_half_intervalIntegral_le
  - exp_pos_half_intervalIntegral_le
  - rep_pointwise_bound
load_bearing_committed_suppliers:
  - E_star_explicitCCMLimitH_inv
  - selectedFerrersFullEStarError_eq_main_sub_targetTail
  - selectedFerrersEStarWindowMainError_bound_of_modeAndChiRates
  - selectedFerrersExplicitTargetTail_bound
  - selectedFerrers_factorFourPortPacketRate_of_modeAndChiRates
mechanism: >-
  exact E_star cancellation: the inversion symmetry folds the left window half
  onto the right, the half-Gaussian envelope turns into a plain decaying
  exponential in the additive coordinate, and no change of variables and no
  Poisson summation is used anywhere.
conditionality: F72_6_MODE_AND_CHI_RATE_INPUTS
closes:
  - W5_L1_LOG_PACKET_MASS_RATE
opens: []
route: CHALLENGER_NOT_RH
rh_claim: false
```
