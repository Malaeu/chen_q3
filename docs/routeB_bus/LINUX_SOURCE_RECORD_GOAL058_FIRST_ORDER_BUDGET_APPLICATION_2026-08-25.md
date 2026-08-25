# SOURCE RECORD — b1 application theorem to the production projection tail

```yaml
schema: q3_codex_source_record.v1
record_for: B1_EXPLICIT_PREANCHOR_TO_PRODUCTION_SOURCE_FAMILY_CONTRACT (application half)
body: LINUX_CLAUDE
node_path: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersFirstOrderBudgetApplication.lean
node_git_blob: f2b2f70a414d48c032b908362bebab56c42c83c3
parent_commit_at_record: 26d0449fdf3af68cbb4894b9e0a50078813faaff
authorizing_verdict: docs/routeB_bus/proshka/PROSHKA_VERDICT_GOAL058_POST_FIRST_ORDER_FAMILY_CROSSWALK_FORK_2026-08-25.md
public_surface:
  - SelectedFerrersPreAnchorProductionFamilyCrosswalk (def, the b1 owner contract)
  - selectedProjectionTailDecay_of_selectedFerrersFirstOrderBudget
private_reconstructions:
  - w5a_coeff_transport (subst-based index/trial transport, no schedule pun)
  - w5a_eStar_scale (E_star linearity in the packet, tsum_mul_left)
  - w5a_gTrial_eq_smul (production trial vector = scale^{-1} * EStarHm)
  - w5a_center_bound (clone of the private W5 center bound; H(0)=0)
  - w5a_paperLambda_one_le
conclusion: >-
  SelectedProjectionTailDecay S holds for any production S given: the explicit
  b1 family contract (eventual equality of selected index and trial), the
  F72.6 mode/chi rates, the open derivative-budget supplier hD, an eventual
  bound M on the inverse source scale, and SelectedPhysicalBandwidthCofinal.
  Final envelope constant: M * (Cb + Cp/(4*pi)) with Cb from the W5
  conditional assembly and Cp from the F72.6 center rate.
key_intermediate: >-
  The forbidden identifications are never used: the index/trial equalities
  enter only through subst at the application boundary, per the verdict.
conditionality:
  - SELECTED_FERRERS_PREANCHOR_PRODUCTION_FAMILY_CROSSWALK (hFamily, owner input)
  - F72_6_MODE_AND_CHI_RATE_INPUTS
  - W5_LOG_DERIVATIVE_BUDGET_BOUNDED (hD)
  - SOURCE_SCALE_INVERSE_BOUNDED (hScale, NEW named input — judge to adjudicate
    whether derivable from committed sources or joins the owner contract)
  - SELECTED_PHYSICAL_BANDWIDTH_COFINAL
closes:
  - PHYSICAL_ENERGY_SOURCE_SUPPLIER (as the b1-conditional chain)
  - ABEL_LIMIT_TO_GTRIAL_MIDPOINT_DELTA (fully consumed)
  - CENTER_VALUE_RATE (consumed via F72.6 at the origin)
opens:
  - SOURCE_SCALE_INVERSE_BOUNDED (one small named input)
kernel_run:
  command: lake build (targeted + full)
  result: Build completed successfully, LAKE_EXIT 0
  axioms: [propext, Classical.choice, Quot.sound]
  sorry: none
route: CHALLENGER_NOT_RH
rh_claim: false
```
