# TOOLS.md — generated map of the repo's instruments

> **GENERATED FILE — do not edit by hand.** Regenerate with `./orchestrator/tools_census.py --markdown`.

> Written because hand-maintained maps rot: MAP.md drifted two days, the frozen atlases two months, and `aristotle_proofs.db` covered 31% of RouteB.

## Summary

- **Permanent tools:** 367 (touched since 2026-07-01: 22)
- **One-shot probes** (goal-local experiment log, not tooling): 159
- **Databases:** 1
- **Ledgers** (accumulating journals, any format): 25
- **State files** (json/yaml/csv > 2 KB, not journals): 511
- Alive tools referenced by nothing (**orphans**): 1
- Alive tools not mentioned in any rule file: 18

## Databases

| Path | Last commit | Refs | In rules |
|---|---|---|---|
| `q3.lean.aristotle/aristotle_db/aristotle_proofs.db` | 2026-08-05 | 18 | yes |

## Ledgers — accumulating journals ("have we already tried this?")

25 journals, **6 alive** / 19 frozen. A frozen ledger that is still cited as current is the project's recurring failure mode: it does not lie, it just stops answering.

### Alive

| Ledger | Entries | Last commit | In rules |
|---|---|---|---|
| `q3.lean.aristotle/docs/INSIGHTS.md` | 1673 | 2026-08-05 | yes |
| `q3.lean.aristotle/ACTIVE/requests/routeB_twolevel_spectral_ladder/ROUTE_B_STATE.md` | 72 | 2026-08-04 | yes |
| `q3.lean.aristotle/ACTIVE/PHASE_MONITOR.md` | 30 | 2026-07-28 | yes |
| `q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` | 23 | 2026-07-10 | yes |
| `q3.lean.aristotle/ACTIVE/pipeline/PROSHKA_REASONING_TIME_LOG.md` | 15 | 2026-08-05 | **NO** |
| `q3.lean.aristotle/ACTIVE/requests/routeB_lamport_rh_closure/MUNTZ_V3_CONSUMPTION_LEDGER.md` | 5 | 2026-08-03 | **NO** |

### Frozen (still on disk, often still cited)

| Ledger | Entries | Last commit |
|---|---|---|
| `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/report.md` | 865 | 2026-06-25 |
| `q3.lean.aristotle/ACTIVE/PSD_STEP33_MONITOR.md` | 817 | 2026-06-25 |
| `q3.lean.aristotle/ACTIVE/requests/step33_bootstrap/node.md` | 434 | 2026-06-24 |
| `docs/trackB/CHECKPOINTS.md` | 23 | 2026-06-14 |
| `docs/Progress_Log.md` | 2 | 2026-03-07 |
| `session_exports/chat_latest.md` | 769 | 2026-02-12 |
| `q3.lean.aristotle/KB/archive/orchestrator_legacy_snapshot_2026-02-08.md` | 27 | 2026-02-08 |
| `q3.lean.aristotle/ACTIVE/insights.md` | 1673 | 2026-01-29 |
| `docs/links/quillen_working_papers.json` | 491 | 2026-01-29 |
| `docs/mac_24_01_2026_13_22.md` | 216 | 2026-01-29 |
| `docs/links/quillen_working_papers_1999_2003.json` | 87 | 2026-01-29 |
| `q3.lean.aristotle/PROSHKA_CONTEXT_SINGLE_SCALE_2026_01_24.md` | 27 | 2026-01-29 |
| `q3.lean.aristotle/aristotle_output/proshka_context_floor_tcritical.md` | 27 | 2026-01-29 |
| `q3.lean.aristotle/aristotle_output/proshka_floor_tcritical_bundle_2026_01_24.md` | 27 | 2026-01-29 |
| `q3.lean.aristotle/aristotle_output/proshka_floor_cert_tcritical_bundle_2026_01_25.md` | 27 | 2026-01-29 |
| `q3.lean.aristotle/ACTIVE/aristotle/proshka_context_single_scale.md` | 27 | 2026-01-29 |
| `q3.lean.aristotle/docs/legacy/full_snapshot_2026_01_16/q3.lean.aristotle/PROJECT_ORCHESTRATOR.md` | 23 | 2026-01-29 |
| `q3.lean.aristotle/ACTIVE/orchestrator.md` | 23 | 2026-01-29 |
| `docs/CHANGELOG_AUTO.md` | 10 | 2026-01-20 |

## Permanent tools, most recently touched first

| Tool | Last | Refs | In rules | Purpose |
|---|---|---|---|---|
| `orchestrator/tools_census.py` | 2026-08-05 | 2 | **NO** | Machine census of every tool, database and state file in the repo. |
| `q3.lean.aristotle/scripts/s2_l2b_mellin_zero_scan.py` | 2026-08-05 | 1 | **NO** | S2-L2b discriminator: do v3-class windows have Mellin zeros INSIDE the open strip? |
| `q3.lean.aristotle/scripts/ccm_h2a_gap_scan.py` | 2026-08-04 | 1 | **NO** | CCM H2a Layer-3 gap-scan discriminator (FIT_NOT_LAW, binary64, NOT proof tree). |
| `q3.lean.aristotle/scripts/ccm_h2a_sector_cell_13_2_arb.py` | 2026-08-04 | 5 | **NO** | Rigorous Arb certificate for the CCM H2a sector cell ``(13, 2)``. |
| `docs/routeB_bus/litreview/litreview_check.py` | 2026-08-03 | 4 | **NO** | litreview validator — chain-of-evidence check for the citation ledger. |
| `docs/routeB_bus/litreview/zotero_pull.py` | 2026-08-03 | 6 | **NO** | Zotero live-sync — pull the RH collections from the local Zotero HTTP API. |
| `orchestrator/packet.py` | 2026-07-31 | 8 | yes | Clipboard-native packet transport for the Route B orchestration bus. |
| `orchestrator/spine.py` | 2026-07-31 | 33 | yes | Knowledge Spine aggregator (adapter pattern, read-only over sources). |
| `orchestrator/codex_app.sh` | 2026-07-30 | 4 | **NO** | Codex.app lane — drive the desktop Codex through its GUI. |
| `orchestrator/desktop_app.sh` | 2026-07-30 | 4 | **NO** | Desktop lane — drive Codex.app and Claude Desktop through their GUI. |
| `orchestrator/relay.py` | 2026-07-30 | 1 | yes | RELAY lane — the conductor's transport. |
| `orchestrator/sense.py` | 2026-07-30 | 0 | yes | SENSE lane — read-only phase detection for the Route B conductor. |
| `docs/routeB_bus/check_full_window_positive_part_certificate.py` | 2026-07-29 | 15 | **NO** | Independent stdlib-only checker for RouteB.033. |
| `docs/routeB_bus/check_priority_band_positive_part_certificate.py` | 2026-07-29 | 13 | **NO** | Independent stdlib-only checker for RouteB.031. |
| `docs/routeB_bus/full_window_positive_part_certificate.py` | 2026-07-29 | 17 | **NO** | Build the RouteB.033 full-window positive-part certificate. |
| `docs/routeB_bus/priority_band_positive_part_certificate.py` | 2026-07-29 | 19 | **NO** | Build the exact-data certificate for RouteB.031. |
| `docs/routeB_bus/check_coupled_full_sum_response_certificate.py` | 2026-07-28 | 13 | **NO** | Independent exact checker for the RouteB.030 certificate. |
| `docs/routeB_bus/check_decisive_finite_core_theta_k_escalation.py` | 2026-07-28 | 14 | **NO** | Independent exact checker for goal 029 decisive K escalation. |
| `docs/routeB_bus/check_finite_core_theta_certificate.py` | 2026-07-28 | 16 | **NO** | Independent exact-rational checker for FINITE_CORE_THETA_CERT.json. |
| `docs/routeB_bus/coupled_full_sum_response_certificate.py` | 2026-07-28 | 25 | **NO** | Goal 030: coupled response-weighted full-sum certificate. |
| `docs/routeB_bus/decisive_finite_core_theta_k_escalation.py` | 2026-07-28 | 9 | **NO** | Goal 029: decisive two-cut finite-core theta escalation. |
| `docs/routeB_bus/finite_core_theta_certificate.py` | 2026-07-28 | 9 | **NO** | Exact rational certificate generator for Route-B goal 028. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_active_actual_horner_row_source.py` | 2026-06-25 | 16 | **NO** | Fail-closed ledger for active-actual order-16 Horner row sources. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_active_actual_order16_horner_payload.py` | 2026-06-25 | 50 | **NO** | Fail-closed activeActual order-16 Horner payload entrypoint. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_direct_signed_segment0.py` | 2026-06-25 | 13 | **NO** | Fail-closed segment0 Taylor-model gate for the direct signed source. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_direct_signed_source_rows.py` | 2026-06-25 | 12 | **NO** | Fail-closed gatekeeper for direct collapsed degree-0 signed-source rows. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_point_slope_rat_audit.py` | 2026-06-25 | 3 | **NO** | Fail-closed audit for the collapsed degree-0 Rat point-row budget gate. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_point_slope_rat_payload.py` | 2026-06-25 | 6 | **NO** | Audit the collapsed degree-0 point-slope Rat payload. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_point_slope_rows.py` | 2026-06-25 | 10 | **NO** | Fail-closed audit for collapsed degree-0 point-slope rows. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_payload.py` | 2026-06-25 | 0 | **NO** | Ledger for the first collapsed degree-0 raw-D17 signed-factor payload. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_raw_d17_signed_factor_segments.py` | 2026-06-25 | 17 | **NO** | Audit for the two-segment collapsed degree-0 raw-D17 signed-factor route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_collapsed_degree0_signed_source.py` | 2026-06-25 | 53 | **NO** | Fail-closed ledger for the collapsed degree-0 signed source route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_cancellation_interval_certificate.py` | 2026-06-25 | 31 | **NO** | Fail-closed combined cancellation high-order certificate ledger. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_certificate.py` | 2026-06-25 | 66 | **NO** | Fail-closed preflight for the direct scaled-remainder certificate. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_direct_payload.py` | 2026-06-25 | 108 | **NO** | Fail-closed ledger for the direct nonzero-model scaled-remainder payload. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_scaled_remainder_whole_expression_pilot.py` | 2026-06-25 | 12 | **NO** | Fail-closed source-data gate for the Step33A.1-A whole-expression pilot. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_component_taylor_remainder_payload.py` | 2026-06-25 | 2 | **NO** | Fail-closed Step33A.1-A sub0 component Taylor remainder ledger. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_component_taylor_residual_payload.py` | 2026-06-25 | 44 | **NO** | Fail-closed component Taylor residual payload for Step33A.1-A sub0. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_raw_d17_sharp_local_center_jets18.py` | 2026-06-25 | 8 | **NO** | Fail-closed audit for sharp raw-D17 local center-jet rows. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_omega_prime_order17_payload.py` | 2026-06-24 | 7 | **NO** | OmegaPrime order-17 rational payload ledger for Step33A.1-A sub0. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_biased_residual_horner_payload.py` | 2026-06-23 | 21 | **NO** | Fail-closed ledger for the biased residual-Horner family payload route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_biased_residual_local_model_segments.py` | 2026-06-23 | 5 | **NO** | Fail-closed ledger for the biased residual local-model segment route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_biased_residual_signed_factor_segments.py` | 2026-06-23 | 6 | **NO** | Fail-closed ledger for the biased residual signed-factor segment route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_biased_residual_source_horner_cert.py` | 2026-06-23 | 5 | **NO** | Fail-closed ledger for the biased residual source-Horner family route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_cancellation_order16_direct_payload.py` | 2026-06-23 | 6 | **NO** | Fail-closed ledger for the Step33A.1-A direct order-16 payload. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_biased_scaled_remainder_interval.py` | 2026-06-23 | 9 | **NO** | Fail-closed ledger for the biased scaled-remainder interval route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_signed_factor_rows.py` | 2026-06-23 | 0 | **NO** | Fail-closed ledger for the Step33A.1-A order-16 signed-factor route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_combined_order16_source_interval.py` | 2026-06-23 | 0 | **NO** | Fail-closed ledger for the Step33A.1-A direct order-16 source interval route. |
| `q3.lean.aristotle/scripts/certify_step33_a1_sub0_existing_pi_scale_budget.py` | 2026-06-22 | 4 | **NO** | Exact rational audit for the Step33A.1-A existing-pi scale route. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_component_assembly_stream_ledger.py` | 2026-06-22 | 43 | **NO** | Fail-closed component assembly coefficient-stream ledger. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_component_taylor_exact_assembly_certificate.py` | 2026-06-22 | 1 | **NO** | Proof-side coefficient materialization for Step33A.1-A sub0. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_realsinc_derivative_payload.py` | 2026-06-22 | 11 | **NO** | Fail-closed realSinc derivative majorant payload for Step33A.1-A sub0. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_shapesq_deriv_tight_payload.py` | 2026-06-22 | 6 | **NO** | Fail-closed audit for the Step33A.1-A Sub0 tight ShapeSqDeriv payload. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_cancellation_residual_interval_certificate.py` | 2026-06-21 | 4 | **NO** | Fail-closed cancellation-preserving residual interval certificate ledger. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_omega_prime_taylor_payload.py` | 2026-06-21 | 87 | **NO** | Fail-closed OmegaPrime Taylor payload for Step33A.1-A sub0. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_anchor_abs_second_deriv_payload.py` | 2026-06-20 | 8 | **NO** | Fail-closed Step33A.1-A sub0 anchor/second-derivative payload audit. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_asymmetric_anchor_curvature_payload.py` | 2026-06-20 | 5 | **NO** | Fail-closed Step33A.1-A sub0 asymmetric anchor/curvature audit. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_residual_deriv_interpolation_payload.py` | 2026-06-20 | 39 | **NO** | Fail-closed Step33A.1-A sub0 residual-derivative interpolation skeleton. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_residual_derivmodel_candidate.py` | 2026-06-20 | 9 | **NO** | Generate the Step33A.1-A sub0 derivative-model candidate, fail closed. |
| `q3.lean.aristotle/scripts/generate_step33_a1_sub0_segmented_residual_deriv_interval_payload.py` | 2026-06-20 | 17 | **NO** | Fail-closed segmented residual-derivative certificate contract for Step33A.1-A. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_direct_proof_input_worklist.py` | 2026-06-20 | 96 | **NO** | Build the direct proof-input worklist for covered refined subchunks. |
| `scripts/trackb_interval_worklist_rationalize.py` | 2026-06-14 | 2 | **NO** | Track B / E5p dyadic rational guard verifier for interval worklists. |
| `scripts/trackb_nonnode_cell_sweep.py` | 2026-06-14 | 3 | **NO** | Track B / E5p compact multi-cell sweep for the non-node interval guard. |
| `scripts/trackb_nonnode_interval_atom_audit.py` | 2026-06-14 | 13 | **NO** | Track B / E5p non-node interval-atom audit. |
| `scripts/trackb_nonnode_refine_failures.py` | 2026-06-14 | 2 | **NO** | Track B / E5p adaptive refinement probe for non-node interval guard failures. |
| `scripts/trackb_raw_edge_interval_cert.py` | 2026-06-14 | 8 | **NO** | Track B / E5p raw-edge interval penalty certificate generator. |
| `q3.lean.aristotle/scripts/q3_psdpd_step21_p0_piecewise_manifest.py` | 2026-06-12 | 58 | **NO** | Exact piecewise-polynomial manifest for the Step21 P0 backend. |
| `q3.lean.aristotle/scripts/q3_psdpd_step22_arch_interval.py` | 2026-06-12 | 26 | **NO** | Step 22 PSD-pd Arch interval patcher. |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_coeff_payload_lean_data.py` | 2026-06-12 | 15 | **NO** | Generate the checked Lean data layer for the active Step 32F coefficient blocks. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_base_hbox_lean.py` | 2026-06-12 | 13 | **NO** | Generate the Step33 A base-hbox receiver layer. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_canonical_decision_audit.py` | 2026-06-12 | 0 | **NO** | Step33A.1-A canonical A decision audit. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_cos_seed.py` | 2026-06-12 | 10 | **NO** | Seed universal cosine-envelope proofs for the Step33 A Taylor payload. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_geometry_seed.py` | 2026-06-12 | 8 | **NO** | Add deterministic chunk geometry fields to the Step33 A proof-data seed. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_inventory.py` | 2026-06-12 | 49 | **NO** | Inventory the missing proof-data layer for Step33 raw-Omega A PayloadFin. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_lean.py` | 2026-06-12 | 39 | **NO** | Guard and future Lean emitter for Step33 raw-Omega A Taylor payloads. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_omega_log_seed.py` | 2026-06-12 | 1 | **NO** | Seed Step33 raw-Omega Taylor payload Omega bounds after the first chunk. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_omega_small_seed.py` | 2026-06-12 | 0 | **NO** | Fill the first finite raw-Omega chunk with the checked compact bound. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_polynomial_radius_seed.py` | 2026-06-12 | 4 | **NO** | Seed direct polynomial value bounds from Taylor coeff/radius data. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_product_abs_seed.py` | 2026-06-12 | 1 | **NO** | Seed direct symmetric product bounds for the Step33 A Taylor payload. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_proof_data_skeleton.py` | 2026-06-12 | 21 | **NO** | Emit the Step33 raw-Omega A Taylor proof-data skeleton. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_row_sum_seed.py` | 2026-06-12 | 7 | **NO** | Add row-sum arithmetic proof-term candidates to the Step33 A proof-data seed. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_row_sum_target_refresh.py` | 2026-06-12 | 3 | **NO** | Build a local target-refresh audit from serialized row-sum proof data. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_scale_seed.py` | 2026-06-12 | 13 | **NO** | Seed shared scale interval proofs for the Step33 A Taylor payload. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_chunk_taylor_payload_shape_seed.py` | 2026-06-12 | 2 | **NO** | Seed structural shape-square bounds for the Step33 A Taylor payload. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_coordinate_invariant_audit.py` | 2026-06-12 | 3 | **NO** | Coordinate-invariant audit for the Step33A Arch A semantic fork. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_data_convention_sync_dry_run.py` | 2026-06-12 | 1 | **NO** | Step33A A data-convention sync dry-run. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_distance_payload_worklist.py` | 2026-06-12 | 52 | **NO** | Build the Step33A.1-A raw-Omega distance-payload worklist. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_finite_tail_arithmetic_lean.py` | 2026-06-12 | 22 | **NO** | Generate Lean arithmetic checks for Step33 A finite/tail payload data. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_local_slack_recenter_audit.py` | 2026-06-12 | 6 | **NO** | Audit local A-window slack against the existing imported A radii. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_margin_ledger.py` | 2026-06-12 | 10 | **NO** | Build the Step33A.1-A margin ledger. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_omega_closed_form_endpoint_contract.py` | 2026-06-12 | 58 | **NO** | Fail-closed contract for Step33A.1-A Omega closed-form endpoint rows. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_omega_first_row_feasibility_audit.py` | 2026-06-12 | 33 | **NO** | Feasibility audit for the first Step33A.1-A Omega direct-anchor row. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_pointwise_route_diagnostic.py` | 2026-06-12 | 4 | **NO** | Diagnostic for the Step33A Arch A pointwise-constant chunk route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_component_value_contract.py` | 2026-06-12 | 4 | **NO** | Audit the refined subchunk ComponentValue proof contract. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_grid_width_accounting.py` | 2026-06-12 | 0 | **NO** | Account sampled refined-grid Taylor/model row widths against row targets. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_interval_residual_route_audit.py` | 2026-06-12 | 5 | **NO** | Audit direct Arb interval residual enclosure for refined subchunks. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_row_recenter_containment_audit.py` | 2026-06-12 | 4 | **NO** | Audit refreshed refined-row A recenter containment. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_row_sum_worklist.py` | 2026-06-12 | 10 | **NO** | Build the refined exact-sum row obligation worklist. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_row_target_refresh_audit.py` | 2026-06-12 | 5 | **NO** | Aggregate row-target refresh accounting for refined-subchunk candidates. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_candidate_coverage.py` | 2026-06-12 | 13 | **NO** | Audit candidate-overlay coverage for the refined raw-Omega subchunk route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_candidate_overlay.py` | 2026-06-12 | 5 | **NO** | Build a fail-closed refined-subchunk candidate overlay from a full probe. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_candidate_seed_audit.py` | 2026-06-12 | 4 | **NO** | Audit seedable proof-data values from selected refined-subchunk candidates. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_component_endpoint_worklist.py` | 2026-06-12 | 20 | **NO** | Build endpoint interval obligations for the v19 endpoint receiver. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_derivative_bound_audit.py` | 2026-06-12 | 24 | **NO** | Audit derivative residual bounds for refined subchunk candidates. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_derivative_remainder_refresh.py` | 2026-06-12 | 4 | **NO** | Refresh refined-subchunk remainders to derivative-envelope requirements. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_direct_derivative_overlay.py` | 2026-06-12 | 105 | **NO** | Seed a direct residual-derivative overlay for the pilot route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_direct_receiver_feasibility_audit.py` | 2026-06-12 | 5 | **NO** | Audit whether current direct subchunks can feed the preferred receivers. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_endpoint_lean_emitter.py` | 2026-06-12 | 21 | **NO** | Fail-closed Lean emitter report for Step33A.1-A endpoint cert rows. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_endpoint_rational_lean.py` | 2026-06-12 | 228 | **NO** | Emit proof-safe rational endpoint certs for Step33A.1-A refined rows. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_hraw_center_coeff_contract.py` | 2026-06-12 | 62 | **NO** | Build the local-component proof-input contract for hRawCenterCoeffAbs. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_payload_lean.py` | 2026-06-12 | 183 | **NO** | Guarded Lean emitter report for refined raw-Omega subchunk payloads. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_pilot_overlay.py` | 2026-06-12 | 3 | **NO** | Seed the first v10 refined-subchunk proof-data pilot overlay. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_probe_seed_audit.py` | 2026-06-12 | 5 | **NO** | Fail-closed audit for mapping Taylor probe output into refined proof data. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_proof_data_skeleton.py` | 2026-06-12 | 71 | **NO** | Emit a fail-closed refined-subchunk proof-data skeleton. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_rational_residual_audit.py` | 2026-06-12 | 9 | **NO** | Sampled residual audit for refined rational polynomial candidates. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_raw_center_coeff_value_bounds_worklist.py` | 2026-06-12 | 15 | **NO** | Build the raw-center-coeff value-bounds worklist for refined subchunks. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_remainder_refresh.py` | 2026-06-12 | 4 | **NO** | Refresh refined-subchunk candidate remainders from a residual audit. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_remainder_slack_audit.py` | 2026-06-12 | 3 | **NO** | Audit remainder slack against parent and row bounds for refined candidates. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_refined_subchunk_worklist.py` | 2026-06-12 | 9 | **NO** | Build the refined-subchunk worklist for Step33 raw-Omega Taylor payloads. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_signed_chunk_payload_contract.py` | 2026-06-12 | 62 | **NO** | Build the Step33A.1-A signed chunked comparison-integral contract. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_source_convention_audit.py` | 2026-06-12 | 3 | **NO** | Step33A A-source convention audit. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_source_normalization_audit.py` | 2026-06-12 | 1 | **NO** | Step33A A-source normalization bridge audit. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_source_sync_psd_sanity.py` | 2026-06-12 | 3 | **NO** | Step33A A-source sync PSD sanity diagnostic. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_tail_remainder_worklist.py` | 2026-06-12 | 13 | **NO** | Emit the Step33 raw-Omega A tail-remainder proof worklist. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_tail_route_diagnostic.py` | 2026-06-12 | 3 | **NO** | Diagnose the Step33A.1-A positive-tail-window proof route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_a_window_contract.py` | 2026-06-12 | 7 | **NO** | Build the exact Step33A.1-A window-payload contract. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_canonical_a_kernel_obstruction.py` | 2026-06-12 | 0 | **NO** | Step33A canonical-A kernel obstruction diagnostic. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_delta_live_rational_payload_lean.py` | 2026-06-12 | 86 | **NO** | Generate the Step33 delta/live rational payload Lean surface. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_direct_profile_payload_audit.py` | 2026-06-12 | 13 | **NO** | Audit the direct Step33 finite-prime profile payload shape. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_direct_profile_payload_lean.py` | 2026-06-12 | 27 | **NO** | Generate the Step33 direct-profile payload Lean surface. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_aristotle_result_ingest.py` | 2026-06-12 | 3 | **NO** | Fail-closed Aristotle result ingest helper for Step33 endpoint packages. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_endpoint_first_row_context_bundle.py` | 2026-06-12 | 11 | **NO** | Build a minimal Aristotle context bundle for the Step33 endpoint pilot. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_p0_base_hbox_lean.py` | 2026-06-12 | 18 | **NO** | Generate the Step33 P0 base-hbox receiver layer. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_p_replay_audit.py` | 2026-06-12 | 27 | **NO** | Audit whether Step33 P-entry replay can use termwise radius sums. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_positive_part_tight_lean.py` | 2026-06-12 | 9 | **NO** | Generate Step33 tight positivePartPower hbox payloads. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_rawomega_a_const_route_diagnostic.py` | 2026-06-12 | 2 | **NO** | Diagnose the raw-Omega Step33 A full-window constant route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_rawomega_a_nonconstant_route_diagnostic.py` | 2026-06-12 | 4 | **NO** | Diagnose the raw-Omega Step33 A nonconstant comparison route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_rawomega_a_quadratic_route_diagnostic.py` | 2026-06-12 | 3 | **NO** | Diagnose the raw-Omega Step33 A quadratic comparison route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_rawomega_a_tail_window_arithmetic_lean.py` | 2026-06-12 | 3 | **NO** | Generate the raw-Omega Step33 A tail-window arithmetic Lean import. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_signed_delta_recenter_audit.py` | 2026-06-12 | 3 | **NO** | Audit whether current A payload radii can contain the signed-A receiver. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_signed_q3astar_payload_lean.py` | 2026-06-12 | 4 | **NO** | Generate the Step33 signed-Q3.a_star A payload Lean import. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_signed_q3astar_penalty_ldl.py` | 2026-06-12 | 2 | **NO** | Generate exact rational LDL certificates for the Step33 signed-Q3.a_star route. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_signed_q3astar_source_relation_audit.py` | 2026-06-12 | 3 | **NO** | Audit the source relation between the route-B signed-Q3.a_star payload and the |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_sync_a_radii.py` | 2026-06-12 | 6 | **NO** | Synchronize Step22 A radii with finite/tail Arch manifests. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_sync_p0_radii.py` | 2026-06-12 | 0 | **NO** | Synchronize Step21/Step22 P0 radii with the current Arb P0 replay. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_sync_p_radii.py` | 2026-06-12 | 0 | **NO** | Synchronize Step22 P radii with the current Step20 direct-profile replay. |
| `q3.lean.aristotle/scripts/q3_psdpd_step33_transformed_a_recert_feasibility.py` | 2026-06-12 | 0 | **NO** | Step33A transformed-A finite recert feasibility dry-run. |
| `q3.lean.aristotle/scripts/q3_psdpd_step19_entry_radii.py` | 2026-05-26 | 7 | **NO** | Step 19 PSD-pd entry radii generator. |
| `q3.lean.aristotle/scripts/q3_psdpd_step20_midpoint_contract.py` | 2026-05-26 | 9 | **NO** | Step 20 PSD-pd midpoint/radius contract generator. |
| `q3.lean.aristotle/scripts/q3_psdpd_step21_p0_interval.py` | 2026-05-26 | 12 | **NO** | Step 21 PSD-pd P0 interval patcher. |
| `q3.lean.aristotle/scripts/q3_psdpd_step25_family_manifest.py` | 2026-05-26 | 7 | **NO** | Step 25 PSD-pd certificate-family manifest. |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_qradius_repair.py` | 2026-05-26 | 0 | **NO** | Repair and audit the active Step32F Q-radius payloads. |
| `q3.lean.aristotle/scripts/q3_psdpd_step32g_qrow_hbox_lean.py` | 2026-05-26 | 2 | **NO** | Generate Lean Q-row hbox certificates for the active Step32F payload. |
| `scripts/q3_check.sh` | 2026-05-26 | 1875 | yes | shellcheck disable=SC1091 |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_coeff_dictionary_lean_data.py` | 2026-05-25 | 4 | **NO** | Generate the concrete coefficient dictionary import for the active Step 32F |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_penalty_lower_bound_lean_params.py` | 2026-05-25 | 15 | **NO** | Generate Lean parameter targets for the Step 32F finite penalty lower bounds. |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_primary_ldl_cert.py` | 2026-05-25 | 12 | **NO** | Generate exact rational LDL certificates for active Step 32F coefficient |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_radius_floor_lean_data.py` | 2026-05-25 | 9 | **NO** | Generate Lean radius-floor data for the active Step 32F coefficient blocks. |
| `q3.lean.aristotle/scripts/q3_psdpd_step32f_coeff_payload_plan.py` | 2026-05-24 | 4 | **NO** | Step 32F coefficient payload import plan. |
| `q3.lean.aristotle/scripts/q3_psdpd_step13_pilot.py` | 2026-05-03 | 18 | **NO** | Step 13 PSD-pd numerical pilot. |
| `q3.lean.aristotle/scripts/q3_psdpd_step14_worst_vector.py` | 2026-05-03 | 7 | **NO** | Step 14 PSD-pd worst-vector autopsy. |
| `q3.lean.aristotle/scripts/q3_psdpd_step15_kappa_stability.py` | 2026-05-03 | 7 | **NO** | Step 15 PSD-pd kappa stability + worst-profile stability. |
| `q3.lean.aristotle/scripts/q3_psdpd_step16_refine_candidate.py` | 2026-05-03 | 6 | **NO** | Step 16 PSD-pd candidate refinement. |
| `q3.lean.aristotle/scripts/q3_psdpd_step17_extract_certificate.py` | 2026-05-03 | 6 | **NO** | Step 17 PSD-pd finite certificate extraction. |
| `q3.lean.aristotle/scripts/q3_psdpd_step18_interval_guard.py` | 2026-05-03 | 22 | **NO** | Step 18 PSD-pd interval/drift guard. |
| `q3.lean.aristotle/scripts/q3_psdpd_step25_certificate_manifest.py` | 2026-05-03 | 3 | **NO** | Step 25 PSD-pd certificate-family manifest. |
| `q3.lean.aristotle/scripts/q3_psdpd_step26_finitecert_ledger.py` | 2026-05-03 | 5 | **NO** | Step 26 PSD-pd FiniteCert ledger consumer. |
| `q3.lean.aristotle/scripts/q3_psdpd_step27_family_seed.py` | 2026-05-03 | 5 | **NO** | Step 27 PSD-pd directed-family seed generator. |
| `q3.lean.aristotle/scripts/po3_gamma_gap_witness.py` | 2026-04-19 | 4 | **NO** | Numerical witness scan for the PO3 raw manuscript prefix gap shell. |
| `q3.lean.aristotle/scripts/oracle_questions.py` | 2026-04-12 | 9 | **NO** | Address-aware journal for oracle question series. |
| `q3.lean.aristotle/scripts/refresh_q3_docs.py` | 2026-04-12 | 21 | yes |  |
| `scripts/research_oracle.py` | 2026-04-11 | 148 | yes |  |
| `q3.lean.aristotle/scripts/d2g16_real_packet_scan.py` | 2026-04-10 | 0 | **NO** | Radar scan for local real packets versus the Hermite line. |
| `src/h1_filtered_bulk_match.py` | 2026-03-12 | 20 | **NO** | Numerical filtered-bulk diagnostics for the direct H1^f bridge. |
| `q3.lean.aristotle/scripts/ingest_incoming_notes.py` | 2026-03-08 | 17 | **NO** |  |
| `src/h1_raw_bulk_match.py` | 2026-03-08 | 5 | **NO** | Numerical raw-bulk check for the H1 Suzuki--Q3 bridge. |
| `src/h1_raw_operator_sanity.py` | 2026-03-08 | 3 | **NO** | Sanity check for the raw H1 operator package. |
| `q3.lean.aristotle/scripts/refresh_erdos_overlap_kb.py` | 2026-03-07 | 3 | **NO** |  |
| `q3.lean.aristotle/scripts/research_oracle.py` | 2026-03-07 | 148 | yes |  |
| `scripts/qmd_ops.py` | 2026-03-07 | 0 | **NO** |  |
| `q3.lean.aristotle/scripts/check_axioms.sh` | 2026-03-06 | 348 | yes | Q3 Axiom Verification Script |
| `q3.lean.aristotle/scripts/audit_nosorry_active_q3.sh` | 2026-02-23 | 10 | **NO** | Re-include the PrimeCert files that are part of the active mainline contract/gate. |
| `scripts/prime_brange_grid_pp_auto.py` | 2026-02-23 | 230 | **NO** | Generate prime-power interval proofs for grid i19 pointwise upper bounds. |
| `scripts/build_primepow_gt10000_sequential.sh` | 2026-02-12 | 29 | **NO** | Sequentially build GT10000 shard modules for PrimePowAuto, |
| `scripts/prime_brange_heat_pp_auto.py` | 2026-02-12 | 1110 | **NO** | Generate prime-power interval proofs for prime-heat bounds on a chosen range. |
| `scripts/primepow_status.sh` | 2026-02-12 | 7 | **NO** | fallback if birth time is unavailable |
| `skills/x-insider/scripts/append_chat_insights.py` | 2026-02-12 | 16 | **NO** | Append a compact chat-insight entry to a markdown knowledge base file. |
| `skills/x-insider/scripts/x_export.py` | 2026-02-12 | 2 | **NO** | Export Codex chat messages from local session logs to a markdown file. |
| `scripts/prime_brange_grid_pp_interval_checker.py` | 2026-02-11 | 2 | **NO** | Generate prime-power upper bounds for the B-grid prime-term buckets. |
| `q3.lean.aristotle/scripts/kb_refresh.py` | 2026-02-09 | 7 | **NO** |  |
| `scripts/prime_brange_heat_pp_interval_checker.py` | 2026-02-08 | 11 | **NO** | Generate prime-power upper bounds for prime-heat partial sums (t_critical, tau=0). |
| `scripts/prime_brange_heat_pp_bucket0_auto.py` | 2026-02-06 | 60 | **NO** | Generate bucket-0 prime-power interval proofs for prime-heat bounds. |
| `scripts/run_heavy.sh` | 2026-02-06 | 51 | **NO** | Run heavy workloads in an isolated user slice to protect GUI session stability. |
| `scripts/prime_brange_heat_interval_checker.py` | 2026-02-01 | 5 | **NO** | Generate bucketed interval sums for the prime-heat partial sum (t_critical, tau=0). |
| `scripts/prime_brange_interval_checker_grid.py` | 2026-02-01 | 5 | **NO** | Generate bucketed interval sums for the full B-grid (20 points). |
| `scripts/prime_brange_heat_partial_interval_cert.py` | 2026-01-31 | 3 | **NO** | Interval certificate for the prime-heat partial sum at t_critical (tau = 0). |
| `scripts/prime_brange_heat_partial_interval_to_lean.py` | 2026-01-31 | 3 | **NO** | Convert prime-heat partial interval output into a Lean SumData file. |
| `scripts/prime_brange_interval_checker_pilot.py` | 2026-01-31 | 4 | **NO** | Generate bucketed interval sums for the pilot B values (B=3.0, 4.9). |
| `scripts/prime_brange_interval_to_lean_ub.py` | 2026-01-31 | 3 | **NO** | Convert a prime B-range interval certificate into a Lean UB table. |
| `scripts/prime_brange_pilot_interval_to_lean_ub.py` | 2026-01-31 | 4 | **NO** | Convert a pilot interval certificate into a Lean UB table. |
| `docs/Aristotle_models_training/build_dependency_graph.py` | 2026-01-30 | 4 | **NO** | Построение графа зависимостей для RH_Q3.pdf |
| `docs/Aristotle_models_training/correct_inequality_example.py` | 2026-01-30 | 1 | **NO** | Пример анализа КОРРЕКТНОГО неравенства с условием t ≤ A |
| `docs/Aristotle_models_training/effective_risk.py` | 2026-01-30 | 8 | **NO** | effective_risk.py - Вычисление Effective Risk Score для разрешения парадокса |
| `docs/Aristotle_models_training/kernel_analysis_example.py` | 2026-01-30 | 1 | **NO** | Пример анализа выражения kernel A t x >= c * A * exp(-t/A) |
| `docs/Aristotle_models_training/lean_error_parser.py` | 2026-01-30 | 41 | **NO** | lean_error_parser.py - Парсер ошибок Lean 4 для автоматической генерации семантических sorry |
| `docs/Aristotle_models_training/norm_balancer.py` | 2026-01-30 | 46 | **NO** | Norm Balancer: Алгоритм балансировки неравенств через нормализацию |
| `docs/Aristotle_models_training/rh_q3_decomposition/rh_q3_analysis/build_dependency_graph.py` | 2026-01-30 | 4 | **NO** | Построение графа зависимостей для RH_Q3.pdf |
| `docs/Aristotle_models_training/rh_q3_decomposition/rh_q3_analysis/visualize_graph.py` | 2026-01-30 | 4 | **NO** | Визуализация графа зависимостей RH_Q3.pdf |
| `docs/Aristotle_models_training/sorry_system_analyzer.py` | 2026-01-30 | 38 | **NO** | sorry_system_analyzer.py - Анализатор системы sorry-лемм в Lean 4 проектах |
| `docs/Aristotle_models_training/verify_critical_constants.py` | 2026-01-30 | 1 | **NO** | Численная верификация критических констант из RH_Q3.pdf |
| `docs/Aristotle_models_training/visualize_graph.py` | 2026-01-30 | 4 | **NO** | Визуализация графа зависимостей RH_Q3.pdf |
| `q3.lean.aristotle/scripts/check_audit_invariants.sh` | 2026-01-30 | 13 | **NO** |  |
| `q3.lean.aristotle/scripts/check_links.py` | 2026-01-30 | 6 | **NO** |  |
| `q3.lean.aristotle/scripts/fill_requests_tree.py` | 2026-01-30 | 0 | **NO** | Fill TODO sections in ACTIVE/requests node.md files with safe placeholders. |
| `q3.lean.aristotle/scripts/floor_cert_tcritical.py` | 2026-01-30 | 1 | **NO** | Certificate for P_A floor at t_critical on Icc(-1/2, 1/2) |
| `q3.lean.aristotle/scripts/update_formalization_stats.sh` | 2026-01-30 | 10 | **NO** | update_formalization_stats.sh - refresh FORMALIZATION_STATS.md with latest snapshot |
| `q3.lean.aristotle/scripts/update_requests_tree.py` | 2026-01-30 | 0 | **NO** | Update ACTIVE/requests node files with related outputs. |
| `scripts/prime_brange_interval_cert.py` | 2026-01-30 | 1 | **NO** | Interval certificate for prime-term partial sums on the full B-grid. |
| `scripts/prime_brange_pilot_interval.py` | 2026-01-30 | 0 | **NO** | Interval certificate for the prime-term partial sums at two pilot B values. |
| `scripts/prime_brange_pilot_points.py` | 2026-01-30 | 1 | **NO** | Extract pilot points (B=3.0 and B=4.9) from the existing B-range certificate. |
| `scripts/prime_brange_to_lean.py` | 2026-01-30 | 2 | **NO** | Convert prime_cert_brange output into a Lean grid table. |
| `bellman_bmo.py` | 2026-01-29 | 3 | **NO** | BMO Optimization via Bellman Functions |
| `q3.lean.aristotle/aristotle_db/parse_lean.py` | 2026-01-29 | 80 | yes | Lean 4 Parser for Aristotle Proofs Database |
| `q3.lean.aristotle/monitor_server.py` | 2026-01-29 | 5 | yes | Simple monitoring server for Aristotle projects. |
| `q3.lean.aristotle/scripts/aristotle_dag_loop.py` | 2026-01-29 | 7 | yes | Generate a lightweight Aristotle queue from open axioms + sorries. |
| `q3.lean.aristotle/scripts/build_docs.sh` | 2026-01-29 | 3 | **NO** | Build Q3 documentation with doc-gen4 |
| `q3.lean.aristotle/scripts/contribution_stats.sh` | 2026-01-29 | 5 | **NO** | contribution_stats.sh - Accurate contribution statistics |
| `q3.lean.aristotle/scripts/refresh_insights.py` | 2026-01-29 | 7 | **NO** | Refresh and validate docs/insights index and links. |
| `q3.lean.aristotle/scripts/refresh_status.py` | 2026-01-29 | 1 | yes | Refresh Aristotle DB + status docs for core A3_FLOOR/Q3 files. |
| `q3.lean.aristotle/scripts/tdd.sh` | 2026-01-29 | 9 | **NO** | Lean 4 TDD Helper Script |
| `q3.lean.aristotle/scripts/update_docs.sh` | 2026-01-29 | 1 | **NO** | Update Q3 API documentation |
| `q3.lean.aristotle/scripts/update_status.py` | 2026-01-29 | 4 | yes |  |
| `scripts/build_dependency_tree.py` | 2026-01-29 | 5 | **NO** | Run Q3/CheckAxioms.lean and parse the axiom dependency list. |
| `scripts/build_proof_graph.py` | 2026-01-29 | 10 | **NO** |  |
| `scripts/build_sorry_frontier.py` | 2026-01-29 | 3 | **NO** | Remove line/block comments while preserving line structure. |
| `scripts/build_taint_graph.py` | 2026-01-29 | 7 | **NO** | Remove line/block comments while preserving line structure. |
| `scripts/numeric_sanity_check.py` | 2026-01-29 | 8 | **NO** |  |
| `scripts/prime_brange_heat_lipschitz_cert.py` | 2026-01-28 | 5 | **NO** | Scaffold: compute heat-weighted Lipschitz constants for the prime/arch terms |
| `scripts/quillen_working_papers.py` | 2026-01-27 | 0 | **NO** |  |
| `scripts/zotero_add_links.py` | 2026-01-27 | 0 | **NO** |  |
| `scripts/zotero_cards.py` | 2026-01-27 | 0 | **NO** |  |
| `scripts/zotero_ingest.py` | 2026-01-27 | 6 | **NO** |  |
| `scripts/floor_grid_to_lean.py` | 2026-01-26 | 1 | **NO** | Convert floor_grid_tcritical output into a Lean grid table. |
| `scripts/pa_floor_cert.py` | 2026-01-25 | 1 | **NO** | Compute a grid + Lipschitz-style certificate for |
| `scripts/pa_lipschitz_cert.py` | 2026-01-25 | 0 | **NO** | Compute Lipschitz bound for P_A(B_min, t_critical) on [-1/2, 1/2]. |
| `scripts/prime_term_cert.py` | 2026-01-25 | 6 | **NO** | Prime-term certificate at t_critical (single-scale, tau = 0). |
| `scripts/prime_term_cert_brange.py` | 2026-01-25 | 5 | **NO** | Prime-term certificate over a B-range at t_critical (single-scale, tau = 0). |
| `scripts/build_proshka_brief.py` | 2026-01-24 | 10 | **NO** | Build a Proshka context pack from the Q3 repo. |
| `scripts/ralph-loop.sh` | 2026-01-24 | 0 | **NO** | Ensure plan file exists in plan mode. |
| `scripts/refresh_proshka_pack.sh` | 2026-01-24 | 1 | **NO** |  |
| `verify_phase0.py` | 2026-01-22 | 19 | **NO** | Phase 0 Verification: Confirm Q definitions match Lean/LaTeX |
| `verify_q_tail.py` | 2026-01-22 | 2 | **NO** | Stronger numerical verification of Q(Φ) with explicit tail control. |
| `verify_variant_b.py` | 2026-01-22 | 16 | **NO** | TDD Step 3: Numerical Certificates for Variant B (Finite Matrix Cap) |
| `docs/afm_opus/METHOD2_circle_method.py` | 2026-01-21 | 0 | **NO** | МЕТОД 2: CIRCLE METHOD (Метод окружности) |
| `docs/afm_opus/METHOD3_direct_proof.py` | 2026-01-21 | 0 | **NO** | МЕТОД 3: ПРЯМОЕ ДОКАЗАТЕЛЬСТВО ЧЕРЕЗ РЕЗОНАНС |
| `docs/synergy_opus/SYNERGY_NUMERICAL_CHECK.py` | 2026-01-21 | 0 | **NO** | ЧИСЛЕННАЯ ПРОВЕРКА СИНЕРГИИ: Bell + χ₄ |
| `scripts/swarm_coordinator 2.py` | 2026-01-20 | 0 | **NO** | Research Swarm Coordinator — status aggregation and cleanup. |
| `scripts/swarm_generate_task 2.sh` | 2026-01-20 | 0 | **NO** | Research Swarm Task Generator — converts insight to TASK.md |
| `scripts/swarm_spawner 2.sh` | 2026-01-20 | 0 | **NO** | Research Swarm Spawner — creates sandbox and opens terminal |
| `scripts/swarm_watcher 2.sh` | 2026-01-20 | 0 | **NO** | Research Swarm Watcher — monitors insights/new/ and spawns workers |
| `src/analyze_digamma_poison.py` | 2026-01-01 | 1 | **NO** | АНАЛИЗ: Где дигамма становится "ядовитой"? |
| `src/energy_functional.py` | 2026-01-01 | 0 | **NO** | Load zeros (one per line) as float array; optionally truncate to `limit`. |
| `src/floor_adaptive_t.py` | 2026-01-01 | 1 | **NO** | ТЕСТ: Адаптивное t для режима перекрытия окон |
| `src/floor_proof.py` | 2026-01-01 | 6 | **NO** | Проверяет поведение МИНИМУМА символа P_A (Archimedean Floor) |
| `src/floor_q3_real.py` | 2026-01-01 | 1 | **NO** | ИСПРАВЛЕННЫЙ ТЕСТ: Реальная функция из Q3 |
| `src/floor_saturation.py` | 2026-01-01 | 1 | **NO** | Проверяет поведение НИЖНЕЙ ГРАНИЦЫ (Floor) символа P_A |
| `src/merlin_kernel_test.py` | 2026-01-01 | 14 | **NO** | MERLIN KERNEL TEST: Поиск положительно-определённого ядра |
| `src/q3_alpha_scaling.py` | 2026-01-01 | 6 | **NO** | Q3 Alpha Scaling Analysis |
| `src/q3_spectrum_V.py` | 2026-01-01 | 4 | **NO** | Q3 Spectrum Analysis: Eigenvalues of V_K |
| `src/q3_stress_test.py` | 2026-01-01 | 6 | **NO** | Q3 STRESS TEST: K=2.0, K=2.5 |
| `src/q3_twins_phase2.py` | 2026-01-01 | 0 | **NO** | Q3 Phase 2: Twin Primes via Two-Particle Operator |
| `src/rescue_archimedes.py` | 2026-01-01 | 4 | **NO** | СПАСАТЕЛЬНАЯ МИССИЯ: Гамма-метрика вместо Дигамма-яда |
| `src/rescue_gamma_pure.py` | 2026-01-01 | 1 | **NO** | СПАСАТЕЛЬНАЯ МИССИЯ v2: Чистая Гамма-метрика без окна |
| `src/saturation_proof.py` | 2026-01-01 | 8 | **NO** | Вычисляет значения g, g', g'' в точке xi для текущего B. |
| `docs/CHECK_B_POSITIVITY.py` | 2025-12-19 | 0 | **NO** | ЧИСЛЕННАЯ ПРОВЕРКА: Оператор B положительно определён? |
| `docs/CRITICAL_GAP_ANALYSIS.py` | 2025-12-19 | 0 | **NO** | КРИТИЧЕСКИЙ АНАЛИЗ: Где мост от operator bounds к TPC? |
| `docs/synergy_extracted/SYNERGY_NUMERICAL_CHECK.py` | 2025-12-19 | 0 | **NO** | ЧИСЛЕННАЯ ПРОВЕРКА СИНЕРГИИ: Bell + χ₄ |
| `src/R_lower_bound_derivation.py` | 2025-12-19 | 14 | **NO** | АНАЛИТИЧЕСКАЯ НИЖНЯЯ ГРАНИЦА R(X) ≥ c > 0 |
| `src/__init__.py` | 2025-12-19 | 10 | **NO** |  |
| `src/analytic_M_computation.py` | 2025-12-19 | 0 | **NO** | STEP 2: Analytic Computation of Sieve Ratio M(F_spec). |
| `src/analytical_B1.py` | 2025-12-19 | 7 | **NO** | Analytical B₁: CD(κ,∞) → Poincaré → B₁(lattice) |
| `src/anchor_analysis.py` | 2025-12-19 | 0 | **NO** | Sieve of Eratosthenes to get primes up to n_max. |
| `src/audit_claims.py` | 2025-12-19 | 0 | **NO** | 🔍 АУДИТ ВСЕХ CLAIMS В PAPER |
| `src/b1_precise_check.py` | 2025-12-19 | 1 | **NO** | B₁ Precise Check: Что именно требует B₁(prime)? |
| `src/bakry_emery_test.py` | 2025-12-19 | 7 | **NO** | Bakry-Émery vs Our Formulation Test |
| `src/boundary_R_analysis.py` | 2025-12-19 | 0 | **NO** | АНАЛИТИЧЕСКИЙ АНАЛИЗ: R на boundary family λ = a·e_0 + b·e_{N-1} |
| `src/boundary_concentration_proof.py` | 2025-12-19 | 0 | **NO** | PROOF ATTEMPT: Lower bound via boundary concentration |
| `src/boundary_rows_bound.py` | 2025-12-19 | 0 | **NO** | STRONGER BOUND USING ALL BOUNDARY ROWS |
| `src/bpq_growth.py` | 2025-12-19 | 0 | **NO** | Quick probe of B_{pq}(X) growth for fixed twin primes p,q. |
| `src/c_twins_lambda_test.py` | 2025-12-19 | 2 | **NO** | c_twins(λ) Dependence Test: Alternative Mechanism for B₁ |
| `src/c_twins_scaling.py` | 2025-12-19 | 7 | **NO** | c_twins Scaling Analysis |
| `src/c_twins_sparse.py` | 2025-12-19 | 3 | **NO** | c_twins Sparse Computation: Extension to X = 10⁶ |
| `src/check_parity_sensitivity.py` | 2025-12-19 | 0 | **NO** | Parity-sensitivity experiment for the Rayleigh quotient R = E_comm / E_lat. |
| `src/check_span_growth.py` | 2025-12-19 | 0 | **NO** | Проверка: span ~ log(N) — это факт или гипотеза? |
| `src/chen_pairs_test.py` | 2025-12-19 | 0 | **NO** | ТЕСТ Q5: Chen pairs как модельный случай |
| `src/chi4_twisted_analysis.py` | 2025-12-19 | 0 | **NO** | χ₄ TWISTED APPROACH: Использование характера χ₄ для выделения twins |
| `src/circularity_analysis.py` | 2025-12-19 | 1 | **NO** | Анализ цикличности Target Theorem |
| `src/commutator_exact_formula.py` | 2025-12-19 | 5 | **NO** | Exact Commutator Formula: Формализация геометрического механизма |
| `src/commutator_resonance.py` | 2025-12-19 | 7 | **NO** | Compute commutator resonance metrics for the twin sector. |
| `src/commutator_rkhs_bounds.py` | 2025-12-19 | 2 | **NO** | Коммутатор [T_P, Ξ]: RKHS оценки |
| `src/compare_interpretations.py` | 2025-12-19 | 0 | **NO** | Сравнение двух интерпретаций Bakry-Émery для Model B₁ |
| `src/constrained_lagrangian.py` | 2025-12-19 | 1 | **NO** | Constrained Lagrangian: minimize R = λᵀQλ/λᵀGλ on CONE. |
| `src/convolution_twin_analysis.py` | 2025-12-19 | 0 | **NO** | CONVOLUTION APPROACH: S₂(X) через Fourier |
| `src/cross_terms_analysis.py` | 2025-12-19 | 0 | **NO** | Cross-Terms Analysis for Step B |
| `src/delta_anatomy.py` | 2025-12-19 | 2 | **NO** | АНАТОМИЯ δ: Где реально живёт экспонента роста? |
| `src/direct_min_R_test.py` | 2025-12-19 | 0 | **NO** | DIRECT TEST: Compute actual min_cone R for large N. |
| `src/e_comm_e_dir_relation.py` | 2025-12-19 | 3 | **NO** | Критический вопрос 1: Связь E_comm ↔ E_dir |
| `src/energy_s2_correlation.py` | 2025-12-19 | 0 | **NO** | Численная проверка связи ℰ_X(λ) ~ S₂(X) |
| `src/f_twin_maynard_bridge.py` | 2025-12-19 | 0 | **NO** | F_twin ↔ M(F) ↔ R(X) Bridge |
| `src/formal_R_min_proof.py` | 2025-12-19 | 0 | **NO** | ФОРМАЛЬНОЕ ДОКАЗАТЕЛЬСТВО: R_min → ∞ |
| `src/formal_lower_bound.py` | 2025-12-19 | 0 | **NO** | FORMAL LOWER BOUND FOR R(1) = Sum(Q)/Sum(G) |
| `src/formal_proof_P_X.py` | 2025-12-19 | 0 | **NO** | FORMAL PROOF of P(X): min_cone R → ∞ |
| `src/fourier_twin_analysis.py` | 2025-12-19 | 0 | **NO** | Fourier analysis of Λ(n) and connection to twins. |
| `src/gaussian_to_powerlaw.py` | 2025-12-19 | 0 | **NO** | Gaussian → Power-law effective exponent analysis. |
| `src/gpy_sieve_approach.py` | 2025-12-19 | 0 | **NO** | GPY SIEVE APPROACH: Goldston-Pintz-Yıldırım method |
| `src/gpy_vs_random_test.py` | 2025-12-19 | 0 | **NO** | GPY VS RANDOM: Проверка даёт ли GPY sieve advantage над random points |
| `src/h_x_convergence.py` | 2025-12-19 | 2 | **NO** | Сходимость ⟨H_X Φ_∞, Φ_∞⟩ при конечных twins |
| `src/hamiltonian.py` | 2025-12-19 | 5 | **NO** | Minimal builder for the Q3 Hamiltonian H = T_A - T_P. |
| `src/kernel_analysis.py` | 2025-12-19 | 6 | **NO** | Kernel Analysis: Исследование ker(M) для twin-матрицы |
| `src/kernel_cone_check.py` | 2025-12-19 | 9 | **NO** | Kernel Cone Check: Проверка — лежат ли собственные вектора ядра в twin-конусе? |
| `src/lagrangian_eigenvalues.py` | 2025-12-19 | 0 | **NO** | Lagrangian approach: solve generalized eigenvalue problem Qλ = μGλ |
| `src/large_N_test.py` | 2025-12-19 | 0 | **NO** | Test scaling at VERY large N to understand true asymptotic behavior. |
| `src/lipschitz_analysis.py` | 2025-12-19 | 0 | **NO** | Lipschitz Analysis of R(λ) on the positive cone. |
| `src/maynard_conditions.py` | 2025-12-19 | 0 | **NO** | STEP 1: Verification of Maynard Conditions for F_spec. |
| `src/model_B1_direct.py` | 2025-12-19 | 9 | **NO** | Model B₁: ПРЯМОЕ ВЫЧИСЛЕНИЕ (без Fourier приближений) |
| `src/model_B1_fourier.py` | 2025-12-19 | 0 | **NO** | Model B₁: Проверка через дискретную Фурье / Пуанкаре |
| `src/off_diagonal_analysis.py` | 2025-12-19 | 0 | **NO** | Off-diagonal decay analysis for H = T_A - T_P. |
| `src/optimal_vector_analysis.py` | 2025-12-19 | 0 | **NO** | ANALYZE OPTIMAL VECTOR STRUCTURE |
| `src/perturbation_check.py` | 2025-12-19 | 8 | **NO** | Perturbation Check: G^prime vs G^lat |
| `src/perturbation_twins.py` | 2025-12-19 | 6 | **NO** | Perturbation Check: TWIN CONE VERSION |
| `src/prove_M_bound.py` | 2025-12-19 | 0 | **NO** | STEP 3: Rigorous Verification that M(F_spec) > 4. |
| `src/prove_boundary_lemma.py` | 2025-12-19 | 0 | **NO** | KEY LEMMA: Lower bound on min(Q_rowsum) via boundary analysis |
| `src/prove_c_constant.py` | 2025-12-19 | 0 | **NO** | GOAL: Understand WHY c = min_cone R / [Tr(Q)/Tr(G)] ≈ 0.486 is stable |
| `src/prove_min_R_growth.py` | 2025-12-19 | 0 | **NO** | GOAL: Prove min_cone R ~ N^δ for some δ > 0 |
| `src/prove_row_sum.py` | 2025-12-19 | 0 | **NO** | 🔥 ФИНАЛЬНОЕ ДОКАЗАТЕЛЬСТВО: row_k(A) ~ Θ(N) 🔥 |
| `src/prove_rowsum_bound.py` | 2025-12-19 | 0 | **NO** | BREAKTHROUGH: rowsum_bound gives a PROVABLE lower bound! |
| `src/q3_atom_model 2.py` | 2025-12-19 | 1 | **NO** | Q3-Atom Toy Model: Spectral Test for Riemann Hypothesis |
| `src/q3_atom_model.py` | 2025-12-19 | 2 | **NO** | Q3-Atom Toy Model: Spectral Test for Riemann Hypothesis |
| `src/q3_coherence_test.py` | 2025-12-19 | 0 | **NO** | Q3 COHERENCE TEST: Резонанс Вейля |
| `src/q3_corrected_model.py` | 2025-12-19 | 1 | **NO** | Q3 Corrected Model: Proper Archimedes Density |
| `src/q3_galerkin_phase1.py` | 2025-12-19 | 15 | **NO** | Q3-Atom Phase 1: Galerkin Approximation with Proper Normalization |
| `src/q3_grh_chi4.py` | 2025-12-19 | 22 | **NO** | Q3 GRH: L-функции с характером Дирихле χ₄ (mod 4) |
| `src/q3_grh_phase_d1.py` | 2025-12-19 | 6 | **NO** | Q3 GRH Phase D.1: Разделение классов вычетов |
| `src/q3_spectral_summary.py` | 2025-12-19 | 4 | **NO** | Q3 SPECTRAL ANALYSIS: SUMMARY AND CONCLUSIONS |
| `src/q3_verify.py` | 2025-12-19 | 6 | **NO** | Q3 Verification: H = T_A - T_P >= 0 |
| `src/q3_vtwin_operator.py` | 2025-12-19 | 19 | **NO** | Q3 V_TWINS: Оператор взаимодействия между секторами |
| `src/r_phi_scaling.py` | 2025-12-19 | 4 | **NO** | Compute and plot the scaling of R(Phi_X) = E_comm / E_lat for the twin vector. |
| `src/ratio_const_analysis.py` | 2025-12-19 | 0 | **NO** | АНАЛИТИЧЕСКОЕ ОБЪЯСНЕНИЕ: Почему Ratio = R(1)/R_min ~ const? |
| `src/ratio_extrapolation.py` | 2025-12-19 | 0 | **NO** | DETAILED ANALYSIS OF R(1)/R_min RATIO |
| `src/ratio_extrapolation_v2.py` | 2025-12-19 | 0 | **NO** | Экстраполяция ratio = R(1)/R_min на большие N. |
| `src/rayleigh_minimum_scan.py` | 2025-12-19 | 2 | **NO** | Rayleigh Minimum Scan: поиск минимума c₁(X) по разным λ |
| `src/row_sum_analytical.py` | 2025-12-19 | 0 | **NO** | ANALYTICAL BOUND ON row_0(A) |
| `src/score_expansion_check.py` | 2025-12-19 | 0 | **NO** | Score expansion sanity-check for Lemma 7.2. |
| `src/shift.py` | 2025-12-19 | 4 | **NO** | Shift operators S_delta for commutator resonance experiments. |
| `src/sieve_spectral_check.py` | 2025-12-19 | 0 | **NO** | Sieve-Spectral Synergy Hypothesis Check. |
| `src/spectral_B_operator.py` | 2025-12-19 | 0 | **NO** | Спектральный анализ симметризованного оператора B. |
| `src/spectral_capture.py` | 2025-12-19 | 1 | **NO** | Spectral capture: decompose psi in eigenbasis of H and measure phase dispersion under S. |
| `src/strict_proof.py` | 2025-12-19 | 0 | **NO** | 🎯 СТРОГОЕ ДОКАЗАТЕЛЬСТВО R(1) → ∞ |
| `src/trace_twisted_commutator.py` | 2025-12-19 | 0 | **NO** | Вычисление ⟨Φ_X, [F, U_2] χ_4 Φ_X⟩ |
| `src/twin_correlation_bridge.py` | 2025-12-19 | 4 | **NO** | Compute classical twin correlations alongside commutator metrics. |
| `src/twins_state.py` | 2025-12-19 | 4 | **NO** | Twin-sector state construction for commutator resonance experiments. |
| `src/verify_B1.py` | 2025-12-19 | 2 | **NO** | Численная верификация B₁ |
| `src/verify_B2.py` | 2025-12-19 | 0 | **NO** | Численная верификация B₂ |
| `src/verify_B2_v2.py` | 2025-12-19 | 0 | **NO** | Численная верификация B₂ (версия 2) |
| `src/verify_gamma_formula.py` | 2025-12-19 | 0 | **NO** | Verification of analytic γ_eff formula against parameter sweep. |
| `src/weil_twin_connection.py` | 2025-12-19 | 0 | **NO** | WEIL → TWIN CONNECTION |
| `src/x_vs_n_dependence.py` | 2025-12-19 | 0 | **NO** | КРИТИЧЕСКИЙ ТЕСТ: X-dependence vs N-dependence |

## Orphans — alive but nothing references them

Either wire them into a contour or archive them; a tool nobody calls is a tool nobody will find when it is needed.

- `orchestrator/sense.py` (last 2026-07-30) — SENSE lane — read-only phase detection for the Route B conductor.

## Note on probes

The 159 one-shot probes are deliberately **not** mapped here. They are goal-local evidence, not instruments; treating them as tooling is what makes the instrument set look unknowably large.

