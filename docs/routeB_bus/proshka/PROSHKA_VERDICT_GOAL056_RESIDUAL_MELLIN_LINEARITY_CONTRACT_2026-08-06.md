OPERATIVE_CLASS:
  TRY_G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE

TRANSACTION:
  G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE

AUTHORITY:
  mathematical_decision: CODEX_PLUS_PROSHKA
  owner_action_required: false
  sole_owner_gate: PX_RH_CLAIM

PHASE:
  phase_key_change: false
  reuse_conversation_id: 6a72e750-dc60-83eb-946b-61d2073c232b
  fresh_chat: forbidden

SOURCE_LOCK:
  repo: Malaeu/chen_q3
  branch: rh_clean
  expected_head: 1b1f36629b1236909c027891d4a8f68748c6134c

  expected_phase4B:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualContract.lean
    sha256: 1f9b0f16210271fc699107f991a244421d98bbdafd695d5a585dae4aca4f73ff

  expected_phase4E:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarProjectedMellinCoordinate.lean
    sha256: 8f0c764615873a6a3e677d13d86ba6686cc5f4b31354749e4cf171f36fed139e

  expected_phase4F:
    path: q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarFullMellinGwinCrosswalk.lean
    sha256: 62cfcbdcc209a3da7fbb7d2dd3a58b24937209f1dde416a721d539e414769818

ON_SOURCE_MISMATCH:
  stop: G6_S2_RESIDUAL_MELLIN_SOURCE_LOCK_MISMATCH
  edit_files: false

CREATE:
  - q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean

IMPORTS_EXACT:
  - Q3.Proofs.RouteB.D0PstarMuntzGalerkinResidualContract
  - Q3.Proofs.RouteB.D0PstarFullMellinGwinCrosswalk

NAMESPACE:
  Q3.RouteB.D0Pstar

PUBLIC_SURFACE:
  definitions: 0
  theorems: 2
  private_production_declarations: 1

PRIVATE_HELPER: |
  private theorem integrable_H_m_mul_mellinKernel
      (i : PairIndex) (f : H_m i) (z : ℂ) :
      Integrable
        (fun u : ℝ =>
          f u * (u : ℂ) ^ (-Complex.I * z))
        (dStar.restrict (I_m i)) := by
    ...

PUBLIC_THEOREM_1: |
  theorem
      selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull
      (S : ProlateCanonicalSourceData)
      (k : ℕ) (z : ℂ) :
      selectedGalerkinResidualMellinCoordinate S k z =
        selectedProjectedMellinCoordinate S k z -
          (selectedTrialNormalizer S k : ℂ) *
            selectedFullMellinCoordinate S k z := by
    ...

PUBLIC_THEOREM_2: |
  theorem D0PstarMuntzGalerkinResidualCrosswalkContract_proved
      (S : ProlateCanonicalSourceData) :
      D0PstarMuntzGalerkinResidualCrosswalkContract S := by
    intro k z
    rw [
      selectedGalerkinResidualMellinCoordinate_eq_projected_sub_scaledFull,
      selectedProjectedMellinCoordinate_eq_selectedRawTransformCoordinate,
      selectedTrialNormalizer_mul_selectedFullMellinCoordinate_eq_selectedScaledGwinTransformCoordinate
    ]
    rfl

REQUIRED_PROOF_ROUTE:
  private_helper:
    - reconstruct IsFiniteMeasure for dStar.restrict(I_m i)
    - derive L1 integrability from Lp.memLp at exponent two
    - prove the complex-power kernel ContinuousOn the positive compact I_m
    - obtain one finite kernel norm bound from compactness
    - apply Integrable.mul_bdd

  jump_theorem:
    - unfold only the selected residual and exact D0 normalizer objects
    - prove quotient representative relations with Lp.coeFn_sub and Lp.coeFn_smul
    - use only almost-everywhere equality
    - prove projected and full integrands integrable before any subtraction
    - use integral_congr_ae
    - use integral_sub only with both integrability proofs
    - use integral_const_mul
    - fold selectedProjectedMellinCoordinate and selectedFullMellinCoordinate
    - do not use Phase4E or Phase4F transform equalities here

  contract_theorem:
    - use the jump theorem
    - rewrite projected coordinate by Phase4E
    - rewrite normalized full coordinate by the Phase4F scaled corollary
    - close the Phase4A defect definition by rfl

K6_OBJECT_PRECOMMIT:
  source_object: selectedNormalizedGalerkinResidual
  selected_index: selectedPairIndex_S_k
  residual_order: projection_minus_full
  normalizer: selectedTrialNormalizer_left_scalar
  measure: dStar_restrict_I_m
  kernel: u_cpow_minus_I_z
  representative_relation: almost_everywhere
  projected_coordinate_argument: z
  full_coordinate_argument: z
  raw_coordinate: rawFplus_at_minus_z
  Gwin_coordinate: Gwin_at_minus_I_times_z
  contract_direction: scalar_defect_equals_object_residual_coordinate

MANDATORY_PLANTS:
  - P056P_1_OBJECT_SURROGATE
  - P056P_2_FINITE_MEASURE
  - P056P_3_POSITIVE_WINDOW
  - P056P_4_LP_QUOTIENT
  - P056P_5_LINEARITY_ORDER
  - P056P_6_NORMALIZER
  - P056P_7_PHASE4E_ORIENTATION
  - P056P_8_PHASE4F_ORIENTATION
  - P056P_9_RESIDUAL_ORDER

VALIDATION:
  - verify HEAD equals origin before editing
  - verify all three SHA-256 source locks
  - lake env lean q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
  - dedicated target build
  - full build
  - bash scripts/q3_check.sh q3.lean.aristotle/Q3/Proofs/RouteB/D0PstarMuntzGalerkinResidualCrosswalk.lean
  - scan for sorry admit exact? native_decide axiom opaque Float
  - scan for imports from aristotle_output or ACTIVE RequestProject
  - require zero public definitions
  - require exactly two public theorems
  - require exactly one private production theorem
  - fire all nine plants
  - remove all temporary plant files
  - print axioms for both public theorems
  - require exactly [propext, Classical.choice, Quot.sound]
  - proof database reimport
  - require all three declarations indexed and both public theorems marked proven
  - run all 67 orchestration tests
  - python3 orchestrator/spine.py --strict --reason goal-close
  - require strict Spine PASS
  - run SQLite integrity_check on knowledge.db
  - run SQLite integrity_check on aristotle_proofs.db
  - run SQLite integrity_check on observability.db
  - require all three results equal ok
  - report observability source and stale counts
  - git diff --check
  - exact git status report

STOP:
  G6_S2_D0_RESIDUAL_MELLIN_LINEARITY_AND_CONTRACT_DISCHARGE_MISSING

SUCCESS:
  G6_S2_D0_RESIDUAL_MELLIN_CROSSWALK_CONTRACT_PROVED

PHASE4B_CONTRACT_AFTER_SUCCESS:
  status: PROVED_UNCONDITIONALLY
  modify_original_contract_file: false
  add_new_axiom_or_hypothesis: false

SOLE_NEXT_NODE_NOT_AUTHORIZED:
  name: G6_S2_D0_SELECTED_NORMALIZED_GALERKIN_RESIDUAL_L2_DECAY
  jump_target: |
    Tendsto
      (fun k : ℕ => ‖selectedNormalizedGalerkinResidual S k‖)
      atTop
      (𝓝 0)

ARISTOTLE:
  status: FORBIDDEN

FORBIDDEN:
  - define residual coordinate from scalar difference
  - replace selectedNormalizedGalerkinResidual by a scalar surrogate
  - use global pointwise equality for Lp representatives
  - invoke integral_sub before integrability
  - reverse projection_minus_full
  - move or duplicate the selected normalizer
  - change the selected parent_extract index
  - flip Phase4E raw reflection
  - flip Phase4F Gwin argument
  - prove residual decay
  - prove compact_open_convergence
  - prove strict SlotS2
  - add an unconditional receiver wrapper duplicating the existing consumer
  - edit Q3.Main
  - edit Goal_055
  - create Bus_010
  - submit Aristotle
  - promote Route_B
  - make PX_or_RH_claim
  - open a fresh Proshka chat

FINAL_BOUNDARY:
  route: CHALLENGER_NOT_RH
  bus_010: VOID
  goal_055: HOLD
  Aristotle_submission: NONE
  route_promotion: false
  PX_RH_CLAIM: NOT_MADE
