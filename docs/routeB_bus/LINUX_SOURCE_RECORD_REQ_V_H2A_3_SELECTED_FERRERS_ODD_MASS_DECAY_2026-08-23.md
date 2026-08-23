# SOURCE RECORD — H2A.3 selected Ferrers odd-mass decay (Linux-тело за Codex)

```yaml
PRIMARY: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LOCK
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 89f10e98 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 89f10e98385cd4621d3ccc54dc56ae631e6b8ec7
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок; fetch origin/rh_clean
  выполнен перед коммитом — новых [Proshka]-коммитов нет; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"selected Ferrers odd mass decay log sqrt rate anchor
  Bessel window integral\" — машинерии распада odd mass нет нигде; Бессель
  (Orthonormal.sum_inner_products_le), inversion-even crosswalk и
  Gwin-нулевой якорь существуют; имена свободны."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean
LEAN_GIT_BLOB: 0b8e3f590a2b968b34f66eb52b9c4e40bf0eed70
LEAN_SHA256: d64d350cc822db3e4bc4a9c25ff20f24ca56cedb8815c1f077ec9dc769ef7f02
LEAN_LINES: 1247

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.G6N1SelectedFerrersH2aSourceQuantities
  - Q3.Proofs.RouteB.G6N1ExplicitCCMLimitBeyondSourceWindowTail
  - Q3.Proofs.RouteB.D0PstarInversionCoefficientCrosswalk

PUBLIC_SURFACE:   # все 7 имён из вердикта
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalPreAnchorRank      # def, m_k − 2
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalSourceData_index_eq_preAnchorIndex
    # ЧИСТЫЙ rfl: Nat-sub дефеквивалентность сквозь приватный tail-shift
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalSourceData_pair_eq_preAnchorPair   # rfl
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalSourceData_sourceScale_eq_preAnchorScale  # rfl
  - Q3.RouteB.D0Pstar.selectedFerrersCofinalPreAnchorRank_tendsto  # mCofinal + omega
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMOddMass_eventually_le_log_div_sqrt_of_modeAndChiRates
    # ∃ C ≥ 0, ∀ᶠ k: η_k ≤ C·log(m_k)/√(m_k); C = 4(C1+C2)²/‖Ξ₀‖²
  - Q3.RouteB.D0Pstar.selectedFerrersFiniteCCMOddMass_tendsto_zero_of_modeAndChiRates
    # η_k → 0; squeeze через isLittleO_log_rpow_atTop (r = 1/2) ∘ m-кофинальность
  # hmode/hχ скопированы VERBATIM из
  # selectedFerrersCCMLemma73PreAnchorPort_of_modeAndChiRates; порт P
  # строится в let-биндере формы вердикта; никакого нового rate-объекта

PRIVATE_DECLARATIONS:
  - vanishing_unnormalized_error_without_anchor_does_not_control_normalized_oddMass_plant
    # REQUIRED: Fin 2, J = diag(1,−1), p_n = (0,1/(n+1)): unnormalized
    # норма → 0, но нормализация всегда (0,1) с odd mass 1
  - targetG / errVec            # inversion-even цель как Lp-элемент; s•gL − G
  - sourceScale_mul_coeff_diff  # решающее тождество: s·(c_n − c_{−n}) =
    # sT·(⟨V_n,e⟩ − ⟨V_{−n},e⟩); чётная цель сокращается через
    # inner_V_neg_eq_inner_V_of_inversion_even; строка НЕ симметризована
  - normSq_sub_le / sum_labels_inner_sq_le   # |a−b|² ≤ 2|a|²+2|b|²; Бессель
    # по инъективным label-семействам (±ccmModeFinite) через Finset.sum_image
  - oddMass_core_le             # η ≤ sT²/|s|² · ‖e‖² (дважды Бессель)
  - window_l2_integral_le       # ∫ normSq(err) d(du/u) ≤ Cf²/λ на I_m:
    # restrict_withDensity + integral_withDensity_eq_integral_toReal_smul +
    # мажоранта Cf²/λ²·u⁻² + integral_rpow(−2) — ровно O(1/λ), без log λ
  - errVec_norm_sq_le           # ‖e‖² = ∫ normSq через L2.inner_def +
    # integral_complex_ofReal; затем оконный интеграл
  - normalizer_ratio_le_of_anchor  # sT²/|s|² ≤ L_m/b² из якоря:
    # Gwin(0) = √L·⟨V₀,gL⟩, проекция сохраняет нулевую моду, Коши-Шварц
  - lambda_m_gen_pos/ge_one, Im_subset_Ioi, isFiniteMeasure_dStar_Im,
    continuousOn_G_Im, memLp_G, G_inversion_even, inner_V_P_eq,
    c_n_eq_sT_inner, label/neg_label/zero_mem_modeSet, L_m_pos
  - копии приватных upstream-блоков (decay chain 33/x⁴, E_star_norm_bound,
    continuity trio, E_star_four_mul_eq, lambda_paper_eq_lambda_m)

EXPECTED_AXIOM_PROFILES: >-
  все 6 публичных теорем и плант:
  [propext, Classical.choice, Quot.sound]

LEDGER:
  CLOSES:
    - SELECTED_FERRERS_FINAL_SHELL_TO_PREANCHOR_RANK_CROSSWALK
    - SELECTED_FERRERS_ODD_MASS_LOG_OVER_SQRT_RATE
    - SELECTED_FERRERS_ODD_MASS_DECAY
  OPENS: []

PROOF_ROUTE_AS_MANDATED:
  - "ask.sh преflight выполнен (пункт 1)"
  - "порт P построен из тех же hmode/hχ; формы теорем judge-verbatim (пункт 2)"
  - "rank m_k − 2 публичен; index/pair/sourceScale crosswalks — чистые rfl;
     rank кофинален (пункт 3, первый решающий гейт)"
  - "полный поточечный E⋆-error (C1+C2)/(λ√u): L73.3 main bound + L73.4
     точный сплит + tail bound, перенос eventual-σ→eventual-k через
     rank_tendsto.eventually (пункт 4)"
  - "квадрат проинтегрирован в точном dStar=du/u: O(1/λ), НЕ O(log λ/λ) —
     ∫u⁻² du = λ − λ⁻¹ ≤ λ (пункт 5)"
  - "цель фактор-четыре точно inversion-even через E_star_explicitCCMLimitH_inv;
     отражённые коэффициенты через inner_V_neg_eq_inner_V_of_inversion_even;
     строка НЕ симметризована (пункт 6)"
  - "нижний floor нормы: preAnchorGwin_zero_eq_sqrtL_mul_innerV0 +
     muntzLimit.tendsto_at(0) + centeredXi_zero_ne_zero ⇒ eventually
     ‖s·Gwin(0)‖ ≥ ‖Ξ₀‖/2 ⇒ |s|‖gN‖ ≥ ‖Ξ₀‖/(2√L); поточечный
     sourceScale_ne НЕ использован как floor (пункт 7)"
  - "дважды Бессель по точной selected-строке; масштаб сокращается:
     η ≤ sT²‖e‖²/|s|² ≤ (4L/‖Ξ₀‖²)·(Cf²/λ) (пункт 8)"
  - "m-кофинальность + log(m)/√m → 0 ⇒ публичный Tendsto (пункт 9)"
  - "#print axioms всех 6 публичных теорем и планта (пункт 10)"

FORBIDDEN_CHECK:
  ProlateCanonicalSourceData_substituted: no (selected shell только)
  rank_or_tail_shift_assumed_without_public_crosswalk: no (crosswalks rfl,
    первым блоком)
  odd_mass_decay_assumed: no (выведен)
  normalized_from_unnormalized_without_anchor: no (плант держит; якорь
    load-bearing)
  sourceScale_ne_as_uniform_bound: no (только муntz-предел при z=0)
  selected_row_symmetrized_or_even_projected: no
  factor_four_target_replaced: no
  unscaled_or_neighboring_target_packet: no (EStarMellinAbsolute-масштаб
    из FullEStarError verbatim)
  normalization_constant_fitted: no (C = 4(C1+C2)²/‖Ξ₀‖² выведен)
  residual_or_sector_floor_claims_added: no
  H2A_4_or_simple_ground_receiver_bundled: no
  H2A_0_H2A_1_H2A_2_L73_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 3 (Mathlib-переименования inv_le_inv₀/sqrt_le_left и
    isLittleO_log_rpow_atTop без Real-префикса; ae_restrict_iff'
    требовал MeasurableSet в I_m-форме; rw-глобальная замена λ под
    корнем — заменена sqrt_le_left; RCLike.ofReal_re не матчился на
    Complex-каст — закрыт simp; хвостовые ring после закрывающего
    field_simp убраны)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.G6N1SelectedFerrersOddMassDecay — Build completed successfully (7924 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/G6N1SelectedFerrersOddMassDecay.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: все 6 публичных + плант
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ (grep = 0)

SUCCESS_CODE: H2A_3_SELECTED_FERRERS_ODD_MASS_DECAY_LEAN
NEXT_LOAD_BEARING_GAP: H2A_4_SELECTED_FERRERS_RESIDUAL_RATE
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
