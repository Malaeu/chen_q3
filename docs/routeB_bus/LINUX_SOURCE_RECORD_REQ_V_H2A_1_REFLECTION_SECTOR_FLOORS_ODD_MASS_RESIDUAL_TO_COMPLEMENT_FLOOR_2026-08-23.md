# SOURCE RECORD — H2A.1 reflection sector floors, odd mass and residual → full complement floor (Linux-тело за Codex)

```yaml
PRIMARY: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR
DATE: 2026-08-23
BODY: Linux (Claude), standing owner grant; Codex недоступен
TASK: verdict 95d45029 — CODEX DIRECTIVE
MODE: ONE_GOAL_ONE_COMMIT
BASE_HEAD: 95d4502961b37bcd579b2a85037e8eb9f6d3d450
BASE_HEAD_PROVENANCE: git rev-parse HEAD, живой снимок перед созданием файла,
  перепроверен после q3_check перед коммитом; точный родитель

COMMIT: SAME_COMMIT_AS_THIS_RECORD

PREFLIGHT: "./ask.sh \"complexTrialComplementFloor reflection involution
  Hermitian sector floor odd mass\" exited 0 — существующий floor-предикат
  и receiver найдены (CCMProposition59ComplexTrialComplementFloor /
  ...ComplementSpectral); reflection-contamination теоремы в дереве НЕТ;
  имя свободно."

LEAN_PATH: q3.lean.aristotle/Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean
LEAN_GIT_BLOB: fe1f65d028002e11f404d46e2c05937f61ac33b1
LEAN_SHA256: 28c78e58692c1cdecf32a07c509fffd1881ad4dab9cbccf3ea0ad45b074f196f
LEAN_LINES: 800

SOURCE_RECORD_PATH: docs/routeB_bus/LINUX_SOURCE_RECORD_REQ_V_H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_2026-08-23.md
SOURCE_RECORD_GIT_BLOB: SELF_FIXED_BY_COMMIT_TREE

DIRECT_IMPORTS:
  - Q3.Proofs.RouteB.CCMProposition59ComplexTrialComplementFloor
    # (директива импорты не фиксировала; выбран минимальный носитель
    #  floor-предиката; matrix-involution API выбран напрямую — J как
    #  эрмитова матрица с J*J = 1, точная комплексная reflection-декомпозиция
    #  сделана в отдельном inner-space-ядре)

PUBLIC_SURFACE:
  - Q3.RouteB.complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual
    # ВСЕ 12 гипотез вердикта: конечный комплексный носитель (Fintype ι);
    # K эрмитова; J эрмитова унитарная инволюция (J*J = 1);
    # K*J = J*K; star q ⬝ᵥ q = 1; a вещественный сдвиг;
    # η = точная квадратная норма J-нечётной части q; 0 ≤ η < 1;
    # even-sector floor на векторах ⊥ чётной части q; odd-sector floor;
    # ρ ≥ 0 и ‖(K−a)q‖² ≤ ρ²; betaEff = min(βp,βm)(1−η) −
    #   ((2√η+η)/√(1−η))·ρ; 0 < betaEff.
    # ВЫВОД: complexTrialComplementFloor K q a betaEff — существующий
    # consumable-предикат, полный literal q-perp

PRIVATE_DECLARATIONS:
  - oddMass_without_residual_control_does_not_force_complementFloor_plant
    # REQUIRED: Fin 3; K = !![0,100,0;100,1,0;0,0,1], J = diag(1,1,−1),
    # q = ![60/61, 0, 11/61] (пифагорейская тройка 60-11-61 — все числа
    # рациональные), a = 0; βp = βm = 1 > 0; odd mass = 121/3721 < 1/25;
    # оба секторных пола выполнены; в literal q-perp вектор
    # v = ![11/61, −1, −60/61] с энергией −126879/3721 < 0.
    # Связь 100 внутри чётного сектора (trial-направление ↔ чётное
    # дополнение) рушит пол; без ρ-гипотезы теорема ложна
  - dot_eq_inner / dot_self_re_eq_norm_sq   # мост ⬝ᵥ ↔ EuclideanSpace inner
  - real_assembly    # финальная вещественная сборка, изолированная от
    # векторного контекста (полиномиальная арифметика остаётся малой)
  - core_contamination_bound  # inner-space ядро: P/M чётно-нечётные
    # проекторы; секторная ортогональность; Пифагор по чётности;
    # γ = ⟨q₊,v₊⟩ = −⟨q₋,v₋⟩; КЛЮЧЕВОЙ шаг d² ≤ η‖v‖² из
    # Коши-Шварца + нормировочного ограничения (d²(1−η) ≤ η‖v₋‖² ∧
    # ‖v₋‖² ≤ ‖v‖²−d²); резидуал-транспорт ‖S q₊‖ ≤ ρ (чётная часть
    # Sq); ‖S u‖ ≤ dρ/√(1−η); три contamination-члена через
    # re z ≥ −‖z‖ и симметрию S

EXACT_EFFECTIVE_FLOOR_VERBATIM: >-
  betaEff = min(betaPlus,betaMinus) * (1-eta)
    - ((2*sqrt(eta)+eta)/sqrt(1-eta)) * rho

EXPECTED_AXIOM_PROFILES:
  oddMass_without_residual_control_does_not_force_complementFloor_plant:
    - propext
    - Classical.choice
    - Quot.sound
  Q3.RouteB.complexTrialComplementFloor_of_reflectionSectorFloors_oddMass_residual:
    - propext
    - Classical.choice
    - Quot.sound

LEDGER:
  CLOSES:
    - REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_FULL_COMPLEMENT_FLOOR
  OPENS: []

PROOF_ROUTE:
  - "ask.sh преflight выполнен"
  - "плант исполнен ДО основной теоремы; отвергает residual-free
     формулировку точно (все не-резидуальные гипотезы выполнены, пол
     отрицателен)"
  - "ядро: точная комплексная reflection-декомпозиция; формула вердикта
     доказана ДОСЛОВНО — решающий шаг d² ≤ η‖v‖² (не η/(1−η)) из
     комбинации Коши-Шварца с ‖v₋‖² + d² + ‖w‖² = ‖v‖²"
  - "полный q-perp вывод: floor-предикат собран через проекторную
     арифметику (Q-аннигиляция q, эрмитовость, идемпотентность —
     локальные копии приватных upstream-хелперов)"
  - "#print axioms обеих деклараций"

FORBIDDEN_CHECK:
  thin_selected_wrapper_around_receiver: no (теорема generic, не wrapper)
  row_called_real_or_even_from_unit_norm: no
  q_replaced_by_even_projection: no (полный q-perp, плант чётности нет)
  exact_source_row_parity_assumed: no
  residual_or_coupling_input_dropped: no (ρ-гипотеза load-bearing, плант)
  full_qperp_floor_replaced_by_sector_only: no
  source_residual_replaced_by_fitted_operator_norm: no (ρ — гипотеза-параметр)
  fixed_shift_or_Rayleigh_proximity_input_introduced: no (a — свободный
    вещественный сдвиг)
  cofinal_floor_claimed: no
  simple_even_ground_claimed: no
  Theorem510_or_real_zeros_claimed: no
  H2A_0_or_L73_3_to_L73_8_edited: no
  paper_axiom_sorry_admit_hole_weakening: none

GATE:
  ROUNDS: 7 (RCLike/Complex re-коэрция в inner_self (exact
    inner_self_eq_norm_sq вместо cast-детура); WithLp/EuclideanSpace
    type-ascription → явный toLp-мост через EuclideanSpace.inner_toLp_toLp;
    rw-глобальная замена 1−η = √·√ портила вложенные корни — явные
    div_eq_div_iff шаги; whnf/isDefEq-таймауты от exact_mod_cast по
    PiLp-норме и от nlinarith на set-цепочке векторных атомов — финальная
    сборка вынесена в чисто вещественную real_assembly; rw-порядок
    S vp до vp; и одна не-Lean итерация: слово «admits» в докстринге
    валило q3_check-скан (→ «contains»). Предсказанный
    COMPLEX_REFLECTION_PROJECTOR_OR_SQRT_NORMAL_FORM сбой ВЫСТРЕЛИЛ:
    вся правка — projector/sqrt/коэрция-нормальные формы, ноль новой
    математики)
  VERIFICATION_HANDOFF:
    - "q3.lean.aristotle: lake env lean Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean — EXIT 0"
    - "q3.lean.aristotle: lake build Q3.Proofs.RouteB.CCMComplexTrialReflectionContaminationFloor — Build completed successfully (7795 jobs)"
    - "repo root: scripts/q3_check.sh Q3/Proofs/RouteB/CCMComplexTrialReflectionContaminationFloor.lean — q3_check ok, EXIT 0"
  AXIOM_PROFILES_OBSERVED: обе декларации
    [propext, Classical.choice, Quot.sound]; sorryAx НЕТ

SUCCESS_CODE: H2A_1_REFLECTION_SECTOR_FLOORS_ODD_MASS_RESIDUAL_TO_COMPLEMENT_FLOOR_LEAN
NEXT_LOAD_BEARING_GAP: SELECTED_FERRERS_SECTOR_FLOORS_ODD_MASS_RESIDUAL_RATE_SUPPLY
NEXT_AFTER_SEMANTIC_ADMISSION_ONLY: true
```
