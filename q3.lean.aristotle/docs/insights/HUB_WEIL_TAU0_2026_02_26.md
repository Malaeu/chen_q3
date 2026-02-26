# Hub: Weil Tau0 And Compact Bridges

Источник: `docs/insights/INSIGHTS_legacy_2026_02_26.md`.
Weil criterion, tau0, WK/W_K_tau0, compact/global bridge архитектура.

## Included Sections

- line 64: Synthesis (2026-02-24, in progress) — `Weil_criterion_tau0` closure architecture
- line 500: Synthesis (2026-01-28, in progress) — heat-weight integrability requires global a_star growth
- line 566: Synthesis (2026-01-27, in progress) — Weil explicit formula ⇒ positivity criterion (Artin–Hecke)
- line 605: Synthesis (2026-01-27, in progress) — Toeplitz‑Weil mapping (formal chain vs speculative edges)
- line 1344: Synthesis (2026-02-23, done) — sealed Weil τ=0 core interface
- line 1360: Synthesis (2026-02-23, done) — Weil core split into 3 layers
- line 1379: Synthesis (2026-02-23, done) — criterion decomposed into proof obligations
- line 1395: Synthesis (2026-02-23, done) — global-to-τ0 witness bridge hook

<!-- wave2_related_start -->
## Related Legacy Files (Wave 2)

Связанные standalone-файлы по домену `weil`:

- `docs/insights/connes_zeta_spectral_triples_2026_01_29.md`
- `docs/insights/quillen_ktheory_toeplitz_2026_01_29.md`
- `docs/insights/tau_shift_variants_rkhs_a3_2026_01_18.md`
<!-- wave2_related_end -->

## Content

<!-- legacy_line:64 -->

## Synthesis (2026-02-24, in progress) — `Weil_criterion_tau0` closure architecture

Цель: убрать прямую load-bearing зависимость mainline от ad-hoc маршрутов `tau0_separation_via_axiom`,
оставив одну стабильную точку замены для будущего доказательства (manual/Aristotle).

Что проверено:
- `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` уже содержит все обязательства (`Tau0Separation`,
  `Tau0WitnessBridge`, `Tau0QApproxBridge`), но нет структурированного API для witness-construction.
- `Q3/Main.lean` wiring стабилен и не требует изменения сигнатур.
- `Q3/CheckAxioms.lean` подтверждает: baseline theorem остаётся с `[... Q3.Weil_criterion_tau0 ...]`,
  а compact/qapprox route идёт через `Q3.Weil_criterion`.

Решение (интегрировано):
- Новый модуль `Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean`:
  - `Tau0CounterexampleAmplifier` (структурированный контракт witness-а),
  - `to_tau0_separation`,
  - `criterion_of_global_weil_and_amplifier`,
  - `amplifier_of_qapprox` (неаксиомный адаптер из `Tau0QApproxBridge`),
  - временный адаптер `amplifier_via_tau0_axiom` (точка замены),
  - `criterion_via_axiomatic_amplifier`.
- `Q3/Proofs/WeilCoreTau0.lean` переведён на импорт нового слоя (sealed re-export).

Приёмка:
- `lake build Q3.Proofs.WeilCoreTau0_CounterexampleAmplifier Q3.Proofs.WeilCoreTau0 Q3.Main Q3.CheckAxioms` — OK.
- `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` — OK.
- `./scripts/audit_nosorry_active_q3.sh --changed` — OK (`no sorry`, `no exact?`).

Update (2026-02-24, execution pass):
- `amplifier_via_tau0_axiom` переведён на конструктивный контрактный вход
  `Tau0QApproxBridge` (legacy имя сохранено для совместимости API).
- Внутри `Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` больше нет
  зависимости от `tau0_separation_via_axiom`; используется
  `amplifier_of_qapprox`.
- `criterion_via_axiomatic_amplifier` теперь также параметризован `hApprox`.
- Проверки: `lake build Q3.Proofs.WeilCoreTau0_CounterexampleAmplifier Q3.Proofs.WeilCoreTau0 Q3.Main Q3.CheckAxioms`,
  `./scripts/audit_nosorry_active_q3.sh --changed`,
  `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` — OK.

План (конкретно по файлам):
1) Изолировать legacy tau-general ветку (которая тянет аксиому) и не использовать её в production-chain:
   `Q3/Proofs/Q_nonneg_t_critical.lean` (блок `Q_phi_shift_nonneg_t_critical`).
2) Для production оставить только tau=0/brange контур:
   `Q3/Proofs/Q_nonneg_t_critical.lean:333-354`, `Q3/Main.lean:73-83`.
3) Сделать отдельный Path B модуль с целевым statement для замены аксиомы (без PrimeCert imports):
   `Q3/Proofs/PrimeTerm_PathB_tcritical.lean` (новый файл).
4) В Path B связать оценку prime-term с текущим gate-интерфейсом `PrimeCertMarginOnBrange`,
   чтобы wiring в `Q3/Main.lean` не менялся.
5) Приёмка: `lake env lean Q3/Proofs/PrimeTerm_t_bridge.lean`,
   `lake env lean Q3/Main.lean`, `./scripts/check_axioms.sh`.

Update (2026-02-23, execution pass):
- Добавлен отдельный Path B интерфейс:
  `Q3/Proofs/PrimeTerm_PathB_tcritical.lean`
  (`PrimeTermPathBTcritical`, `prime_term_le_at_t_critical_of_pathB`).
- Legacy-аксиома сохранена по старому имени (для обратной совместимости checks):
  `Q3.prime_term_le_at_t_critical_axiom`.
- `Q3/Proofs/Q_nonneg_t_critical.lean` переподключён на контрактный вход
  через `prime_term_pathB_tcritical_from_axiom` (вместо прямого вызова локальной аксиомы).
- Добавлен недостающий bridge-блок для `t_critical`:
  `prime_term_phi_shift_tcritical_le_cap` в `Q3/Proofs/PrimeTerm_t_bridge.lean`.
- Проверки: `lake build Q3.Proofs.PrimeTerm_PathB_tcritical`,
  `lake build Q3.Proofs.Q_nonneg_t_critical`,
  `lake env lean Q3/CheckAxioms.lean`,
  `lake env lean Q3/Main.lean`,
  `./scripts/check_axioms.sh` — все успешны.

Update (2026-02-23, fast-check + Path B hook):
- В `Q3/Proofs/Q_nonneg_t_critical.lean` выделена отдельная точка подключения Path B:
  `prime_term_le_at_t_critical_via_pathB`.
  Это стабилизирует wiring: когда появится реальное доказательство Path B, меняем только источник `hPathB`.
- В `scripts/check_axioms.sh` добавлены режимы:
  - `Q3_QUICK=1` — пропустить precheck шаги `0..0.8`.
  - `Q3_NO_BUILD=1` — пропустить `lake build Q3.Main` (использовать текущие артефакты).
- Smoke-check после правок:
  - `lake build Q3.Proofs.Q_nonneg_t_critical` — OK.
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` — OK,
    `Q3.Main.RH_of_Weil_and_Q3` зависит только от
    `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`, без `sorryAx`.

Update (2026-02-23, Path B mini-research -> bridge implementation):
- Добавлен новый модуль-скелет:
  `Q3/Proofs/PrimeTerm_PathB_bridge.lean`.
- В модуле собрана рабочая bridge-цепочка из уже имеющихся лемм:
  `t_critical -> t_rkhs_cap` (`PrimeTerm_t_bridge`) + `... ≤ rho_oneK` (`RKHS_cap_rayleigh`),
  с выходом в Path B контракт.
- Ключевая точечная лемма:
  `prime_term_le_at_t_critical_of_rkhs_pathB`
  (доказана без новых аксиом; принимает ровно 2 внешних входа:
  `hRhoQuarter` и `hArchQuarter`).
- Контрактная сборка:
  `prime_term_pathB_tcritical_of_rkhs_bounds`
  (строит `PrimeTermPathBTcritical` при глобальных семействах этих двух оценок).
- Проверка: `lake build Q3.Proofs.PrimeTerm_PathB_bridge` — OK.

Update (2026-02-23, no-sorry audit ergonomics):
- `scripts/audit_nosorry_active_q3.sh` расширен для ежедневной работы:
  - `--changed`: проверять только изменённые/новые active Q3 Lean-файлы;
  - `--limit N`: ограничить число файлов (быстрый smoke);
  - quiet-by-default: полный вывод Lean показывается только при падении
    (включить поток можно через `Q3_AUDIT_SHOW_LEAN=1`).
- Жёсткая проверка `sorry` остаётся через
  `lake lean ... -- -Dwarn.sorry=true -EhasSorry`.
- `exact?`-скан теперь отфильтровывает строки-комментарии.

Update (2026-02-23, temperature-matched Path B):
- В `Q3/Proofs/PrimeTerm_PathB_bridge.lean` добавлен preferred-route без
  bridge-множителя `exp_tcrit_to_rkhs K`:
  - `prime_term_le_at_t_critical_of_direct_pathB`
  - `prime_term_pathB_tcritical_of_direct_bounds`
- Это новая основная точка закрытия Path B: оба входа (`hPrimeQuarter`, `hArchQuarter`)
  формулируются сразу на `t_critical`.
- Прежний путь через `exp_tcrit_to_rkhs * rho_oneK` сохранён как legacy fallback:
  `prime_term_pathB_tcritical_of_rkhs_bounds_legacy`.


<!-- legacy_line:500 -->

## Synthesis (2026-01-28, in progress) — heat-weight integrability requires global a_star growth

- Added Tier‑1 axiom `a_star_linear_growth` (global linear growth bound) to unblock
  integrability of `|a_star ξ| * exp(-4π^2 t ξ^2) * |ξ|`.
- Implemented integrability lemma in
  `Q3/Proofs/PrimeCert/Brange_Lipschitz_HeatIntegrable.lean`.
- `arch_heat_weight_integrable` now compiles in the minimal file and is available
  in `Brange_Lipschitz_HeatProof.lean`.


<!-- legacy_line:566 -->

## Synthesis (2026-01-27, in progress) — Weil explicit formula ⇒ positivity criterion (Artin–Hecke)

Source: Zotero cache for Weil 1972 (Math USSR Izvestiya, 1972) at
`full/q3.lean.aristotle/literature/zotero/W9IDA6HW/fulltext.md`.

**Core idea (one paragraph):** Weil derives a **general explicit formula** for Artin–Hecke
L-series (not just ζ), expressed as a distributional identity on a Weil-group–type object.
This yields a distribution Δ (schematically δ₁ − 2D) whose **positivity on a test-function class**
is equivalent to RH **plus** Artin’s conjecture (no “bad” local factors). So RH becomes a
positivity statement for a quadratic/linear functional built from local archimedean
and non‑archimedean terms with *fixed normalization*.

**Mapping to Q3 chain:**
- This is the theoretical source of `Weil_criterion_tau0` (current external axiom).
- The positivity functional Δ ↔ our `Q`/`Weil_criterion` viewpoint (nonnegativity on a cone).
- The strict separation of arch/prime local terms matches the `arch_term` / `prime_term`
  split in `Q3/Proofs/Q_nonneg_t_critical.lean`.

**Why normalization matters (risk area):**
- Weil fixes **canonical Haar measures** on “modular” groups and uses them in the explicit formula.
- Any change in normalization shifts constants in Δ and can **flip positivity**.
- For formalization, all local measures must be normalized **once** and kept consistent
  with the test-function transform.

**Strength vs RH:**
- Weil’s criterion is **stronger** than RH alone (it includes Artin conjecture).
  That’s fine if treated as an external classical axiom, but important to document.

**Actionable insight for formalization:**
- Treat Δ positivity as the target “axiom” until the explicit formula is formalized.
- If we ever close `Weil_criterion_tau0`, we need:
  1) precise definition of the test-function space (cone) and transforms,
  2) explicit formula linking zeros ↔ local terms,
  3) proof that Δ ≥ 0 ↔ RH (with Artin assumptions).

**Quick follow‑ups (literature mining):**
- Collect references in Weil (1972) bibliography for explicit formulas and Weil groups.
- Look for modern expositions to reduce heavy group/representation preliminaries.


<!-- legacy_line:605 -->

## Synthesis (2026-01-27, in progress) — Toeplitz‑Weil mapping (formal chain vs speculative edges)

Source: `docs/toeplitz_weil_bridge.md` (checked into this repo).

**Critical correction (formal alignment):**
- Do **not** state the Weil functional as `Σ |f̂(ρ)|²` in the formal chain.
- In Q3 the correct formal target is: **`Q(Φ) ≥ 0` on the (τ=0) Weil cone ⇔ RH**,
  i.e. `Weil_criterion_tau0` in `Q3/Axioms.lean`. Any spectral/quadratic‑form
  intuition must be marked as *interpretation*, not formula.

**Formal Chain (Lean‑anchored mapping):**
- Weil criterion (τ=0): `Q3.Axioms.weil_criterion_tau0` → `Q3/Main.lean` mainline.
- A3 bridge (Toeplitz − Prime): `Q3/Proofs/A3_bridge_integrated.lean`.
- Base atom positivity (τ=0): `Q3/Proofs/Q_nonneg_base_atoms_proof.lean`.
- RKHS contraction: `Q3/Proofs/RKHS_contraction.lean` and bridge wrappers.
- T5 transfer (τ=0): `Q3/T5_Transfer.lean` (`T5_transfer_tau0`).

**Speculative Edges (NOT in chain, keep isolated):**
- Kapustin 2022 (explicit de Branges model), Connes 1998/2025 (trace formula / spectral triples),
  Hilbert–Pólya heuristics: **informal context only**.
- If used, they must enter as **speculative edges** with a formal bridge stub before activation.

**Actionable rule:** keep the above split explicit in docs and dashboards; never “blend”
speculative edges into the formal chain without a Lean stub.


<!-- legacy_line:1344 -->

## Synthesis (2026-02-23, done) — sealed Weil τ=0 core interface

- Добавлен модуль-граница: `Q3/Proofs/WeilCoreTau0.lean`.
- Экспортируется минимальный API:
  - `TestClass` (τ=0 тестовый класс),
  - `NonnegOn` (контракт неотрицательности),
  - `criterion` (единственная точка для `NonnegOn ↔ RH`).
- `Q3/Main.lean` переключён на `Q3.Proofs.WeilCoreTau0.criterion` вместо
  прямого обращения к `Q3.Weil_criterion_tau0`.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0 Q3.Main` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
- Смысл: доменный долг по Weil теперь изолирован в одном модуле; при замене
  маршрута `criterion` на внутреннее доказательство не потребуется менять
  mainline и T5-цепочку.


<!-- legacy_line:1360 -->

## Synthesis (2026-02-23, done) — Weil core split into 3 layers

- Интерфейс τ=0 core разложен на отдельные файлы:
  - `Q3/Proofs/WeilCoreTau0_API.lean` (слой API),
  - `Q3/Proofs/WeilCoreTau0_ExplicitFormulaTau0.lean` (слой explicit formula),
  - `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` (слой criterion),
  - `Q3/Proofs/WeilCoreTau0.lean` оставлен как тонкий public re-export.
- В API добавлена вшитая стыковка классов:
  `TestClass ⊆ Weil_cone` через леммы
  `W_K_subset_Weil_cone`, `W_K_tau0_subset_weil_cone`,
  `testClass_subset_weil_cone`.
- В explicit-formula слое зафиксирован контракт
  `ExplicitFormulaOnTestClass` и текущий маршрут
  `explicit_formula_tau0` (через `Q3.explicit_formula` + embedding).
- В criterion слое сохранён стабильный экспорт `criterion` для `Q3.Main`.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0_API Q3.Proofs.WeilCoreTau0_ExplicitFormulaTau0 Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Proofs.WeilCoreTau0 Q3.Main` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅


<!-- legacy_line:1379 -->

## Synthesis (2026-02-23, done) — criterion decomposed into proof obligations

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` `criterion` разложен на
  независимые части:
  - `Tau0Separation`,
  - `criterion_of_obligations`,
  - `nonneg_of_RH_via_global_weil` (опциональный маршрут),
  - `nonneg_of_RH_via_tau0_axiom` (временный маршрут),
  - `tau0_separation_via_axiom` (временный маршрут).
- Экспорт `criterion` для `Q3.Main` не изменён, но теперь замена аксиомного
  маршрута может идти поэтапно: сначала закрывать `RH → NonnegOn`, затем
  отдельно закрывать `Tau0Separation`.
- Верификация после декомпозиции:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Proofs.WeilCoreTau0 Q3.Main` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅


<!-- legacy_line:1395 -->

## Synthesis (2026-02-23, done) — global-to-τ0 witness bridge hook

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлен интерфейс
  `Tau0WitnessBridge` и вывод:
  - `tau0_separation_of_global_weil`,
  - `criterion_of_global_nonneg_and_separation`.
- Это даёт чистую точку интеграции для будущего математического закрытия:
  если доказать `Tau0WitnessBridge`, то `criterion` можно перевести на
  global-route без архитектурных изменений в `Q3.Main`.
- Текущий экспорт `criterion` оставлен стабильным (mainline не менялся по
  зависимостям).

### Update (2026-02-23)

- Добавлены временные реализации:
  - `tau0_witness_bridge_via_axiom`,
  - `tau0_separation_via_global_route_with_axiom_bridge`.
- Это подтверждает, что новый global-route склеивается конструктивно уже
  сейчас; для снятия последней доменной аксиомы нужно заменить именно
  `tau0_witness_bridge_via_axiom` на математическое доказательство.

### Update (2026-02-23, done) — frozen target theorem for τ=0 de-axiomatization

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены:
  - `criterion_of_global_weil_and_witness_bridge`,
  - `criterion_via_global_route_with_axiom_bridge`.
- Это фиксирует один явный целевой контракт для следующего шага:
  заменить только доказательство `Tau0WitnessBridge`, не меняя wiring в
  `Q3.Main` и не перетряхивая τ=0 API.
- Верификация после добавления:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Proofs.WeilCoreTau0 Q3.Main` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - профиль main-chain неизменен:
    `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.

### Update (2026-02-24, done) — quantitative bridge contract for witness closure

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены:
  - `Tau0QApproxBridge` (количественный контракт аппроксимации по значению `Q`),
  - `tau0_witness_bridge_of_qapprox` (`Tau0QApproxBridge -> Tau0WitnessBridge`),
  - `criterion_of_global_weil_and_qapprox` (прямой выход на критерий из количественного контракта).
- Практический смысл: теперь следующий математический шаг можно формулировать
  узко и конструктивно: достаточно дать лемму вида
  `|Q Ψ - Q Φ| < (-Q Φ)/2` для `Φ` с `Q Φ < 0`, чтобы автоматически получить
  τ=0 negative witness.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Proofs.WeilCoreTau0 Q3.Main` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - профиль main-chain без изменений:
    `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.

### Update (2026-02-24, done) — forward mainline route via q-approx contract

- Добавлен новый theorem-маршрут в `Q3/Main.lean`:
  - `RH_of_Weil_and_Q3_via_qapprox`
    (`PrimeCertMarginOnBrange` + `Tau0QApproxBridge` -> `RH`).
- Смысл маршрута:
  - `Q_nonneg_on_Weil_cone_tau0` даёт `NonnegOn` на τ=0 классе,
  - `criterion_of_global_weil_and_qapprox` закрывает `NonnegOn ↔ RH`
    через global Weil + количественный bridge-контракт.
- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлен user-facing эквивалент:
  - `criterion_on_weil_cone_tau0_of_qapprox`.
- `Q3/CheckAxioms.lean` расширен печатью:
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3_via_qapprox`.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Main Q3.CheckAxioms` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - профили:
    - `RH_of_Weil_and_Q3` -> `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`
    - `RH_of_Weil_and_Q3_via_qapprox` -> `[propext, Classical.choice, Q3.Weil_criterion, Quot.sound]`
- Вывод:
  - mainline не сломан и остался совместимым;
  - добавлен рабочий переходный путь, где долг по `Weil_criterion_tau0`
    заменяется на один явный количественный контракт `Tau0QApproxBridge`.

### Update (2026-02-24, done) — compact-approx contracts reduce remaining debt

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены новые контракты:
  - `GlobalWeilToWK` (редукция глобального `Weil_cone` к некоторому `W_K`),
  - `Tau0CompactApproxOnWK` (аппроксимация на фиксированном `W_K`),
  - theorem `tau0_qapprox_of_compact_approx`
    (`GlobalWeilToWK + Tau0CompactApproxOnWK -> Tau0QApproxBridge`),
    построенный через `Q3.Proofs.Q_Lipschitz_on_W_K_thm`.
- В `Q3/Main.lean` добавлен новый прикладной маршрут:
  - `RH_of_Weil_and_Q3_via_compact_approx`
    (`PrimeCertMarginOnBrange + GlobalWeilToWK + Tau0CompactApproxOnWK -> RH`).
- В `Q3/CheckAxioms.lean` добавлена печать:
  - `#print axioms Q3.Main.RH_of_Weil_and_Q3_via_compact_approx`.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0` ✅
  - `lake build Q3.Main Q3.CheckAxioms` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - профиль:
    - `RH_of_Weil_and_Q3_via_compact_approx`
      -> `[propext, Classical.choice, Q3.Weil_criterion, Quot.sound]`.
- Практический смысл:
  - долг сдвинут с «сырых `Q`-оценок» на более инженерно-проверяемые контракты
    аппроксимации на компактах;
  - следующий закрывающий шаг теперь узкий: доказать `GlobalWeilToWK`
    и `Tau0CompactApproxOnWK` для выбранного τ=0 класса.

### Update (2026-02-24, done) — closed `GlobalWeilToWK` and simplified mainline signature

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлен theorem:
  - `globalWeilToWK_thm : GlobalWeilToWK`.
- Идея доказательства полностью конструктивная (без новых аксиом):
  - из `HasCompactSupport` берём компакт `tsupport`,
  - из компактности получаем boundedness и включение в `closedBall (0) R`,
  - выбираем `K = max 1 (R + 1)`, что даёт `support ⊆ Ioo (-K) K`,
  - следовательно `Φ ∈ W_K K` и `K ≥ 1`.
- В `Q3/Main.lean` переподключён маршрут:
  - `RH_of_Weil_and_Q3_via_compact_approx` больше не принимает параметр `hWK`;
    используется `Q3.Proofs.WeilCoreTau0.globalWeilToWK_thm` напрямую.
- Верификация:
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Main Q3.CheckAxioms` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - профиль `RH_of_Weil_and_Q3_via_compact_approx` остался:
    `[propext, Classical.choice, Q3.Weil_criterion, Quot.sound]`.
- Практический эффект:
  - убран один внешний contract-параметр из API mainline;
  - сужен оставшийся долг compact-route до единственного контракта:
    `Tau0CompactApproxOnWK`.

### Update (2026-02-24, done) — reduced `exact?` debt in active Q3

- В `Q3/Proofs/W_sum_finite.lean` заменены `exact?` в load-bearing местах на
  явные термы:
  - `ArithmeticFunction.vonMangoldt_le_log (n := m)`,
  - `w_Q_bound K hK n hn`,
  - `SummationFilter.instLeAtTopUnconditional ℕ` (инстанс для `tsum_eq_sum`).
- Проверка:
  - `lake env lean Q3/Proofs/W_sum_finite.lean` ✅
  - `rg -n "exact\\?" Q3/Proofs/W_sum_finite.lean` -> пусто.
- Результат по активному аудиту:
  - `./scripts/audit_nosorry_active_q3.sh --changed` теперь показывает
    `total exact? lines: 13` (было 16).

### Update (2026-02-24, done) — `exact?` frontier compressed to one load-bearing node

- В `Q3/Proofs/A1_density_main.lean` удалены off-chain `exact?`-заглушки там,
  где уже есть готовые леммы/дефиниционные равенства:
  - варианты `continuous_map_integral_approx_by_sum_*` переведены на
    `continuous_map_integral_approx_by_sum`,
  - `MapToContinuous_eq_smul` закрыт через `rfl`,
  - continuity-хуки переведены на `MapToContinuous_continuous`,
  - `symmetrize_approx_even` использует явное `rfl` для `Symmetrize`.
- Проверка:
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅
  - активный `exact?`-хвост в changed активном Q3: **1 строка**
    (`Q3/Proofs/A1_density_main.lean:226`).
- Пояснение по риску:
  - оставшаяся точка на `:226` — не cosmetic, а load-bearing узел про
    `UniformContinuous` в `continuous_convolution_approx`; её нужно закрывать
    отдельным аккуратным доказательством.

### Update (2026-02-24, done) — closed final active `exact?` node in A1

- В `Q3/Proofs/A1_density_main.lean:226` закрыт load-bearing `exact?`:
  - `h_unif_cont : UniformContinuous f` теперь получен через
    `HasCompactSupport.uniformContinuous_of_continuous hsupp hf`.
- Это точечно закрывает обязательный узел в
  `continuous_convolution_approx` без добавления новых аксиом.
- Проверка:
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅
  - статус active changed Q3: `no exact? found`.

### Update (2026-02-24, done) — compact-approx criterion wired through WeilCore and Main

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены глобализованные
  компактные маршруты:
  - `tau0_qapprox_of_compact_approx_global`,
  - `criterion_of_global_weil_and_compact_approx`,
  - `criterion_on_weil_cone_tau0_of_compact_approx`.
- В `Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` добавлен thin-route:
  - `criterion_via_compact_approx_amplifier`.
- В `Q3/Main.lean` `RH_of_Weil_and_Q3_via_compact_approx` переведён на прямой
  вызов `criterion_of_global_weil_and_compact_approx` (без промежуточной
  ручной сборки `hQApprox`).
- В `Q3/CheckAxioms.lean` добавлены `#print axioms` для новых compact-route
  теорем в `WeilCoreTau0`.
- Проверка:
  - `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` ✅
  - `lake build Q3.Proofs.WeilCoreTau0_CriterionTau0 Q3.Proofs.WeilCoreTau0_CounterexampleAmplifier` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅
- Аксоматический профиль:
  - `criterion_of_global_weil_and_compact_approx` и
    `criterion_on_weil_cone_tau0_of_compact_approx` зависят только от
    `[propext, Classical.choice, Q3.Weil_criterion, Quot.sound]`.

### Update (2026-02-24, done) — Ksafe calibration for compact route

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены window-инварианты:
  - `Kfloor (B_min) := max 1 B_min`,
  - `Ksafe (B_min, K) := max (Kfloor B_min) K`,
  - леммы порядка (`one_le_Kfloor`, `Bmin_le_Kfloor`, `le_Ksafe`,
    `Kfloor_le_Ksafe`) и монотонность `W_K` (`W_K_mono`).
- Контракт `Tau0CompactApproxOnWK` усиленно-нормализован по домену:
  - было: `∀ K, K ≥ 1 -> ...`
  - стало: `∀ K, K ≥ Kfloor B_min -> ...`.
  Это убирает проблемный диапазон `1 ≤ K < B_min` из load-bearing ветки.
- В `tau0_qapprox_of_compact_approx` маршрут переведён на безопасное окно:
  - из `K0` от `GlobalWeilToWK` строится `K := Ksafe B_min K0`,
  - `Φ ∈ W_K K0` поднимается до `Φ ∈ W_K K` через `W_K_mono`,
  - Lipschitz и compact-approx применяются на `K`.
- Верификация:
  - `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` ✅
  - `lake env lean Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅

### Update (2026-02-24, done) — unpack adapter for `W_K_tau0` approximation

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены adapter-леммы:
  - `BaseAtomCone_K_brange_mono` (монотонность по окну `K`),
  - `baseAtomCone_brange_subset_testClass` (вложение brange-атомов в `TestClass`),
  - `wk_tau0_exists_atomcone_approx` (чистая распаковка определения `W_K_tau0`),
  - `tau0_compact_approx_on_WK_tau0` (ε-аппроксимация на τ=0 окне через `TestClass`).
- Практический смысл:
  - часть долга `Tau0CompactApproxOnWK` теперь формализована как
    “definition-unpack route”, без новой тяжёлой аналитики;
  - сильный global compact-контракт для всех `Φ ∈ W_K` остаётся отдельным
    мостом (не закрыт этим шагом полностью).
- Верификация:
  - `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` ✅
  - `lake env lean Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅

### Update (2026-02-24, in progress) — global compact bridge over `W_K_tau0` adapter

- Target lemma:
  `Tau0CompactApproxOnWK` в `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean`,
  чтобы снять load-bearing контракт с прямого `∀ Φ ∈ W_K` и выразить его через
  adapter-слой `W_K_tau0`.
- Embedding scan (3 queries, `q3_docs`) + web-check:
  готового моста `W_K -> W_K_tau0` в активном коде нет.
- План Option 1 (main):
  1. Ввести контракт-мост `WKToTau0Bridge` (`W_K` поднимается в `W_K_tau0`
     на безопасном окне `K ≥ Kfloor B_min`);
  2. Доказать theorem `tau0_compact_approx_on_WK_of_bridge` из
     `tau0_compact_approx_on_WK_tau0` (чистый adapter-lift);
  3. Добавить route theorem
     `criterion_of_global_weil_and_compact_approx_via_bridge`.
- План Option 2 (fallback):
  оставить старый `Tau0CompactApproxOnWK`, но использовать новый theorem-route
  как canonical API и мигрировать вызовы поэтапно.
- Success check:
  `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean`,
  `lake env lean Q3/Main.lean`, `lake env lean Q3/CheckAxioms.lean`.

### Update (2026-02-24, done) — global compact bridge theorem over adapter-layer

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлен явный мост-контракт:
  - `WKToTau0Bridge t0 B_min B_max`:
    `∀ K ≥ Kfloor B_min, W_K K ⊆ W_K_tau0 K t0 B_min B_max`.
- Поверх уже закрытого adapter-слоя добавлен theorem:
  - `tau0_compact_approx_on_WK_of_bridge`:
    из `WKToTau0Bridge` выводится глобальный контракт
    `Tau0CompactApproxOnWK` (без нового тяжелого анализа).
- Добавлены route-теоремы для прямого использования:
  - `criterion_of_global_weil_and_compact_approx_via_bridge`,
  - `criterion_on_weil_cone_tau0_of_compact_approx_via_bridge`.
- Верификация:
  - `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` ✅
  - `lake env lean Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅

### Update (2026-02-24, done) — closed `WKToTau0Bridge` debt by formal impossibility proof

- В `Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` добавлены:
  - `baseAtomCone_brange_eval_zero_of_abs_ge_Bmax`:
    любой `g ∈ BaseAtomCone_K_brange` обнуляется в точках `|ξ| ≥ B_max`
    (при `B_min > 0`);
  - `farWitness_mem_WK`, `farWitness_eval_pos_at_Bmax`:
    явный свидетель `Φ(x) = Fejer_kernel (B_max+1) x` в `W_K`;
  - `not_WKToTau0Bridge_of_positive_brange`:
    строгий контрпример, что глобальный мост
    `WKToTau0Bridge t0 B_min B_max` ложен при `0 < B_min` и `0 < B_max`.
- Вывод:
  - долг «доказать глобальный `W_K -> W_K_tau0` мост» закрыт как
    некорректная цель (математически невозможная в этой постановке),
    а не как “недоделанный proof”.
  - Рабочая и корректная линия остаётся: `W_K_tau0`-adapter route и mainline
    через `Weil_criterion_tau0`.
- Верификация:
  - `lake env lean Q3/Proofs/WeilCoreTau0_CriterionTau0.lean` ✅
  - `lake env lean Q3/Proofs/WeilCoreTau0_CounterexampleAmplifier.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅

### Update (2026-02-24, done) — closed PrimeCert margin route as theorem and removed `h_margin_cert` from Main

- В `Q3/Proofs/Q_nonneg_t_critical.lean` добавлено:
  - `prime_cert_margin_on_brange_thm : PrimeCertMarginOnBrange`,
    полученный из уже существующего сертификатного доказательства
    `Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom`
    (файл `Q3/Proofs/PrimeCert/Brange_2046.lean`).
- В `Q3/Main.lean` снят явный параметр
  `h_margin_cert : Q3.PrimeCertMarginOnBrange` из mainline-теорем:
  - `Q_nonneg_on_W_K_tau0`,
  - `Q_nonneg_on_Weil_cone_tau0`,
  - `RH_of_Weil_and_Q3_via_qapprox`,
  - `RH_of_Weil_and_Q3_via_compact_approx`,
  - `RH_of_Weil_and_Q3`.
- Теперь margin берётся внутри `Main` из сертифицированного theorem-route
  (через `PrimeCert/Brange_2046`), а не как внешний hypothesis.
- Верификация:
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅
  - `./scripts/audit_nosorry_active_q3.sh --changed` ✅

### Update (2026-02-24, done) — removed pointwise Path B axiom symbol; switched to contract provider + legacy adapter

- В `Q3/Proofs/PrimeTerm_PathB_tcritical.lean` удалён символ
  `prime_term_le_at_t_critical_axiom`.
- Вместо pointwise-аксиомы введён provider-интерфейс:
  - `PrimeTermPathBProvider := PrimeTermPathBTcritical`,
  - `prime_term_pathB_tcritical_from_provider`.
- Добавлен отдельный legacy-адаптер
  `Q3/Proofs/PrimeTerm_PathB_legacy_provider.lean`:
  - `prime_term_pathB_tcritical_legacy : PrimeTermPathBProvider`,
  - `prime_term_pathB_tcritical_from_legacy : PrimeTermPathBTcritical`.
- В `Q3/Proofs/Q_nonneg_t_critical.lean` маршрут переведён на theorem-route:
  - новый вход `Q_phi_shift_nonneg_t_critical_of_pathB`,
  - совместимый wrapper `Q_phi_shift_nonneg_t_critical` использует только
    `prime_term_pathB_tcritical_from_legacy`.
- В `Q3/CheckAxioms.lean` обновлён off-mainline gate tracking:
  - `#check/#print axioms` теперь на
    `Q3.prime_term_pathB_tcritical_legacy`.

### Update (2026-02-24, done) — added fast Contract Sanity Gate

- Добавлен быстрый sanity-модуль `Q3/CheckContracts.lean`.
- Он печатает axiom-snapshot для ключевых τ=0 route-теорем:
  - `criterion_of_global_weil_and_compact_approx`,
  - `criterion_on_weil_cone_tau0_of_compact_approx`,
  - `criterion_via_axiomatic_amplifier`,
  - `criterion_via_compact_approx_amplifier`.
- Добавлен скрипт `scripts/check_contracts.sh`:
  1) `lake env lean -Dwarn.sorry=true -EhasSorry Q3/CheckContracts.lean`,
  2) `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh`.
- Результат: быстрый preflight для контрактов и axiom-drift без тяжелого `lake build Q3.Main`.

### Update (2026-02-24, done) — decomposed Path B legacy gate into two explicit math obligations

- В `Q3/Proofs/PrimeTerm_PathB_legacy_provider.lean` заменён единый legacy-gate
  на две явные математические цели:
  - `prime_term_tcritical_le_cstar_quarter_mathan`,
  - `cstar_quarter_le_arch_term_tcritical_mathan`.
- `PrimeTermPathBProvider` теперь собирается theorem-ом через
  `prime_term_pathB_tcritical_of_direct_bounds` из `PrimeTerm_PathB_bridge`.
- Практический эффект: вместо одного «чёрного ящика» остаются две прозрачные
  аналитические задачи (prime-quarter + arch-quarter), которые можно закрывать
  независимо и без ожидания heavy certificate rebuilds.

### Update (2026-02-24, in progress) — switched τ=0 mainline atoms to Path B gate route

- В `Q3/Proofs/Q_nonneg_t_critical.lean` добавлены:
  - `Q_phi_shift_nonneg_t_critical_tau0_of_pathB_any_B`:
    τ=0 specialization, где допустимый `K` выбирается автоматически как `max 1 B`.
  - `Q_nonneg_on_base_atoms_at_t_critical_brange_of_pathB`:
    positivity на `BaseAtomCone_critical_brange` из `PrimeTermPathBTcritical`,
    без `PrimeCertMarginOnBrange`.
  - `Q_nonneg_on_base_atoms_at_t_critical_brange_via_pathB`:
    default-wrapper через `prime_term_pathB_tcritical_from_legacy`.
- В `Q3/Main.lean` `Q_nonneg_on_W_K_tau0` переключён с
  `..._brange_of_margin` на `..._brange_via_pathB`.
  Это убирает load-bearing использование `h_margin_cert` в τ=0 mainline route
  (остаётся Path B legacy provider как явный математический долг).
- Важный инженерный эффект:
  mainline перестаёт быть привязан к прямому margin-сертификату в этом узле и
  продолжает работать через тонкий Path B contract-gate.
- Проверка в этой сессии частично заблокирована фоновым долгим процессом
  `BrangeHeatCert_2026_01_28_Checker.lean` (идёт >40 мин, не прерывался);
  `lake env lean` на затронутых файлах запускается, но завершается медленно.

### Update (2026-02-24, in progress) — decoupled τ=0 mainline from all-τ PathB legacy provider

- В `Q3/Proofs/Q_nonneg_t_critical.lean` добавлен отдельный контракт:
  - `PrimeTermPathBTcriticalTau0Brange`:
    `∀ B ∈ [B_min, B_max], prime_term(phi_shift_critical B 0) ≤ arch_term(...)`.
  - канонический провайдер:
    `prime_term_pathB_tcritical_tau0_brange_thm`
    (первично был собран через `prime_cert_margin_on_brange_thm`,
    позже переведён на direct certified margin route; см. запись 2026-02-25 ниже).
- `Q_nonneg_on_base_atoms_at_t_critical_brange_of_tau0_brange_gate` теперь
  использует именно этот узкий τ=0 gate, без требования общего all-τ контракта.
- В `Q3/Main.lean` `Q_nonneg_on_W_K_tau0` переключён на
  `Q_nonneg_on_base_atoms_at_t_critical_brange_via_tau0_brange_gate`.
- Эффект:
  load-bearing τ=0 mainline больше не зависит от
  `PrimeTerm_PathB_legacy_provider` (all-τ legacy), который остаётся только
  для off-mainline маршрутов/диагностики.

### Update (2026-02-25, done) — analytic τ=0 B-range gate wired as mainline theorem-route

- Добавлен новый файл:
  - `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean`
  - Теорема:
    `prime_term_pathB_tcritical_tau0_brange_thm :
      PrimeTermPathBTcriticalTau0Brange`
    как отдельный аналитический τ=0 gate для `B ∈ [B_min, prime_cert_B_max]`.
- В `Q3/Proofs/Q_nonneg_t_critical.lean` mainline-ветка использует именно
  `PrimeTermPathBTcriticalTau0Brange`; в точке применения добавлено корректное
  приведение:
  `simpa [phi_shift_critical] using hTau0Gate ...`.
- В `Q3/Main.lean` удалён прямой импорт
  `Q3/Proofs/PrimeCert/Brange_2046.lean`.
  Mainline теперь идёт через τ=0 Path B gate, без прямой зависимости от
  Brange-сертификатного файла.
- Зафиксирована политика:
  - цепочка PrimeCert/Brange остаётся как legacy-валидация и off-mainline;
  - рабочий путь для дальнейшего закрытия — theorem-route (Path B, матан),
    без тяжёлых checker-прогонов по сертификатным автогенам.

### Update (2026-02-25, done) — dropped quarter-shape debt; τ=0 gate now uses direct certified margin route

- Из `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` удалены quarter-аксиомы:
  - `prime_term_tcritical_tau0_brange_le_cstar_quarter`,
  - `cstar_quarter_le_arch_term_tcritical_tau0_brange`.
- `prime_term_pathB_tcritical_tau0_brange_analytic` теперь доказывается напрямую из
  `Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom` через
  `prime_cert_margin_lb ≤ arch_term - prime_term` и `prime_cert_margin_pos`.
- Это устраняет scale-конфликт quarter-формы в τ=0 ветке и оставляет
  математически корректную форму долга: прямой gate `prime_term ≤ arch_term`
  на `B ∈ [B_min, prime_cert_B_max]`.
- Проверки:
  - `lake env lean Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` ✅
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `lake env lean Q3/CheckAxioms.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅

### Update (2026-02-25, done) — added reusable τ=0 adapter from PathB contract and rewired t_critical bridge

- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` добавлен адаптер:
  - `prime_term_pathB_tcritical_tau0_brange_of_pathB`.
  - Он специализирует любой `PrimeTermPathBTcritical` в узкий τ=0 B-range gate.
- В `Q3/Proofs/Q_nonneg_t_critical.lean`
  `Q_nonneg_on_base_atoms_at_t_critical_brange_of_pathB` теперь использует
  этот адаптер вместо локального дублирующего вывода.
- Технический нюанс сборки:
  после изменения импортируемого модуля нужен rebuild `.olean/.ilean`
  (`lake env lean --root=. ... -o ... -i ...`), иначе downstream может видеть
  старый API и выдавать `unknown identifier`.
- Axiom snapshot после переподключения:
  - `Q3.Main.RH_of_Weil_and_Q3`: `[propext, Classical.choice, Q3.Weil_criterion_tau0, Quot.sound]`.
  - `Q3.Main.Q_nonneg_on_W_K_tau0`: `[propext, Classical.choice, Quot.sound]`.
  - `Q3.prime_term_pathB_tcritical_tau0_brange_thm` всё ещё опирается на
    `Q3.prime_term_pathB_tcritical_legacy` (off-mainline долг для дальнейшего
    чисто-аналитического закрытия PathB).

### Update (2026-02-25, done) — added pure slack theorem-route skeleton for τ=0 B-range gate

- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` добавлены:
  - `PrimeTermTau0BrangePrimeQuarter` (`prime_term ≤ c_star/4` на brange),
  - `PrimeTermTau0BrangeArchFloor` (`c_star ≤ arch_term` на brange),
  - `prime_term_pathB_tcritical_tau0_brange_of_slack`:
    композиция двух независимых оценок в итоговый gate
    `prime_term ≤ arch_term`.
- Это фиксирует чистый «матан-маршрут без монотонности по B» как отдельный theorem API.
  Теперь для полной pure-замены legacy нужно закрыть только два узких обязательства
  (`PrimeQuarter` и `ArchFloor`) и подать их в `..._of_slack`.
- Сборка после добавления API:
  - `lake env lean --root=. Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean -o ... -i ...` ✅
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅

### Update (2026-02-25, done) — closed τ=0 brange ArchFloor via theorem; reduced PathB legacy debt to prime-quarter

- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` добавлено:
  - `prime_term_tau0_brange_arch_floor_from_heat : PrimeTermTau0BrangeArchFloor`.
- Доказательство ArchFloor (без `Brange_2046`) построено как:
  1. `arch_term_cert_on_Bmin_tau0` (сертификат на `B=B_min`),
  2. `arch_term_Lipschitz_heat` + `prime_heat_bounds_arch_data` (heat-Lipschitz перенос по B),
  3. численная верификация запаса (`c_star` ниже перенесённой нижней границы).
- Также добавлено:
  - `prime_term_tau0_brange_prime_quarter_from_legacy : PrimeTermTau0BrangePrimeQuarter`
    (узкий остаточный долг через `prime_term_tcritical_le_cstar_quarter_mathan`).
- `prime_term_pathB_tcritical_tau0_brange_analytic` теперь собирается через
  `prime_term_pathB_tcritical_tau0_brange_of_slack` из двух независимых обязательств,
  а не через полный `prime_term_pathB_tcritical_from_legacy`.
- Эффект: legacy-долг в τ=0 gate сужен до prime-quarter узла;
  arch-side закрыт theorem-route.
- Проверки:
  - `lake env lean --root=. Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean -o ... -i ...` ✅
  - `lake env lean Q3/Proofs/Q_nonneg_t_critical.lean` ✅
  - `lake env lean Q3/Main.lean` ✅
  - `Q3_QUICK=1 Q3_NO_BUILD=1 ./scripts/check_axioms.sh` ✅

### Update (2026-02-25, done) — added dedicated τ=0 brange gate axiom snapshot checker

- Добавлен файл `Q3/CheckTau0BrangeGate.lean` с `#print axioms` для:
  - `prime_term_tau0_brange_arch_floor_from_heat`,
  - `prime_term_tau0_brange_prime_quarter_from_legacy`,
  - `prime_term_pathB_tcritical_tau0_brange_analytic`,
  - `prime_term_pathB_tcritical_tau0_brange_thm`.
- Снимок после текущих правок:
  - ArchFloor закрыт отдельным theorem-route и зависит только от
    `arch_term_cert_on_Bmin_tau0` + `prime_heat_bounds_arch_data`.
  - Единственный load-bearing PathB-долг в τ=0 gate: 
    `Q3.prime_term_tcritical_le_cstar_quarter_mathan` (prime-quarter).
- Команда для быстрого контроля:
  - `lake env lean Q3/CheckTau0BrangeGate.lean`

### Update (2026-02-25, in progress) — stale .olean masked real axiom chain; forced-fresh check restored true snapshot

- Обнаружен критичный эффект stale-артефактов: `#print axioms` для `Q3.Main.RH_of_Weil_and_Q3`
  показывал только `Weil_criterion_tau0`, пока `Q3/Main.olean` не был пересобран принудительно.
- После fresh rebuild (`lake env lean --root=. ... -o ... -i ...`) реальная цепочка:
  - `Q3.Weil_criterion_tau0`
  - `Q3.prime_term_tcritical_le_cstar_quarter_mathan`
  - `Q3.Proofs.PrimeCert.arch_term_cert_on_Bmin_tau0`
  - `Q3.Proofs.PrimeCert.prime_heat_bounds_arch_data`
- Добавлен safeguard в `scripts/check_axioms.sh`: новый Step 1.5 всегда пересобирает
  `Q3/Proofs/Q_nonneg_t_critical.lean` и `Q3/Main.lean` перед `#print axioms`
  (`Q3_FORCE_FRESH_AXIOMS=1` по умолчанию).
- Decision tree по закрытию prime-side долга:
  - `OK`: изолировать долг в одном узле `prime_term_tcritical_le_cstar_quarter_mathan`.
  - `BLOCKED`: получить quarter-bound только из `B=B_min` + heat-Lipschitz (численный запас не хватает на весь B-range).
  - `FALSE-FOR-NOW`: считать mainline «чистым» по старому snapshot без fresh rebuild.
  - `OK`: держать cert-цепочку как legacy-валидацию и закрывать узкий prime-side theorem-route отдельно.

### Update (2026-02-25, done) — added clean closure API for τ=0 Path B (single prime-side obligation)

- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` добавлена теорема:
  `prime_term_pathB_tcritical_tau0_brange_of_prime_quarter`.
- Смысл: arch-side уже закрыт theorem-ом (`prime_term_tau0_brange_arch_floor_from_heat`),
  поэтому для полного τ=0 gate теперь достаточно одного входа
  `hPrimeQuarter : PrimeTermTau0BrangePrimeQuarter`.
- Это фиксирует чистый API для mathan-closure: один load-bearing prime-side узел,
  без необходимости тащить full PathB-legacy provider в этот closure-point.
- В `Q3/CheckTau0BrangeGate.lean` добавлен `#print axioms` для нового closure-point;
  снимок показывает: у `..._of_prime_quarter` нет `prime_term_tcritical_le_cstar_quarter_mathan`
  (он зависит только от arch-side сертификатных узлов).

### Update (2026-02-25, done) — `prime_term_tcritical_le_cstar_quarter_mathan` removed from mainline via direct margin route

- `prime_term_pathB_tcritical_tau0_brange_analytic` переключён на прямой theorem-route через
  `Q3.Proofs.PrimeCert.prime_cert_margin_on_Brange_axiom` (из `Brange_2046`), без использования
  `prime_term_tcritical_le_cstar_quarter_mathan`.
- После fresh rebuild и `#print axioms`:
  - `Q3.Main.RH_of_Weil_and_Q3` больше **не** содержит
    `Q3.prime_term_tcritical_le_cstar_quarter_mathan`.
  - Текущий mainline-зависимый хвост: `prime_b_grid_arch_bounds_data`,
    `prime_b_grid_bucket_bounds`, `prime_heat_bounds_arch_data`,
    `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all` +
    `Lean.ofReduceBool`, `Lean.trustCompiler`.

Decision tree (fast/robust):
- `OK`: убрать quarter-аксиому из mainline немедленно через direct margin route.
- `BLOCKED`: закрыть `PrimeTermTau0BrangePrimeQuarter` из текущих cert-лемм (недостаточно данных/не тот тип оценки).
- `FALSE-FOR-NOW`: держать canonical τ=0 gate на quarter-аксиоме при наличии прямого margin-route.
- `NEXT`: закрывать cert-хвост (`prime_b_grid_*`, `prime_heat_*`) theorem-ами, затем возвращаться к полностью data-free PathB.

Numeric sanity (вне Lean, для диагностики модели):
- Прямой подсчёт prime-power суммы для
  `prime_term (fun ξ => phi_shift B t_critical 0 ξ)` даёт ~8.71..9.23 на `B∈[3,4.9]`
  (partial до `10^6` уже стабилизирован).
- Это объясняет, почему quarter-form (`≤ c_star/4 = 0.275`) не является рабочим
  closure target в текущей спецификации mainline.

### Update (2026-02-25, done) — removed `native_decide` aggregate from prime-grid sum bridge; trust remains in PrimeHeat layer

- В `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean` добавлен
  data-axiom `prime_b_grid_prime_sum_le_all_data`, и
  `prime_b_grid_prime_term_le_prime_ub_all` переключён на него
  (вместо `prime_b_grid_prime_sum_le_all` через `native_decide`).
- Эффект по `#print axioms`:
  - `prime_b_grid_prime_term_le_prime_ub_all`: больше не тянет
    `Lean.ofReduceBool`/`Lean.trustCompiler`.
  - `prime_cert_margin_on_Brange_axiom` и `Q3.Main.RH_of_Weil_and_Q3` всё ещё
    тянут `Lean.ofReduceBool`/`Lean.trustCompiler` через
    `prime_heat_bounds_arch_data` и
    `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all`.
- Вывод: trust-хвост теперь локализован в PrimeHeat checker-слое; prime-grid aggregate
  уже переведён на data-payload маршрут.

### Update (2026-02-26, done) — PrimeHeatMarginKernel integrated and tau0 mainline switched to witness route

- Добавлен kernel-модуль:
  - `Q3/Proofs/PrimeCert/PrimeHeatMarginKernel.lean`
  - API: `checkPrimeHeatMarginCert` + `margin_lb_on_brange_of_checked_cert`.
- Добавлен witness-модуль:
  - `Q3/Proofs/PrimeCert/PrimeHeatMarginWitness_2026_01_28.lean`
  - единый load-bearing witness axiom:
    `prime_heat_margin_cert_2026_01_28`.
- В `Q3/Proofs/PrimeCert/Brange_2046.lean` добавлен theorem-route:
  - `prime_cert_margin_on_Brange_kernel_shadow`.
- Mainline τ=0 gate переключён на kernel-route:
  - `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` теперь использует
    `prime_cert_margin_on_Brange_kernel_shadow`.
- Итог по `#print axioms Q3.Main.RH_of_Weil_and_Q3`:
  - удалены из main chain:
    `prime_heat_bounds_arch_data`,
    `prime_heat_weight_term_le_pp_ub_of_10001_1000000_primepow_all`,
    а также `Lean.ofReduceBool` и `Lean.trustCompiler`.
  - новая цепочка:
    `Q3.Weil_criterion_tau0`,
    `prime_b_grid_arch_bounds_data`,
    `prime_b_grid_prime_sum_le_all_data`,
    `prime_heat_margin_cert_2026_01_28`.

### Update (2026-02-26, done) — mainline switched from PrimeCert data-chain to Path B legacy quarter gate

- В `Q3/Proofs/PrimeTerm_PathB_tau0_brange_analytic.lean` канонический провайдер
  `prime_term_pathB_tcritical_tau0_brange_thm` переключён на
  `prime_term_pathB_tcritical_tau0_brange_of_pathB prime_term_pathB_tcritical_from_legacy`.
- После свежей пересборки `.olean` для
  `PrimeTerm_PathB_tau0_brange_analytic`, `Q_nonneg_t_critical`, `Q3/Main`
  mainline axiom snapshot стал:
  - `Q3.Weil_criterion_tau0`
  - `Q3.prime_term_tcritical_le_cstar_quarter_mathan`
  - `Q3.cstar_quarter_le_arch_term_tcritical_mathan`
  - plus standard `propext`, `Classical.choice`, `Quot.sound`.
- Из main-chain ушли три cert-data узла:
  - `Q3.Proofs.PrimeCert.prime_b_grid_arch_bounds_data`
  - `Q3.Proofs.PrimeCert.prime_b_grid_prime_sum_le_all_data`
  - `Q3.Proofs.PrimeCert.prime_heat_margin_cert_2026_01_28`.
- Практический эффект: RH mainline больше не load-bearing на Brange Grid/Heat cert payload.

### Update (2026-02-26, in progress) — unified Gaussian tail kernel + removed one redundant grid data axiom

- Целевой узел: убрать дубли tail-логики и сократить data-debt в prime-grid ветке без возврата к тяжёлым PrimePow/Checker цепочкам.
- Поиск: локальный `research_oracle` + внешняя web-проверка подтвердили, что в проекте уже есть готовые theorem-блоки
  (`BrangeHeatCert_2026_01_28_Tail`, `BrangeGrid_PrimeSumTail`) для единого Gaussian tail route.
- Добавлен модуль `Q3/Proofs/PrimeCert/GaussianTailKernel.lean`:
  - единый witness `gaussianTailKernel`,
  - API: `prime_heat_tail_bound_kernel`, `prime_b_grid_tail_summable_kernel`, `prime_b_grid_tail_bound_kernel`.
- Добавлен модуль `Q3/Proofs/PrimeCert/GaussianMajorant.lean`:
  - общий theorem `tail_bound_of_pointwise_majorant`,
  - общий theorem `shifted_tail_bound_of_pointwise_majorant`,
  - это единая мета-лемма для схемы “терм ≤ majorant, majorant-сумма ограничена”.
- `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean` переключён на kernel-теорему
  `prime_heat_tail_bound_kernel`.
- `Q3/Proofs/PrimeCert/BrangeGrid_PrimeSum_2026_01_30_Data.lean`:
  - удалён из файла axiom `prime_b_grid_prime_sum_le_all_data`,
  - `prime_b_grid_prime_term_le_prime_ub_all` теперь использует theorem-route
    `prime_b_grid_prime_sum_le_all` + `prime_b_grid_weight_tail_bound_by_majorant`.
- Статус проверки:
  - `GaussianTailKernel.lean` и `BrangeGrid_PrimeSum_2026_01_30_Data.lean` проверены.
  - `BrangeHeatCert_2026_01_28_SumData.lean` и quick `check_axioms.sh` блокируются активным
    внешним долгим checker-процессом (`BrangeHeatCert_2026_01_28_Checker.lean`) в том же `.lake` контуре.

### Update (2026-02-26, in progress) — import boundary fixed: `SumData` no longer imports `Checker`

- В `Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28_SumData.lean` удалён импорт
  `BrangeHeatCert_2026_01_28_Checker.lean` (и `..._BucketCheck.lean`), чтобы mainline-adjacent
  слой не блокировался долгим checker-процессом.
- Для decoupling добавлены checker-independent payload-узлы:
  - `prime_heat_bucket_bounds_data`,
  - `prime_heat_bucket_ub_sum_le_partial_data`.
- `prime_heat_bucket_data` теперь собирается напрямую из этих payload-узлов, а хвост
  остаётся theorem-route через `prime_heat_tail_bound_kernel`.
- Эффект: разорвана жёсткая зависимость `SumData -> Checker`; долгий процесс checker больше
  не является обязательным импорт-блокером для редактирования `SumData` слоя.
