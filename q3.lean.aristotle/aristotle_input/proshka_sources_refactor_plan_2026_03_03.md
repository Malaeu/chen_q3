# Proshka Sources: Inventory + Refactor Plan (2026-03-03)

## 1) Инвентаризация файлов из скриншотов "Источники"

Базовый корень:
`/mnt/hdd01/Soft/GitHub/chen_q3/worktrees/rh_clean/docs/Aristotle_models_training`

Найдены (соответствие скриншотам):
- Анализ критических констант для высоко-ERS узлов.md
- План интеграции- Автоматическая генерация семантических .md
- dependency_graph.json
- Aristotle- Технические детали из arXiv статьи.md
- RH_Q3.pdf
- Декомпозиция RH_Q3.pdf для формализации в Lean.md
- Критические константы из RH_Q3.pdf (страницы 32-36).md
- Руководство для Aristotle- Закрытие sorries в Q_nonneg_on_atoms_fourier_axiom.lean.md
- claude_code_skills.md
- Методы балансировки неравенств и поиска констант.md
- visualize_graph.py
- SKILL.md
- lean_error_parser.py
- Aristotle Emulator v7- Полная Спецификация.md
- verify_critical_constants.py
- Технический анализ Aristotle и разработка эмулирующего скилла для Claude.md
- Конкуренты Aristotle в области автоматического доказательства теорем.md
- effective_risk.py
- lean4_errors_research.md
- norm_balancer.py
- Логика автоматической генерации семантических .md
- FormalizingRiemannHypothesis.md
- final_report.md
- План формализации RH_Q3.pdf в Lean.md
- extracted_structure.md
- Claude Code Skills- Документация.md
- kernel_analysis_example.py
- Руководство по закрытию tau-shift sorries через workflow скилла.md
- Формализация Effective Risk Score.md
- Алгоритм Приоритизации .md
- Полный справочник по ошибкам Lean 4 для семантического именования sorry.md
- Концепция-  как система уравнений.md
- План интеграции x-critical в Aristotle Emulator.md
- Инсайты из FormalizingRiemannHypothesis.md
- critical_path.mmd

## 2) Что видно после чтения (кратко)

- Часть документов помечена как legacy/two-scale и конфликтует с текущим single-scale mainline.
- Несколько файлов дублируют содержание (например final_report и большой технический анализ).
- Есть workflow-материалы полезные методологически, но не дающие актуальные константы/леммы для текущего cert-слоя.
- Часть скриптов завязана на старые пути и исследовательские артефакты, а не на текущий репозиторный pipeline.

## 3) Shortlist до 10 файлов для "Источников" (рекомендуемый минимум)

1. RH_Q3.pdf
2. extracted_structure.md
3. План формализации RH_Q3.pdf в Lean.md
4. Критические константы из RH_Q3.pdf (страницы 32-36).md
5. Декомпозиция RH_Q3.pdf для формализации в Lean.md
6. Анализ критических констант для высоко-ERS узлов.md
7. Руководство по закрытию tau-shift sorries через workflow скилла.md
8. Руководство для Aristotle- Закрытие sorries в Q_nonneg_on_atoms_fourier_axiom.lean.md
9. SKILL.md
10. dependency_graph.json

## 4) Что убрать из активных "Источников" (перенести в архив)

- Конкуренты Aristotle в области автоматического доказательства теорем.md
- claude_code_skills.md
- Claude Code Skills- Документация.md
- Технический анализ Aristotle и разработка эмулирующего скилла для Claude.md
- final_report.md (дубликат большого анализа)
- FormalizingRiemannHypothesis.md (chat-like mixed content)
- Алгоритм Приоритизации .md
- Концепция-  как система уравнений.md
- Логика автоматической генерации семантических .md

## 5) Что добавить для стабильной работы с нашим текущим контекстом

Добавлять не из historical training-папки, а из текущего Q3:
- q3.lean.aristotle/PROJECT_WORKFLOW.md
- q3.lean.aristotle/PROJECT_ORCHESTRATOR.md
- q3.lean.aristotle/PHILOSOPHY_OF_PROOF.md
- q3.lean.aristotle/docs/INSIGHTS.md
- q3.lean.aristotle/Q3/Proofs/PrimeCert/BrangeHeatCert_2026_01_28.lean
- q3.lean.aristotle/Q3/Proofs/PrimeCert/ArchHeatMajorant.lean
- q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatArchPiecewiseKernel.lean
- q3.lean.aristotle/Q3/Proofs/PrimeCert/PrimeHeatDigammaShift.lean
- q3.lean.aristotle/aristotle_input/prime_heat_bucket_pp_sum_ub_q_le_kernel_target.lean

## 6) Рекомендуемый рефактор "Источников"

Шаг 1. Создать 3 логических набора:
- `sources_core/` (до 10 файлов, только канон + target-specific)
- `sources_tasks/arch/` (арх-задача)
- `sources_tasks/bucket/` (bucket-задача)

Шаг 2. Все legacy/методологические файлы отправить в `sources_archive/`.

Шаг 3. Нормализовать имена (убрать вариации `:`/`-`, двойные пробелы), завести `MANIFEST.md`.

Шаг 4. Для каждого task-пакета держать `READ_FIRST.md` с 5 пунктами:
- цель,
- точный target theorem,
- ограничения,
- разрешённые модули,
- required output format.

Шаг 5. Обновлять пакет только по диффу за неделю (не полное копирование всего репо).
